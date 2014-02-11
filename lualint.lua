#!/usr/bin/env lua

--[[

-------------------------------------------------
TMOORE UPDATES:
- Sorted listing
- Added -m option to skip missing module warnings
- Removed warning for use of "_"
- Added support to pass a path and lint all Lua
  (requires the use of "ls")
- Got it working with target HW and Windows
- Error format changed to match Visual Studio
  to make jumping to errors seemless in
  Visual Studio and SlickEdit.
- Cleaned up displaying errors during compilation
- Added error summaries
- Added some more keywords to ignore
- Changed the "declare" to "lint_declare"
- Ignore the "lint_declare" keyword for "lint_decalre/lint_ignore"
- Added multiple arg support for "lint_ignore" (lint_ignore("arg1","arg2")
- Some code cleanup
-------------------------------------------------


Usage: lualint [-r|-s|-m] filename.lua|path [ [-r|-s|-m] [filename.lua|path] ...]

-m ...... skip missed module warnings
-r ...... relaxed mode
-s ...... strict mode   (default)

Example:
lua ./lualint.lua -m /mnt/net/cmdbg/usr/share/

lualint performs static analysis of Lua source code's usage of global
variables..  It uses luac's bytecode listing.  It reports all accesses
to undeclared global variables, which catches many typing errors in
variable names.  For example:

  local really_aborting
  local function abort() os.exit(1) end
  if not os.getenv("HOME") then
    realy_aborting = true
    abortt()
  end

reports:

  /tmp/example.lua:4: *** global SET of realy_aborting
  /tmp/example.lua:5: global get of abortt

It is primarily designed for use on LTN7-style modules, where each
source file only exports one global symbol.  (A module contained in
the file "foobar.lua" should only export the symbol "foobar".)

A "relaxed" mode is available for source not in LTN7 style.  It only
detects reads from globals that were never set.  The switch "-r" puts
lualint into relaxed mode for the following files; "-s" switches back
to strict.

Required packages are tracked, although not recursively.  If you call
"myext.process()" you should require "myext", and not depend on other
dependencies to load it.  LUA_PATH is followed as usual to find
requirements.

Some (not strictly LTN7) modules may wish to export other variables
into the global environment.  To do so, use the declare function:

  lint_declare "xpairs"
  function xpairs(node)
    [...]

Similarly, to quiet warnings about reading global variables you are
aware may be unavailable:

  lint_ignore "lua_fltk_version"
  if lua_fltk_version then print("fltk loaded") end

One way of defining these is in a module "lint_declare.lua":

  function lint_declare(s)
  end
  declare "lint_ignore"
  function lint_ignore(s)
  end

(Setting declare is OK, because it's in the "declare" module.)  These
functions don't have to do anything, or in fact actually exist!  They
can be in dead code:

  if false then lint_declare "xpairs" end

This is because lualint only performs a rather primitive and cursory
scan of the bytecode.  Perhaps declarations should only be allowed in
the main chunk.

E.g.
function lint_declare(s)           --<<  REQUIRED   For SET's
end                                --<<  REQUIRED
lint_declare "lint_ignore"         --<<  REQUIRED
function lint_ignore(s)            --<<  REQUIRED   For GET's
end                                --<<  REQUIRED

lint_ignore( "g_val" )
lint_ignore( "x" )
--or lint_ignore( "g_val", "x" )

lint_declare( "g_unused" )

g_unused = 1
print( g_other )
print( g_val )
x()

Results:
/home/tmoore/junk.lua(59) : error 2: global get of: g_other

TODO:

The errors don't come out in any particular order.

Should switch to Rici's parser, which should do a much better job of
this, and allow detection of some other common situations.

CREDITS:

Jay Carlson (nop@nop.com)

This is all Ben Jackson's (ben@ben.com) fault, who did some similar
tricks in MOO.
]]

local APP_VER          = "v1.6"

-- OPTIONAL: Can use this if you have luac in a strange place
local TARGET_LUAC_PATH = "/mnt/net/target/qnx6/armle-v7/usr/bin/luac"

local skip_missed_module = false
local found_sets         = false
local found_gets         = false
local parse_failed       = false
local import_failed      = true
local LUAC               = TARGET_LUAC_PATH

-- Total across all files
local totalCompilerErr   = 0
local totalGetErr        = 0
local totalSetErr        = 0
local totalFilesErr      = 0

-----------------------------------------------
-- Set
--
-- [add description here]
--
-- l....
--
-- Return:   [add here]
-----------------------------------------------
local function Set(l)
  local t = {}
  for _,v in ipairs(l) do
    t[v] = true
  end
  return t
end

local ignoreget = Set{
"LUA_PATH", "_G",             "_LOADED",      "_TRACEBACK", "_VERSION", "__pow",    "arg",
"assert",   "collectgarbage", "coroutine",    "debug",      "dofile",   "error",
"gcinfo",   "getfenv",        "getmetatable", "io",         "ipairs",   "loadfile",
"loadlib",  "loadstring",     "math",         "newproxy",   "next",     "os",       "pairs",
"pcall",    "print",          "rawequal",     "rawget",     "rawset",   "require",
"setfenv",  "setmetatable",   "string",       "table",      "tonumber", "tostring",
"type",     "unpack",         "xpcall",       "package",    "select",
"lint_declare"  -- LINT INTERNAL
}


-----------------------------------------------
-- fileexists
--
-- [add description here]
--
-- fname....
--
-- Return:   [add here]
-----------------------------------------------
local function fileexists(fname)
  local f = io.open(fname)
  if f then
    f:close()
    return true
  else
    return false
  end
end

-----------------------------------------------
-- locate
--
-- borrowed from LTN11
--
-- name....
--
-- Return:   [add here]
-----------------------------------------------
local function locate(name)
  local path = LUA_PATH
  if type(path) ~= "string" then
    path = os.getenv "LUA_PATH" or "./?.lua"
  end
  for path in string.gfind(path, "[^;]+") do
    path = string.gsub(path, "?", name)
    if fileexists(path) then
      return path
    end
  end
  return nil
end

-----------------------------------------------
-- scanfile
--
-- [add description here]
--
-- filename....
--
-- Return:   [add here]
-----------------------------------------------
local function scanfile(filename)
  local modules = {}
  local declared = { "lint_declare" }  -- Ignores "lint_declare"
  local lint_ignored = {}
  local refs = {}
  local saw_last = nil
  local line

  -- This is used to support more than one argument for the
  -- lint_ignore() for example: lint_ignore( "arg1", "arg2" )
  local last_ignore = false

  local context, curfunc

  if not fileexists(filename) then
    return nil, "file "..filename.." does not exist"
  end

  -- Run once to see if it parses correctly

  -- This will result in errors being displayed better
  local f = assert (io.popen (LUAC.." -o lualint.tmp "..filename.." 2>&1"))
  for line in f:lines() do
    print("ERROR: "..line)
  end
  f:close()

  if not fileexists("lualint.tmp") then
    return nil, "file "..filename.." did not successfully parse"
  end

  assert(os.remove("lualint.tmp"))

  local bc = assert(io.popen(LUAC.." -l -p "..filename))

  for line in bc:lines() do
    -- main <examples/xhtml2wiki.lua:0> (64 instructions, 256 bytes at 0x805c1a0)
    -- function <examples/xhtml2wiki.lua:13> (6 instructions, 24 bytes at 0x805c438)
    local found, _, type, fname = string.find(line, "(%w+) <([^>]+)>")
    if found then
      if context == "main" then fname="*MAIN*" end
      curfunc = fname
    end

    --print( ">>", line )  -- for debug only

    --print("sawlast", saw_last, "last_ignore", last_ignore)
    -- 69   [54]   GETGLOBAL   21  -23 ; lint_ignore
    --  2   [1]    LOADK        1    1 ; "lazytree"
    -- or
    -- 69  [54]    GETGLOBAL   21 -23  ; lint_ignore
    -- 70  [54]    LOADK       22 -24  ; "g_val"
    -- 71  [54]    LOADK       23 -25  ; "x"
    local found, _, constname = string.find(line, '%sLOADK .-;%s"(.-)"')
    if (saw_last or last_ignore) and found then
      if saw_last == "require" then
        --print("require", constname)
        table.insert(modules, constname)
        last_ignore = false
      elseif saw_last == "lint_declare" then
        --print("lint_declare", constname)
        table.insert(declared, constname)
        last_ignore = false
      elseif last_ignore or saw_last == "lint_ignore" then
        --print("lint_ignore", constname)
        lint_ignored[constname] = true
        last_ignore = true
      else
        last_ignore = false
      end
    else
      last_ignore = false
    end

    --  4   [2] GETGLOBAL   0 0 ; require
    local found, _, lineno, instr, gname = string.find(line, "%[(%d+)%]%s+([SG]ETGLOBAL).-; (.+)")
    if found and gname ~= "_" then
      local t = refs[curfunc] or {SETGLOBAL={n=0}, GETGLOBAL={n=0}}
      local err = {name=gname, lineno=lineno}
      table.insert(t[instr], err)
      refs[curfunc] = t
      saw_last = gname
    else
      saw_last = nil
    end
  end
  bc:close()
  return modules, declared, lint_ignored, refs
end

-----------------------------------------------
-- lint
--
-- [add description here]
--
-- filename....
-- relaxed ....
-----------------------------------------------
local function lint(filename, relaxed)
  local modules, declared, lint_ignored, refs = scanfile(filename)

  if not modules then
    totalFilesErr    = totalFilesErr + 1
    totalCompilerErr = totalCompilerErr + 1
    print(string.format("%s:%d: *** could not parse: %s ", filename, 1, declared))
    parse_failed = true
    return
  end

  local imported_declare_set = {}
  for i,module in ipairs(modules) do
    local path = locate(module)
    if not path then
      if not skip_missed_module then
        print(string.format("%s:%d: could not find imported module %s ", filename, 1, module))
      end
      import_failed = true
    else
      local success, imported_declare, _, _ = scanfile(path)
      if not success then
        print(string.format("%s:%d: could not parse import: %s ", path, 1, imported_declare))
        import_failed = true
      else
        for i,declared in ipairs(imported_declare) do
          imported_declare_set[declared] = true
        end
      end
    end
  end

  local moduleset   = Set(modules)
  local declaredset = Set(declared)

  local self_name = nil
  do
    local _
    if string.find(filename, "/") then
      _, _, self_name = string.find(filename, ".-/(%w+)%.lua")
    else
      _,_,self_name = string.find(filename, "(%w+)%.lua")
    end
  end
  -- print("selfname", self_name)

  local was_set = {}

  local function will_warn_for(name)
    if relaxed and was_set[name] then
      return false
    end
    if name == self_name or
      lint_ignored[name] or
      ignoreget[name] or
      moduleset[name] or
      declaredset[name] or
      imported_declare_set[name] then
      return false
    end
    return true
  end

  local outList  = {}
  local setCount = 0
  local getCount = 0

  for f,t in pairs(refs) do
    for _,r in ipairs(t.SETGLOBAL) do
      if r.name ~= self_name and not declaredset[r.name] then
        was_set[r.name] = true
        if not relaxed then
          setCount    = setCount+1
          totalSetErr = totalSetErr + 1
          --table.insert(outList, string.format("%010d:%s:%6d: *** global SET of: %s", r.lineno, filename, r.lineno, r.name))
          table.insert(outList, string.format("%010d:%s(%d) : error 1: *** global SET of: %s", r.lineno, filename, r.lineno, r.name))
          --print(string.format("%s:%d: *** global SET of %s", filename, r.lineno, r.name))
          found_sets = true
        end
      end
    end
  end

  for f,t in pairs(refs) do
    for _,r in ipairs(t.GETGLOBAL) do
      if will_warn_for(r.name) then
        getCount    = getCount+1
        totalGetErr = totalGetErr + 1
        --table.insert(outList, string.format("%010d:%s:%6d: global get of:     %s", r.lineno, filename, r.lineno, r.name))
        table.insert(outList, string.format("%010d:%s(%d) : error 2: global get of: %s", r.lineno, filename, r.lineno, r.name))
        --print(string.format("%s:%d: global get of %s", filename, r.lineno, r.name))
        found_gets = true
      end
    end
  end

  -- Display stats and sorted listing
  if #outList ~= 0 then
    table.sort(outList)
    local idx, sOut
    print()
    --print(string.format("\n****** TOTAL WARNINGS: %d  (Set: %d, Get: %d)", #outList, setCount, getCount))
    for idx,sOut in ipairs(outList) do
      -- remove the leading line number used for sorting
      print(string.sub(sOut, 12))
    end
  end

  print(string.format("****** TOTAL WARNINGS: %d  (Set: %d, Get: %d)\n", #outList, setCount, getCount))

  if #outList ~= 0 then
    totalFilesErr = totalFilesErr + 1
  end

end


-----------------------------------------------
-- lint_arg
--
-- Will lint a single file or directory
--
-- sStartPath....
-- relaxed   ....
-----------------------------------------------
local function lint_arg(sStartPath, relaxed)

    local iFileCount= 0
    local sDir      = ""
    local sFile     = ""
    local sPathFile = ""
    local sCurrDir  = sStartPath
    local sPos, ePos

    -- TODO: Would be nice to make this more flexible possibly
    --       using luafilesystem or somethig else.  Tried to keep
    --       the dependencies down.
    for i in io.popen("ls -1 -F -R "..sStartPath):lines() do
      sPos, ePos, sDir = string.find(i, "(.*):")
      if sDir ~= nil then
          sCurrDir = sDir
      end

      if string.find(i,"%.lua") then
          -- QNX will have a * for all files
          -- Windows will not have the *
          sPos, ePos, sFile = string.find(i, "(.*)%*")
          if sFile == nil then
            sPos, ePos, sFile = string.find(i, "(.*)")
          end

          iFileCount = iFileCount+1
          print("\n"..string.rep("-", 80))
          if sCurrDir and sFile then
            if sStartPath == sFile then
                -- MUST have a file passed in
                print(string.format("LINTING: %s\n", sFile))
                lint(sFile, relaxed)
            else
                sPathFile = string.format("%s/%s", sCurrDir, sFile)
                print(string.format("LINTING: %s\n", sPathFile))
                lint(sPathFile, relaxed)
            end
          else
            -- something wrong, don't crash
            print("SKIPPING:",i,"FILE:",sFile)
          end
      end
    end

    if iFileCount > 1 then
      print("\n"..string.rep("-", 80))
      print(string.format("TOTAL FILES LINTING: %d", iFileCount))
      print(string.format("TOTAL FILES WITH WARNINGS: %d  (Error: %d, Set: %d, Get: %d)", totalFilesErr, totalCompilerErr, totalSetErr, totalGetErr))
      print(string.rep("-", 80).."\n")
    end

end


--------------------------------------
-- Main
--------------------------------------

-- Check for the required luac executable
if not fileexists(LUAC) then
  -- target path for luac is missing
  -- try execution where environ will be used
  LUAC = "luac"
end

print()
if arg.n == 0 then
  print("Usage: lualint [-r|-s|-m] filename.lua|path [ [-r|-s|-m] [filename.lua|path] ...]")
  os.exit(1)
end

print("\n"..string.rep("*", 80))
print("Lua Lint "..APP_VER, "Executed: "..os.date())
print(string.rep("*", 80).."\n")

local relaxed_mode = false

for i,v in ipairs(arg) do
  if v == "-r" then
    relaxed_mode = true
  elseif v == "-s" then
    relaxed_mode = false
  elseif v == "-m" then
    skip_missed_module = true
  else
    lint_arg(v, relaxed_mode)
  end
end

print()
if parse_failed then
  os.exit(3)
elseif import_failed then
  os.exit(1)
elseif found_sets then
  os.exit(2)
elseif found_gets then
  os.exit(1)
else
  os.exit(0)
end




--=============================================================
--=============================================================
--=============================================================
-- Test code
--=============================================================
--=============================================================
--=============================================================
--function lint_declare(s)           --<<  REQUIRED   For SET's missing
--end                                --<<  REQUIRED
--lint_declare "lint_ignore"         --<<  REQUIRED
--function lint_ignore(s)            --<<  REQUIRED   For GET's missing
--end                                --<<  REQUIRED
--
--lint_ignore( "g_val", "x" )
--lint_declare( "g_unused" )
--
--
--g_unused = 1
--print( g_other )
--print( g_val )
--x()
--
-- RESULT:
--/home/tmoore/junk.lua(60) : error 2: global get of: g_other
--****** TOTAL WARNINGS: 1  (Set: 0, Get: 1)


