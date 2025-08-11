#!/bin/csh

# Type
if (! $?TYPE) then
    setenv TYPE "v"
endif

# Check to ensure at least 2 inputs
if (($#argv != 2) || ($1 == "")) then
    echo "[1] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Check to ensure the valid 1st input
if (($1 != "dv") && ($1 != "idebug") && ($1 != "pdebug") && ($1 != "cov")) then
    echo "[2] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Check to ensure the valid 2nd input
if (!(-e $ROOT/design/{$2}_tb.$TYPE)) then
    echo "[3] Usage: $0 <dv|idebug|pdebug|cov> <module_name>"
    exit 1
endif

# Run
set command = ""
setenv MODE $1
setenv MODULE $2
if (! $?STEP) then
    setenv STEP "2"
endif
if (! $?FLIST) then
    setenv FLIST "0"
endif
if (! $?MODULE_TB) then
    setenv MODULE_TB "$MODULE""_tb"
endif
if (! $?NR) then
    setenv NR "0"
endif
if (! $?COVERAGE) then
    setenv COVERAGE "0"
endif
if (! $?ASSERT) then
    setenv ASSERT "0"
endif
if (! $?UVM_DESIGN) then
    setenv UVM_DESIGN "$ROOT/design"
endif
echo "[==== INFO ====] SIMULATION: $0 $1 $2"
echo "[==== INFO ====] TYPE: $TYPE"
echo "[==== INFO ====] MODE: $MODE"
echo "[==== INFO ====] MODULE: $MODULE"
echo "[==== INFO ====] MODULE_TB: $MODULE_TB"
echo "[==== INFO ====] STEP: $STEP"
echo "[==== INFO ====] FLIST: $FLIST"
echo "[==== INFO ====] COVERAGE: $COVERAGE"
echo "[==== INFO ====] ASSERT: $ASSERT"
echo "[==== INFO ====] UVM_DESIGN: $UVM_DESIGN"
echo "[==== INFO ====] NR: $NR"
if ($NR == 1) then
    set qrun_file = "qrun"
    \rm -frd $qrun_file
    touch $qrun_file
    chmod 755 $qrun_file
else
    set qrun_file = ""
endif
if ($COVERAGE == 1) then
    set coverage1 = "-cm line+tgl+cond+fsm+branch"
    set coverage2 = "-cm line+tgl+cond+fsm+branch"
else
    set coverage1 = ""
    set coverage2 = ""
endif
if ($ASSERT == 1) then
    set coverage1 = "-cm line+tgl+cond+fsm+branch+assert"
    set coverage2 = "-cm line+tgl+cond+fsm+branch+assert"
    set assert1 = "-assert enable_diag"
    set assert2 = "-assert summary"
else
    set assert1 = ""
    set assert2 = ""
endif
if ($FLIST == 1) then
    set filelist = "$ROOT/design/$MODULE.f"
    if (! -e $filelist) then
        echo "[4] ERROR: Filelist $filelist not found."
        exit 1
    endif
    set files = "-ntb_opts uvm-ieee-2020-2.0 +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR -file $filelist -timescale=1ns/1ps $coverage1 $assert1"
else
    set files = "-ntb_opts uvm-ieee-2020-2.0 +define+UVM_OBJECT_MUST_HAVE_CONSTRUCTOR +incdir+$UVM_DESIGN $VCS_HOME/etc/uvm-ieee-2020-2.0/uvm_pkg.sv $ROOT/design/$MODULE_TB.$TYPE -timescale=1ns/1ps $coverage1 $assert1"
endif

if ($MODE == "dv") then
    if ($STEP == 3) then
        set command = "vlogan -l $MODULE\_ana.log -sverilog -kdb $files"
        echo "[=== =INFO ====] $command"
        if ($NR != 1) then
            eval $command
        else
            echo "$command" >> $qrun_file
        endif

        set command = "vcs -full64 -l $MODULE\_comp.log -sverilog +v2k +vcs+lic+wait +vcs+flush+all -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files"
        echo "[==== INFO ====] $command"
        if ($NR != 1) then
            eval $command
        else
            echo "$command" >> $qrun_file
        endif

        set command = "$MODULE\_simv -l $MODULE\_sim.log +UVM_NO_RELNOTES $coverage2 $assert2"
        echo "[==== INFO ====] $command"
        if ($NR != 1) then
            eval $command
        else
            echo "$command" >> $qrun_file
        endif
    else
        set command = "vcs -full64 -l $MODULE\_comp.log -sverilog +v2k +vcs+lic+wait +vcs+flush+all -debug_access+all -kdb -debug_report -top $MODULE_TB -o $MODULE\_simv $files"
        echo "[==== INFO ====] $command"
        if ($NR != 1) then
            eval $command
        else
            echo "$command" >> $qrun_file
        endif

        set command = "$MODULE\_simv -l $MODULE\_sim.log +UVM_NO_RELNOTES $coverage2 $assert2"
        echo "[==== INFO ====] $command"
        if ($NR != 1) then
            eval $command
        else
            echo "$command" >> $qrun_file
        endif
    endif
endif
