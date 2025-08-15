ROOT := $(shell pwd)
export ROOT
SEED = 5
Bit?=8

#variables
VCS_OPTS = -sverilog -kdb -debug_access+all 
SV_DESIGN = $(ROOT)/spi_design
SV_TESTBENCH = $(ROOT)/spi_tb_sv
INCLUDE = +incdir+$(SV_DESIGN)+$(SV_TESTBENCH)
TIMESCALE = -timescale=1ns/1ps
RANDOM_SEED = +ntb_random_seed=$(SEED)
RUN_OPTS = -R 
FUNC_CVR = -cm line+cond+tgl+fsm+branch+assert
FILE_TO_DEL = csrc simv simv.daidir ucli.key libnz4w_r.soLog verdiLog \
verdi_config_file inter.fsdb dump.vcd novas* cm.log simv.vdb urgReport \
vdCov.conf vdCovLog build.log sim.log 

#Grab the second word in the make command (e.g., the .sv file)
#SRC      = $(filter %.sv, $(MAKECMDGOALS))
SRC		  = -f ./build.f

#target
all: build run

build:
	vcs $(SRC) $(VCS_OPTS) $(FUNC_CVR) $(INCLUDE) $(TIMESCALE) \
	    +define+SPI_TRF_BIT=$(BIT) | tee build.log
run:
	./simv $(FUNC_CVR) | tee sim.log 
	@if grep -i "mismatch" sim.log; then \
		grep --color=always -nH -i "mismatch" sim.log; \
	else \
		printf "\033[0;32mTEST PASSED\033[0m: No mismatch in sim.log\n"; \
	fi

wave:
	verdi -ssf fsdbdump.fsdb &

#To generate coverage reports and analyze the results
#using Unified Report Generator 
urgcov:
	urg -dir simv.vdb

# using Verdi Coverage GUI
verdicov:
	verdi -cov -covdir simv.vdb &

clean:
	rm -rf $(FILE_TO_DEL) 

# Dummy target to absorb extra argument (e.g., .sv)
%:
	@true

.PHONY: all build run clean

