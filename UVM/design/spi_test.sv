class spi_test extends uvm_test;
  `uvm_component_utils(spi_test)

  spi_env env;
  spi_seq seq;
 

  int seq_count = 8, hseq_count = 2, lseq_count = 5;
  int seq_min_delay = 10,  seq_max_delay = 15;
 
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    env = spi_env::type_id::create("env", this);
  endfunction

  task run_phase(uvm_phase phase);
    seq = spi_seq::type_id::create("seq");
    
    seq.seq_count = this.seq_count;
    seq.min_delay = this.seq_min_delay;
    seq.max_delay = this.seq_max_delay;
   
    `uvm_info("TEST", $sformatf("Starting sequences with config:\n\
                                Normal: count=%0d, delay=%0d-%0d\n,
                               
                                seq.seq_count, seq.min_delay, seq.max_delay,
                               
                                UVM_MEDIUM)

    phase.raise_objection(this);
    fork
      seq.start(env.agt.sqr);
     
    join
    // Important to avoid simulation ended before processing all the FIFO contents
    wait(phase.drop_objection(this);
  endtask
endclass
