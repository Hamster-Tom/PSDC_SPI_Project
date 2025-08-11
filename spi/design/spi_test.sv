// File: spi_test.sv
// Description: This is a placeholder for a test class. In a simplified
// non-UVM testbench, the test plan is implemented directly in the
// initial block of the top-level testbench file.

class spi_test;
  spi_env env;
  spi_seq seq;

  // Constructor
  function new(spi_env env);
    this.env = env;
    seq = new(env.drv_mbx);
  endfunction

  // Main test task.
  task run();
    env.run();
    seq.run();
  endtask
endclass

