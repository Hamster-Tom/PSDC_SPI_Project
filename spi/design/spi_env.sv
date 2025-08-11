// File: spi_env.sv
// Description: The environment class is the top-level container for all
// testbench components, including the driver, monitor, and scoreboard.
// It connects the components using mailboxes.

class spi_env;
  // Mailboxes for communication between components.
  mailbox #(spi_tran) drv_mbx;
  mailbox #(spi_tran) mon_mbx;
  
  // Component handles.
  spi_drv drv;
  spi_mon mon;
  spi_scb scb;
  //spi_cov cov; // Uncomment to include coverage component.

  // Virtual interface handle.
  virtual spi_if spi_vif;

  // Constructor
  function new(virtual spi_if spi_vif);
    this.spi_vif = spi_vif;
    
    // Create mailboxes.
    drv_mbx = new();
    mon_mbx = new();
    
    // Create and connect components.
    drv = new(drv_mbx);
    mon = new(mon_mbx);
    scb = new(mon_mbx);
    //cov = new();

    drv.spi_vif = this.spi_vif;
    mon.spi_vif = this.spi_vif;
  endfunction

  // Main task to run all components concurrently.
  task run();
    fork
      drv.run();
      mon.run();
      scb.run();
      // Add cov.sample() call inside a forever loop that waits for a transaction
    join_none
  endtask
endclass

