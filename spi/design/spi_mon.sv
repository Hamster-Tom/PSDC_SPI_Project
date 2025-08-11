// File: spi_mon.sv
// Description: The monitor passively observes the interface signals and
// creates transactions based on the observed activity.

class spi_mon;
  // Virtual interface handle for signal observation.
  virtual spi_if.MONITOR spi_vif;
  // Mailbox to put observed transactions into for the scoreboard.
  mailbox #(spi_tran) mbx;

  // Constructor
  function new(mailbox #(spi_tran) mbx);
    this.mbx = mbx;
  endfunction

  // Main monitor task.
  task run();
    spi_tran tr;
    forever begin
      // Wait for a new transfer to start (start signal).
      @(posedge spi_vif.start);
      tr = new();
      tr.tx_data = spi_vif.tx_data;
      
      // Wait for the transfer to end (done signal).
      @(posedge spi_vif.done);
      tr.rx_data = spi_vif.rx_data;
      
      $display("Monitor observed transaction: %s", tr.toString());
      // Put the captured transaction into the mailbox.
      mbx.put(tr);
    end
  endtask
endclass

