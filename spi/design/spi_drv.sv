// File: spi_drv.sv
// Description: The driver takes transactions from a mailbox and drives the
// physical signals of the SPI interface.

class spi_drv;
  // Virtual interface handle for signal access.
  virtual spi_if.DRIVER spi_vif;
  // Mailbox to receive transactions from a sequence.
  mailbox #(spi_tran) mbx;

  // Constructor
  function new(mailbox #(spi_tran) mbx);
    this.mbx = mbx;
  endfunction

  // Main driver task.
  task run();
    spi_tran tr;
    forever begin
      // Get a new transaction from the mailbox.
      mbx.get(tr);
      @(spi_vif.drv_cb);

      // Drive the transaction's data and start signal.
      spi_vif.tx_data <= tr.tx_data;
      spi_vif.start <= 1;

      @(spi_vif.drv_cb);
      spi_vif.start <= 0;
      
      // Wait for the 'done' signal from the DUT.
      while (!spi_vif.done) @(spi_vif.drv_cb);
      // Capture the received data.
      tr.rx_data = spi_vif.rx_data;

      $display("Driver sent transaction: %s", tr.toString());
    end
  endtask
endclass

