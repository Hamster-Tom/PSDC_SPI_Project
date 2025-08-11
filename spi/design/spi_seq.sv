// File: spi_seq.sv
// Description: Defines a simple sequence that generates transactions and sends them
// to the driver's mailbox.

class spi_seq;
  // Mailbox handle to communicate with the driver.
  mailbox #(spi_tran) drv_mbx;

  // Constructor
  function new(mailbox #(spi_tran) drv_mbx);
    this.drv_mbx = drv_mbx;
  endfunction

  // Task to generate and send transactions.
  task run();
    spi_tran tr;
    repeat(10) begin
      tr = new();
      // Randomize the transaction's transmit data.
      tr.tx_data = $random;
      $display("Sequence sending a transaction with TX data: 0x%h", tr.tx_data);
      // Put the transaction in the driver's mailbox.
      drv_mbx.put(tr);
      // Wait a short time before sending the next transaction.
      #500;
    end
  endtask
endclass

