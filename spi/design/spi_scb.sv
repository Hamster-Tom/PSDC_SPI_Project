// File: spi_scb.sv
// Description: The scoreboard receives transactions from the monitor and
// compares the received data against expected values.

class spi_scb;
  // Mailbox to receive transactions from the monitor.
  mailbox #(spi_tran) mbx;

  // Constructor
  function new(mailbox #(spi_tran) mbx);
    this.mbx = mbx;
  endfunction

  // Main scoreboard task.
  task run();
    spi_tran tr;
    // Simple reference model for expected data.
    bit [7:0] SLAVE_RESET_RESPONSE = 8'hB9;
    forever begin
      // Get a transaction from the monitor's mailbox.
      mbx.get(tr);

      // Set the expected data based on a simple reference model.
      tr.expected_rx_data = SLAVE_RESET_RESPONSE;

      if (tr.rx_data == tr.expected_rx_data) begin
        $display("Scoreboard: PASSED. Received data matches expected. %s", tr.toString());
      end else begin
        $display("Scoreboard: FAILED. Received data mismatch. %s", tr.toString());
      end
    end
  endtask
endclass

