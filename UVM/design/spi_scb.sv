class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)
    
  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) scb_imp;
    
  int passed_count = 0;
  int failed_count = 0;
  int slave_rx_data = 0

  function new(string name, uvm_component parent);
    super.new(name, parent);
    scb_imp = new("scb_imp", this);
  endfunction
    
  function void write(spi_tran tr);
    
    if(!uvm_config_db#(int)::get(this, "", "slave_rx_data", slave_rx_data)) begin
        `uvm_warning("MONITOR", "Unable to retrieve slave_rx_data from spi_tb")
      end

    if (slave_rx_data === tr.tx_data) begin
      passed_count++;
      `uvm_info("SCOREBOARD", $sformatf(
        "PASS: Seq[%0d/%0d] %s expected_data=0x%0h recieved_data=0x%0h",
        tr.seq_index, tr.seq_count, tr.seq_type,
        tr.tx_data, slave_rx_data), UVM_LOW)
    end else begin
      failed_count++;
      `uvm_error("SCOREBOARD", $sformatf(
        "FAIL: Seq[%0d/%0d] %s expected_data=0x%0h recieved_data=0x%0h",
        tr.seq_index, tr.seq_count, tr.seq_type,
        tr.tx_data, slave_rx_data))
    end
  endfunction
    
  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Results: Passed=%0d Failed=%0d",
	                                  passed_count, failed_count), UVM_NONE)
  endfunction
endclass