class spi_scb extends uvm_scoreboard;
  `uvm_component_utils(spi_scb)
    
  // Use implementation port to receive transactions
  uvm_analysis_imp #(spi_tran, spi_scb) mon_imp;
    
  int passed_count = 0;
  int failed_count = 0;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    mon_imp = new("mon_imp", this);
  endfunction
    
  // This will be called when transactions arrive
  function void write(spi_tran tr);
   // Add in assertion for this area.
    
  endfunction
    
  function void report_phase(uvm_phase phase);
    `uvm_info("SCOREBOARD", $sformatf("Test Results: Passed=%0d Failed=%0d",
	                                  passed_count, failed_count), UVM_NONE)
  endfunction
endclass
