class spi_cov extends uvm_component;
  `uvm_component_utils(spi_cov)
    
	// Use implementation port to receive transactions
	uvm_analysis_imp #(spi_tran, spi_cov) cov_imp;

	function new(string name, uvm_component parent);
	super.new(name, parent);
		cov_imp = new("cov_imp", this);

		tx_rx_data_cg 		= new();
		state_machine_cg 	= new();

		tx_rx_data_cg.set_inst_name($sformatf("%s\ (tx_rx_data_cg\)", get_full_name()));
		state_machine_cg.set_inst_name($sformatf("%s\ (state_machine_cg\)", get_full_name()));
	endfunction

	// This will be called when transactions arrive
	function void write(spi_tran tr);
		tx_rx_data_cg.sample(tr);
		state_machine_cg.sample(tr);
	endfunction

	// Requirement: 5.1.3 Coverage: tx_data and rx_data.

	covergroup tx_rx_data_cg with function sample(spi_tran tr);
		option.per_instance = 1;
		tx_data_cp: coverpoint tr.tx_data {
		    bins low = {8'h00};
		    bins mid = {8'h7F};
		    bins high = {8'hFF};
		    bins other = default;
		}
		rx_data_cp: coverpoint tr.rx_data {
		    bins low = {8'h00};
		    bins mid = {8'h7F};
		    bins high = {8'hFF};
		    bins other = default;
		}
		tx_rx_cross: cross tx_data_cp, rx_data_cp; // Cross coverage
	endgroup

	// Requirement: 5.1.5 State machine and parameter coverage.

	covergroup state_machine_cg with function sample(spi_tran tr);
	  option.per_instance = 1;

	  // Coverpoints for handshake/control signals
	  start_cp: coverpoint tr.start {
		bins start_low  = {0};
		bins start_high = {1};
	  }

	  busy_cp: coverpoint tr.busy {
		bins busy_low  = {0};
		bins busy_high = {1};
	  }

	  done_cp: coverpoint tr.done {
		bins done_low  = {0};
		bins done_high = {1};
	  }

	  // Transitions that represent state-machine behavior
	  start_to_busy: coverpoint tr.start iff (tr.busy) {
		bins start_then_busy = (1 => 0); // start goes high, then low as busy asserts
	  }

	  busy_to_done: coverpoint tr.busy iff (tr.done) {
		bins busy_then_done = (1 => 0);  // busy deasserts as done asserts
	  }

	  // Cross-coverage for overall state machine consistency
	  start_busy_done_cross: cross start_cp, busy_cp, done_cp;
	endgroup

  function void report_phase(uvm_phase phase);
    `uvm_info("COVERAGE", $sformatf("Coverage tx_rx_data_cg		: %.2f%%", tx_rx_data_cg.get_coverage()), UVM_NONE)
    `uvm_info("COVERAGE", $sformatf("Coverage state_machine_cg	: %.2f%%", state_machine_cg.get_coverage()), UVM_NONE)

  endfunction
endclass
