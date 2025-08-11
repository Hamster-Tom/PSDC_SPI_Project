// File: spi_agt.sv
// Description: This is a placeholder for an agent class.
// In a non-UVM testbench, the environment class often directly manages
// the driver and monitor, fulfilling the agent's role.

class spi_agt;
  spi_drv driver_comp;
  spi_mon monitor_comp;

  // Constructor
  function new(mailbox #(spi_tran) drv_mbx, mailbox #(spi_tran) mon_mbx);
    driver_comp = new(drv_mbx);
    monitor_comp = new(mon_mbx);
  endfunction
endclass

