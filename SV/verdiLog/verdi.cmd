debImport "-sverilog" "spi_tb_sv/spi_tb_top.sv" "-assertion" "open"
nsMsgSwitchTab -tab general
debLoadSimResult \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/dump.fsdb
wvCreateWindow
nsMsgSwitchTab -tab cmpl
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "238" "114" "1440" "752"
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
verdiSetActWin -win $_nWave2
wvRestoreSignal -win $_nWave2 \
           "/home/user19/Downloads/final_project/PSDC_SPI_Project/SV/signal.rc" \
           -overWriteAutoAlias on -appendSignals on
srcDeselectAll -win $_nTrace1
srcSelect -word -line 75 -pos 3 -win $_nTrace1
srcAction -pos 75 3 13 -win $_nTrace1 -name "dout_master_sampled_n" -ctrlKey off
verdiSetActWin -dock widgetDock_MTB_SOURCE_TAB_1
srcDeselectAll -win $_nTrace1
srcAction -pos 85 3 13 -win $_nTrace1 -name "dout_slave_sampled_n" -ctrlKey off
srcDeselectAll -win $_nTrace1
srcAction -pos 95 3 13 -win $_nTrace1 -name "sclk_en_assert_sclk" -ctrlKey off
srcHBSelect "spi_top_tb.82_spi_tb_top_sv_assert" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBDrag -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 7)}
wvSetPosition -win $_nWave2 {("G1" 8)}
wvSetPosition -win $_nWave2 {("G1" 9)}
wvSetPosition -win $_nWave2 {("G1" 10)}
wvSetPosition -win $_nWave2 {("G1" 11)}
wvSetPosition -win $_nWave2 {("G1" 12)}
wvSetPosition -win $_nWave2 {("G1" 13)}
wvSetPosition -win $_nWave2 {("G1" 14)}
wvSetPosition -win $_nWave2 {("G1" 15)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G1" 11)}
wvSetPosition -win $_nWave2 {("G2" 0)}
wvSetPosition -win $_nWave2 {("G1" 15)}
wvSetPosition -win $_nWave2 {("G1" 14)}
wvSetPosition -win $_nWave2 {("G1" 13)}
wvSetPosition -win $_nWave2 {("G1" 12)}
wvSetPosition -win $_nWave2 {("G1" 11)}
evalPropAtBgMode {{spi_top_tb.82_spi_tb_top_sv_assert}} -logToVcfShell
assCtrlClose -eval
assCtrlInvoke -eval
psmCommitAssertions
nsMsgSwitchTab -tab general
vdac /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/dump.fsdb -o /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056931  -write 2 -reset_filter 
assMoveFile -from \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056931 \
           -to \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb
assToolBuildVirFile -virtualFile \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf \
           -virtualFileType 1 -fileNum 2 -FileList \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/dump.fsdb /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb  \
           -FilePriorityList 0 0 
debCloseSimResult -IsShowWarn 0
debLoadSimResult \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf
assCtrlInvoke -statistic
propRstSetTab -propStat
verdiDockWidgetSetCurTab -dock windowDock_nWave_2
wvAddSignal -win $_nWave2 "/spi_top_tb/82_spi_tb_top_sv_assert"
wvSetPosition -win $_nWave2 {("G1" 11)}
wvSetPosition -win $_nWave2 {("G1" 12)}
srcHBSelect "spi_top_tb.92_spi_tb_top_sv_assert" -win $_nTrace1
srcHBDrag -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 0)}
wvSetPosition -win $_nWave2 {("G1" 1)}
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 3)}
wvSetPosition -win $_nWave2 {("G1" 4)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 6)}
wvSetPosition -win $_nWave2 {("G1" 7)}
wvSetPosition -win $_nWave2 {("G1" 8)}
wvSetPosition -win $_nWave2 {("G1" 9)}
wvSetPosition -win $_nWave2 {("G1" 10)}
wvSetPosition -win $_nWave2 {("G1" 11)}
wvSetPosition -win $_nWave2 {("G1" 12)}
wvSetPosition -win $_nWave2 {("G1" 13)}
wvSetPosition -win $_nWave2 {("G1" 12)}
evalPropAtBgMode {{spi_top_tb.92_spi_tb_top_sv_assert}} -logToVcfShell
psmCommitAssertions
vdac /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf -o /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056936  -write 2 -reset_filter 
assMoveFile -from \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056936 \
           -to \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb
assToolBuildVirFile -virtualFile \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf \
           -virtualFileType 1 -fileNum 2 -FileList \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/dump.fsdb /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb  \
           -FilePriorityList 0 0 
debCloseSimResult -IsShowWarn 0
debLoadSimResult \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf
assCtrlInvoke -statistic
verdiDockWidgetSetCurTab -dock windowDock_nWave_2
wvAddSignal -win $_nWave2 "/spi_top_tb/92_spi_tb_top_sv_assert"
wvSetPosition -win $_nWave2 {("G1" 12)}
wvSetPosition -win $_nWave2 {("G1" 13)}
verdiSetActWin -win $_nWave2
srcHBSelect "spi_top_tb.102_spi_tb_top_sv_assert" -win $_nTrace1
verdiSetActWin -dock widgetDock_<Inst._Tree>
srcHBDrag -win $_nTrace1
wvSetPosition -win $_nWave2 {("G1" 2)}
wvSetPosition -win $_nWave2 {("G1" 5)}
wvSetPosition -win $_nWave2 {("G1" 9)}
wvSetPosition -win $_nWave2 {("G1" 11)}
wvSetPosition -win $_nWave2 {("G1" 12)}
wvSetPosition -win $_nWave2 {("G1" 13)}
wvSetPosition -win $_nWave2 {("G1" 14)}
wvSetPosition -win $_nWave2 {("G1" 13)}
evalPropAtBgMode {{spi_top_tb.102_spi_tb_top_sv_assert}} -logToVcfShell
psmCommitAssertions
vdac /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf -o /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056942  -write 2 -reset_filter 
assMoveFile -from \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/.tmp_evaluate_result.fsdb_1755056942 \
           -to \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb
assToolBuildVirFile -virtualFile \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf \
           -virtualFileType 1 -fileNum 2 -FileList \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/dump.fsdb /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb  \
           -FilePriorityList 0 0 
debCloseSimResult -IsShowWarn 0
debLoadSimResult \
           /home/user19/Downloads/final_project/PSDC_SPI_Project/SV/evaluate_result.fsdb.vf
assCtrlInvoke -statistic
verdiDockWidgetSetCurTab -dock windowDock_nWave_2
wvAddSignal -win $_nWave2 "/spi_top_tb/102_spi_tb_top_sv_assert"
wvSetPosition -win $_nWave2 {("G1" 13)}
wvSetPosition -win $_nWave2 {("G1" 14)}
wvScrollDown -win $_nWave2 1
verdiSetActWin -win $_nWave2
verdiWindowResize -win $_Verdi_1 "238" "114" "1440" "752"
debExit
