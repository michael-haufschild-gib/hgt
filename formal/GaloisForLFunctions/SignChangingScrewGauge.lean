import GaloisForLFunctions.SignChangingScrewGauge.SignChangingCollarGaugeLedger
import GaloisForLFunctions.SignChangingScrewGauge.NetPrimeAutocorrelationAndEdgeTentResolution
import GaloisForLFunctions.SignChangingScrewGauge.ScrewResonantCollarAndPoleCalibration
import GaloisForLFunctions.SignChangingScrewGauge.MasterSignChangingScrewGaugeTheorem

/-!
# Sign-Changing Screw-Resonant Gauges in GlobalIncidenceAllocation

Umbrella module for `GaloisForLFunctions.SignChangingScrewGauge`, formalizing Mechanism 3 of
Project Argon (`docs/reports/review-2110/argon.md`, §1.4): unconditional ground-state energy and
prime-strip ledgers for sign-changing collar gauges (`markovEnergy_eq_signedCollarGauge`,
`signedCollar_primeJump_add_potential_eq`), prime-shift subsolution escape via negative collar
values, bilateral net prime-autocorrelation positivity (`netPrimeStripBalance_nonneg_of_odd_nonneg_on_Ici`),
complete resolution of the `edgeTentOdd` `thinBand` sharing obstruction
(`sum_thinBand_netPrimeStripBalance_edgeTentOdd_eq_zero`), and the exact screw-resonant zero-form
ledger across the plastic threshold `screwSignThreshold = Real.log plasticRoot`
(`fullZeroForm_odd_eq_screwResonantLedger`).

See `GaloisForLFunctions/SignChangingScrewGauge/README.md` for the module ledger and theorem
summary.
-/
