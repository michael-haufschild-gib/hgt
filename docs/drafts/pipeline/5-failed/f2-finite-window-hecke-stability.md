# Universal finite-window Hecke stability

- **Stage:** 5-failed
- **Claim rejected:** Every compact smooth window lift has compact Hecke output.
- **Exact obstruction:** At every stage `A≥log 2`, some smooth test has a nonzero first-prime germ and therefore a Hecke cusp tail with unbounded support, at every spectral parameter.
- **Strong positive survivor:** Exact tail formula, germ admission criterion, and sharp universal threshold `A<log 2`. Modular inversion recovers both tails from one germ.
- **New insight:** Zero endpoint value is insufficient; cusp admission depends on the entire one-sided germ.
- **Paper and Lean:** Complete and individually audited in [sharp Hecke cusp admission](../3-formalized/f2-sharp-hecke-cusp-admission.md), including `hecke_windowPeriodLift_finite_window_iff` and `hecke_windowPeriodLift_all_upper_cutoffs_iff`. Corrected F2 transport remains active.

**Additional positive survivor [K].** [Every finite word in the actual prime-two and prime-three Hecke operators preserves decaying finite-energy cusp admission](../3-formalized/f2-hecke-cusp-decay-carrier.md) for window lifts at every aperture when `Re s>0`. The paper proof and final Lean audit are complete. Compact-support failure therefore does not imply cusp-energy divergence.

**Whole-Haar boundary [K].** [The first image has finite whole-axis Haar energy iff `H(−log2)=0`](../3-formalized/f2-whole-haar-hecke-admission.md), for `Re s>0`. Universal admission holds exactly for `A≤log2`; the endpoint has a noncompact finite-energy example. Paper proof and individual Lean audit are complete.
