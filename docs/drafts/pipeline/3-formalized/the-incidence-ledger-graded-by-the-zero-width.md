# Weil positivity is stable, and the incidence ledger is graded by the zero width

- **ID:** graded-incidence-ledger
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `formal/GaloisForLFunctions/ArithmeticIncidencePositivity/README.md` mechanism 43 and
  research topic 6 (paying the ledger past the windows); the unit list of the shared-target section
  ("Identities, finite classifications and nonselective positivity count as zero in these units").
- **Statement (headline):** The sign in Weil's criterion may be replaced by any **subexponential**
  bound in the aperture: if for every `σ > 0` some constant gives `Ẑ(F) ≥ −C_σ e^{2σ r}∫F²` on odd
  `C²_c` tests of aperture `r`, then RH holds; in particular a single constant defect
  `Ẑ(F) ≥ −C∫F²` suffices.  Consequently a graded global incidence allocation at rate `2σ` — the costs and the pole may
  exceed the pool, the crossing potential, the gains and the remainder by `C e^{2σr}∫F²` at
  aperture `r` — gives the zero-free strip `Θ ≤ ½ + σ`; at rate `0` an **arbitrary constant**
  deficit `C∫F²` at every aperture still gives RH.

## Goal
`ArithmeticIncidencePositivity` mechanism 43 is an exact identity plus a sign:
`forall_odd_fullZeroForm_nonneg_iff_globalIncidenceAllocation` says RH is the allocation condition
at every aperture, and the AIP README is explicit that the ledger "counts as zero" in the shared
units — a partial result on it certifies no aperture, no lag, no exponent. Two things change here.

1. **The exactness of the sign is unnecessary.** The allocation may fail by an absolute constant
   times the mass, at *every* aperture, and RH still follows
   (`riemannHypothesis_of_gradedIncidenceAllocation_zero`, with no sign condition on `C`). So the
   criterion that must be proved is strictly weaker than the one stated: what is needed is a
   *bounded* deficit, not a nonpositive one.
2. **The ledger acquires a value in the width unit.** An estimate of the deficit at rate `2σ` is
   the explicit exponent `Θ ≤ ½ + σ` (`zetaZeroWidth_le_of_gradedIncidenceAllocation`). Partial
   quantitative work on the ledger is therefore scoreable in the shared unit, exactly as the
   partial damping continuation of `ArithmeticContinuationAndCriticalEnergy` scores
   `Θ ≤ ½ + a₀`. The exact sign is the endpoint `σ = 0`, `C = 0` of a one-parameter family.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (composition of four owned theorems; see Approach)
- [x] 2 → 3  formalized:
  `formal/GaloisForLFunctions/SquareRootThreshold/TheIncidenceLedgerGradedByTheZeroWidth.lean`,
  wired into `GaloisForLFunctions.SquareRootThreshold`; all three capstones depend only on
  `propext, Classical.choice, Quot.sound`.
- [ ] 3 → 4  publication-ready

## Approach
The difference tests of the lag family are the bridge, and every step is owned:

* the test `f_{w,v} = κ_w(·+v/2) − κ_w(·−v/2)` is odd (`twoBump_modScaledBump_zero_neg`), `C²`,
  and supported in `[−(v/2+w), v/2+w]` (`tsupport_twoBump_modScaledBump_subset`), so the graded
  floor applies to its real and imaginary parts at aperture `r = v/2 + w`;
* the two parts reassemble into the Weil form (`zeta_W_re_eq_fullZeroForm_re_add_im`) and the mass
  is `∫‖f‖² = 2∫‖κ_w‖²` (`integral_norm_sq_twoBump_modScaledBump_eq`);
* the Weil form of the test is its lag functional (`zeta_W_eq_literatureRHS`,
  `literatureRHS_twoBump_eq_lagPrimeWindowRHS`);
* the zero width is exactly the exponential rate at which the lag family may go negative
  (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`), for every width outside a countable set
  (`exists_mem_Ioo_notMem_of_countable`).

The arithmetic of the exponents is exact: the aperture rate `e^{2σ(v/2+w)}` is the lag rate
`e^{σv}` times the constant `e^{2σw}`, so an aperture-graded floor is a lag-graded floor at half
the exponent — which is the width. The ledger identity `fullZeroForm_eq_incidenceLedger` then
rewrites the floor as the graded allocation, with the plateau radius taken as `r + 1`.

## Stability of the criterion
`riemannHypothesis_of_odd_fullZeroForm_bddBelow` and `riemannHypothesis_of_subexponential_odd_floor`
are the headline: exact positivity is not what has to be proved.  A positivity problem — which
needs a sign mechanism, and for which the corpus proves criticality in three senses (no Hardy
weight, rate-criticality, variance-criticality: "no slack anywhere") — becomes an **estimation**
problem that may lose any polynomial or logarithmic factor in the aperture.  The criticality
statements are not contradicted: they say no positive weight can be subtracted while keeping the
sign; the stability here says a negative subexponential allowance keeps the *conclusion*.

## Lean (unconditional, standard axioms only)
- `riemannHypothesis_of_odd_fullZeroForm_bddBelow` — Weil positivity up to one constant is Weil
  positivity.
- `riemannHypothesis_of_subexponential_odd_floor` — any subexponential-in-aperture defect suffices.
- `zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor` — an odd-sector floor `Ẑ(F) ≥ −Ce^{2σr}∫F²`
  at every aperture gives `zetaZeroWidth ≤ σ`. No sign condition on `C`.
- `zetaZeroWidth_le_half_mul_of_subTrivial_odd_floor` — **the target, sharply**: the trivial floor
  is at rate exactly `1`, being the `ℓ¹` norm `Σ_{n ≤ e^{2r}}Λ(n)n^{−1/2} ≍ 2e^{r}` of the prime
  side (`RHTower.aperturePrimeSum_le_four_mul_mul_exp`, which is why
  `polarWindowFloor` gives only the trivial width `½`); a floor at any rate `θ < 1`, i.e. **any
  power saving on the prime side uniform in the height**, is the fixed zero-free strip
  `Θ ≤ 1 − (1−θ)/2`.
- `zetaZeroWidth_le_of_graded_odd_zeroForm_floor` — the same for the gauge-invariant zero form,
  hence for the signed jump energy plus the variance of mechanism 1 in any smeared gauge
  (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`,
  `fullZeroForm_eq_zeroForm_of_odd`) and for ACT's pole-free variation inequality
  (`poleFreeForm_eq_zeroForm`): the prime-side inequality of mechanism 1 has slack after all, and
  the slack costs exactly an exponent.
- `GradedIncidenceAllocation` — the graded allocation condition at rate `2σ`.
- `zetaZeroWidth_le_of_gradedIncidenceAllocation` — the ledger in the width unit.
- `riemannHypothesis_of_gradedIncidenceAllocation_zero` — a constant-deficit allocation is RH.

## Why only the odd sector is needed
The corpus already grades the aperture face's *ground energy*
(`zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`), but `μ(A)` is an infimum over
sources of **both** parities, so that route needs the even sector, which is exactly where ACT and
AIP are blocked between `3/10` and `½ log 2`. The route here goes through the odd difference tests
of the lag family instead, so an odd-sector floor alone suffices — which is what makes it apply to
AIP's ledger and to the jump form, both of which are defined on odd tests.

## Units
The contribution is the gradation: an allocation estimate at rate `2σ` reports the strip
`Θ ≤ ½ + σ`. The windows of AIP mechanisms 23–35 and 40 are the case `σ = 0`, `C = 0` restricted
to a bounded aperture, and remain worth zero in the width unit; what is now scoreable is a deficit
estimate valid at *every* aperture, however large its rate.

## What it does not prove
No bound on the deficit. At large aperture the costs are `≍ e^{r}` (the prime side's ℓ¹ norm) and so
are the gains and the pole, so a deficit estimate at any rate below `1` is a statement about the
second-order balance between the prime and polar sides — the square-root barrier. The gradation
says what an estimate is worth, not that one exists.

## Log
- 2026-10-22 — created at stage 3; module written, compiled, wired into `SquareRootThreshold`.
