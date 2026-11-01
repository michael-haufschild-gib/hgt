import GaloisForLFunctions.HodgeTheoryWithoutVarieties.StarsAreLowerHorizons
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheLiouvilleGaugeFlipsThePolarDivergence
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleIsTheTopOfThePrimeForm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheSpectralGapOfThePrimeFormIsTwoLogTwo

/-!
# The depth of a star is its energy

The renormalized prime form `R_N(x) = (log N − γ)|x|² − P_N(x)` restricted to the star of `d` is
the renormalized form of the lower horizon `⌊N/d⌋` plus the boundary flux `log N − log ⌊N/d⌋ ≥
log d` times the mass (`renormalizedPrimeForm_starRestrict`). The lower-horizon form is bounded
below uniformly (RAPT's spectrum ends), and asymptotically it is `≥ −ε` (the pole is the top of the
prime form). Hence:

* **depth coercivity** (`renormalizedPrimeForm_starRestrict_ge`): on the star of `d`, at every
  horizon `N ≥ d`, `R_N ≥ (log d − C₀)|x|²` with the absolute constant `C₀ = γ + log 4 + 4`;
* **sharp depth law** (`eventually_renormalizedPrimeForm_starRestrict_ge`): for every `ε > 0`, once
  `⌊N/d⌋` is large, `R_N ≥ (log d − ε)|x|²` on the star of `d`;
* **primitive depth law** (`eventually_renormalizedPrimeForm_starRestrict_ge_primitive`): on
  vectors of the star whose pullback is pole-orthogonal at the lower horizon,
  `R_N ≥ (log d + 2 log 2 − ε)|x|²`.

Depth in the divisor lattice costs exactly `log d`, the Ramanujan energy `log m` of a conductor read
on the dual side. The renormalized prime form is locally Hodge–Riemann on every star of depth
`d > e^{C₀}`, with a margin that grows with the depth. Its only possible negative directions live
across the shallow stars. There the counterterm flux is small and the gluing between stars decides
the sign.
-/

noncomputable section

open Finset
open GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-- The absolute depth constant `C₀ = γ + log 4 + 4`. -/
def depthConstant : ℝ := Real.eulerMascheroniConstant + (Real.log 4 + 4)

/-- The renormalized prime form is bounded below by `−C₀` times the mass at every horizon. -/
theorem renormalizedPrimeForm_ge {M : ℕ} (hM : 1 ≤ M) (y : ℕ → ℝ) :
    -depthConstant * ∑ a ∈ Icc 1 M, y a ^ 2 ≤ renormalizedPrimeForm M y := by
  have h := (atomicWeilForm_spectrum_ends hM).1 y
  rw [renormalizedPrimeForm, depthConstant]
  have := (abs_le.mp h).2
  nlinarith

/-- **Depth coercivity.** On the star of `d`, at every horizon `N ≥ d`, the renormalized prime form
is at least `(log d − C₀)` times the mass. -/
theorem renormalizedPrimeForm_starRestrict_ge {d N : ℕ} (hd : 0 < d) (hdN : d ≤ N) (x : ℕ → ℝ) :
    (Real.log d - depthConstant) * ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 ≤
      renormalizedPrimeForm N (starRestrict d x) := by
  rw [renormalizedPrimeForm_starRestrict hd, sum_sq_starRestrict hd]
  have hM : 1 ≤ N / d := Nat.div_pos hdN hd
  have h1 := renormalizedPrimeForm_ge hM (starPullback d x)
  have h2 := log_le_log_sub_log_div hd hdN
  have hmass : 0 ≤ ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- **The sharp depth law.** For every `ε > 0` there is `M₀` such that on the star of every `d` with
`⌊N/d⌋ ≥ M₀` the renormalized prime form is at least `(log d − ε)` times the mass. -/
theorem eventually_renormalizedPrimeForm_starRestrict_ge {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ d N : ℕ, 0 < d → d ≤ N → M₀ ≤ N / d → ∀ x : ℕ → ℝ,
      (Real.log d - ε) * ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 ≤
        renormalizedPrimeForm N (starRestrict d x) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atomicWeilForm_le_sharp hε
  refine ⟨M₀, fun d N hd hdN hM x => ?_⟩
  rw [renormalizedPrimeForm_starRestrict hd, sum_sq_starRestrict hd, renormalizedPrimeForm]
  have h1 := hM₀ (N / d) hM (starPullback d x)
  have h2 := log_le_log_sub_log_div hd hdN
  have hmass : 0 ≤ ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- **The primitive depth law.** On vectors of the star of `d` whose pullback is orthogonal to the
pole of the lower horizon, the renormalized prime form is at least `(log d + 2 log 2 − ε)` times
the mass once `⌊N/d⌋` is large. -/
theorem eventually_renormalizedPrimeForm_starRestrict_ge_primitive {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ d N : ℕ, 0 < d → d ≤ N → M₀ ≤ N / d → ∀ x : ℕ → ℝ,
      ∑ a ∈ Icc 1 (N / d), starPullback d x a / Real.sqrt a = 0 →
      (Real.log d + 2 * Real.log 2 - ε) * ∑ n ∈ Icc 1 N, starRestrict d x n ^ 2 ≤
        renormalizedPrimeForm N (starRestrict d x) := by
  obtain ⟨M₀, hM₀⟩ := eventually_atomicWeilForm_le_two_log_two hε
  refine ⟨M₀, fun d N hd hdN hM x hprim => ?_⟩
  rw [renormalizedPrimeForm_starRestrict hd, sum_sq_starRestrict hd, renormalizedPrimeForm]
  have h1 := hM₀ (N / d) hM (starPullback d x) hprim
  have h2 := log_le_log_sub_log_div hd hdN
  have hmass : 0 ≤ ∑ a ∈ Icc 1 (N / d), starPullback d x a ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
