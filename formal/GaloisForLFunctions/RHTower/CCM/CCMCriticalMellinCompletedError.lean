import GaloisForLFunctions.RHTower.PolarPrimeMellinDefect

/-!
# The completed critical-Mellin error as a Chebyshev potential

The square-root main terms in the polar and von Mangoldt channels cancel exactly.  What remains
is a normalized potential of the genuine Chebyshev error `psi(X) - X`.  Consequently the
equal-scale adjacent-block coefficient used by the rectangular RH detector is exactly a Haar
coefficient of this Chebyshev potential.

This is an unconditional source identity.  It does not assert the remaining one-sided subpower
estimate.
-/

open scoped BigOperators
open Finset MeasureTheory ArithmeticFunction Set

noncomputable section

namespace RHTower

/-- The completed critical-Mellin prime-polar error in logarithmic coordinates. -/
def criticalMellinCompletedError (h : ℝ) : ℝ :=
  4 * Real.sinh (h / 2) -
    ∑ k ∈ Icc 0 ⌊Real.exp h⌋₊,
      ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k

/-- The same completed error written entirely through the Chebyshev remainder. -/
def criticalMellinChebyshevPotential (h : ℝ) : ℝ :=
  1 - 2 / Real.sqrt (Real.exp h) -
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) /
      Real.sqrt (Real.exp h) -
    (1 / 2 : ℝ) * ∫ t in Ioc (1 : ℝ) (Real.exp h),
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
        t ^ (-3 / 2 : ℝ)

/-- The Chebyshev error normalized at the critical square-root scale and pulled back to the
logarithmic coordinate. -/
def criticalMellinNormalizedChebyshevError (h : ℝ) : ℝ :=
  criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp h) /
    Real.sqrt (Real.exp h)

/-- Logarithmic substitution in the critical Mellin primitive. -/
theorem criticalMellinError_integral_exp_substitution
    {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in Ioc (1 : ℝ) (Real.exp h),
      criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
        t ^ (-3 / 2 : ℝ)) =
      ∫ u in Ioc (0 : ℝ) h, criticalMellinNormalizedChebyshevError u := by
  let g : ℝ → ℝ := fun t =>
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) t *
      t ^ (-3 / 2 : ℝ)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := h) (f := Real.exp) (f' := Real.exp) (g := g)
    Real.continuous_exp.continuousOn
    (fun x _hx => Real.hasDerivAt_exp x)
    (fun x _hx => (Real.exp_pos x).le)
  rw [intervalIntegral.integral_of_le hh] at hsub
  simp only [Real.exp_zero] at hsub
  rw [intervalIntegral.integral_of_le (Real.one_le_exp hh)] at hsub
  rw [← hsub]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  rw [criticalMellinNormalizedChebyshevError]
  dsimp only [Function.comp_apply, g]
  have hu : 0 < Real.exp u := Real.exp_pos u
  have hweight :
      (Real.exp u) ^ (-3 / 2 : ℝ) * Real.exp u =
        1 / Real.sqrt (Real.exp u) := by
    nth_rewrite 2 [← Real.rpow_one (Real.exp u)]
    rw [← Real.rpow_add hu]
    rw [show (-3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hu.le, ← Real.sqrt_eq_rpow]
    simp [one_div]
  calc
    criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp u) *
          (Real.exp u) ^ (-3 / 2 : ℝ) * Real.exp u =
        criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp u) *
          ((Real.exp u) ^ (-3 / 2 : ℝ) * Real.exp u) := by ring
    _ = criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp u) *
          (1 / Real.sqrt (Real.exp u)) := by rw [hweight]
    _ = criticalMellinError (fun k => ArithmeticFunction.vonMangoldt k) (Real.exp u) /
          Real.sqrt (Real.exp u) := by ring

/-- Causal logarithmic Volterra form of the normalized Chebyshev potential. -/
def criticalMellinChebyshevVolterraPotential (h : ℝ) : ℝ :=
  1 - 2 / Real.sqrt (Real.exp h) - criticalMellinNormalizedChebyshevError h -
    (1 / 2 : ℝ) * ∫ u in Ioc (0 : ℝ) h,
      criticalMellinNormalizedChebyshevError u

/-- The critical Mellin potential is a fixed causal Volterra filter of the normalized Chebyshev
error on the logarithmic ray. -/
theorem criticalMellinChebyshevPotential_eq_volterraPotential
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinChebyshevPotential h =
      criticalMellinChebyshevVolterraPotential h := by
  rw [criticalMellinChebyshevPotential,
    criticalMellinChebyshevVolterraPotential,
    criticalMellinNormalizedChebyshevError,
    criticalMellinError_integral_exp_substitution hh]

/-- **Completed-error reduction.**  On the nonnegative logarithmic ray, the polar main term and
the critical von Mangoldt main term cancel exactly, leaving only the normalized Chebyshev error
and its critical Mellin primitive. -/
theorem criticalMellinCompletedError_eq_chebyshevPotential
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinCompletedError h = criticalMellinChebyshevPotential h := by
  have hX : 1 ≤ Real.exp h := Real.one_le_exp hh
  have hsum := vonMangoldt_criticalMellinError_identity (Real.exp h) hX
  have hpolar := polarMultiplier_zero_eq_sqrtExp (h / 2)
  rw [polarMultiplier_zero, show 2 * (h / 2) = h by ring] at hpolar
  rw [criticalMellinCompletedError, criticalMellinChebyshevPotential, hsum]
  linear_combination (1 / 2 : ℝ) * hpolar

/-- The completed prime-polar error is directly the causal Volterra transform of the normalized
Chebyshev error. -/
theorem criticalMellinCompletedError_eq_volterraPotential
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinCompletedError h =
      criticalMellinChebyshevVolterraPotential h := by
  rw [criticalMellinCompletedError_eq_chebyshevPotential hh,
    criticalMellinChebyshevPotential_eq_volterraPotential hh]

/-- Equal-scale adjacent logarithmic block imbalance of the completed error. -/
def criticalMellinAdjacentBlock (L x : ℝ) : ℝ :=
  (∫ h in Ioc (x - L) x, criticalMellinCompletedError h) -
    ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinCompletedError h

/-- The corresponding adjacent block imbalance after Chebyshev reduction. -/
def criticalMellinChebyshevAdjacentBlock (L x : ℝ) : ℝ :=
  (∫ h in Ioc (x - L) x, criticalMellinChebyshevPotential h) -
    ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinChebyshevPotential h

/-- Adjacent block imbalance of the causal logarithmic Volterra potential. -/
def criticalMellinChebyshevVolterraAdjacentBlock (L x : ℝ) : ℝ :=
  (∫ h in Ioc (x - L) x, criticalMellinChebyshevVolterraPotential h) -
    ∫ h in Ioc (x - 2 * L) (x - L),
      criticalMellinChebyshevVolterraPotential h

/-- **Adjacent-block Chebyshev law.**  Once both blocks lie on the nonnegative logarithmic ray,
the completed prime-polar Haar coefficient is exactly the Haar coefficient of the normalized
Chebyshev potential. -/
theorem criticalMellinAdjacentBlock_eq_chebyshevAdjacentBlock
    {L x : ℝ} (hL : 0 ≤ L) (hx : 2 * L ≤ x) :
    criticalMellinAdjacentBlock L x =
      criticalMellinChebyshevAdjacentBlock L x := by
  have hright :
      (∫ h in Ioc (x - L) x, criticalMellinCompletedError h) =
        ∫ h in Ioc (x - L) x, criticalMellinChebyshevPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_chebyshevPotential
    linarith [hhmem.1]
  have hleft :
      (∫ h in Ioc (x - 2 * L) (x - L), criticalMellinCompletedError h) =
        ∫ h in Ioc (x - 2 * L) (x - L), criticalMellinChebyshevPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_chebyshevPotential
    linarith [hhmem.1]
  rw [criticalMellinAdjacentBlock, criticalMellinChebyshevAdjacentBlock,
    hright, hleft]

/-- The same adjacent-block coefficient is exactly the fixed causal Volterra--Haar filter of the
normalized logarithmic Chebyshev error. -/
theorem criticalMellinAdjacentBlock_eq_volterraAdjacentBlock
    {L x : ℝ} (hL : 0 ≤ L) (hx : 2 * L ≤ x) :
    criticalMellinAdjacentBlock L x =
      criticalMellinChebyshevVolterraAdjacentBlock L x := by
  have hright :
      (∫ h in Ioc (x - L) x, criticalMellinCompletedError h) =
        ∫ h in Ioc (x - L) x,
          criticalMellinChebyshevVolterraPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_volterraPotential
    linarith [hhmem.1]
  have hleft :
      (∫ h in Ioc (x - 2 * L) (x - L), criticalMellinCompletedError h) =
        ∫ h in Ioc (x - 2 * L) (x - L),
          criticalMellinChebyshevVolterraPotential h := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hhmem
    apply criticalMellinCompletedError_eq_volterraPotential
    linarith [hhmem.1]
  rw [criticalMellinAdjacentBlock,
    criticalMellinChebyshevVolterraAdjacentBlock, hright, hleft]

/-- Logarithmic integer specialization of the adjacent-block Chebyshev law. -/
theorem criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : 2 * L ≤ Real.log n) :
    criticalMellinAdjacentBlock L (Real.log n) =
      criticalMellinChebyshevAdjacentBlock L (Real.log n) :=
  criticalMellinAdjacentBlock_eq_chebyshevAdjacentBlock hL hn

/-- The all-epsilon one-sided subpower problem for the completed adjacent blocks is literally the
same problem for the normalized Chebyshev potential.  This removes the polar main term and the
raw von Mangoldt sum from the remaining RH-bearing estimate without weakening its quantifiers. -/
theorem completedAdjacentBlock_subpowerLower_iff_chebyshevAdjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 2 * L ≤ Real.log n) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinAdjacentBlock L (Real.log n) + C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinChebyshevAdjacentBlock L (Real.log n) +
          C * (n : ℝ) ^ epsilon) := by
  constructor
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [← criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
      hL (hN n hn)]
    exact hlowerC n hn
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [criticalMellinAdjacentBlock_logSample_eq_chebyshevAdjacentBlock
      hL (hN n hn)]
    exact hlowerC n hn

/-- Fully local logarithmic form of the open estimate: the completed adjacent-block subpower
problem is equivalent, with unchanged quantifiers, to the same lower bound for the causal
Volterra--Haar filter of the normalized Chebyshev error. -/
theorem completedAdjacentBlock_subpowerLower_iff_volterraAdjacentBlock
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 2 * L ≤ Real.log n) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinAdjacentBlock L (Real.log n) + C * (n : ℝ) ^ epsilon) ↔
    (∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        0 ≤ criticalMellinChebyshevVolterraAdjacentBlock L (Real.log n) +
          C * (n : ℝ) ^ epsilon) := by
  constructor
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [← criticalMellinAdjacentBlock_eq_volterraAdjacentBlock hL (hN n hn)]
    exact hlowerC n hn
  · intro hlower epsilon hepsilon
    obtain ⟨C, hC, hlowerC⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    rw [criticalMellinAdjacentBlock_eq_volterraAdjacentBlock hL (hN n hn)]
    exact hlowerC n hn

end RHTower
