import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitnessTheorem
import GaloisForLFunctions.RHTower.XiGaussianHeatWindowFromWeilMargin

/-!
# The heat Hankel window threshold law

`HeatWindowNonneg K`: for all large `n`, the heat Hankel form `H_{K/n}(P, P)` has nonnegative real
part on every real polynomial of degree `≤ n` vanishing at the pole node `w = −1/4`.

`EvenPoleWeilNonneg A`: every smooth even real source vanishing outside `[−A, A]` with
`∫ u e^{x/2} = 0` has nonnegative zero-side Weil energy `Re Σ_q F_u(z_q)²`.

* `evenPoleWeilNonneg_of_heatWindowNonneg`: `HeatWindowNonneg K` forces `EvenPoleWeilNonneg A` for
  every `A² < 4K` (the sharp witness).
* `heatWindowNonneg_of_polarGroundEnergy_pos`: a positive pole-vanishing ground energy at aperture
  `A` forces `HeatWindowNonneg K` for every `4K < A²`.
* `heatWindowNonneg_threshold`: if the pole-vanishing ground energy is positive below an aperture
  `A` and even pole-vanishing sources of negative energy exist above it, then the window
  constant is exactly `A²/4`: windows `K < A²/4` are nonnegative and windows `K > A²/4` are not.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- Heat Hankel nonnegativity on the pole hyperplane in the window `aN = K`. -/
def HeatWindowNonneg (K : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ P : ℝ[X], P.natDegree ≤ n → P.eval (-1 / 4) = 0 →
    0 ≤ (heatHankel (K / n) (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ))).re

/-- Nonnegative zero-side Weil energy on smooth even pole-vanishing sources of half-width `A`. -/
def EvenPoleWeilNonneg (A : ℝ) : Prop :=
  ∀ u : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → (∀ t : ℝ, A < |t| → u t = 0) →
    (∀ x, u (-x) = u x) → ∫ x, u x * Real.exp (x / 2) = 0 →
      0 ≤ (∑' q : XiZeroCopy, heatStripTransform (fun x => ((u x : ℝ) : ℂ))
        (xiSpectralPoint q) ^ 2).re

/-- **Sharp witness, contrapositive.**  A nonnegative window `K` forces nonnegative even
pole-vanishing Weil energy at every half-width `A` with `A² < 4K`. -/
theorem evenPoleWeilNonneg_of_heatWindowNonneg {K : ℝ} (hK0 : 0 < K) (hW : HeatWindowNonneg K)
    {A : ℝ} (hA : A ^ 2 < 4 * K) : EvenPoleWeilNonneg A := by
  intro u hu hcpt hsupp heven hpole
  by_contra hneg
  obtain ⟨n, ⟨P, hPd, hPe, hP⟩, hn⟩ :=
    ((eventually_exists_poleHyperplane_heatHankel_neg_of_source hu hcpt hsupp heven hpole
      (lt_of_not_ge hneg) hK0 hA).and hW).exists
  exact (lt_irrefl _ (hP.trans_le (hn P hPd hPe)))

/-- **Weil margin side.**  A positive pole-vanishing ground energy at aperture `A` makes every
window `K < A²/4` nonnegative. -/
theorem heatWindowNonneg_of_polarGroundEnergy_pos {A : SuzukiPositiveAperture}
    (hμ : 0 < ccmRestrictedWeilPolarGroundEnergy A) {K : ℝ} (hK0 : 0 < K)
    (hKA : 4 * K < A.1 ^ 2) : HeatWindowNonneg K := by
  filter_upwards [eventually_le_re_heatHankel_of_polarGroundEnergy hμ hK0 hKA,
    eventually_gt_atTop 0] with n hn hn0 P hPd hPe
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have h := hn (K / n) (div_pos hK0 hn') le_rfl P hPd hPe
  have hV : 0 ≤ ∫ x, heatTest (K / n) P x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact (mul_nonneg (div_nonneg hμ.le (by norm_num)) hV).trans h

/-- **The window threshold law.**  If the pole-vanishing ground energy is positive at every
aperture below `A` and every half-width above `A` carries an even pole-vanishing source of negative
Weil energy, then the heat Hankel window constant is exactly `A²/4`. -/
theorem heatWindowNonneg_threshold {A : ℝ} (hA : 0 < A)
    (hpos : ∀ A' : SuzukiPositiveAperture, A'.1 < A → 0 < ccmRestrictedWeilPolarGroundEnergy A')
    (hneg : ∀ A' : ℝ, A < A' → ¬ EvenPoleWeilNonneg A') {K : ℝ} (hK0 : 0 < K) :
    (4 * K < A ^ 2 → HeatWindowNonneg K) ∧ (A ^ 2 < 4 * K → ¬ HeatWindowNonneg K) := by
  have hs := Real.sqrt_nonneg (4 * K)
  have hs2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * K)
  refine ⟨fun hKA => ?_, fun hKA hW => ?_⟩
  · have hsA : Real.sqrt (4 * K) < A := by
      rw [← Real.sqrt_sq hA.le]; exact Real.sqrt_lt_sqrt (by positivity) hKA
    have hmid : 0 < (Real.sqrt (4 * K) + A) / 2 := by linarith only [hs, hA]
    refine heatWindowNonneg_of_polarGroundEnergy_pos (A := ⟨(Real.sqrt (4 * K) + A) / 2, hmid⟩)
      (hpos _ (by change (Real.sqrt (4 * K) + A) / 2 < A; linarith only [hsA])) hK0 ?_
    change 4 * K < ((Real.sqrt (4 * K) + A) / 2) ^ 2
    have h1 : Real.sqrt (4 * K) < (Real.sqrt (4 * K) + A) / 2 := by linarith only [hsA]
    have h2 := pow_lt_pow_left₀ h1 hs two_ne_zero
    rwa [hs2] at h2
  · have hAs : A < Real.sqrt (4 * K) := by
      rw [← Real.sqrt_sq hA.le]; exact Real.sqrt_lt_sqrt (by positivity) hKA
    have h1 : (A + Real.sqrt (4 * K)) / 2 < Real.sqrt (4 * K) := by linarith only [hAs]
    have h0 : 0 ≤ (A + Real.sqrt (4 * K)) / 2 := by linarith only [hs, hA]
    have h2 := pow_lt_pow_left₀ h1 h0 two_ne_zero
    rw [hs2] at h2
    exact hneg _ (by linarith only [hAs]) (evenPoleWeilNonneg_of_heatWindowNonneg hK0 hW h2)

end

end RHTower
