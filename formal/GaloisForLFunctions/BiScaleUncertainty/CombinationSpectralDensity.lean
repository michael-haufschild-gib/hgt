import GaloisForLFunctions.RHTower.BlindSymbolSlackPrimePowerPeriodization
import GaloisForLFunctions.BiScaleUncertainty.PoleInvisibilityOnGappedBlindGrids

/-!
# The spectral density of a nonnegative combination of Weil tests

For a combination `c` put `G_c(r) = Σ_f c_f |f̂(r)|²`. Then

* `∫ G_c = 2π mass(c)`;
* `∫ G_c γ = 2π A(c)`, with `A(c)` the archimedean part without the pole;
* `∫ G_c(r) cos(r log n) dr = π√n · (node value of c at n)`;
* if `c` is blind at every power of `q`, the phase `r log q mod 2π` of `G_c` is uniform for even
  observables: `∫ G_c P(phase) = (∫ G_c) · ∫ P` for every even continuous `P` on the circle.

These are the spectral coordinates in which blind symbol slack becomes a moment problem.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided RHTower.PrimeCirclePeriodization RHTower.BlindPrimePowerSlack
local notation "π" => Real.pi

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

/-- The powers `q^j`, `j ≥ 1`. -/
abbrev powerNodes (q : ℕ) : Set ℕ := {n | ∃ j : ℕ, 1 ≤ j ∧ n = q ^ j}

/-- The spectral density `G_c(r) = Σ_f c_f |f̂(r)|²`. -/
def combinationSpectralDensity (c : WeilTestFn →₀ ℝ) (r : ℝ) : ℝ :=
  ∑ f ∈ c.support, c f * ‖paperFT f.1 r‖ ^ 2

theorem continuous_combinationSpectralDensity (c : WeilTestFn →₀ ℝ) :
    Continuous (combinationSpectralDensity c) :=
  continuous_finsetSum _ fun f _ => continuous_const.mul (continuous_normSq_paperFT f)

theorem combinationSpectralDensity_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (r : ℝ) :
    0 ≤ combinationSpectralDensity c r :=
  Finset.sum_nonneg fun f _ => mul_nonneg (hc f) (by positivity)

theorem integrable_combinationSpectralDensity (c : WeilTestFn →₀ ℝ) :
    Integrable (combinationSpectralDensity c) :=
  integrable_finsetSum _ fun f _ => (integrable_normSq_paperFT f).const_mul _

theorem combinationSpectralDensity_mul_eq (c : WeilTestFn →₀ ℝ) (F : ℝ → ℝ) :
    (fun r => combinationSpectralDensity c r * F r) =
      fun r : ℝ => ∑ f ∈ c.support, c f * (‖paperFT f.1 r‖ ^ 2 * F r) := by
  ext r
  simp only [combinationSpectralDensity, Finset.sum_mul]
  exact Finset.sum_congr rfl fun f _ => by ring

theorem integrable_combinationSpectralDensity_mul_gammaBracket (c : WeilTestFn →₀ ℝ) :
    Integrable fun r => combinationSpectralDensity c r * EF.gammaBracket r := by
  rw [combinationSpectralDensity_mul_eq]
  exact integrable_finsetSum _ fun f _ =>
    (integrable_normSq_paperFT_mul_gammaBracket f).const_mul _

theorem integral_combinationSpectralDensity (c : WeilTestFn →₀ ℝ) :
    ∫ r, combinationSpectralDensity c r = 2 * π * massOf c := by
  rw [show combinationSpectralDensity c = fun r : ℝ => ∑ f ∈ c.support, c f * ‖paperFT f.1 r‖ ^ 2
    from rfl, integral_finsetSum _ fun f _ => (integrable_normSq_paperFT f).const_mul _]
  simp_rw [integral_const_mul, integral_normSq_paperFT_eq]
  rw [massOf, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- The `γ`-moment is `2π` times the archimedean part without the pole. -/
theorem integral_combinationSpectralDensity_mul_gammaBracket (c : WeilTestFn →₀ ℝ) :
    ∫ r, combinationSpectralDensity c r * EF.gammaBracket r = 2 * π * nodeArchOnly c := by
  rw [combinationSpectralDensity_mul_eq, integral_finsetSum _ fun f _ =>
    (integrable_normSq_paperFT_mul_gammaBracket f).const_mul _]
  simp_rw [integral_const_mul]
  rw [nodeArchOnly, nodeArchEnergy_eq, nodePoleMass, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [smul_eq_mul]
  rw [← mul_sub, weilArchRe_sub_pole_eq]
  field_simp

/-- The cosine moment at `log n` is the node value at `n`. -/
theorem integral_normSq_paperFT_mul_cos_log (f : WeilTestFn) {n : ℕ} (hn : 1 ≤ n) :
    ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * Real.cos (r * Real.log n) =
      π * Real.sqrt n * logValue f.1 n := by
  obtain ⟨a, ha⟩ := exists_Icc_support f
  rw [integral_normSq_paperFT_mul_cos_eq f.2.1 ha, logValue]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  field_simp

theorem integral_combinationSpectralDensity_mul_cos_log (c : WeilTestFn →₀ ℝ) {n : ℕ}
    (hn : 2 ≤ n) :
    ∫ r, combinationSpectralDensity c r * Real.cos (r * Real.log n) =
      π * Real.sqrt n * nodeVector c ⟨n, hn⟩ := by
  rw [combinationSpectralDensity_mul_eq, integral_finsetSum _ fun f _ => by
    simpa [mul_assoc] using ((integrable_normSq_paperFT_mul_cos f.2.1
      (exists_Icc_support f).choose_spec (Real.log n)).const_mul (c f))]
  simp_rw [integral_const_mul, integral_normSq_paperFT_mul_cos_log _ (by omega : 1 ≤ n)]
  rw [nodeVector_eq, linearCombination_logVector_apply, Finsupp.sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun f _ => by ring

/-- **Uniform phase.** Blindness at every power of `q` makes the phase `r log q mod 2π` of the
spectral density uniform for even continuous observables. -/
theorem integral_combinationSpectralDensity_mul_periodic {q : ℕ} (hq : 2 ≤ q)
    {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (hb : BlindOn (powerNodes q) c)
    {P : AddCircle (2 * π) → ℝ} (hP : Continuous P) (heven : ∀ z, P (-z) = P z) :
    ∫ r, combinationSpectralDensity c r * P (phase (Real.log q) r) =
      (∫ r, combinationSpectralDensity c r) * ∫ z, P z ∂AddCircle.haarAddCircle := by
  refine integral_mul_periodic_eq_of_cos_blind (continuous_combinationSpectralDensity c)
    (combinationSpectralDensity_nonneg hc) (integrable_combinationSpectralDensity c)
    (fun j hj => ?_) hP heven
  have hqj : 2 ≤ q ^ j := le_trans hq (Nat.le_self_pow (by omega) q)
  have hlog : (j : ℝ) * Real.log q = Real.log ((q ^ j : ℕ) : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  rw [hlog, integral_combinationSpectralDensity_mul_cos_log c hqj, hb ⟨q ^ j, hqj⟩ ⟨j, hj, rfl⟩,
    mul_zero]

/-- The circle mean of an observable of the folded radius `‖z‖/ℓ`. -/
theorem integral_haarAddCircle_norm_comp {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ z : AddCircle (2 * π), F (‖z‖ / ℓ) ∂AddCircle.haarAddCircle =
      ℓ / π * ∫ v in (0 : ℝ)..π / ℓ, F v := by
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hpre := AddCircle.intervalIntegral_preimage (2 * π) (-π)
    (fun z : AddCircle (2 * π) => F (‖z‖ / ℓ))
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hpi.le, show -π + 2 * π = π by ring] at hpre
  have hcongr : ∫ a in (-π)..π, F (‖(a : AddCircle (2 * π))‖ / ℓ) =
      ∫ a in (-π)..π, F (|a| / ℓ) := by
    refine intervalIntegral.integral_congr fun a ha => ?_
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at ha
    rw [(AddCircle.norm_coe_eq_abs_iff (2 * π) hpi.ne').mpr]
    rw [abs_of_pos hpi]
    exact abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hc : Continuous fun a : ℝ => F (|a| / ℓ) := hF.comp (continuous_abs.div_const ℓ)
  have hsplit : ∫ a in (-π)..π, F (|a| / ℓ) = 2 * ∫ a in (0 : ℝ)..π, F (a / ℓ) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h1 : ∫ a in (-π)..0, F (|a| / ℓ) = ∫ a in (0 : ℝ)..π, F (a / ℓ) := by
      have := intervalIntegral.integral_comp_neg (a := 0) (b := π) (fun a => F (|a| / ℓ))
      simp only [abs_neg, neg_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun a ha => ?_
      rw [Set.uIcc_of_le Real.pi_pos.le] at ha
      simp only [abs_of_nonneg ha.1]
    have h2 : ∫ a in (0 : ℝ)..π, F (|a| / ℓ) = ∫ a in (0 : ℝ)..π, F (a / ℓ) := by
      refine intervalIntegral.integral_congr fun a ha => ?_
      rw [Set.uIcc_of_le Real.pi_pos.le] at ha
      simp only [abs_of_nonneg ha.1]
    rw [h1, h2]; ring
  have hsub : ∫ a in (0 : ℝ)..π, F (a / ℓ) = ℓ * ∫ v in (0 : ℝ)..π / ℓ, F v := by
    rw [intervalIntegral.integral_comp_div (fun v => F v) hℓ.ne', zero_div, smul_eq_mul]
  rw [hcongr, hsplit, hsub] at hpre
  have : ∫ z : AddCircle (2 * π), F (‖z‖ / ℓ) ∂AddCircle.haarAddCircle =
      (2 * (ℓ * ∫ v in (0 : ℝ)..π / ℓ, F v)) / (2 * π) := by
    rw [hpre, smul_eq_mul]; field_simp
  rw [this]; field_simp

end

end GaloisForLFunctions.BiScaleUncertainty
