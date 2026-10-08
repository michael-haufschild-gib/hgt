import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorInversionDecay
import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorFourierBoundary
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The complete moving Fourier pairing limit

The spatial compact-test limit is dominated uniformly in frequency by the
inverse-square estimate. The original cubic datum supplies the summable weighted
coefficients. Identifying this pairing with the actual inverted Maass integral,
including its constant term, is a separate transport step.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.WeilHigherDenominator

/-- The inverted boundary cosine coefficient before the change of variables. -/
def inversionCosineBoundaryPairing (φ : ℝ → ℂ) (a b k : ℝ) : ℂ :=
  ∫ x in a..b, (Real.cos (2 * Real.pi * k * x⁻¹) : ℂ) * (φ x * (x⁻¹ : ℝ))

private lemma eventually_inversion_height {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y : ℝ in 𝓝[>] 0, y ∈ Ioc 0 δ ∧ Real.log y ≤ -1 := by
  have hy : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hy.eventually (Iio_mem_nhds hδ),
    Real.tendsto_log_nhdsGT_zero.eventually (eventually_le_atBot (-1))] with y hy0 hyδ hlog
  exact ⟨⟨hy0, hyδ.le⟩, hlog⟩

theorem tendsto_inversionBoundaryPhase {x : ℝ} (hx : 0 < x) :
    Tendsto (fun y => inversionBoundaryPhase y x) (𝓝[>] 0) (𝓝 x⁻¹) := by
  have hc : Continuous (fun y : ℝ => inversionBoundaryPhase y x) :=
    continuous_const.div (by fun_prop : Continuous (fun y : ℝ => x ^ 2 + y ^ 2))
      fun y => (inversionBoundaryDenom_pos hx y).ne'
  have h0 : inversionBoundaryPhase 0 x = x⁻¹ := by
    dsimp [inversionBoundaryPhase]
    field_simp [hx.ne']
    ring
  simpa only [h0] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- The fixed-mode spatial limit, using domination on the whole test interval. -/
theorem tendsto_inversionCosinePairing {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (inversionCosinePairing φ a b k) (𝓝[>] 0)
      (𝓝 (-inversionCosineBoundaryPairing φ a b k)) := by
  obtain ⟨δ, M, G, hδ, hM, hG, hδa, hbound⟩ :=
    exists_inversionAmplitude_jets_bound (b := b) hφ ha
  have hk0 := lt_of_lt_of_le zero_lt_one hk
  let f := fun y x => (Real.cos (2 * Real.pi * k * inversionBoundaryPhase y x) : ℂ) *
    inversionAmplitude φ k y x
  let g := fun x : ℝ => -((Real.cos (2 * Real.pi * k * x⁻¹) : ℂ) * (φ x * (x⁻¹ : ℝ)))
  have hmeas : ∀ᶠ y : ℝ in 𝓝[>] 0,
      AEStronglyMeasurable (f y) (volume.restrict (uIoc a b)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hA : ContinuousOn (inversionAmplitude φ k y) (uIcc a b) := by
      intro x hx
      exact (hasDerivAt_inversionAmplitude hφ hk0 hy
        (ha.trans_le (uIcc_of_le hab ▸ hx).1)).continuousAt.continuousWithinAt
    have hP : ContinuousOn (inversionBoundaryPhase y) (uIcc a b) := by
      intro x hx
      exact (hasDerivAt_inversionBoundaryPhase
        (ha.trans_le (uIcc_of_le hab ▸ hx).1) y).continuousAt.continuousWithinAt
    have hc : ContinuousOn (f y) (uIcc a b) := by dsimp [f]; fun_prop
    exact hc.intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  have hdom : ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ᵐ x : ℝ, x ∈ uIoc a b → ‖f y x‖ ≤ M := by
    filter_upwards [eventually_inversion_height hδ] with y hy
    filter_upwards [] with x hx
    have hxcc : x ∈ Icc a b := uIcc_of_le hab ▸ uIoc_subset_uIcc hx
    have h := (hbound y hy.1 hy.2 k hk x hxcc).1
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * ‖inversionAmplitude φ k y x‖ :=
        mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)
      _ ≤ M := by simpa using h
  have hlim : ∀ᵐ x : ℝ, x ∈ uIoc a b → Tendsto (fun y => f y x) (𝓝[>] 0) (𝓝 (g x)) := by
    filter_upwards [] with x hx
    have hx0 : 0 < x := ha.trans_le (uIcc_of_le hab ▸ uIoc_subset_uIcc hx).1
    have hw := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inversion_weighted_scaledKLog hx0 hk0)
    have hp := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_cos.continuousAt.tendsto.comp
        ((tendsto_inversionBoundaryPhase hx0).const_mul (2 * Real.pi * k)))
    have ht := hp.mul (hw.const_mul (φ x))
    convert ht using 1 <;>
      simp only [f, g, inversionAmplitude, inversionTestWeight, Function.comp_def,
        ofReal_mul, ofReal_neg, mul_assoc, mul_neg]
  have ht := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => M) hmeas hdom intervalIntegrable_const hlim
  change Tendsto (fun y => inversionCosinePairing φ a b k y) _ _
  simpa only [inversionCosinePairing, inversionCosineBoundaryPairing, f, g,
    intervalIntegral.integral_neg] using ht

/-- Dominated convergence through the complete infinite moving Fourier pairing. -/
theorem tendsto_inversionFourierPairing {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (fun y : ℝ => ∑' n : ℕ, q (n + 1) * inversionCosinePairing φ a b (n + 1) y)
      (𝓝[>] 0) (𝓝 (-∑' n : ℕ, q (n + 1) * inversionCosineBoundaryPairing φ a b (n + 1))) := by
  obtain ⟨δ, C, hδ, hC, hdecay⟩ := exists_inversionCosinePairing_decay hφ ha hab hs
  have hlim (n : ℕ) : Tendsto (fun y : ℝ =>
      q (n + 1) * inversionCosinePairing φ a b (n + 1) y) (𝓝[>] 0)
        (𝓝 (-(q (n + 1) * inversionCosineBoundaryPairing φ a b (n + 1)))) := by
    have hn : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    simpa only [mul_neg] using (tendsto_inversionCosinePairing hφ ha hab hn).const_mul (q (n + 1))
  have hdom : ∀ᶠ y : ℝ in 𝓝[>] 0, ∀ n : ℕ,
      ‖q (n + 1) * inversionCosinePairing φ a b (n + 1) y‖ ≤
        (‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) * C := by
    filter_upwards [eventually_inversion_height hδ] with y hy
    intro n
    have hn : 1 ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have h := mul_le_mul_of_nonneg_left (hdecay y hy.1 hy.2 (n + 1) hn)
      (norm_nonneg (q (n + 1)))
    rw [norm_mul]
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc, div_mul_eq_mul_div,
      mul_comm C] using h
  simpa only [tsum_neg] using tendsto_tsum_of_dominated_convergence (hq.mul_right C) hlim hdom

/-- The original cubic correspondence pays every coefficient hypothesis of the moving limit. -/
theorem degreeTwoQuotient_tendsto_inversionFourierPairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hs : tsupport φ ⊆ Ioo a b) :
    Tendsto (fun y : ℝ => ∑' n : ℕ,
      degreeTwoQuotientCoeff g (n + 1) * inversionCosinePairing φ a b (n + 1) y)
      (𝓝[>] 0) (𝓝 (-∑' n : ℕ,
        degreeTwoQuotientCoeff g (n + 1) * inversionCosineBoundaryPairing φ a b (n + 1))) :=
  tendsto_inversionFourierPairing (degreeTwoQuotientCoeff_summable_shift_square hD) hφ ha hab hs

end RHTower.WeilHigherDenominator
