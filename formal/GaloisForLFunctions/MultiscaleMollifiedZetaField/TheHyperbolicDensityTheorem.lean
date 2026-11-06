import GaloisForLFunctions.MultiscaleMollifiedZetaField.OnlyComparablyDeepZerosCompete
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount

/-!
# The hyperbolic density theorem

Put a zero `ρ` in the half plane `Re s > ½` with its pseudo-hyperbolic ratios `ϱ(ρ, ρ') = |ρ − ρ'|/|ρ + ρ̄' − 1|` to the other zeros.

**Theorem** (`exists_card_hyperbolically_isolated_zeros_unconditional_le`). Fix `0 < c ≤ 1/60000` and write `x = (1−3c)α`, `L = log T`. For `2 ≤ x ≤ (3/2) c L`,
separated zeros of depth in `[α/L, (α+1)/L]` with

`Π_{ρ'} ϱ(ρ, ρ') ≥ B₀ ≥ e^{−x/8}`, the product over the zeros deeper than `x/(2L)`,

number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³ T^{1/2}`.

This is the Density Hypothesis rate, up to the free `c`, for every zero that is hyperbolically isolated from the zeros at least half as deep as itself. Its only
condition is on the geometry of the zeros: the near-line zeros, the far zeros and the much deeper zeros need no hypothesis, as the ratio of a far or much deeper zero is close to `1`.

**The last input.** The condition on the very deep zeros at the low centre of `OnlyComparablyDeepZerosCompete` holds off a small set of heights
(`exists_volume_very_deep_mass_gt_le`), since each zero costs `π/δ` of first moment and the exponential moment of the depth converges
(`exists_sum_very_deep_le`, from the weighted window count of the corpus).
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### The exponential moment of the depth -/

/-- A nonnegative sum over a set covered by three conditions is at most the sum of the three filtered sums. -/
theorem sum_le_three_filters {α : Type*} (S : Finset α) {f : α → ℝ} (hf : ∀ a ∈ S, 0 ≤ f a)
    (P Q R : α → Prop) [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    (h : ∀ a ∈ S, P a ∨ Q a ∨ R a) :
    ∑ a ∈ S, f a ≤ ∑ a ∈ S.filter P, f a + ∑ a ∈ S.filter Q, f a + ∑ a ∈ S.filter R, f a := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a ha => ?_
  have h0 := hf a ha
  rcases h a ha with h1 | h1 | h1
  · rw [if_pos h1]
    split_ifs <;> linarith
  · rw [if_pos h1]
    split_ifs <;> linarith
  · rw [if_pos h1]
    split_ifs <;> linarith

/-- One window of the weighted count, read at the scale `L ≤ log U ≤ 2L`. -/
theorem window_sum_le {A K T U L T₁ T₂ lam v₀ : ℝ} (hA : 0 < A) (hK : 0 ≤ K) (hT : 0 < T) (hL : 0 < L) (hU1 : T ≤ U)
    (hU2 : U ≤ 8 * T) (hlogU1 : L ≤ Real.log U) (hlogU2 : Real.log U ≤ 2 * L) (hlam : 0 ≤ lam) (hv : 0 < v₀)
    (hT₁ : 0 < T₁) (hT12 : T₁ ≤ T₂)
    (hw : ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
          RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) ≤
        U * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
            Real.exp (-(v₀ * Real.log U / 4800)) +
          Real.log U * (K * Real.log U / (Real.pi * v₀) * Real.exp (lam * Real.log U)))
    (S : Finset ℂ) (hS : ∀ w ∈ S, riemannZeta w = 0 ∧ 1 / 2 + v₀ < w.re ∧ w.re < 1 ∧ T₁ ≤ w.im ∧ w.im ≤ T₂) :
    ∑ w ∈ S, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) ≤
      8 * T * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * L)) * Real.exp (-(v₀ * L / 4800)) +
        2 * L * (K * (2 * L) / (Real.pi * v₀) * Real.exp (lam * (2 * L))) := by
  have hsub : S ⊆ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re) := by
    intro w hw'
    obtain ⟨h0, h1, h2, h3, h4⟩ := hS w hw'
    refine Finset.mem_filter.mpr ⟨(mem_windowZeros_iff hT₁ hT12 w).2 ⟨?_, h0⟩, h1⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, ?_⟩
    · rw [Set.uIcc_of_le (by norm_num)]
      exact ⟨by linarith, by linarith⟩
    · rw [Set.uIcc_of_le hT12]
      exact ⟨h3, h4⟩
  have hstep1 : ∑ w ∈ S, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) ≤
      ∑ w ∈ (windowZeros T₁ T₂).filter (fun w => 1 / 2 + v₀ < w.re),
        RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) := by
    have hle : ∑ w ∈ S, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) ≤
        ∑ w ∈ S, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log U) := by
      refine Finset.sum_le_sum fun w hw' => ?_
      obtain ⟨-, h1, -⟩ := hS w hw'
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (zeroMult_nonneg w)
      have hb : 0 ≤ lam * (w.re - 1 / 2) := mul_nonneg hlam (by linarith)
      exact mul_le_mul_of_nonneg_left hlogU1 hb
    refine hle.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => ?_)
    exact mul_nonneg (zeroMult_nonneg w) (Real.exp_pos _).le
  refine hstep1.trans (hw.trans ?_)
  have hlogU0 : 0 < Real.log U := by linarith
  have hvL : 0 < v₀ * L := by positivity
  have h1 : U * A / (4 * Real.pi * v₀) ≤ 8 * T * A / (4 * Real.pi * v₀) := by
    gcongr
  have h2 : 1 + 4800 / (v₀ * Real.log U) ≤ 1 + 4800 / (v₀ * L) := by
    gcongr
  have h3 : Real.exp (-(v₀ * Real.log U / 4800)) ≤ Real.exp (-(v₀ * L / 4800)) := by
    gcongr
  have h4 : Real.exp (lam * Real.log U) ≤ Real.exp (lam * (2 * L)) := by
    gcongr
  have hpi := Real.pi_pos
  refine add_le_add ?_ ?_
  · calc U * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log U)) *
          Real.exp (-(v₀ * Real.log U / 4800))
        ≤ 8 * T * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * L)) * Real.exp (-(v₀ * L / 4800)) := by
          gcongr
  · calc Real.log U * (K * Real.log U / (Real.pi * v₀) * Real.exp (lam * Real.log U))
        ≤ 2 * L * (K * (2 * L) / (Real.pi * v₀) * Real.exp (lam * (2 * L))) := by
          gcongr

/-- **The exponential moment of the depth.** The zeros deeper than `v₀` with ordinates in `[T/2 + 2, 3T]` have
`Σ m e^{λ b L} ≪ (T/v₀)(1 + 4800/(v₀L)) e^{−v₀L/4800} + (L²/v₀) e^{2λL}`. -/
theorem exists_sum_very_deep_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ lam v₀ : ℝ, 0 ≤ lam → 2 * lam ≤ 1 / 4800 →
      2 / Real.log T ≤ v₀ → v₀ ≤ 1 / 4 → ∀ S : Finset ℂ,
      (∀ w ∈ S, riemannZeta w = 0 ∧ 1 / 2 + v₀ < w.re ∧ w.re < 1 ∧ T / 2 + 2 ≤ w.im ∧ w.im ≤ 3 * T) →
      ∑ w ∈ S, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * Real.log T) ≤
        3 * (8 * T * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log T)) *
            Real.exp (-(v₀ * Real.log T / 4800)) +
          2 * Real.log T * (K * (2 * Real.log T) / (Real.pi * v₀) * Real.exp (lam * (2 * Real.log T)))) := by
  classical
  obtain ⟨A, K, hA, hK, hev⟩ := exists_windowZeros_weighted_le
  refine ⟨A, K, hA, hK, ?_⟩
  have htend : ∀ {a b : ℝ}, 0 < a → Tendsto (fun T : ℝ => a * T - b) atTop atTop := fun {a b} ha =>
    tendsto_atTop_add_const_right _ (-b) (tendsto_id.const_mul_atTop ha) |>.congr fun T => by
      simp [sub_eq_add_neg]
  have h1 := (htend (a := 2) (b := 0) (by norm_num)).eventually hev
  have h2 := (htend (a := 4) (b := 8) (by norm_num)).eventually hev
  have h3 := (htend (a := 8) (b := 24) (by norm_num)).eventually hev
  filter_upwards [h1, h2, h3, eventually_ge_atTop 100, Real.tendsto_log_atTop.eventually_ge_atTop 3]
    with T hU1 hU2 hU3 hT100 hL3 lam v₀ hlam hlam2 hv1 hv2 S hS
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hL3 hv1 hS ⊢
  have hL0 : 0 < L := by linarith
  have hv0 : 0 < v₀ := lt_of_lt_of_le (by positivity) hv1
  have hexpL : Real.exp L = T := by
    rw [hLdef]
    exact Real.exp_log hT0
  have hlogbound : ∀ U : ℝ, T ≤ U → U ≤ 8 * T → L ≤ Real.log U ∧ Real.log U ≤ 2 * L := by
    intro U h1 h2
    refine ⟨?_, ?_⟩
    · rw [hLdef]
      exact Real.log_le_log hT0 h1
    · have h3 : Real.log U ≤ Real.log (8 * T) := Real.log_le_log (by linarith) h2
      rw [Real.log_mul (by norm_num) hT0.ne', ← hLdef] at h3
      have h4 : Real.log 8 ≤ 3 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        have := Real.log_two_lt_d9
        push_cast
        linarith
      linarith
  have hv1' : ∀ U : ℝ, L ≤ Real.log U → 2 / Real.log U ≤ v₀ := by
    intro U h
    refine le_trans ?_ hv1
    exact div_le_div_of_nonneg_left (by norm_num) hL0 h
  -- the three windows
  obtain ⟨Ta, hTa, Tb, hTb, hwa⟩ := hU1
  obtain ⟨Tc, hTc, Td, hTd, hwb⟩ := hU2
  obtain ⟨Te, hTe, Tf, hTf, hwc⟩ := hU3
  simp only at hTa hTb hTc hTd hTe hTf
  have hTa0 : 0 < Ta := by linarith [hTa.1]
  have hTc0 : 0 < Tc := by linarith [hTc.1]
  have hTe0 : 0 < Te := by linarith [hTe.1]
  have hcover : ∀ w ∈ S, w.im ≤ Tb ∨ w.im ≤ Td ∧ Tc ≤ w.im ∨ Te ≤ w.im := by
    intro w hw
    obtain ⟨-, -, -, h4, h5⟩ := hS w hw
    by_cases h6 : w.im ≤ Tb
    · exact Or.inl h6
    · refine Or.inr ?_
      by_cases h7 : w.im ≤ Td
      · refine Or.inl ⟨h7, ?_⟩
        have := not_le.mp h6
        linarith [hTb.1, hTc.2]
      · refine Or.inr ?_
        have := not_le.mp h7
        linarith [hTd.1, hTe.2]
  have hnn : ∀ w ∈ S, 0 ≤ RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) := fun w _ =>
    mul_nonneg (zeroMult_nonneg w) (Real.exp_pos _).le
  refine (sum_le_three_filters S hnn _ _ _ hcover).trans ?_
  have ha := hlogbound (2 * T - 0) (by linarith) (by linarith)
  have hb := hlogbound (4 * T - 8) (by linarith) (by linarith)
  have hc := hlogbound (8 * T - 24) (by linarith) (by linarith)
  have hsa := window_sum_le hA hK hT0 hL0 (by linarith) (by linarith) ha.1 ha.2 hlam hv0 hTa0
    (by linarith [hTa.2, hTb.1]) (hwa lam v₀ hlam hlam2 (hv1' _ ha.1) hv2) (S.filter fun w => w.im ≤ Tb)
    (fun w hw => by
      obtain ⟨hwS, h6⟩ := Finset.mem_filter.mp hw
      obtain ⟨h1, h2, h3, h4, -⟩ := hS w hwS
      exact ⟨h1, h2, h3, by linarith [hTa.2], h6⟩)
  have hsb := window_sum_le hA hK hT0 hL0 (by linarith) (by linarith) hb.1 hb.2 hlam hv0 hTc0
    (by linarith [hTc.2, hTd.1]) (hwb lam v₀ hlam hlam2 (hv1' _ hb.1) hv2)
    (S.filter fun w => w.im ≤ Td ∧ Tc ≤ w.im)
    (fun w hw => by
      obtain ⟨hwS, h6, h7⟩ := Finset.mem_filter.mp hw
      obtain ⟨h1, h2, h3, -, -⟩ := hS w hwS
      exact ⟨h1, h2, h3, h7, h6⟩)
  have hsc := window_sum_le hA hK hT0 hL0 (by linarith) (by linarith) hc.1 hc.2 hlam hv0 hTe0
    (by linarith [hTe.2, hTf.1]) (hwc lam v₀ hlam hlam2 (hv1' _ hc.1) hv2) (S.filter fun w => Te ≤ w.im)
    (fun w hw => by
      obtain ⟨hwS, h6⟩ := Finset.mem_filter.mp hw
      obtain ⟨h1, h2, h3, -, h5⟩ := hS w hwS
      exact ⟨h1, h2, h3, h6, by linarith [hTf.1]⟩)
  linarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
