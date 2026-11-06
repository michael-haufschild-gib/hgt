import GaloisForLFunctions.MultiscaleMollifiedZetaField.OnlyComparablyDeepZerosCompete
import GaloisForLFunctions.RHTower.ZetaRightZeroWeightedCount

/-!
# The very deep zeros are rare

The zeros deeper than `v₀` carry an exponential moment `Σ m e^{λ b L} ≪ (T/v₀)(1 + 4800/(v₀L)) e^{−v₀L/4800} + (L²/v₀) e^{2λL}` for `2λ ≤ 1/4800`
(`exists_sum_very_deep_le`), summed from three windows of the weighted count of the corpus.

Each zero costs `π/δ` of first moment in `t`. So the mass `Σ m e^{(y+δ)b}/(1 + δ²(γ−t)²)` of the zeros deeper than `v₀`, at the low centre `y = 2δ` with `δ = cL`, exceeds `X ≥ 2` only on a set of
measure `≪ (1/(cL)) (Σ m e^{3cbL})/X` (`exists_volume_very_deep_mass_gt_le`). The zeros outside `[T/2 + 2, 3T]` contribute at most `1` by the Lorentzian tails, since `T^{1/4}` beats their mass `L/T`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23
open GaloisForLFunctions.SquareRootThreshold (sum_mult_le_tsum_copies)

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
  have hP : 0 ≤ U * A / (4 * Real.pi * v₀) := by
    have hU0 : 0 ≤ U := by linarith
    positivity
  have hQ : 0 ≤ 1 + 4800 / (v₀ * Real.log U) := by positivity
  refine add_le_add ?_ ?_
  · exact mul_le_mul (mul_le_mul h1 h2 hQ (hP.trans h1)) h3 (Real.exp_pos _).le
      (mul_nonneg (hP.trans h1) (by positivity))
  · have h5 : K * Real.log U / (Real.pi * v₀) ≤ K * (2 * L) / (Real.pi * v₀) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogU2 hK) (by positivity)
    have h6 : 0 ≤ K * Real.log U / (Real.pi * v₀) := by positivity
    exact mul_le_mul hlogU2 (mul_le_mul h5 h4 (Real.exp_pos _).le (h6.trans h5))
      (mul_nonneg h6 (Real.exp_pos _).le) (by positivity)

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
  rw [← hLdef] at hL3 hv1 ⊢
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

/-! ### The very deep zeros at the low centre -/

/-- The zeros deeper than `v₀` with ordinates in `[T/2 + 2, 3T]`. -/
def deepWindow (T v₀ : ℝ) : Finset ℂ :=
  (zetaZeroConfig.finite_window (T / 2) (3 * T)).toFinset.filter
    fun w => 1 / 2 + v₀ < w.re ∧ T / 2 + 2 ≤ w.im

/-- The Lorentzian mass of the zeros of the window, with the exponential weight of the depth. -/
def deepMass (δ lam L T v₀ t : ℝ) : ℝ :=
  ∑ w ∈ deepWindow T v₀, (zetaZeroConfig.mult w : ℝ) * Real.exp (lam * (w.re - 1 / 2) * L) *
    lorentzKernel δ (w.im - t)

theorem deepMass_nonneg (δ lam L T v₀ t : ℝ) : 0 ≤ deepMass δ lam L T v₀ t :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
    (lorentzKernel_nonneg _ _)

theorem continuous_lorentzKernel_sub (δ a : ℝ) : Continuous fun t : ℝ => lorentzKernel δ (a - t) := by
  unfold lorentzKernel
  refine continuous_const.div (by fun_prop) fun t => ?_
  positivity

theorem continuous_deepMass (δ lam L T v₀ : ℝ) : Continuous (deepMass δ lam L T v₀) := by
  unfold deepMass
  exact continuous_finsetSum _ fun w _ => continuous_const.mul (continuous_lorentzKernel_sub δ _)

theorem mem_deepWindow_props {T v₀ : ℝ} {w : ℂ} (hw : w ∈ deepWindow T v₀) :
    riemannZeta w = 0 ∧ 1 / 2 + v₀ < w.re ∧ w.re < 1 ∧ T / 2 + 2 ≤ w.im ∧ w.im ≤ 3 * T := by
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hw
  rw [Set.Finite.mem_toFinset] at h1
  obtain ⟨⟨h4, -, h5⟩, -, h6⟩ := h1
  exact ⟨h4, h2, h5, h3, h6⟩

theorem mult_eq_zeroMult {w : ℂ} (h1 : w.re < 1) :
    (zetaZeroConfig.mult w : ℝ) = RHTower.zeroMult w := by
  have hne : w ≠ 1 := fun h => by
    rw [h] at h1
    simp at h1
  rw [zeroMult_eq_zeta_order hne]
  rfl

/-- The first moment of the very deep mass. -/
theorem integral_deepMass_le {δ lam L T v₀ : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) :
    ∫ t in T..(2 * T), deepMass δ lam L T v₀ t ≤
      π / δ * ∑ w ∈ deepWindow T v₀, RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) := by
  unfold deepMass
  rw [intervalIntegral.integral_finsetSum (f := fun w t => (zetaZeroConfig.mult w : ℝ) *
    Real.exp (lam * (w.re - 1 / 2) * L) * lorentzKernel δ (w.im - t)) (fun w _ =>
    (continuous_const.mul (continuous_lorentzKernel_sub δ _)).intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_le_sum fun w hw => ?_
  rw [intervalIntegral.integral_const_mul]
  obtain ⟨-, -, h3, -, -⟩ := mem_deepWindow_props hw
  rw [mult_eq_zeroMult h3]
  have h1 := integral_lorentzian_le hδ w.im T hT
  have h0 : 0 ≤ RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) :=
    mul_nonneg (zeroMult_nonneg w) (Real.exp_pos _).le
  calc _ ≤ RHTower.zeroMult w * Real.exp (lam * (w.re - 1 / 2) * L) * (π / δ) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

/-- The far zeros, with ordinates off `[T/2 + 2, 3T]`, have Lorentzian mass `≪ L/T` at unit scale. -/
theorem sum_far_unit_le {T t : ℝ} (hT : 16 ≤ T) (ht : t ∈ Ioc T (2 * T))
    (F : Finset zetaZeroConfig.carrier)
    (hF : ∀ ρ' ∈ F, (ρ' : ℂ).im < T / 2 + 2 ∨ 3 * T < (ρ' : ℂ).im) :
    ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2)) ≤
      80 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T := by
  classical
  have hT0 : 0 < T := by linarith
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hC := xiLineTwoLogDerivConstant_nonneg
  set g₁ : ℂ → ℝ := fun z => if 3 * T < z.im then 1 / (1 + (t - z.im) ^ 2) else 0 with hg₁
  set g₂ : ℂ → ℝ := fun z => if z.im ≤ T / 2 + 2 then 1 / (1 + (t - z.im) ^ 2) else 0 with hg₂
  have hg₁0 : ∀ z, 0 ≤ g₁ z := fun z => by
    simp only [hg₁]
    split_ifs <;> positivity
  have hg₂0 : ∀ z, 0 ≤ g₂ z := fun z => by
    simp only [hg₂]
    split_ifs <;> positivity
  have hq₁ : (fun q : XiZeroCopy => g₁ (q.1 : ℂ)) =
      {q : XiZeroCopy | 3 * T < (q.1 : ℂ).im}.indicator (lorentzMassTerm t) := by
    funext q
    simp only [hg₁, Set.indicator_apply, Set.mem_setOf_eq, lorentzMassTerm]
  have hq₂ : (fun q : XiZeroCopy => g₂ (q.1 : ℂ)) =
      {q : XiZeroCopy | (q.1 : ℂ).im ≤ T / 2 + 2}.indicator (lorentzMassTerm t) := by
    funext q
    simp only [hg₂, Set.indicator_apply, Set.mem_setOf_eq, lorentzMassTerm]
  have hs₁ : Summable fun q : XiZeroCopy => g₁ (q.1 : ℂ) := by
    rw [hq₁]
    exact (summable_lorentzMassTerm t).indicator _
  have hs₂ : Summable fun q : XiZeroCopy => g₂ (q.1 : ℂ) := by
    rw [hq₂]
    exact (summable_lorentzMassTerm t).indicator _
  have hmemS : ∀ ρ ∈ F.image Subtype.val, ρ ∈ zetaZeroConfig.carrier := fun ρ hρ => by
    obtain ⟨ρ', -, rfl⟩ := Finset.mem_image.mp hρ
    exact ρ'.2
  have h1 := sum_mult_le_tsum_copies g₁ (fun q => hg₁0 _) hs₁ (F.image Subtype.val) hmemS
  have h2 := sum_mult_le_tsum_copies g₂ (fun q => hg₂0 _) hs₂ (F.image Subtype.val) hmemS
  rw [Finset.sum_image Subtype.val_injective.injOn] at h1 h2
  rw [hq₁] at h1
  rw [hq₂] at h2
  have hT1 := tsum_indicator_gt_le ht0 (by linarith [ht.2] : t ≤ 3 * T)
  have hT2 := tsum_indicator_le_le (T := T / 2 + 2) (t := t) (by positivity) (by linarith [ht.1])
  have hlog1 : Real.log (2 * (3 * T) + 5) ≤ 2 * Real.log T := by
    have h3 : 2 * (3 * T) + 5 ≤ T ^ 2 := by nlinarith
    calc _ ≤ Real.log (T ^ 2) := Real.log_le_log (by positivity) h3
      _ = _ := by rw [Real.log_pow]; norm_num
  have hlog2 : Real.log (t + 5) ≤ 2 * Real.log T := by
    have h3 : t + 5 ≤ T ^ 2 := by nlinarith [ht.2]
    calc _ ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h3
      _ = _ := by rw [Real.log_pow]; norm_num
  have hL0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hnum : 0 ≤ xiLineTwoLogDerivConstant + 2 * Real.log T := by positivity
  have hb1 : 16 * (xiLineTwoLogDerivConstant + Real.log (2 * (3 * T) + 5)) / (1 + (3 * T - t)) ≤
      16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T := by
    refine div_le_div₀ (by positivity) (by linarith) hT0 (by linarith [ht.2])
  have hb2 : 16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) / (1 + (t - (T / 2 + 2))) ≤
      64 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T := by
    rw [div_le_div_iff₀ (by linarith [ht.1]) hT0]
    have h3 : T ≤ 4 * (1 + (t - (T / 2 + 2))) := by linarith [ht.1]
    have h4 : 16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) ≤
        16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) := by linarith
    have h5 : 16 * (xiLineTwoLogDerivConstant + Real.log (t + 5)) * T ≤
        16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) * T :=
      mul_le_mul_of_nonneg_right h4 hT0.le
    have h6 : 16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) * T ≤
        16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) * (4 * (1 + (t - (T / 2 + 2)))) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  have hterm : ∀ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2)) ≤
      (zetaZeroConfig.mult ρ' : ℝ) * g₁ (ρ' : ℂ) + (zetaZeroConfig.mult ρ' : ℝ) * g₂ (ρ' : ℂ) := by
    intro ρ' hρ'
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rcases hF ρ' hρ' with h | h
    · have h0 := hg₁0 (ρ' : ℂ)
      have : g₂ (ρ' : ℂ) = 1 / (1 + (t - (ρ' : ℂ).im) ^ 2) := if_pos h.le
      linarith
    · have h0 := hg₂0 (ρ' : ℂ)
      have : g₁ (ρ' : ℂ) = 1 / (1 + (t - (ρ' : ℂ).im) ^ 2) := if_pos h
      linarith
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  have e : 80 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T =
      16 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T +
        64 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T := by ring
  rw [e]
  exact add_le_add (h1.trans (hT1.trans hb1)) (h2.trans (hT2.trans hb2))

/-- The far very deep zeros have negligible mass at the low centre. -/
theorem sum_far_low_le {T t c v₀ : ℝ} (hT : 16 ≤ T) (ht : t ∈ Ioc T (2 * T)) (hc : 6 * c ≤ 1) (hc0 : 0 < c)
    (hδ1 : 1 ≤ c * Real.log T) (hv₀ : 0 ≤ v₀)
    (hsmall : 160 * Real.exp (Real.log T / 4) * (xiLineTwoLogDerivConstant + 2 * Real.log T) ≤ T)
    (F : Finset zetaZeroConfig.carrier) (hdeep : ∀ ρ' ∈ F, v₀ < (ρ' : ℂ).re - 1 / 2)
    (hF : ∀ ρ' ∈ F, (ρ' : ℂ).im < T / 2 + 2 ∨ 3 * T < (ρ' : ℂ).im) :
    ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
      companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤ 1 := by
  have hT0 : 0 < T := by linarith
  have hδ0 : 0 < c * Real.log T := by linarith
  have hunit := sum_far_unit_le hT ht F hF
  have hterm : ∀ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
      companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤
      2 * Real.exp (Real.log T / 4) *
        ((zetaZeroConfig.mult ρ' : ℝ) * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2))) := by
    intro ρ' hρ'
    have hb0 : 0 ≤ (ρ' : ℂ).re - 1 / 2 := by linarith [hdeep ρ' hρ']
    have hb1 := abs_le.mp (abs_re_sub_half_le ρ')
    have hexp : ((ρ' : ℂ).re - 1 / 2) * (2 * (c * Real.log T)) +
        |(ρ' : ℂ).re - 1 / 2| * (c * Real.log T) ≤ Real.log T / 4 := by
      rw [abs_of_nonneg hb0]
      have hL0 : 0 < Real.log T := by
        by_contra h
        have := mul_nonpos_of_nonneg_of_nonpos hc0.le (not_lt.mp h)
        linarith
      have h1 : ((ρ' : ℂ).re - 1 / 2) * (c * Real.log T) ≤ 1 / 2 * (1 / 6 * Real.log T) :=
        mul_le_mul hb1.2 (mul_le_mul_of_nonneg_right (by linarith) hL0.le) hδ0.le (by norm_num)
      nlinarith
    have hw := companionWeight_le_of_exponent (t := t) hexp
    have hd : 1 ≤ |(ρ' : ℂ).im - t| := by
      rcases hF ρ' hρ' with h | h
      · refine le_trans ?_ (neg_le_abs _)
        linarith [ht.1]
      · refine le_trans ?_ (le_abs_self _)
        linarith [ht.2]
    have hd2 : 1 ≤ ((ρ' : ℂ).im - t) ^ 2 := by
      calc (1 : ℝ) ≤ |(ρ' : ℂ).im - t| ^ 2 := one_le_pow₀ hd
        _ = _ := sq_abs _
    have hK : lorentzKernel (c * Real.log T) ((ρ' : ℂ).im - t) ≤ 2 * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2)) := by
      unfold lorentzKernel
      have e : (t - (ρ' : ℂ).im) ^ 2 = ((ρ' : ℂ).im - t) ^ 2 := by ring
      rw [e, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hδ2 : 1 ≤ (c * Real.log T) ^ 2 := one_le_pow₀ hδ1
      nlinarith [mul_le_mul_of_nonneg_right hδ2 (sq_nonneg ((ρ' : ℂ).im - t))]
    have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ' := Nat.cast_nonneg _
    calc (zetaZeroConfig.mult ρ' : ℝ) * companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ'
        ≤ (zetaZeroConfig.mult ρ' : ℝ) * (Real.exp (Real.log T / 4) *
            (2 * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2)))) := by
          refine mul_le_mul_of_nonneg_left (hw.trans ?_) hm
          exact mul_le_mul_of_nonneg_left hK (Real.exp_pos _).le
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h1 := mul_le_mul_of_nonneg_left hunit (by positivity : 0 ≤ 2 * Real.exp (Real.log T / 4))
  refine h1.trans ?_
  have e : 2 * Real.exp (Real.log T / 4) * (80 * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T) =
      160 * Real.exp (Real.log T / 4) * (xiLineTwoLogDerivConstant + 2 * Real.log T) / T := by ring
  rw [e, div_le_one hT0]
  exact hsmall

/-- **The very deep zeros are rare.** Mass `X ≥ 2` of the zeros deeper than `v₀`, at the low centre, occurs on measure at most `2/X` times the first
moment `(π/δ) Σ m e^{3cbL}`. -/
theorem exists_volume_very_deep_mass_gt_le :
    ∃ A K : ℝ, 0 < A ∧ 0 ≤ K ∧ ∀ᶠ T : ℝ in atTop, ∀ c v₀ X : ℝ, 0 < c → 6 * c ≤ 1 / 4800 →
      1 ≤ c * Real.log T → 2 / Real.log T ≤ v₀ → v₀ ≤ 1 / 4 → 2 ≤ X →
      volume {t | t ∈ Ioc T (2 * T) ∧ ∃ V : Finset zetaZeroConfig.carrier,
        (∀ ρ' ∈ V, v₀ < (ρ' : ℂ).re - 1 / 2) ∧
        X < ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
          companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ'} ≤
      ENNReal.ofReal (π / (c * Real.log T) *
        (3 * (8 * T * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log T)) *
            Real.exp (-(v₀ * Real.log T / 4800)) +
          2 * Real.log T * (K * (2 * Real.log T) / (Real.pi * v₀) *
            Real.exp (3 * c * (2 * Real.log T))))) / (X / 2)) := by
  classical
  obtain ⟨A, K, hA, hK, hev⟩ := exists_sum_very_deep_le
  refine ⟨A, K, hA, hK, ?_⟩
  have hsmall : ∀ᶠ T : ℝ in atTop, 160 * Real.exp (Real.log T / 4) *
      (xiLineTwoLogDerivConstant + 2 * Real.log T) ≤ T := by
    have h := eventually_mul_add_one_le_exp (a := 3 / 4) (by norm_num)
      (160 * (xiLineTwoLogDerivConstant + 2))
    filter_upwards [Real.tendsto_log_atTop.eventually h, eventually_gt_atTop 0,
      Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hT hT0 hL1
    have hC := xiLineTwoLogDerivConstant_nonneg
    have h1 : 160 * (xiLineTwoLogDerivConstant + 2 * Real.log T) ≤
        160 * (xiLineTwoLogDerivConstant + 2) * (Real.log T + 1) := by nlinarith
    have hexp : T = Real.exp (Real.log T / 4) * Real.exp (3 / 4 * Real.log T) := by
      rw [← Real.exp_add, show Real.log T / 4 + 3 / 4 * Real.log T = Real.log T by ring,
        Real.exp_log hT0]
    calc 160 * Real.exp (Real.log T / 4) * (xiLineTwoLogDerivConstant + 2 * Real.log T)
        = Real.exp (Real.log T / 4) * (160 * (xiLineTwoLogDerivConstant + 2 * Real.log T)) := by ring
      _ ≤ Real.exp (Real.log T / 4) * Real.exp (3 / 4 * Real.log T) :=
          mul_le_mul_of_nonneg_left (h1.trans hT) (Real.exp_pos _).le
      _ = T := hexp.symm
  filter_upwards [hev, hsmall, eventually_ge_atTop 16, Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hT hTs hT16 hL1 c v₀ X hc0 hc hδ1 hv1 hv2 hX
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hδ0 : 0 < c * Real.log T := by linarith
  have hv0 : 0 < v₀ := lt_of_lt_of_le (by positivity) hv1
  have hX2 : 0 < X / 2 := by linarith
  have hS := hT (3 * c) v₀ (by positivity) (by linarith) hv1 hv2 (deepWindow T v₀)
    (fun w hw => mem_deepWindow_props hw)
  have hint := integral_deepMass_le (lam := 3 * c) (L := Real.log T) (v₀ := v₀) hδ0 hT0.le
  have hmean : ∫ t in T..(2 * T), deepMass (c * Real.log T) (3 * c) (Real.log T) T v₀ t ≤
      π / (c * Real.log T) * (3 * (8 * T * A / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log T)) *
            Real.exp (-(v₀ * Real.log T / 4800)) +
          2 * Real.log T * (K * (2 * Real.log T) / (Real.pi * v₀) *
            Real.exp (3 * c * (2 * Real.log T))))) :=
    hint.trans (mul_le_mul_of_nonneg_left hS (by positivity))
  have hvol := volume_ge_le_of_integral (continuous_deepMass (c * Real.log T) (3 * c) (Real.log T) T v₀)
    (deepMass_nonneg _ _ _ _ _) hT0 hX2 hmean
  refine (measure_mono ?_).trans hvol
  rintro t ⟨ht, V, hdeep, hV⟩
  refine ⟨ht, ?_⟩
  -- split the family at the window
  have hsplit := Finset.sum_filter_add_sum_filter_not V
    (fun ρ' : zetaZeroConfig.carrier => T / 2 + 2 ≤ (ρ' : ℂ).im ∧ (ρ' : ℂ).im ≤ 3 * T)
    (fun ρ' => (zetaZeroConfig.mult ρ' : ℝ) *
      companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ')
  have hfar := sum_far_low_le hT16 ht (by linarith) hc0 hδ1 hv0.le hTs
    (V.filter fun ρ' : zetaZeroConfig.carrier => ¬ (T / 2 + 2 ≤ (ρ' : ℂ).im ∧ (ρ' : ℂ).im ≤ 3 * T))
    (fun ρ' h => hdeep ρ' (Finset.mem_filter.mp h).1) (fun ρ' h => by
      have h1 := (Finset.mem_filter.mp h).2
      by_cases h2 : T / 2 + 2 ≤ (ρ' : ℂ).im
      · exact Or.inr (not_le.mp fun h3 => h1 ⟨h2, h3⟩)
      · exact Or.inl (not_le.mp h2))
  have hnear : ∑ ρ' ∈ V.filter (fun ρ' : zetaZeroConfig.carrier =>
      T / 2 + 2 ≤ (ρ' : ℂ).im ∧ (ρ' : ℂ).im ≤ 3 * T), (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤
      deepMass (c * Real.log T) (3 * c) (Real.log T) T v₀ t := by
    unfold deepMass
    rw [← Finset.sum_image (f := fun w : ℂ => (zetaZeroConfig.mult w : ℝ) *
      companionWeight (c * Real.log T) (2 * (c * Real.log T)) t w) (g := Subtype.val)
      Subtype.val_injective.injOn]
    have hsub : (V.filter (fun ρ' : zetaZeroConfig.carrier =>
        T / 2 + 2 ≤ (ρ' : ℂ).im ∧ (ρ' : ℂ).im ≤ 3 * T)).image Subtype.val ⊆ deepWindow T v₀ := by
      intro w hw
      obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hρ'
      refine Finset.mem_filter.mpr ⟨?_, ?_, h2⟩
      · rw [Set.Finite.mem_toFinset]
        exact ⟨ρ'.2, by linarith, h3⟩
      · have := hdeep ρ' h1
        linarith
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun w _ _ => ?_)
      (Finset.sum_le_sum fun w hw => ?_)
    · refine mul_nonneg (Nat.cast_nonneg _) ?_
      unfold companionWeight
      positivity
    · have hb : 0 < w.re - 1 / 2 := by
        have := (mem_deepWindow_props hw).2.1
        linarith
      have hexp : (w.re - 1 / 2) * (2 * (c * Real.log T)) + |w.re - 1 / 2| * (c * Real.log T) =
          3 * c * (w.re - 1 / 2) * Real.log T := by
        rw [abs_of_pos hb]
        ring
      have hw2 := companionWeight_le_of_exponent (δ := c * Real.log T) (y := 2 * (c * Real.log T)) (t := t)
        (ρ' := w) hexp.le
      calc (zetaZeroConfig.mult w : ℝ) * companionWeight (c * Real.log T) (2 * (c * Real.log T)) t w
          ≤ (zetaZeroConfig.mult w : ℝ) * (Real.exp (3 * c * (w.re - 1 / 2) * Real.log T) *
              lorentzKernel (c * Real.log T) (w.im - t)) :=
            mul_le_mul_of_nonneg_left hw2 (Nat.cast_nonneg _)
        _ = _ := by ring
  linarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
