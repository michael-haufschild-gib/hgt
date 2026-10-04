import GaloisForLFunctions.HTGeometry.PowerHyperbolaConvolution

/-!
# The partial-summation constant is the value of the continued Dirichlet series

Let `c : ℕ → ℝ`, `c(0) = 0`, `|c| ≤ 1`, with `|A(t) − a t| ≤ C t^γ` (`γ < 1`), and suppose
`L(c, s) = H(s)/(s − 1)` on `Re s > 1` with `H` holomorphic on `Re s > a₀`.  Then on
`Re s > max(γ, a₀)`

`H(s) = a s + (s − 1) s ∫_1^∞ (A(t) − a t) t^{−s−1} dt`

(`eqOn_continuation`): both sides are holomorphic there (the integral is a Mellin transform of a
function `O(t^γ)` at infinity), and they agree on `Re s > 1` by Abel summation
(`LSeries_eq_mul_integral`).  Consequently `H(1) = a` (`perronNum_one_eq`) and, for real
`max(γ, a₀) < β < 1`, `(β − 1) Z_β = H(β)` (`mul_abelConst_eq`), where `Z_β` is the constant of
`Σ_{k ≤ Y} c(k) k^{−β} = a Y^{1−β}/(1−β) + Z_β + O(Y^{γ−β})`.
-/

open Finset MeasureTheory Set Filter Complex Topology Asymptotics

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PowerHyperbola

/-- The error `A(t) − a t`, cut off to `t > 1`, as a complex function. -/
def errFn (c : ℕ → ℝ) (a : ℝ) (t : ℝ) : ℂ := (Ioi (1 : ℝ)).indicator
  (fun t => ((countFn c t - a * t : ℝ) : ℂ)) t

/-- The continuation `a s + (s − 1) s ∫_1^∞ (A(t) − a t) t^{−s−1} dt`. -/
def contFn (c : ℕ → ℝ) (a : ℝ) (s : ℂ) : ℂ := a * s + (s - 1) * s * mellin (errFn c a) (-s)

theorem abs_countFn_le (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    |countFn c t| ≤ t + 1 := by
  unfold countFn
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, |c k| ≤ ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => hc k
    _ = ⌊t⌋₊ + 1 := by simp
    _ ≤ t + 1 := by linarith [Nat.floor_le ht]

theorem locallyIntegrable_errFn (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) (a : ℝ) :
    LocallyIntegrable (errFn c a) := by
  have hg : LocallyIntegrable (fun t : ℝ => ((1 + |a|) * (|t| + 1) : ℝ)) :=
    (by fun_prop : Continuous fun t : ℝ => (1 + |a|) * (|t| + 1)).locallyIntegrable
  refine hg.mono ?_ (Eventually.of_forall fun t => ?_)
  · refine (Measurable.indicator ?_ measurableSet_Ioi).aestronglyMeasurable
    exact Complex.measurable_ofReal.comp ((measurable_countFn c).sub
      (measurable_const.mul measurable_id))
  · unfold errFn
    rw [Set.indicator_apply]
    split_ifs with h
    · have ht : 1 < t := h
      rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + |a|) * (|t| + 1)),
        abs_of_pos (show (0 : ℝ) < t by linarith)]
      have h1 := abs_countFn_le c hc (by linarith : (0 : ℝ) ≤ t)
      calc |countFn c t - a * t| ≤ |countFn c t| + |a * t| := abs_sub _ _
        _ ≤ (t + 1) + |a| * t := by rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t)]; linarith
        _ ≤ (1 + |a|) * (t + 1) := by nlinarith [abs_nonneg a]
    · simp only [norm_zero]; positivity

/-- The Mellin transform of the error is holomorphic on `Re s > γ` (in the variable `−s`). -/
theorem differentiableAt_mellin_errFn (c : ℕ → ℝ) (hc : ∀ n, |c n| ≤ 1) {a C γ : ℝ}
    (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {s : ℂ} (hs : γ < s.re) :
    DifferentiableAt ℂ (fun s => mellin (errFn c a) (-s)) s := by
  have hm : DifferentiableAt ℂ (mellin (errFn c a)) (-s) := by
    refine mellin_differentiableAt_of_isBigO_rpow (a := -γ) (b := -s.re - 1)
      ((locallyIntegrable_errFn c hc a).locallyIntegrableOn _) ?_ (by simp; linarith) ?_
      (by simp)
    · refine isBigO_iff.mpr ⟨C, ?_⟩
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
      unfold errFn
      rw [Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from ht), Complex.norm_real, Real.norm_eq_abs,
        neg_neg, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)]
      exact hA t ht.le
    · refine isBigO_iff.mpr ⟨0, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
      unfold errFn
      rw [Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => by
        have : (1 : ℝ) < t := h; linarith [ht.2])]
      simp
  exact hm.comp s differentiableAt_id.neg

/-- The Mellin transform of the error is the integral over `(1, ∞)`. -/
theorem mellin_errFn_eq (c : ℕ → ℝ) (a : ℝ) (z : ℂ) :
    mellin (errFn c a) z =
      ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (z - 1) * ((countFn c t - a * t : ℝ) : ℂ) := by
  unfold mellin
  have h : ∀ t : ℝ, (t : ℂ) ^ (z - 1) • errFn c a t =
      (Ioi (1 : ℝ)).indicator (fun t => (t : ℂ) ^ (z - 1) * ((countFn c t - a * t : ℝ) : ℂ)) t := by
    intro t
    unfold errFn
    rw [Set.indicator_apply, Set.indicator_apply, smul_eq_mul]
    split_ifs <;> simp
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioi,
    Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi zero_le_one)]

/-- **Abel summation for the Dirichlet series** on `Re s > 1`. -/
theorem eq_contFn_of_one_lt (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1) {a C γ : ℝ}
    (hγ1 : γ < 1) (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {H : ℂ → ℂ}
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries (fun n => (c n : ℂ)) s) {s : ℂ}
    (hs : 1 < s.re) : H s = contFn c a s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [h] at hs; simp at hs
  have hsum : LSeriesSummable (fun n => (c n : ℂ)) s :=
    LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨1, fun n _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]; simpa using hc n⟩
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (c k : ℂ)) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun n => ?_⟩
    rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n), one_mul]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k ∈ Finset.Icc 1 n, ‖(c k : ℂ)‖ ≤ ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hc k
      _ = n := by simp
  have hL := LSeries_eq_mul_integral (fun n => (c n : ℂ)) zero_le_one hs hsum hO
  have hA' : ∀ t : ℝ, ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (c k : ℂ) = ((countFn c t : ℝ) : ℂ) := by
    intro t
    rw [countFn, ← sum_Icc_one_eq c hc0, Complex.ofReal_sum]
  simp_rw [hA'] at hL
  -- split the integral
  have hpow : ∀ t : ℝ, 0 < t → (t : ℂ) ^ (-(s + 1)) * (t : ℂ) = (t : ℂ) ^ (-s) := by
    intro t ht
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    rw [show -(s + 1) = -s - 1 by ring, Complex.cpow_sub _ _ ht', Complex.cpow_one]
    field_simp
  have hi1 : IntegrableOn (fun t : ℝ => (a : ℂ) * (t : ℂ) ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one).const_mul _
  have hi2 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((countFn c t - a * t : ℝ) : ℂ))
      (Ioi 1) := by
    refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (a := γ - s.re - 1) (by linarith)
      zero_lt_one).const_mul C) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi |>.mul ?_
      · refine fun t ht => (continuousAt_ofReal_cpow_const _ _ (Or.inr ?_)).continuousWithinAt
        have : (1 : ℝ) < t := ht; linarith
      · exact (Complex.measurable_ofReal.comp ((measurable_countFn c).sub
          (measurable_const.mul measurable_id))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1 : ℝ) < t := ht
      have ht0 : (0 : ℝ) < t := by linarith
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
      calc t ^ (-s.re - 1) * |countFn c t - a * t| ≤ t ^ (-s.re - 1) * (C * t ^ γ) := by
            gcongr; exact hA t ht1.le
        _ = C * t ^ (γ - s.re - 1) := by
            rw [mul_comm, mul_assoc, ← Real.rpow_add ht0]; ring_nf
  have hsplit : ∫ t in Ioi (1 : ℝ), ((countFn c t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      (∫ t in Ioi (1 : ℝ), (a : ℂ) * (t : ℂ) ^ (-s)) +
        ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s - 1) * ((countFn c t - a * t : ℝ) : ℂ) := by
    rw [← integral_add hi1 hi2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := by have : (1 : ℝ) < t := ht; linarith
    rw [show -s - 1 = -(s + 1) by ring]
    have := hpow t ht0
    push_cast
    linear_combination (a : ℂ) * this
  have hI1 : ∫ t in Ioi (1 : ℝ), (a : ℂ) * (t : ℂ) ^ (-s) = a / (s - 1) := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have : -s + 1 ≠ 0 := by
      intro h; apply hs1; linear_combination -h
    field_simp
    ring
  rw [hsplit, hI1, ← show (-s) - 1 = -s - 1 from rfl, ← mellin_errFn_eq] at hL
  rw [← hLS s hs] at hL
  have := congrArg (fun z => z * (s - 1)) hL
  simp only [div_mul_cancel₀ _ hs1] at this
  rw [this, contFn]
  field_simp

/-- **The continuation identity** on `Re s > max(γ, a₀)`. -/
theorem eqOn_continuation (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1) {a C γ : ℝ}
    (hγ1 : γ < 1) (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {H : ℂ → ℂ}
    {a₀ : ℝ} (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries (fun n => (c n : ℂ)) s) :
    EqOn H (contFn c a) {s | max γ a₀ < s.re} := by
  set U : Set ℂ := {s | max γ a₀ < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := by
    have : Convex ℝ U := convex_halfSpace_re_gt (max γ a₀)
    exact this.isPreconnected
  have hHU : DifferentiableOn ℂ H U := hH.mono fun s hs => by
    have : max γ a₀ < s.re := hs
    show a₀ < s.re
    linarith [le_max_right γ a₀]
  have hGU : DifferentiableOn ℂ (contFn c a) U := by
    intro s hs
    have hs' : γ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
    have hm := differentiableAt_mellin_errFn c hc hA hs'
    have : DifferentiableAt ℂ (contFn c a) s := by
      unfold contFn
      exact (differentiableAt_const _ |>.mul differentiableAt_id).add
        (((differentiableAt_id.sub_const 1).mul differentiableAt_id).mul hm)
    exact this.differentiableWithinAt
  set z₀ : ℂ := ((max (max γ a₀) 1 + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = max (max γ a₀) 1 + 1 := by simp [hz₀]
  have hz₀U : z₀ ∈ U := by
    show max γ a₀ < z₀.re
    rw [hz₀re]; linarith [le_max_left (max γ a₀) 1]
  have hev : H =ᶠ[𝓝 z₀] contFn c a := by
    have hre : ∀ᶠ s in 𝓝 z₀, 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by show 1 < z₀.re; rw [hz₀re]; linarith [le_max_right (max γ a₀) 1])
    filter_upwards [hre] with s hs
    exact eq_contFn_of_one_lt c hc0 hc hγ1 hA hLS hs
  exact (hHU.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hGU.analyticOnNhd hUo) hUc
    hz₀U hev

/-- The residue of the Dirichlet series at `s = 1` is the density: `H(1) = a`. -/
theorem eq_density (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1) {a C γ : ℝ}
    (hγ1 : γ < 1) (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {H : ℂ → ℂ}
    {a₀ : ℝ} (ha₀ : a₀ < 1) (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries (fun n => (c n : ℂ)) s) :
    H 1 = a := by
  rw [eqOn_continuation c hc0 hc hγ1 hA hH hLS (by show max γ a₀ < (1 : ℂ).re; simp; exact
    ⟨hγ1, ha₀⟩)]
  simp [contFn]

/-- **The partial-summation constant is the continued value:** `(β − 1) Z_β = H(β)`. -/
theorem mul_abelConst_eq (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc : ∀ n, |c n| ≤ 1) {a C γ : ℝ}
    (hγ1 : γ < 1) (hA : ∀ t : ℝ, 1 ≤ t → |countFn c t - a * t| ≤ C * t ^ γ) {H : ℂ → ℂ}
    {a₀ : ℝ} (hH : DifferentiableOn ℂ H {s | a₀ < s.re})
    (hLS : ∀ s : ℂ, 1 < s.re → H s / (s - 1) = LSeries (fun n => (c n : ℂ)) s) {β : ℝ}
    (hβγ : γ < β) (hβa : a₀ < β) (hβ1 : β ≠ 1) :
    ((β : ℂ) - 1) * (abelConst c a β : ℂ) = H β := by
  rw [eqOn_continuation c hc0 hc hγ1 hA hH hLS (by show max γ a₀ < ((β : ℂ)).re; simp; exact
    ⟨hβγ, hβa⟩)]
  unfold contFn abelConst
  rw [mellin_errFn_eq]
  have hint : ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(β : ℂ) - 1) * ((countFn c t - a * t : ℝ) : ℂ) =
      ((∫ t in Ioi (1 : ℝ), (countFn c t - a * t) * t ^ (-β - 1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := by have : (1 : ℝ) < t := ht; linarith
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht0, mul_comm]
    push_cast
    ring_nf
  rw [hint]
  have hβ1' : (β : ℂ) - 1 ≠ 0 := by
    intro h; apply hβ1; exact_mod_cast sub_eq_zero.mp h
  push_cast
  field_simp

end GaloisForLFunctions.HTGeometry.PowerHyperbola
