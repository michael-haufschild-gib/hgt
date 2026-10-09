import GaloisForLFunctions.RHTower.Sieve.UnitBlockReflection
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTwistedFourthMoments
import GaloisForLFunctions.HTGeometry.IntervalIntegralHolderSwap

/-!
# Ingredients for the twisted fourth moment of a reflected unit block

* `integral_normSq_mtWattCoefficientBlock_window_le`: the mean value
  `∫_{T/2}^{T} |𝒜(t)|² ≤ (5πe/A + (5π/2)T/A²) ∑_{A<m≤2A} |a_m|²`.
* `mtWattCoefficientBlock_add`: a vertical shift is a coefficient twist,
  `𝒜_a(τ + u) = 𝒜_{a·m^{-iu}}(τ)`, and twisting preserves `|a_m|` (`norm_mtTwist_le`).
* `exists_norm_mtWattUnitBlock_le_dual`: the pointwise reflection in the form
  `|U_N(t)| ≤ C((1 + log t)/N + t^{-1/2}) + 23 t^{-1/2} |∑_{k ∈ D} k^{it}|`.
* `integral_comp_sub_le_three_windows`: a shift by `|u| ≤ T/4` keeps `[T/2, T]` inside
  `[T/4, T/2] ∪ [T/2, T] ∪ [5T/8, 5T/4]`, three windows of the form `[T'/2, T']`.
* `integral_inv_norm_one_add_le`: `∫_{-U}^{U} du/|1 + iu| ≤ 4 log(1 + U)`, the mass of the
  Perron weight.
-/

open Complex Set MeasureTheory Filter
open GaloisForLFunctions.HTGeometry
open scoped Real

namespace RHTower.Sieve

noncomputable section

/-! ## Mean value of a coefficient block on a window -/

/-- **Mean value on a window.** -/
theorem integral_normSq_mtWattCoefficientBlock_window_le (a : ℕ → ℂ) {A : ℕ} (hA : 1 ≤ A)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t in (T / 2)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      (5 * π * Real.exp 1 * (1 / (A : ℝ)) + (5 * π / 2) * (1 / (A : ℝ) ^ 2) * T) *
        ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 := by
  have hcoeffCont : Continuous (mtWattCoefficientBlock a A) := continuous_perronPoly _ _ _
  have hfullSet := integral_Icc_normSq_mtWattCoefficientBlock_le_general_affine a A hT
  have hfull : (∫ t in (-T)..T, ‖mtWattCoefficientBlock a A t‖ ^ 2) ≤
      generalMeanSquareConst (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 +
        generalMeanSquareRate (fun n => mtRealIntervalAF a (A : ℝ) (2 * A : ℝ) n)
          (Finset.Icc 1 (2 * A)) 1 * T := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    exact hfullSet
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t : ℝ => ‖mtWattCoefficientBlock a A t‖ ^ 2) (μ := volume) (a := -T) (b := T / 2)
    (c := T) ((hcoeffCont.norm.pow 2).intervalIntegrable _ _)
    ((hcoeffCont.norm.pow 2).intervalIntegrable _ _)
  have hleft : 0 ≤ ∫ t in (-T)..(T / 2), ‖mtWattCoefficientBlock a A t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  have hconst := generalMeanSquareConst_mtWattCoefficientBlock_le_energy a hA
  have hrate := generalMeanSquareRate_mtWattCoefficientBlock_le_energy a hA
  have hrateT := mul_le_mul_of_nonneg_right hrate (by linarith : (0 : ℝ) ≤ T)
  have e : (5 * π * Real.exp 1 * (1 / (A : ℝ)) + (5 * π / 2) * (1 / (A : ℝ) ^ 2) * T) *
      ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 =
      5 * π * Real.exp 1 * (1 / (A : ℝ)) * (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) +
        (5 * π / 2) * (1 / (A : ℝ) ^ 2) * (∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2) * T := by
    ring
  rw [e]
  linarith

/-! ## Vertical shifts are coefficient twists -/

/-- The coefficient twist `a_m m^{-iu}`. -/
def mtTwist (a : ℕ → ℂ) (u : ℝ) : ℕ → ℂ := fun m => a m * (m : ℂ) ^ (-((u : ℂ) * I))

theorem norm_natCast_cpow_neg_mul_I_le (m : ℕ) (u : ℝ) : ‖(m : ℂ) ^ (-((u : ℂ) * I))‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · by_cases hu : u = 0
    · simp [hu]
    · rw [Nat.cast_zero, Complex.zero_cpow (by
        intro h; apply hu
        have := congrArg Complex.im h; simpa using this)]
      simp
  · rw [Complex.norm_natCast_cpow_of_pos hm]
    simp

theorem norm_mtTwist_le (a : ℕ → ℂ) (u : ℝ) (m : ℕ) : ‖mtTwist a u m‖ ≤ ‖a m‖ := by
  rw [mtTwist, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_natCast_cpow_neg_mul_I_le m u)

theorem norm_mtTwist_of_pos (a : ℕ → ℂ) (u : ℝ) {m : ℕ} (hm : 0 < m) :
    ‖mtTwist a u m‖ = ‖a m‖ := by
  rw [mtTwist, norm_mul, Complex.norm_natCast_cpow_of_pos hm]
  simp

theorem sum_normSq_mtTwist (a : ℕ → ℂ) (u : ℝ) (A : ℕ) :
    ∑ n ∈ Finset.Ioc A (2 * A), ‖mtTwist a u n‖ ^ 2 = ∑ n ∈ Finset.Ioc A (2 * A), ‖a n‖ ^ 2 :=
  Finset.sum_congr rfl fun n hn => by
    rw [norm_mtTwist_of_pos a u (by have := (Finset.mem_Ioc.1 hn).1; omega)]

/-- **A vertical shift is a coefficient twist.** -/
theorem mtWattCoefficientBlock_add (a : ℕ → ℂ) (A : ℕ) (τ u : ℝ) :
    mtWattCoefficientBlock a A (τ + u) = mtWattCoefficientBlock (mtTwist a u) A τ := by
  rw [mtWattCoefficientBlock_eq_sum_Ioc, mtWattCoefficientBlock_eq_sum_Ioc]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Ioc.1 hn).1
    exact_mod_cast (show n ≠ 0 by omega)
  rw [mtTwist, mul_assoc, ← Complex.cpow_add _ _ hn0]
  congr 2
  push_cast; ring

/-! ## The pointwise reflection in dual-sum form -/

theorem ubMainTerm_eq {t : ℝ} (ht : 0 < t) {k : ℤ} (hk : 0 < k) :
    ubMainTerm t k = ubJ t * Complex.exp (((-(t * Real.log (t / (2 * π)))) : ℝ) * I) *
      (k : ℂ) ^ ((t : ℂ) * I) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [ubMainTerm, Complex.cpow_def_of_ne_zero (by exact_mod_cast hk.ne'),
    show ((k : ℤ) : ℂ) = ((k : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_log hk0.le,
    show t / (2 * π * k) = t / (2 * π) / k by field_simp, Real.log_div (by positivity) hk0.ne']
  have e : Complex.exp (((-(t * (Real.log (t / (2 * π)) - Real.log k))) : ℝ) * I) =
      Complex.exp (((-(t * Real.log (t / (2 * π)))) : ℝ) * I) *
        Complex.exp (((Real.log k : ℝ) : ℂ) * ((t : ℂ) * I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

theorem norm_intCast_cpow_mul_I {k : ℤ} (hk : 0 < k) (t : ℝ) :
    ‖(k : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
  have : (k : ℂ) = ((k.toNat : ℕ) : ℂ) := by
    rw [show ((k.toNat : ℕ) : ℂ) = (((k.toNat : ℕ) : ℤ) : ℂ) by push_cast; rfl,
      Int.toNat_of_nonneg hk.le]
  rw [this, Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- **Pointwise reflection, dual-sum form.** -/
theorem exists_norm_mtWattUnitBlock_le_dual :
    ∃ C : ℝ, 0 < C ∧ ∀ (N N' : ℕ), 1 ≤ N → N < N' → N' ≤ 2 * N → ∀ t : ℝ, 1 ≤ t →
      t ≤ (N : ℝ) ^ 2 → (N : ℝ) ≤ 2 * t →
      ‖mtWattUnitBlock N N' t‖ ≤ C * ((1 + Real.log t) / N + 1 / Real.sqrt t) +
        23 / Real.sqrt t * ‖∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I)‖ := by
  obtain ⟨C, hC, h⟩ := exists_norm_mtWattUnitBlock_sub_main_le
  refine ⟨C, hC, fun N N' hN hNN' hN' t ht htN hNt => ?_⟩
  have ht0 : 0 < t := by linarith
  have hpos : ∀ k ∈ ubDual N N' t, 0 < k := fun k hk => by
    have := (mem_ubDual.1 hk).1
    have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  have hmain : ∑ k ∈ ubDual N N' t, ubMainTerm t k = ubJ t *
      Complex.exp (((-(t * Real.log (t / (2 * π)))) : ℝ) * I) *
        ∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k hk => ubMainTerm_eq ht0 (hpos k hk)
  have hnorm : ‖∑ k ∈ ubDual N N' t, ubMainTerm t k‖ ≤
      23 / Real.sqrt t * ‖∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I)‖ := by
    rw [hmain, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_mul_of_nonneg_right (norm_ubJ_le ht0) (norm_nonneg _)
  calc ‖mtWattUnitBlock N N' t‖ ≤ ‖mtWattUnitBlock N N' t - ∑ k ∈ ubDual N N' t, ubMainTerm t k‖
        + ‖∑ k ∈ ubDual N N' t, ubMainTerm t k‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := add_le_add (h N N' hN hNN' hN' t ht htN hNt) hnorm

/-- **The dual sum is at most its length.**  `|∑_{k ∈ D} k^{it}| ≤ t/(2π(N + ¾))`. -/
theorem norm_sum_ubDual_le {N N' : ℕ} {t : ℝ} (ht : 0 < t) :
    ‖∑ k ∈ ubDual N N' t, (k : ℂ) ^ ((t : ℂ) * I)‖ ≤ t / (2 * π * ((N : ℝ) + 3 / 4)) := by
  have hpos : ∀ k ∈ ubDual N N' t, 0 < k := fun k hk => by
    have := (mem_ubDual.1 hk).1
    have : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) this
    exact_mod_cast this
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_congr rfl fun k hk => norm_intCast_cpow_mul_I (hpos k hk) t, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  set k₂ := t / (2 * π * ((N : ℝ) + 3 / 4))
  have hk2 : 0 ≤ k₂ := by positivity
  have hsub : ubDual N N' t ⊆ Finset.Icc 1 ⌊k₂⌋ := fun k hk => by
    obtain ⟨-, h2⟩ := mem_ubDual.1 hk
    exact Finset.mem_Icc.2 ⟨hpos k hk, Int.le_floor.2 (by linarith)⟩
  have h1 := Finset.card_le_card hsub
  rw [Int.card_Icc, show ⌊k₂⌋ + 1 - 1 = ⌊k₂⌋ by ring] at h1
  have h0 : 0 ≤ ⌊k₂⌋ := Int.floor_nonneg.2 hk2
  have h2 : ((⌊k₂⌋.toNat : ℕ) : ℝ) ≤ k₂ := by
    rw [show ((⌊k₂⌋.toNat : ℕ) : ℝ) = ((⌊k₂⌋.toNat : ℤ) : ℝ) by push_cast; rfl,
      Int.toNat_of_nonneg h0]
    exact Int.floor_le k₂
  exact le_trans (by exact_mod_cast h1) h2

/-! ## Shifted windows and the Perron weight -/

/-- **Three windows cover a shifted window.** -/
theorem integral_comp_sub_le_three_windows {F : ℝ → ℝ} (hF : Continuous F)
    (hF0 : ∀ x, 0 ≤ F x) {T u : ℝ} (hT : 0 < T) (hu : |u| ≤ T / 4) :
    ∫ t in (T / 2)..T, F (t - u) ≤
      (∫ x in (T / 4)..(T / 2), F x) + (∫ x in (T / 2)..T, F x) +
        ∫ x in (5 * T / 8)..(5 * T / 4), F x := by
  rw [intervalIntegral.integral_comp_sub_right]
  have hu1 := (abs_le.1 hu).1
  have hu2 := (abs_le.1 hu).2
  have hint : ∀ a b : ℝ, IntervalIntegrable F volume a b := fun a b => hF.intervalIntegrable a b
  have h1 : ∫ x in (T / 2 - u)..(T - u), F x ≤ ∫ x in (T / 4)..(5 * T / 4), F x :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall hF0) (hint _ _)
  have h2 : ∫ x in (T / 4)..(5 * T / 4), F x = (∫ x in (T / 4)..(T / 2), F x) +
      (∫ x in (T / 2)..T, F x) + ∫ x in T..(5 * T / 4), F x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
      intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have h3 : ∫ x in T..(5 * T / 4), F x ≤ ∫ x in (5 * T / 8)..(5 * T / 4), F x :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) le_rfl
      (Filter.Eventually.of_forall hF0) (hint _ _)
  linarith

theorem norm_one_add_mul_I (u : ℝ) : ‖(1 : ℂ) + (u : ℂ) * I‖ = Real.sqrt (1 + u ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp; ring

/-- **Mass of the Perron weight.**  `∫_{-U}^{U} du/|1 + iu| ≤ 4 log(1 + U)` for `U ≥ 0`. -/
theorem integral_inv_norm_one_add_le {U : ℝ} (hU : 0 ≤ U) :
    ∫ u in (-U)..U, 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ 4 * Real.log (1 + U) := by
  have hw : ∀ u : ℝ, 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ ≤ 2 / (1 + |u|) := by
    intro u
    rw [norm_one_add_mul_I]
    have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [div_le_div_iff₀ hs (by positivity), one_mul]
    have : (1 + |u|) ^ 2 ≤ 4 * (1 + u ^ 2) := by
      have := sq_abs u
      nlinarith [abs_nonneg u, sq_nonneg (|u| - 1)]
    have h2 : 1 + |u| ≤ 2 * Real.sqrt (1 + u ^ 2) := by
      rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + |u|),
        show 2 * Real.sqrt (1 + u ^ 2) = Real.sqrt (4 * (1 + u ^ 2)) by
          rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
      exact Real.sqrt_le_sqrt this
    linarith
  have hcont : Continuous fun u : ℝ => 1 / ‖(1 : ℂ) + (u : ℂ) * I‖ := by
    refine continuous_const.div (by fun_prop) fun u => ?_
    rw [norm_one_add_mul_I]; exact (Real.sqrt_pos.2 (by positivity)).ne'
  have hcont2 : Continuous fun u : ℝ => 2 / (1 + |u|) :=
    continuous_const.div (by fun_prop) fun u => by positivity
  refine le_trans (intervalIntegral.integral_mono_on (by linarith) (hcont.intervalIntegrable _ _)
    (hcont2.intervalIntegrable _ _) fun u _ => hw u) ?_
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont2.intervalIntegrable (μ := volume) (-U) 0) (hcont2.intervalIntegrable 0 U)
  rw [← hsplit]
  have hright : ∫ u in (0 : ℝ)..U, 2 / (1 + |u|) = 2 * Real.log (1 + U) := by
    have hcongr : ∫ u in (0 : ℝ)..U, 2 / (1 + |u|) = ∫ u in (0 : ℝ)..U, 2 * (1 / (1 + u)) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      rw [uIcc_of_le hU] at hu
      rw [abs_of_nonneg hu.1]; ring
    rw [hcongr, intervalIntegral.integral_const_mul]
    have hF : ∀ x ∈ uIcc (0 : ℝ) U, HasDerivAt (fun y => Real.log (1 + y)) (1 / (1 + x)) x := by
      intro x hx
      rw [uIcc_of_le hU] at hx
      have h := ((hasDerivAt_id' x).const_add 1).log (by linarith [hx.1])
      simpa [one_div] using h
    have hc : ContinuousOn (fun x : ℝ => 1 / (1 + x)) (uIcc 0 U) :=
      continuousOn_const.div (continuousOn_const.add continuousOn_id) fun x hx => by
        rw [uIcc_of_le hU] at hx; linarith [hx.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hc.intervalIntegrable]
    simp
  have hleft : ∫ u in (-U)..0, 2 / (1 + |u|) = ∫ u in (0 : ℝ)..U, 2 / (1 + |u|) := by
    have e : ∫ u in (0 : ℝ)..U, 2 / (1 + |u|) = ∫ u in (0 : ℝ)..U, 2 / (1 + |-u|) := by
      simp only [abs_neg]
    rw [e, intervalIntegral.integral_comp_neg (fun u : ℝ => 2 / (1 + |u|))]
    simp
  rw [hleft, hright]; linarith

end

end RHTower.Sieve
