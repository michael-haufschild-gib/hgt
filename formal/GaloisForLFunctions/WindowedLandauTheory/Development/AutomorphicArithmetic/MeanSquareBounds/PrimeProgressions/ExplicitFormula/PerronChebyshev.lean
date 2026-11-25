import GaloisForLFunctions.RHTower.DirichletCharacterPerron
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronContourShift
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.ShortNorms.RayClass.TruncatedPerron
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.ExceptionalZeroBounds.NativeRightBound
import GaloisForLFunctions.WindowedLandauTheory.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

/-! The unsmoothed Chebyshev sum is approximated by the Perron integral at a nearby height. -/

open Complex DirichletCharacter ArithmeticFunction Filter MeasureTheory Set Topology
open WindowedLandauTheory.MainNotions.GlobalTheoryTheory WindowedLandauTheory.ZeroFreeDirichlet

open scoped Classical

noncomputable section

namespace QH.PrimeProgressions

private theorem continuous_primitivePerron_right {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {u c : ℝ} (hu : 0 < u) (hc : 1 < c) :
    Continuous (fun t : ℝ => primitivePerronIntegrand χ u ((c : ℂ) + t * I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  let s : ℂ := c + t * I
  have hr : s.re = c := by simp [s]
  have hs : 1 < s.re := hr.symm ▸ hc
  have h₁ : s ≠ 1 := fun e => by norm_num [e] at hs
  have h₀ : s ≠ 0 := fun e => by norm_num [e] at hs
  have hL := LFunction_ne_zero_of_one_le_re χ (.inr h₁) hs.le
  have hk : AnalyticAt ℂ (primitivePerronIntegrand χ u) s :=
    analyticAt_primitivePerronIntegrand hu h₀ h₁ hL
  have hpath : ContinuousAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * I) t :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  exact ContinuousAt.comp' (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * I)
    (x := t) hk.continuousAt hpath

private theorem primitive_perron_right_tails :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (u T U : ℝ), 2 ≤ u → 0 < T → T ≤ U → U ≤ T + 1 →
      ‖primitivePerronVertical χ u U - primitivePerronVertical χ u T‖ ≤ C * (u * Real.log u / T) := by
  obtain ⟨C, hC, HC⟩ := l_log_deriv_right
  refine ⟨6 * (1 + 2 * C), by positivity, ?_⟩
  intro N _ χ u T U hu hT hTU hU
  let c := primitivePerronAbscissa u
  let F (t : ℝ) := primitivePerronIntegrand χ u ((c : ℂ) + t * I)
  let K : ℂ := 1 / (2 * Real.pi)
  let A := (1 + 2 * C) * Real.log u
  let B := A * (3 * u) / T
  have hc := (primitivePerronAbscissa_bounds hu).1
  have hcu := (primitivePerronAbscissa_bounds hu).2.2
  have hu₀ : 0 < u := by linarith only [hu]
  have hlog : (1 / 2 : ℝ) ≤ Real.log u :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hu)
  have hF : Continuous F := continuous_primitivePerron_right χ hu₀ hc
  have hB : 0 ≤ B := by dsimp only [B, A]; positivity [show 0 ≤ Real.log u by linarith only [hlog]]
  have hpoint (t : ℝ) (ht : T ≤ |t|) : ‖F t‖ ≤ B := by
    let s : ℂ := c + t * I
    have hr : s.re = c := by simp [s]
    have hi : s.im = t := by simp [s]
    have hd : T ≤ ‖s‖ := ht.trans (by rw [← hi]; exact abs_im_le_norm s)
    have hmain := HC N χ s (hr.symm ▸ hc)
    have hmain' : ‖logDeriv χ.LFunction s‖ ≤ A := by
      change ‖-(logDeriv χ.LFunction s)‖ ≤ _ at hmain
      rw [norm_neg, hr] at hmain
      have hrec : 1 / (c - 1) = Real.log u := by
        dsimp only [c, primitivePerronAbscissa]
        rw [add_sub_cancel_left, one_div, one_div, inv_inv]
      rw [hrec] at hmain
      refine hmain.trans ?_
      dsimp only [A]
      nlinarith only [mul_nonneg hC (sub_nonneg.mpr hlog)]
    change ‖primitivePerronIntegrand χ u s‖ ≤ _
    rw [norm_primitivePerronIntegrand _ hu₀, hr]
    exact (div_le_div_of_nonneg_right (mul_le_mul hmain' hcu (by positivity) (by positivity))
      (norm_nonneg _)).trans (div_le_div_of_nonneg_left (by positivity) hT hd)
  have hedge (a b : ℝ) (hab : a ≤ b) (hlen : b - a ≤ 1) (habs : ∀ t ∈ Ioc a b, T ≤ |t|) :
      ‖∫ t in a..b, F t‖ ≤ B := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => hpoint t
      (habs t (by simpa only [uIoc_of_le hab] using ht))).trans ?_
    rw [abs_of_nonneg (sub_nonneg.mpr hab)]
    exact (mul_le_mul_of_nonneg_left hlen hB).trans_eq (mul_one B)
  have hp := hedge T U hTU (by linarith only [hU]) fun t ht =>
    ht.1.le.trans (le_abs_self t)
  have hm := hedge (-U) (-T) (neg_le_neg hTU) (by linarith only [hU]) fun t ht =>
    (by linarith only [ht.2] : T ≤ -t).trans (neg_le_abs t)
  have e := intervalIntegral.integral_add_adjacent_intervals (f := F) (a := -U) (b := -T) (c := T)
    (hF.intervalIntegrable (μ := volume) _ _) (hF.intervalIntegrable _ _)
  have e' := intervalIntegral.integral_add_adjacent_intervals (f := F) (a := -U) (b := T) (c := U)
    (hF.intervalIntegrable (μ := volume) _ _) (hF.intervalIntegrable _ _)
  change ‖K * (∫ t in -U..U, F t) - K * (∫ t in -T..T, F t)‖ ≤ _
  rw [← e', ← e]
  have hcomb : K * (((∫ t in -U..-T, F t) + (∫ t in -T..T, F t)) + (∫ t in T..U, F t)) -
      K * (∫ t in -T..T, F t) = K * ((∫ t in -U..-T, F t) + (∫ t in T..U, F t)) := by ring
  rw [hcomb, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) norm_perron_vertical_factor_le_one).trans
    ((norm_add_le _ _).trans ((add_le_add hm hp).trans_eq ?_))
  dsimp only [B, A]
  ring

theorem primitive_perron_chebyshev :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (u T U : ℝ), 2 ≤ T → T ≤ u → T ≤ U → U ≤ T + 1 →
      ‖psi0 χ u + (if χ = 1 then (u : ℂ) else 0) - primitivePerronVertical χ u U‖ ≤
        C * (u * Real.log u ^ 2 / T + Real.log u) := by
  obtain ⟨C, hC, HC⟩ := GlobalTheory.PerronCoeff.truncated_perron_of_le_two_vonMangoldt
  obtain ⟨D, hD, HD⟩ := primitive_perron_right_tails
  refine ⟨C + 2 * D, by positivity, ?_⟩
  intro N _ χ u T U hT hTu hTU hU
  have hu := hT.trans hTu
  have ht₀ : 0 < T := by linarith only [hT]
  let M : ℂ := if χ = 1 then (u : ℂ) else 0
  let a (n : ℕ) := χ (n : ZMod N) * (Λ n : ℂ)
  have ha (n : ℕ) : ‖a n‖ ≤ 2 * Λ n := by
    dsimp only [a]
    rw [norm_mul, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hs := mul_le_of_le_one_left (vonMangoldt_nonneg (n := n)) (χ.norm_le_one (n : ZMod N))
    linarith only [hs, vonMangoldt_nonneg (n := n)]
  have hc₁ := (primitivePerronAbscissa_bounds hu).1
  have hv : ‖psi0 χ u + M - primitivePerronVertical χ u T‖ ≤
      C * (u * Real.log u ^ 2 / T + Real.log u) := by
    have hsum : (∑ n ∈ Finset.Icc 1 ⌊u⌋₊, a n) = psi0 χ u + M := by
      have h : psi0 χ u + M = ∑ n ∈ Finset.Icc 1 ⌊u⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) := by
        by_cases hχ : χ = 1 <;> simp [psi0, M, hχ]
      rw [h]
      exact Finset.sum_congr rfl fun n _ => mul_comm _ _
    have hh := HC a u T ha hT hTu
    rw [hsum] at hh
    refine le_of_eq_of_le ?_ hh
    unfold primitivePerronVertical
    congr 3
    refine intervalIntegral.integral_congr fun t _ => ?_
    have h := RHTower.LSeries_character_vonMangoldt_eq χ
      (s := (primitivePerronAbscissa u : ℂ) + t * I) (by simpa using hc₁)
    simpa only [primitivePerronIntegrand, primitivePerronAbscissa, logDeriv_apply, neg_div, a] using
      congrArg (fun z : ℂ => z * (u : ℂ) ^ ((primitivePerronAbscissa u : ℂ) + t * I) /
        ((primitivePerronAbscissa u : ℂ) + t * I)) h.symm
  have hlog : (1 / 2 : ℝ) ≤ Real.log u :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) hu)
  have hlog' : 0 ≤ Real.log u := by linarith only [hlog]
  have hh : u * Real.log u / T ≤ 2 * (u * Real.log u ^ 2 / T) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ ht₀.le
    have h := mul_nonneg hlog' (sub_nonneg.mpr hlog)
    exact (mul_le_mul_of_nonneg_left (by nlinarith only [h] : Real.log u ≤ 2 * Real.log u ^ 2)
      (by linarith only [hu])).trans_eq (by ring)
  have e : psi0 χ u + M - primitivePerronVertical χ u U =
      (psi0 χ u + M - primitivePerronVertical χ u T) -
        (primitivePerronVertical χ u U - primitivePerronVertical χ u T) := by ring
  change ‖psi0 χ u + M - _‖ ≤ _
  rw [e]
  refine (norm_sub_le _ _).trans ((add_le_add hv ((HD N χ u T U hu ht₀ hTU hU).trans
    (mul_le_mul_of_nonneg_left hh hD.le))).trans ?_)
  nlinarith only [mul_nonneg hD.le hlog']

end QH.PrimeProgressions
