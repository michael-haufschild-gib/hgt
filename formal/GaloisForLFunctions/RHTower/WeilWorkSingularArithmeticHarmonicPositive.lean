import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMeanSmall
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPositiveEuler
import GaloisForLFunctions.RHTower.WeilFullConeDeviationResidue
import GaloisForLFunctions.RHTower.DeningerAbelianLimit
import GaloisForLFunctions.RHTower.DeningerAbelSummation
import Mathlib.Analysis.PSeries

/-!
# Positive ordinary normalization for strict multiplicative Weil sources

Ordinary harmonic convergence is identified with the right Dirichlet limit
by finite Abel summation. The actual analytic source germ retains its unit
coefficient. A fractional Euler lower bound excludes a zero at one, so the
ordinary normalization is strictly positive. The final theorem pays every
analytic input of the finite Euler real-part bound from the source profile.
-/

open ArithmeticFunction Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open RHTower.WeilSpectral RHTower.WeilHerglotz

noncomputable section
namespace RHTower.WeilSingularArithmetic

private theorem harmonicPrefix_eq (f : ℕ → ℝ) (N : ℕ) :
    deningerPartialSum (fun n => f n / (n : ℝ)) N =
      ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ) := by
  have hz : f 0 / ((0 : ℕ) : ℝ) = 0 := by simp
  have he : (Finset.range (N + 1)).erase 0 = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
    omega
  rw [deningerPartialSum, ← Finset.sum_erase (Finset.range (N + 1)) hz, he]

theorem summable_harmonic_dirichlet_weight {f : ℕ → ℝ} (hb : ∀ n, |f n| ≤ 1)
    {t : ℝ} (ht : 0 < t) : Summable (fun n : ℕ => f n / (n : ℝ) * (n : ℝ) ^ (-t)) := by
  have hp : Summable (fun n : ℕ => ((n : ℝ) ^ (1 + t))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by linarith)
  apply Summable.of_norm_bounded hp
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, div_zero, zero_mul, norm_zero]
    positivity
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hnr,
    abs_of_pos (Real.rpow_pos_of_pos hnr _)]
  have hsplit : ((n : ℝ) ^ (1 + t))⁻¹ = (n : ℝ)⁻¹ * (n : ℝ) ^ (-t) := by
    rw [Real.rpow_add hnr, Real.rpow_one, Real.rpow_neg hnr.le, mul_inv]
  rw [hsplit]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hnr _).le
  rw [div_le_iff₀ hnr, inv_mul_cancel₀ hnr.ne']
  exact hb n

private theorem harmonic_dirichlet_finite_abel (f : ℕ → ℝ) (t : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 2), f n / (n : ℝ) * (n : ℝ) ^ (-t)) =
      deningerPartialSum (fun n => f n / (n : ℝ)) (N + 1) * (((N : ℝ) + 1) ^ (-t)) +
      ∑ m ∈ Finset.range N, deningerPartialSum (fun n => f n / (n : ℝ)) (m + 1) *
        deningerAbelWeight t m := by
  have h := deningerAbelSummation (fun n => f n / (n : ℝ))
    (fun n => (n : ℝ) ^ (-t)) (N + 1)
  rw [h]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  rw [Finset.sum_range_succ']
  simp only [deningerPartialSum_zero, Nat.cast_zero, div_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m _
  rw [deningerAbelWeight]
  simp only [Nat.cast_add, Nat.cast_one]
  congr 2
  congr 1
  ring

/-- The ordinary harmonic sum is the right Abel limit of its Dirichlet series. -/
theorem tendsto_harmonic_dirichlet_weight {f : ℕ → ℝ} (hb : ∀ n, |f n| ≤ 1)
    {H : ℝ} (hH : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ))
      atTop (𝓝 H)) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, f n / (n : ℝ) * (n : ℝ) ^ (-t))
      (𝓝[>] 0) (𝓝 H) := by
  let A (N : ℕ) := deningerPartialSum (fun n => f n / (n : ℝ)) N
  have hA : Tendsto A atTop (𝓝 H) := by
    simpa only [A, harmonicPrefix_eq] using hH
  have hshift : Tendsto (fun N => A (N + 1)) atTop (𝓝 H) :=
    hA.comp (tendsto_add_atTop_nat 1)
  obtain ⟨C, hC⟩ := deningerBounded_of_tendsto hshift
  have he (t : ℝ) (ht : 0 < t) :
      (∑' n : ℕ, f n / (n : ℝ) * (n : ℝ) ^ (-t)) =
        ∑' m : ℕ, A (m + 1) * deningerAbelWeight t m := by
    have hs := summable_harmonic_dirichlet_weight hb ht
    have hl := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 2)
    have hn : Tendsto (fun N : ℕ => ((N : ℝ) + 1)) atTop atTop := by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
    have hp : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ (-t)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop ht).comp hn
    have hbdry := hshift.mul hp
    rw [mul_zero] at hbdry
    have hav := deningerAbelAverage_summable hC ht
    have hr := hbdry.add hav.hasSum.tendsto_sum_nat
    rw [zero_add] at hr
    apply tendsto_nhds_unique hl
    refine hr.congr (fun N => ?_)
    exact (harmonic_dirichlet_finite_abel f t N).symm
  refine (deningerAbelian_tendsto hshift).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (he t ht).symm


theorem lSeries_term_ofReal_eq (f : ArithmeticFunction ℝ) (σ : ℝ) (n : ℕ) :
    LSeries.term (fun n => (f n : ℂ)) (σ : ℂ) n = (realDirichletWeight f σ n : ℂ) := by
  rw [LSeries.term_def₀ (by simp)]
  change (f n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)) = (f n * (n : ℝ) ^ (-σ) : ℝ)
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg n),
    Complex.ofReal_neg, Complex.ofReal_natCast]

theorem lSeries_ofReal_eq (f : ArithmeticFunction ℝ) (σ : ℝ) :
    LSeries (fun n => (f n : ℂ)) (σ : ℂ) = (∑' n : ℕ, realDirichletWeight f σ n : ℝ) := by
  rw [LSeries, Complex.ofReal_tsum]
  exact tsum_congr (lSeries_term_ofReal_eq f σ)

def multiplicativeSourceGerm {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (s : ℂ) : ℂ :=
  1 + logDeriv xi s - weilContinuation hW s

theorem analyticAt_multiplicativeSourceGerm {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    AnalyticAt ℂ (multiplicativeSourceGerm hW) 1 := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΦ : AnalyticAt ℂ (weilContinuation hW) 1 :=
    (differentiableOn_weilContinuation hW).analyticAt (hU.mem_nhds (by norm_num))
  have hd : AnalyticAt ℂ (deriv xi) 1 := (xi_analyticOnNhd Set.univ).deriv 1 (Set.mem_univ _)
  have hlog : AnalyticAt ℂ (logDeriv xi) 1 := by
    have he : logDeriv xi = fun s => deriv xi s / xi s := funext fun s => logDeriv_apply xi s
    rw [he]
    exact hd.div (xi_differentiable.analyticAt 1) (by norm_num [xi_one])
  exact (analyticAt_const.add hlog).sub hΦ

theorem multiplicativeSourceGerm_eq_realDirichlet {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) {σ : ℝ} (hσ : 1 < σ) :
    multiplicativeSourceGerm hW (σ : ℂ) = (∑' n : ℕ, realDirichletWeight f σ n : ℝ) := by
  have hfc : LSeriesSummable (fun n => (f n : ℂ)) (σ : ℂ) := by
    change Summable (fun n => LSeries.term (fun n => (f n : ℂ)) (σ : ℂ) n)
    simp only [lSeries_term_ofReal_eq, Complex.summable_ofReal]
    exact (realDirichletWeight_summable hb hσ).of_norm
  have hδ : LSeriesSummable LSeries.delta (σ : ℂ) := by
    change Summable (fun n => LSeries.term LSeries.delta (σ : ℂ) n)
    simp only [LSeries.term_delta]
    exact summable_of_ne_finset_zero (s := {1}) (by simp_all)
  have he : lamC lam - (fun n => (vonMangoldt n : ℂ)) =
      (fun n => (f n : ℂ)) - LSeries.delta := by
    funext n
    by_cases hn : 2 ≤ n
    · simp only [Pi.sub_apply, lamC, if_pos hn, hs n hn, LSeries.delta,
        if_neg (show n ≠ 1 by omega)]
      push_cast
      ring
    · have hn' : n = 0 ∨ n = 1 := by omega
      rcases hn' with rfl | rfl <;> simp [lamC, LSeries.delta, hf.map_one]
  calc
    _ = 1 + (logDeriv xi (σ : ℂ) - weilContinuation hW (σ : ℂ)) := by
      unfold multiplicativeSourceGerm
      ring
    _ = 1 + LSeries ((fun n => (f n : ℂ)) - LSeries.delta) (σ : ℂ) := by
      rw [logDeriv_xi_sub_weilContinuation_eq hW (by simpa using hσ),
        ← LSeries_sub (summable_term_lamC hW (by simpa using hσ))
          (ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)), he]
    _ = LSeries (fun n => (f n : ℂ)) (σ : ℂ) := by
      rw [LSeries_sub hfc hδ, LSeries_delta]
      simp
    _ = _ := lSeries_ofReal_eq f σ

theorem realDirichletWeight_one_add (f : ArithmeticFunction ℝ) (t : ℝ) (n : ℕ) :
    realDirichletWeight f (1 + t) n = f n / (n : ℝ) * (n : ℝ) ^ (-t) := by
  by_cases hn : n = 0
  · subst n; simp [realDirichletWeight]
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  change f n * (n : ℝ) ^ (-(1 + t)) = _
  rw [neg_add, Real.rpow_add hnr, Real.rpow_neg_one]
  ring

theorem tendsto_realDirichletWeight_one_add {f : ArithmeticFunction ℝ}
    (hb : ∀ n, |f n| ≤ 1) {H : ℝ}
    (hH : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H)) :
    Tendsto (fun t : ℝ => ∑' n : ℕ, realDirichletWeight f (1 + t) n)
      (𝓝[>] 0) (𝓝 H) := by
  simpa only [realDirichletWeight_one_add] using tendsto_harmonic_dirichlet_weight hb hH

/-- The analytic source value is the actual ordinary harmonic value. -/
theorem multiplicativeSourceGerm_one_eq_harmonic {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n)
    {H : ℝ} (hH : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ))
      atTop (𝓝 H)) : multiplicativeSourceGerm hW 1 = (H : ℂ) := by
  have hD := (Complex.continuous_ofReal.tendsto H).comp
    (tendsto_realDirichletWeight_one_add hb hH)
  have hG : Tendsto (fun t : ℝ => multiplicativeSourceGerm hW ((1 + t : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 (H : ℂ)) := by
    refine hD.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact (multiplicativeSourceGerm_eq_realDirichlet hf hb hW hs (by linarith : 1 < 1 + t)).symm
  have hp : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun t : ℝ => ((1 + t : ℝ) : ℂ)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique ((analyticAt_multiplicativeSourceGerm hW).continuousAt.tendsto.comp hp) hG

private theorem tendsto_one_add_real :
    Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 1) := by
  have hc : ContinuousAt (fun t : ℝ => ((1 + t : ℝ) : ℂ)) 0 := by fun_prop
  simpa using hc.tendsto.mono_left nhdsWithin_le_nhds

/-- The residue controls the actual zeta values on the right real ray. -/
theorem eventually_norm_zeta_one_add_le :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ‖riemannZeta ((1 + t : ℝ) : ℂ)‖ ≤ 2 / t := by
  have hp : Tendsto (fun t : ℝ => ((1 + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_add_real, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change ((1 + t : ℝ) : ℂ) ≠ 1
    intro he
    have hr := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.one_re] at hr
    linarith
  have hres := (riemannZeta_residue_one.comp hp).norm
  have hevent := hres.eventually (gt_mem_nhds (by norm_num : ‖(1 : ℂ)‖ < 2))
  filter_upwards [hevent, self_mem_nhdsWithin] with t hz ht
  change 0 < t at ht
  have he : ((1 + t : ℝ) : ℂ) - (1 : ℂ) = (t : ℂ) := by push_cast; ring
  change ‖(((1 + t : ℝ) : ℂ) - 1) * riemannZeta ((1 + t : ℝ) : ℂ)‖ < 2 at hz
  rw [norm_mul, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at hz
  exact (le_div_iff₀ ht).mpr (by nlinarith)

/-- The strict local profile gives a positive fractional lower bound at one. -/
theorem exists_dirichlet_fractional_lower {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpowers : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ t : ℝ in 𝓝[>] 0,
      A * t ^ θ ≤ ∑' n : ℕ, realDirichletWeight f (1 + t) n := by
  let c := Real.exp (-(3 * θ + 4 * θ ^ 2 / (1 - θ)) * invSquareTailConst)
  refine ⟨c * (2 : ℝ) ^ (-θ), mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  filter_upwards [eventually_norm_zeta_one_add_le, self_mem_nhdsWithin] with t hz ht
  change 0 < t at ht
  have hσ : 1 < 1 + t := by linarith
  have hzpos : 0 < ‖riemannZeta ((1 + t : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))
  have hpow := Real.rpow_le_rpow_of_nonpos hzpos hz (neg_nonpos.mpr hθ0)
  calc
    _ = c * (2 / t) ^ (-θ) := by
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 2) ht.le, Real.rpow_neg ht.le,
        div_inv_eq_mul, mul_assoc]
    _ ≤ c * ‖riemannZeta ((1 + t : ℝ) : ℂ)‖ ^ (-θ) :=
      mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ ≤ _ := realDirichletWeight_lower_zeta hf hb hθ0 hθ1 hpowers hσ

/-- A source germ cannot have an integer-order zero above a strict fractional
Euler lower bound. All bounds here are derived from the actual coefficients. -/
theorem multiplicativeSourceGerm_one_ne_zero {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpowers : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    multiplicativeSourceGerm hW 1 ≠ 0 := by
  intro hzero
  obtain ⟨A, hA, hlower⟩ := exists_dirichlet_fractional_lower hf hb hθ0 hθ1 hpowers
  obtain ⟨C, hC, hO⟩ :=
    (analyticAt_multiplicativeSourceGerm hW).differentiableAt.isBigO_sub.exists_pos
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (∑' n : ℕ, realDirichletWeight f (1 + t) n) ≤ C * t := by
    filter_upwards [tendsto_one_add_real.eventually hO.bound, self_mem_nhdsWithin] with t ht htpos
    change 0 < t at htpos
    have he : ((1 + t : ℝ) : ℂ) - (1 : ℂ) = (t : ℂ) := by push_cast; ring
    rw [hzero, sub_zero, multiplicativeSourceGerm_eq_realDirichlet hf hb hW hs
      (by linarith : 1 < 1 + t), he, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos] at ht
    exact (le_abs_self _).trans ht
  have hpower : Tendsto (fun t : ℝ => C * t ^ (1 - θ)) (𝓝[>] 0) (𝓝 0) := by
    have h := ((Real.continuous_rpow_const (by linarith : 0 ≤ 1 - θ)).tendsto 0).const_mul C
    simpa [Real.zero_rpow (by linarith : 1 - θ ≠ 0)] using h.mono_left nhdsWithin_le_nhds
  have hsmall := hpower.eventually (gt_mem_nhds hA)
  have hfalse : ∀ᶠ t : ℝ in 𝓝[>] 0, False := by
    filter_upwards [hlower, hupper, hsmall, self_mem_nhdsWithin] with t hl hu hsm ht
    change 0 < t at ht
    have hratio : A ≤ C * t ^ (1 - θ) := by
      rw [Real.rpow_sub ht, Real.rpow_one, ← mul_div_assoc, le_div_iff₀ (Real.rpow_pos_of_pos ht θ)]
      exact hl.trans hu
    exact (not_le_of_gt hsm) hratio
  exact hfalse.exists.elim (fun _ h => h)

/-- The ordinary harmonic value of the actual strict-profile source is positive. -/
theorem harmonic_pos_of_strict_multiplicative_source {f : ArithmeticFunction ℝ}
    (hf : f.IsMultiplicative) (hb : ∀ n, |f n| ≤ 1) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hpowers : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n)
    {H : ℝ} (hH : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ))
      atTop (𝓝 H)) : 0 < H := by
  have hH0 : 0 ≤ H := by
    apply ge_of_tendsto (tendsto_realDirichletWeight_one_add hb hH)
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    exact (Real.exp_pos _).le.trans
      (realDirichletWeight_lower_exp hf hb hθ0 hθ1 hpowers (by linarith))
  have hne := multiplicativeSourceGerm_one_ne_zero hf hb hθ0 hθ1 hpowers hW hs
  rw [multiplicativeSourceGerm_one_eq_harmonic hf hb hW hs hH, Complex.ofReal_ne_zero] at hne
  exact lt_of_le_of_ne hH0 hne.symm

/-- Full source positivity and the strict multiplicative profile produce the
positive ordinary normalization and every finite Euler real-part bound. -/
theorem exists_positive_finiteEuler_bound_of_strict_multiplicative_source
    {f : ArithmeticFunction ℝ} (hf : f.IsMultiplicative) {θ : ℝ} (hθ : θ < 1)
    (hb : ∀ p : ℕ, p.Prime → ∀ k : ℕ, 1 ≤ k → |f (p ^ k)| ≤ θ)
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hs : ∀ n : ℕ, 2 ≤ n → lam n = vonMangoldt n + f n) :
    ∃ H : ℝ,
      Tendsto (fun N => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℝ)) atTop (𝓝 H) ∧
      0 < H ∧ H ≤ 1 ∧
      ∀ (P : Finset ℕ) (_ : ∀ p ∈ P, p.Prime) (x : UnitAddTorus P),
        (H / ∏ p ∈ P, localEulerValue f p) *
          (∏ p : P, boundedFun (fun k => (f ((p : ℕ) ^ k) : ℂ))
            ((primeRadius p : ℂ) * fourier 1 (x p))).re ≤ 1 := by
  obtain ⟨H, hH, hHle, hbound⟩ :=
    exists_finiteEuler_bound_of_strict_multiplicative_source hf hθ hb hW hs
  have hθ0 : 0 ≤ θ := (abs_nonneg _).trans (hb 2 Nat.prime_two 1 le_rfl)
  have hglobal (n : ℕ) : |f n| ≤ 1 := by
    simpa [primeAttenuation] using
      abs_le_primeAttenuation hf hθ0 hθ.le hb ∅ (by simp) n
  exact ⟨H, hH, harmonic_pos_of_strict_multiplicative_source hf hglobal hθ0 hθ hb hW hs hH,
    hHle, hbound⟩

end RHTower.WeilSingularArithmetic
