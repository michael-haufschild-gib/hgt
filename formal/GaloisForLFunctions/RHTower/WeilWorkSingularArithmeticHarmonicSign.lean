import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleSign
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSummatory

/-!
# The ordinary source harmonic limit is nonpositive

The centered source series is holomorphic across one by ordinary Dirichlet
convergence. Its value there identifies the ordinary harmonic limit with
the signed Gaussian pole coefficient. No local-mass premise is used.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower.WeilSingularArithmetic

theorem centered_source_dirichletSum_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    dirichletSum (fun n => WeilHerglotz.lamC lam (n + 1) - 1) 1 =
      sourcePoleNumerator hW 1 - 2 * (Real.eulerMascheroniConstant : ℂ) := by
  let b : ℕ → ℂ := fun n => WeilHerglotz.lamC lam (n + 1) - 1
  have hb {s : ℂ} (hs : 1 / 2 < s.re) : DirichletConvergesAt b s :=
    centered_source_dirichletConvergesAt hW hs
  have hc : ContinuousAt (dirichletSum b) 1 :=
    ((differentiableOn_dirichletSum (hb (s := (3 / 4 : ℂ)) (by norm_num))).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).continuousAt
  have he {s : ℂ} (hs : 1 < s.re) : dirichletSum b s =
      zetaArchimedeanDatum s - WeilSpectral.weilContinuation hW s -
        (riemannZeta s - 1 / (s - 1)) := by
    have hl : LSeriesSummable (WeilHerglotz.lamC lam - 1) s :=
      LSeriesSummable.sub (WeilHerglotz.summable_term_lamC hW hs) (LSeriesSummable_one_iff.mpr hs)
    have hh : HasSum (fun n => LSeries.term (WeilHerglotz.lamC lam - 1) s (n + 1))
        (LSeries (WeilHerglotz.lamC lam - 1) s) := by
      have := (hasSum_nat_add_iff' 1).mpr hl.LSeriesHasSum
      simpa [LSeries.term_zero] using this
    have ht : Tendsto (fun N => dirichletPartialSum b N s) atTop
        (𝓝 (LSeries (WeilHerglotz.lamC lam - 1) s)) := by
      refine hh.tendsto_sum_nat.congr fun N => Finset.sum_congr rfl fun n _ => ?_
      exact term_succ_eq (WeilHerglotz.lamC lam - 1) s n
    rw [tendsto_nhds_unique (tendsto_dirichletSum (hb (by linarith))) ht,
      LSeries_sub (WeilHerglotz.summable_term_lamC hW hs) (LSeriesSummable_one_iff.mpr hs),
      LSeries_one_eq_riemannZeta hs, WeilSpectral.weilContinuation_eq hW hs,
      WeilHerglotz.weilFunction, zetaArchimedeanDatum]
    ring
  have hR : ContinuousAt (fun s : ℂ => zetaArchimedeanDatum s -
      WeilSpectral.weilContinuation hW s) 1 :=
    (WeilFiniteType.differentiableAt_zetaArchimedeanDatum (by norm_num)).continuousAt.sub
      ((WeilSpectral.differentiableOn_weilContinuation hW).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).continuousAt
  have hcast := tendsto_ofReal_nhdsWithin_ne_one.mono_right nhdsWithin_le_nhds
  have ht := (hR.tendsto.comp hcast).sub tendsto_riemannZeta_sub_pole_real
  have hd := hc.tendsto.comp hcast
  have ht' : Tendsto (fun σ : ℝ => dirichletSum b (σ : ℂ)) (𝓝[>] 1)
      (𝓝 (zetaArchimedeanDatum 1 - WeilSpectral.weilContinuation hW 1 -
        (Real.eulerMascheroniConstant : ℂ))) := by
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (he (s := (σ : ℂ)) hσ).symm
  change dirichletSum b 1 = _
  rw [tendsto_nhds_unique hd ht', sourcePoleNumerator_one]
  ring

theorem tendsto_coneDeviation_harmonic_pole {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam n / n) atTop (𝓝 (sourcePoleNumerator hW 1).re) := by
  let v : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  let b : ℕ → ℂ := fun n => WeilHerglotz.lamC lam (n + 1) - 1
  have hL := tendsto_dirichletSum (centered_source_dirichletConvergesAt hW (s := 1) (by norm_num))
  have hc : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (v (n + 1) - 1) / ((n : ℝ) + 1)) atTop (𝓝 (dirichletSum b 1).re) := by
    have ht (n : ℕ) : ((v (n + 1) : ℂ) - 1) *
        ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ))) =
        (((v (n + 1) - 1) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
      rw [Complex.cpow_neg_one]
      push_cast
      rfl
    have hreal := Complex.continuous_re.tendsto _ |>.comp hL
    refine hreal.congr fun N => ?_
    change (∑ n ∈ Finset.range N, ((v (n + 1) : ℂ) - 1) *
      ((((n : ℝ) + 1 : ℝ) : ℂ) ^ (-(1 : ℂ)))).re = _
    simp_rw [ht]
    rw [← Complex.ofReal_sum]
    rfl
  have hh : Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1),
      1 / ((n : ℝ) + 1)) - Real.log ((N : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    have ht := Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
    refine ht.congr fun N => ?_
    simp [harmonic, Nat.cast_add, Nat.cast_one, one_div]
  have hdev := ((hc.comp (tendsto_add_atTop_nat 1)).add hh).sub tendsto_vonMangoldt_harmonicWeighted
  have heL : ((dirichletSum b 1).re + Real.eulerMascheroniConstant) -
      (Real.eulerMascheroniConstant + mertensAbelTail) = (sourcePoleNumerator hW 1).re := by
    dsimp only [b]
    rw [centered_source_dirichletSum_one hW, mertensAbelTail_eq]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    ring
  rw [heL] at hdev
  have hdev' : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (sourcePoleNumerator hW 1).re) := by
    refine hdev.congr fun N => ?_
    simp only [Function.comp_apply]
    have hterm (n : ℕ) : WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1) =
        (v (n + 1) - 1) / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) -
          ArithmeticFunction.vonMangoldt (n + 1) / ((n : ℝ) + 1) := by
      have heq : WeilOneSided.coneDeviation lam (n + 1) =
          v (n + 1) - ArithmeticFunction.vonMangoldt (n + 1) := by
        by_cases hn : 2 ≤ n + 1
        · simp [v, WeilOneSided.coneDeviation, hn]
        · have hn0 : n = 0 := by omega
          subst n
          simp [v, WeilOneSided.coneDeviation]
      rw [heq]
      ring
    simp_rw [hterm]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    ring
  have hreindex (N : ℕ) : (∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam (n + 1) / ((n : ℝ) + 1)) =
      ∑ n ∈ Finset.range (N + 2), WeilOneSided.coneDeviation lam n / n := by
    conv_rhs => rw [show N + 2 = (N + 1) + 1 by omega, Finset.sum_range_succ']
    simp [WeilOneSided.coneDeviation]
  exact (tendsto_add_atTop_iff_nat 1).mp (hdev'.congr hreindex)

/-- The ordinary harmonic deviation limit exists and is nonpositive for every
full-positive source, with no coefficient sign or local-mass assumption. -/
theorem exists_nonpos_tendsto_coneDeviation_harmonic {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ L : ℝ, L ≤ 0 ∧ Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N + 1),
      WeilOneSided.coneDeviation lam n / n) atTop (𝓝 L) :=
  ⟨(sourcePoleNumerator hW 1).re, re_sourcePoleNumerator_one_nonpos hW,
    tendsto_coneDeviation_harmonic_pole hW⟩

end RHTower.WeilSingularArithmetic
