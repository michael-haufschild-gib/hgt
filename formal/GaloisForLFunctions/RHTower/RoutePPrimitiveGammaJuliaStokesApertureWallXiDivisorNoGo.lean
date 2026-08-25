import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit
import GaloisForLFunctions.RHTower.RoutePPrimitiveBaseCauchyCapacityReduction
import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.RHTower.CompletedZetaGrowth
import GaloisForLFunctions.RHTower.XiEntireReal
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesExpWallXiTauProjectiveJetNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallThetaJetSeparation
import Mathlib.Analysis.MeanInequalities

/-!
# Exact aperture-wall/Xi divisor obstruction

The balanced exponential aperture wall is the ordinary Fredholm limit produced by the two
reflected Hellinger channels.  This file proves that its divisor cannot equal the nontrivial
divisor of centered completed Xi.

The decisive point is canonicality, not positivity.  The wall kernel is an exact positive
Cauchy-cubic Gram matrix with diagonal one.  Hence every Fredholm integrand has determinant norm
at most one, every coefficient is bounded by `1 / n!`, and the balanced determinant has order at
most one.  Equal divisors would then leave an entire zero-free quotient.  Evenness removes its
linear exponential gauge and normalization removes its constant gauge, forcing equality with
normalized `XiC`.  Source arithmetic disproves that equality at the quadratic jet:
the wall value is `-32 / 35`, while the Xi value is the negative normalized theta moment, which is
strictly different.

Thus exact aperture-wall identification is not a missing theorem for this operator: it is false.
A surviving determinant carrier must change the divisor-bearing source operator itself rather than
add a zero-free scalar correction.
-/

open Complex Matrix MeasureTheory Filter Topology Set
open scoped BigOperators ComplexOrder

namespace RHTower

/-- A positive semidefinite `n x n` matrix of trace `n` has determinant norm at most one. -/
theorem norm_det_le_one_of_posSemidef_of_trace_eq_card
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = (n : ℂ)) : ‖A.det‖ ≤ 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  let e : Fin n → ℝ := hA.isHermitian.eigenvalues
  have he_nonneg (i : Fin n) : 0 ≤ e i := hA.eigenvalues_nonneg i
  have hsum : ∑ i : Fin n, e i = (n : ℝ) := by
    have h := congrArg Complex.re htrace
    rw [hA.isHermitian.trace_eq_sum_eigenvalues] at h
    simpa [e] using h
  have hgeom : (∏ i : Fin n, e i) ^ ((n : ℝ)⁻¹) ≤ 1 := by
    have h := Real.geom_mean_le_arith_mean
      (Finset.univ : Finset (Fin n)) (fun _ => (1 : ℝ)) e
      (by simp) (by simpa using hnpos) (by simpa using he_nonneg)
    simpa [hsum, hn, e] using h
  have hprod_nonneg : 0 ≤ ∏ i : Fin n, e i :=
    Finset.prod_nonneg fun i _ => he_nonneg i
  have hprod_le : ∏ i : Fin n, e i ≤ 1 := by
    rcases hprod_nonneg.eq_or_lt with hp0 | hp
    · rw [← hp0]
      norm_num
    · have hcases := (Real.rpow_le_one_iff_of_pos hp).mp hgeom
      rcases hcases with hbad | hgood
      · exact False.elim ((not_le_of_gt (inv_pos.mpr hnpos)) hbad.2)
      · exact hgood.1
  rw [hA.isHermitian.det_eq_prod_eigenvalues, norm_prod]
  simpa [e, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hA.eigenvalues_nonneg _)] using hprod_le

/-- The mean-one exponential wall matrix is the diagonal congruence of the positive
Cauchy-cubic kernel. -/
theorem routePPrimitiveGammaJuliaStokesExpWallFredholmMatrix_posSemidef
    (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1) :
    (routePPrimitiveGammaJuliaStokesWallFredholmMatrix
      (ProbabilityTheory.expMeasure 1) n x).PosSemidef := by
  let a : Fin n → ℝ := fun i =>
    GaloisForLFunctions.HTGeometry.quantile (ProbabilityTheory.expMeasure 1) (x i)
  have ha (i : Fin n) : 0 < a i := by
    change 0 < GaloisForLFunctions.HTGeometry.quantile
      (ProbabilityTheory.expMeasure 1) (x i)
    rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one
      (hx i).1 (hx i).2]
    rw [neg_pos, Real.log_neg_iff (by linarith [(hx i).2])]
    linarith [(hx i).1, (hx i).2]
  let D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal fun i => ((2 * Real.sqrt (a i) ^ 3 : ℝ) : ℂ)
  let B : Matrix (Fin n) (Fin n) ℂ :=
    routePBaseCauchyCubicKernelMatrix 1 a (fun _ => 0)
  have hB : B.PosSemidef :=
    routePBaseCauchyCubicKernelMatrix_posSemidef (by norm_num) ha
  have hfactor :
      routePPrimitiveGammaJuliaStokesWallFredholmMatrix
          (ProbabilityTheory.expMeasure 1) n x = D * B * Dᴴ := by
    ext i j
    rw [routePPrimitiveGammaJuliaStokesWallFredholmMatrix,
      routePPrimitiveGammaJuliaStokesWallQuantileKernel,
      if_pos ⟨hx i, hx j⟩]
    change (routePPrimitiveGammaJuliaStokesWallCubicKernel (a i) (a j) : ℂ) = _
    simp [D, B, Matrix.diagonal_mul, Matrix.mul_diagonal,
      routePBaseCauchyCubicKernelMatrix,
      routePBaseCauchyCubicKernel, routePCollisionPairFrequency]
    rw [routePPrimitiveGammaJuliaStokesWallCubicKernel]
    push_cast
    ring
  rw [hfactor]
  exact hB.mul_mul_conjTranspose_same D

/-- Every exponential-wall matrix has trace equal to its matrix size. -/
theorem routePPrimitiveGammaJuliaStokesExpWallFredholmMatrix_trace_eq_card
    (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1) :
    (routePPrimitiveGammaJuliaStokesWallFredholmMatrix
      (ProbabilityTheory.expMeasure 1) n x).trace = (n : ℂ) := by
  have hdiag (i : Fin n) :
      routePPrimitiveGammaJuliaStokesWallFredholmMatrix
        (ProbabilityTheory.expMeasure 1) n x i i = 1 := by
    rw [routePPrimitiveGammaJuliaStokesWallFredholmMatrix,
      routePPrimitiveGammaJuliaStokesWallQuantileKernel,
      if_pos ⟨hx i, hx i⟩]
    apply congrArg Complex.ofReal
    apply routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal
    rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one
      (hx i).1 (hx i).2]
    rw [neg_pos, Real.log_neg_iff (by linarith [(hx i).2])]
    linarith [(hx i).1]
  calc
    (routePPrimitiveGammaJuliaStokesWallFredholmMatrix
        (ProbabilityTheory.expMeasure 1) n x).trace = ∑ i : Fin n, (1 : ℂ) := by
      rw [Matrix.trace]
      exact Finset.sum_congr rfl fun i _ => hdiag i
    _ = (n : ℂ) := by simp

/-- Uniform determinant bound for every finite wall configuration. -/
theorem norm_routePPrimitiveGammaJuliaStokesExpWallFredholmIntegrand_le_one
    (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
      (ProbabilityTheory.expMeasure 1) n x‖ ≤ 1 := by
  exact norm_det_le_one_of_posSemidef_of_trace_eq_card
    (routePPrimitiveGammaJuliaStokesExpWallFredholmMatrix_posSemidef n x hx)
    (routePPrimitiveGammaJuliaStokesExpWallFredholmMatrix_trace_eq_card n x hx)

/-- The exact positive Gram structure improves Hadamard's generic estimate to `1 / n!`. -/
theorem norm_routePPrimitiveGammaJuliaStokesExpWallFredholmCoefficient_le_inv_factorial
    (n : ℕ) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (ProbabilityTheory.expMeasure 1) n‖ ≤ 1 / (n.factorial : ℝ) := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n.factorial)
  have h := norm_integral_le_of_norm_le_const
    (μ := routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n)
    (ae_routePPrimitiveGammaJuliaStokesWallUnitCube_all_mem_Ioo n |>.mono
      fun x hx => norm_routePPrimitiveGammaJuliaStokesExpWallFredholmIntegrand_le_one n x hx)
  simpa [Measure.real,
    routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ] using h

/-- The one-channel exponential wall determinant has exponential type at most one. -/
theorem norm_routePPrimitiveGammaJuliaStokesExpWallFredholmEntireDet_le_exp
    (z : ℂ) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1) z‖ ≤ Real.exp ‖z‖ := by
  let f : ℕ → ℂ := fun n => z ^ n *
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (ProbabilityTheory.expMeasure 1) n
  let g : ℕ → ℝ := fun n => ‖z‖ ^ n / (n.factorial : ℝ)
  have hg : Summable g :=
    (NormedSpace.expSeries_div_hasSum_exp ‖z‖).summable
  have hfg (n : ℕ) : ‖f n‖ ≤ g n := by
    dsimp only [f, g]
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left
      (by simpa [one_div] using
        norm_routePPrimitiveGammaJuliaStokesExpWallFredholmCoefficient_le_inv_factorial n)
      (pow_nonneg (norm_nonneg z) n)
  have hfnorm : Summable fun n => ‖f n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) hfg hg
  rw [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet]
  change ‖∑' n, f n‖ ≤ _
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hfnorm
    _ ≤ ∑' n, g n := hfnorm.tsum_le_tsum hfg hg
    _ = Real.exp ‖z‖ := by
      simpa only [g, Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp ‖z‖).tsum_eq

/-- Balanced ordinary determinant at the exact exponential aperture wall. -/
noncomputable def routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
    (z : ℂ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1) z *
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
      (ProbabilityTheory.expMeasure 1) (-z)

theorem norm_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_le
    (z : ℂ) :
    ‖routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z‖ ≤
      Real.exp (4 * (1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
  have hprod : ‖routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z‖ ≤
      Real.exp (2 * ‖z‖) := by
    rw [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet, norm_mul]
    calc
      _ ≤ Real.exp ‖z‖ * Real.exp ‖-z‖ :=
        mul_le_mul
          (norm_routePPrimitiveGammaJuliaStokesExpWallFredholmEntireDet_le_exp z)
          (norm_routePPrimitiveGammaJuliaStokesExpWallFredholmEntireDet_le_exp (-z))
          (norm_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (2 * ‖z‖) := by
        rw [norm_neg, ← Real.exp_add]
        congr 1
        ring
  refine hprod.trans (Real.exp_le_exp.mpr ?_)
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 + ‖z‖) := by
    have hmono : Real.log 2 ≤ Real.log (2 + ‖z‖) :=
      Real.strictMonoOn_log.monotoneOn
        (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (2 + ‖z‖ : ℝ) ∈ Set.Ioi 0 by
          change 0 < (2 : ℝ) + ‖z‖
          positivity)
        (by linarith [norm_nonneg z])
    exact (show (1 / 2 : ℝ) ≤ Real.log 2 by
      linarith [Real.log_two_gt_d9]).trans hmono
  nlinarith [norm_nonneg z]

theorem differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet :
    Differentiable ℂ routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet := by
  letI : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure one_pos
  exact (differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (ProbabilityTheory.expMeasure 1)
    GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero).mul
      ((differentiable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (ProbabilityTheory.expMeasure 1)
        GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero).comp differentiable_neg)

@[simp] theorem routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_zero :
    routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet 0 = 1 := by
  simp [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet,
    routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_zero]

theorem routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_even (z : ℂ) :
    routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet (-z) =
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z := by
  simp only [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet, neg_neg]
  ring

theorem analyticOrderAt_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_ne_top
    (z : ℂ) :
    analyticOrderAt routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
  apply han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr (by
    rw [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_zero]
    exact one_ne_zero))]
  exact ENat.zero_ne_top

theorem analyticOrderAt_XiC_ne_top (z : ℂ) : analyticOrderAt XiC z ≠ ⊤ := by
  have han : AnalyticOnNhd ℂ XiC Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable
  apply han.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := 0) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  rw [analyticOrderAt_eq_zero.mpr (Or.inr XiC_zero_ne)]
  exact ENat.zero_ne_top

/-- For normalized even order-one entire functions, exact divisor equality forces function
equality. -/
theorem routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_eq_XiC_normalized_of_same_divisor
    (horder : ∀ z : ℂ,
      analyticOrderAt routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z =
        analyticOrderAt XiC z) (z : ℂ) :
    routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z = XiC z / XiC 0 := by
  have hWallAn : AnalyticOnNhd ℂ
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
  have hXiAn : AnalyticOnNhd ℂ XiC Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable
  obtain ⟨h, hhdiff, hhne, hfac⟩ :=
    GaloisForLFunctions.EntireQuotient.exists_entire_nonvanishing_quotient
      hWallAn hXiAn
      analyticOrderAt_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_ne_top
      horder (z₀ := 0) XiC_zero_ne
  have hWallOrd : ∀ w,
      meromorphicOrderAt routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet w ≠ ⊤ := by
    intro w
    rw [(hWallAn w (Set.mem_univ w)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_ne_top w]
  have hXiOrd : ∀ w, meromorphicOrderAt XiC w ≠ ⊤ := by
    intro w
    rw [(hXiAn w (Set.mem_univ w)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_XiC_ne_top w]
  have hXiNear : ∀ᶠ w in nhds (0 : ℂ), XiC w ≠ 0 :=
    XiC_differentiable.continuous.continuousAt.eventually_ne XiC_zero_ne
  have hlocal : (fun w => h (-w)) =ᶠ[nhds 0] h := by
    filter_upwards [hXiNear] with w hw
    have hn := hfac (-w)
    have hp := hfac w
    rw [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_even, XiC_even] at hn
    exact mul_right_cancel₀ hw (hn.symm.trans hp)
  have hhan : AnalyticOnNhd ℂ h Set.univ :=
    fun w _ => Differentiable.analyticAt hhdiff w
  have hnegAn : AnalyticOnNhd ℂ (fun w => h (-w)) Set.univ := by
    intro w _
    exact (hhan (-w) (Set.mem_univ _)).comp
      (by fun_prop : AnalyticAt ℂ (fun u : ℂ => -u) w)
  have hheven : ∀ w, h (-w) = h w :=
    congrFun (hnegAn.eq_of_eventuallyEq hhan hlocal)
  obtain ⟨C, hC, hXiGrowth⟩ := XiC_order
  have hproxXi :=
    OrderOneRigidity.proximity_isLittleO_sq_of_growth hC.le
      XiC_differentiable hXiGrowth
  have hproxWall :=
    OrderOneRigidity.proximity_isLittleO_sq_of_growth (C := 4)
      (by norm_num)
      differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
      norm_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_le
  have hconst := OrderOneRigidity.exists_const_of_even_entire_quotient
    XiC_differentiable
    differentiable_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet
    hhdiff hXiOrd hWallOrd hhne hfac hheven hproxXi hproxWall z
  have hzero := hfac 0
  rw [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_zero] at hzero
  have hh0 : h 0 = (XiC 0)⁻¹ := by
    rw [inv_eq_one_div]
    exact (eq_div_iff XiC_zero_ne).2 hzero.symm
  rw [hfac z, hconst, hh0]
  field_simp [XiC_zero_ne]

/-- The balanced aperture wall's quadratic derivative is the fixed source value `-32 / 35`. -/
theorem iteratedDeriv_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_two :
    iteratedDeriv 2 routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet 0 =
      (-32 / 35 : ℂ) := by
  have hfun : routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet =
      routePPrimitiveGammaJuliaStokesExpWallScaledTau 1 *
        routePPrimitiveGammaJuliaStokesExpWallScaledTau (-1) := by
    funext z
    simp [routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet,
      routePPrimitiveGammaJuliaStokesExpWallScaledTau]
  rw [hfun, iteratedDeriv_mul
    (differentiable_routePPrimitiveGammaJuliaStokesExpWallScaledTau 1).contDiff.contDiffAt
    (differentiable_routePPrimitiveGammaJuliaStokesExpWallScaledTau (-1)).contDiff.contDiffAt]
  norm_num [Finset.sum_range_succ,
    routePPrimitiveGammaJuliaStokesExpWallScaledTau_zero,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesExpWallScaledTau_two]

/-- The normalized Xi quadratic derivative is the negative normalized theta second moment. -/
theorem iteratedDeriv_XiC_normalized_two :
    iteratedDeriv 2 (fun z => XiC z / XiC 0) 0 =
      -((thetaCuspNormalizedEvenMoment 1 : ℝ) : ℂ) := by
  have hXi0 : XiC 0 = (thetaCuspRawEvenMoment 0 : ℂ) := by
    simpa using iteratedDeriv_XiC_zero_eq_rawEvenMoment 0
  rw [show (fun z => XiC z / XiC 0) =
      fun z => (XiC 0)⁻¹ * XiC z by
        funext z
        simp [div_eq_mul_inv, mul_comm]]
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_XiC_zero_eq_rawEvenMoment 1, hXi0]
  rw [thetaCuspNormalizedEvenMoment]
  push_cast
  field_simp [ne_of_gt thetaCuspRawEvenMoment_zero_pos]

/-- Exact multiplicity-bearing identification of the balanced exponential aperture-wall divisor
with the nontrivial centered Xi divisor. -/
def RoutePPrimitiveGammaJuliaStokesExactApertureWallXiDivisorIdentification : Prop :=
  ∀ z : ℂ,
    analyticOrderAt routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet z =
      analyticOrderAt XiC z

/-- **Exact aperture-wall no-go.** The source-built ordinary Fredholm wall has a different divisor
from centered completed Xi. -/
theorem not_routePPrimitiveGammaJuliaStokesExactApertureWallXiDivisorIdentification :
    ¬ RoutePPrimitiveGammaJuliaStokesExactApertureWallXiDivisorIdentification := by
  intro horder
  have hfun : routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet =
      fun z => XiC z / XiC 0 := by
    funext z
    exact
      routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_eq_XiC_normalized_of_same_divisor
        horder z
  have hjet := congrArg (fun f : ℂ → ℂ => iteratedDeriv 2 f 0) hfun
  rw [iteratedDeriv_routePPrimitiveGammaJuliaStokesExactApertureWallEntireDet_two,
    iteratedDeriv_XiC_normalized_two] at hjet
  have hreal := congrArg Complex.re hjet
  norm_num at hreal
  exact thetaCuspNormalizedEvenMoment_one_ne_wallSignedSquareCalibration hreal.symm

end RHTower
