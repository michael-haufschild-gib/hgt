import GaloisForLFunctions.RHTower.XiMassCriticalDiagonalPrimeCoronaZeroDensity
import GaloisForLFunctions.RHTower.XiMassZeroFreeProfiledPrimeEnvelope

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Zero-free strip width adds a height-amplified defect on the critical mass wall. -/
theorem xiMass_critical_phase_defect_zeroFree
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (_hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1)
    (q : XiZeroCopy) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ (2 : ℕ) + A) -
        4 * σ * A * R * xiWardZeroFreeMargin R := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  have hA : 0 < A := by dsimp only [A]; linarith
  have hR : 0 < R := by dsimp only [R]; exact xiPoissonAbstract.re_pos q
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.re_lt_csqrtRe_massArg haHalf q
    linarith
  have hsq : A ^ (2 : ℕ) + R ^ (2 : ℕ) + A ≤ M ^ (2 : ℕ) := by
    dsimp only [A, R, M]
    simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt] using
      xiPoissonAbstract.sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re ha q
  have hprod := xiPoissonAbstract.re_mul_im_mass haHalf q
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    rw [abs_mul, abs_mul] at habs
    change |M| * |K| = |R| * |J| at habs
    simpa only [abs_of_pos hM, abs_of_pos hR] using habs
  have himAbs : |J| = |(xiSpectralPoint q).im| := by
    dsimp only [J]
    unfold xiPoissonPoint
    split_ifs <;> simp
  have hJ : |J| ≤ 1 / 2 - xiWardZeroFreeMargin R := by
    rw [himAbs]
    simpa only [R] using abs_xiSpectralPoint_im_le_half_sub_zeroFreeMargin q
  have hmarginPos : 0 < xiWardZeroFreeMargin R := xiWardZeroFreeMargin_pos R
  have hMK : M * |K| ≤ R * (1 / 2 - xiWardZeroFreeMargin R) := by
    rw [hprodAbs]
    exact mul_le_mul_of_nonneg_left hJ hR.le
  have huK : M * (u * K) ≤
      |u| * (R * (1 / 2 - xiWardZeroFreeMargin R)) := by
    calc
      M * (u * K) ≤ M * |u * K| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hM.le
      _ = |u| * (M * |K|) := by rw [abs_mul]; ring
      _ ≤ |u| * (R * (1 / 2 - xiWardZeroFreeMargin R)) :=
        mul_le_mul_of_nonneg_left hMK (abs_nonneg u)
  have hfactorNonneg : 0 ≤ R * (1 / 2 - xiWardZeroFreeMargin R) := by
    have hmle := xiWardZeroFreeMargin_le_half R
    positivity
  have hconeMul := mul_le_mul_of_nonneg_right hcone hfactorNonneg
  have hucrit :
      |u| * (R * (1 / 2 - xiWardZeroFreeMargin R)) ≤
        4 * σ * A * (R * (1 / 2 - xiWardZeroFreeMargin R)) := by
    calc
      |u| * (R * (1 / 2 - xiWardZeroFreeMargin R)) =
          (4 * σ * v) * (|u| * (R * (1 / 2 - xiWardZeroFreeMargin R))) := by
            rw [hcritical]
            ring
      _ = 4 * σ * ((v * |u|) *
          (R * (1 / 2 - xiWardZeroFreeMargin R))) := by ring
      _ ≤ 4 * σ * (A *
          (R * (1 / 2 - xiWardZeroFreeMargin R))) := by
            exact mul_le_mul_of_nonneg_left hconeMul (by positivity)
      _ = 4 * σ * A * (R * (1 / 2 - xiWardZeroFreeMargin R)) := by ring
  have hphase : M * (-σ * M + u * K) ≤
      -σ * M ^ (2 : ℕ) + 4 * σ * A *
        (R * (1 / 2 - xiWardZeroFreeMargin R)) := by
    nlinarith
  change M * (-σ * M + u * K) ≤
    -σ * ((A - R) ^ (2 : ℕ) + A) -
      4 * σ * A * R * xiWardZeroFreeMargin R
  nlinarith

/-- Inside the diagonal corona, the zero-free width yields a uniform decaying exponent. -/
theorem norm_xiMassFamily_term_le_critical_zeroFree
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1)
    {q : XiZeroCopy} (hq : q ∈ xiMassCriticalDiagonalCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
      Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  have hA : 3 / 2 ≤ A := by dsimp only [A]; linarith
  have hR : 0 < R := by dsimp only [R]; exact xiPoissonAbstract.re_pos q
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.re_lt_csqrtRe_massArg haHalf q
    linarith
  have hmem := xiPoissonAbstract.mem_criticalDiagonalCorona.mp hq
  have hRlo : A / 2 ≤ R := by
    simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt, A, R] using hmem.1
  have hRhi : R ≤ 2 * A := by
    simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt, A, R] using hmem.2
  have hMupRaw := xiPoissonAbstract.csqrtRe_massArg_le_add haHalf q
  have hMup : M ≤ A + R + 1 / 2 := by
    have h : M ≤ R + a := by
      dsimp only [M, R]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using hMupRaw
    dsimp only [A]
    linarith
  have hMupA : M ≤ (10 / 3 : ℝ) * A := by nlinarith
  have hratio : (3 / 20 : ℝ) * A * M ≤ A * R := by
    have hmul := mul_le_mul_of_nonneg_left hMupA (show 0 ≤ (3 / 20 : ℝ) * A by positivity)
    nlinarith
  have hmarginAnti : xiWardZeroFreeMargin (2 * A) ≤ xiWardZeroFreeMargin R := by
    apply xiWardZeroFreeMargin_anti
    rw [abs_of_nonneg hR.le, abs_of_nonneg (by positivity : 0 ≤ 2 * A)]
    exact hRhi
  have hmargin2Pos : 0 < xiWardZeroFreeMargin (2 * A) := xiWardZeroFreeMargin_pos _
  have hratioMargin :
      (3 / 20 : ℝ) * A * M * xiWardZeroFreeMargin (2 * A) ≤
        A * R * xiWardZeroFreeMargin R := by
    have h1 := mul_le_mul_of_nonneg_right hratio hmargin2Pos.le
    have hAR : 0 ≤ A * R := by positivity
    have h2 := mul_le_mul_of_nonneg_left hmarginAnti hAR
    nlinarith
  have hdefect := xiMass_critical_phase_defect_zeroFree ha hσ hv hcone hcritical q
  have hphaseMul :
      M * (-σ * M + u * K) ≤
        M * (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) := by
    have hbase : 0 ≤ σ * ((A - R) ^ (2 : ℕ) + A) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hratioMargin (show 0 ≤ 4 * σ by positivity)
    dsimp only at hdefect
    change M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ (2 : ℕ) + A) -
        4 * σ * A * R * xiWardZeroFreeMargin R at hdefect
    nlinarith
  have hphase : -σ * M + u * K ≤
      -(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A) :=
    le_of_mul_le_mul_left hphaseMul hM
  rw [(xiMassFamily haHalf).norm_term]
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  apply Real.exp_le_exp.mpr
  have hphase' : -(σ * M - u * K) ≤
      -(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A) := by
    linarith
  simpa only [M, K, A] using hphase'

/-- The whole critical Xi corona spends the zero-free edge margin termwise. -/
theorem norm_xiMassCriticalDiagonalCoronaTraceC_le_zeroFree
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      (xiMassCriticalDiagonalCorona a).card *
        Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let E : ℝ := Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A))
  classical
  unfold xiMassCriticalDiagonalCoronaTraceC
  unfold HTGeometry.AbstractSpectralFamily.massCriticalDiagonalCoronaTraceC
  calc
    ‖∑ i ∈ xiPoissonAbstract.criticalDiagonalCorona a,
        (xiPoissonAbstract.mass haHalf).term ((σ : ℂ) + u * I) i‖ ≤
      ∑ i ∈ xiPoissonAbstract.criticalDiagonalCorona a,
        ‖(xiPoissonAbstract.mass haHalf).term ((σ : ℂ) + u * I) i‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _i ∈ xiPoissonAbstract.criticalDiagonalCorona a, E := by
      exact Finset.sum_le_sum fun i hi => by
        dsimp only [E, A]
        simpa only [xiMassFamily_pt_eq_mass_pt,
          HTGeometry.AbstractSpectralFamily.norm_term] using
          norm_xiMassFamily_term_le_critical_zeroFree ha hσ hv hcone hcritical hi
    _ = (xiMassCriticalDiagonalCorona a).card * E := by
      simp only [Finset.sum_const, nsmul_eq_mul, xiMassCriticalDiagonalCorona]
    _ = (xiMassCriticalDiagonalCorona a).card *
        Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) := by rfl

/-- Zero-counted critical corona envelope: polynomial divisor mass times zero-free edge decay. -/
theorem norm_xiMassCriticalDiagonalCoronaTraceC_le_zeroCount_mul_zeroFree
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let r := 2 * A + 2
    ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      (xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r)) *
        Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let r : ℝ := 2 * A + 2
  let E : ℝ := Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A))
  have htrace := norm_xiMassCriticalDiagonalCoronaTraceC_le_zeroFree
    ha hσ hv hcone hcritical
  have hcard : ((xiMassCriticalDiagonalCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r) := by
    simpa only [r, A] using xiMassCriticalDiagonalCorona_card_le_zeroCountEnvelope ha
  have htrace' :
      ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
        (xiMassCriticalDiagonalCorona a).card * E := by
    simpa only [A, E] using htrace
  have hmul : ((xiMassCriticalDiagonalCorona a).card : ℝ) * E ≤
      (xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r)) * E :=
    mul_le_mul_of_nonneg_right hcard (by dsimp only [E]; positivity)
  have hbound := htrace'.trans hmul
  simpa only [A, r, E] using hbound

/-- Every fixed log power of `2A+9` is negligible compared with `A`. -/
theorem tendsto_pow_log_two_mul_add_nine_div_id (n : ℕ) :
    Tendsto (fun A : ℝ => Real.log (2 * A + 9) ^ n / A)
      atTop (𝓝 0) := by
  have haff : Tendsto (fun A : ℝ => 2 * A + 9) atTop atTop :=
    tendsto_atTop_add_const_right atTop 9
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hraw :=
    (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-9 / 2) n
      (by norm_num : (1 / 2 : ℝ) ≠ 0)).comp haff
  convert hraw using 1
  funext A
  congr 1
  ring

/-- The critical edge scale `A / log(2A+9)^(9 : ℕ)` diverges. -/
theorem tendsto_xiCriticalZeroFreeScale :
    Tendsto (fun A : ℝ => A / Real.log (2 * A + 9) ^ (9 : ℕ))
      atTop atTop := by
  have hratio := tendsto_pow_log_two_mul_add_nine_div_id 9
  have hratioGT :
      Tendsto (fun A : ℝ => Real.log (2 * A + 9) ^ (9 : ℕ) / A)
        atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hratio, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    have hlog : 0 < Real.log (2 * A + 9) := by
      apply Real.log_pos
      linarith
    exact div_pos (pow_pos hlog 9) hA
  have hinv := hratioGT.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  have hlog : 0 < Real.log (2 * A + 9) := by
    apply Real.log_pos
    linarith
  change (Real.log (2 * A + 9) ^ (9 : ℕ) / A)⁻¹ =
    A / Real.log (2 * A + 9) ^ (9 : ℕ)
  rw [inv_div]

/-- Explicit zero-count times zero-free-edge envelope for the critical Xi corona. -/
def xiMassCriticalZeroFreeEnvelope (σ A : ℝ) : ℝ :=
  xiZeroCountEnvelopeConstant * (2 * A + 3) * Real.log (2 * A + 4) *
    Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A))

/-- The critical Xi corona is bounded by the explicit vanishing edge envelope. -/
theorem norm_xiMassCriticalDiagonalCoronaTraceC_le_criticalZeroFreeEnvelope
    {a σ v u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hv : 0 < v)
    (hcone : v * |u| ≤ a - 1 / 2) (hcritical : 4 * σ * v = 1) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      xiMassCriticalZeroFreeEnvelope σ A := by
  dsimp only
  have h := norm_xiMassCriticalDiagonalCoronaTraceC_le_zeroCount_mul_zeroFree
    ha hσ hv hcone hcritical
  unfold xiMassCriticalZeroFreeEnvelope
  convert h using 1
  ring_nf

/-- Complete critical literal source: vanishing corona envelope plus two exponential tails. -/
theorem norm_xiMassBottomPrimeIntegral_critical_le_zeroFreeEnvelope_add_tails
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) (u : ℝ) :
    let a := xiObliqueComovingMass v u
    let A := a - 1 / 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let a : ℝ := xiObliqueComovingMass v u
  let A : ℝ := a - 1 / 2
  let ha : 1 / 2 ≤ a := by
    dsimp only [a]
    linarith [xiObliqueComovingMass_ge_two hv.le u]
  let P : ℂ := xiMassCriticalPrimeCoronaModel a ha ((σ : ℂ) + u * I)
  have ha2 : 2 ≤ a := by
    dsimp only [a]
    exact xiObliqueComovingMass_ge_two hv.le u
  have hcorona :
      ‖xiMassCriticalDiagonalCoronaTraceC a ha ((σ : ℂ) + u * I)‖ ≤
        xiMassCriticalZeroFreeEnvelope σ A := by
    simpa only [a, A, ha] using
      norm_xiMassCriticalDiagonalCoronaTraceC_le_criticalZeroFreeEnvelope
        ha2 hσ hv (velocity_mul_abs_le_xiObliqueComovingMass_sub_half v u) hcritical
  have hP : ‖P‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ A := by
    unfold P xiMassCriticalPrimeCoronaModel
    rw [norm_mul, norm_mul]
    simp only [norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left hcorona (norm_nonneg _)
  have hrem :=
    norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le hσ hv hcritical u
  calc
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ =
        ‖(xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P) + P‖ := by ring_nf
    _ ≤ ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) +
        ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ A := by
      exact add_le_add (by simpa only [a, A, ha, P] using hrem) hP
    _ = ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by ring

/-- Polynomial-log zero count is absorbed by the critical zero-free edge defect. -/
theorem tendsto_xiMassCriticalZeroFreeEnvelope_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassCriticalZeroFreeEnvelope σ) atTop (𝓝 0) := by
  let C : ℝ := xiZeroCountEnvelopeConstant
  let D : ℝ := C + 1
  let c : ℝ := (3 * σ / 5) * xiWardZeroFreeMarginC
  have hC : 0 < C := by dsimp only [C]; exact xiZeroCountEnvelopeConstant_pos
  have hD : 0 < D := by dsimp only [D]; linarith
  have hc : 0 < c := by
    dsimp only [c]
    exact mul_pos (by positivity) xiWardZeroFreeMarginC_pos
  have h9 := tendsto_pow_log_two_mul_add_nine_div_id 9
  have h10 := tendsto_pow_log_two_mul_add_nine_div_id 10
  have hcombo :
      Tendsto (fun A : ℝ =>
        Real.log D * (Real.log (2 * A + 9) ^ (9 : ℕ) / A) +
          2 * (Real.log (2 * A + 9) ^ (10 : ℕ) / A))
        atTop (𝓝 0) := by
    simpa only [zero_add, mul_zero] using
      (tendsto_const_nhds.mul h9).add (tendsto_const_nhds.mul h10)
  have hsmall := hcombo.eventually_le_const (show 0 < c / 2 by positivity)
  have hscale := tendsto_xiCriticalZeroFreeScale
  have hscaledBot :
      Tendsto (fun A : ℝ => -(c / 2) *
        (A / Real.log (2 * A + 9) ^ (9 : ℕ))) atTop atBot :=
    hscale.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (div_pos hc (by norm_num)))
  have hdecay :
      Tendsto (fun A : ℝ =>
        Real.exp (-(c / 2) *
          (A / Real.log (2 * A + 9) ^ (9 : ℕ)))) atTop (𝓝 0) := by
    exact Real.tendsto_exp_atBot.comp hscaledBot
  apply squeeze_zero'
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
    unfold xiMassCriticalZeroFreeEnvelope
    have hlog : 0 ≤ Real.log (2 * A + 4) :=
      Real.log_nonneg (by linarith)
    change 0 ≤ C * (2 * A + 3) * Real.log (2 * A + 4) *
      Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A))
    positivity
  · filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with A hsmallA hA
    let x : ℝ := 2 * A + 9
    let y : ℝ := 2 * A + 4
    let L : ℝ := Real.log x
    let X : ℝ := A / L ^ (9 : ℕ)
    let P : ℝ := C * (2 * A + 3) * Real.log y
    have hx : 0 < x := by dsimp only [x]; linarith
    have hy : 0 < y := by dsimp only [y]; linarith
    have hL : 0 < L := by
      dsimp only [L]
      exact Real.log_pos (by dsimp only [x]; linarith)
    have hL9 : 0 < L ^ (9 : ℕ) := pow_pos hL 9
    have hCD : C ≤ D := by dsimp only [D]; linarith
    have hfac0 : 0 ≤ 2 * A + 3 := by linarith
    have hfac : 2 * A + 3 ≤ x := by dsimp only [x]; linarith
    have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg (by dsimp only [y]; linarith)
    have hlogyx : Real.log y ≤ L := by
      dsimp only [L]
      exact Real.log_le_log hy (by dsimp only [x, y]; linarith)
    have hLx : L ≤ x := by
      have h := Real.log_le_sub_one_of_pos hx
      dsimp only [L]
      linarith
    have hlogyx' : Real.log y ≤ x := hlogyx.trans hLx
    have hP : P ≤ D * x ^ (2 : ℕ) := by
      dsimp only [P]
      calc
        C * (2 * A + 3) * Real.log y ≤ D * x * x := by gcongr
        _ = D * x ^ (2 : ℕ) := by ring
    have hsmallMul :
        Real.log D * L ^ (9 : ℕ) + 2 * L ^ (10 : ℕ) ≤ c / 2 * A := by
      have hmul := mul_le_mul_of_nonneg_left hsmallA hA.le
      have heqLeft :
          A * (Real.log D * (L ^ (9 : ℕ) / A) +
            2 * (L ^ (10 : ℕ) / A)) =
              Real.log D * L ^ (9 : ℕ) + 2 * L ^ (10 : ℕ) := by
        field_simp
      rw [show Real.log (2 * A + 9) = L by rfl, heqLeft] at hmul
      nlinarith
    have hbudget : Real.log D + 2 * L ≤ c / 2 * X := by
      dsimp only [X]
      rw [show c / 2 * (A / L ^ (9 : ℕ)) =
        (c / 2 * A) / L ^ (9 : ℕ) by ring, le_div_iff₀ hL9]
      calc
        (Real.log D + 2 * L) * L ^ (9 : ℕ) =
            Real.log D * L ^ (9 : ℕ) + 2 * L ^ (10 : ℕ) := by ring
        _ ≤ c / 2 * A := hsmallMul
    have hexpEq : Real.exp (Real.log D + 2 * L) = D * x ^ (2 : ℕ) := by
      rw [Real.exp_add, Real.exp_log hD]
      have htwo : 2 * L = L + L := by ring
      rw [htwo, Real.exp_add]
      dsimp only [L]
      rw [Real.exp_log hx]
      ring
    have hPexp : P ≤ Real.exp (c / 2 * X) := by
      calc
        P ≤ D * x ^ (2 : ℕ) := hP
        _ = Real.exp (Real.log D + 2 * L) := hexpEq.symm
        _ ≤ Real.exp (c / 2 * X) := Real.exp_le_exp.mpr hbudget
    have hcalc :
        P * Real.exp (-c * X) ≤ Real.exp (-(c / 2) * X) := by
      calc
        P * Real.exp (-c * X) ≤
            Real.exp (c / 2 * X) * Real.exp (-c * X) :=
          mul_le_mul_of_nonneg_right hPexp (Real.exp_pos _).le
        _ = Real.exp (-(c / 2) * X) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hmargin :
        xiWardZeroFreeMargin (2 * A) =
          xiWardZeroFreeMarginC / L ^ (9 : ℕ) := by
      unfold xiWardZeroFreeMargin
      rw [abs_of_nonneg (by positivity : 0 ≤ 2 * A)]
    have hexponent :
        -(3 * σ / 5) * A *
            (xiWardZeroFreeMarginC / L ^ (9 : ℕ)) = -c * X := by
      dsimp only [c, X]
      ring
    change P * Real.exp (-(3 * σ / 5) * A * xiWardZeroFreeMargin (2 * A)) ≤
      Real.exp (-(c / 2) * X)
    rw [hmargin, hexponent]
    exact hcalc
  · exact hdecay

/-- **Critical Xi extinction.**  On the exact geometric phase wall, the complete literal
von-Mangoldt source tends to zero; the corpus zero-free width empties the universal corona. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_critical_zero
    {σ v : ℝ} (hσ : 0 < σ) (hv : 0 < v)
    (hcritical : 4 * σ * v = 1) :
    Tendsto (fun u : ℝ =>
      ‖xiMassBottomPrimeIntegral (xiObliqueComovingMass v u) 1
        ((σ : ℂ) + u * I)‖) atTop (𝓝 0) := by
  let A : ℝ → ℝ := fun u => xiObliqueComovingMass v u - 1 / 2
  have hlinear : Tendsto (fun u : ℝ => v * u + 3 / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (3 / 2)
      (tendsto_id.const_mul_atTop hv)
  have hA : Tendsto A atTop atTop := by
    apply hlinear.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    dsimp only [A, xiObliqueComovingMass]
    rw [abs_of_nonneg hu]
    ring
  have henv : Tendsto (fun u : ℝ => xiMassCriticalZeroFreeEnvelope σ (A u))
      atTop (𝓝 0) :=
    (tendsto_xiMassCriticalZeroFreeEnvelope_zero hσ).comp hA
  have henvMul :
      Tendsto (fun u : ℝ =>
        ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ (A u))
        atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ henv
  have hσ12neg : -(σ / 12) < 0 := by linarith
  have hσ2neg : -(σ / 2) < 0 := by linarith
  have hexpTrace : Tendsto (fun u : ℝ => Real.exp (-(σ / 12) * A u))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hA.const_mul_atTop_of_neg hσ12neg)
  have hexpArch : Tendsto (fun u : ℝ => Real.exp (-(σ / 2) * A u))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hA.const_mul_atTop_of_neg hσ2neg)
  have htraceTail :
      Tendsto (fun u : ℝ =>
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A u) * xiPoissonTraceReal (σ / 12)))
        atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.mul_const (xiPoissonTraceReal (σ / 12)) hexpTrace
    have h2 := Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ h1
    simpa only [zero_mul, mul_zero] using h2
  have harchTail :
      Tendsto (fun u : ℝ =>
        Real.exp (-(σ / 2) * A u) * xiMassBottomArchUniformBound 2 (σ / 2))
        atTop (𝓝 0) := by
    simpa only [zero_mul] using
      Filter.Tendsto.mul_const (xiMassBottomArchUniformBound 2 (σ / 2)) hexpArch
  have hmajor :
      Tendsto (fun u : ℝ =>
        ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope σ (A u) +
          ‖(Real.pi : ℂ) * I‖ *
            (Real.exp (-(σ / 12) * A u) * xiPoissonTraceReal (σ / 12)) +
          Real.exp (-(σ / 2) * A u) *
            xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · exact Filter.Eventually.of_forall fun u => by
      simpa only [A] using
        norm_xiMassBottomPrimeIntegral_critical_le_zeroFreeEnvelope_add_tails
          hσ hv hcritical u
  · exact hmajor

end

end RHTower

