import GaloisForLFunctions.RHTower.XiMassCriticalZeroFreeEdgeExtinction

/-!
# Xi mass zero-free subcritical boundary extinction

Zero-free width is a quantitative budget: half pays the deficit beyond the universal
critical wall and half gives decay.  This module proves an explicit genuinely subcritical
frequency schedule along which the complete literal Euler/Gamma source still vanishes.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

theorem xiWardZeroFreeMargin_le_one_eighth (y : ℝ) :
    xiWardZeroFreeMargin y ≤ 1 / 8 := by
  exact (xiWardZeroFreeMargin_le_marginC y).trans
    ((min_le_right zetaZeroFreeC zetaLowHeightZeroFreeDelta).trans
      zetaLowHeightZeroFreeDelta_spec.2.1)

/-- Half the zero-free width pays a subcritical wall deficit; half remains as decay. -/
theorem xiMass_subcriticalBoundary_phase_defect
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∈ xiMassCriticalDiagonalCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ (2 : ℕ) + A) -
        |u| * R * xiWardZeroFreeMargin (2 * A) / 2 := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (2 * A)
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
  have hmem := xiPoissonAbstract.mem_criticalDiagonalCorona.mp hq
  have hRhi : R ≤ 2 * A := by
    simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt, A, R] using hmem.2
  have hdAnti : d ≤ xiWardZeroFreeMargin R := by
    dsimp only [d]
    apply xiWardZeroFreeMargin_anti
    rw [abs_of_nonneg hR.le, abs_of_nonneg (by positivity : 0 ≤ 2 * A)]
    exact hRhi
  have himAbs : |J| = |(xiSpectralPoint q).im| := by
    dsimp only [J]
    unfold xiPoissonPoint
    split_ifs <;> simp
  have hJraw := abs_xiSpectralPoint_im_le_half_sub_zeroFreeMargin q
  have hJ : |J| ≤ 1 / 2 - d := by
    rw [himAbs]
    have hJ' : |(xiSpectralPoint q).im| ≤
        1 / 2 - xiWardZeroFreeMargin R := by simpa only [R] using hJraw
    linarith
  have hprod := xiPoissonAbstract.re_mul_im_mass haHalf q
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    rw [abs_mul, abs_mul] at habs
    change |M| * |K| = |R| * |J| at habs
    simpa only [abs_of_pos hM, abs_of_pos hR] using habs
  have hMK : M * |K| ≤ R * (1 / 2 - d) := by
    rw [hprodAbs]
    exact mul_le_mul_of_nonneg_left hJ hR.le
  have huK : M * (u * K) ≤ |u| * (R * (1 / 2 - d)) := by
    calc
      M * (u * K) ≤ M * |u * K| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hM.le
      _ = |u| * (M * |K|) := by rw [abs_mul]; ring
      _ ≤ |u| * (R * (1 / 2 - d)) :=
        mul_le_mul_of_nonneg_left hMK (abs_nonneg u)
  have hlayerR := mul_le_mul_of_nonneg_right hlayer hR.le
  have hspend : |u| * (R * (1 / 2 - d)) ≤
      2 * σ * A * R - |u| * R * d / 2 := by
    dsimp only [A, d] at hlayerR ⊢
    nlinarith
  have hphase : M * (-σ * M + u * K) ≤
      -σ * M ^ (2 : ℕ) + 2 * σ * A * R - |u| * R * d / 2 := by
    nlinarith
  change M * (-σ * M + u * K) ≤
    -σ * ((A - R) ^ (2 : ℕ) + A) - |u| * R * d / 2
  nlinarith

/-- Every boundary-layer corona term has explicit zero-free decay. -/
theorem norm_xiMassFamily_term_le_subcriticalBoundary
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∈ xiMassCriticalDiagonalCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
      Real.exp (-(3 * σ / 20) * A * xiWardZeroFreeMargin (2 * A)) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (2 * A)
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
  have hratio : (3 / 20 : ℝ) * M ≤ R := by nlinarith
  have hdPos : 0 < d := by dsimp only [d]; exact xiWardZeroFreeMargin_pos _
  have hscaled1 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ |u| * d / 2 by positivity)
  have hlower' : 2 * σ * A ≤ |u| := by simpa only [A] using hlower
  have hscaled2 := mul_le_mul_of_nonneg_right hlower' (show 0 ≤ (3 / 40 : ℝ) * d * M by positivity)
  have hextra : (3 * σ / 20) * A * d * M ≤ |u| * R * d / 2 := by
    nlinarith
  have hdefect := xiMass_subcriticalBoundary_phase_defect ha hσ hlayer hq
  have hphaseMul : M * (-σ * M + u * K) ≤
      M * (-(3 * σ / 20) * A * d) := by
    dsimp only at hdefect
    change M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ (2 : ℕ) + A) - |u| * R * d / 2 at hdefect
    have hbase : 0 ≤ σ * ((A - R) ^ (2 : ℕ) + A) := by positivity
    nlinarith
  have hphase : -σ * M + u * K ≤ -(3 * σ / 20) * A * d :=
    le_of_mul_le_mul_left hphaseMul hM
  rw [(xiMassFamily haHalf).norm_term]
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  apply Real.exp_le_exp.mpr
  have hphase' : -(σ * M - u * K) ≤ -(3 * σ / 20) * A * d := by linarith
  simpa only [M, K, A, d] using hphase'

/-- Outside the diagonal corona, the whole shrinking boundary layer retains an exponential tail. -/
theorem xiMass_subcriticalBoundary_phase_le_outside_corona
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∉ xiMassCriticalDiagonalCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    (-σ * M + u * K) ≤ -(σ / 28) * (A + R) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (2 * A)
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
  have hd8 : d ≤ 1 / 8 := by
    dsimp only [d]
    exact xiWardZeroFreeMargin_le_one_eighth _
  have hfactor : 7 / 16 ≤ 1 / 2 - d / 2 := by linarith
  have hfactorMul := mul_le_mul_of_nonneg_left hfactor (abs_nonneg u)
  have huBound : 7 * |u| ≤ 32 * σ * A := by
    dsimp only [A, d] at hlayer hfactorMul ⊢
    nlinarith
  have hprod := xiPoissonAbstract.re_mul_im_mass haHalf q
  have hprodAbs : M * |K| = R * |J| := by
    have habs := congrArg abs hprod
    rw [abs_mul, abs_mul] at habs
    change |M| * |K| = |R| * |J| at habs
    simpa only [abs_of_pos hM, abs_of_pos hR] using habs
  have hJ : |J| ≤ 1 / 2 := by
    dsimp only [J]
    exact (abs_xiPoissonPoint_im_lt_half q).le
  have hMK : M * |K| ≤ R / 2 := by
    rw [hprodAbs]
    nlinarith [mul_le_mul_of_nonneg_left hJ hR.le]
  have huK : M * (u * K) ≤ |u| * (R / 2) := by
    calc
      M * (u * K) ≤ M * |u * K| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hM.le
      _ = |u| * (M * |K|) := by rw [abs_mul]; ring
      _ ≤ |u| * (R / 2) := mul_le_mul_of_nonneg_left hMK (abs_nonneg u)
  have huR := mul_le_mul_of_nonneg_right huBound hR.le
  have hucrit : |u| * (R / 2) ≤ (16 / 7 : ℝ) * σ * A * R := by
    nlinarith
  have hphase : M * (-σ * M + u * K) ≤
      -σ * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) := by
    nlinarith
  have hMupRaw := xiPoissonAbstract.csqrtRe_massArg_le_add haHalf q
  have hMup : M ≤ A + R + 1 / 2 := by
    have h : M ≤ R + a := by
      dsimp only [M, R]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using hMupRaw
    dsimp only [A]
    linarith
  have hMup' : M ≤ (4 / 3 : ℝ) * (A + R) := by
    have hAthree : 3 / 2 ≤ A := by dsimp only [A]; linarith
    nlinarith
  have hout : R < A / 2 ∨ 2 * A < R := by
    have hnot : ¬ (A / 2 ≤ R ∧ R ≤ 2 * A) := by
      intro hmem
      apply hq
      exact xiPoissonAbstract.mem_criticalDiagonalCorona.mpr
        (by simpa only [xiMassCriticalDiagonalCorona, xiPoissonAbstract_pt, A, R] using hmem)
    by_cases hlo : A / 2 ≤ R
    · exact Or.inr (lt_of_not_ge (fun hupper => hnot ⟨hlo, hupper⟩))
    · exact Or.inl (lt_of_not_ge hlo)
  have hquad : (A + R) ^ (2 : ℕ) ≤
      21 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) := by
    rcases hout with hlo | hhi
    · have h1 : 0 ≤ A - 2 * R := by linarith
      have h2 : 0 ≤ 2 * A - R := by linarith
      have hp := mul_nonneg h1 h2
      rw [show 21 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) =
        (A + R) ^ (2 : ℕ) + 10 * ((A - 2 * R) * (2 * A - R)) by ring]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hp)
    · have h1 : 0 ≤ R - 2 * A := by linarith
      have h2 : 0 ≤ 2 * R - A := by linarith
      have hp := mul_nonneg h1 h2
      rw [show 21 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) =
        (A + R) ^ (2 : ℕ) + 10 * ((R - 2 * A) * (2 * R - A)) by ring]
      exact le_add_of_nonneg_right (mul_nonneg (by norm_num) hp)
  have hratio : (A + R) * M ≤
      28 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) := by
    have hmul := mul_le_mul_of_nonneg_left hMup' (by positivity : 0 ≤ A + R)
    calc
      (A + R) * M ≤ (A + R) * ((4 / 3 : ℝ) * (A + R)) := hmul
      _ = (4 / 3 : ℝ) * (A + R) ^ (2 : ℕ) := by ring
      _ ≤ (4 / 3 : ℝ) *
          (21 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R)) :=
        mul_le_mul_of_nonneg_left hquad (by norm_num)
      _ = 28 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) := by ring
  have hscaled :
      -σ * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) ≤
        M * (-(σ / 28) * (A + R)) := by
    have hσratio := mul_le_mul_of_nonneg_left hratio (show 0 ≤ σ / 28 by positivity)
    calc
      -σ * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R) =
          -(σ / 28 *
            (28 * (A ^ (2 : ℕ) + R ^ (2 : ℕ) - (16 / 7 : ℝ) * A * R))) := by ring
      _ ≤ -(σ / 28 * ((A + R) * M)) := neg_le_neg hσratio
      _ = M * (-(σ / 28) * (A + R)) := by ring
  have hmul : M * (-σ * M + u * K) ≤ M * (-(σ / 28) * (A + R)) :=
    hphase.trans hscaled
  exact le_of_mul_le_mul_left hmul hM

/-- Termwise exponential tail outside the shrinking boundary-layer corona. -/
theorem norm_xiMassFamily_term_le_subcriticalBoundary_tail
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∉ xiMassCriticalDiagonalCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
      Real.exp (-(σ / 28) * A) * xiPoissonAbstract.weight (σ / 28) q := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  have hphase := xiMass_subcriticalBoundary_phase_le_outside_corona ha hσ hlayer hq
  rw [(xiMassFamily haHalf).norm_term, HTGeometry.AbstractSpectralFamily.weight,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  dsimp only at hphase
  rw [xiPoissonAbstract_pt]
  linarith

/-- The shrinking-boundary corona is controlled by the already vanishing envelope at `σ/4`. -/
theorem norm_xiMassCriticalDiagonalCoronaTraceC_le_subcriticalBoundaryEnvelope
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2)) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      xiMassCriticalZeroFreeEnvelope (σ / 4) A := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let E : ℝ := Real.exp (-(3 * σ / 20) * A * xiWardZeroFreeMargin (2 * A))
  classical
  have hsum :
      ‖xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
        (xiMassCriticalDiagonalCorona a).card * E := by
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
            norm_xiMassFamily_term_le_subcriticalBoundary ha hσ hlower hlayer hi
      _ = (xiMassCriticalDiagonalCorona a).card * E := by
        simp only [Finset.sum_const, nsmul_eq_mul, xiMassCriticalDiagonalCorona]
  have hcard : ((xiMassCriticalDiagonalCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (2 * A + 3) * Real.log (2 * A + 4) := by
    have h := xiMassCriticalDiagonalCorona_card_le_zeroCountEnvelope ha
    dsimp only at h
    dsimp only [A]
    convert h using 1
    ring_nf
  have hmul := mul_le_mul_of_nonneg_right hcard (show 0 ≤ E by dsimp only [E]; positivity)
  apply hsum.trans
  calc
    (xiMassCriticalDiagonalCorona a).card * E ≤
        (xiZeroCountEnvelopeConstant * (2 * A + 3) * Real.log (2 * A + 4)) * E := hmul
    _ = xiMassCriticalZeroFreeEnvelope (σ / 4) A := by
      dsimp only [E, xiMassCriticalZeroFreeEnvelope]
      congr 2
      ring

/-- Complete mass trace equals the shrinking-boundary corona modulo an explicit `σ/28` tail. -/
theorem norm_xiMassTraceC_sub_criticalDiagonalCoronaTraceC_le_subcriticalBoundary
    {a σ u : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2)) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).traceC ((σ : ℂ) + u * I) -
        xiMassCriticalDiagonalCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(σ / 28) * A) * xiPoissonTraceReal (σ / 28) := by
  dsimp only
  classical
  let haHalf : 1 / 2 ≤ a := by linarith
  let S : Finset XiZeroCopy := xiPoissonAbstract.criticalDiagonalCorona a
  let T : Set XiZeroCopy := (S : Set XiZeroCopy)ᶜ
  let τ : ℂ := (σ : ℂ) + u * I
  let E : ℝ := Real.exp (-(σ / 28) * (a - 1 / 2))
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ28 : 0 < σ / 28 := by positivity
  have hsum : Summable (fun q : XiZeroCopy => (xiMassFamily haHalf).term τ q) :=
    ((xiMassFamily haHalf).summable_norm_term hτ).of_norm
  have hsumnorm : Summable (fun q : XiZeroCopy => ‖(xiMassFamily haHalf).term τ q‖) :=
    (xiMassFamily haHalf).summable_norm_term hτ
  have hweight : Summable (fun q : XiZeroCopy => xiPoissonAbstract.weight (σ / 28) q) :=
    xiPoissonAbstract.summable_weight hσ28
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hdiff :
      (xiMassFamily haHalf).traceC τ -
          xiMassCriticalDiagonalCoronaTraceC a haHalf τ =
        ∑' q : T, (xiMassFamily haHalf).term τ (q : XiZeroCopy) := by
    rw [HTGeometry.AbstractSpectralFamily.traceC,
      xiMassCriticalDiagonalCoronaTraceC,
      HTGeometry.AbstractSpectralFamily.massCriticalDiagonalCoronaTraceC,
      ← hsplit]
    simp only [HTGeometry.AbstractSpectralFamily.term, xiMassFamily_pt_eq_mass_pt]
    dsimp only [S, T]
    ring
  rw [hdiff]
  calc
    ‖∑' q : T, (xiMassFamily haHalf).term τ (q : XiZeroCopy)‖ ≤
        ∑' q : T, ‖(xiMassFamily haHalf).term τ (q : XiZeroCopy)‖ :=
      norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ ≤ ∑' q : T, E * xiPoissonAbstract.weight (σ / 28) (q : XiZeroCopy) := by
      refine Summable.tsum_le_tsum (fun q => ?_)
        (hsumnorm.subtype _) ((hweight.subtype _).mul_left E)
      have hq : (q : XiZeroCopy) ∉ xiMassCriticalDiagonalCorona a := by
        simpa only [T, S, xiMassCriticalDiagonalCorona,
          Set.mem_compl_iff, Finset.mem_coe] using q.2
      simpa only [τ, E] using
        norm_xiMassFamily_term_le_subcriticalBoundary_tail ha hσ hlayer hq
    _ = E * ∑' q : T, xiPoissonAbstract.weight (σ / 28) (q : XiZeroCopy) := tsum_mul_left
    _ = E * ∑' q : XiZeroCopy,
        T.indicator (xiPoissonAbstract.weight (σ / 28)) q := by rw [tsum_subtype]
    _ ≤ E * ∑' q : XiZeroCopy, xiPoissonAbstract.weight (σ / 28) q := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Summable.tsum_le_tsum
        (fun q => Set.indicator_le_self'
          (fun _ _ => (xiPoissonAbstract.weight_pos _ _).le) q)
        (hweight.indicator _) hweight
    _ = Real.exp (-(σ / 28) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 28) := by
      simp only [E, xiPoissonTraceReal, xiPoissonWeight,
        HTGeometry.AbstractSpectralFamily.weight, xiPoissonAbstract_pt]

/-- Literal Euler/Gamma source localization throughout the shrinking subcritical layer. -/
theorem norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le_subcriticalBoundary
    {a σ u : ℝ} (ha2 : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2)) :
    let ha : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) -
        xiMassCriticalPrimeCoronaModel a ha ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * A) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let ha : 1 / 2 ≤ a := by linarith
  let τ : ℂ := (σ : ℂ) + u * I
  let C : ℂ := xiMassCriticalDiagonalCoronaTraceC a ha τ
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < a := by linarith
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ2 : 0 < σ / 2 := by positivity
  have hσ2lt : σ / 2 < σ := by linarith
  have htrace :
      ‖(xiMassFamily ha).traceC τ - C‖ ≤
        Real.exp (-(σ / 28) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 28) := by
    simpa only [τ, C, ha] using
      norm_xiMassTraceC_sub_criticalDiagonalCoronaTraceC_le_subcriticalBoundary
        ha2 hσ hlayer
  have harch0 :
      ‖xiMassBottomArchIntegral a 1 τ‖ ≤ xiMassBottomArchUniformBound a σ :=
    norm_integral_xiMassBottomArchIntegrand_le_uniform hhalf hca hσ
  have harchGap := xiMassBottomArchUniformBound_le_exponential_gap
    (a := a) (b := (2 : ℝ)) (σ := σ) (δ := σ / 2)
    (by norm_num) ha2 hσ2 hσ2lt
  have harch :
      ‖xiMassBottomArchIntegral a 1 τ‖ ≤
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
    exact harch0.trans (by simpa only [sub_half] using harchGap)
  rw [xiMassBottomPrimeIntegral_eq_I_mul_source_add_arch hhalf hca hτ,
    integral_xiMassBottomSourceIntegrand_eq_pi_I_mul_trace hhalf hca hτ]
  unfold xiMassCriticalPrimeCoronaModel
  change ‖I * (Real.pi * I * (xiMassFamily ha).traceC τ) +
      xiMassBottomArchIntegral a 1 τ - I * (Real.pi * I * C)‖ ≤ _
  have heq :
      I * (Real.pi * I * (xiMassFamily ha).traceC τ) +
          xiMassBottomArchIntegral a 1 τ - I * (Real.pi * I * C) =
        I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C)) +
          xiMassBottomArchIntegral a 1 τ := by ring
  rw [heq]
  calc
    ‖I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C)) +
        xiMassBottomArchIntegral a 1 τ‖ ≤
      ‖I * (Real.pi * I * ((xiMassFamily ha).traceC τ - C))‖ +
        ‖xiMassBottomArchIntegral a 1 τ‖ := norm_add_le _ _
    _ = ‖(Real.pi : ℂ) * I‖ * ‖(xiMassFamily ha).traceC τ - C‖ +
        ‖xiMassBottomArchIntegral a 1 τ‖ := by rw [norm_mul, norm_mul]; simp
    _ ≤ ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left htrace (norm_nonneg _)) harch

/-- Complete literal source envelope in the zero-free subcritical boundary layer. -/
theorem norm_xiMassBottomPrimeIntegral_le_subcriticalBoundaryEnvelope
    {a σ u : ℝ} (ha2 : 2 ≤ a) (hσ : 0 < σ)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - xiWardZeroFreeMargin (2 * (a - 1 / 2)) / 2) ≤
        2 * σ * (a - 1 / 2)) :
    let A := a - 1 / 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope (σ / 4) A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * A) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let ha : 1 / 2 ≤ a := by linarith
  let P : ℂ := xiMassCriticalPrimeCoronaModel a ha ((σ : ℂ) + u * I)
  have hcorona := norm_xiMassCriticalDiagonalCoronaTraceC_le_subcriticalBoundaryEnvelope
    ha2 hσ hlower hlayer
  have hP : ‖P‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope (σ / 4) (a - 1 / 2) := by
    unfold P xiMassCriticalPrimeCoronaModel
    rw [norm_mul, norm_mul]
    simp only [norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [ha] using hcorona) (norm_nonneg _)
  have hrem :=
    norm_xiMassBottomPrimeIntegral_sub_criticalPrimeCoronaModel_le_subcriticalBoundary
      ha2 hσ hlayer
  calc
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ =
        ‖(xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P) + P‖ := by ring_nf
    _ ≤ ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2)) +
        ‖(Real.pi : ℂ) * I‖ *
          xiMassCriticalZeroFreeEnvelope (σ / 4) (a - 1 / 2) := by
      exact add_le_add (by simpa only [ha, P] using hrem) hP
    _ = ‖(Real.pi : ℂ) * I‖ *
          xiMassCriticalZeroFreeEnvelope (σ / 4) (a - 1 / 2) +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by ring

/-- Extremal frequency spending exactly half the available zero-free width on wall crossing. -/
def xiMassZeroFreeBoundaryFrequency (σ A : ℝ) : ℝ :=
  2 * σ * A /
    (1 / 2 - xiWardZeroFreeMargin (2 * A) / 2)

theorem xiMassZeroFreeBoundaryDenom_pos (A : ℝ) :
    0 < 1 / 2 - xiWardZeroFreeMargin (2 * A) / 2 := by
  have hd8 := xiWardZeroFreeMargin_le_one_eighth (2 * A)
  linarith

theorem xiMassZeroFreeBoundaryFrequency_pos
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    0 < xiMassZeroFreeBoundaryFrequency σ A := by
  unfold xiMassZeroFreeBoundaryFrequency
  exact div_pos (by positivity) (xiMassZeroFreeBoundaryDenom_pos A)

/-- The extremal schedule lies exactly on the half-margin boundary-layer wall. -/
theorem xiMassZeroFreeBoundaryFrequency_layer_eq
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    |xiMassZeroFreeBoundaryFrequency σ A| *
        (1 / 2 - xiWardZeroFreeMargin (2 * A) / 2) =
      2 * σ * A := by
  have hD := xiMassZeroFreeBoundaryDenom_pos A
  rw [abs_of_pos (xiMassZeroFreeBoundaryFrequency_pos hσ hA)]
  unfold xiMassZeroFreeBoundaryFrequency
  exact div_mul_cancel₀ _ hD.ne'

theorem xiMassZeroFreeBoundaryFrequency_lower
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    2 * σ * A ≤ |xiMassZeroFreeBoundaryFrequency σ A| := by
  have hD := xiMassZeroFreeBoundaryDenom_pos A
  have hdPos := xiWardZeroFreeMargin_pos (2 * A)
  have hDle : 1 / 2 - xiWardZeroFreeMargin (2 * A) / 2 ≤ 1 := by
    linarith
  rw [abs_of_pos (xiMassZeroFreeBoundaryFrequency_pos hσ hA)]
  unfold xiMassZeroFreeBoundaryFrequency
  apply (le_div_iff₀ hD).2
  exact mul_le_of_le_one_right (by positivity) hDle

/-- The zero-free boundary schedule is genuinely below the geometric critical wall. -/
theorem xiMassZeroFreeBoundaryFrequency_strictly_subcritical
    {σ A : ℝ} (hσ : 0 < σ) (hA : 0 < A) :
    4 * σ * A < |xiMassZeroFreeBoundaryFrequency σ A| := by
  have hD := xiMassZeroFreeBoundaryDenom_pos A
  have hdPos := xiWardZeroFreeMargin_pos (2 * A)
  have hDlt : 1 / 2 - xiWardZeroFreeMargin (2 * A) / 2 < 1 / 2 := by
    linarith
  rw [abs_of_pos (xiMassZeroFreeBoundaryFrequency_pos hσ hA)]
  unfold xiMassZeroFreeBoundaryFrequency
  apply (lt_div_iff₀ hD).2
  have hmul := mul_lt_mul_of_pos_left hDlt (show 0 < 4 * σ * A by positivity)
  nlinarith

theorem tendsto_xiMassZeroFreeBoundaryFrequency_atTop
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (xiMassZeroFreeBoundaryFrequency σ) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  simpa only [abs_of_pos (xiMassZeroFreeBoundaryFrequency_pos hσ hA)] using
    (xiMassZeroFreeBoundaryFrequency_strictly_subcritical hσ hA).le

/-- **Zero-free subcritical extinction.**  The literal Euler/Gamma source still vanishes on an
explicit schedule lying strictly beyond the universal geometric wall by half the zero-free width. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_zeroFreeBoundary_zero
    {σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassZeroFreeBoundaryFrequency σ A * I)‖)
      atTop (𝓝 0) := by
  have henv : Tendsto (fun A : ℝ =>
      xiMassCriticalZeroFreeEnvelope (σ / 4) A) atTop (𝓝 0) :=
    tendsto_xiMassCriticalZeroFreeEnvelope_zero (by positivity)
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope (σ / 4) A)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ henv
  have hexpTrace : Tendsto (fun A : ℝ => Real.exp (-(σ / 28) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 28) < 0))
  have hexpArch : Tendsto (fun A : ℝ => Real.exp (-(σ / 2) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 2) < 0))
  have htraceTail : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ *
        (Real.exp (-(σ / 28) * A) * xiPoissonTraceReal (σ / 28)))
      atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.mul_const (xiPoissonTraceReal (σ / 28)) hexpTrace
    have h2 := Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ h1
    simpa only [zero_mul, mul_zero] using h2
  have harchTail : Tendsto (fun A : ℝ =>
      Real.exp (-(σ / 2) * A) * xiMassBottomArchUniformBound 2 (σ / 2))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      Filter.Tendsto.mul_const (xiMassBottomArchUniformBound 2 (σ / 2)) hexpArch
  have hmajor : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassCriticalZeroFreeEnvelope (σ / 4) A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 28) * A) * xiPoissonTraceReal (σ / 28)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with A hA
    have hApos : 0 < A := by linarith
    have hlower := xiMassZeroFreeBoundaryFrequency_lower hσ hApos
    have hlayer := (xiMassZeroFreeBoundaryFrequency_layer_eq hσ hApos).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_subcriticalBoundaryEnvelope
      (a := A + 1 / 2) (σ := σ)
      (u := xiMassZeroFreeBoundaryFrequency σ A) (by linarith) hσ
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right] using hlayer)
    simpa only [add_sub_cancel_right] using hbound
  · exact hmajor

end

end RHTower
