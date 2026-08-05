import GaloisForLFunctions.RHTower.XiMassZeroFreeSubcriticalBoundary

/-!
# Parameterized Xi zero-free margin budget

Every fixed fraction `0 < θ < 1` of the known zero-free width may pay subcritical wall
deficit while the complementary fraction extinguishes a widened finite corona.  This proves
literal Euler/Gamma source extinction on explicit schedules approaching the full zero-free edge.
-/

open Complex Metric Set Filter
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- Widened corona required when an arbitrary fraction of zero-free width pays wall deficit. -/
def xiMassMarginBudgetCorona (a : ℝ) : Finset XiZeroCopy :=
  ((xiPoissonAbstract.shell_finite (3 * (a - 1 / 2))).toFinset).filter
    (fun q => (a - 1 / 2) / 2 ≤ (xiPoissonPoint q).re)

theorem mem_xiMassMarginBudgetCorona {a : ℝ} {q : XiZeroCopy} :
    q ∈ xiMassMarginBudgetCorona a ↔
      (a - 1 / 2) / 2 ≤ (xiPoissonPoint q).re ∧
        (xiPoissonPoint q).re ≤ 3 * (a - 1 / 2) := by
  simp [xiMassMarginBudgetCorona, xiPoissonAbstract_pt, and_comm]

/-- Finite trace on the widened margin-budget corona. -/
def xiMassMarginBudgetCoronaTraceC
    (a : ℝ) (ha : 1 / 2 ≤ a) (τ : ℂ) : ℂ :=
  ∑ q ∈ xiMassMarginBudgetCorona a, (xiMassFamily ha).term τ q

/-- Every zero copy in the widened corona lies in an explicit Xi disc. -/
theorem xiMassMarginBudgetCorona_support_mem_closedBall
    {a : ℝ} (_ha : 2 ≤ a) {q : XiZeroCopy}
    (hq : q ∈ xiMassMarginBudgetCorona a) :
    (q.1 : ℂ) ∈ closedBall (2 : ℂ) (3 * (a - 1 / 2) + 2) := by
  have hmem := mem_xiMassMarginBudgetCorona.mp hq
  have hR : (xiPoissonPoint q).re ≤ 3 * (a - 1 / 2) := hmem.2
  have hRnn : 0 ≤ (xiPoissonPoint q).re := xiPoissonPoint_re_nonneg q
  have himP : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  have himAbs : |(xiSpectralPoint q).im| = |(xiPoissonPoint q).im| := by
    unfold xiPoissonPoint
    split_ifs <;> simp
  have himAlpha : |(xiSpectralPoint q).im| < 1 / 2 := by rw [himAbs]; exact himP
  have hAlphaIm : (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
    rw [xiSpectralPoint]
    simp [Complex.mul_im]
  have hrhoRe : 0 < (q.1 : ℂ).re ∧ (q.1 : ℂ).re < 1 := by
    rw [abs_lt] at himAlpha
    constructor <;> linarith
  have hAlphaRe : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    rw [xiSpectralPoint]
    simp [Complex.mul_re]
  have himRho : |(q.1 : ℂ).im| = (xiPoissonPoint q).re := by
    rw [← hAlphaRe, xiPoissonPoint_re_eq_abs]
  rw [mem_closedBall, dist_eq_norm]
  apply le_of_lt
  calc
    ‖(q.1 : ℂ) - 2‖ ≤ |((q.1 : ℂ) - 2).re| + |((q.1 : ℂ) - 2).im| :=
      norm_le_abs_re_add_abs_im _
    _ < 2 + (xiPoissonPoint q).re := by
      rw [sub_re, sub_im]
      norm_num
      rw [abs_of_neg (by linarith : (q.1 : ℂ).re - 2 < 0), himRho]
      linarith
    _ ≤ 3 * (a - 1 / 2) + 2 := by linarith

/-- Sharp multiplicity-exact zero-count envelope for the widened corona. -/
theorem xiMassMarginBudgetCorona_card_le_zeroCountEnvelope
    {a : ℝ} (ha : 2 ≤ a) :
    let r := 3 * (a - 1 / 2) + 2
    ((xiMassMarginBudgetCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (1 + r) * Real.log (2 + r) := by
  dsimp only
  let r : ℝ := 3 * (a - 1 / 2) + 2
  have hr : 1 ≤ r := by dsimp only [r]; linarith
  have hpacket := card_le_xiBallOrderSum_of_support_mem
    (r := r) (xiMassMarginBudgetCorona a)
    (fun q hq => by
      dsimp only [r]
      exact xiMassMarginBudgetCorona_support_mem_closedBall ha hq)
  exact hpacket.trans (xiBallOrderSum_le_zeroCountEnvelope r hr)

/-- An arbitrary margin fraction pays wall deficit and leaves the complementary fraction as decay. -/
theorem xiMass_marginBudget_phase_defect_of_re_le
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2))
    (q : XiZeroCopy)
    (hRhiInput : (xiPoissonPoint q).re ≤ 3 * (a - 1 / 2)) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    let d := xiWardZeroFreeMargin (3 * A)
    M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ 2 + A) - |u| * R * (1 - θ) * d := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (3 * A)
  have hA : 0 < A := by dsimp only [A]; linarith
  have hR : 0 < R := by dsimp only [R]; exact xiPoissonAbstract.re_pos q
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.re_lt_csqrtRe_massArg haHalf q
    linarith
  have hsq : A ^ 2 + R ^ 2 + A ≤ M ^ 2 := by
    dsimp only [A, R, M]
    simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt] using
      xiPoissonAbstract.sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re ha q
  have hRhi : R ≤ 3 * A := by simpa only [A, R] using hRhiInput
  have hdAnti : d ≤ xiWardZeroFreeMargin R := by
    dsimp only [d]
    apply xiWardZeroFreeMargin_anti
    rw [abs_of_nonneg hR.le, abs_of_nonneg (by positivity : 0 ≤ 3 * A)]
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
      2 * σ * A * R - |u| * R * (1 - θ) * d := by
    dsimp only [A, d] at hlayerR ⊢
    nlinarith
  have hphase : M * (-σ * M + u * K) ≤
      -σ * M ^ 2 + 2 * σ * A * R - |u| * R * (1 - θ) * d := by
    nlinarith
  change M * (-σ * M + u * K) ≤
    -σ * ((A - R) ^ 2 + A) - |u| * R * (1 - θ) * d
  nlinarith

theorem xiMass_marginBudget_phase_defect
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∈ xiMassMarginBudgetCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    let d := xiWardZeroFreeMargin (3 * A)
    M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ 2 + A) - |u| * R * (1 - θ) * d := by
  have hmem := mem_xiMassMarginBudgetCorona.mp hq
  exact xiMass_marginBudget_phase_defect_of_re_le ha hσ hlayer q hmem.2

/-- Each widened-corona term has residual-margin decay. -/
theorem norm_xiMassFamily_term_le_marginBudget
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hθ1 : θ < 1)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∈ xiMassMarginBudgetCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let d := xiWardZeroFreeMargin (3 * A)
    ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
      Real.exp (-(3 * σ / 13) * A * (1 - θ) * d) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (3 * A)
  have hA : 3 / 2 ≤ A := by dsimp only [A]; linarith
  have hR : 0 < R := by dsimp only [R]; exact xiPoissonAbstract.re_pos q
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.re_lt_csqrtRe_massArg haHalf q
    linarith
  have hmem := mem_xiMassMarginBudgetCorona.mp hq
  have hRlo : A / 2 ≤ R := by simpa only [A, R] using hmem.1
  have hRhi : R ≤ 3 * A := by simpa only [A, R] using hmem.2
  have hMupRaw := xiPoissonAbstract.csqrtRe_massArg_le_add haHalf q
  have hMup : M ≤ A + R + 1 / 2 := by
    have h : M ≤ R + a := by
      dsimp only [M, R]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using hMupRaw
    dsimp only [A]
    linarith
  have hMupA : M ≤ (13 / 3 : ℝ) * A := by nlinarith
  have hratio : (3 / 26 : ℝ) * M ≤ R := by nlinarith
  have hdPos : 0 < d := by dsimp only [d]; exact xiWardZeroFreeMargin_pos _
  have hgap : 0 < 1 - θ := by linarith
  have hscaled1 := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ |u| * (1 - θ) * d by positivity)
  have hlower' : 2 * σ * A ≤ |u| := by simpa only [A] using hlower
  have hscaled2 := mul_le_mul_of_nonneg_right hlower'
    (show 0 ≤ (3 / 26 : ℝ) * (1 - θ) * d * M by positivity)
  have hextra : (3 * σ / 13) * A * (1 - θ) * d * M ≤
      |u| * R * (1 - θ) * d := by
    nlinarith
  have hdefect := xiMass_marginBudget_phase_defect ha hσ hlayer hq
  have hphaseMul : M * (-σ * M + u * K) ≤
      M * (-(3 * σ / 13) * A * (1 - θ) * d) := by
    dsimp only at hdefect
    change M * (-σ * M + u * K) ≤
      -σ * ((A - R) ^ 2 + A) - |u| * R * (1 - θ) * d at hdefect
    have hbase : 0 ≤ σ * ((A - R) ^ 2 + A) := by positivity
    nlinarith
  have hphase : -σ * M + u * K ≤ -(3 * σ / 13) * A * (1 - θ) * d :=
    le_of_mul_le_mul_left hphaseMul hM
  rw [(xiMassFamily haHalf).norm_term]
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  apply Real.exp_le_exp.mpr
  have hphase' : -(σ * M - u * K) ≤ -(3 * σ / 13) * A * (1 - θ) * d := by
    linarith
  simpa only [M, K, A, d] using hphase'

set_option maxHeartbeats 800000 in
/-- Outside the widened corona, every fixed margin budget retains a uniform spectral tail. -/
theorem xiMass_marginBudget_phase_le_outside_corona
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hθ1 : θ ≤ 1)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∉ xiMassMarginBudgetCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    let R := (xiPoissonPoint q).re
    let M := ((xiMassFamily haHalf).pt q).re
    let K := ((xiMassFamily haHalf).pt q).im
    (-σ * M + u * K) ≤ -(σ / 12) * (A + R) := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let R : ℝ := (xiPoissonPoint q).re
  let J : ℝ := (xiPoissonPoint q).im
  let M : ℝ := ((xiMassFamily haHalf).pt q).re
  let K : ℝ := ((xiMassFamily haHalf).pt q).im
  let d : ℝ := xiWardZeroFreeMargin (3 * A)
  have hA : 3 / 2 ≤ A := by dsimp only [A]; linarith
  have hR : 0 < R := by dsimp only [R]; exact xiPoissonAbstract.re_pos q
  have hM : 0 < M := by
    have hMR : R < M := by
      dsimp only [R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using
        xiPoissonAbstract.re_lt_csqrtRe_massArg haHalf q
    linarith
  have hMupRaw := xiPoissonAbstract.csqrtRe_massArg_le_add haHalf q
  have hMup : M ≤ A + R + 1 / 2 := by
    have h : M ≤ R + a := by
      dsimp only [M, R]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt,
        HTGeometry.AbstractSpectralFamily.mass_pt, HTGeometry.csqrt_re] using hMupRaw
    dsimp only [A]
    linarith
  have hMup' : M ≤ (4 / 3 : ℝ) * (A + R) := by nlinarith
  have hd8 : d ≤ 1 / 8 := by
    dsimp only [d]
    exact xiWardZeroFreeMargin_le_one_eighth _
  have hd0 : 0 ≤ d := (xiWardZeroFreeMargin_pos _).le
  have hθd : θ * d ≤ d := by nlinarith
  have hfactor : 3 / 8 ≤ 1 / 2 - θ * d := by linarith
  have hfactorMul := mul_le_mul_of_nonneg_left hfactor (abs_nonneg u)
  have huBound : 3 * |u| ≤ 16 * σ * A := by
    dsimp only [A, d] at hlayer hfactorMul ⊢
    nlinarith
  have hout : R < A / 2 ∨ 3 * A < R := by
    have hnot : ¬ (A / 2 ≤ R ∧ R ≤ 3 * A) := by
      intro hmem
      apply hq
      exact mem_xiMassMarginBudgetCorona.mpr (by simpa only [A, R] using hmem)
    by_cases hlo : A / 2 ≤ R
    · exact Or.inr (lt_of_not_ge (fun hupper => hnot ⟨hlo, hupper⟩))
    · exact Or.inl (lt_of_not_ge hlo)
  rcases hout with hlo | hhi
  · have hRhi : R ≤ 3 * A := by linarith
    have hdefect := xiMass_marginBudget_phase_defect_of_re_le
      ha hσ hlayer q (by simpa only [A, R] using hRhi)
    have hres : 0 ≤ |u| * R * (1 - θ) * d := by positivity
    have hphase : M * (-σ * M + u * K) ≤ -σ * ((A - R) ^ 2 + A) := by
      dsimp only at hdefect
      change M * (-σ * M + u * K) ≤
        -σ * ((A - R) ^ 2 + A) - |u| * R * (1 - θ) * d at hdefect
      linarith
    have hlin : A + R ≤ 3 * (A - R) := by linarith
    have hsqgap : (A + R) ^ 2 ≤ 9 * (A - R) ^ 2 := by
      nlinarith [mul_self_le_mul_self (by positivity : 0 ≤ A + R) hlin]
    have hratio : (A + R) * M ≤ 12 * (A - R) ^ 2 := by
      have hmul := mul_le_mul_of_nonneg_left hMup' (by positivity : 0 ≤ A + R)
      nlinarith
    have hscaled : -σ * ((A - R) ^ 2 + A) ≤
        M * (-(σ / 12) * (A + R)) := by
      have hσratio := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ σ / 12 by positivity)
      nlinarith
    exact le_of_mul_le_mul_left (hphase.trans hscaled) hM
  · have hsq : A ^ 2 + R ^ 2 + A ≤ M ^ 2 := by
      dsimp only [A, R, M]
      simpa only [xiPoissonAbstract_pt, xiMassFamily_pt_eq_mass_pt] using
        xiPoissonAbstract.sq_sub_half_add_sq_re_add_sub_half_le_sq_mass_re ha q
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
    have hucrit : |u| * (R / 2) ≤ (8 / 3 : ℝ) * σ * A * R := by
      nlinarith
    have hsqσ := mul_le_mul_of_nonneg_left hsq hσ.le
    have hsqNeg : -σ * M ^ 2 ≤ -σ * (A ^ 2 + R ^ 2 + A) := by
      nlinarith only [hsqσ]
    have hphase : M * (-σ * M + u * K) ≤
        -σ * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) := by
      calc
        M * (-σ * M + u * K) = -σ * M ^ 2 + M * (u * K) := by ring
        _ ≤ -σ * (A ^ 2 + R ^ 2 + A) + |u| * (R / 2) :=
          add_le_add hsqNeg huK
        _ ≤ -σ * (A ^ 2 + R ^ 2 + A) +
            (8 / 3 : ℝ) * σ * A * R := by
          nlinarith only [hucrit]
        _ ≤ -σ * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) := by
          nlinarith only [hσ, hA]
    have hfac1 : 0 ≤ R - 3 * A := by linarith only [hhi]
    have hfac2 : 0 ≤ 3 * R - A := by linarith only [hhi, hA]
    have hprodFac := mul_nonneg hfac1 hfac2
    have hquad : (A + R) ^ 2 ≤
        8 * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) := by
      nlinarith only [hprodFac]
    have hratio : (A + R) * M ≤
        12 * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) := by
      have hmul := mul_le_mul_of_nonneg_left hMup' (by positivity : 0 ≤ A + R)
      have hQ : 0 ≤ A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R := by
        nlinarith only [hquad]
      calc
        (A + R) * M ≤ (A + R) * ((4 / 3 : ℝ) * (A + R)) := hmul
        _ = (4 / 3 : ℝ) * (A + R) ^ 2 := by ring
        _ ≤ (4 / 3 : ℝ) *
            (8 * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R)) :=
          mul_le_mul_of_nonneg_left hquad (by norm_num)
        _ ≤ 12 * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) := by
          nlinarith only [hQ]
    have hscaled : -σ * (A ^ 2 + R ^ 2 - (8 / 3 : ℝ) * A * R) ≤
        M * (-(σ / 12) * (A + R)) := by
      have hσratio := mul_le_mul_of_nonneg_left hratio
        (show 0 ≤ σ / 12 by positivity)
      nlinarith only [hσratio]
    exact le_of_mul_le_mul_left (hphase.trans hscaled) hM

theorem norm_xiMassFamily_term_le_marginBudget_tail
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ)
    (hθ1 : θ ≤ 1)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2))
    {q : XiZeroCopy} (hq : q ∉ xiMassMarginBudgetCorona a) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
      Real.exp (-(σ / 12) * A) * xiPoissonAbstract.weight (σ / 12) q := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  have hphase := xiMass_marginBudget_phase_le_outside_corona
    ha hσ hθ1 hlayer hq
  rw [(xiMassFamily haHalf).norm_term, HTGeometry.AbstractSpectralFamily.weight,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((σ : ℂ) + u * I)).re = σ := by simp [Complex.mul_re]
  have him : (((σ : ℂ) + u * I)).im = u := by simp [Complex.mul_im]
  rw [hre, him]
  dsimp only at hphase
  rw [xiPoissonAbstract_pt]
  linarith

/-- Existing critical envelope at rescaled aperture exactly represents widened-corona entropy. -/
def xiMassMarginBudgetEnvelope (σ θ A : ℝ) : ℝ :=
  xiMassCriticalZeroFreeEnvelope
    ((10 / 39) * σ * (1 - θ)) ((3 / 2) * A)

theorem tendsto_xiMassMarginBudgetEnvelope_zero
    {σ θ : ℝ} (hσ : 0 < σ) (hθ1 : θ < 1) :
    Tendsto (xiMassMarginBudgetEnvelope σ θ) atTop (𝓝 0) := by
  have hκ : 0 < (10 / 39 : ℝ) * σ * (1 - θ) := by positivity
  have hscale : Tendsto (fun A : ℝ => (3 / 2) * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  exact (tendsto_xiMassCriticalZeroFreeEnvelope_zero hκ).comp hscale

/-- Widened-corona trace is absorbed by complementary zero-free margin. -/
theorem norm_xiMassMarginBudgetCoronaTraceC_le_envelope
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hθ1 : θ < 1)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2)) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassMarginBudgetCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      xiMassMarginBudgetEnvelope σ θ A := by
  dsimp only
  let haHalf : 1 / 2 ≤ a := by linarith
  let A : ℝ := a - 1 / 2
  let E : ℝ := Real.exp (-(3 * σ / 13) * A * (1 - θ) *
    xiWardZeroFreeMargin (3 * A))
  classical
  have hsum :
      ‖xiMassMarginBudgetCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
        (xiMassMarginBudgetCorona a).card * E := by
    unfold xiMassMarginBudgetCoronaTraceC
    calc
      ‖∑ q ∈ xiMassMarginBudgetCorona a,
          (xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ ≤
        ∑ q ∈ xiMassMarginBudgetCorona a,
          ‖(xiMassFamily haHalf).term ((σ : ℂ) + u * I) q‖ := norm_sum_le _ _
      _ ≤ ∑ _q ∈ xiMassMarginBudgetCorona a, E := by
        exact Finset.sum_le_sum fun q hq => by
          dsimp only [E, A]
          simpa only [haHalf] using
            norm_xiMassFamily_term_le_marginBudget ha hσ hθ1 hlower hlayer hq
      _ = (xiMassMarginBudgetCorona a).card * E := by
        simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((xiMassMarginBudgetCorona a).card : ℝ) ≤
      xiZeroCountEnvelopeConstant * (3 * A + 3) * Real.log (3 * A + 4) := by
    have h := xiMassMarginBudgetCorona_card_le_zeroCountEnvelope ha
    dsimp only at h
    dsimp only [A]
    convert h using 1
    all_goals ring_nf
  have hmul := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ E by dsimp only [E]; positivity)
  apply hsum.trans
  calc
    (xiMassMarginBudgetCorona a).card * E ≤
        (xiZeroCountEnvelopeConstant * (3 * A + 3) * Real.log (3 * A + 4)) * E := hmul
    _ = xiMassMarginBudgetEnvelope σ θ A := by
      dsimp only [E, xiMassMarginBudgetEnvelope, xiMassCriticalZeroFreeEnvelope]
      rw [show 2 * ((3 / 2 : ℝ) * A) = 3 * A by ring]
      congr 1
      ring_nf

/-- Complete mass trace equals widened corona modulo a fixed exponential tail. -/
theorem norm_xiMassTraceC_sub_marginBudgetCoronaTraceC_le
    {a σ u θ : ℝ} (ha : 2 ≤ a) (hσ : 0 < σ) (hθ1 : θ ≤ 1)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2)) :
    let haHalf : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖(xiMassFamily haHalf).traceC ((σ : ℂ) + u * I) -
        xiMassMarginBudgetCoronaTraceC a haHalf ((σ : ℂ) + u * I)‖ ≤
      Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12) := by
  dsimp only
  classical
  let haHalf : 1 / 2 ≤ a := by linarith
  let S : Finset XiZeroCopy := xiMassMarginBudgetCorona a
  let T : Set XiZeroCopy := (S : Set XiZeroCopy)ᶜ
  let τ : ℂ := (σ : ℂ) + u * I
  let E : ℝ := Real.exp (-(σ / 12) * (a - 1 / 2))
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ12 : 0 < σ / 12 := by positivity
  have hsum : Summable (fun q : XiZeroCopy => (xiMassFamily haHalf).term τ q) :=
    ((xiMassFamily haHalf).summable_norm_term hτ).of_norm
  have hsumnorm : Summable (fun q : XiZeroCopy => ‖(xiMassFamily haHalf).term τ q‖) :=
    (xiMassFamily haHalf).summable_norm_term hτ
  have hweight : Summable (fun q : XiZeroCopy => xiPoissonAbstract.weight (σ / 12) q) :=
    xiPoissonAbstract.summable_weight hσ12
  have hsplit := hsum.sum_add_tsum_compl (s := S)
  have hdiff :
      (xiMassFamily haHalf).traceC τ - xiMassMarginBudgetCoronaTraceC a haHalf τ =
        ∑' q : T, (xiMassFamily haHalf).term τ (q : XiZeroCopy) := by
    rw [HTGeometry.AbstractSpectralFamily.traceC, xiMassMarginBudgetCoronaTraceC, ← hsplit]
    dsimp only [S, T]
    ring
  rw [hdiff]
  calc
    ‖∑' q : T, (xiMassFamily haHalf).term τ (q : XiZeroCopy)‖ ≤
        ∑' q : T, ‖(xiMassFamily haHalf).term τ (q : XiZeroCopy)‖ :=
      norm_tsum_le_tsum_norm (hsumnorm.subtype _)
    _ ≤ ∑' q : T, E * xiPoissonAbstract.weight (σ / 12) (q : XiZeroCopy) := by
      refine Summable.tsum_le_tsum (fun q => ?_)
        (hsumnorm.subtype _) ((hweight.subtype _).mul_left E)
      have hq : (q : XiZeroCopy) ∉ xiMassMarginBudgetCorona a := by
        simpa only [T, S, Set.mem_compl_iff, Finset.mem_coe] using q.2
      simpa only [τ, E] using
        norm_xiMassFamily_term_le_marginBudget_tail ha hσ hθ1 hlayer hq
    _ = E * ∑' q : T, xiPoissonAbstract.weight (σ / 12) (q : XiZeroCopy) := tsum_mul_left
    _ = E * ∑' q : XiZeroCopy,
        T.indicator (xiPoissonAbstract.weight (σ / 12)) q := by rw [tsum_subtype]
    _ ≤ E * ∑' q : XiZeroCopy, xiPoissonAbstract.weight (σ / 12) q := by
      refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
      exact Summable.tsum_le_tsum
        (fun q => Set.indicator_le_self'
          (fun _ _ => (xiPoissonAbstract.weight_pos _ _).le) q)
        (hweight.indicator _) hweight
    _ = Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) := by
      simp only [E, xiPoissonTraceReal, xiPoissonWeight,
        HTGeometry.AbstractSpectralFamily.weight, xiPoissonAbstract_pt]

/-- Literal prime model carried by the widened margin-budget corona. -/
def xiMassMarginBudgetPrimeCoronaModel
    (a : ℝ) (ha : 1 / 2 ≤ a) (τ : ℂ) : ℂ :=
  I * (Real.pi * I * xiMassMarginBudgetCoronaTraceC a ha τ)

/-- Literal Euler/Gamma source localization throughout every fixed margin-budget layer. -/
theorem norm_xiMassBottomPrimeIntegral_sub_marginBudgetPrimeCoronaModel_le
    {a σ u θ : ℝ} (ha2 : 2 ≤ a) (hσ : 0 < σ) (hθ1 : θ ≤ 1)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2)) :
    let ha : 1 / 2 ≤ a := by linarith
    let A := a - 1 / 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) -
        xiMassMarginBudgetPrimeCoronaModel a ha ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let ha : 1 / 2 ≤ a := by linarith
  let τ : ℂ := (σ : ℂ) + u * I
  let C : ℂ := xiMassMarginBudgetCoronaTraceC a ha τ
  have hhalf : (1 : ℝ) / 2 < 1 := by norm_num
  have hca : (1 : ℝ) < a := by linarith
  have hτ : 0 < τ.re := by dsimp only [τ]; simpa [Complex.mul_re] using hσ
  have hσ2 : 0 < σ / 2 := by positivity
  have hσ2lt : σ / 2 < σ := by linarith
  have htrace :
      ‖(xiMassFamily ha).traceC τ - C‖ ≤
        Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12) := by
    simpa only [τ, C, ha] using
      norm_xiMassTraceC_sub_marginBudgetCoronaTraceC_le ha2 hσ hθ1 hlayer
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
  unfold xiMassMarginBudgetPrimeCoronaModel
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
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) :=
      add_le_add (mul_le_mul_of_nonneg_left htrace (norm_nonneg _)) harch

/-- Complete literal source envelope for every fixed complementary margin. -/
theorem norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
    {a σ u θ : ℝ} (ha2 : 2 ≤ a) (hσ : 0 < σ) (hθ1 : θ < 1)
    (hlower : 2 * σ * (a - 1 / 2) ≤ |u|)
    (hlayer : |u| *
      (1 / 2 - θ * xiWardZeroFreeMargin (3 * (a - 1 / 2))) ≤
        2 * σ * (a - 1 / 2)) :
    let A := a - 1 / 2
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by
  dsimp only
  let ha : 1 / 2 ≤ a := by linarith
  let P : ℂ := xiMassMarginBudgetPrimeCoronaModel a ha ((σ : ℂ) + u * I)
  have hcorona := norm_xiMassMarginBudgetCoronaTraceC_le_envelope
    ha2 hσ hθ1 hlower hlayer
  have hP : ‖P‖ ≤
      ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ (a - 1 / 2) := by
    unfold P xiMassMarginBudgetPrimeCoronaModel
    rw [norm_mul, norm_mul]
    simp only [norm_I, one_mul]
    exact mul_le_mul_of_nonneg_left (by simpa only [ha] using hcorona) (norm_nonneg _)
  have hrem := norm_xiMassBottomPrimeIntegral_sub_marginBudgetPrimeCoronaModel_le
    ha2 hσ hθ1.le hlayer
  calc
    ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I)‖ =
        ‖(xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P) + P‖ := by ring_nf
    _ ≤ ‖xiMassBottomPrimeIntegral a 1 ((σ : ℂ) + u * I) - P‖ + ‖P‖ := norm_add_le _ _
    _ ≤ (‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2)) +
        ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ (a - 1 / 2) := by
      exact add_le_add (by simpa only [ha, P] using hrem) hP
    _ = ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ (a - 1 / 2) +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * (a - 1 / 2)) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * (a - 1 / 2)) *
          xiMassBottomArchUniformBound 2 (σ / 2) := by ring

/-- Extremal frequency spending fraction `θ` of the zero-free width on wall crossing. -/
def xiMassMarginBudgetFrequency (σ θ A : ℝ) : ℝ :=
  2 * σ * A /
    (1 / 2 - θ * xiWardZeroFreeMargin (3 * A))

theorem xiMassMarginBudgetDenom_pos
    {θ A : ℝ} (hθ1 : θ ≤ 1) :
    0 < 1 / 2 - θ * xiWardZeroFreeMargin (3 * A) := by
  have hd8 := xiWardZeroFreeMargin_le_one_eighth (3 * A)
  have hd0 := (xiWardZeroFreeMargin_pos (3 * A)).le
  have hθd : θ * xiWardZeroFreeMargin (3 * A) ≤
      xiWardZeroFreeMargin (3 * A) := by nlinarith
  linarith

theorem xiMassMarginBudgetFrequency_pos
    {σ θ A : ℝ} (hσ : 0 < σ) (hθ1 : θ ≤ 1) (hA : 0 < A) :
    0 < xiMassMarginBudgetFrequency σ θ A := by
  unfold xiMassMarginBudgetFrequency
  exact div_pos (by positivity) (xiMassMarginBudgetDenom_pos hθ1)

theorem xiMassMarginBudgetFrequency_layer_eq
    {σ θ A : ℝ} (hσ : 0 < σ) (hθ1 : θ ≤ 1) (hA : 0 < A) :
    |xiMassMarginBudgetFrequency σ θ A| *
        (1 / 2 - θ * xiWardZeroFreeMargin (3 * A)) =
      2 * σ * A := by
  have hD := xiMassMarginBudgetDenom_pos (A := A) hθ1
  rw [abs_of_pos (xiMassMarginBudgetFrequency_pos hσ hθ1 hA)]
  unfold xiMassMarginBudgetFrequency
  exact div_mul_cancel₀ _ hD.ne'

theorem xiMassMarginBudgetFrequency_lower
    {σ θ A : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) :
    2 * σ * A ≤ |xiMassMarginBudgetFrequency σ θ A| := by
  have hD := xiMassMarginBudgetDenom_pos (A := A) hθ1.le
  have hdPos := xiWardZeroFreeMargin_pos (3 * A)
  have hDle : 1 / 2 - θ * xiWardZeroFreeMargin (3 * A) ≤ 1 := by
    nlinarith
  rw [abs_of_pos (xiMassMarginBudgetFrequency_pos hσ hθ1.le hA)]
  unfold xiMassMarginBudgetFrequency
  apply (le_div_iff₀ hD).2
  exact mul_le_of_le_one_right (by positivity) hDle

/-- Every positive fixed budget fraction gives a genuinely subcritical schedule. -/
theorem xiMassMarginBudgetFrequency_strictly_subcritical
    {σ θ A : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) :
    4 * σ * A < |xiMassMarginBudgetFrequency σ θ A| := by
  have hD := xiMassMarginBudgetDenom_pos (A := A) hθ1.le
  have hdPos := xiWardZeroFreeMargin_pos (3 * A)
  have hDlt : 1 / 2 - θ * xiWardZeroFreeMargin (3 * A) < 1 / 2 := by
    nlinarith
  rw [abs_of_pos (xiMassMarginBudgetFrequency_pos hσ hθ1.le hA)]
  unfold xiMassMarginBudgetFrequency
  apply (lt_div_iff₀ hD).2
  have hmul := mul_lt_mul_of_pos_left hDlt (show 0 < 4 * σ * A by positivity)
  nlinarith

theorem tendsto_xiMassMarginBudgetFrequency_atTop
    {σ θ : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (xiMassMarginBudgetFrequency σ θ) atTop atTop := by
  have hlinear : Tendsto (fun A : ℝ => 4 * σ * A) atTop atTop :=
    tendsto_id.const_mul_atTop (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlinear
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
  simpa only [abs_of_pos (xiMassMarginBudgetFrequency_pos hσ hθ1.le hA)] using
    (xiMassMarginBudgetFrequency_strictly_subcritical hσ hθ0 hθ1 hA).le

/-- **Parameterized subcritical extinction.**  Every fixed fraction strictly below the full
zero-free width yields a genuinely subcritical infinite-frequency schedule on which the complete
literal Euler/Gamma source vanishes. -/
theorem tendsto_norm_xiMassBottomPrimeIntegral_marginBudget_zero
    {σ θ : ℝ} (hσ : 0 < σ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    Tendsto (fun A : ℝ =>
      ‖xiMassBottomPrimeIntegral (A + 1 / 2) 1
        ((σ : ℂ) + xiMassMarginBudgetFrequency σ θ A * I)‖)
      atTop (𝓝 0) := by
  have henv := tendsto_xiMassMarginBudgetEnvelope_zero hσ hθ1
  have henvMul : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ A)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ henv
  have hexpTrace : Tendsto (fun A : ℝ => Real.exp (-(σ / 12) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 12) < 0))
  have hexpArch : Tendsto (fun A : ℝ => Real.exp (-(σ / 2) * A))
      atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(σ / 2) < 0))
  have htraceTail : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ *
        (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)))
      atTop (𝓝 0) := by
    have h1 := Filter.Tendsto.mul_const (xiPoissonTraceReal (σ / 12)) hexpTrace
    have h2 := Filter.Tendsto.const_mul ‖(Real.pi : ℂ) * I‖ h1
    simpa only [zero_mul, mul_zero] using h2
  have harchTail : Tendsto (fun A : ℝ =>
      Real.exp (-(σ / 2) * A) * xiMassBottomArchUniformBound 2 (σ / 2))
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      Filter.Tendsto.mul_const (xiMassBottomArchUniformBound 2 (σ / 2)) hexpArch
  have hmajor : Tendsto (fun A : ℝ =>
      ‖(Real.pi : ℂ) * I‖ * xiMassMarginBudgetEnvelope σ θ A +
        ‖(Real.pi : ℂ) * I‖ *
          (Real.exp (-(σ / 12) * A) * xiPoissonTraceReal (σ / 12)) +
        Real.exp (-(σ / 2) * A) *
          xiMassBottomArchUniformBound 2 (σ / 2)) atTop (𝓝 0) := by
    simpa only [zero_add] using (henvMul.add htraceTail).add harchTail
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun _ => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (3 / 2 : ℝ)] with A hA
    have hApos : 0 < A := by linarith
    have hlower := xiMassMarginBudgetFrequency_lower hσ hθ0 hθ1 hApos
    have hlayer := (xiMassMarginBudgetFrequency_layer_eq hσ hθ1.le hApos).le
    have hbound := norm_xiMassBottomPrimeIntegral_le_marginBudgetEnvelope
      (a := A + 1 / 2) (σ := σ) (θ := θ)
      (u := xiMassMarginBudgetFrequency σ θ A) (by linarith) hσ hθ1
      (by simpa only [add_sub_cancel_right] using hlower)
      (by simpa only [add_sub_cancel_right] using hlayer)
    simpa only [add_sub_cancel_right] using hbound
  · exact hmajor

end

end RHTower
