import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerSourceParameterHolomorphy
import GaloisForLFunctions.HTGeometry.PolyaMaximumTransfer
import GaloisForLFunctions.HTGeometry.TracePowerDetDerivative
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue
import GaloisForLFunctions.HTGeometry.EntireNonzeroPathConnected

/-!
# Exact pole and cancellation of the actual Mayer determinant

The constant projection occupies one Cauchy row, making the genuine Fredholm
limit affine in its zeta coefficient. A parameter-circle maximum principle
extends the uniform geometric bounds for the remainder through the source
pole. The resulting numerator classifies removability exactly.

The spectral residue is entire, vanishes at zero, and has derivative minus
one there. Its zeros form a closed discrete countable set; small nonzero
spectral parameters therefore give genuine simple source poles.
-/

open Complex Metric Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerCutoff
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerNuclear
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerFredholm
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerParameter

set_option autoImplicit false

noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPole

/-- Cauchy matrix of an operator on the actual source disc algebra. -/
def operatorMatrix (T : DiscSpace →L[ℂ] DiscSpace) (i j : ℕ) : ℂ :=
  functional i (((balanceRadius : ℂ)^j)⁻¹ • T (monomial j))

/-- The matrix of the actual constant-mode projection. -/
def projectionMatrix : ℕ → ℕ → ℂ := operatorMatrix constantProjection

/-- The source matrix after subtraction of its zeta constant mode. -/
def remainderMatrix (w : ℂ) : ℕ → ℕ → ℂ := operatorMatrix (remainder w)

theorem sourceMatrix_decomposition (w : ℂ) (i j : ℕ) :
    sourceMatrix w i j = remainderMatrix w i j + riemannZeta w * projectionMatrix i j := by
  change functional i (((balanceRadius : ℂ)^j)⁻¹ •
    ((riemannZeta w • constantProjection + remainder w) (monomial j))) = _
  rw [_root_.add_apply, _root_.smul_apply, smul_add, map_add, smul_comm, map_smul,
    smul_eq_mul]
  change riemannZeta w * projectionMatrix i j + remainderMatrix w i j = _
  exact add_comm _ _

private theorem projection_monomial (j : ℕ) :
    constantProjection (monomial j) = constant ((-1 : ℂ)^j) := by
  apply Subtype.ext
  ext z
  change ((0 : ℂ) - 1)^j = (-1 : ℂ)^j
  rw [zero_sub]

/-- Constant functions have precisely their zeroth Cauchy coefficient. -/
theorem coefficient_constant (i : ℕ) (c : ℂ) :
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 i (constant c) =
      if i = 0 then c else 0 := by
  change DiscCoefficients.cauchyCoeff 1 coefficientRadius i (plane (constant c)) = _
  have he : DiscCoefficients.cauchyCoeff 1 coefficientRadius i (plane (constant c)) =
      c * (2 * Real.pi * Complex.I)⁻¹ *
        (∮ z in C(1, coefficientRadius), ((z - 1)^(i + 1))⁻¹) := by
    unfold DiscCoefficients.cauchyCoeff
    have hi : (∮ z in C(1, coefficientRadius), ((z - 1)^(i + 1))⁻¹ * plane (constant c) z) =
        (∮ z in C(1, coefficientRadius), c * ((z - 1)^(i + 1))⁻¹) := by
      apply circleIntegral.integral_congr coefficientRadius_pos.le
      intro z hz
      have hzD : z ∈ outer :=
        ball_subset_closedBall (closedBall_subset_ball radii.2.2 (sphere_subset_closedBall hz))
      change ((z - 1)^(i + 1))⁻¹ * plane (constant c) z = c * ((z - 1)^(i + 1))⁻¹
      rw [plane_eq (constant c) ⟨z, hzD⟩]
      exact mul_comm _ _
    rw [hi, circleIntegral.integral_const_mul]
    ring
  rw [he]
  cases i with
  | zero =>
    simp only [Nat.zero_add, pow_one, ite_true]
    rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self coefficientRadius_pos)]
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [mul_assoc, inv_mul_cancel₀ hpi, mul_one]
  | succ k =>
    simp only [Nat.succ_ne_zero, if_false]
    have hi := circleIntegral.integral_sub_zpow_of_ne
      (n := -((k + 1 + 1 : ℕ) : ℤ)) (by omega) (1 : ℂ) 1 coefficientRadius
    have hi' : (∮ z in C(1, coefficientRadius), ((z - 1)^(k + 1 + 1))⁻¹) = 0 := by
      simpa only [zpow_neg, zpow_natCast] using hi
    rw [hi', mul_zero]

/-- The actual pole projection occupies only the first Cauchy row. -/
theorem projectionMatrix_eq (i j : ℕ) :
    projectionMatrix i j =
      if i = 0 then ((balanceRadius : ℂ)^j)⁻¹ * (-1 : ℂ)^j else 0 := by
  change (balanceRadius : ℂ)^i *
    coefficient coefficientRadius coefficientRadius_pos radii.2.2 i
      (((balanceRadius : ℂ)^j)⁻¹ • constantProjection (monomial j)) = _
  rw [projection_monomial, map_smul, coefficient_constant, smul_eq_mul]
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, pow_zero, one_mul]
  · rw [if_neg hi, mul_zero, mul_zero, if_neg hi]

/-- The constant-mode matrix has the same fixed geometric rate as the source. -/
theorem geomDecay_projection : GeomFredholm.GeomDecay projectionMatrix 1 rate := by
  refine ⟨zero_le_one, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  rw [projectionMatrix_eq]
  by_cases hi : i = 0
  · subst i
    simp only [ite_true, pow_zero, one_mul]
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg balanceRadius_pos.le, norm_pow, norm_neg, norm_one,
      one_pow, mul_one, ← inv_pow]
    exact pow_le_pow_left₀ (inv_nonneg.mpr balanceRadius_pos.le)
      (by norm_num [balanceRadius, rate]) j
  · rw [if_neg hi, norm_zero]
    exact mul_nonneg (mul_nonneg zero_le_one (pow_nonneg rate_bounds.1 i))
      (pow_nonneg rate_bounds.1 j)

private theorem matrix_differentiableOn {F : ℂ → DiscSpace →L[ℂ] DiscSpace} {U : Set ℂ}
    (hF : DifferentiableOn ℂ F U) (i j : ℕ) :
    DifferentiableOn ℂ (fun w => operatorMatrix (F w) i j) U := by
  have hd := (ContinuousLinearMap.apply ℂ DiscSpace (monomial j)).differentiable.comp_differentiableOn hF
  have hd' : DifferentiableOn ℂ
      (fun w => ((balanceRadius : ℂ)^j)⁻¹ • F w (monomial j)) U :=
    hd.const_smul (((balanceRadius : ℂ)^j)⁻¹)
  exact (functional i).differentiable.comp_differentiableOn hd'

/-- Each entry of the genuine remainder matrix is holomorphic through one. -/
theorem differentiableOn_remainderMatrix (i j : ℕ) :
    DifferentiableOn ℂ (fun w => remainderMatrix w i j) {w : ℂ | 0 < w.re} :=
  matrix_differentiableOn differentiableOn_remainder i j

/-- A matrix supported on one row gives an affine determinant perturbation. -/
private theorem det_oneRow_affine {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hB : ∀ i, i ≠ 0 → ∀ j, B i j = 0) (t : ℂ) :
    (A + t • B).det = A.det + t * ((A + B).det - A.det) := by
  have hupdate (u : ℂ) : A + u • B = A.updateRow 0 (A 0 + u • B 0) := by
    ext i j
    by_cases hi : i = 0
    · subst i
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.updateRow_apply, ite_true, Pi.add_apply, Pi.smul_apply]
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        Matrix.updateRow_apply, if_neg hi, hB i hi j, mul_zero, add_zero]
  have hself : A.updateRow 0 (A 0) = A := by
    ext i j
    by_cases hi : i = 0
    · subst i; simp only [Matrix.updateRow_apply, ite_true]
    · simp only [Matrix.updateRow_apply, if_neg hi]
  have hdet (u : ℂ) : (A + u • B).det = A.det + u * (A.updateRow 0 (B 0)).det := by
    rw [hupdate, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, hself]
  have hone : (A + B).det = A.det + (A.updateRow 0 (B 0)).det := by
    simpa only [one_smul, one_mul] using hdet 1
  rw [hdet, hone]
  ring

/-- A parameter circle stays in the right half-plane and avoids the pole on its boundary. -/
private theorem parameter_circle {w : ℂ} (hw : 0 < w.re) :
    ∃ r : ℝ, 0 < r ∧ closedBall w r ⊆ {z : ℂ | 0 < z.re} ∧
      sphere w r ⊆ {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
  by_cases hw1 : w = 1
  · subst w
    have hb : closedBall (1 : ℂ) (1 / 2) ⊆ {z : ℂ | 0 < z.re} := by
      intro z hz
      have hd : ‖z - 1‖ ≤ (1 / 2 : ℝ) := by simpa only [mem_closedBall, dist_eq_norm] using hz
      have hr := (neg_le_abs (z - 1).re).trans ((Complex.abs_re_le_norm _).trans hd)
      simp only [Complex.sub_re, Complex.one_re] at hr
      change 0 < z.re
      linarith only [hr]
    refine ⟨1 / 2, by norm_num, hb, fun z hz => ⟨hb (sphere_subset_closedBall hz), ?_⟩⟩
    intro he
    subst z
    norm_num [mem_sphere] at hz
  · have hU : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter isClosed_singleton.isOpen_compl
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU w ⟨hw, hw1⟩
    have hc : closedBall w (r / 2) ⊆ {z : ℂ | 0 < z.re ∧ z ≠ 1} :=
      (closedBall_subset_ball (half_lt_self hr)).trans hball
    exact ⟨r / 2, half_pos hr, fun z hz => (hc hz).1,
      fun z hz => hc (sphere_subset_closedBall hz)⟩

private theorem geomDecay_add_smul {M N : ℕ → ℕ → ℂ} {C D : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) (hN : GeomFredholm.GeomDecay N D rate) (t : ℂ) :
    GeomFredholm.GeomDecay (fun i j => M i j + t * N i j) (C + ‖t‖ * D) rate := by
  refine ⟨add_nonneg hM.const_nonneg (mul_nonneg (norm_nonneg _) hN.const_nonneg),
    rate_bounds.1, rate_bounds.2, fun i j => ?_⟩
  calc
    ‖M i j + t * N i j‖ ≤ ‖M i j‖ + ‖t‖ * ‖N i j‖ := by
      simpa only [norm_mul] using norm_add_le (M i j) (t * N i j)
    _ ≤ C * rate^i * rate^j + ‖t‖ * (D * rate^i * rate^j) :=
      add_le_add (hM.bound i j) (mul_le_mul_of_nonneg_left (hN.bound i j) (norm_nonneg t))
    _ = _ := by ring

/-- The remainder matrix retains a locally uniform nuclear bound through the source pole. -/
theorem remainderMatrix_local_bound {w : ℂ} (hw : 0 < w.re) :
    ∃ r C : ℝ, 0 < r ∧ closedBall w r ⊆ {z : ℂ | 0 < z.re} ∧
      ∀ z ∈ closedBall w r, GeomFredholm.GeomDecay (remainderMatrix z) C rate := by
  obtain ⟨r, hr, hclosed, hsphere⟩ := parameter_circle hw
  obtain ⟨C, hC0, hC⟩ := constantBound_boundedOn_compact hsphere (isCompact_sphere w r)
  have hzcont : ContinuousOn riemannZeta (sphere w r) :=
    fun z hz => (differentiableAt_riemannZeta (hsphere hz).2).continuousAt.continuousWithinAt
  obtain ⟨Z, hZ⟩ := (isCompact_sphere w r).exists_bound_of_continuousOn hzcont
  have hZ0 : 0 ≤ max Z 0 := le_max_right _ _
  have hb : ∀ z ∈ sphere w r, ∀ i j,
      ‖remainderMatrix z i j‖ ≤ (C + max Z 0) * rate^i * rate^j := by
    intro z hz i j
    have hzw := (hsphere hz).1
    have he : remainderMatrix z i j = sourceMatrix z i j - riemannZeta z * projectionMatrix i j := by
      rw [sourceMatrix_decomposition]
      ring
    have hs : ‖sourceMatrix z i j‖ ≤ C * rate^i * rate^j := by
      rw [sourceMatrix_eq hzw]
      exact ((geomDecay_matrix hzw).bound i j).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC z hz) (pow_nonneg rate_bounds.1 i))
          (pow_nonneg rate_bounds.1 j))
    have hp : ‖riemannZeta z * projectionMatrix i j‖ ≤ max Z 0 * (rate^i * rate^j) := by
      rw [norm_mul]
      have hproj : ‖projectionMatrix i j‖ ≤ rate^i * rate^j := by
        simpa only [one_mul] using geomDecay_projection.bound i j
      exact mul_le_mul ((hZ z hz).trans (le_max_left _ _)) hproj (norm_nonneg _) hZ0
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add hs hp).trans_eq (by ring))
  refine ⟨r, C + max Z 0, hr, hclosed, fun z hz =>
    ⟨add_nonneg hC0 hZ0, rate_bounds.1, rate_bounds.2, fun i j => ?_⟩⟩
  have ha : AnalyticOnNhd ℂ (fun v => remainderMatrix v i j) (closedBall w r) :=
    ((differentiableOn_remainderMatrix i j).analyticOnNhd
      (isOpen_lt continuous_const Complex.continuous_re)).mono hclosed
  exact norm_le_of_sphere_bound_centre hr ha (fun v hv => hb v hv i j) z hz

/-- Add an arbitrary coefficient of the actual pole projection to the holomorphic remainder. -/
def perturbedMatrix (w t : ℂ) (i j : ℕ) : ℂ :=
  remainderMatrix w i j + t * projectionMatrix i j

/-- Fredholm determinant before choosing the meromorphic coefficient `t=ζ(w)`. -/
def perturbedDeterminant (w t lam : ℂ) : ℂ := GeomFredholm.fdet (perturbedMatrix w t) lam

theorem differentiable_perturbedDeterminant {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    Differentiable ℂ (perturbedDeterminant w t) := by
  obtain ⟨r, C, hr, _, hC⟩ := remainderMatrix_local_bound hw
  exact GeomFredholm.differentiable_fdet
    (geomDecay_add_smul (hC w (mem_closedBall_self hr.le)) geomDecay_projection t)

/-- The auxiliary determinants are source-holomorphic even at one. -/
theorem differentiableOn_perturbedDeterminant (t lam : ℂ) :
    DifferentiableOn ℂ (fun w => perturbedDeterminant w t lam) {w : ℂ | 0 < w.re} := by
  intro w hw
  obtain ⟨r, C, hr, hclosed, hC⟩ := remainderMatrix_local_bound hw
  have hM : ∀ z ∈ ball w r, GeomFredholm.GeomDecay (perturbedMatrix z t) (C + ‖t‖ * 1) rate :=
    fun z hz => geomDecay_add_smul (hC z (ball_subset_closedBall hz)) geomDecay_projection t
  have hd : ∀ i j, DifferentiableOn ℂ (fun z => perturbedMatrix z t i j) (ball w r) :=
    fun i j => ((differentiableOn_remainderMatrix i j).add (differentiableOn_const _)).mono
      (ball_subset_closedBall.trans hclosed)
  have hf := GeomFredholm.differentiableOn_fdet isOpen_ball hM hd lam rate_bounds.1 rate_bounds.2
  exact (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).differentiableWithinAt

/-- The genuine source determinant chooses exactly the scalar zeta coefficient. -/
theorem sourceDeterminant_eq_perturbed (w lam : ℂ) :
    sourceDeterminant w lam = perturbedDeterminant w (riemannZeta w) lam := by
  have he : sourceMatrix w = perturbedMatrix w (riemannZeta w) := by
    funext i j
    exact sourceMatrix_decomposition w i j
  exact congrArg (fun M => GeomFredholm.fdet M lam) he

private theorem truncDet_projection_affine (M : ℕ → ℕ → ℂ) (t lam : ℂ) (N : ℕ) :
    GeomFredholm.truncDet (fun i j => M i j + t * projectionMatrix i j) lam N =
      GeomFredholm.truncDet M lam N + t *
        (GeomFredholm.truncDet (fun i j => M i j + projectionMatrix i j) lam N -
          GeomFredholm.truncDet M lam N) := by
  cases N with
  | zero => simp [GeomFredholm.truncDet]
  | succ n =>
    let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := 1 - lam • GeomFredholm.trunc M (n + 1)
    let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := -lam • GeomFredholm.trunc projectionMatrix (n + 1)
    have hB : ∀ i : Fin (n + 1), i ≠ 0 → ∀ j, B i j = 0 := by
      intro i hi j
      have hi' : (i : ℕ) ≠ 0 := by
        intro he
        exact hi (Fin.ext he)
      change -lam * projectionMatrix i j = 0
      rw [projectionMatrix_eq, if_neg hi', mul_zero]
    have hA (u : ℂ) :
        1 - lam • GeomFredholm.trunc (fun i j => M i j + u * projectionMatrix i j) (n + 1) =
          A + u • B := by
      ext i j
      simp only [A, B, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, GeomFredholm.trunc, Matrix.of_apply]
      ring
    have hA1 :
        1 - lam • GeomFredholm.trunc (fun i j => M i j + projectionMatrix i j) (n + 1) = A + B := by
      simpa only [one_mul, one_smul] using hA 1
    unfold GeomFredholm.truncDet
    rw [hA, hA1]
    exact det_oneRow_affine A B hB t

/-- Exact affine dependence of the genuine Fredholm limit on the pole coefficient. -/
theorem perturbedDeterminant_affine {w : ℂ} (hw : 0 < w.re) (t lam : ℂ) :
    perturbedDeterminant w t lam = perturbedDeterminant w 0 lam + t *
      (perturbedDeterminant w 1 lam - perturbedDeterminant w 0 lam) := by
  obtain ⟨r, C, hr, _, hC⟩ := remainderMatrix_local_bound hw
  have hM := hC w (mem_closedBall_self hr.le)
  have ht := GeomFredholm.tendsto_truncDet (geomDecay_add_smul hM geomDecay_projection t) lam
  have h0 := GeomFredholm.tendsto_truncDet hM lam
  have h1 := GeomFredholm.tendsto_truncDet (geomDecay_add_smul hM geomDecay_projection 1) lam
  simp only [one_mul] at h1
  have hlim := h0.add ((h1.sub h0).const_mul t)
  have he : GeomFredholm.truncDet (fun i j => remainderMatrix w i j + t * projectionMatrix i j) lam =
      fun N => GeomFredholm.truncDet (remainderMatrix w) lam N + t *
        (GeomFredholm.truncDet (fun i j => remainderMatrix w i j + projectionMatrix i j) lam N -
          GeomFredholm.truncDet (remainderMatrix w) lam N) := by
    funext N
    exact truncDet_projection_affine _ t lam N
  rw [he] at ht
  have heq := tendsto_nhds_unique ht hlim
  have hz : perturbedMatrix w 0 = remainderMatrix w := by
    funext i j
    simp only [perturbedMatrix, zero_mul, add_zero]
  have ho : perturbedMatrix w 1 = fun i j => remainderMatrix w i j + projectionMatrix i j := by
    funext i j
    simp only [perturbedMatrix, one_mul]
  change GeomFredholm.fdet (perturbedMatrix w t) lam =
    GeomFredholm.fdet (perturbedMatrix w 0) lam + t *
      (GeomFredholm.fdet (perturbedMatrix w 1) lam - GeomFredholm.fdet (perturbedMatrix w 0) lam)
  rw [hz, ho]
  exact heq

/-- Determinant of the actual holomorphic operator remainder. -/
def regularPart (w lam : ℂ) : ℂ := perturbedDeterminant w 0 lam

/-- Exact coefficient of the zeta pole in the source determinant. -/
def polePart (w lam : ℂ) : ℂ :=
  perturbedDeterminant w 1 lam - perturbedDeterminant w 0 lam

theorem differentiable_regularPart {w : ℂ} (hw : 0 < w.re) : Differentiable ℂ (regularPart w) :=
  differentiable_perturbedDeterminant hw 0

theorem differentiable_polePart {w : ℂ} (hw : 0 < w.re) : Differentiable ℂ (polePart w) :=
  (differentiable_perturbedDeterminant hw 1).sub (differentiable_perturbedDeterminant hw 0)

theorem differentiableOn_regularPart (lam : ℂ) :
    DifferentiableOn ℂ (fun w => regularPart w lam) {w : ℂ | 0 < w.re} :=
  differentiableOn_perturbedDeterminant 0 lam

theorem differentiableOn_polePart (lam : ℂ) :
    DifferentiableOn ℂ (fun w => polePart w lam) {w : ℂ | 0 < w.re} :=
  (differentiableOn_perturbedDeterminant 1 lam).sub (differentiableOn_perturbedDeterminant 0 lam)

/-- The actual source determinant is affine in zeta, with coefficients holomorphic through one. -/
theorem sourceDeterminant_decomposition {w : ℂ} (hw : 0 < w.re) (lam : ℂ) :
    sourceDeterminant w lam = regularPart w lam + riemannZeta w * polePart w lam := by
  rw [sourceDeterminant_eq_perturbed, perturbedDeterminant_affine hw]
  rfl

/-- The actual determinant residue is the entire spectral function `polePart 1`. -/
theorem determinant_residue (lam : ℂ) :
    Tendsto (fun w : ℂ => (w - 1) * sourceDeterminant w lam) (𝓝[≠] 1)
      (𝓝 (polePart 1 lam)) := by
  have hH : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : ContinuousAt (fun w => regularPart w lam) 1 :=
    ((differentiableOn_regularPart lam).differentiableAt (hH.mem_nhds (by norm_num))).continuousAt
  have hB : ContinuousAt (fun w => polePart w lam) 1 :=
    ((differentiableOn_polePart lam).differentiableAt (hH.mem_nhds (by norm_num))).continuousAt
  have hw : Tendsto (fun w : ℂ => w - 1) (𝓝[≠] 1) (𝓝 0) := by
    have hc : Continuous (fun w : ℂ => w - 1) := continuous_id.sub continuous_const
    simpa only [sub_self] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim := (hw.mul (hA.tendsto.mono_left nhdsWithin_le_nhds)).add
    (riemannZeta_residue_one.mul (hB.tendsto.mono_left nhdsWithin_le_nhds))
  have he : (fun w : ℂ => (w - 1) * regularPart w lam +
      ((w - 1) * riemannZeta w) * polePart w lam) =ᶠ[𝓝[≠] 1]
        (fun w : ℂ => (w - 1) * sourceDeterminant w lam) := by
    have hh : ∀ᶠ w : ℂ in 𝓝[≠] 1, 0 < w.re :=
      nhdsWithin_le_nhds (hH.mem_nhds (by norm_num))
    filter_upwards [hh] with w hw
    rw [sourceDeterminant_decomposition hw]
    ring
  simpa only [zero_mul, one_mul, zero_add] using hlim.congr' he

private theorem fdet_zero {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) : GeomFredholm.fdet M 0 = 1 := by
  rw [GeomFredholm.fdet_eq_exp_of_small hM (by simp)]
  simp [GeomFredholm.traceSeries]

/-- The first coefficient follows from the normally convergent power-trace exponential. -/
private theorem fdet_deriv_zero {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) :
    deriv (GeomFredholm.fdet M) 0 = -(∑' i, M i i) := by
  let a : ℝ := C * GeomFredholm.sqSum rate
  let B : ℝ := a + 1
  let r : ℝ := (2 * B)⁻¹
  have ha0 : 0 ≤ a := mul_nonneg hM.const_nonneg
    (GeomFredholm.sqSum_pos rate_bounds.1 rate_bounds.2).le
  have hB1 : 1 ≤ B := by dsimp [B]; linarith only [ha0]
  have hBpos : 0 < B := zero_lt_one.trans_le hB1
  have hr : 0 < r := inv_pos.mpr (mul_pos (by norm_num) hBpos)
  have hrB : r * B < 1 := by
    dsimp [r]
    rw [inv_mul_lt_iff₀ (mul_pos (by norm_num) hBpos)]
    linarith only [hBpos]
  have hab : a ≤ B := by dsimp [B]; linarith
  have hbound (k : ℕ) : ‖GeomFredholm.itrace M (k + 1)‖ ≤ a * B^k := by
    calc
      _ ≤ a^(k + 1) := GeomFredholm.norm_itrace_succ_le hM k
      _ = a * a^k := pow_succ' a k
      _ ≤ a * B^k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 hab k) ha0
  have he : GeomFredholm.fdet M =ᶠ[𝓝 0] tracePowerDet 1 (GeomFredholm.itrace M) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) hr] with z hz
    have hz' : ‖z‖ ≤ r := (mem_ball_zero_iff.mp hz).le
    exact GeomFredholm.fdet_eq_exp_of_small hM
      ((mul_le_mul hz' hab ha0 hr.le).trans_lt hrB)
  have hz0 : (0 : ℂ) ∈ ball 0 r := mem_ball_self hr
  have hd := deriv_tracePowerDetExp_eq (by decide : 0 < (1 : ℕ))
    hB1 ha0 hbound hr hrB hz0
  have hd' : deriv (tracePowerDetExp 1 (GeomFredholm.itrace M)) 0 = GeomFredholm.itrace M 1 := by
    rw [hd]
    simp only [Nat.add_sub_cancel]
    rw [tsum_eq_single 0]
    · simp only [pow_zero, one_mul, Nat.zero_add]
    · intro k hk
      rw [zero_pow hk, zero_mul]
  rw [he.deriv_eq, deriv_tracePowerDet_eq (by decide : 0 < (1 : ℕ)) hB1 ha0 hbound hr hrB hz0, hd']
  have hzero : tracePowerDet 1 (GeomFredholm.itrace M) 0 = 1 := by
    simp [tracePowerDet, tracePowerDetExp]
  rw [hzero, neg_one_mul]
  simp only [GeomFredholm.itrace, GeomFredholm.ipow_one]

private theorem diagonal_summable {M : ℕ → ℕ → ℂ} {C : ℝ}
    (hM : GeomFredholm.GeomDecay M C rate) : Summable (fun i => M i i) := by
  have hs := (GeomFredholm.hasSum_pow_two_mul rate_bounds.1 rate_bounds.2).summable.mul_left C
  have hn : Summable (fun i => ‖M i i‖) :=
    hs.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i =>
      (hM.bound i i).trans_eq (mul_assoc _ _ _))
  exact hn.of_norm

theorem perturbedDeterminant_zero {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    perturbedDeterminant w t 0 = 1 := by
  obtain ⟨r, C, hr, _, hC⟩ := remainderMatrix_local_bound hw
  exact fdet_zero (geomDecay_add_smul (hC w (mem_closedBall_self hr.le)) geomDecay_projection t)

private theorem perturbedDeterminant_deriv_zero {w : ℂ} (hw : 0 < w.re) (t : ℂ) :
    deriv (perturbedDeterminant w t) 0 =
      -(∑' i, (remainderMatrix w i i + t * projectionMatrix i i)) := by
  obtain ⟨r, C, hr, _, hC⟩ := remainderMatrix_local_bound hw
  have h := fdet_deriv_zero
    (geomDecay_add_smul (hC w (mem_closedBall_self hr.le)) geomDecay_projection t)
  have he : perturbedDeterminant w t =
      GeomFredholm.fdet (fun i j => remainderMatrix w i j + t * projectionMatrix i j) := by
    funext lam
    rfl
  rw [he]
  exact h

/-- The zero spectral parameter necessarily cancels the pole. -/
theorem polePart_zero {w : ℂ} (hw : 0 < w.re) : polePart w 0 = 0 := by
  rw [polePart, perturbedDeterminant_zero hw, perturbedDeterminant_zero hw, sub_self]

/-- The pole coefficient has the exact nonzero first spectral derivative. -/
theorem polePart_deriv_zero {w : ℂ} (hw : 0 < w.re) : deriv (polePart w) 0 = -1 := by
  have hd1 := (differentiable_perturbedDeterminant hw 1 0).hasDerivAt
  have hd0 := (differentiable_perturbedDeterminant hw 0 0).hasDerivAt
  have he : deriv (polePart w) 0 = deriv (perturbedDeterminant w 1) 0 -
      deriv (perturbedDeterminant w 0) 0 := (hd1.sub hd0).deriv
  rw [he, perturbedDeterminant_deriv_zero hw, perturbedDeterminant_deriv_zero hw]
  simp only [one_mul, zero_mul, add_zero]
  obtain ⟨r, C, hr, _, hC⟩ := remainderMatrix_local_bound hw
  rw [(diagonal_summable (hC w (mem_closedBall_self hr.le))).tsum_add
    (diagonal_summable geomDecay_projection)]
  have hP : (∑' i, projectionMatrix i i) = 1 := by
    rw [tsum_eq_single 0]
    · simp only [projectionMatrix_eq, ite_true, pow_zero, inv_one, one_mul]
    · intro i hi
      rw [projectionMatrix_eq, if_neg hi]
  rw [hP]
  ring

/-- The actual determinant with its possible simple pole removed algebraically. -/
def clearedDeterminant (lam w : ℂ) : ℂ :=
  (w - 1) * regularPart w lam + _root_.RHTower.zetaResidueUnit w * polePart w lam

theorem differentiableOn_clearedDeterminant (lam : ℂ) :
    DifferentiableOn ℂ (clearedDeterminant lam) {w : ℂ | 0 < w.re} := by
  have hz : Differentiable ℂ _root_.RHTower.zetaResidueUnit :=
    fun w => (_root_.RHTower.analyticAt_zetaResidueUnit w).differentiableAt
  exact ((differentiableOn_id.sub_const 1).mul (differentiableOn_regularPart lam)).add
    (hz.differentiableOn.mul (differentiableOn_polePart lam))

theorem clearedDeterminant_one (lam : ℂ) : clearedDeterminant lam 1 = polePart 1 lam := by
  simp only [clearedDeterminant, sub_self, zero_mul, _root_.RHTower.zetaResidueUnit_one,
    one_mul, zero_add]

/-- The cleared source determinant is holomorphic across one, for every spectral parameter. -/
theorem analyticAt_clearedDeterminant_one (lam : ℂ) : AnalyticAt ℂ (clearedDeterminant lam) 1 :=
  (differentiableOn_clearedDeterminant lam).analyticAt
    ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))

theorem clearedDeterminant_eq {w : ℂ} (hw : 0 < w.re) (hw1 : w ≠ 1) (lam : ℂ) :
    clearedDeterminant lam w = (w - 1) * sourceDeterminant w lam := by
  rw [clearedDeterminant, _root_.RHTower.zetaResidueUnit, Function.update_of_ne hw1,
    sourceDeterminant_decomposition hw]
  ring

/-- The actual source determinant is meromorphic at one, including cancellation parameters. -/
theorem meromorphicAt_sourceDeterminant_one (lam : ℂ) :
    MeromorphicAt (fun w => sourceDeterminant w lam) 1 := by
  have hA : AnalyticAt ℂ (fun w : ℂ => (w - 1) * clearedDeterminant lam w) 1 :=
    (analyticAt_id.sub analyticAt_const).mul (analyticAt_clearedDeterminant_one lam)
  refine ⟨2, hA.congr ?_⟩
  have hh : ∀ᶠ w : ℂ in 𝓝 1, 0 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hh] with w hw
  by_cases hw1 : w = 1
  · subst w
    simp only [sub_self, zero_mul, zero_pow two_ne_zero, zero_smul]
  · rw [clearedDeterminant_eq hw hw1, smul_eq_mul]
    ring

/-- Nonvanishing of the exact residue gives a pole of order exactly one. -/
theorem sourceDeterminant_order_of_residue_ne_zero {lam : ℂ} (hB : polePart 1 lam ≠ 0) :
    meromorphicOrderAt (fun w => sourceDeterminant w lam) 1 = -1 := by
  apply (meromorphicOrderAt_eq_int_iff (meromorphicAt_sourceDeterminant_one lam)).mpr
  refine ⟨clearedDeterminant lam, analyticAt_clearedDeterminant_one lam, ?_, ?_⟩
  · rwa [clearedDeterminant_one]
  · have hh : ∀ᶠ w : ℂ in 𝓝[≠] 1, 0 < w.re :=
      nhdsWithin_le_nhds ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (by norm_num))
    filter_upwards [hh, self_mem_nhdsWithin] with w hw hw1
    rw [clearedDeterminant_eq hw hw1, smul_eq_mul]
    simp only [zpow_neg, zpow_one]
    field_simp [sub_ne_zero.mpr hw1]

/-- Removability is exactly the vanishing of the entire spectral residue. -/
theorem sourceDeterminant_removable_iff (lam : ℂ) :
    (∃ F : ℂ → ℂ, AnalyticAt ℂ F 1 ∧
      F =ᶠ[𝓝[≠] 1] (fun w => sourceDeterminant w lam)) ↔ polePart 1 lam = 0 := by
  constructor
  · rintro ⟨F, hF, he⟩
    have hw : Tendsto (fun w : ℂ => w - 1) (𝓝[≠] 1) (𝓝 0) := by
      have hc : Continuous (fun w : ℂ => w - 1) := continuous_id.sub continuous_const
      simpa only [sub_self] using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    have hzero : Tendsto (fun w : ℂ => (w - 1) * sourceDeterminant w lam)
        (𝓝[≠] 1) (𝓝 0) := by
      have ht := hw.mul (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      have he' : (fun w : ℂ => (w - 1) * F w) =ᶠ[𝓝[≠] 1]
          (fun w => (w - 1) * sourceDeterminant w lam) := by
        filter_upwards [he] with w hw
        rw [hw]
      simpa only [zero_mul] using ht.congr' he'
    exact tendsto_nhds_unique (determinant_residue lam) hzero
  · intro hB
    have hH : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) := hH.mem_nhds (by norm_num)
    have hd : DifferentiableOn ℂ (dslope (clearedDeterminant lam) 1) {w : ℂ | 0 < w.re} :=
      (differentiableOn_dslope hmem).mpr (differentiableOn_clearedDeterminant lam)
    refine ⟨dslope (clearedDeterminant lam) 1, hd.analyticAt hmem, ?_⟩
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with w hw hw1
    have he := sub_smul_dslope (clearedDeterminant lam) 1 w
    rw [smul_eq_mul, clearedDeterminant_one, hB, sub_zero, clearedDeterminant_eq hw hw1] at he
    exact mul_left_cancel₀ (sub_ne_zero.mpr hw1) he

private theorem exists_polePart_ne_zero {w : ℂ} (hw : 0 < w.re) :
    ∃ lam, polePart w lam ≠ 0 := by
  by_contra hn
  push Not at hn
  have he : polePart w = fun _ : ℂ => 0 := funext hn
  have hd := polePart_deriv_zero hw
  rw [he, deriv_const] at hd
  norm_num at hd

/-- For every source parameter the zeros of the pole coefficient form a closed discrete set. -/
theorem polePart_zeros_closed_discrete {w : ℂ} (hw : 0 < w.re) :
    IsClosed {lam | polePart w lam = 0} ∧ IsDiscrete {lam | polePart w lam = 0} := by
  have ha : AnalyticOnNhd ℂ (polePart w) univ :=
    fun lam _ => (differentiable_polePart hw).analyticAt lam
  obtain ⟨lam, hlam⟩ := exists_polePart_ne_zero hw
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with he | he
  · exact (hlam (he (mem_univ lam))).elim
  · exact compl_mem_codiscrete_iff.mp he

/-- The exceptional spectral parameters are countable. -/
theorem countable_polePart_zeros {w : ℂ} (hw : 0 < w.re) :
    {lam | polePart w lam = 0}.Countable := by
  obtain ⟨lam, hlam⟩ := exists_polePart_ne_zero hw
  exact countable_zeros_of_entire_nonzero (differentiable_polePart hw) hlam

/-- Every sufficiently small nonzero spectral parameter gives a genuine simple source pole. -/
theorem eventually_sourceDeterminant_simple_pole :
    ∀ᶠ lam : ℂ in 𝓝[≠] 0,
      meromorphicOrderAt (fun w => sourceDeterminant w lam) 1 = -1 := by
  have hC : {lam | polePart 1 lam = 0}ᶜ ∈ codiscrete ℂ :=
    compl_mem_codiscrete_iff.mpr (polePart_zeros_closed_discrete (by norm_num))
  have he : {lam | polePart 1 lam = 0}ᶜ ∈ 𝓝[≠] (0 : ℂ) := by
    simpa only [compl_compl] using
      (disjoint_principal_right.mp ((mem_codiscrete.mp hC) 0))
  have hne : ∀ᶠ lam : ℂ in 𝓝[≠] 0, polePart 1 lam ≠ 0 := by
    filter_upwards [he] with lam hlam
    exact hlam
  exact hne.mono fun _ h => sourceDeterminant_order_of_residue_ne_zero h

#print axioms projectionMatrix_eq
#print axioms geomDecay_projection
#print axioms remainderMatrix_local_bound
#print axioms differentiableOn_perturbedDeterminant
#print axioms perturbedDeterminant_affine
#print axioms sourceDeterminant_decomposition
#print axioms determinant_residue
#print axioms polePart_deriv_zero
#print axioms meromorphicAt_sourceDeterminant_one
#print axioms sourceDeterminant_order_of_residue_ne_zero
#print axioms sourceDeterminant_removable_iff
#print axioms polePart_zeros_closed_discrete
#print axioms countable_polePart_zeros
#print axioms eventually_sourceDeterminant_simple_pole

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerPole
