import GaloisForLFunctions.RHTower.SelbergMaassCuspTransport

/-!
# Selberg's mean-value theorem for rotation averages

For `k_θ = [[cos θ, sin θ], [-sin θ, cos θ]]`, the orbit chart `M(θ,y) = k_θ·(iy)` has
`∂_θ M = (1-y²)/D²` and `∂_y M = i/D²` with `D = cos θ - iy sin θ`. For any real-`C²`
eigenfunction `G` of the positive hyperbolic Laplacian (eigenvalue `λ ∈ ℂ`), the conformal
trace of the real Hessian gives the pointwise orbit identity

  `∂²_θ G(M) = (1-y²)²(-λG/y² - ∂²_y G(M)) + 2y(1-y²)∂_y G(M)`.

Averaging over a full period kills the left side, so the rotation average `A(y)` satisfies
`(1-y²)(-λA/y² - A'') + 2yA' = 0` for `y ≠ 1`. A Gronwall argument on `[1, ∞)` plus the symmetry
`A(1/y) = A(y)` shows that a solution vanishing at `y = 1` vanishes identically. Hence two
eigenfunctions with the same eigenvalue have proportional rotation averages
(`rotAverage_eq_smul`). This is Selberg's point-pair-invariant principle, proved without Legendre
functions. It is the first layer of the pretrace/counting route to uniform spectral gaps.
-/

open Complex Set Filter Topology UpperHalfPlane MeasureTheory
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.HyperbolicRotationMean
noncomputable section

/-- The rotation matrix fixing `i`. -/
def rotMatrix (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

theorem rotMatrix_det (θ : ℝ) : (rotMatrix θ).det = 1 := by
  rw [rotMatrix, Matrix.det_fin_two_of]
  nlinarith [Real.cos_sq_add_sin_sq θ]

/-- The rotation about `i` as an element of `GL(2,ℝ)`. -/
def rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (rotMatrix θ) (by rw [rotMatrix_det]; norm_num)

theorem rot_det (θ : ℝ) : (rot θ).val.det = 1 := rotMatrix_det θ

theorem rot_det_pos (θ : ℝ) : 0 < (rot θ).val.det := by rw [rot_det]; norm_num

theorem rot_det_pos' (θ : ℝ) : 0 < ((Matrix.GeneralLinearGroup.det (rot θ) : ℝˣ) : ℝ) := by
  simpa [Matrix.GeneralLinearGroup.val_det_apply] using rot_det_pos θ

theorem rot_add (θ φ : ℝ) : rot (θ + φ) = rot θ * rot φ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, rotMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.mul_apply,
      Fin.sum_univ_two, Real.cos_add, Real.sin_add] <;> ring

theorem rot_add_smul (θ φ : ℝ) (z : ℍ) : rot (θ + φ) • z = rot θ • rot φ • z := by
  rw [rot_add, mul_smul]

/-- Numerator and denominator of the rotation action in the complex chart. -/
theorem coe_rot_smul (θ : ℝ) (z : ℍ) :
    ((rot θ • z : ℍ) : ℂ) =
      ((z : ℂ) * Real.cos θ + Real.sin θ) / (-(z : ℂ) * Real.sin θ + Real.cos θ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (rot_det_pos' θ)]
  simp [UpperHalfPlane.num, UpperHalfPlane.denom, rot, rotMatrix,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ring

theorem rot_denom_ne_zero (θ : ℝ) (z : ℍ) :
    -(z : ℂ) * Real.sin θ + Real.cos θ ≠ 0 := by
  have h := UpperHalfPlane.denom_ne_zero (rot θ) z
  simpa [UpperHalfPlane.denom, rot, rotMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    neg_mul, mul_comm] using h

theorem rot_zero_smul (z : ℍ) : rot 0 • z = z := by
  apply UpperHalfPlane.ext
  rw [coe_rot_smul]
  simp

/-- The rotation flow has generator `1 + w²`. -/
theorem hasDerivAt_rot_smul (θ : ℝ) (z : ℍ) :
    HasDerivAt (fun t : ℝ => ((rot t • z : ℍ) : ℂ))
      (1 + ((rot θ • z : ℍ) : ℂ) ^ 2) θ := by
  have hN : HasDerivAt (fun t : ℝ => (z : ℂ) * Real.cos t + Real.sin t)
      (-(z : ℂ) * Real.sin θ + Real.cos θ) θ := by
    have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp).const_mul (z : ℂ)
    have h2 := (Real.hasDerivAt_sin θ).ofReal_comp
    exact (h1.add h2).congr_deriv (by push_cast; ring)
  have hD : HasDerivAt (fun t : ℝ => -(z : ℂ) * Real.sin t + Real.cos t)
      (-((z : ℂ) * Real.cos θ + Real.sin θ)) θ := by
    have h1 := ((Real.hasDerivAt_sin θ).ofReal_comp).const_mul (-(z : ℂ))
    have h2 := (Real.hasDerivAt_cos θ).ofReal_comp
    exact (h1.add h2).congr_deriv (by push_cast; ring)
  have hne := rot_denom_ne_zero θ z
  have hq := hN.div hD hne
  have he : (fun t : ℝ => ((rot t • z : ℍ) : ℂ)) =
      fun t => ((z : ℂ) * Real.cos t + Real.sin t) / (-(z : ℂ) * Real.sin t + Real.cos t) := by
    funext t
    exact coe_rot_smul t z
  rw [he]
  refine hq.congr_deriv ?_
  rw [coe_rot_smul, div_pow, one_add_div (pow_ne_zero 2 hne)]
  congr 1
  ring

/-! ### The orbit chart `M(θ,y) = k_θ·(iy)` -/

/-- Denominator of the orbit chart. -/
def orbitDen (θ y : ℝ) : ℂ := Real.cos θ - Complex.I * y * Real.sin θ

/-- Numerator of the orbit chart. -/
def orbitNum (θ y : ℝ) : ℂ := Complex.I * y * Real.cos θ + Real.sin θ

/-- The orbit chart `k_θ·(iy)` in complex coordinates. -/
def orbit (θ y : ℝ) : ℂ := orbitNum θ y / orbitDen θ y

theorem orbitDen_normSq (θ y : ℝ) :
    Complex.normSq (orbitDen θ y) = Real.cos θ ^ 2 + y ^ 2 * Real.sin θ ^ 2 := by
  unfold orbitDen
  generalize Real.cos θ = c
  generalize Real.sin θ = s
  simp [Complex.normSq_apply]
  ring

theorem orbitDen_ne_zero (θ : ℝ) {y : ℝ} (hy : 0 < y) : orbitDen θ y ≠ 0 := by
  intro h
  have hn := orbitDen_normSq θ y
  rw [h, Complex.normSq_zero] at hn
  have hc := Real.cos_sq_add_sin_sq θ
  have h1 : y ^ 2 * Real.sin θ ^ 2 = 0 := by
    nlinarith [sq_nonneg (Real.cos θ), mul_nonneg (sq_nonneg y) (sq_nonneg (Real.sin θ))]
  have hs : Real.sin θ ^ 2 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · nlinarith [pow_pos hy 2]
    · exact h
  have hc0 : Real.cos θ ^ 2 = 0 := by nlinarith [sq_nonneg (Real.cos θ)]
  linarith

/-- Key conformal identity `D² + N² = 1 − y²`. -/
theorem orbit_num_sq_add_den_sq (θ y : ℝ) :
    orbitDen θ y ^ 2 + orbitNum θ y ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
  have hc : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  unfold orbitDen orbitNum
  generalize (Real.cos θ : ℂ) = c at hc ⊢
  generalize (Real.sin θ : ℂ) = s at hc ⊢
  push_cast
  linear_combination (1 + Complex.I ^ 2 * (y : ℂ) ^ 2) * hc + (y : ℂ) ^ 2 * Complex.I_sq

theorem orbit_im (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    (orbit θ y).im = y / Complex.normSq (orbitDen θ y) := by
  have hn : Complex.normSq (orbitDen θ y) ≠ 0 := by
    rw [Ne, Complex.normSq_eq_zero]; exact orbitDen_ne_zero θ hy
  have hc := Real.cos_sq_add_sin_sq θ
  rw [orbit, Complex.div_im]
  rw [orbitDen_normSq] at hn ⊢
  unfold orbitNum orbitDen
  generalize Real.cos θ = c at hc hn ⊢
  generalize Real.sin θ = s at hc hn ⊢
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    Complex.sub_re]
  field_simp
  nlinarith [hc]

theorem orbit_im_pos (θ : ℝ) {y : ℝ} (hy : 0 < y) : 0 < (orbit θ y).im := by
  rw [orbit_im θ hy]
  exact div_pos hy (Complex.normSq_pos.mpr (orbitDen_ne_zero θ hy))

theorem orbit_zero (y : ℝ) : orbit 0 y = Complex.I * y := by
  simp [orbit, orbitNum, orbitDen]

/-- Conformal factor `1/D²`. -/
def orbitConf (θ y : ℝ) : ℂ := 1 / orbitDen θ y ^ 2

theorem hasDerivAt_orbitNum_θ (θ y : ℝ) :
    HasDerivAt (fun t => orbitNum t y) (orbitDen θ y) θ := by
  unfold orbitNum orbitDen
  have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp).const_mul (Complex.I * y)
  have h2 := (Real.hasDerivAt_sin θ).ofReal_comp
  exact (h1.add h2).congr_deriv (by push_cast; ring)

theorem hasDerivAt_orbitDen_θ (θ y : ℝ) :
    HasDerivAt (fun t => orbitDen t y) (-orbitNum θ y) θ := by
  unfold orbitNum orbitDen
  have h1 := (Real.hasDerivAt_cos θ).ofReal_comp
  have h2 := ((Real.hasDerivAt_sin θ).ofReal_comp).const_mul (Complex.I * y)
  exact (h1.sub h2).congr_deriv (by push_cast; ring)

theorem hasDerivAt_orbitNum_y (θ y : ℝ) :
    HasDerivAt (fun t => orbitNum θ t) (Complex.I * Real.cos θ) y := by
  unfold orbitNum
  have h := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul Complex.I).mul_const
    (Real.cos θ : ℂ)
  exact (h.add_const _).congr_deriv (by simp)

theorem hasDerivAt_orbitDen_y (θ y : ℝ) :
    HasDerivAt (fun t => orbitDen θ t) (-(Complex.I * Real.sin θ)) y := by
  unfold orbitDen
  have h := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul Complex.I).mul_const
    (Real.sin θ : ℂ)
  exact (h.const_sub _).congr_deriv (by simp)

theorem hasDerivAt_orbit_θ (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => orbit t y) (((1 - y ^ 2 : ℝ) : ℂ) * orbitConf θ y) θ := by
  have h := (hasDerivAt_orbitNum_θ θ y).div (hasDerivAt_orbitDen_θ θ y) (orbitDen_ne_zero θ hy)
  refine h.congr_deriv ?_
  rw [orbitConf, ← orbit_num_sq_add_den_sq θ y]
  field_simp
  ring

theorem hasDerivAt_orbit_y (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => orbit θ t) (Complex.I * orbitConf θ y) y := by
  have h := (hasDerivAt_orbitNum_y θ y).div (hasDerivAt_orbitDen_y θ y) (orbitDen_ne_zero θ hy)
  refine h.congr_deriv ?_
  have hc : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  rw [orbitConf]
  unfold orbitNum orbitDen
  have hD := orbitDen_ne_zero θ hy
  unfold orbitDen at hD
  field_simp
  linear_combination hc

theorem hasDerivAt_orbitConf_θ (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => orbitConf t y) (2 * orbit θ y * orbitConf θ y) θ := by
  have hD := orbitDen_ne_zero θ hy
  have h := ((hasDerivAt_orbitDen_θ θ y).pow 2).inv (pow_ne_zero 2 hD)
  unfold orbitConf
  simp only [one_div]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [orbit]
  norm_num
  field_simp

theorem hasDerivAt_orbitConf_y (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => orbitConf θ t)
      (2 * Complex.I * Real.sin θ / orbitDen θ y ^ 3) y := by
  have hD := orbitDen_ne_zero θ hy
  have h := ((hasDerivAt_orbitDen_y θ y).pow 2).inv (pow_ne_zero 2 hD)
  unfold orbitConf
  simp only [one_div]
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  norm_num
  field_simp

/-- The vector identity behind the averaged ODE:
`(1-y²)·(-2 sin θ / D³) + 2 M c = 2 y I c`. -/
theorem orbit_vector_identity (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    ((1 - y ^ 2 : ℝ) : ℂ) * (-2 * Real.sin θ / orbitDen θ y ^ 3) +
        2 * orbit θ y * orbitConf θ y = 2 * y * Complex.I * orbitConf θ y := by
  have hD := orbitDen_ne_zero θ hy
  rw [orbitConf, orbit]
  field_simp
  unfold orbitNum orbitDen
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem orbitConf_normSq_div_im_sq (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    Complex.normSq (orbitConf θ y) / (orbit θ y).im ^ 2 = 1 / y ^ 2 := by
  have hD := orbitDen_ne_zero θ hy
  have hn : Complex.normSq (orbitDen θ y) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  rw [orbitConf, orbit_im θ hy, Complex.normSq_div, Complex.normSq_one, map_pow]
  field_simp

/-! ### Calculus of a C² function along the orbit chart -/

/-- Second derivative of a C² function along a C² curve. -/
theorem curve_second {F : ℂ → ℂ} {γ γ' : ℝ → ℂ} {γ'' : ℂ} {t : ℝ}
    (hF : ContDiffAt ℝ 2 F (γ t)) (hγ : HasDerivAt γ (γ' t) t) (hγ' : HasDerivAt γ' γ'' t) :
    HasDerivAt (fun s => fderiv ℝ F (γ s) (γ' s))
      (fderiv ℝ (fderiv ℝ F) (γ t) (γ' t) (γ' t) + fderiv ℝ F (γ t) γ'') t := by
  have hDF : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) (γ t)) (γ t) :=
    ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hc := hDF.comp_hasDerivAt t hγ
  exact hc.clm_apply hγ'

private theorem real_linear_expand {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℂ →L[ℝ] E) (w : ℂ) :
    A w = w.re • A 1 + w.im • A Complex.I := by
  have he : w = w.re • (1 : ℂ) + w.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using w.re_add_im.symm
  calc A w = A (w.re • (1 : ℂ) + w.im • Complex.I) := congrArg A he
    _ = _ := by rw [A.map_add, A.map_smul, A.map_smul]

/-- Conformal trace of a real bilinear form. -/
theorem bilinear_conformal_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (a : ℂ) :
    B a a + B (Complex.I * a) (Complex.I * a) =
      (Complex.normSq a : ℂ) * (B 1 1 + B Complex.I Complex.I) := by
  rw [real_linear_expand B a, real_linear_expand B (Complex.I * a)]
  simp only [add_apply, smul_apply]
  rw [real_linear_expand (B 1) a, real_linear_expand (B Complex.I) a,
    real_linear_expand (B 1) (Complex.I * a), real_linear_expand (B Complex.I) (Complex.I * a)]
  simp only [Complex.I_mul_re, Complex.I_mul_im, Complex.real_smul,
    Complex.normSq_apply, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

theorem clm_real_mul (A : ℂ →L[ℝ] ℂ) (r : ℝ) (z : ℂ) : A ((r : ℂ) * z) = (r : ℂ) * A z := by
  rw [← Complex.real_smul, A.map_smul, Complex.real_smul]

theorem bilinear_real_mul (B : ℂ →L[ℝ] ℂ →L[ℝ] ℂ) (r : ℝ) (z : ℂ) :
    B ((r : ℂ) * z) ((r : ℂ) * z) = ((r ^ 2 : ℝ) : ℂ) * B z z := by
  rw [← Complex.real_smul, B.map_smul, smul_apply,
    (B z).map_smul, smul_smul, Complex.real_smul]
  push_cast
  ring

section eigen

variable {G : ℍ → ℂ} (hG : IsRealSmoothUpperHalfPlane G) {lam : ℂ}
  (heig : ∀ z, positiveHyperbolicLaplacian G z = lam * G z)

include hG in
theorem chart_contDiffAt {w : ℂ} (hw : 0 < w.im) : ContDiffAt ℝ 2 (G ∘ ofComplex) w :=
  hG.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hw)

include hG heig in
/-- The eigen-equation as a trace of the real Hessian in the chart. -/
theorem hessian_trace {w : ℂ} (hw : 0 < w.im) :
    fderiv ℝ (fderiv ℝ (G ∘ ofComplex)) w 1 1 +
        fderiv ℝ (fderiv ℝ (G ∘ ofComplex)) w Complex.I Complex.I =
      -(lam * (G ∘ ofComplex) w) / ((w.im : ℂ) ^ 2) := by
  have hF := chart_contDiffAt hG hw
  have hsec : ∀ v : ℂ, fderiv ℝ (fun u => fderiv ℝ (G ∘ ofComplex) u v) w v =
      fderiv ℝ (fderiv ℝ (G ∘ ofComplex)) w v v := by
    intro v
    have hh := ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
    have hd := hh.clm_apply (hasFDerivAt_const v w)
    simpa using congrArg (fun L => L v) hd.fderiv
  have he := heig ⟨w, hw⟩
  simp only [positiveHyperbolicLaplacian, UpperHalfPlane.im] at he
  rw [hsec 1, hsec Complex.I] at he
  have hy : ((w.im : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hw.ne')
  have hGw : (G ∘ ofComplex) w = G ⟨w, hw⟩ := by
    simp [Function.comp_apply, ofComplex_apply_of_im_pos hw]
  rw [hGw, eq_div_iff hy]
  linear_combination -he

include hG heig in
/-- **Orbit identity.** Along `M(θ,y) = k_θ·(iy)`, with `h'' ` the second θ-derivative
and `v', v''` the y-derivatives of `F(M)`, one has
`h'' = (1-y²)²(-λF/y² - v'') + 2y(1-y²)v'`. -/
theorem orbit_identity (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    let F := G ∘ ofComplex
    let M := orbit θ y
    let c := orbitConf θ y
    let B := fderiv ℝ (fderiv ℝ F) M
    (B (((1 - y ^ 2 : ℝ) : ℂ) * c) (((1 - y ^ 2 : ℝ) : ℂ) * c) +
        fderiv ℝ F M (((1 - y ^ 2 : ℝ) : ℂ) * (2 * M * c))) =
      ((1 - y ^ 2 : ℝ) : ℂ) ^ 2 * (-(lam * F M) / (y : ℂ) ^ 2 -
          (B (Complex.I * c) (Complex.I * c) +
            fderiv ℝ F M (Complex.I * (2 * Complex.I * Real.sin θ / orbitDen θ y ^ 3)))) +
        2 * y * ((1 - y ^ 2 : ℝ) : ℂ) * fderiv ℝ F M (Complex.I * c) := by
  intro F M c B
  have hM : 0 < M.im := orbit_im_pos θ hy
  have htr := bilinear_conformal_trace B c
  have hlap := hessian_trace hG heig hM
  have hq := orbitConf_normSq_div_im_sq θ hy
  have hvec := orbit_vector_identity θ hy
  rw [bilinear_real_mul]
  have hBcc : B c c = -(lam * F M) / (y : ℂ) ^ 2 - B (Complex.I * c) (Complex.I * c) := by
    have hMim : (M.im : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hM.ne')
    have hyy : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hy.ne')
    have hq' : (Complex.normSq c : ℂ) = (M.im : ℂ) ^ 2 / (y : ℂ) ^ 2 := by
      have := hq
      rw [div_eq_iff (pow_ne_zero 2 hM.ne')] at this
      rw [this]
      push_cast
      field_simp
    have hM0 : (M.im : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have hsimp : (M.im : ℂ) ^ 2 / (y : ℂ) ^ 2 * (-(lam * F M) / (M.im : ℂ) ^ 2) =
        -(lam * F M) / (y : ℂ) ^ 2 := by
      field_simp
    rw [hlap, hq', hsimp] at htr
    linear_combination htr
  rw [hBcc]
  have hlin : fderiv ℝ F M (((1 - y ^ 2 : ℝ) : ℂ) * (2 * M * c)) =
      ((1 - y ^ 2 : ℝ) : ℂ) * fderiv ℝ F M (2 * M * c) := clm_real_mul _ _ _
  have hvec' : 2 * M * c = 2 * y * Complex.I * c -
      ((1 - y ^ 2 : ℝ) : ℂ) * (-2 * Real.sin θ / orbitDen θ y ^ 3) := by
    rw [← hvec]; ring
  have hsin : Complex.I * (2 * Complex.I * Real.sin θ / orbitDen θ y ^ 3) =
      -2 * Real.sin θ / orbitDen θ y ^ 3 := by
    rw [← mul_div_assoc, ← mul_assoc, ← mul_assoc, mul_comm Complex.I 2, mul_assoc 2,
      Complex.I_mul_I]
    ring
  rw [hlin, hvec', hsin]
  have e1 : fderiv ℝ F M (2 * y * Complex.I * c -
      ((1 - y ^ 2 : ℝ) : ℂ) * (-2 * Real.sin θ / orbitDen θ y ^ 3)) =
      ((2 * y : ℝ) : ℂ) * fderiv ℝ F M (Complex.I * c) -
        ((1 - y ^ 2 : ℝ) : ℂ) * fderiv ℝ F M (-2 * Real.sin θ / orbitDen θ y ^ 3) := by
    rw [map_sub, ← clm_real_mul, ← clm_real_mul]
    congr 2
    push_cast
    ring
  rw [e1]
  push_cast
  ring

end eigen

/-! ### Differentiation under the rotation integral -/

/-- Differentiate a full-period θ-integral in the height parameter, given joint continuity of the
height derivative on `ℝ × (0,∞)`. -/
theorem hasDerivAt_theta_integral {Φ Ψ : ℝ → ℝ → ℂ} {y₀ : ℝ} (hy₀ : 0 < y₀)
    (hΦ : ∀ y, 0 < y → Continuous fun θ => Φ θ y)
    (hΨ : ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 p.2) (univ ×ˢ Ioi 0))
    (hd : ∀ θ y, 0 < y → HasDerivAt (fun t => Φ θ t) (Ψ θ y) y) :
    HasDerivAt (fun y => ∫ θ in (0 : ℝ)..2 * Real.pi, Φ θ y)
      (∫ θ in (0 : ℝ)..2 * Real.pi, Ψ θ y₀) y₀ := by
  set K : Set (ℝ × ℝ) := Icc 0 (2 * Real.pi) ×ˢ Icc (y₀ / 2) (2 * y₀)
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hKsub : K ⊆ univ ×ˢ Ioi 0 := fun p hp =>
    ⟨trivial, lt_of_lt_of_le (by linarith) hp.2.1⟩
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hΨ.mono hKsub)
  have hs : Ioo (y₀ / 2) (2 * y₀) ∈ 𝓝 y₀ := Ioo_mem_nhds (by linarith) (by linarith)
  have hΨ0 : Continuous fun θ => Ψ θ y₀ := by
    have : Continuous fun θ : ℝ => ((θ, y₀) : ℝ × ℝ) := continuous_id.prodMk continuous_const
    exact hΨ.comp_continuous this (fun θ => ⟨trivial, hy₀⟩)
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 2 * Real.pi) (bound := fun _ => C)
    (F := fun y θ => Φ θ y) (F' := fun y θ => Ψ θ y) (x₀ := y₀) hs
    (by
      filter_upwards [Ioi_mem_nhds hy₀] with y hy
      exact (hΦ y hy).aestronglyMeasurable)
    ((hΦ y₀ hy₀).intervalIntegrable _ _)
    hΨ0.aestronglyMeasurable
    (by
      filter_upwards with θ hθ y hy
      have hθ' : θ ∈ Icc 0 (2 * Real.pi) := by
        rw [Set.uIoc_of_le (by positivity)] at hθ
        exact ⟨hθ.1.le, hθ.2⟩
      exact hC (θ, y) ⟨hθ', hy.1.le, hy.2.le⟩)
    intervalIntegrable_const
    (by
      filter_upwards with θ _ y hy
      exact hd θ y (lt_trans (by linarith) hy.1))
  exact h.2

/-! ### Continuity and periodicity of the orbit chart -/

theorem orbitNum_continuous : Continuous fun p : ℝ × ℝ => orbitNum p.1 p.2 := by
  unfold orbitNum; fun_prop

theorem orbitDen_continuous : Continuous fun p : ℝ × ℝ => orbitDen p.1 p.2 := by
  unfold orbitDen; fun_prop

theorem orbit_continuousOn : ContinuousOn (fun p : ℝ × ℝ => orbit p.1 p.2) (univ ×ˢ Ioi 0) :=
  orbitNum_continuous.continuousOn.div orbitDen_continuous.continuousOn
    (fun p hp => orbitDen_ne_zero p.1 hp.2)

theorem orbitConf_continuousOn :
    ContinuousOn (fun p : ℝ × ℝ => orbitConf p.1 p.2) (univ ×ˢ Ioi 0) := by
  unfold orbitConf
  exact continuousOn_const.div (orbitDen_continuous.continuousOn.pow 2)
    (fun p hp => pow_ne_zero 2 (orbitDen_ne_zero p.1 hp.2))

theorem orbit_mapsTo : MapsTo (fun p : ℝ × ℝ => orbit p.1 p.2) (univ ×ˢ Ioi 0)
    {z : ℂ | 0 < z.im} := fun p hp => orbit_im_pos p.1 hp.2

theorem orbitNum_periodic (θ y : ℝ) : orbitNum (θ + 2 * Real.pi) y = orbitNum θ y := by
  simp [orbitNum, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem orbitDen_periodic (θ y : ℝ) : orbitDen (θ + 2 * Real.pi) y = orbitDen θ y := by
  simp [orbitDen, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem orbit_periodic (θ y : ℝ) : orbit (θ + 2 * Real.pi) y = orbit θ y := by
  simp [orbit, orbitNum_periodic, orbitDen_periodic]

theorem orbitConf_periodic (θ y : ℝ) : orbitConf (θ + 2 * Real.pi) y = orbitConf θ y := by
  simp [orbitConf, orbitDen_periodic]

/-! ### The averaged equation -/

section average

variable {G : ℍ → ℂ} (hG : IsRealSmoothUpperHalfPlane G)

/-- Rotation average of `G` on the circle through `iy`. -/
def rotAverage (G : ℍ → ℂ) (y : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, (G ∘ ofComplex) (orbit θ y)

/-- First height derivative of `G` along the orbit chart. -/
def dY (G : ℍ → ℂ) (θ y : ℝ) : ℂ :=
  fderiv ℝ (G ∘ ofComplex) (orbit θ y) (Complex.I * orbitConf θ y)

/-- Second height derivative of `G` along the orbit chart. -/
def dYY (G : ℍ → ℂ) (θ y : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ (G ∘ ofComplex)) (orbit θ y) (Complex.I * orbitConf θ y)
      (Complex.I * orbitConf θ y) +
    fderiv ℝ (G ∘ ofComplex) (orbit θ y)
      (Complex.I * (2 * Complex.I * Real.sin θ / orbitDen θ y ^ 3))

/-- First angular derivative of `G` along the orbit chart. -/
def dT (G : ℍ → ℂ) (θ y : ℝ) : ℂ :=
  fderiv ℝ (G ∘ ofComplex) (orbit θ y) (((1 - y ^ 2 : ℝ) : ℂ) * orbitConf θ y)

/-- Second angular derivative of `G` along the orbit chart. -/
def dTT (G : ℍ → ℂ) (θ y : ℝ) : ℂ :=
  fderiv ℝ (fderiv ℝ (G ∘ ofComplex)) (orbit θ y) (((1 - y ^ 2 : ℝ) : ℂ) * orbitConf θ y)
      (((1 - y ^ 2 : ℝ) : ℂ) * orbitConf θ y) +
    fderiv ℝ (G ∘ ofComplex) (orbit θ y)
      (((1 - y ^ 2 : ℝ) : ℂ) * (2 * orbit θ y * orbitConf θ y))

include hG in
theorem fderiv_continuousOn :
    ContinuousOn (fderiv ℝ (G ∘ ofComplex)) {z : ℂ | 0 < z.im} :=
  (hG.fderiv_of_isOpen isOpen_upperHalfPlaneSet (m := 1) (by norm_num)).continuousOn

include hG in
theorem fderiv2_continuousOn :
    ContinuousOn (fderiv ℝ (fderiv ℝ (G ∘ ofComplex))) {z : ℂ | 0 < z.im} :=
  ((hG.fderiv_of_isOpen isOpen_upperHalfPlaneSet (m := 1) (by norm_num)).fderiv_of_isOpen
    isOpen_upperHalfPlaneSet (m := 0) (by norm_num)).continuousOn

include hG in
theorem hasDerivAt_y (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => (G ∘ ofComplex) (orbit θ t)) (dY G θ y) y := by
  have hF := chart_contDiffAt hG (orbit_im_pos θ hy)
  exact (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt y (hasDerivAt_orbit_y θ hy)

include hG in
theorem hasDerivAt_dY (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => dY G θ t) (dYY G θ y) y := by
  have hF := chart_contDiffAt hG (orbit_im_pos θ hy)
  exact curve_second hF (hasDerivAt_orbit_y θ hy) ((hasDerivAt_orbitConf_y θ hy).const_mul _)

include hG in
theorem hasDerivAt_θ (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => (G ∘ ofComplex) (orbit t y)) (dT G θ y) θ := by
  have hF := chart_contDiffAt hG (orbit_im_pos θ hy)
  exact (hF.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_orbit_θ θ hy)

include hG in
theorem hasDerivAt_dT (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => dT G t y) (dTT G θ y) θ := by
  have hF := chart_contDiffAt hG (orbit_im_pos θ hy)
  exact curve_second hF (hasDerivAt_orbit_θ θ hy) ((hasDerivAt_orbitConf_θ θ hy).const_mul _)

include hG in
theorem dY_continuousOn : ContinuousOn (fun p : ℝ × ℝ => dY G p.1 p.2) (univ ×ˢ Ioi 0) :=
  ((fderiv_continuousOn hG).comp orbit_continuousOn orbit_mapsTo).clm_apply
    (continuousOn_const.mul orbitConf_continuousOn)

include hG in
theorem dYY_continuousOn : ContinuousOn (fun p : ℝ × ℝ => dYY G p.1 p.2) (univ ×ˢ Ioi 0) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => Complex.I * orbitConf p.1 p.2) (univ ×ˢ Ioi 0) :=
    continuousOn_const.mul orbitConf_continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ =>
      Complex.I * (2 * Complex.I * Real.sin p.1 / orbitDen p.1 p.2 ^ 3)) (univ ×ˢ Ioi 0) := by
    apply continuousOn_const.mul
    apply ContinuousOn.div (by fun_prop) (orbitDen_continuous.continuousOn.pow 3)
    exact fun p hp => pow_ne_zero 3 (orbitDen_ne_zero p.1 hp.2)
  have hB := (fderiv2_continuousOn hG).comp orbit_continuousOn orbit_mapsTo
  have hD := (fderiv_continuousOn hG).comp orbit_continuousOn orbit_mapsTo
  unfold dYY
  exact ((hB.clm_apply hc).clm_apply hc).add (hD.clm_apply h3)

include hG in
theorem dTT_continuousOn : ContinuousOn (fun p : ℝ × ℝ => dTT G p.1 p.2) (univ ×ˢ Ioi 0) := by
  have hr : Continuous fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (by fun_prop)
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) * orbitConf p.1 p.2)
      (univ ×ˢ Ioi 0) := hr.continuousOn.mul orbitConf_continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => ((1 - p.2 ^ 2 : ℝ) : ℂ) *
      (2 * orbit p.1 p.2 * orbitConf p.1 p.2)) (univ ×ˢ Ioi 0) :=
    hr.continuousOn.mul ((continuousOn_const.mul orbit_continuousOn).mul orbitConf_continuousOn)
  have hB := (fderiv2_continuousOn hG).comp orbit_continuousOn orbit_mapsTo
  have hD := (fderiv_continuousOn hG).comp orbit_continuousOn orbit_mapsTo
  unfold dTT
  exact ((hB.clm_apply hc).clm_apply hc).add (hD.clm_apply h3)

theorem slice_continuous_of_continuousOn {Φ : ℝ → ℝ → ℂ}
    (h : ContinuousOn (fun p : ℝ × ℝ => Φ p.1 p.2) (univ ×ˢ Ioi 0)) {y : ℝ} (hy : 0 < y) :
    Continuous fun θ => Φ θ y := by
  have hin : Continuous fun θ : ℝ => ((θ, y) : ℝ × ℝ) := continuous_id.prodMk continuous_const
  exact h.comp_continuous hin (fun θ => ⟨trivial, hy⟩)

include hG in
theorem dTT_continuous {y : ℝ} (hy : 0 < y) : Continuous fun θ => dTT G θ y :=
  slice_continuous_of_continuousOn (dTT_continuousOn hG) hy

include hG in
theorem u_continuous {y : ℝ} (hy : 0 < y) : Continuous fun θ => (G ∘ ofComplex) (orbit θ y) :=
  continuous_iff_continuousAt.mpr fun θ => (hasDerivAt_θ hG θ hy).continuousAt

include hG in
/-- The full-period integral of the second angular derivative vanishes. -/
theorem integral_dTT {y : ℝ} (hy : 0 < y) : ∫ θ in (0 : ℝ)..2 * Real.pi, dTT G θ y = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_dT hG θ hy)
    ((dTT_continuous hG hy).intervalIntegrable _ _)]
  have h := orbit_periodic 0 y
  have h' := orbitConf_periodic 0 y
  simp only [zero_add] at h h'
  simp [dT, h, h']

include hG in
theorem hasDerivAt_rotAverage {y : ℝ} (hy : 0 < y) :
    HasDerivAt (rotAverage G) (∫ θ in (0 : ℝ)..2 * Real.pi, dY G θ y) y :=
  hasDerivAt_theta_integral hy (fun _ hy => u_continuous hG hy) (dY_continuousOn hG)
    (fun θ _ hy => hasDerivAt_y hG θ hy)

include hG in
theorem hasDerivAt_rotAverage' {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun t => ∫ θ in (0 : ℝ)..2 * Real.pi, dY G θ t)
      (∫ θ in (0 : ℝ)..2 * Real.pi, dYY G θ y) y :=
  hasDerivAt_theta_integral hy (fun _ hy => slice_continuous_of_continuousOn (dY_continuousOn hG) hy)
    (dYY_continuousOn hG) (fun θ _ hy => hasDerivAt_dY hG θ hy)

end average

/-! ### Uniqueness for the averaged radial equation -/

/-- Uniqueness for the averaged radial equation on `[1, ∞)`. -/
theorem radial_unique {A A1 A2 : ℝ → ℂ} {lam : ℂ}
    (hA : ∀ y, 0 < y → HasDerivAt A (A1 y) y)
    (hA1 : ∀ y, 0 < y → HasDerivAt A1 (A2 y) y)
    (hode : ∀ y, 0 < y → y ≠ 1 →
      ((1 - y ^ 2 : ℝ) : ℂ) * (-(lam * A y) / (y : ℂ) ^ 2 - A2 y) + 2 * y * A1 y = 0)
    (h1 : A 1 = 0) : ∀ y, 1 ≤ y → A y = 0 := by
  have hAc : ∀ y, 0 < y → ContinuousAt A y := fun y hy => (hA y hy).continuousAt
  have hA1c : ∀ y, 0 < y → ContinuousAt A1 y := fun y hy => (hA1 y hy).continuousAt
  have hAcOn : ∀ a b, 0 < a → ContinuousOn A (Icc a b) := fun a b ha x hx =>
    (hAc x (ha.trans_le hx.1)).continuousWithinAt
  -- weight and integral term
  let w : ℝ → ℂ := fun t => (((t ^ 2 - 1) / t ^ 2 : ℝ) : ℂ) * A t
  have hwc : ∀ t, 0 < t → ContinuousAt w t := by
    intro t ht
    have hr : ContinuousAt (fun t : ℝ => (t ^ 2 - 1) / t ^ 2) t :=
      ((continuous_pow 2).sub continuous_const).continuousAt.div (continuous_pow 2).continuousAt
        (pow_ne_zero 2 ht.ne')
    exact ((Complex.continuous_ofReal.continuousAt).comp hr).mul (hAc t ht)
  have hwi : ∀ a b, 0 < a → 0 < b → IntervalIntegrable w volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 : 0 < x := by
      rcases le_total a b with h | h
      · rw [uIcc_of_le h] at hx; exact ha.trans_le hx.1
      · rw [uIcc_of_ge h] at hx; exact hb.trans_le hx.1
    exact (hwc x hx0).continuousWithinAt
  let I : ℝ → ℂ := fun y => ∫ t in (1 : ℝ)..y, w t
  have hI : ∀ y, 0 < y → HasDerivAt I (w y) y := by
    intro y hy
    exact intervalIntegral.integral_hasDerivAt_right (hwi 1 y one_pos hy)
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun x hx => hwc x hx) y hy) (hwc y hy)
  let Q : ℝ → ℂ := fun y => (((y ^ 2 - 1 : ℝ)) : ℂ) * A1 y + lam * I y
  have hQd : ∀ y, 0 < y → y ≠ 1 → HasDerivAt Q 0 y := by
    intro y hy hy1
    have hp : HasDerivAt (fun t : ℝ => (((t ^ 2 - 1 : ℝ)) : ℂ)) (((2 * y : ℝ)) : ℂ) y := by
      have := ((hasDerivAt_pow 2 y).sub_const 1).ofReal_comp
      simpa using this
    have h := (hp.mul (hA1 y hy)).add ((hI y hy).const_mul lam)
    refine h.congr_deriv ?_
    have ho := hode y hy hy1
    simp only [w]
    push_cast at ho ⊢
    linear_combination ho
  have hQc : ∀ y, 0 < y → ContinuousAt Q y := by
    intro y hy
    exact ((Complex.continuous_ofReal.continuousAt).comp (by fun_prop)).mul (hA1c y hy) |>.add
      ((hI y hy).continuousAt.const_mul lam)
  have hQ1 : Q 1 = 0 := by simp [Q, I]
  -- Q vanishes on [1, ∞)
  have hQ : ∀ y, 1 ≤ y → Q y = 0 := by
    intro y hy
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h]; exact hQ1
    have hconst : ∀ a ∈ Ioo 1 y, Q a = Q y := by
      intro a ha
      have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment (f := Q) (f' := fun _ => 0)
        (a := a) (b := y) (C := 0)
        (fun x hx => (hQc x (lt_trans one_pos (ha.1.trans_le hx.1))).continuousWithinAt)
        (fun x hx => (hQd x (lt_trans one_pos (ha.1.trans_le hx.1))
          (ne_of_gt (ha.1.trans_le hx.1))).hasDerivWithinAt)
        (fun x _ => by simp) y ⟨ha.2.le, le_rfl⟩
      rw [zero_mul, norm_le_zero_iff, sub_eq_zero] at hseg
      exact hseg.symm
    have ht : Tendsto Q (𝓝[>] 1) (𝓝 (Q 1)) := (hQc 1 one_pos).tendsto.mono_left nhdsWithin_le_nhds
    have ht' : Tendsto Q (𝓝[>] 1) (𝓝 (Q y)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT h] with a ha
      exact (hconst a ha).symm
    rw [← tendsto_nhds_unique ht ht', hQ1]
  -- norm bounds and Gronwall
  let B : ℝ → ℝ := fun y => ∫ t in (1 : ℝ)..y, ‖A t‖
  have hBd : ∀ y, 0 < y → HasDerivAt B ‖A y‖ y := by
    intro y hy
    have hc : ∀ x, 0 < x → ContinuousAt (fun t => ‖A t‖) x := fun x hx => (hAc x hx).norm
    exact intervalIntegral.integral_hasDerivAt_right
      (ContinuousOn.intervalIntegrable (fun x hx => (hc x (by
        rcases le_total 1 y with h | h
        · rw [uIcc_of_le h] at hx; exact one_pos.trans_le hx.1
        · rw [uIcc_of_ge h] at hx; exact hy.trans_le hx.1)).continuousWithinAt))
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi (fun x hx => hc x hx) y hy) (hc y hy)
  have hB0 : ∀ y, 1 ≤ y → 0 ≤ B y := fun y hy =>
    intervalIntegral.integral_nonneg hy (fun _ _ => norm_nonneg _)
  have hBmono : ∀ s t, 1 ≤ s → s ≤ t → B s ≤ B t := by
    intro s t hs hst
    have hsplit := intervalIntegral.integral_add_adjacent_intervals (a := 1) (b := s) (c := t)
      (μ := volume) (f := fun t => ‖A t‖)
      (ContinuousOn.intervalIntegrable (fun x hx => (hAc x (by
        rw [uIcc_of_le hs] at hx; exact one_pos.trans_le hx.1)).norm.continuousWithinAt))
      (ContinuousOn.intervalIntegrable (fun x hx => (hAc x (by
        rw [uIcc_of_le hst] at hx; exact one_pos.trans_le (hs.trans hx.1))).norm.continuousWithinAt))
    have hnn : 0 ≤ ∫ x in s..t, ‖A x‖ := intervalIntegral.integral_nonneg hst (fun _ _ => norm_nonneg _)
    change B s ≤ B t
    simp only [B]
    linarith
  have hA1b : ∀ t, 1 < t → ‖A1 t‖ ≤ ‖lam‖ * B t := by
    intro t ht
    have hq := hQ t ht.le
    simp only [Q] at hq
    have hpos : 0 < t ^ 2 - 1 := by nlinarith
    have hA1eq : A1 t = -(lam * I t) / (((t ^ 2 - 1 : ℝ)) : ℂ) := by
      have hne : (((t ^ 2 - 1 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
      field_simp
      linear_combination hq
    rw [hA1eq, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpos, div_le_iff₀ hpos]
    have hIb : ‖I t‖ ≤ (t ^ 2 - 1) * B t := by
      calc ‖I t‖ ≤ ∫ s in (1 : ℝ)..t, ‖w s‖ :=
            intervalIntegral.norm_integral_le_integral_norm ht.le
        _ ≤ ∫ s in (1 : ℝ)..t, (t ^ 2 - 1) * ‖A s‖ := by
            apply intervalIntegral.integral_mono_on ht.le
            · exact ContinuousOn.intervalIntegrable (fun x hx => (hwc x (by
                rw [uIcc_of_le ht.le] at hx; exact one_pos.trans_le hx.1)).norm.continuousWithinAt)
            · exact ContinuousOn.intervalIntegrable (fun x hx => ((hAc x (by
                rw [uIcc_of_le ht.le] at hx; exact one_pos.trans_le hx.1)).norm.const_mul _).continuousWithinAt)
            · intro s hs
              simp only [w, norm_mul, Complex.norm_real, Real.norm_eq_abs]
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              have hs1 : 1 ≤ s := hs.1
              have hs0 : 0 < s := one_pos.trans_le hs1
              rw [abs_of_nonneg (div_nonneg (by nlinarith) (sq_nonneg _)), div_le_iff₀ (by positivity)]
              have e1 : s ^ 2 - 1 ≤ t ^ 2 - 1 := by nlinarith [hs.2]
              have e2 : 0 ≤ s ^ 2 - 1 := by nlinarith
              nlinarith [mul_nonneg (sub_nonneg.mpr e1) (sq_nonneg s), mul_nonneg e2 e2]
        _ = (t ^ 2 - 1) * B t := by rw [intervalIntegral.integral_const_mul]
    calc ‖lam‖ * ‖I t‖ ≤ ‖lam‖ * ((t ^ 2 - 1) * B t) := mul_le_mul_of_nonneg_left hIb (norm_nonneg _)
      _ = ‖lam‖ * B t * (t ^ 2 - 1) := by ring
  intro Y hY
  rcases eq_or_lt_of_le hY with h | h
  · rw [← h]; exact h1
  have hAb : ∀ y ∈ Icc 1 Y, ‖A y‖ ≤ ‖lam‖ * (Y - 1) * B y := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h' | h'
    · rw [← h', h1, norm_zero]; simp [B]
    have hseg := norm_image_sub_le_of_norm_deriv_right_le_segment (f := A) (f' := A1)
      (a := 1) (b := y) (C := ‖lam‖ * B y) (hAcOn 1 y one_pos)
      (fun x hx => (hA x (one_pos.trans_le hx.1)).hasDerivWithinAt)
      (by
        intro x hx
        rcases eq_or_lt_of_le hx.1 with hx1 | hx1
        · rw [← hx1]
          -- at x = 1 the bound follows by continuity from the right
          have hlim : Tendsto (fun t => ‖A1 t‖) (𝓝[>] 1) (𝓝 ‖A1 1‖) :=
            ((hA1c 1 one_pos).norm.tendsto).mono_left nhdsWithin_le_nhds
          have hlim2 : Tendsto (fun t => ‖lam‖ * B t) (𝓝[>] 1) (𝓝 (‖lam‖ * B 1)) :=
            (((hBd 1 one_pos).continuousAt.const_mul _).tendsto).mono_left nhdsWithin_le_nhds
          have hle : ‖A1 1‖ ≤ ‖lam‖ * B 1 := le_of_tendsto_of_tendsto hlim hlim2
            (by filter_upwards [self_mem_nhdsWithin] with t ht; exact hA1b t ht)
          exact hle.trans (mul_le_mul_of_nonneg_left (hBmono 1 y le_rfl hy.1) (norm_nonneg _))
        · exact (hA1b x hx1).trans (mul_le_mul_of_nonneg_left (hBmono x y hx.1 hx.2.le)
            (norm_nonneg _))) y ⟨hy.1, le_rfl⟩
    rw [h1, sub_zero] at hseg
    calc ‖A y‖ ≤ ‖lam‖ * B y * (y - 1) := hseg
      _ ≤ ‖lam‖ * B y * (Y - 1) :=
          mul_le_mul_of_nonneg_left (by linarith [hy.2]) (mul_nonneg (norm_nonneg _) (hB0 y hy.1))
      _ = ‖lam‖ * (Y - 1) * B y := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := B) (f' := fun y => ‖A y‖)
    (δ := 0) (K := ‖lam‖ * (Y - 1)) (ε := 0) (a := 1) (b := Y)
    (fun x hx => (hBd x (one_pos.trans_le hx.1)).continuousAt.continuousWithinAt)
    (fun x hx => (hBd x (one_pos.trans_le hx.1)).hasDerivWithinAt)
    (by simp [B])
    (by
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
        abs_of_nonneg (hB0 x hx.1), add_zero]
      exact hAb x ⟨hx.1, hx.2.le⟩)
  have hBY : ∀ y ∈ Icc 1 Y, B y = 0 := by
    intro y hy
    have := hgr y hy
    rw [gronwallBound_ε0_δ0, Real.norm_eq_abs] at this
    exact abs_nonpos_iff.mp this
  have := hAb Y ⟨hY, le_rfl⟩
  rw [hBY Y ⟨hY, le_rfl⟩, mul_zero] at this
  exact norm_le_zero_iff.mp this


/-! ### The averaged radial equation and the mean-value theorem -/

theorem orbit_one (θ : ℝ) : orbit θ 1 = Complex.I := by
  have hD : orbitDen θ 1 ≠ 0 := orbitDen_ne_zero θ one_pos
  rw [orbit, div_eq_iff hD]
  unfold orbitNum orbitDen
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem orbit_quarter (θ : ℝ) {y : ℝ} (hy : 0 < y) :
    orbit (θ + Real.pi / 2) y = orbit θ (1 / y) := by
  have h1 := orbitDen_ne_zero (θ + Real.pi / 2) hy
  have h2 := orbitDen_ne_zero θ (one_div_pos.mpr hy)
  rw [orbit, orbit, div_eq_div_iff h1 h2]
  unfold orbitNum orbitDen
  rw [Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

section eigenAverage

variable {G : ℍ → ℂ} (hG : IsRealSmoothUpperHalfPlane G) {lam : ℂ}
  (heig : ∀ z, positiveHyperbolicLaplacian G z = lam * G z)

include hG heig in
/-- The rotation average satisfies the radial equation off `y = 1`. -/
theorem rotAverage_ode {y : ℝ} (hy : 0 < y) (hy1 : y ≠ 1) :
    ((1 - y ^ 2 : ℝ) : ℂ) * (-(lam * rotAverage G y) / (y : ℂ) ^ 2 -
        ∫ θ in (0 : ℝ)..2 * Real.pi, dYY G θ y) +
      2 * y * ∫ θ in (0 : ℝ)..2 * Real.pi, dY G θ y = 0 := by
  have hpt : ∀ θ, dTT G θ y = (-(((1 - y ^ 2 : ℝ) : ℂ) ^ 2 * lam / (y : ℂ) ^ 2)) *
        (G ∘ ofComplex) (orbit θ y) + (-(((1 - y ^ 2 : ℝ) : ℂ) ^ 2)) * dYY G θ y +
      (2 * y * ((1 - y ^ 2 : ℝ) : ℂ)) * dY G θ y := by
    intro θ
    have h := orbit_identity hG heig θ hy
    simp only at h
    unfold dTT dYY dY
    rw [h]
    ring
  have hu := (u_continuous hG hy).intervalIntegrable (μ := volume) 0 (2 * Real.pi)
  have hyy := (slice_continuous_of_continuousOn (dYY_continuousOn hG) hy).intervalIntegrable
    (μ := volume) 0 (2 * Real.pi)
  have hyi := (slice_continuous_of_continuousOn (dY_continuousOn hG) hy).intervalIntegrable
    (μ := volume) 0 (2 * Real.pi)
  have hint := integral_dTT hG hy
  simp_rw [hpt] at hint
  rw [intervalIntegral.integral_add ((hu.const_mul _).add (hyy.const_mul _)) (hyi.const_mul _),
    intervalIntegral.integral_add (hu.const_mul _) (hyy.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hint
  have hne : ((1 - y ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : (1 - y ^ 2 : ℝ) ≠ 0 := by
      intro h0
      have : (y - 1) * (y + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h | h
      · exact hy1 (by linarith)
      · linarith
    exact_mod_cast this
  have hy2 : (y : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hy.ne')
  apply (mul_eq_zero.mp (show ((1 - y ^ 2 : ℝ) : ℂ) * (((1 - y ^ 2 : ℝ) : ℂ) *
      (-(lam * rotAverage G y) / (y : ℂ) ^ 2 - ∫ θ in (0 : ℝ)..2 * Real.pi, dYY G θ y) +
      2 * y * ∫ θ in (0 : ℝ)..2 * Real.pi, dY G θ y) = 0 by
    rw [← hint]; unfold rotAverage; ring)).resolve_left hne

omit hG in
theorem rotAverage_one : rotAverage G 1 = 2 * Real.pi * G UpperHalfPlane.I := by
  unfold rotAverage
  simp only [orbit_one]
  rw [intervalIntegral.integral_const]
  have : (G ∘ ofComplex) Complex.I = G UpperHalfPlane.I := by
    simp [Function.comp_apply, ofComplex_apply_of_im_pos (show 0 < Complex.I.im by simp)]
    rfl
  rw [this]
  simp

omit hG in
theorem rotAverage_inv {y : ℝ} (hy : 0 < y) : rotAverage G (1 / y) = rotAverage G y := by
  unfold rotAverage
  have hper : Function.Periodic (fun θ => (G ∘ ofComplex) (orbit θ y)) (2 * Real.pi) := by
    intro θ
    simp only [orbit_periodic]
  have hshift := intervalIntegral.integral_comp_add_right
    (fun θ => (G ∘ ofComplex) (orbit θ y)) (Real.pi / 2) (a := 0) (b := 2 * Real.pi)
  simp only [orbit_quarter _ hy] at hshift
  rw [hshift, zero_add]
  have := hper.intervalIntegral_add_eq (Real.pi / 2) 0
  rw [zero_add] at this
  rw [show 2 * Real.pi + Real.pi / 2 = Real.pi / 2 + 2 * Real.pi by ring, this]

end eigenAverage

/-- **Selberg mean-value theorem for rotation averages.** Two real-`C²` eigenfunctions of the
positive hyperbolic Laplacian with the same eigenvalue have proportional rotation averages about
`i`: the average of `G` is `G(i)/E(i)` times the average of `E`. -/
theorem rotAverage_eq_smul {G E : ℍ → ℂ} {lam : ℂ}
    (hG : IsRealSmoothUpperHalfPlane G) (hGe : ∀ z, positiveHyperbolicLaplacian G z = lam * G z)
    (hE : IsRealSmoothUpperHalfPlane E) (hEe : ∀ z, positiveHyperbolicLaplacian E z = lam * E z)
    (hEI : E UpperHalfPlane.I ≠ 0) {y : ℝ} (hy : 0 < y) :
    rotAverage G y = G UpperHalfPlane.I / E UpperHalfPlane.I * rotAverage E y := by
  set c := G UpperHalfPlane.I / E UpperHalfPlane.I
  let A : ℝ → ℂ := fun t => rotAverage G t - c * rotAverage E t
  let A1 : ℝ → ℂ := fun t => (∫ θ in (0 : ℝ)..2 * Real.pi, dY G θ t) -
    c * ∫ θ in (0 : ℝ)..2 * Real.pi, dY E θ t
  let A2 : ℝ → ℂ := fun t => (∫ θ in (0 : ℝ)..2 * Real.pi, dYY G θ t) -
    c * ∫ θ in (0 : ℝ)..2 * Real.pi, dYY E θ t
  have hA : ∀ t, 0 < t → HasDerivAt A (A1 t) t := fun t ht =>
    (hasDerivAt_rotAverage hG ht).sub ((hasDerivAt_rotAverage hE ht).const_mul c)
  have hA1 : ∀ t, 0 < t → HasDerivAt A1 (A2 t) t := fun t ht =>
    (hasDerivAt_rotAverage' hG ht).sub ((hasDerivAt_rotAverage' hE ht).const_mul c)
  have hode : ∀ t, 0 < t → t ≠ 1 →
      ((1 - t ^ 2 : ℝ) : ℂ) * (-(lam * A t) / (t : ℂ) ^ 2 - A2 t) + 2 * t * A1 t = 0 := by
    intro t ht ht1
    have h1 := rotAverage_ode hG hGe ht ht1
    have h2 := rotAverage_ode hE hEe ht ht1
    simp only [A, A1, A2]
    linear_combination h1 - c * h2
  have h1 : A 1 = 0 := by
    simp only [A, rotAverage_one (G := G), rotAverage_one (G := E), c]
    field_simp
    ring
  have hzero := radial_unique hA hA1 hode h1
  have hy' : A y = 0 := by
    rcases le_total 1 y with h | h
    · exact hzero y h
    · have hinv : 1 ≤ 1 / y := by rw [le_div_iff₀ hy]; linarith
      have := hzero (1 / y) hinv
      simp only [A, rotAverage_inv (G := G) hy, rotAverage_inv (G := E) hy] at this
      exact this
  simp only [A] at hy'
  exact sub_eq_zero.mp hy'

end
end GaloisForLFunctions.RHTower.HyperbolicRotationMean
