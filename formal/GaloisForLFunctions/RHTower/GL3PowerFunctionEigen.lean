import GaloisForLFunctions.RHTower.GL3ChartSmooth
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas


/-!
# Power functions are eigenfunctions of the invariant Laplacian

`Δ(y₁^α y₂^β) = (2α² − 2αβ + 2β² − 2α − 2β) · y₁^α y₂^β` (`lap_pw`). With `α = ν₁ + 2ν₂`,
`β = 2ν₁ + ν₂` the eigenvalue is `−2(3ν₁ + 3ν₂ − 3ν₁² − 3ν₁ν₂ − 3ν₂²)`, so the exponential-chart
Laplacian is `−2` times the Laplacian in Goldfeld's normalisation.

**Proof.** The power function is multiplicative for the Iwasawa group law (`pwR_mul`), so invariance
of `Δ` reduces the claim to the base point (`lap_pw`). There the Laplacian is the sum of second
derivatives along the nine Frobenius unit directions (`laplacian_eq_iteratedFDeriv_orthonormalBasis`,
`iteratedFDeriv_two_line`). Along `e_{aa}` the exponential is diagonal, and along `e_{ab}` (`a ≠ b`)
it is the hyperbolic rotation `exp(t(E_ab + E_ba))`, computed by diagonalising with a `π/4`-rotation
(`exp_Jmat`). In each case the chart point is an explicit point of `h³` (Gram identification,
`ofMat_eq_of_gram`), and the power function is `e^{βt}`, `e^{(α−β)t}`, `e^{−αt}`,
`cosh(t)^{α/2−β}`, `cosh(t)^{−(α+β)/2}` or `cosh(t)^{β/2−α}` (`pwR_line_ab`). Their second
derivatives at `0` are `k²` and `r` respectively.
-/

open Matrix Laplacian InnerProductSpace

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### Exponentials along the coordinate directions -/

theorem exp_diagonal_real (d : Fin 3 → ℝ) :
    NormedSpace.exp (Matrix.diagonal d) = Matrix.diagonal fun i => Real.exp (d i) := by
  rw [Matrix.exp_diagonal, Pi.exp_def]
  congr 1
  funext i
  rw [Real.exp_eq_exp_ℝ]

/-- `√2`. -/
noncomputable abbrev r2 : ℝ := Real.sqrt 2

theorem r2_mul_self : r2 * r2 = 2 := Real.mul_self_sqrt (by norm_num)

theorem r2_ne_zero : r2 ≠ 0 := by positivity

theorem r2_sq : r2 ^ 2 = 2 := by rw [sq]; exact r2_mul_self

/-- A rotation by `π/4` in a coordinate plane, composed with a reflection; it is symmetric and
squares to `1`. -/
noncomputable def rot (a b c : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i = c ∧ j = c then 1
    else if i = b ∧ j = b then -r2⁻¹
    else if (i = a ∨ i = b) ∧ (j = a ∨ j = b) then r2⁻¹ else 0

theorem rot_mul_self {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    rot a b c * rot a b c = 1 := by
  have h := r2_mul_self
  have hr := r2_ne_zero
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hac hbc <;>
    fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;> linarith

/-- `t(E_ab + E_ba)`. -/
def Jmat (a b : Fin 3) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then t else 0

/-- The hyperbolic rotation `exp(t(E_ab + E_ba))`. -/
noncomputable def Hmat (a b c : Fin 3) (t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j =>
    if i = c ∧ j = c then 1
    else if (i = a ∧ j = a) ∨ (i = b ∧ j = b) then Real.cosh t
    else if (i = a ∧ j = b) ∨ (i = b ∧ j = a) then Real.sinh t else 0

/-- **`exp(t(E_ab + E_ba))` is a hyperbolic rotation**, by diagonalising `E_ab + E_ba` with `rot`. -/
theorem exp_Jmat {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t : ℝ) :
    NormedSpace.exp (Jmat a b t) = Hmat a b c t := by
  have hQ := rot_mul_self hab hac hbc
  have hinv : (rot a b c)⁻¹ = rot a b c := Matrix.inv_eq_right_inv hQ
  have hU : IsUnit (rot a b c) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact IsUnit.of_mul_eq_one ((rot a b c).det) (by rw [← Matrix.det_mul, hQ, Matrix.det_one])
  have h := r2_mul_self
  have hr := r2_ne_zero
  set d : Fin 3 → ℝ := fun i => if i = a then t else if i = b then -t else 0
  have hconj : Jmat a b t = rot a b c * Matrix.diagonal d * (rot a b c)⁻¹ := by
    rw [hinv]
    ext i j
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hac hbc <;>
      fin_cases i <;> fin_cases j <;>
      simp [Jmat, rot, d, Matrix.mul_apply, Fin.sum_univ_three] <;> field_simp <;>
      first | linarith | (rw [r2_sq]; ring)
  rw [hconj, Matrix.exp_conj _ _ hU, exp_diagonal_real, hinv]
  ext i j
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp at hab hac hbc <;>
    fin_cases i <;> fin_cases j <;>
    simp [Hmat, rot, d, Matrix.mul_apply, Fin.sum_univ_three, Real.cosh_eq, Real.sinh_eq] <;>
    field_simp <;> first | linarith | (rw [r2_sq]; ring)

/-! ### The chart points along the coordinate directions -/

/-- The unit direction `e_{ab}` of the Frobenius space. -/
noncomputable def eDir (a b : Fin 3) : Dir := EuclideanSpace.single (a, b) 1

theorem symMat_smul_eDir (t : ℝ) (a b : Fin 3) :
    toMat (t • eDir a b) + (toMat (t • eDir a b))ᵀ =
      fun i j => (if i = a ∧ j = b then t else 0) + (if i = b ∧ j = a then t else 0) := by
  ext i j
  simp only [toMat, eDir, Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply,
    PiLp.smul_apply, PiLp.single_apply, Prod.mk.injEq, smul_eq_mul, mul_ite, mul_one, mul_zero]
  congr 1
  by_cases h1 : j = a <;> by_cases h2 : i = b <;> simp [h1, h2]

theorem symExp_diag (t : ℝ) (a : Fin 3) :
    symExp (t • eDir a a) = Matrix.diagonal fun i => Real.exp (if i = a then 2 * t else 0) := by
  rw [symExp, symMat_smul_eDir, ← exp_diagonal_real]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst hij; by_cases h : i = a <;> simp [h, Matrix.diagonal]; ring
  · have h' : ¬ (i = a ∧ j = a) := fun h => hij (h.1.trans h.2.symm)
    simp [Matrix.diagonal, hij, h']

theorem symExp_offdiag {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (t : ℝ) :
    symExp (t • eDir a b) = Hmat a b c t := by
  rw [symExp, symMat_smul_eDir, ← exp_Jmat hab hac hbc]
  congr 1
  ext i j
  simp only [Jmat]
  by_cases h1 : i = a ∧ j = b
  · simp [h1, hab, Ne.symm hab]
  · by_cases h2 : i = b ∧ j = a <;> simp [h1, h2, hab, Ne.symm hab]

theorem chart_one (F : H3 → ℂ) (v : Dir) : chart F 1 v = F (ofMat (symExp v)) := by
  simp [chart, map_one, one_smul]

theorem ofMat_eq_of_gram {M : Matrix (Fin 3) (Fin 3) ℝ} (w : H3) {c : ℝ} (hc : 0 < c)
    (h : M = c • w.gram) : ofMat M = w := by
  rw [h, ofMat_smul w.posDef_gram hc, ofMat_gram]

/-- The power function `y₁^α y₂^β`. -/
noncomputable def pwR (α β : ℝ) (z : H3) : ℝ := z.y1 ^ α * z.y2 ^ β

theorem cosh_rpow_mul (c : ℝ) (hc : 0 < c) (x y : ℝ) : c ^ x * c ^ y = c ^ (x + y) :=
  (Real.rpow_add hc x y).symm

theorem sqrt_rpow (c : ℝ) (hc : 0 ≤ c) (x : ℝ) : (√c) ^ x = c ^ (x / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hc]; ring_nf

theorem inv_rpow' (c : ℝ) (hc : 0 < c) (x : ℝ) : c⁻¹ ^ x = c ^ (-x) := by
  rw [Real.inv_rpow hc.le, Real.rpow_neg hc.le]

theorem exp_sq (x : ℝ) : Real.exp x ^ 2 = Real.exp (2 * x) := by
  rw [sq, ← Real.exp_add]; ring_nf

theorem pwR_line_00 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 0 0))) = Real.exp (β * t) := by
  have hw : ofMat (symExp (t • eDir 0 0)) = ⟨0, 0, 0, 1, Real.exp t, one_pos, Real.exp_pos t⟩ := by
    refine ofMat_eq_of_gram _ one_pos ?_
    rw [symExp_diag, one_smul, gram_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, exp_sq]
  rw [hw, pwR]
  simp only [Real.one_rpow, one_mul, ← Real.exp_mul]; ring_nf

theorem pwR_line_11 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 1 1))) = Real.exp ((α - β) * t) := by
  have hw : ofMat (symExp (t • eDir 1 1)) =
      ⟨0, 0, 0, Real.exp t, Real.exp (-t), Real.exp_pos t, Real.exp_pos _⟩ := by
    refine ofMat_eq_of_gram _ one_pos ?_
    rw [symExp_diag, one_smul, gram_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, exp_sq, mul_pow]
    all_goals rw [← Real.exp_add]; ring_nf; simp
  rw [hw, pwR, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]; ring_nf

theorem pwR_line_22 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 2 2))) = Real.exp (-α * t) := by
  have hw : ofMat (symExp (t • eDir 2 2)) =
      ⟨0, 0, 0, Real.exp (-t), 1, Real.exp_pos _, one_pos⟩ := by
    refine ofMat_eq_of_gram _ (Real.exp_pos (2 * t)) ?_
    rw [symExp_diag, gram_apply]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, exp_sq]
    all_goals rw [← Real.exp_add]; ring_nf; simp
  rw [hw, pwR, ← Real.exp_mul, Real.one_rpow, mul_one]; ring_nf

theorem Hmat_swap (a b c : Fin 3) (t : ℝ) : Hmat a b c t = Hmat b a c t := by
  ext i j
  simp only [Hmat, or_comm]

theorem pwR_line_01 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 0 1))) = Real.cosh t ^ (α / 2 - β) := by
  have hc := Real.cosh_pos t
  have hsq := Real.cosh_sq t
  have hw : ofMat (symExp (t • eDir 0 1)) =
      ⟨0, Real.sinh t / Real.cosh t, 0, √(Real.cosh t), (Real.cosh t)⁻¹,
        Real.sqrt_pos.2 hc, inv_pos.2 hc⟩ := by
    refine ofMat_eq_of_gram _ one_pos ?_
    rw [symExp_offdiag (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) t, one_smul,
      gram_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hmat, mul_pow, Real.sq_sqrt hc.le]
    all_goals first | (field_simp; done) | (field_simp; linear_combination hsq)
  rw [hw, pwR]
  simp only [sqrt_rpow _ hc.le, inv_rpow' _ hc, cosh_rpow_mul _ hc]
  ring_nf

theorem pwR_line_10 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 1 0))) = Real.cosh t ^ (α / 2 - β) := by
  rw [← pwR_line_01, symExp_offdiag (a := 1) (b := 0) (c := 2) (by decide) (by decide) (by decide) t,
    symExp_offdiag (a := 0) (b := 1) (c := 2) (by decide) (by decide) (by decide) t, Hmat_swap]

theorem pwR_line_02 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 0 2))) = Real.cosh t ^ (-(α + β) / 2) := by
  have hc := Real.cosh_pos t
  have hsq := Real.cosh_sq t
  have hs := Real.sqrt_pos.2 hc
  have hw : ofMat (symExp (t • eDir 0 2)) =
      ⟨0, 0, Real.sinh t / Real.cosh t, (√(Real.cosh t))⁻¹, (√(Real.cosh t))⁻¹,
        inv_pos.2 hs, inv_pos.2 hs⟩ := by
    refine ofMat_eq_of_gram _ hc ?_
    rw [symExp_offdiag (a := 0) (b := 2) (c := 1) (by decide) (by decide) (by decide) t, gram_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hmat, mul_pow, inv_pow, Real.sq_sqrt hc.le]
    all_goals first | (field_simp; done) | (field_simp; linear_combination hsq)
  rw [hw, pwR]
  simp only [inv_rpow' _ hs, sqrt_rpow _ hc.le, cosh_rpow_mul _ hc]
  ring_nf

theorem pwR_line_20 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 2 0))) = Real.cosh t ^ (-(α + β) / 2) := by
  rw [← pwR_line_02, symExp_offdiag (a := 2) (b := 0) (c := 1) (by decide) (by decide) (by decide) t,
    symExp_offdiag (a := 0) (b := 2) (c := 1) (by decide) (by decide) (by decide) t, Hmat_swap]

theorem pwR_line_12 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 1 2))) = Real.cosh t ^ (β / 2 - α) := by
  have hc := Real.cosh_pos t
  have hsq := Real.cosh_sq t
  have hw : ofMat (symExp (t • eDir 1 2)) =
      ⟨Real.sinh t / Real.cosh t, 0, 0, (Real.cosh t)⁻¹, √(Real.cosh t),
        inv_pos.2 hc, Real.sqrt_pos.2 hc⟩ := by
    refine ofMat_eq_of_gram _ hc ?_
    rw [symExp_offdiag (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide) t, gram_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Hmat, mul_pow, inv_pow, Real.sq_sqrt hc.le]
    all_goals first | (field_simp; done) | (field_simp; linear_combination hsq)
  rw [hw, pwR]
  simp only [inv_rpow' _ hc, sqrt_rpow _ hc.le, cosh_rpow_mul _ hc]
  ring_nf

theorem pwR_line_21 (α β t : ℝ) :
    pwR α β (ofMat (symExp (t • eDir 2 1))) = Real.cosh t ^ (β / 2 - α) := by
  rw [← pwR_line_12, symExp_offdiag (a := 2) (b := 1) (c := 0) (by decide) (by decide) (by decide) t,
    symExp_offdiag (a := 1) (b := 2) (c := 0) (by decide) (by decide) (by decide) t, Hmat_swap]

/-! ### Second derivatives along the lines -/

theorem iteratedDeriv_two_exp_mul (k : ℝ) :
    iteratedDeriv 2 (fun t => Real.exp (k * t)) 0 = k ^ 2 := by
  have h1 : deriv (fun t => Real.exp (k * t)) = fun t => k * Real.exp (k * t) := by
    funext t
    have := ((hasDerivAt_id t).const_mul k).exp
    simp only [id, mul_one] at this
    rw [this.deriv]; ring
  have h2 : deriv (fun t => k * Real.exp (k * t)) 0 = k ^ 2 := by
    have := (((hasDerivAt_id (0 : ℝ)).const_mul k).exp).const_mul k
    simp only [id, mul_one, mul_zero, Real.exp_zero] at this
    rw [this.deriv]; ring
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]

theorem iteratedDeriv_two_cosh_rpow (r : ℝ) :
    iteratedDeriv 2 (fun t => Real.cosh t ^ r) 0 = r := by
  have h1 : deriv (fun t => Real.cosh t ^ r) =
      fun t => r * Real.cosh t ^ (r - 1) * Real.sinh t := by
    funext t
    have := (Real.hasDerivAt_cosh t).rpow_const (p := r) (Or.inl (Real.cosh_pos t).ne')
    rw [this.deriv]; ring
  have h2 : deriv (fun t => r * Real.cosh t ^ (r - 1) * Real.sinh t) 0 = r := by
    have hc : HasDerivAt (fun t => Real.cosh t ^ (r - 1))
        ((r - 1) * Real.cosh 0 ^ (r - 1 - 1) * Real.sinh 0) 0 := by
      have := (Real.hasDerivAt_cosh 0).rpow_const (p := r - 1) (Or.inl (Real.cosh_pos 0).ne')
      convert this using 1; ring
    have := ((hc.const_mul r).mul (Real.hasDerivAt_sinh 0))
    rw [show (fun t => r * Real.cosh t ^ (r - 1) * Real.sinh t) =
      (fun y => r * Real.cosh y ^ (r - 1)) * Real.sinh from rfl, this.deriv]
    simp
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1, h2]

/-- The second derivative of a smooth function along a line. -/
theorem iteratedFDeriv_two_line {φ : Dir → ℂ} (hφ : ContDiff ℝ ⊤ φ) (v : Dir) :
    iteratedFDeriv ℝ 2 φ 0 ![v, v] = iteratedDeriv 2 (fun t : ℝ => φ (t • v)) 0 := by
  set L : ℝ →L[ℝ] Dir := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  have hL : (fun t : ℝ => φ (t • v)) = φ ∘ L := by
    funext t; simp [L]
  rw [hL, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hφ 0 (by exact_mod_cast le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  congr 1
  funext j
  fin_cases j <;> simp [L]

/-- A real second derivative cast to `ℂ`. -/
theorem iteratedDeriv_two_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (x : ℝ) :
    iteratedDeriv 2 (fun t => (f t : ℂ)) x = ((iteratedDeriv 2 f x : ℝ) : ℂ) := by
  have e : (fun t => (f t : ℂ)) = Complex.ofRealCLM ∘ f := rfl
  rw [e, iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_left _ hf.contDiffAt (by exact_mod_cast le_top)]
  rfl

/-- The power function `y₁^α y₂^β` as a complex function. -/
noncomputable def pw (α β : ℝ) (z : H3) : ℂ := (pwR α β z : ℂ)

theorem isSmooth_pw (α β : ℝ) : IsSmooth (pw α β) := by
  have h : ContDiffOn ℝ ⊤ (fun p : Fin 5 → ℝ => ((p 3 ^ α * p 4 ^ β : ℝ) : ℂ)) dom := by
    refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
    exact ((contDiff_apply ℝ ℝ 3).contDiffOn.rpow_const_of_ne fun p hp => hp.1.ne').mul
      ((contDiff_apply ℝ ℝ 4).contDiffOn.rpow_const_of_ne fun p hp => hp.2.ne')
  refine h.congr fun p hp => ?_
  simp [pw, pwR, ofCoords_eq hp]

theorem pwR_mul (α β : ℝ) (z w : H3) : pwR α β (z * w) = pwR α β z * pwR α β w := by
  simp only [pwR, mul_y1, mul_y2, Real.mul_rpow z.y1_pos.le w.y1_pos.le,
    Real.mul_rpow z.y2_pos.le w.y2_pos.le]
  ring

theorem chart_pw_one_line (α β : ℝ) (a b : Fin 3) (t : ℝ) :
    chart (pw α β) 1 (t • eDir a b) = (pwR α β (ofMat (symExp (t • eDir a b))) : ℂ) := by
  rw [chart_one]; rfl

theorem line_term (α β : ℝ) (a b : Fin 3) {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f)
    (hfun : ∀ t, pwR α β (ofMat (symExp (t • eDir a b))) = f t) :
    iteratedFDeriv ℝ 2 (chart (pw α β) 1) 0 ![EuclideanSpace.single (a, b) 1,
      EuclideanSpace.single (a, b) 1] = ((iteratedDeriv 2 f 0 : ℝ) : ℂ) := by
  rw [show EuclideanSpace.single (a, b) (1 : ℝ) = eDir a b from rfl,
    iteratedFDeriv_two_line (contDiff_chart (isSmooth_pw α β) 1)]
  simp only [chart_pw_one_line, hfun]
  exact iteratedDeriv_two_ofReal hf 0

theorem contDiff_exp_mul (k : ℝ) : ContDiff ℝ ⊤ fun t => Real.exp (k * t) :=
  Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)

theorem contDiff_cosh_rpow (r : ℝ) : ContDiff ℝ ⊤ fun t => Real.cosh t ^ r :=
  Real.contDiff_cosh.rpow_const_of_ne fun t => (Real.cosh_pos t).ne'

/-- **The Laplacian of the power function at the base point.** -/
theorem lap_pw_one (α β : ℝ) :
    lap (pw α β) 1 = ((2 * α ^ 2 - 2 * α * β + 2 * β ^ 2 - 2 * α - 2 * β : ℝ) : ℂ) := by
  rw [lap, laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 3 × Fin 3) ℝ)]
  simp only [EuclideanSpace.basisFun_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three]
  rw [line_term α β 0 0 (contDiff_exp_mul β) (pwR_line_00 α β),
    line_term α β 0 1 (contDiff_cosh_rpow _) (pwR_line_01 α β),
    line_term α β 0 2 (contDiff_cosh_rpow _) (pwR_line_02 α β),
    line_term α β 1 0 (contDiff_cosh_rpow _) (pwR_line_10 α β),
    line_term α β 1 1 (contDiff_exp_mul (α - β)) (pwR_line_11 α β),
    line_term α β 1 2 (contDiff_cosh_rpow _) (pwR_line_12 α β),
    line_term α β 2 0 (contDiff_cosh_rpow _) (pwR_line_20 α β),
    line_term α β 2 1 (contDiff_cosh_rpow _) (pwR_line_21 α β),
    line_term α β 2 2 (contDiff_exp_mul (-α)) (pwR_line_22 α β)]
  simp only [iteratedDeriv_two_exp_mul, iteratedDeriv_two_cosh_rpow]
  push_cast
  ring

/-- **Power functions are eigenfunctions of the Laplacian**:
`Δ(y₁^α y₂^β) = (2α² − 2αβ + 2β² − 2α − 2β) · y₁^α y₂^β`. -/
theorem lap_pw (α β : ℝ) (z : H3) :
    lap (pw α β) z = ((2 * α ^ 2 - 2 * α * β + 2 * β ^ 2 - 2 * α - 2 * β : ℝ) : ℂ) * pw α β z := by
  have h := lap_comp_smul (pw α β) (toGL z) 1
  rw [toGL_smul_one] at h
  rw [← h]
  have e : (fun w => pw α β (toGL z • w)) = fun w => pw α β z * pw α β w := by
    funext w
    simp only [pw, toGL_smul, pwR_mul]
    push_cast; ring
  have hc : chart (fun w => pw α β z * pw α β w) 1 = (pw α β z) • chart (pw α β) 1 := by
    funext v; simp [chart, smul_eq_mul]
  rw [e, lap, hc, laplacian_smul _ ((contDiff_chart (isSmooth_pw α β) 1).contDiffAt.of_le
    (by exact_mod_cast le_top)), smul_eq_mul, ← lap, lap_pw_one]
  ring

end H3
end GaloisForLFunctions.RHTower.GL3
