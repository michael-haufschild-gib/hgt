import GaloisForLFunctions.AdelicKreinGeometry.TheSignatureOfASeparableAssembly
import GaloisForLFunctions.ArithmeticPositiveDuality.AContinuousArchimedeanSpectrumIsSeenByTheSuccessor

/-!
# The pole is a Krein state of the affine group

The maps `x ↦ ax + b`, `a > 0`, form the Borel subgroup of `SL(2, ℝ) ≅ SU(1,1)`:
`(a, b) ↦ [[a^{1/2}, b a^{−1/2}], [0, a^{−1/2}]]`. `SL(2, ℝ)` preserves the indefinite Hermitian form
`h(x, y) = i(x̄₀y₁ − x̄₁y₀)` of signature `(1, 1)` on `ℂ²`. Its coefficient at `v = (1, −i)` is

  `φ_pole(x ↦ ax + b) = a^{1/2} + a^{−1/2} − i b a^{−1/2}`.

* **Coefficient identity** (`poleState_inv_mul`): `φ_pole(g⁻¹h) = h(w_g, w_h)` with
  `w_g = (a^{1/2} − i b a^{−1/2}, −i a^{−1/2})`.
* **Exactly one negative square** (`negIndex_poleState`): every Gram matrix is `Wᴴ h W` for the
  matrix `W` of columns `w_g`, and `h` is nonnegative on the line `x₀ = i x₁`.
* **Two actions in one state** (`poleState_dilation`, `poleState_translation`,
  `poleState_conformal`): on the dilations `φ_pole` is the pole pair `u^{1/2} + u^{−1/2}`, the boost of
  the pole plane in the Hecke normalization; on the translations it is `2 − ib`, and the dilation
  `x ↦ ux` multiplies its successor part by the conformal factor `u`.

So the pole of the Weil kernel is a Pontryagin state of the whole affine group, at index one, with a
nontrivial successor. The critical part of Weil's correlation carries only a blind successor (APD),
and no Hecke-supported part carries one at finite index; the pole is the hyperbolic pair through
which the successor and the dilations meet.
-/

open Complex Finset
open scoped ComplexConjugate Matrix
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.ArithmeticPositiveDuality

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The slope of a map of positive slope, as a real. -/
def posSlope (g : posAffine) : ℝ := (affSlope (g : AffineGroupQ) : ℝ)

theorem posSlope_pos (g : posAffine) : 0 < posSlope g := by
  have : (0 : ℚ) < affSlope (g : AffineGroupQ) := g.2
  show (0 : ℝ) < ((affSlope (g : AffineGroupQ) : ℚ) : ℝ)
  exact_mod_cast this

/-- The shift of a map, as a real. -/
def posShift (g : posAffine) : ℝ := (affShift (g : AffineGroupQ) : ℝ)

/-- **The pole state** `a^{1/2} + a^{−1/2} − i b a^{−1/2}`. -/
def poleState (g : posAffine) : ℂ :=
  ((Real.sqrt (posSlope g) + 1 / Real.sqrt (posSlope g) : ℝ) : ℂ) -
    I * ((posShift g / Real.sqrt (posSlope g) : ℝ) : ℂ)

/-- The first coordinate of `w_g = ρ(g)(1, −i)`. -/
def poleVec₀ (g : posAffine) : ℂ :=
  ((Real.sqrt (posSlope g) : ℝ) : ℂ) - I * ((posShift g / Real.sqrt (posSlope g) : ℝ) : ℂ)

/-- The second coordinate of `w_g`. -/
def poleVec₁ (g : posAffine) : ℂ := -I * ((1 / Real.sqrt (posSlope g) : ℝ) : ℂ)

/-- The form `h(x, y) = i(x̄₀y₁ − x̄₁y₀)` of signature `(1, 1)`. -/
def kreinForm (x₀ x₁ y₀ y₁ : ℂ) : ℂ := I * (conj x₀ * y₁ - conj x₁ * y₀)

theorem slope_inv_mul (g h : posAffine) :
    posSlope (g⁻¹ * h) = posSlope h / posSlope g := by
  simp only [posSlope, Subgroup.coe_mul, Subgroup.coe_inv, affSlope_mul, affSlope_inv]
  push_cast; ring

theorem shift_inv_mul (g h : posAffine) :
    posShift (g⁻¹ * h) = (posShift h - posShift g) / posSlope g := by
  simp only [posShift, posSlope, Subgroup.coe_mul, Subgroup.coe_inv, affShift_mul, affSlope_inv,
    affShift_inv]
  have : (affSlope (g : AffineGroupQ) : ℝ) ≠ 0 := (posSlope_pos g).ne'
  push_cast
  field_simp
  ring

/-- **The coefficient identity** `φ_pole(g⁻¹h) = h(w_g, w_h)`. -/
theorem poleState_inv_mul (g h : posAffine) :
    poleState (g⁻¹ * h) = kreinForm (poleVec₀ g) (poleVec₁ g) (poleVec₀ h) (poleVec₁ h) := by
  have ha := posSlope_pos g
  have ha' := posSlope_pos h
  obtain ⟨s, hs, hsg, hsq⟩ : ∃ s, 0 < s ∧ Real.sqrt (posSlope g) = s ∧ posSlope g = s ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr ha, rfl, (Real.sq_sqrt ha.le).symm⟩
  obtain ⟨s', hs', hsh, -⟩ : ∃ s', 0 < s' ∧ Real.sqrt (posSlope h) = s' ∧ posSlope h = s' ^ 2 :=
    ⟨_, Real.sqrt_pos.mpr ha', rfl, (Real.sq_sqrt ha'.le).symm⟩
  have hq : Real.sqrt (posSlope h / posSlope g) = s' / s := by
    rw [Real.sqrt_div' _ ha.le, hsg, hsh]
  simp only [poleState, poleVec₀, poleVec₁, kreinForm, slope_inv_mul, shift_inv_mul, hq, hsg, hsh]
  rw [hsq]
  generalize posShift g = b
  generalize posShift h = b'
  simp only [map_sub, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im] <;>
    field_simp <;> ring

/-- The form `h` is nonnegative on the line `x₀ = i x₁`. -/
theorem kreinForm_re_nonneg {x₀ x₁ : ℂ} (h : x₀ = I * x₁) : 0 ≤ (kreinForm x₀ x₁ x₀ x₁).re := by
  have e : kreinForm x₀ x₁ x₀ x₁ = 2 * (conj x₁ * x₁) := by
    rw [kreinForm, h, map_mul, Complex.conj_I]
    linear_combination (-2 * conj x₁ * x₁) * Complex.I_sq
  rw [e]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.re_ofNat,
    Complex.im_ofNat]
  nlinarith [sq_nonneg x₁.re, sq_nonneg x₁.im]

/-- The matrix of the form `h`. -/
def krein2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, I; -I, 0]

/-- The vectors `w_{z_a}` as the columns of a `2 × n` matrix. -/
def poleMat {n : ℕ} (z : Fin n → posAffine) : Matrix (Fin 2) (Fin n) ℂ :=
  Matrix.of fun i a => ![poleVec₀ (z a), poleVec₁ (z a)] i

/-- The Gram matrices of the pole state are compressions of `h`. -/
theorem gram_poleState {n : ℕ} (z : Fin n → posAffine) :
    gram poleState z = (poleMat z)ᴴ * krein2 * poleMat z := by
  ext a b
  simp only [gram, poleState_inv_mul, kreinForm, Matrix.mul_apply, Fin.sum_univ_two, krein2,
    poleMat, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    Complex.star_def]
  ring

theorem hermQuad_krein2 (y : Fin 2 → ℂ) :
    hermQuad krein2 y = (kreinForm (y 0) (y 1) (y 0) (y 1)).re := by
  simp only [hermQuad, krein2, kreinForm, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Pi.star_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Complex.star_def]
  congr 1
  ring

/-- **The pole state has exactly one negative square.** -/
theorem negIndex_poleState : negIndex poleState = 1 := by
  refine le_antisymm ?_ ?_
  · refine negIndex_le_iff.mpr fun n z => ?_
    -- nonnegative on the kernel of `c ↦ (S c)₀ − i (S c)₁`
    let φ : Fin 1 → (Fin n → ℂ) →ₗ[ℂ] ℂ := fun _ =>
      { toFun := fun c => (poleMat z *ᵥ c) 0 - I * (poleMat z *ᵥ c) 1
        map_add' := fun c d => by simp only [Matrix.mulVec_add, Pi.add_apply]; ring
        map_smul' := fun t c => by
          simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
    have h := ArithmeticCastelnuovoSeveri.negIndex_le_card_of_nonneg_on_ker (gram poleState z) φ
      fun c hc => by
        rw [gram_poleState, HTGeometry.hermQuad_rect_conjugate, hermQuad_krein2]
        refine kreinForm_re_nonneg ?_
        have := hc 0
        simp only [φ, LinearMap.coe_mk, AddHom.coe_mk] at this
        linear_combination this
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  · -- the dilation by `4`: `2 − 2(s + 1/s) < 0` for `s = √4 ≠ 1`
    have h4 : (0 : ℚ) < ((Units.mk0 (4 : ℚ) (by norm_num) : ℚˣ) : ℚ) := by norm_num
    set d : posAffine := ⟨dilation (Units.mk0 (4 : ℚ) (by norm_num)), by
      show (0 : ℚ) < affSlope _; rw [affSlope_dilation]; exact h4⟩
    have hd : posSlope d = 4 := by
      simp only [posSlope, d, affSlope_dilation, Units.val_mk0]; norm_num
    have hdi : posSlope d⁻¹ = 1 / 4 := by
      rw [show posSlope d⁻¹ = posSlope (d⁻¹ * 1) by rw [mul_one], slope_inv_mul, hd]
      simp [posSlope, affSlope_one]
    have hsh : posShift d = 0 := by simp [posShift, d, affShift_dilation]
    have hshi : posShift d⁻¹ = 0 := by
      rw [show posShift d⁻¹ = posShift (d⁻¹ * 1) by rw [mul_one], shift_inv_mul, hsh]
      simp [posShift, affShift_one]
    have hs4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hs14 : Real.sqrt (1 / 4) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h1 : poleState 1 = 2 := by
      simp [poleState, posSlope, posShift, affSlope_one, affShift_one]; norm_num
    have hval : poleState d = 5 / 2 := by
      simp only [poleState, hd, hsh, hs4, zero_div]; push_cast; norm_num
    have hvali : poleState d⁻¹ = 5 / 2 := by
      simp only [poleState, hdi, hshi, hs14, zero_div]; push_cast; norm_num
    have hneg : hermQuad (gram poleState ![1, d]) ![1, -1] < 0 := by
      rw [hermQuad_gram]
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, inv_one, one_mul,
        mul_one, inv_mul_cancel, h1, hval, hvali]
      norm_num
    simpa using card_le_negIndex_of_orthogonal_translates (J := Fin 1) hneg (fun _ => 1)
      fun j j' h => absurd (Subsingleton.elim j j') h

/-- On the dilations the pole state is the pole pair `u^{1/2} + u^{−1/2}`. -/
theorem poleState_dilation (u : ℚˣ) (hu : 0 < (u : ℚ)) :
    poleState ⟨dilation u, by show (0 : ℚ) < affSlope _; rw [affSlope_dilation]; exact hu⟩ =
      ((Real.sqrt (u : ℚ) + 1 / Real.sqrt (u : ℚ) : ℝ) : ℂ) := by
  simp [poleState, posSlope, posShift, affSlope_dilation, affShift_dilation]

/-- On the translations the pole state is `2 − ib`. -/
theorem poleState_translation (b : ℚ) :
    poleState ⟨translation b, by show (0 : ℚ) < affSlope _; rw [affSlope_translation]; exact one_pos⟩
      = 2 - I * (b : ℂ) := by
  simp [poleState, posSlope, posShift, affSlope_translation, affShift_translation]
  norm_num

/-- The dilation `x ↦ ux` multiplies the successor part by the conformal factor `u`. -/
theorem poleState_conformal (u b : ℚ) :
    poleState ⟨translation (u * b), by
        show (0 : ℚ) < affSlope _; rw [affSlope_translation]; exact one_pos⟩ - 2 =
      (u : ℂ) * (poleState ⟨translation b, by
        show (0 : ℚ) < affSlope _; rw [affSlope_translation]; exact one_pos⟩ - 2) := by
  rw [poleState_translation, poleState_translation]
  push_cast
  ring

end GaloisForLFunctions.AdelicKreinGeometry
