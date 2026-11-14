import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionCocompact
import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Walls and a homomorphism `Γ(N) → ℤ`

A *wall* is `w ∈ O` with `trd w = 0`, `nrd w = −2` and `w ≡ i mod N`.  For `M = ι(w)` the form
`H_M(z) = M₁₀|z|² − (M₀₀ − M₁₁) Re z − M₀₁` vanishes exactly on the geodesic fixed by the reflection
`w`, and `H_{gMg⁻¹}(gz) = H_M(z)/|cz + d|²` (`hermForm_conj_smul`), so its sign is invariant.
Conjugation by `γ ∈ Γ(N)` permutes the walls (`wallEquiv`).  Only finitely many walls separate two
points (`finite_separating`): a wall through a point of the segment `[z₁, z₂]` has
`(a − cx)² + c²y² = 2`, hence bounded entries.

`wallCount z₀ z = Σ_w (1[H_w(z) > 0] − 1[H_w(z₀) > 0])` satisfies
`wallCount z₀ (γz) = wallCount z₀ z + wallCount z₀ (γz₀)` (`wallCount_smul`), so
`χ(γ) = wallCount z₀ (γ z₀)` is a homomorphism (`wallHom`).

`two_lt_abs_trSL_congGroup`: every `γ ≠ 1` in `Γ(N)`, `N ≥ 3`, has `|tr γ| ≥ 4`.
-/

open Matrix UpperHalfPlane Set
open scoped MatrixGroups

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Hyperbolicity in `Γ(N)` -/

/-- **Every nontrivial element of `Γ(N)` is hyperbolic**, `N ≥ 3`. -/
theorem two_lt_abs_trSL_congGroup {N : ℕ} (hN : 3 ≤ N) (γ : congGroup N) (hγ : γ ≠ 1) :
    2 < |trSL (γ : SL(2, ℝ))| := by
  obtain ⟨x, hx1, ⟨u, hu⟩, hxg⟩ := γ.2
  have hent : ∀ i j, (γ : SL(2, ℝ)) i j = quatMat x i j := fun i j => by
    rw [show (γ : SL(2, ℝ)) i j = ((γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j from rfl, hxg]
  have htr : trSL (γ : SL(2, ℝ)) = 2 * (x 0 : ℝ) := by
    rw [trSL, hent, hent]; simp [quatMat_apply]; ring
  have hx0 : x 0 = 1 + (N : ℤ) * u 0 := by
    have := congrFun hu 0
    simpa [quatOne] using this
  have hN' : (3 : ℤ) ≤ N := by exact_mod_cast hN
  rw [htr]
  by_contra hle
  have hle' : |(x 0 : ℝ)| ≤ 1 := by
    rw [abs_mul, abs_two] at hle; linarith [not_lt.mp hle]
  have hle'' : |x 0| ≤ 1 := by exact_mod_cast hle'
  have hb := abs_le.mp hle''
  rcases (show x 0 = -1 ∨ x 0 = 0 ∨ x 0 = 1 by omega) with h | h | h
  · have hd : (N : ℤ) ∣ 2 := ⟨-u 0, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd; omega
  · have hd : (N : ℤ) ∣ 1 := ⟨-u 0, by linarith⟩
    have := Int.le_of_dvd (by norm_num) hd; omega
  · -- the pure part has norm zero, hence vanishes
    have hpure : nrd ![0, x 1, x 2, x 3] = 0 := by
      have := hx1; simp only [nrd] at this ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons]
      rw [h] at this; linarith
    have h0 := eq_zero_of_nrd_eq_zero _ hpure
    have e1 : x 1 = 0 := by simpa using congrFun h0 1
    have e2 : x 2 = 0 := by simpa using congrFun h0 2
    have e3 : x 3 = 0 := by simpa using congrFun h0 3
    apply hγ
    have hxe : x = quatOne := by
      funext k; fin_cases k
      · simp [quatOne, h]
      · simp [quatOne, e1]
      · simp [quatOne, e2]
      · simp [quatOne, e3]
    apply Subtype.ext
    apply Subtype.ext
    rw [hxg, hxe, quatMat_one]
    rfl

/-! ### The side of a wall -/

/-- `H_M(z) = M₁₀ |z|² − (M₀₀ − M₁₁) Re z − M₀₁`. -/
def hermForm (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℍ) : ℝ :=
  M 1 0 * (z.re ^ 2 + z.im ^ 2) - (M 0 0 - M 1 1) * z.re - M 0 1

/-- `|cz + d|²`. -/
def denomSq (g : SL(2, ℝ)) (z : ℍ) : ℝ := (g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2

theorem denomSq_pos (g : SL(2, ℝ)) (z : ℍ) : 0 < denomSq g z := by
  have hdet := det_SL g
  have hy := z.im_pos
  unfold denomSq
  rcases eq_or_ne (g 1 0) 0 with h | h
  · rw [h] at hdet ⊢
    have : g 1 1 ≠ 0 := fun h' => by rw [h'] at hdet; simp at hdet
    simp only [zero_mul, zero_add]
    positivity
  · have : 0 < (g 1 0 * z.im) ^ 2 := by positivity
    positivity

theorem coe_smul_SL (g : SL(2, ℝ)) (z : ℍ) : ((g • z : ℍ) : ℂ) =
    ((g 0 0 : ℂ) * z + g 0 1) / ((g 1 0 : ℂ) * z + g 1 1) := by
  rw [coe_specialLinearGroup_apply]
  rfl

theorem re_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (g • z).re =
    ((g 0 0 * z.re + g 0 1) * (g 1 0 * z.re + g 1 1) + g 0 0 * g 1 0 * z.im ^ 2) / denomSq g z := by
  have hD := (denomSq_pos g z).ne'
  rw [← UpperHalfPlane.coe_re, coe_smul_SL, Complex.div_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im,
    Complex.mul_im, add_zero]
  unfold denomSq at hD ⊢
  field_simp
  ring

theorem im_smul_SL (g : SL(2, ℝ)) (z : ℍ) : (g • z).im = z.im / denomSq g z := by
  have hD := (denomSq_pos g z).ne'
  have hdet := det_SL g
  rw [← UpperHalfPlane.coe_im, coe_smul_SL, Complex.div_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, zero_mul, sub_zero, Complex.add_im,
    Complex.mul_im, add_zero]
  unfold denomSq at hD ⊢
  field_simp
  linear_combination (z.im * ((g 1 0 * z.re + g 1 1) ^ 2 + (g 1 0 * z.im) ^ 2)) * hdet

/-- **Equivariance.**  `H_{gMg⁻¹}(gz) = H_M(z)/|cz + d|²`. -/
theorem hermForm_conj_smul (g : SL(2, ℝ)) (M : Matrix (Fin 2) (Fin 2) ℝ) (z : ℍ) :
    hermForm ((g : Matrix (Fin 2) (Fin 2) ℝ) * M * ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ))
      (g • z) = hermForm M z / denomSq g z := by
  have hD := (denomSq_pos g z).ne'
  have hdet := det_SL g
  rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two, hermForm, hermForm, re_smul_SL,
    im_smul_SL]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons]
  unfold denomSq at hD ⊢
  field_simp
  have key : ∀ p q r t x y m00 m01 m10 m11 : ℝ, p * t - q * r = 1 →
      ((r * m00 + t * m10) * t + (r * m01 + t * m11) * -r) *
          (((p * x + q) * (r * x + t) + p * r * y ^ 2) ^ 2 + (y * ((r * x + t) ^ 2 + (r * y) ^ 2)) ^ 2 /
            ((r * x + t) ^ 2 + (r * y) ^ 2)) -
        (((p * m00 + q * m10) * t + (p * m01 + q * m11) * -r) -
            ((r * m00 + t * m10) * -q + (r * m01 + t * m11) * p)) *
          (((p * x + q) * (r * x + t) + p * r * y ^ 2) * ((r * x + t) ^ 2 + (r * y) ^ 2)) -
        ((p * m00 + q * m10) * -q + (p * m01 + q * m11) * p) *
          ((r * x + t) ^ 2 + (r * y) ^ 2) ^ 2 = 0 → True := fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  ring_nf
  ring_nf at hdet
  nlinarith [hdet, sq_nonneg z.im]

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
