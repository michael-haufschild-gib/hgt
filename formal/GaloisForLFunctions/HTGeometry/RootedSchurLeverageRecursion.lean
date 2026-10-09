import GaloisForLFunctions.HTGeometry.ComplementaryFeshbachImprovement
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# The rooted Schur recursion of a rank-one polar load

Let `M = [[A, B], [B*, D]]` act on `X ⊕ Y` and let `(s, t)` be a polar vector. Put
`S = D − B* A⁻¹ B` and `η = t − B* A⁻¹ s`, and define the root defects
`δ_old = 1 − 2 Re⟨s, A⁻¹ s⟩` and `δ_new = 1 − 2 Re⟨(s, t), M⁻¹(s, t)⟩`.
Then `A − 2|s⟩⟨s|` is positive iff `δ_old > 0`, and similarly for `M` and `δ_new`.

* **Recursion** (`rootDefect_succ_eq`, `rootDefect_succ_eq_mul`).
  `δ_new = δ_old − 2 Re⟨η, S⁻¹ η⟩ = δ_old (1 − ℓ)` with `ℓ = 2 Re⟨η, S⁻¹ η⟩/δ_old`.
* **Variational form** (`normSq_inner_le_leverage_mul`, `normSq_inner_eq_leverage_mul`). For
  positive `S` with right inverse `S⁻¹`, `|⟨η, f⟩|² ≤ Re⟨η, S⁻¹η⟩ Re⟨S f, f⟩`, with equality at
  `f = S⁻¹ η`. So `ℓ = sup_f 2|⟨η, f⟩|²/(δ_old Re⟨S f, f⟩)`.
* **Rooted block** (`rootedBlock_ge`). If `δ_old > 0` and `ℓ ≤ q`, then
  `Re⟨S f, f⟩ − (2/δ_old)|⟨η, f⟩|² ≥ (1 − q) Re⟨S f, f⟩`.

The recursion is the quotient formula for Schur complements, through the corpus split
`complementarySchur_inverse_inner_split`. The variational form is Cauchy–Schwarz for the positive
form `⟨S ·, ·⟩`.
-/

open scoped InnerProductSpace ComplexConjugate ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open ContinuousLinearMap

variable {X Y : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

/-! ## The defect recursion -/

/-- **Root-defect recursion.** If `(x, y)` solves `M(x, y) = (u, v)`, then
`1 − 2 Re(⟨u, x⟩ + ⟨v, y⟩) = (1 − 2 Re⟨u, A⁻¹u⟩) − 2 Re⟨η, S⁻¹η⟩` with
`η = v − B* A⁻¹ u`. -/
theorem rootDefect_succ_eq
    (A Ainv : X →L[ℂ] X) (B : Y →L[ℂ] X) (C : X →L[ℂ] Y) (D Oinv : Y →L[ℂ] Y)
    (u x : X) (v y : Y)
    (hAinvLeft : Ainv ∘L A = 1)
    (hOinvLeft : Oinv ∘L complementarySchurBlock D C Ainv B = 1)
    (hAinvSelf : IsSelfAdjoint Ainv) (hC : C = B.adjoint)
    (hLow : A x + B y = u) (hHigh : C x + D y = v) :
    1 - 2 * (inner ℂ u x + inner ℂ v y).re =
      (1 - 2 * (inner ℂ u (Ainv u)).re) -
        2 * (inner ℂ (complementarySchurResidual v C Ainv u)
          (Oinv (complementarySchurResidual v C Ainv u))).re := by
  rw [complementarySchur_inverse_inner_split A Ainv B C D Oinv u x v y hAinvLeft hOinvLeft
    hAinvSelf hC hLow hHigh, Complex.add_re]
  ring

/-- **Multiplicative form.** `δ_new = δ_old (1 − ℓ)` with `ℓ = 2 Re⟨η, S⁻¹η⟩/δ_old`. -/
theorem rootDefect_succ_eq_mul {δold δnew gain : ℝ} (hδ : δold ≠ 0)
    (hrec : δnew = δold - 2 * gain) :
    δnew = δold * (1 - 2 * gain / δold) := by
  rw [hrec]
  field_simp

/-! ## The variational form of the leverage -/

omit [CompleteSpace Y] in
/-- Real Cauchy–Schwarz for a positive operator:
`(Re⟨S g, f⟩)² ≤ Re⟨S g, g⟩ Re⟨S f, f⟩`. -/
theorem re_inner_sq_le_of_isPositive {S : Y →L[ℂ] Y} (hS : S.IsPositive) (g f : Y) :
    (inner ℂ (S g) f).re ^ 2 ≤ (inner ℂ (S g) g).re * (inner ℂ (S f) f).re := by
  have hsym : (inner ℂ (S f) g).re = (inner ℂ (S g) f).re := by
    rw [hS.inner_left_eq_inner_right, ← inner_conj_symm, Complex.conj_re]
  have key : ∀ t : ℝ, 0 ≤ (inner ℂ (S g) g).re * (t * t) +
      (-2 * (inner ℂ (S g) f).re) * t + (inner ℂ (S f) f).re := by
    intro t
    have h := hS.re_inner_nonneg_left ((t : ℂ) • g - f)
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal] at h
    simp only [RCLike.re_to_complex, mul_sub, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] at h
    rw [hsym] at h
    nlinarith
  have hd := discrim_le_zero key
  unfold discrim at hd
  nlinarith

omit [CompleteSpace Y] in
/-- **Leverage bound.** For positive `S` with `S S⁻¹ = 1`,
`|⟨η, f⟩|² ≤ Re⟨η, S⁻¹η⟩ Re⟨S f, f⟩`. -/
theorem normSq_inner_le_leverage_mul {S Sinv : Y →L[ℂ] Y} (hS : S.IsPositive)
    (hSinv : S ∘L Sinv = 1) (η f : Y) :
    ‖inner ℂ η f‖ ^ 2 ≤ (inner ℂ η (Sinv η)).re * (inner ℂ (S f) f).re := by
  set g := Sinv η with hg
  have hSg : S g = η := by
    have h := DFunLike.congr_fun hSinv η
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h
  have hA : inner ℂ η g = inner ℂ (S g) g := by rw [hSg]
  set z := inner ℂ η f with hz
  by_cases hz0 : z = 0
  · rw [hz0, norm_zero, zero_pow two_ne_zero, hA]
    exact mul_nonneg (hS.re_inner_nonneg_left g) (hS.re_inner_nonneg_left f)
  -- rotate `f` so that the pairing becomes `‖z‖`
  have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz0
  set c : ℂ := conj z / ‖z‖ with hc
  have hcz : c * z = ‖z‖ := by
    rw [hc, div_mul_eq_mul_div, Complex.conj_mul', pow_two]
    field_simp
  have hcc : conj c * c = 1 := by
    rw [hc, map_div₀, Complex.conj_ofReal, Complex.conj_conj, div_mul_div_comm,
      Complex.mul_conj', ← pow_two]
    field_simp
  have h := re_inner_sq_le_of_isPositive hS g (c • f)
  have h1 : (inner ℂ (S g) (c • f)).re = ‖z‖ := by
    rw [inner_smul_right, hSg, ← hz, hcz, Complex.ofReal_re]
  have h2 : (inner ℂ (S (c • f)) (c • f)).re = (inner ℂ (S f) f).re := by
    rw [map_smul, inner_smul_left, inner_smul_right, ← mul_assoc, hcc, one_mul]
  rw [h1, h2] at h
  rw [hA]
  exact h

omit [CompleteSpace Y] in
/-- **The bound is attained** at `f = S⁻¹η`. -/
theorem normSq_inner_eq_leverage_mul {S Sinv : Y →L[ℂ] Y} (hS : S.IsPositive)
    (hSinv : S ∘L Sinv = 1) (η : Y) :
    ‖inner ℂ η (Sinv η)‖ ^ 2 =
      (inner ℂ η (Sinv η)).re * (inner ℂ (S (Sinv η)) (Sinv η)).re := by
  have hSg : S (Sinv η) = η := by
    have h := DFunLike.congr_fun hSinv η
    simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h
  rw [hSg]
  have hnn : 0 ≤ inner ℂ η (Sinv η) := by
    have := hS.inner_nonneg_left (Sinv η)
    rwa [hSg] at this
  obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hnn
  have heq : inner ℂ η (Sinv η) = ((inner ℂ η (Sinv η)).re : ℂ) :=
    Complex.ext (by simp) (by simp [← him])
  rw [heq, Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg hre, pow_two]

omit [CompleteSpace Y] in
/-- **Rooted block.** If `δ > 0` and `2 Re⟨η, S⁻¹η⟩ ≤ q δ`, then
`Re⟨S f, f⟩ − (2/δ)|⟨η, f⟩|² ≥ (1 − q) Re⟨S f, f⟩`. -/
theorem rootedBlock_ge {S Sinv : Y →L[ℂ] Y} (hS : S.IsPositive) (hSinv : S ∘L Sinv = 1)
    (η : Y) {δ q : ℝ} (hδ : 0 < δ) (hℓ : 2 * (inner ℂ η (Sinv η)).re ≤ q * δ) (f : Y) :
    (1 - q) * (inner ℂ (S f) f).re ≤ (inner ℂ (S f) f).re - 2 / δ * ‖inner ℂ η f‖ ^ 2 := by
  have hcs := normSq_inner_le_leverage_mul hS hSinv η f
  have hB := hS.re_inner_nonneg_left f
  have h1 : 2 / δ * ‖inner ℂ η f‖ ^ 2 ≤ 2 / δ * ((inner ℂ η (Sinv η)).re * (inner ℂ (S f) f).re) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  have h2 : 2 / δ * ((inner ℂ η (Sinv η)).re * (inner ℂ (S f) f).re) ≤ q * (inner ℂ (S f) f).re := by
    rw [← mul_assoc, div_mul_eq_mul_div, mul_comm 2]
    have : (inner ℂ η (Sinv η)).re * 2 / δ ≤ q := by
      rw [div_le_iff₀ hδ]; linarith
    exact mul_le_mul_of_nonneg_right this hB
  linarith

end GaloisForLFunctions.HTGeometry
