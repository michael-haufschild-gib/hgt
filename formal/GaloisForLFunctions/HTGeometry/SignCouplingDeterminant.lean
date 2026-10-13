import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The sign-coupling determinant

For `λ, g : Fin n → ℂ` let `K` be the matrix with entries `K_{uv} = i·g_u·g_v` for `u < v`,
`K_{uv} = −i·g_u·g_v` for `u > v` and zero diagonal.  For real `g` it is Hermitian.  Then

`det(diag λ − K) = (∏ (λ_u + i g_u²) + ∏ (λ_u − i g_u²)) / 2`
(`det_diagonal_sub_signCoupling`).

So the real part of a product `∏ (λ_u + i c_u)` is the determinant of a diagonal matrix minus a
Hermitian coupling with entries `± i √(c_u c_v)`.  This is the algebraic core of the matrix
realization of the cosine step `cos(aD)p = Re p(z + ia)`.

**Proof.**  Embed `diag λ − K` in the affine family
`N(λ, g, ν)_{uv} = (ν − 2i) g_u g_v` (`u < v`), `ν g_u g_v` (`u > v`), `λ_u + (ν − i) g_u²` (`u = v`),
which equals `diag λ − K` at `ν = i`.  Claim: `det N = P₋ + ν (P₊ − P₋)/(2i)` with
`P_± = ∏ (λ_u ± i g_u²)` (`det_signFamily`).  Induction on `n`: when the pivot
`λ₀ + (ν − i) g₀²` equals `1`, eliminating the first column leaves the family on the tail with
`ν' = ν − ν (ν − 2i) g₀²` (`det_signFamily_of_pivot_eq_one`); the first-row expansion shows that
`det N` is affine in `λ₀` with slope the tail determinant at the same `ν`
(`det_signFamily_sub_update`), which moves a general `λ₀` to the pivot-one value.
-/

open Matrix Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The affine sign family `N(λ, g, ν)`. -/
def signFamily {n : ℕ} (lam g : Fin n → ℂ) (ν : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i < j then (ν - 2 * I) * g i * g j
    else if j < i then ν * g i * g j else lam i + (ν - I) * g i ^ 2

/-- The closed form `P₋ + ν (P₊ − P₋)/(2i)`. -/
def signFamilyDet {n : ℕ} (lam g : Fin n → ℂ) (ν : ℂ) : ℂ :=
  ∏ i, (lam i - I * g i ^ 2) +
    ν * ((∏ i, (lam i + I * g i ^ 2) - ∏ i, (lam i - I * g i ^ 2)) / (2 * I))

/-- The Hermitian sign coupling `K`. -/
def signCoupling {n : ℕ} (g : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i < j then I * g i * g j else if j < i then -(I * g i * g j) else 0

/-- Removing a rank-one multiple of `g gᵀ` from the tail shifts `ν`. -/
theorem signFamily_succ_succ_sub {n : ℕ} (lam g : Fin (n + 1) → ℂ) (ν μ : ℂ) (i j : Fin n) :
    signFamily lam g ν i.succ j.succ - μ * g i.succ * g j.succ =
      signFamily (fun k => lam k.succ) (fun k => g k.succ) (ν - μ) i j := by
  simp only [signFamily, of_apply, Fin.succ_lt_succ_iff]
  rcases lt_trichotomy i j with h | h | h
  · simp only [h, if_true]; ring
  · subst h; simp only [lt_irrefl, if_false]; ring
  · simp only [h, not_lt.mpr h.le, if_true, if_false]; ring

/-- **Elimination at pivot one.** -/
theorem det_signFamily_of_pivot_eq_one {n : ℕ} (lam g : Fin (n + 1) → ℂ) (ν : ℂ)
    (hπ : lam 0 + (ν - I) * g 0 ^ 2 = 1) :
    (signFamily lam g ν).det =
      (signFamily (fun k => lam k.succ) (fun k => g k.succ) (ν - ν * (ν - 2 * I) * g 0 ^ 2)).det := by
  set N := signFamily lam g ν with hN
  let L : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -(ν * g i * g 0) else 0
  have hLtri : L.BlockTriangular OrderDual.toDual := by
    intro i j hij
    have hij' : i < j := hij
    have hne : i ≠ j := ne_of_lt hij'
    have hj0 : j ≠ 0 := fun h => by rw [h] at hij'; exact absurd hij' (Fin.not_lt_zero i)
    simp [L, hne, hj0]
  have hL : L.det = 1 := by
    rw [det_of_lowerTriangular L hLtri]
    simp [L]
  have hz : ∀ x : Fin n, ((0 : Fin (n + 1)) = x.succ) = False :=
    fun x => propext ⟨fun h => Fin.succ_ne_zero x h.symm, False.elim⟩
  have hrow0 : ∀ j, (L * N) 0 j = N 0 j := by
    intro j
    rw [mul_apply, Fin.sum_univ_succ]
    simp [L, Fin.succ_ne_zero, hz]
  have hrow : ∀ (i : Fin n) j, (L * N) i.succ j = N i.succ j - ν * g i.succ * g 0 * N 0 j := by
    intro i j
    rw [mul_apply, Fin.sum_univ_succ]
    have hsum : ∑ k : Fin n, L i.succ k.succ * N k.succ j = N i.succ j := by
      simp only [L, of_apply, Fin.succ_inj, Fin.succ_ne_zero, if_false]
      simp
    rw [hsum]
    simp only [L, of_apply, (Fin.succ_ne_zero i), if_false, if_true]
    ring
  have h00 : N 0 0 = 1 := by simpa [hN, signFamily] using hπ
  have hcol : ∀ i : Fin n, (L * N) i.succ 0 = 0 := by
    intro i
    rw [hrow, h00]
    have : N i.succ 0 = ν * g i.succ * g 0 := by
      simp [hN, signFamily, Fin.succ_pos, not_lt.mpr (Fin.zero_le _)]
    rw [this]; ring
  rw [← one_mul N.det, ← hL, ← det_mul, det_succ_column_zero, Fin.sum_univ_succ]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, hrow0, h00, Fin.succAbove_zero]
  congr 1
  ext i j
  simp only [submatrix_apply, hrow]
  rw [← signFamily_succ_succ_sub lam g ν (ν * (ν - 2 * I) * g 0 ^ 2) i j]
  have : N 0 j.succ = (ν - 2 * I) * g 0 * g j.succ := by
    simp [hN, signFamily, Fin.succ_pos]
  rw [this]; ring

/-- **Affine dependence on the first diagonal entry.** -/
theorem det_signFamily_sub_update {n : ℕ} (lam g : Fin (n + 1) → ℂ) (ν t : ℂ) :
    (signFamily lam g ν).det - (signFamily (Function.update lam 0 t) g ν).det =
      (lam 0 - t) * (signFamily (fun k => lam k.succ) (fun k => g k.succ) ν).det := by
  set lam' := Function.update lam 0 t
  have hsub : ∀ c : Fin n → Fin (n + 1),
      (signFamily lam' g ν).submatrix Fin.succ c = (signFamily lam g ν).submatrix Fin.succ c := by
    intro c; ext i j
    simp [signFamily, lam']
  have hrow : ∀ j : Fin n, signFamily lam' g ν 0 j.succ = signFamily lam g ν 0 j.succ := by
    intro j; simp [signFamily, Fin.succ_pos]
  have htail : (signFamily lam g ν).submatrix Fin.succ Fin.succ =
      signFamily (fun k => lam k.succ) (fun k => g k.succ) ν := by
    ext i j
    simp only [submatrix_apply]
    have := signFamily_succ_succ_sub lam g ν 0 i j
    simpa using this
  rw [det_succ_row_zero, det_succ_row_zero (signFamily lam' g ν), Fin.sum_univ_succ,
    Fin.sum_univ_succ]
  simp only [hsub, hrow, Fin.succAbove_zero, Fin.val_zero, pow_zero, one_mul]
  rw [htail]
  have h0 : signFamily lam g ν 0 0 - signFamily lam' g ν 0 0 = lam 0 - t := by
    simp [signFamily, lam']
  linear_combination (signFamily (fun k => lam k.succ) (fun k => g k.succ) ν).det * h0

/-- The algebra of the induction step. -/
theorem signFamilyDet_step_alg (l G ν Pp Pm : ℂ) :
    Pm + (ν - ν * (ν - 2 * I) * G) * ((Pp - Pm) / (2 * I)) +
        (l - (1 - (ν - I) * G)) * (Pm + ν * ((Pp - Pm) / (2 * I))) =
      (l - I * G) * Pm + ν * (((l + I * G) * Pp - (l - I * G) * Pm) / (2 * I)) := by
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp
  ring

/-- **The affine sign family determinant.** -/
theorem det_signFamily : ∀ (n : ℕ) (lam g : Fin n → ℂ) (ν : ℂ),
    (signFamily lam g ν).det = signFamilyDet lam g ν := by
  intro n
  induction n with
  | zero => intro lam g ν; simp [signFamilyDet]
  | succ n ih =>
    intro lam g ν
    set t := 1 - (ν - I) * g 0 ^ 2 with ht
    have hπ : (Function.update lam 0 t) 0 + (ν - I) * g 0 ^ 2 = 1 := by simp [ht]
    have h1 := det_signFamily_of_pivot_eq_one (Function.update lam 0 t) g ν hπ
    have htl : (fun k : Fin n => Function.update lam 0 t k.succ) = fun k => lam k.succ := by
      funext k; exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
    rw [htl, ih] at h1
    have h2 := det_signFamily_sub_update lam g ν t
    rw [ih] at h2
    have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
    rw [show (signFamily lam g ν).det =
        (signFamily (Function.update lam 0 t) g ν).det +
          (lam 0 - t) * signFamilyDet (fun k => lam k.succ) (fun k => g k.succ) ν by
        linear_combination h2, h1]
    simp only [signFamilyDet, Fin.prod_univ_succ]
    rw [ht]
    exact signFamilyDet_step_alg _ _ _ _ _

/-- **The sign-coupling determinant.** `det(diag λ − K) = (∏ (λ + i g²) + ∏ (λ − i g²)) / 2`. -/
theorem det_diagonal_sub_signCoupling {n : ℕ} (lam g : Fin n → ℂ) :
    (diagonal lam - signCoupling g).det =
      ((∏ i, (lam i + I * g i ^ 2)) + ∏ i, (lam i - I * g i ^ 2)) / 2 := by
  have h : diagonal lam - signCoupling g = signFamily lam g I := by
    ext i j
    simp only [Matrix.sub_apply, signCoupling, signFamily, of_apply]
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne]; ring
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  rw [h, det_signFamily, signFamilyDet]
  have hI : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  field_simp
  ring

end

end GaloisForLFunctions.HTGeometry
