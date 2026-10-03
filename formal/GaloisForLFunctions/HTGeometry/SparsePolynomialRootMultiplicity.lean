import Mathlib

/-!
# A polynomial with `m` terms has no nonzero root of multiplicity `m`

Over a field of characteristic `p`, a nonzero polynomial of degree `< p` with at most `m` nonzero
coefficients is not divisible by `(X − r)^m` for any `r ≠ 0`
(`not_pow_dvd_of_card_support_le`).  The Euler-type operator `f ↦ X f′ − e₀ f`, with `e₀` the
trailing degree, multiplies the coefficient of `Xⁿ` by `n − e₀`; it kills the lowest term, keeps all
others (their exponents differ from `e₀` by less than `p`), and lowers the multiplicity of the root
`r` by at most one.  Induction on `m` finishes.

This is the linear-independence input of Stepanov's method for shifted multiplicative subgroups.
-/

open Polynomial Finset

namespace GaloisForLFunctions.HTGeometry.SparsePolynomial

variable {K : Type*} [Field K]

theorem coeff_X_mul_derivative (f : K[X]) (n : ℕ) : (X * derivative f).coeff n = f.coeff n * n := by
  rcases n with _ | k
  · simp
  · rw [coeff_X_mul, coeff_derivative]; push_cast; ring

/-- The Euler-type operator `f ↦ X f′ − e f`. -/
noncomputable def euler (e : ℕ) (f : K[X]) : K[X] := X * derivative f - C (e : K) * f

theorem coeff_euler (e : ℕ) (f : K[X]) (n : ℕ) :
    (euler e f).coeff n = f.coeff n * ((n : K) - e) := by
  rw [euler, coeff_sub, coeff_X_mul_derivative, coeff_C_mul]; ring

theorem pow_dvd_euler {r : K} {m : ℕ} {f : K[X]} (e : ℕ) (h : (X - C r) ^ (m + 1) ∣ f) :
    (X - C r) ^ m ∣ euler e f := by
  obtain ⟨g, rfl⟩ := h
  have hd : (X - C r) ^ m ∣ derivative ((X - C r) ^ (m + 1) * g) := by
    rw [derivative_mul, derivative_pow, Nat.add_sub_cancel]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _)
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Nat.le_succ m)) _)
  exact dvd_sub (dvd_mul_of_dvd_right hd X)
    (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (pow_dvd_pow _ (Nat.le_succ m)) g) _)

/-- **Sparse polynomials have no high-multiplicity nonzero roots.**  In characteristic `p`, a
nonzero polynomial of degree `< p` with at most `m` nonzero coefficients is not divisible by
`(X − r)^m` for `r ≠ 0`. -/
theorem not_pow_dvd_of_card_support_le {p : ℕ} [CharP K p] {r : K} (hr : r ≠ 0) :
    ∀ (m : ℕ) {f : K[X]}, f ≠ 0 → f.natDegree < p → f.support.card ≤ m → ¬ (X - C r) ^ m ∣ f := by
  intro m
  induction m with
  | zero =>
    intro f hf _ hm
    exact absurd (card_eq_zero.mp (Nat.le_zero.mp hm)) (by simpa using hf)
  | succ m ih =>
    intro f hf hdeg hm hdvd
    set e₀ := f.natTrailingDegree
    have he₀ : f.coeff e₀ ≠ 0 := by
      rw [show f.coeff e₀ = f.trailingCoeff from rfl]
      exact trailingCoeff_nonzero_iff_nonzero.mpr hf
    set g := euler e₀ f
    have hsupp : g.support ⊆ f.support.erase e₀ := by
      intro n hn
      rw [mem_support_iff, coeff_euler] at hn
      refine mem_erase.mpr ⟨fun h => hn (by rw [h]; ring), ?_⟩
      rw [mem_support_iff]; intro h0; exact hn (by rw [h0, zero_mul])
    have hcard : g.support.card ≤ m := by
      have := card_le_card hsupp
      rw [card_erase_of_mem (mem_support_iff.mpr he₀)] at this
      omega
    have hgdeg : g.natDegree < p := by
      rcases eq_or_ne g 0 with h0 | h0
      · rw [h0, natDegree_zero]; exact lt_of_le_of_lt (Nat.zero_le _) hdeg
      · exact lt_of_le_of_lt (le_natDegree_of_mem_supp _
          (mem_of_mem_erase (hsupp (natDegree_mem_support_of_nonzero h0)))) hdeg
    by_cases hg : g = 0
    · -- `f` is a single monomial `c Xᵉ⁰`
      have hmono : f = C (f.coeff e₀) * X ^ e₀ := by
        ext n
        rw [coeff_C_mul_X_pow]
        split_ifs with hn
        · rw [hn]
        · by_contra hne
          have hmem : n ∈ f.support := mem_support_iff.mpr hne
          have hle : e₀ ≤ n := natTrailingDegree_le_of_mem_supp n hmem
          have hlt : n < p := lt_of_le_of_lt (le_natDegree_of_mem_supp n hmem) hdeg
          have h1 : g.coeff n = 0 := by rw [hg, coeff_zero]
          rw [show g = euler e₀ f from rfl, coeff_euler] at h1
          have hsub : ((n : K) - e₀) = ((n - e₀ : ℕ) : K) := by push_cast [hle]; ring
          rw [hsub] at h1
          have hne0 : ((n - e₀ : ℕ) : K) ≠ 0 := by
            rw [Ne, CharP.cast_eq_zero_iff K p]
            intro hdv
            have := Nat.le_of_dvd (by omega) hdv
            omega
          exact hne (by simpa [hne0] using h1)
      have hroot : (X - C r) ∣ f := (dvd_pow_self _ (Nat.succ_ne_zero m)).trans hdvd
      rw [dvd_iff_isRoot, IsRoot, hmono] at hroot
      simp only [eval_mul, eval_C, eval_pow, eval_X] at hroot
      exact he₀ ((mul_eq_zero.mp hroot).resolve_right (pow_ne_zero _ hr))
    · exact ih hg hgdeg hcard (pow_dvd_euler e₀ hdvd)

end GaloisForLFunctions.HTGeometry.SparsePolynomial
