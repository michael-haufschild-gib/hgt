import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Derivative

/-!
# The power map is finite free of rank `n`: the residue decomposition

Deninger's Frobenius/Verschiebung operators on the rational-Witt source come from the power
maps `f_n : 𝔸¹ → 𝔸¹`, `x ↦ xⁿ`.  The finite-syntomic framed-transfer machinery rests on one
algebraic fact: along `f_n` the coordinate ring upstairs is **finite free of rank `n`** with
basis `1, x, …, x^(n-1)` — `ℤ[y][x]/(xⁿ - y) ≃ ℤ[x]`.

This file formalizes that fact in exact residue-decomposition form, over the integral
coefficients the Milnor–Witt realization demands:

* `coeff_sum_expand_mul_X_pow` — the single-contributor coefficient formula: in
  `Σᵢ gᵢ(Xⁿ)·Xⁱ` the coefficient at degree `d` reads exactly `g_{d % n}` at `d / n`;
* `powerMap_residue_decomposition` — **every `f : ℤ[X]` is uniquely
  `Σ_{i<n} gᵢ(Xⁿ)·Xⁱ`**: existence and uniqueness of the rank-`n` free decomposition along
  the power map;
* `powerMap_tower` — the Frobenius composition law `F_m ∘ F_n = F_{mn}` in these coordinates
  (`expand` composition), and `powerMap_chainRule` — the composite framing scalar
  `d(x^{mn}) = mn·x^{mn-1}`, the determinant datum of the iterated cotangent reduction.

Unconditional, elementary, and the exact algebraic layer the framed finite-syntomic transfer
coherence (proof obligation 2 of the Milnor–Witt realization card) builds on.
-/

namespace GaloisForLFunctions

noncomputable section

open Polynomial

/-- **Single-contributor coefficient formula**: in `Σᵢ gᵢ(Xⁿ)·Xⁱ` (indices `i < n`), the
coefficient at degree `d` is the `d/n`-th coefficient of the residue component `g_{d % n}`. -/
theorem coeff_sum_expand_mul_X_pow {n : ℕ} (hn : 0 < n)
    (g : Fin n → Polynomial ℤ) (d : ℕ) :
    (∑ i : Fin n, Polynomial.expand ℤ n (g i) * Polynomial.X ^ (i : ℕ)).coeff d =
      (g ⟨d % n, Nat.mod_lt d hn⟩).coeff (d / n) := by
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (⟨d % n, Nat.mod_lt d hn⟩ : Fin n)]
  · have hdm := Nat.div_add_mod d n
    have hval : ((⟨d % n, Nat.mod_lt d hn⟩ : Fin n) : ℕ) = d % n := rfl
    rw [Polynomial.coeff_mul_X_pow', hval, if_pos (Nat.mod_le d n),
      Polynomial.coeff_expand hn, if_pos ⟨d / n, by omega⟩]
    congr 1
    rw [show d - d % n = n * (d / n) by omega]
    exact Nat.mul_div_cancel_left _ hn
  · intro i _ hne
    rw [Polynomial.coeff_mul_X_pow']
    by_cases hle : (i : ℕ) ≤ d
    · rw [if_pos hle, Polynomial.coeff_expand hn, if_neg ?_]
      rintro ⟨k, hk⟩
      have hi := i.isLt
      apply hne
      apply Fin.ext
      show (i : ℕ) = d % n
      have hd : d = n * k + (i : ℕ) := by omega
      rw [hd, Nat.mul_add_mod]
      exact (Nat.mod_eq_of_lt hi).symm
    · rw [if_neg hle]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The residue component of `f` along the power map: the coefficients of `f` in degrees
`≡ i (mod n)`, reassembled on the base. -/
def powerMapResidueComponent (n : ℕ) (f : Polynomial ℤ) (i : Fin n) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (f.natDegree + 1),
    Polynomial.C (f.coeff (n * k + i)) * Polynomial.X ^ k

theorem powerMapResidueComponent_coeff {n : ℕ} (hn : 0 < n) (f : Polynomial ℤ)
    (i : Fin n) (k : ℕ) :
    (powerMapResidueComponent n f i).coeff k = f.coeff (n * k + i) := by
  rw [powerMapResidueComponent, Polynomial.finsetSum_coeff]
  by_cases hk : k ∈ Finset.range (f.natDegree + 1)
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hb.symm,
        mul_zero]
    · intro hknot
      exact absurd hk hknot
  · rw [Finset.sum_eq_zero, eq_comm]
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Finset.mem_range] at hk
      have hnk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
      omega
    · intro b hb
      rw [Finset.mem_range] at hb hk
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (by omega : ¬ k = b), mul_zero]

/-- **The power map is finite free of rank `n`**: every integral polynomial is uniquely
`Σ_{i<n} gᵢ(Xⁿ)·Xⁱ`.  This is `ℤ[y][x]/(xⁿ - y) ≃ ℤ[x]` with free basis `1, x, …, x^(n-1)`
in residue-decomposition form — the algebraic core of the finite-syntomic framed transfer
along `x ↦ xⁿ`. -/
theorem powerMap_residue_decomposition {n : ℕ} (hn : 0 < n) (f : Polynomial ℤ) :
    ∃! g : Fin n → Polynomial ℤ,
      f = ∑ i : Fin n, Polynomial.expand ℤ n (g i) * Polynomial.X ^ (i : ℕ) := by
  refine ⟨powerMapResidueComponent n f, ?_, ?_⟩
  · ext d
    rw [coeff_sum_expand_mul_X_pow hn, powerMapResidueComponent_coeff hn]
    congr 1
    exact (Nat.div_add_mod d n).symm
  · intro h hh
    funext i
    ext k
    have h1 := congrArg (fun p => Polynomial.coeff p (n * k + i)) hh
    rw [coeff_sum_expand_mul_X_pow hn] at h1
    have hi := i.isLt
    have hidx : ((⟨(n * k + (i : ℕ)) % n, Nat.mod_lt _ hn⟩ : Fin n)) = i := by
      apply Fin.ext
      show (n * k + (i : ℕ)) % n = (i : ℕ)
      rw [Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt hi
    have hdiv : (n * k + (i : ℕ)) / n = k := by
      rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hi, add_zero]
    rw [hidx, hdiv] at h1
    rw [powerMapResidueComponent_coeff hn]
    exact h1.symm

/-- The Frobenius composition law `F_m ∘ F_n = F_{mn}` in power-map coordinates. -/
theorem powerMap_tower (m n : ℕ) (f : Polynomial ℤ) :
    Polynomial.expand ℤ m (Polynomial.expand ℤ n f) =
      Polynomial.expand ℤ (m * n) f :=
  Polynomial.expand_expand m n f

/-- The composite framing scalar: `d(x^{mn}) = mn·x^{mn-1}`, the determinant datum of the
iterated cotangent reduction of the composed power maps. -/
theorem powerMap_chainRule (m n : ℕ) :
    Polynomial.derivative ((Polynomial.X : Polynomial ℤ) ^ (m * n)) =
      Polynomial.C ((m * n : ℕ) : ℤ) * Polynomial.X ^ (m * n - 1) :=
  Polynomial.derivative_X_pow (m * n)

end

end GaloisForLFunctions
