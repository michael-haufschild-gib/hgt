/-
# Böttcher tower — the field-theoretic core of the Kummer non-squareness

The Kummer route's one irreducibility input is `a = F^{2ᵏ}` not a square in the base. This file isolates
the abstract algebraic skeleton: if a field automorphism `σ` scales `F` by a primitive `2ᵏ`-th root of
unity `ζ` (`ζ^{2^{k-1}} = -1`), then `F^{2ᵏ}` is not a square among the `σ`-fixed elements — any fixed
`b` with `b² = F^{2ᵏ}` is forced to `±F^{2^{k-1}}`, which `σ` negates, so `b = 0`. Geometrically `σ` is
the dynamics monodromy and "σ-fixed" is "descends to the cover base"; the realized fractional period
`2πi/2ⁿ` (`LiftExists.exists_circle_lift_period`) is what makes `σ F = ζ F` non-trivial. This lemma is
the algebra the period feeds into.
-/
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Tactic

namespace Bottcher

/-- **Non-squareness from a scaling automorphism.** If `σ : V ≃ₐ[K] V` scales `F` by `ζ` with
`ζ^{2^{k-1}} = -1` (so `ζ` is a primitive `2ᵏ`-th root), then no `σ`-fixed `b` squares to `F^{2ᵏ}`
(unless `F = 0`). Hence `F^{2ᵏ}` is not a square in the fixed field — the irreducibility input
`Irreducible(X^{2ᵏ} − C a)` of `q62_disconnected_kummer` (Capelli `p=2`, `−1` a square). The geometric
content `σ F = ζ F` is the dyadic monodromy of the Böttcher coordinate around the lift loop. -/
theorem fixed_not_sqrt_of_scaling {K V : Type*} [Field K] [Field V] [CharZero V] [Algebra K V]
    (σ : V ≃ₐ[K] V) {F ζ b : V} {k : ℕ} (hk : 1 ≤ k)
    (hF : F ≠ 0) (hζ : ζ ^ (2 ^ (k - 1)) = -1)
    (hσF : σ F = ζ * F) (hb : σ b = b) :
    b ^ (2 : ℕ) ≠ F ^ (2 ^ k) := by
  intro hbsq
  have hexp : 2 ^ (k - 1) * 2 = 2 ^ k := by rw [← pow_succ]; congr 1; omega
  have hFsq : (F ^ (2 ^ (k - 1))) ^ (2 : ℕ) = F ^ (2 ^ k) := by rw [← pow_mul, hexp]
  have hσFpow : σ (F ^ (2 ^ (k - 1))) = - F ^ (2 ^ (k - 1)) := by
    rw [map_pow, hσF, mul_pow, hζ]; ring
  have hfac : (b - F ^ (2 ^ (k - 1))) * (b + F ^ (2 ^ (k - 1))) = 0 := by
    have h2 : b ^ (2 : ℕ) = (F ^ (2 ^ (k - 1))) ^ (2 : ℕ) := by rw [hbsq, hFsq]
    linear_combination h2
  rcases mul_eq_zero.mp hfac with h | h
  · have hbeq : b = F ^ (2 ^ (k - 1)) := by linear_combination h
    rw [hbeq, hσFpow] at hb
    have h2x : (2 : V) * F ^ (2 ^ (k - 1)) = 0 := by linear_combination -hb
    rcases mul_eq_zero.mp h2x with h0 | h0
    · exact absurd h0 (by norm_num)
    · exact pow_ne_zero _ hF h0
  · have hbeq : b = - F ^ (2 ^ (k - 1)) := by linear_combination h
    rw [hbeq, map_neg, hσFpow] at hb
    have h2x : (2 : V) * F ^ (2 ^ (k - 1)) = 0 := by linear_combination hb
    rcases mul_eq_zero.mp h2x with h0 | h0
    · exact absurd h0 (by norm_num)
    · exact pow_ne_zero _ hF h0

end Bottcher
