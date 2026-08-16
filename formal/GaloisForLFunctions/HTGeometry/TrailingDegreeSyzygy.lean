import Mathlib

/-!
# Trailing degree kills a low product modulo the horizon

Two facts about polynomials over a domain, both used to show that a syzygy between two states over
the same branch value forces the states to coincide.

The first is the multiplicativity of trailing degree: a nonzero factor of degree below `m` times a
factor with a nonzero coefficient at `n` has a nonzero coefficient strictly below `m + n`, so the
product is not divisible by `X^(m+n)`.  This is what converts "the two states differ" into a
contradiction with the compatibility equation, and it needs no hypothesis on the second factor
beyond one nonvanishing coefficient.

The second is Euclid's lemma in the shape a syzygy produces it: `D V + E U = 0` with `U, V` coprime
forces `D = C U` and `E = −C V` for a single cofactor `C`.
-/

noncomputable section

open Polynomial

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Trailing degree obstructs divisibility by the horizon.**  A nonzero polynomial of degree below
`m` multiplied by one with a nonzero coefficient at `n` has a nonzero coefficient strictly below
`m + n`. -/
theorem not_X_pow_dvd_mul_of_trailing {f g : R[X]} {m n : ℕ}
    (hf : f ≠ 0) (hfdeg : f.natDegree < m) (hg : g.coeff n ≠ 0) :
    ¬ (X : R[X]) ^ (m + n) ∣ f * g := by
  intro hdvd
  have hg0 : g ≠ 0 := by
    intro h
    rw [h] at hg
    simp at hg
  have htf : f.natTrailingDegree ≤ f.natDegree := natTrailingDegree_le_natDegree f
  have htg : g.natTrailingDegree ≤ n := natTrailingDegree_le_of_ne_zero hg
  have hlt : f.natTrailingDegree + g.natTrailingDegree < m + n := by omega
  have hne : (f * g).trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.2 (mul_ne_zero hf hg0)
  have hval : (f * g).trailingCoeff
      = (f * g).coeff (f.natTrailingDegree + g.natTrailingDegree) := by
    rw [Polynomial.trailingCoeff, natTrailingDegree_mul hf hg0]
  rw [hval] at hne
  exact hne ((X_pow_dvd_iff.1 hdvd) _ hlt)

/-- **The low factor of a horizon-divisible product vanishes.**  Contrapositive of the previous
statement: if the product *is* divisible by the horizon, the low factor is zero. -/
theorem eq_zero_of_X_pow_dvd_mul {f g : R[X]} {m n : ℕ}
    (hfdeg : f.natDegree < m) (hg : g.coeff n ≠ 0)
    (hdvd : (X : R[X]) ^ (m + n) ∣ f * g) : f = 0 := by
  by_contra hf
  exact not_X_pow_dvd_mul_of_trailing hf hfdeg hg hdvd

/-- **Euclid's lemma in syzygy form.**  A syzygy between coprime polynomials has a single
cofactor. -/
theorem exists_cofactor_of_syzygy {U V D E : R[X]}
    (huv : IsCoprime U V) (hU : U ≠ 0) (h : D * V + E * U = 0) :
    ∃ C : R[X], D = C * U ∧ E = -(C * V) := by
  have hdvd : U ∣ D * V := ⟨-E, by linear_combination h⟩
  obtain ⟨C, hC⟩ := huv.dvd_of_dvd_mul_right hdvd
  refine ⟨C, by rw [hC]; ring, ?_⟩
  have hcancel : E * U = -(C * V) * U := by
    rw [hC] at h
    linear_combination h
  exact mul_right_cancel₀ hU hcancel

/-- **Two low states over the same value coincide.**  If the difference of the two states is low and
the marked tail has a nonzero coefficient at the second depth, the difference vanishes. -/
theorem eq_of_low_difference {A A' T : R[X]} {m n : ℕ}
    (hdeg : (A' - A).natDegree < m) (hT : T.coeff n ≠ 0)
    (hdvd : (X : R[X]) ^ (m + n) ∣ (A' - A) * T) : A' = A :=
  sub_eq_zero.1 (eq_zero_of_X_pow_dvd_mul hdeg hT hdvd)

end GaloisForLFunctions.HTGeometry

end
