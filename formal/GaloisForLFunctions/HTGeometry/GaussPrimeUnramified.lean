import Mathlib.RingTheory.Polynomial.Quotient
import Mathlib.NumberTheory.RamificationInertia.Ramification

/-!
# The Gauss prime of a polynomial ring is unramified

Extending a prime `q` of `R` to `R[X]` gives the *Gauss prime* `q · R[X]`.  It is prime
(`Ideal.isPrime_map_C_of_isPrime`), its residue ring is `(R ⧸ q)[X]`
(`Ideal.polynomialQuotientEquivQuotientPolynomial`), and — the statement proved here — it is
**unramified** over `q`:

```text
ramificationIdx'_map_C_eq_one
    ** an element of q outside q² stays outside the square of the Gauss prime **
map_C_le_map_C_iff        extending ideals to the polynomial ring reflects inclusion
ramificationIdx'_map_C
    ** the ramification index is UNCHANGED by adjoining a free variable **
```

The proof is that membership in an extended ideal `I · R[X]` is coefficientwise
(`Ideal.mem_map_C_iff`), so contracting the constant coefficient returns the base statement.

This is the algebraic form of "the Gauss valuation has ramification index one", the step that lets an
induction on the number of variables transport unramifiedness from `𝔽[u_k]` back to
`K[u_1, …, u_{k-1}]` — and hence the step a field-theoretic proof of algebraic simple connectedness of
affine space runs on, without ever needing freeness of an integral closure over a multivariable
polynomial ring.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **The Gauss prime is unramified over the base prime.**  Extending a prime to the polynomial ring
does not raise its order: a base element outside the square stays outside the square upstairs,
because membership in an extended ideal is coefficientwise. -/
theorem ramificationIdx'_map_C_eq_one {R : Type*} [CommRing R] {q : Ideal R}
    {π : R} (hπ : π ∈ q) (hπ2 : π ∉ q ^ 2) :
    Ideal.ramificationIdx' q (q.map (C : R →+* Polynomial R)) = 1 := by
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [pow_one]
    exact le_of_eq rfl
  · intro hle
    have hmem : (C π : Polynomial R) ∈ q.map (C : R →+* Polynomial R) :=
      Ideal.mem_map_of_mem _ hπ
    have h2 : (C π : Polynomial R) ∈ (q.map (C : R →+* Polynomial R)) ^ 2 := hle hmem
    rw [← Ideal.map_pow, Ideal.mem_map_C_iff] at h2
    exact hπ2 (by simpa using h2 0)

theorem map_C_le_map_C_iff {R : Type*} [CommRing R] (I J : Ideal R) :
    I.map (C : R →+* Polynomial R) ≤ J.map (C : R →+* Polynomial R) ↔ I ≤ J := by
  constructor
  · intro h a ha
    have hm : (C a : Polynomial R) ∈ J.map (C : R →+* Polynomial R) :=
      h (Ideal.mem_map_of_mem _ ha)
    rw [Ideal.mem_map_C_iff] at hm
    simpa using hm 0
  · exact fun h => Ideal.map_mono h

/-- **The ramification index is unchanged by adjoining a free variable.** -/
theorem ramificationIdx'_map_C {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra (Polynomial R) (Polynomial S)]
    (hcompat : ∀ p : Polynomial R, algebraMap (Polynomial R) (Polynomial S) p
      = Polynomial.map (algebraMap R S) p)
    (q : Ideal R) (Q : Ideal S) :
    Ideal.ramificationIdx' (q.map (C : R →+* Polynomial R))
        (Q.map (C : S →+* Polynomial S))
      = Ideal.ramificationIdx' q Q := by
  have hmapeq : (q.map (C : R →+* Polynomial R)).map
      (algebraMap (Polynomial R) (Polynomial S))
      = (q.map (algebraMap R S)).map (C : S →+* Polynomial S) := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    refine RingHom.ext fun a => ?_
    show algebraMap (Polynomial R) (Polynomial S) (C a) = C (algebraMap R S a)
    rw [hcompat]
    simp
  have hset : {n : ℕ | Ideal.map (algebraMap (Polynomial R) (Polynomial S))
        (q.map (C : R →+* Polynomial R)) ≤ (Q.map (C : S →+* Polynomial S)) ^ n}
      = {n : ℕ | Ideal.map (algebraMap R S) q ≤ Q ^ n} := by
    ext n
    simp only [Set.mem_setOf_eq, hmapeq, ← Ideal.map_pow]
    exact map_C_le_map_C_iff _ _
  unfold Ideal.ramificationIdx'
  rw [hset]

end GaloisForLFunctions.HTGeometry
