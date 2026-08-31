import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion

/-!
# Transferring an observability Jacobian along a differential specialization

A morphism of differential algebras that also intertwines the coordinate derivations carries the
observability Jacobian to the observability Jacobian.  A nonzero image therefore certifies a nonzero
source, so algebraic independence of the time jets can be read off any specialization in which the
model is easier — the Newton-corner degeneration being the intended one.
-/

open Matrix

namespace GaloisForLFunctions.HTGeometry

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] {m : ℕ}

/-- The observability Jacobian of the first `m + 1` time jets of `x` against `m + 1` coordinate
derivations. -/
def observabilityJacobian (δ : R → R) (P : Fin (m + 1) → R → R) (x : R) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Matrix.of fun i j => P j ((δ^[(i : ℕ)]) x)

/-- **Specialization transfers the Jacobian.**  A `ℂ`-algebra map intertwining the time derivation
and every coordinate derivation carries the observability Jacobian to the observability Jacobian. -/
theorem map_observabilityJacobian (π : R →ₐ[ℂ] S)
    {δR : R → R} {δS : S → S} (hδ : ∀ y, π (δR y) = δS (π y))
    {pR : Fin (m + 1) → R → R} {pS : Fin (m + 1) → S → S}
    (hP : ∀ j y, π (pR j y) = pS j (π y)) (x : R) (i j : Fin (m + 1)) :
    π (observabilityJacobian δR pR x i j)
      = observabilityJacobian δS pS (π x) i j := by
  have hiter : ∀ k : ℕ, π ((δR^[k]) x) = (δS^[k]) (π x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hδ, ih]
  simp only [observabilityJacobian, Matrix.of_apply]
  rw [hP, hiter]

/-- **A nonzero specialized Jacobian certifies a nonzero Jacobian.** -/
theorem observabilityJacobian_det_ne_zero_of_map (π : R →ₐ[ℂ] S)
    {δR : R → R} {δS : S → S} (hδ : ∀ y, π (δR y) = δS (π y))
    {pR : Fin (m + 1) → R → R} {pS : Fin (m + 1) → S → S}
    (hP : ∀ j y, π (pR j y) = pS j (π y)) (x : R)
    (hS : (observabilityJacobian δS pS (π x)).det ≠ 0) :
    (observabilityJacobian δR pR x).det ≠ 0 := by
  intro hzero
  apply hS
  have hmap : (observabilityJacobian δS pS (π x))
      = (observabilityJacobian δR pR x).map (π : R →+* S) := by
    funext i j
    rw [Matrix.map_apply]
    exact (map_observabilityJacobian π hδ hP x i j).symm
  rw [hmap]
  have hdet : ((observabilityJacobian δR pR x).map (π : R →+* S)).det
      = (π : R →+* S) ((observabilityJacobian δR pR x).det) :=
    (RingHom.map_det (π : R →+* S) _).symm
  rw [hdet, hzero, map_zero]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S] {m : ℕ}

/-- **Weighted specialization transfers the Jacobian up to a row-column rescaling.** -/
theorem map_observabilityJacobian_weighted (π : R →ₐ[ℂ] S)
    {δR : R → R} {δS : S → S} {c : S}
    (hδ : ∀ y, π (δR y) = c * δS (π y)) (hcδ : ∀ y, δS (c * y) = c * δS y)
    {pR : Fin (m + 1) → R → R} {pS : Fin (m + 1) → S → S} {d : Fin (m + 1) → S}
    (hP : ∀ j y, π (pR j y) = d j * pS j (π y))
    (hcp : ∀ j y, pS j (c * y) = c * pS j y) (x : R) (i j : Fin (m + 1)) :
    π (observabilityJacobian δR pR x i j)
      = c ^ (i : ℕ) * d j * observabilityJacobian δS pS (π x) i j := by
  have hcδpow : ∀ (k : ℕ) (y : S), δS (c ^ k * y) = c ^ k * δS y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
        intro y
        have hrw : c ^ (k + 1) * y = c * (c ^ k * y) := by ring
        rw [hrw, hcδ, ih, pow_succ]
        ring
  have hiter : ∀ k : ℕ, π ((δR^[k]) x) = c ^ k * (δS^[k]) (π x) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hδ, ih, hcδpow, pow_succ]
        ring
  have hcpow : ∀ (k : ℕ) (y : S), pS j (c ^ k * y) = c ^ k * pS j y := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
        intro y
        have hrw : c ^ (k + 1) * y = c * (c ^ k * y) := by ring
        rw [hrw, hcp, ih, pow_succ]
        ring
  simp only [observabilityJacobian, Matrix.of_apply]
  rw [hP, hiter, hcpow]
  ring

/-- **A nonzero weighted-specialized Jacobian certifies a nonzero Jacobian.** -/
theorem observabilityJacobian_det_ne_zero_of_weighted_map [IsDomain S] (π : R →ₐ[ℂ] S)
    {δR : R → R} {δS : S → S} {c : S} (hc : c ≠ 0)
    (hδ : ∀ y, π (δR y) = c * δS (π y)) (hcδ : ∀ y, δS (c * y) = c * δS y)
    {pR : Fin (m + 1) → R → R} {pS : Fin (m + 1) → S → S} {d : Fin (m + 1) → S}
    (hd : ∀ j, d j ≠ 0)
    (hP : ∀ j y, π (pR j y) = d j * pS j (π y))
    (hcp : ∀ j y, pS j (c * y) = c * pS j y) (x : R)
    (hS : (observabilityJacobian δS pS (π x)).det ≠ 0) :
    (observabilityJacobian δR pR x).det ≠ 0 := by
  intro hzero
  set N : Matrix (Fin (m + 1)) (Fin (m + 1)) S :=
    Matrix.of fun a b => d b * observabilityJacobian δS pS (π x) a b with hN
  have hmap : ((observabilityJacobian δR pR x).map (π : R →+* S))
      = Matrix.of fun a b => c ^ a.val * N a b := by
    funext a b
    rw [Matrix.map_apply]
    show π (observabilityJacobian δR pR x a b) = _
    rw [map_observabilityJacobian_weighted π hδ hcδ hP hcp x a b, hN]
    simp only [Matrix.of_apply]
    ring
  have hdet0 : ((observabilityJacobian δR pR x).map (π : R →+* S)).det
      = (π : R →+* S) ((observabilityJacobian δR pR x).det) :=
    (RingHom.map_det (π : R →+* S) _).symm
  have hdet : ((observabilityJacobian δR pR x).map (π : R →+* S)).det = 0 := by
    rw [hdet0, hzero, map_zero]
  rw [hmap, Matrix.det_mul_column] at hdet
  rw [hN, Matrix.det_mul_row] at hdet
  have hcprod : (∏ i : Fin (m + 1), c ^ i.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ hc
  have hdprod : (∏ j : Fin (m + 1), d j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hd j
  rcases mul_eq_zero.mp hdet with h | h
  · exact hcprod h
  · rcases mul_eq_zero.mp h with h1 | h2
    · exact hdprod h1
    · exact hS h2

end GaloisForLFunctions.HTGeometry
