import GaloisForLFunctions.HTGeometry.TwistedInhomogeneousReduction

/-!
# The rank law for a diagonalizable curved source datum

An affine source law with a base-diagonalizable adjoint local system is carried, by the gauge
groupoid, into a family of scalar affine laws; if the gauged increments have a base particular
solution, each of those is homogenized and then flattened by logarithmic differentiation.  The
gauge and the base translation are both invisible to the differential matroid, so the rank of the
original observables is computed by the flat source-boundary theory applied to the logarithmic
derivatives of the diagonal entries.

This closes the curved rank problem for every datum whose adjoint local system is diagonalizable
over the base and whose gauged increments are base coboundaries for the diagonal twist.  What is
left genuinely open is a local system that is not diagonalizable over the base, or a diagonal one
whose increments carry a nontrivial twisted class.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

variable {κ : Type u} [Fintype κ]

/-- **The curved rank law for a diagonalizable adjoint local system.**  If a base gauge `P`
diagonalizes the adjoint local system with entries `m_(i,p)`, and the gauged increments have a
base particular solution `b`, then the differential rank of the observables themselves equals the
`C[D]`-rank of the span of the boundary classes of the logarithmic derivatives of `m_(i,p)`. -/
theorem diagonalizableCurved_eRk_eq_rank_span_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i w, sigma i w′ = (sigma i w)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] [CharZero L] [DecidableEq κ]
    {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    {m : I → κ → K}
    (hdiag : ∀ i p q, gaugeLinearPart tau P Q M i p q = if p = q then m i p else 0)
    {b : κ → K}
    (hbase : ∀ i p, tau i (b p) = m i p * b p + gaugeIncrement tau P om i p)
    (hy : ∀ p, baseTranslate (gaugeFamily P z) b p ≠ 0) (hm : ∀ i p, m i p ≠ 0) :
    ∃ r : ℕ,
      (differentialMatroid K L).eRk (Set.range z) = r ∧
      Module.rank (Polynomial C) (Submodule.span (Polynomial C)
        (Set.range fun p : κ =>
          boundaryClass tau hC hfix hderiv fun i => logDerivTwist m i p)) = r := by
  obtain ⟨r, hrk, hrank⟩ := twistedInhomogeneous_eRk_eq_rank_span_boundaryClass tau sigma hcomp
    hderivL hCfixed hfixed hC hfix hderiv
    (gauge_shift_scalar_of_diagonal tau sigma hshift hcomp hinv hdiag) hbase hy hm
  exact ⟨r, (eRk_gaugeFamily hinv z).symm.trans hrk, hrank⟩

/-- **The curved independence criterion for a diagonalizable adjoint local system.**  After the
gauge, the base translation and the logarithmic derivative, differential independence of the
observables is linear independence over `C[D]` of the boundary classes of the logarithmic
derivatives of the diagonal entries. -/
theorem diagonalizableCurved_differentialIndependent_iff
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i w, sigma i w′ = (sigma i w)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ w : L, (∀ i, sigma i w = w) → ∃ c : C, algebraMap C L c = w)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    [CharZero K] [DecidableEq κ]
    {z : κ → L} {M : I → κ → κ → K} {om : I → κ → K}
    (hshift : ∀ i p, sigma i (z p)
      = (∑ q, algebraMap K L (M i p q) * z q) + algebraMap K L (om i p))
    {P Q : κ → κ → K}
    (hinv : ∀ p q, (∑ r, Q p r * P r q) = if p = q then 1 else 0)
    {m : I → κ → K}
    (hdiag : ∀ i p q, gaugeLinearPart tau P Q M i p q = if p = q then m i p else 0)
    {b : κ → K}
    (hbase : ∀ i p, tau i (b p) = m i p * b p + gaugeIncrement tau P om i p)
    (hy : ∀ p, baseTranslate (gaugeFamily P z) b p ≠ 0) (hm : ∀ i p, m i p ≠ 0) :
    DifferentialIndependent K (logDerivFamily (baseTranslate (gaugeFamily P z) b)) ↔
      LinearIndependent (Polynomial C)
        (fun p : κ => boundaryClass tau hC hfix hderiv fun i => logDerivTwist m i p) :=
  twistedInhomogeneous_differentialIndependent_iff tau sigma hcomp hderivL hCfixed hfixed hC hfix
    hderiv (gauge_shift_scalar_of_diagonal tau sigma hshift hcomp hinv hdiag) hbase hy hm

end

end GaloisForLFunctions.HTGeometry
