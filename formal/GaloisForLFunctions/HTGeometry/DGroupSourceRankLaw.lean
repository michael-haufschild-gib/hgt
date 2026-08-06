import GaloisForLFunctions.HTGeometry.DGroupSourceBoundary
import GaloisForLFunctions.HTGeometry.SourceCoboundaryOperatorBridge

/-!
# The complete source-boundary rank law

Differential independence of a family of observables which shift by base increments in every
source direction is exactly linear independence, over the constant-coefficient differential
operators, of the boundary classes of those increments.

For a family of points of a commutative algebraic `D`-group this identifies the whole differential
polymatroid of the observables with the linear polymatroid of the boundary classes of their
logarithmic source increments, and the rank identity of the logarithmic linearization transports
the answer to the coordinates of the points themselves.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K L : Type u} [Field C] [Field K] [Field L]
  [Algebra C K] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L] [CharZero K]
  {I : Type u} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)

/-- **The master source-boundary law.**  A family of observables shifting by base increments in
every source direction is differentially independent exactly when the boundary classes of those
increments are linearly independent over the constant-coefficient differential operators. -/
theorem differentialIndependent_iff_linearIndependent_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C L c = z)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {κ : Type u} (z : κ → L) (omega : I → κ → K)
    (hshift : ∀ i p, sigma i (z p) = z p + algebraMap K L (omega i p)) :
    DifferentialIndependent K z ↔
      LinearIndependent (Polynomial C)
        (fun p : κ => boundaryClass tau hC hfix hderiv fun i => omega i p) := by
  rw [linearIndependent_boundaryClass_iff tau hC hfix hderiv omega,
    operator_criterion_iff_jet_criterion tau hC omega]
  exact
    GaloisForLFunctions.automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
      tau sigma hcomp hderivL hCfixed hfixed z omega hshift

variable {G : Type*} [CommGroup G] {n d : ℕ}

/-- **Theorem B for a commutative `D`-group family.**  The logarithmic coordinates of the family
are differentially independent exactly when the boundary classes of their logarithmic source
increments are linearly independent over `C[D]`. -/
theorem dGroup_differentialIndependent_iff_linearIndependent_boundaryClass
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C L c = z)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {P : DGroupPresentation G K L n d} {S : Type u} {g : S → G}
    (Dat : DGroupSourceData P sigma g) :
    DifferentialIndependent K (P.ellFamily g) ↔
      LinearIndependent (Polynomial C)
        (fun p : S × Fin d =>
          boundaryClass tau hC hfix hderiv fun i => Dat.omegaFamily i p) :=
  differentialIndependent_iff_linearIndependent_boundaryClass tau sigma hcomp hderivL hCfixed
    hfixed hC hfix hderiv (P.ellFamily g) Dat.omegaFamily
    (fun i p => Dat.sigma_ellFamily i p)

/-- **The polymatroid form of the rank law.**  For every subfamily of the observables — that is,
for every reindexing — differential independence of the logarithmic coordinates is linear
independence of the corresponding boundary classes. -/
theorem dGroup_subfamily_differentialIndependent_iff
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C L c = z)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {P : DGroupPresentation G K L n d} {S : Type u} {g : S → G}
    (Dat : DGroupSourceData P sigma g) {T : Type u} (e : T → S × Fin d) :
    DifferentialIndependent K (fun t : T => P.ellFamily g (e t)) ↔
      LinearIndependent (Polynomial C)
        (fun t : T =>
          boundaryClass tau hC hfix hderiv fun i => Dat.omegaFamily i (e t)) :=
  differentialIndependent_iff_linearIndependent_boundaryClass tau sigma hcomp hderivL hCfixed
    hfixed hC hfix hderiv (fun t => P.ellFamily g (e t)) (fun i t => Dat.omegaFamily i (e t))
    (fun i t => Dat.sigma_ellFamily i (e t))

/-- **The complete source-boundary universality theorem.**  For a family of points of a
commutative algebraic `D`-group with an arbitrary, possibly noncommuting source family: the
coordinates of the points and their logarithmic coordinates have the same differential rank, and
that rank is the linear rank of the boundary classes of the logarithmic source increments. -/
theorem dGroup_sourceBoundary_universality [CharZero L]
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderivL : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C L c = z)
    (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′)
    {P : DGroupPresentation G K L n d} {S : Type u} [Fintype S] {g : S → G}
    (Dat : DGroupSourceData P sigma g) :
    (differentialMatroid K L).eRk (Set.range (P.coordFamily g))
        = (differentialMatroid K L).eRk (Set.range (P.ellFamily g)) ∧
      ∀ T : Type u, ∀ e : T → S × Fin d,
        (DifferentialIndependent K (fun t : T => P.ellFamily g (e t)) ↔
          LinearIndependent (Polynomial C)
            (fun t : T =>
              boundaryClass tau hC hfix hderiv fun i => Dat.omegaFamily i (e t))) :=
  ⟨P.eRk_coordFamily_eq_ellFamily g,
    fun _ e => dGroup_subfamily_differentialIndependent_iff tau sigma hcomp hderivL hCfixed
      hfixed hC hfix hderiv Dat e⟩

end

end GaloisForLFunctions.HTGeometry
