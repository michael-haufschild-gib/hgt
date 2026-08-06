import GaloisForLFunctions.HTGeometry.CommutativeDGroupObservable
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# The source boundary of a commutative `D`-group observable

A family of points of a commutative algebraic `D`-group translated by a source family of
base points has logarithmic coordinates which shift by the logarithmic coordinates of the
translating points: the group homomorphism law of the logarithmic derivative turns the
multiplicative source recurrence into an additive one, in every source direction at once.

The arbitrary-family additive source theorem then computes the differential independence of the
logarithmic coordinate family exactly, and the rank identity of the previous module transfers the
answer back to the coordinates of the points themselves.  The source family is not assumed to
commute.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {G : Type*} [CommGroup G] {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L] {n d : ℕ}

/-- The source datum of a family of `D`-group observables: an action of the source family on the
points which is equivariant for the logarithmic derivative, together with the base translations
realising the source recurrence and their logarithmic coordinates. -/
structure DGroupSourceData (P : DGroupPresentation G K L n d) {I S : Type*}
    (sigma : I → L ≃+* L) (g : S → G) where
  /-- The action of the source family on the points. -/
  act : I → G → G
  /-- Equivariance of the logarithmic derivative. -/
  act_ell : ∀ (i : I) (x : G) (j : Fin d), P.ell (act i x) j = sigma i (P.ell x j)
  /-- The translating points of the source recurrence. -/
  mult : I → S → G
  /-- The source recurrence itself. -/
  recurrence : ∀ (i : I) (a : S), act i (g a) = mult i a * g a
  /-- The logarithmic coordinates of the translating points, over the base field. -/
  omega : I → S → Fin d → K
  /-- They are the logarithmic coordinates of the translating points. -/
  omega_spec : ∀ (i : I) (a : S) (j : Fin d),
    algebraMap K L (omega i a j) = P.ell (mult i a) j

namespace DGroupSourceData

variable {P : DGroupPresentation G K L n d} {I S : Type*} {sigma : I → L ≃+* L} {g : S → G}

/-- The source increments of the whole logarithmic-coordinate family. -/
def omegaFamily (D : DGroupSourceData P sigma g) (i : I) : S × Fin d → K :=
  fun p => D.omega i p.1 p.2

/-- **Equation `(3)`: the logarithmic coordinates shift additively.**  The multiplicative source
recurrence of the points becomes an additive source recurrence of their logarithmic coordinates,
because the logarithmic derivative of a commutative `D`-group is a homomorphism. -/
theorem sigma_ellFamily (D : DGroupSourceData P sigma g) (i : I) (p : S × Fin d) :
    sigma i (P.ellFamily g p) = P.ellFamily g p + algebraMap K L (D.omegaFamily i p) := by
  have hact : P.ell (D.act i (g p.1)) p.2 = sigma i (P.ell (g p.1) p.2) :=
    D.act_ell i (g p.1) p.2
  rw [D.recurrence i p.1, P.ell_mul] at hact
  show sigma i (P.ell (g p.1) p.2)
    = P.ell (g p.1) p.2 + algebraMap K L (D.omega i p.1 p.2)
  rw [← hact, D.omega_spec]
  show (P.ell (D.mult i p.1) + P.ell (g p.1)) p.2
    = P.ell (g p.1) p.2 + P.ell (D.mult i p.1) p.2
  rw [Pi.add_apply]
  ring

end DGroupSourceData

/-! ### The exact source-boundary criterion -/

/-- **Theorem B, criterion form.**  The logarithmic coordinates of a family of commutative
`D`-group observables are differentially independent over the base exactly when no nonzero finite
differential character of their source increments is one simultaneous base coboundary in every
source direction. -/
theorem dGroupSource_ellFamily_differentialIndependent_iff
    {C : Type u} [Field C] [Algebra C K] [Algebra C L] [IsScalarTower C K L] [CharZero K]
    {I S : Type*} (tau : I → K ≃+* K) (sigma : I → L ≃+* L)
    (hcomp : ∀ i k, sigma i (algebraMap K L k) = algebraMap K L (tau i k))
    (hderiv : ∀ i y, sigma i y′ = (sigma i y)′)
    (hCfixed : ∀ i c, sigma i (algebraMap C L c) = algebraMap C L c)
    (hfixed : ∀ z : L, (∀ i, sigma i z = z) → ∃ c : C, algebraMap C L c = z)
    {P : DGroupPresentation G K L n d} {g : S → G}
    (D : DGroupSourceData P sigma g) :
    DifferentialIndependent K (P.ellFamily g) ↔
      ∀ c : ((S × Fin d) × ℕ) →₀ C, c ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          Finsupp.linearCombination K
            (fun p ↦ differentialJet p.2 (D.omegaFamily i p.1))
            (Finsupp.mapRange (algebraMap C K)
              (map_zero (algebraMap C K)) c) :=
  GaloisForLFunctions.automorphismFamily_differentialIndependent_iff_no_constant_simultaneous_jet_telescoping
    tau sigma hcomp hderiv hCfixed hfixed (P.ellFamily g) D.omegaFamily
    (fun i p => D.sigma_ellFamily i p)

/-- **Theorem B for the points themselves.**  The differential rank of the coordinates of the
family equals the differential rank of its logarithmic coordinates, which the source-boundary
criterion computes. -/
theorem dGroupSource_eRk_coordFamily_eq [CharZero L]
    {P : DGroupPresentation G K L n d} {S : Type u} [Fintype S] (g : S → G) :
    (differentialMatroid K L).eRk (Set.range (P.coordFamily g))
      = (differentialMatroid K L).eRk (Set.range (P.ellFamily g)) :=
  P.eRk_coordFamily_eq_ellFamily g

end

end GaloisForLFunctions.HTGeometry
