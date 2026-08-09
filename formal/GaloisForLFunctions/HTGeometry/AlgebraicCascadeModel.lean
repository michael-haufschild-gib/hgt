import GaloisForLFunctions.HTGeometry.AdjoinRootDerivation
import GaloisForLFunctions.HTGeometry.CoordinateDerivationCommute

/-!
# The model for a cascade whose derivative law is algebraic

When the derivative law of a cascade is not solved for the derivative, the factor at level `k`
satisfies a polynomial equation of degree at least two in the derivative, so it is algebraic over
the coordinate field and does not lie in `CascadeField`.  The model is then a simple algebraic
extension `CascadeField[X]/(p)` with `p` irreducible.

Everything the peel uses on the base transports:

* every coordinate derivation extends, in exactly one way (`afpderiv`, `eq_afpderiv`);
* the extended coordinate derivations still commute (`afpderiv_comm`), which is the exactness the
  border row of the peel rests on;
* the extension is a finite field extension, so the degree-at-infinity has a finite ramification
  index to work with.

`CascadeField` has characteristic zero, so an irreducible polynomial over it is separable and the
extension is separable; that is what makes the extension of a derivation unique.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable (p : Polynomial CascadeField) [Fact (Irreducible p)]

/-- The field a cascade with an algebraic derivative law lives in. -/
abbrev AlgCascadeField : Type := AdjoinRoot p

/-- The extension of a coordinate derivation to the algebraic model. -/
noncomputable def afpderiv (k : ℕ) : Derivation ℂ (AlgCascadeField p) (AlgCascadeField p) :=
  adjoinRootDeriv (fpderiv k) p

@[simp]
theorem afpderiv_algebraMap (k : ℕ) (f : CascadeField) :
    afpderiv p k (algebraMap CascadeField (AlgCascadeField p) f)
      = algebraMap CascadeField (AlgCascadeField p) (fpderiv k f) :=
  adjoinRootDeriv_algebraMap _ _

@[simp]
theorem afpderiv_root (k : ℕ) :
    afpderiv p k (AdjoinRoot.root p) = rootShift (fpderiv k) p :=
  adjoinRootDeriv_root _

/-- **The extension is the only one.** -/
theorem eq_afpderiv (k : ℕ) (D : Derivation ℂ (AlgCascadeField p) (AlgCascadeField p))
    (hD : ∀ f : CascadeField, D (algebraMap CascadeField (AlgCascadeField p) f)
      = algebraMap CascadeField (AlgCascadeField p) (fpderiv k f)) :
    D = afpderiv p k :=
  eq_adjoinRootDeriv _ _ hD

theorem fpderiv_commutator_eq_zero (k l : ℕ) :
    ⁅fpderiv k, fpderiv l⁆ = (0 : Derivation ℂ CascadeField CascadeField) := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [Derivation.commutator_apply, fpderiv_comm, sub_self, Derivation.zero_apply]

/-- **The extended coordinate derivations still commute.** -/
theorem afpderiv_comm (k l : ℕ) (x : AlgCascadeField p) :
    afpderiv p k (afpderiv p l x) = afpderiv p l (afpderiv p k x) := by
  have h : ⁅afpderiv p k, afpderiv p l⁆ = 0 :=
    adjoinRootDeriv_commutator (p := p) (fpderiv k) (fpderiv l) (fpderiv_commutator_eq_zero k l)
  have hx : ⁅afpderiv p k, afpderiv p l⁆ x = 0 := by rw [h, Derivation.zero_apply]
  rw [Derivation.commutator_apply] at hx
  exact sub_eq_zero.mp hx

/-! ## The extension of an arbitrary law, and its compatibility with the coordinates -/

/-- The extension of a derivation of the coordinate field to the algebraic model. -/
noncomputable def algLaw (D : Derivation ℂ CascadeField CascadeField) :
    Derivation ℂ (AlgCascadeField p) (AlgCascadeField p) :=
  adjoinRootDeriv D p

@[simp]
theorem algLaw_algebraMap (D : Derivation ℂ CascadeField CascadeField) (f : CascadeField) :
    algLaw p D (algebraMap CascadeField (AlgCascadeField p) f)
      = algebraMap CascadeField (AlgCascadeField p) (D f) :=
  adjoinRootDeriv_algebraMap _ _

/-- **A law that commutes with a coordinate derivation downstairs still does upstairs.**  This is
the exactness of the border row, transported to the algebraic model. -/
theorem algLaw_afpderiv_comm (D : Derivation ℂ CascadeField CascadeField) (k : ℕ)
    (h : ∀ f : CascadeField, D (fpderiv k f) = fpderiv k (D f)) (x : AlgCascadeField p) :
    algLaw p D (afpderiv p k x) = afpderiv p k (algLaw p D x) := by
  have hcomm : ⁅D, fpderiv k⁆ = (0 : Derivation ℂ CascadeField CascadeField) := by
    refine DFunLike.ext _ _ fun f => ?_
    rw [Derivation.commutator_apply, h, sub_self, Derivation.zero_apply]
  have hx : ⁅algLaw p D, afpderiv p k⁆ x = 0 := by
    rw [adjoinRootDeriv_commutator (p := p) D (fpderiv k) hcomm, Derivation.zero_apply]
  rw [Derivation.commutator_apply] at hx
  exact sub_eq_zero.mp hx

/-! ## The extension is finite -/

theorem algCascadeField_finiteDimensional :
    FiniteDimensional CascadeField (AlgCascadeField p) :=
  PowerBasis.finite (AdjoinRoot.powerBasis (Fact.out : Irreducible p).ne_zero)

theorem algebraMap_injective :
    Function.Injective (algebraMap CascadeField (AlgCascadeField p)) :=
  (algebraMap CascadeField (AlgCascadeField p)).injective

end GaloisForLFunctions.HTGeometry
