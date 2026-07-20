import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Scalar extension of multivariate-polynomial algebra maps

A polynomial algebra endomorphism over a base semiring extends canonically to every commutative
scalar algebra by applying the old map to the variables and fixing the new coefficient ring.  The
extension is natural on old-base polynomials, respects composition, and carries every polynomial
algebra automorphism to an actual ring automorphism after arbitrary scalar extension.

The injectivity statement is proved by extending the inverse automorphism and using functoriality;
it requires no flatness hypothesis and is the reusable interface needed by nonlinear value
coordinate changes over enlarged coefficient fields.
-/

open MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Extend a polynomial algebra homomorphism along a scalar map while fixing the new
coefficient ring. -/
def mvPolynomialAlgHomBaseChange
    {k K σ τ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) :
    MvPolynomial σ K →ₐ[K] MvPolynomial τ K where
  toRingHom := MvPolynomial.eval₂Hom MvPolynomial.C fun i =>
    MvPolynomial.map (algebraMap k K) (f (MvPolynomial.X i))
  commutes' c := by simp

@[simp] theorem mvPolynomialAlgHomBaseChange_C
    {k K σ τ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) (c : K) :
    mvPolynomialAlgHomBaseChange f (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [mvPolynomialAlgHomBaseChange]

@[simp] theorem mvPolynomialAlgHomBaseChange_X
    {k K σ τ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) (i : σ) :
    mvPolynomialAlgHomBaseChange f (MvPolynomial.X i) =
      MvPolynomial.map (algebraMap k K) (f (MvPolynomial.X i)) := by
  simp [mvPolynomialAlgHomBaseChange]

/-- Scalar extension is natural on polynomials whose coefficients still lie in the old base. -/
theorem mvPolynomialAlgHomBaseChange_map
    {k K σ τ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k)
    (P : MvPolynomial σ k) :
    mvPolynomialAlgHomBaseChange f
        (MvPolynomial.map (algebraMap k K) P) =
      MvPolynomial.map (algebraMap k K) (f P) := by
  let lhs : MvPolynomial σ k →+* MvPolynomial τ K :=
    (mvPolynomialAlgHomBaseChange f).toRingHom.comp
      (MvPolynomial.map (algebraMap k K))
  let rhs : MvPolynomial σ k →+* MvPolynomial τ K :=
    (MvPolynomial.map (algebraMap k K)).comp f.toRingHom
  have h : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lhs, rhs]
    · intro i
      simp [lhs, rhs]
  exact RingHom.congr_fun h P

/-- Scalar extension respects composition of polynomial algebra homomorphisms. -/
theorem mvPolynomialAlgHomBaseChange_comp
    {k K σ τ υ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (g : MvPolynomial τ k →ₐ[k] MvPolynomial υ k)
    (f : MvPolynomial σ k →ₐ[k] MvPolynomial τ k) :
    mvPolynomialAlgHomBaseChange (K := K) (g.comp f) =
      (mvPolynomialAlgHomBaseChange (K := K) g).comp
        (mvPolynomialAlgHomBaseChange (K := K) f) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [mvPolynomialAlgHomBaseChange_map]

@[simp] theorem mvPolynomialAlgHomBaseChange_id
    {k K σ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K] :
    mvPolynomialAlgHomBaseChange (AlgHom.id k (MvPolynomial σ k)) =
      AlgHom.id K (MvPolynomial σ K) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

/-- A polynomial automorphism remains injective after arbitrary commutative scalar extension. -/
theorem mvPolynomialAlgHomBaseChange_injective
    {k K σ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k) :
    Function.Injective (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom) := by
  let g := mvPolynomialAlgHomBaseChange (K := K) e.symm.toAlgHom
  have he : e.symm.toAlgHom.comp e.toAlgHom =
      AlgHom.id k (MvPolynomial σ k) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact e.symm_apply_apply (MvPolynomial.X i)
  have hcomp : g.comp (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom) =
      AlgHom.id K (MvPolynomial σ K) := by
    rw [← mvPolynomialAlgHomBaseChange_comp, he,
      mvPolynomialAlgHomBaseChange_id]
  exact (show Function.LeftInverse g
      (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom) from fun P => by
        simpa using AlgHom.congr_fun hcomp P).injective

/-- A polynomial automorphism remains bijective after arbitrary commutative scalar extension. -/
theorem mvPolynomialAlgHomBaseChange_bijective
    {k K σ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k) :
    Function.Bijective (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom) := by
  refine ⟨mvPolynomialAlgHomBaseChange_injective (K := K) e, ?_⟩
  let g := mvPolynomialAlgHomBaseChange (K := K) e.symm.toAlgHom
  have he : e.toAlgHom.comp e.symm.toAlgHom =
      AlgHom.id k (MvPolynomial σ k) := by
    apply MvPolynomial.algHom_ext
    intro i
    exact e.apply_symm_apply (MvPolynomial.X i)
  have hcomp : (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom).comp g =
      AlgHom.id K (MvPolynomial σ K) := by
    rw [← mvPolynomialAlgHomBaseChange_comp, he,
      mvPolynomialAlgHomBaseChange_id]
  exact (show Function.RightInverse g
      (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom) from fun P => by
        simpa using AlgHom.congr_fun hcomp P).surjective

/-- Scalar extension of a polynomial algebra automorphism as an algebra equivalence. -/
noncomputable def mvPolynomialAlgEquivBaseChange
    {k K σ : Type*} [CommSemiring k] [CommSemiring K] [Algebra k K]
    (e : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k) :
    MvPolynomial σ K ≃ₐ[K] MvPolynomial σ K :=
  AlgEquiv.ofBijective (mvPolynomialAlgHomBaseChange (K := K) e.toAlgHom)
    (mvPolynomialAlgHomBaseChange_bijective (K := K) e)

end

end GaloisForLFunctions
