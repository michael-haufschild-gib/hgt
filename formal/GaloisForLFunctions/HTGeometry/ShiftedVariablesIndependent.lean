import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Shifting an independent family by constants

Adding constants to an algebraically independent family leaves it independent: the shift is a
polynomial automorphism, so composing with it cannot create a relation.

Together with the independence of the variables of a multivariate power series ring — inherited from
the polynomial ring, which embeds in it — this is what makes a deformed observation as generic as an
undeformed one when the deformation is an affine change of the deformation parameters.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

/-- **An independent family stays independent after adding constants.** -/
theorem algebraicIndependent_add_const {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    {f : ι → A} (hf : AlgebraicIndependent K f) (c : ι → K) :
    AlgebraicIndependent K (fun i => f i + algebraMap K A (c i)) := by
  classical
  rw [algebraicIndependent_iff_injective_aeval] at hf ⊢
  set shift : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (c i)) with hshiftdef
  set unshift : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
    MvPolynomial.aeval (fun i => MvPolynomial.X i - MvPolynomial.C (c i)) with hunshiftdef
  have hcomp : (MvPolynomial.aeval (fun i => f i + algebraMap K A (c i)) :
      MvPolynomial ι K →ₐ[K] A) = (MvPolynomial.aeval f).comp shift := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    rw [hshiftdef]
    simp
  have hinv : unshift.comp shift = AlgHom.id K (MvPolynomial ι K) := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    rw [hshiftdef, hunshiftdef]
    simp
  have hleft : Function.LeftInverse (unshift : MvPolynomial ι K → MvPolynomial ι K) shift := by
    intro p
    have := congrArg (fun F : MvPolynomial ι K →ₐ[K] MvPolynomial ι K => F p) hinv
    simpa using this
  rw [hcomp, AlgHom.coe_comp]
  exact hf.comp hleft.injective

/-- **The variables of a multivariate power series ring are algebraically independent.** -/
theorem algebraicIndependent_mvPowerSeries_X {K σ : Type*} [Field K] :
    AlgebraicIndependent K (MvPowerSeries.X : σ → MvPowerSeries σ K) := by
  rw [algebraicIndependent_iff_injective_aeval]
  have hcoe : ∀ p : MvPolynomial σ K,
      (MvPolynomial.aeval (MvPowerSeries.X : σ → MvPowerSeries σ K)) p
        = (p : MvPowerSeries σ K) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  intro p q hpq
  rw [hcoe, hcoe] at hpq
  exact MvPolynomial.coe_injective σ K hpq

end GaloisForLFunctions.HTGeometry
