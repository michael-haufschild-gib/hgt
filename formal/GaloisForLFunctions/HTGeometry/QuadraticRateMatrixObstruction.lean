import GaloisForLFunctions.HTGeometry.QuadraticRateOrbitPolynomialField
import GaloisForLFunctions.HTGeometry.PolynomialHermitianMatrixProjectiveGenericity
import GaloisForLFunctions.HTGeometry.AnalyticEscapeGenericityTransfer
import GaloisForLFunctions.HTGeometry.AnalyticFiniteProductDomain

/-!
# The quadratic-rate obstruction of a polynomial matrix family

The labeling orbit of a quadratic-rate spectral relation is a symmetric polynomial in the
spectrum, hence a polynomial in the characteristic coefficients, hence -- for a polynomial matrix
family -- a polynomial in the parameters.  This module builds that pullback, evaluates it on a
full simple root packet, and draws the consequence the fixed-shell nonflatness theorem needs:

*one* parameter at which no relabeling of the spectrum satisfies the quadratic-rate relation
already forces the relation to fail somewhere inside every nonempty open set of **real**
parameters.

The multiple `κ` is an arbitrary complex number, which is what distinguishes this from the
rational construction: the fixed-shell theorem meets `κ = b²` with `b` the constant value of a
projective spectral action on a sphere patch.
-/

open Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Elementary symmetric evaluation does not see the coefficient field. -/
theorem eval₂_esymm_rat_eq {I : Type*} [Fintype I] (energy : I → ℂ) (n : ℕ) :
    MvPolynomial.eval₂ (Rat.castHom ℂ) energy (MvPolynomial.esymm I ℚ n)
      = MvPolynomial.eval₂ (RingHom.id ℂ) energy (MvPolynomial.esymm I ℂ n) := by
  rw [show MvPolynomial.eval₂ (Rat.castHom ℂ) energy (MvPolynomial.esymm I ℚ n)
      = MvPolynomial.aeval energy (MvPolynomial.esymm I ℚ n) from rfl,
    show MvPolynomial.eval₂ (RingHom.id ℂ) energy (MvPolynomial.esymm I ℂ n)
      = MvPolynomial.aeval energy (MvPolynomial.esymm I ℂ n) from rfl,
    MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm]

/-- Pull the labeling-orbit obstruction of a quadratic-rate relation through the characteristic
coefficients of a polynomial matrix family. -/
def quadraticRateObstructionPullback {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ)) (c : I → ℂ) (κ : ℂ) : MvPolynomial θ ℂ :=
  MvPolynomial.aeval (matrixCharacteristicElementaryPolynomial M)
    (fieldQuadraticRateCoefficientPolynomial c κ)

/-- **The pullback evaluates to the orbit obstruction of the root packet.** -/
theorem eval_quadraticRateObstructionPullback {θ I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial θ ℂ)) (c : I → ℂ) (κ : ℂ) (z : θ → ℂ)
    (energy : I → ℂ) (hinj : Function.Injective energy)
    (hroot : ∀ i, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) z), energy i) = 0) :
    MvPolynomial.eval₂ (RingHom.id ℂ) z (quadraticRateObstructionPullback M c κ)
      = fieldQuadraticRateOrbitValue c κ energy := by
  have hstep : MvPolynomial.eval₂ (RingHom.id ℂ) z (quadraticRateObstructionPullback M c κ)
      = MvPolynomial.eval₂ (RingHom.id ℂ)
          (fun i : Fin (Fintype.card I) => MvPolynomial.eval₂ (RingHom.id ℂ) z
            (matrixCharacteristicElementaryPolynomial M i))
          (fieldQuadraticRateCoefficientPolynomial c κ) := by
    rw [quadraticRateObstructionPullback]
    exact MvPolynomial.comp_aeval_apply (R := ℂ) _ (MvPolynomial.aeval z) _
  have hcoeff : ∀ i : Fin (Fintype.card I),
      MvPolynomial.eval₂ (RingHom.id ℂ) z (matrixCharacteristicElementaryPolynomial M i)
        = MvPolynomial.eval₂ (RingHom.id ℂ) energy (MvPolynomial.esymm I ℂ (i + 1)) := by
    intro i
    rw [eval_matrixCharacteristicElementaryPolynomial,
      matrixCharacteristicElementaryCoefficient_eq_rootPacket _ energy hinj hroot i,
      eval₂_esymm_rat_eq]
  rw [hstep, funext hcoeff, eval_fieldQuadraticRateCoefficientPolynomial_esymm]
  rw [show MvPolynomial.eval₂ (RingHom.id ℂ) energy (fieldQuadraticRateOrbitPolynomial c κ)
      = MvPolynomial.eval energy (fieldQuadraticRateOrbitPolynomial c κ) from rfl,
    eval_fieldQuadraticRateOrbitPolynomial]

/-- **One complex witness beats every real open set.**  If some parameter of the family carries a
full simple root packet on which no relabeling satisfies the quadratic-rate relation, then inside
every nonempty open set of real parameters the obstruction is somewhere nonzero. -/
theorem exists_mem_eval_quadraticRateObstructionPullback_ne_zero
    {m : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ)) (c : I → ℂ) (κ : ℂ)
    (hwitness : ∃ z : Fin m → ℂ,
      MvPolynomial.eval₂ (RingHom.id ℂ) z (quadraticRateObstructionPullback M c κ) ≠ 0)
    {U : Set (Fin m → ℝ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ p ∈ U, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p t : ℂ))
      (quadraticRateObstructionPullback M c κ) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz⟩ := hwitness
  refine hz ?_
  set P : MvPolynomial (Fin m) ℂ := quadraticRateObstructionPullback M c κ with hPdef
  have hre : complexMvPolynomialRealPart P = 0 := by
    refine realMvPolynomial_eq_zero_of_eqOn_zero_isOpen hUopen hUne ?_
    intro p hp
    rw [eval_complexMvPolynomialRealPart, hcon p hp, Complex.zero_re]
  have him : complexMvPolynomialImagPart P = 0 := by
    refine realMvPolynomial_eq_zero_of_eqOn_zero_isOpen hUopen hUne ?_
    intro p hp
    rw [eval_complexMvPolynomialImagPart, hcon p hp, Complex.zero_im]
  have hzero : P = 0 := by
    refine MvPolynomial.ext _ _ fun d => ?_
    refine Complex.ext ?_ ?_
    · rw [← coeff_complexMvPolynomialRealPart, hre]
      simp
    · rw [← coeff_complexMvPolynomialImagPart, him]
      simp
  rw [hzero, MvPolynomial.eval₂_zero]

end GaloisForLFunctions.HTGeometry
