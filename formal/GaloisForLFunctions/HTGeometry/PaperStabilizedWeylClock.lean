import GaloisForLFunctions.HTGeometry.PaperStabilizedPolynomialClock
import GaloisForLFunctions.HTGeometry.StokesWeylFourierSource

/-!
The stable-coordinate clock represents the native Stokes Weyl algebra.
Fourier substitution produces another concrete representation. Its derivative
is injective, whereas the original derivative kills constants; consequently
no complex-linear equivalence of polynomial states intertwines the two.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open StableCoordinate GaloisForLFunctions.IrregularStokes.WeylFourier

def paperStabilizedCoordinateOperator : Module.End ℂ (R 5) :=
  LinearMap.mulLeft ℂ (stabilize f)

def paperStabilizedDerivativeOperator : Module.End ℂ (R 5) :=
  paperStabilizedClock.toLinearMap

theorem paperStabilizedOperators_commutator :
    paperStabilizedDerivativeOperator * paperStabilizedCoordinateOperator -
      paperStabilizedCoordinateOperator * paperStabilizedDerivativeOperator = 1 := by
  apply LinearMap.ext
  intro p
  change paperStabilizedClock (stabilize f * p) -
    stabilize f * paperStabilizedClock p = p
  rw [Derivation.leibniz, paperStabilizedClock_slice]
  simp [smul_eq_mul]

def paperStabilizedWeylWords : PresentedWeyl →ₐ[ℂ] Module.End ℂ (R 5) :=
  FreeAlgebra.lift ℂ (fun
    | Generator.coordinate => paperStabilizedCoordinateOperator
    | Generator.derivative => paperStabilizedDerivativeOperator)

private theorem words_relation : paperStabilizedWeylWords weylRelation = 0 := by
  simp only [weylRelation, map_sub, map_mul, map_one, derivativeWord, coordinateWord,
    paperStabilizedWeylWords, FreeAlgebra.lift_ι_apply]
  exact sub_eq_zero.mpr paperStabilizedOperators_commutator

private theorem words_kill_ideal {a : PresentedWeyl} (ha : a ∈ weylIdeal) :
    paperStabilizedWeylWords a = 0 := by
  apply TwoSidedIdeal.span_induction (s := {weylRelation})
    (p := fun a _ => paperStabilizedWeylWords a = 0) (x := a) ?_ ?_ ?_ ?_ ?_ ?_ ha
  · intro z hz
    have hz' : z = weylRelation := by simpa using hz
    subst z
    exact words_relation
  · exact map_zero paperStabilizedWeylWords
  · intro u v hu hv ihu ihv
    simp [ihu, ihv]
  · intro u hu ihu
    simp [ihu]
  · intro u v hv ihv
    simp [map_mul, ihv]
  · intro v u hv ihv
    simp [map_mul, ihv]

private theorem words_kernel :
    weylCongruence ≤ RingCon.ker paperStabilizedWeylWords.toRingHom := by
  intro a b hab
  rw [RingCon.ker_apply]
  have hz := words_kill_ideal ((TwoSidedIdeal.rel_iff weylIdeal a b).mp hab)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

/-- The native Weyl quotient acts on the actual stabilized polynomial ring. -/
def paperStabilizedWeylRepresentation : WeylAlgebra →ₐ[ℂ] Module.End ℂ (R 5) :=
  weylCongruence.liftₐ paperStabilizedWeylWords words_kernel

@[simp] theorem paperStabilizedWeylRepresentation_X :
    paperStabilizedWeylRepresentation X = paperStabilizedCoordinateOperator := by
  simp [paperStabilizedWeylRepresentation, X, toWeylAlgebra,
    coordinateWord, paperStabilizedWeylWords]

@[simp] theorem paperStabilizedWeylRepresentation_D :
    paperStabilizedWeylRepresentation D = paperStabilizedDerivativeOperator := by
  simp [paperStabilizedWeylRepresentation, D, toWeylAlgebra,
    derivativeWord, paperStabilizedWeylWords]

theorem paperStabilizedWeylRepresentation_derivative_terminates (p : R 5) :
    ∃ n : ℕ, paperStabilizedWeylRepresentation (D ^ n) p = 0 := by
  obtain ⟨n, hn⟩ := paperStabilizedClock_locallyNilpotent p
  refine ⟨n, ?_⟩
  rw [map_pow, paperStabilizedWeylRepresentation_D, Module.End.pow_apply]
  exact hn

theorem paperStabilizedClock_polynomial_ne_zero : stabilize f ≠ 0 := by
  intro h
  have hs := paperStabilizedClock_slice
  rw [h, map_zero] at hs
  exact zero_ne_one hs

theorem paperStabilizedCoordinateOperator_injective :
    Function.Injective paperStabilizedCoordinateOperator := by
  intro p q hpq
  change stabilize f * p = stabilize f * q at hpq
  have hz : stabilize f * (p - q) = 0 := by rw [mul_sub, hpq, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left paperStabilizedClock_polynomial_ne_zero)

/-- Fourier substitution is a concrete representation on the same polynomial space. -/
def paperStabilizedFourierRepresentation : WeylAlgebra →ₐ[ℂ] Module.End ℂ (R 5) :=
  paperStabilizedWeylRepresentation.comp fourier.toAlgHom

@[simp] theorem paperStabilizedFourierRepresentation_X :
    paperStabilizedFourierRepresentation X = paperStabilizedDerivativeOperator := by
  simp [paperStabilizedFourierRepresentation]

@[simp] theorem paperStabilizedFourierRepresentation_D :
    paperStabilizedFourierRepresentation D = -paperStabilizedCoordinateOperator := by
  simp [paperStabilizedFourierRepresentation]

theorem paperStabilizedFourierRepresentation_derivative_injective :
    Function.Injective (paperStabilizedFourierRepresentation D) := by
  intro p q h
  rw [paperStabilizedFourierRepresentation_D] at h
  apply paperStabilizedCoordinateOperator_injective
  simpa using congrArg Neg.neg h

theorem paperStabilizedWeylRepresentation_fourier_fourth (a : WeylAlgebra) :
    paperStabilizedWeylRepresentation (fourier (fourier (fourier (fourier a)))) =
      paperStabilizedWeylRepresentation a := by
  rw [fourier_fourth]

theorem paperStabilizedFourierRepresentation_commutator :
    paperStabilizedFourierRepresentation D * paperStabilizedFourierRepresentation X -
      paperStabilizedFourierRepresentation X * paperStabilizedFourierRepresentation D = 1 := by
  rw [← map_mul, ← map_mul, ← map_sub, D_mul_X_sub_X_mul_D, map_one]

/-- The Fourier action on operators is not conjugation by a linear map of polynomial states. -/
theorem paperStabilizedWeyl_no_fourier_intertwiner :
    ¬ ∃ U : R 5 ≃ₗ[ℂ] R 5, ∀ (a : WeylAlgebra) (p : R 5),
      U (paperStabilizedWeylRepresentation a p) =
        paperStabilizedFourierRepresentation a (U p) := by
  rintro ⟨U, hU⟩
  have hz : paperStabilizedFourierRepresentation D (U 1) = 0 := by
    rw [← hU D 1, paperStabilizedWeylRepresentation_D]
    change U (paperStabilizedClock 1) = 0
    rw [Derivation.map_one_eq_zero, map_zero]
  have h1 : U 1 = U 0 := paperStabilizedFourierRepresentation_derivative_injective (by
    rw [hz, map_zero, map_zero])
  exact one_ne_zero (U.injective h1)

end
end GaloisForLFunctions.HTGeometry
