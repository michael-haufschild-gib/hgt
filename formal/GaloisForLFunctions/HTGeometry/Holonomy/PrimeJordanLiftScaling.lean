import GaloisForLFunctions.HTGeometry.LinearAlgebra.NilpotentDilation
import GaloisForLFunctions.HTGeometry.PrimeHodgeJordanLift

/-!
# Independent shear amplitude in the prime--Hodge Jordan lift

On the doubled prime Hilbert space, the bounded diagonal unit `(q,1)` rescales
the square-zero Jordan step by `q`, fixes the diagonal prime heat, and fixes the
source vector. Consequently conjugation changes the Jordan semigroup to
`jointHeat(r) * (1 + r*q*N)`.

The nilpotent amplitude is therefore a genuine similarity freedom independent
of the prime heat parameter. The construction works on the actual infinite
prime Hilbert space and uses no finite-dimensional approximation.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower
open scoped NNReal
local notation "P" => lp (fun _ : Nat.Primes => ℂ) 2
local notation "J" => (P × P →L[ℂ] P × P)

/-- The bounded diagonal unit scaling the first prime-Hilbert summand. -/
def jordanAmplitudeUnit (q : ℂˣ) : Jˣ where
  val := (q.val • ContinuousLinearMap.fst ℂ P P).prod (ContinuousLinearMap.snd ℂ P P)
  inv := (q.inv • ContinuousLinearMap.fst ℂ P P).prod (ContinuousLinearMap.snd ℂ P P)
  val_inv := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · change q.val • (q.inv • z.1) = z.1
      rw [smul_smul, q.val_inv, one_smul]
    · rfl
  inv_val := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · change q.inv • (q.val • z.1) = z.1
      rw [smul_smul, q.inv_val, one_smul]
    · rfl

/-- Conjugation by the diagonal amplitude unit. -/
def jordanAmplitudeEquiv (q : ℂˣ) : J ≃ₐ[ℂ] J :=
  clockInnerAlgEquiv (jordanAmplitudeUnit q)

/-- The actual square-zero Jordan step has arbitrary nonzero complex amplitude. -/
theorem jordanAmplitudeEquiv_nilpotent (q : ℂˣ) :
    jordanAmplitudeEquiv q jordanNilpotent = q.val • jordanNilpotent := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · change q.val • z.2 = q.val • z.2
    rfl
  · change (0 : P) = q.val • (0 : P)
    rw [smul_zero]

/-- Diagonal prime heat is fixed by amplitude conjugation. -/
theorem jordanAmplitudeEquiv_jointHeat (q : ℂˣ) (r : ℝ≥0) :
    jordanAmplitudeEquiv q (jointHeat r) = jointHeat r := by
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · change q.val • primeHeat r (q.inv • z.1) = primeHeat r z.1
    rw [map_smul, smul_smul, q.val_inv, one_smul]
  · rfl

/-- Amplitude conjugation preserves heat time and rescales the Jordan shear. -/
theorem jordanAmplitudeEquiv_semigroup (q : ℂˣ) (r : ℝ≥0) :
    jordanAmplitudeEquiv q (jordanSemigroup r) =
      jointHeat r * (1 + ((r : ℂ) * q.val) • jordanNilpotent) := by
  rw [jordanSemigroup, exp_smul_jordanNilpotent, map_mul,
    jordanAmplitudeEquiv_jointHeat, map_add, map_one, map_smul,
    jordanAmplitudeEquiv_nilpotent, smul_smul]

/-- The actual prime--Hodge source vector is fixed by the amplitude unit. -/
theorem jordanAmplitudeEquiv_source {d : ℝ} (hd : 0 < d) (q : ℂˣ) :
    (jordanAmplitudeUnit q).val (jordanSource hd) = jordanSource hd := by
  apply Prod.ext
  · change q.val • (0 : P) = 0
    exact smul_zero _
  · rfl

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.jordanAmplitudeEquiv_nilpotent
#print axioms GaloisForLFunctions.HTGeometry.jordanAmplitudeEquiv_jointHeat
#print axioms GaloisForLFunctions.HTGeometry.jordanAmplitudeEquiv_semigroup
#print axioms GaloisForLFunctions.HTGeometry.jordanAmplitudeEquiv_source
