import GaloisForLFunctions.HTGeometry.FiniteRegularGeneratorCost
import GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
import GaloisForLFunctions.RHTower.SelbergMaassTraceDirection
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Actual S/T comparison for the original congruence source

The literal modular generators generate every original finite congruence
quotient. Their certified finite word costs therefore control the complete
mean-zero variance, with a positive coefficient depending only on the level.
The two energies are identified with the original Maass pullbacks, and the
multiplied normalized-chord law includes common zeros. No level-uniform cost,
quarter comparison, or Xi occurrence is assumed or asserted.
-/

open Complex Set UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassGeneratorComparison
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassTraceDirection
open GaloisForLFunctions.HTGeometry
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

def generatorS (N : ℕ) : Deck N := QuotientGroup.mk S

def generatorT (N : ℕ) : Deck N := QuotientGroup.mk T

/-- The literal modular generators generate the actual finite congruence quotient. -/
theorem generators_generate (N : ℕ) :
    Subgroup.closure ({generatorS N,generatorT N}:Set (Deck N))=⊤ := by
  let p : SL2Z →* Deck N := QuotientGroup.mk' (CongruenceSubgroup.Gamma (N+1))
  have h := congrArg (fun H : Subgroup SL2Z => H.map p) SpecialLinearGroup.SL2Z_generators
  rw [MonoidHom.map_closure,Subgroup.map_top_of_surjective p
    (QuotientGroup.mk'_surjective (CongruenceSubgroup.Gamma (N+1)))] at h
  simpa only [Set.image_insert_eq,Set.image_singleton,p,QuotientGroup.mk'_apply,generatorS,generatorT] using h

/-- A positive finite cost constructed from this level's literal S and T generators. -/
def generatorConstant (N : ℕ) : ℝ :=
  FiniteRegularGeneratorCost.comparisonConstant (generatorS N) (generatorT N) (generators_generate N)

theorem generatorConstant_pos (N : ℕ) : 0 < generatorConstant N :=
  FiniteRegularGeneratorCost.comparisonConstant_pos _ _ _

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Complete original component displacement under an actual modular pullback. -/
def displacementEnergy (A : SL2Z) (z : ℍ) : ℝ :=
  ∑ q : Deck N, normSq ((quotientForm N f q).1.1 (A • z)-(quotientForm N f q).1.1 z)

/-- The two literal modular-generator energies, with every original component retained. -/
def generatorEnergy (z : ℍ) : ℝ := displacementEnergy N f S z+displacementEnergy N f T z

theorem displacementEnergy_nonneg (A : SL2Z) (z : ℍ) : 0 ≤ displacementEnergy N f A z :=
  Finset.sum_nonneg (fun _ _ => normSq_nonneg _)

theorem generatorEnergy_nonneg (z : ℍ) : 0 ≤ generatorEnergy N f z :=
  add_nonneg (displacementEnergy_nonneg N f S z) (displacementEnergy_nonneg N f T z)

theorem displacementEnergy_eq_norm (A : SL2Z) (z : ℍ) :
    displacementEnergy N f A z=
      ‖finiteRegularUnitary (QuotientGroup.mk A : Deck N) (sourceVector N f z)-sourceVector N f z‖^2 := by
  rw [← sourceVector_pullback,EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rfl

/-- The actual full centered source variance is controlled by the literal S and
T displacements with a constructed finite coefficient depending only on level. -/
theorem variance_le_generatorEnergy (z : ℍ) :
    (∑ q : Deck N, normSq (centeredComponent N f q z)) ≤
      generatorConstant N*generatorEnergy N f z := by
  have h := FiniteRegularGeneratorCost.variance_le_generator_energy
    (generatorS N) (generatorT N) (generators_generate N) (sourceVector N f z)
  rw [complement_sourceVector_norm_sq] at h
  simpa only [generatorConstant,generatorEnergy,displacementEnergy_eq_norm,generatorS,generatorT] using h

/-- The invariant mean and the complete two-generator energy retain the full
original source density, including its zero-average case. -/
theorem density_le_mean_add_generatorEnergy (z : ℍ) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      generatorConstant N*generatorEnergy N f z := by
  rw [density_mean_variance]
  exact add_le_add_right (variance_le_generatorEnergy N f z) _

/-- When the actual mean vanishes at a point, the two literal generator motions
control the entire original density there. -/
theorem density_le_generatorEnergy_of_mean_zero (z : ℍ) (hm : sourceMean N f z=0) :
    density N f z ≤ generatorConstant N*generatorEnergy N f z := by
  simpa only [hm,normSq_zero,mul_zero,zero_add] using density_le_mean_add_generatorEnergy N f z

/-- Exact conversion to the original normalized source chord. The multiplied
identity includes common zeros and uses the original modular density invariance. -/
theorem displacementEnergy_eq_density_mul_chord (A : SL2Z) (z : ℍ) :
    displacementEnergy N f A z=density N f z*directionDistanceSq N f z (A • z) := by
  have he (q : Deck N) :
      (quotientForm N f q).1.1 (A • z)-(quotientForm N f q).1.1 z=
        (Real.sqrt (density N f z):ℂ)*(direction N f q (A • z)-direction N f q z) := by
    have hz := amplitude_mul_direction N f q z
    have hw := amplitude_mul_direction N f q (A • z)
    rw [density_invariant] at hw
    rw [mul_sub,hw,hz]
  unfold displacementEnergy directionDistanceSq
  simp only [he,normSq_mul,Complex.normSq_ofReal,Real.mul_self_sqrt (density_nonneg N f z)]
  rw [Finset.mul_sum]

/-- Mean-zero points of positive original density have quantitatively separated
S/T directions with the level's proved finite comparison constant. -/
theorem one_le_generator_chords_of_mean_zero (z : ℍ) (hz : 0 < density N f z)
    (hm : sourceMean N f z=0) :
    1 ≤ generatorConstant N*
      (directionDistanceSq N f z (S • z)+directionDistanceSq N f z (T • z)) := by
  have h := density_le_generatorEnergy_of_mean_zero N f z hm
  rw [generatorEnergy,displacementEnergy_eq_density_mul_chord,
    displacementEnergy_eq_density_mul_chord] at h
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassGeneratorComparison
