import GaloisForLFunctions.HTGeometry.FiniteRingSl2
import GaloisForLFunctions.HTGeometry.FiniteRegularBlocks
import GaloisForLFunctions.RHTower.SelbergMaassGeneratorComparison

/-!
# Uniform full-unipotent comparison for the original congruence source

Four alternating complete unipotent blocks cover every actual congruence deck
quotient, including composite levels. Their exact original pullback energies
control the full centered source variance with coefficient sixteen. The
invariant mean and the multiplied normalized-chord identity retain the full
density and its common zeros. The blocks contain all residue parameters;
comparison to original differential currents remains a separate problem.
-/

open Complex Set UpperHalfPlane ModularGroup
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassUnipotentBlocks
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage
open SelbergMaassGeneratorComparison SelbergMaassTraceDirection
open GaloisForLFunctions.HTGeometry FiniteRingSl2 FiniteRegularBlocks
noncomputable section

local instance gammaNormal (N : ℕ) : (CongruenceSubgroup.Gamma (N+1)).Normal :=
  CongruenceSubgroup.Gamma_normal (N+1)

/-- Literal modular reduction is onto at every positive level, including composite levels. -/
theorem reduction_surjective (N : ℕ) : Function.Surjective
    (Matrix.SpecialLinearGroup.map (n:=Fin 2) (Int.castRingHom (ZMod (N+1)))) :=
  FiniteRingSl2.map_surjective _ ZMod.intCast_surjective

/-- The actual deck quotient is the complete determinant-one group over its residue ring. -/
def deckResidueEquiv (N : ℕ) : Deck N ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod (N+1)) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (reduction_surjective N)

theorem deckResidueEquiv_mk (N : ℕ) (A : SL2Z) :
    deckResidueEquiv N (QuotientGroup.mk A)=
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N+1))) A := rfl

/-- The complete upper unipotent block of the actual deck group. -/
def upperBlock (N : ℕ) : Multiplicative (ZMod (N+1)) →* Deck N :=
  (deckResidueEquiv N).symm.toMonoidHom.comp upperHom

/-- The complete lower unipotent block of the actual deck group. -/
def lowerBlock (N : ℕ) : Multiplicative (ZMod (N+1)) →* Deck N :=
  (deckResidueEquiv N).symm.toMonoidHom.comp lowerHom

/-- Four alternating blocks cover the literal congruence deck group. -/
theorem deck_four_blocks (N : ℕ) (g : Deck N) :
    ∃ a : Multiplicative (ZMod (N+1)), ∃ b : Multiplicative (ZMod (N+1)),
    ∃ c : Multiplicative (ZMod (N+1)), ∃ d : Multiplicative (ZMod (N+1)),
      g=upperBlock N a*lowerBlock N b*upperBlock N c*lowerBlock N d := by
  obtain ⟨a,b,c,d,h⟩ := exists_four_factors_finite (deckResidueEquiv N g)
  refine ⟨Multiplicative.ofAdd a,Multiplicative.ofAdd b,Multiplicative.ofAdd c,Multiplicative.ofAdd d,?_⟩
  apply (deckResidueEquiv N).injective
  simpa only [map_mul,upperBlock,lowerBlock,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,upperHom,lowerHom,MonoidHom.coe_mk,OneHom.coe_mk,
    toAdd_ofAdd] using h

/-- Each upper block element is the literal class of an integer elementary matrix. -/
theorem upperBlock_eq_mk (N : ℕ) (j : Multiplicative (ZMod (N+1))) :
    upperBlock N j=QuotientGroup.mk (upper (j.toAdd.val:ℤ)) := by
  apply (deckResidueEquiv N).injective
  rw [deckResidueEquiv_mk]
  simp only [upperBlock,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,upperHom,MonoidHom.coe_mk,OneHom.coe_mk,map_upper]
  simp

/-- Each lower block element is the literal class of an integer elementary matrix. -/
theorem lowerBlock_eq_mk (N : ℕ) (j : Multiplicative (ZMod (N+1))) :
    lowerBlock N j=QuotientGroup.mk (lower (j.toAdd.val:ℤ)) := by
  apply (deckResidueEquiv N).injective
  rw [deckResidueEquiv_mk]
  simp only [lowerBlock,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply,lowerHom,MonoidHom.coe_mk,OneHom.coe_mk,map_lower]
  simp

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

/-- Orthogonal variances discarded by the two complete unipotent averages. -/
def blockVariance (z : ℍ) : ℝ :=
  ‖sourceVector N f z-blockAverage (upperBlock N) (sourceVector N f z)‖^2+
    ‖sourceVector N f z-blockAverage (lowerBlock N) (sourceVector N f z)‖^2

/-- Averaged literal upper and lower modular displacements of the full original source. -/
def blockEnergy (z : ℍ) : ℝ :=
  (2*(N+1:ℕ):ℝ)⁻¹*((∑ j : Multiplicative (ZMod (N+1)),
    displacementEnergy N f (upper (j.toAdd.val:ℤ)) z)+
      ∑ j : Multiplicative (ZMod (N+1)), displacementEnergy N f (lower (j.toAdd.val:ℤ)) z)

theorem blockEnergy_eq_variance (z : ℍ) : blockEnergy N f z=blockVariance N f z := by
  have hu := blockAverage_energy (upperBlock N) (sourceVector N f z)
  have hl := blockAverage_energy (lowerBlock N) (sourceVector N f z)
  rw [blockEnergy,mul_add]
  unfold blockVariance
  rw [← hu,← hl]
  simp only [upperBlock_eq_mk,lowerBlock_eq_mk,displacementEnergy_eq_norm]
  congr 2 <;> simp

/-- Uniform control of every original centered component by actual full-block motion. -/
theorem variance_le_blockEnergy (z : ℍ) :
    (∑ q : Deck N, normSq (centeredComponent N f q z)) ≤ 16*blockEnergy N f z := by
  have h := variance_le_two_blocks (upperBlock N) (lowerBlock N) (deck_four_blocks N) (sourceVector N f z)
  rw [complement_sourceVector_norm_sq] at h
  simpa only [blockEnergy_eq_variance,blockVariance] using h

/-- The full original density retains its invariant mean in the uniform block comparison. -/
theorem density_le_mean_add_blockEnergy (z : ℍ) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+16*blockEnergy N f z := by
  rw [density_mean_variance]
  exact add_le_add_right (variance_le_blockEnergy N f z) _

theorem density_le_blockEnergy_of_mean_zero (z : ℍ) (hm : sourceMean N f z=0) :
    density N f z ≤ 16*blockEnergy N f z := by
  simpa only [hm,normSq_zero,mul_zero,zero_add] using density_le_mean_add_blockEnergy N f z

/-- Averaged normalized chords for the same complete original block motions. -/
def blockChord (z : ℍ) : ℝ :=
  (2*(N+1:ℕ):ℝ)⁻¹*((∑ j : Multiplicative (ZMod (N+1)),
    directionDistanceSq N f z (upper (j.toAdd.val:ℤ) • z))+
      ∑ j : Multiplicative (ZMod (N+1)), directionDistanceSq N f z (lower (j.toAdd.val:ℤ) • z))

/-- Multiplied reconstruction includes all original common zeros. -/
theorem blockEnergy_eq_density_mul_chord (z : ℍ) :
    blockEnergy N f z=density N f z*blockChord N f z := by
  unfold blockEnergy blockChord
  simp only [displacementEnergy_eq_density_mul_chord,← Finset.mul_sum]
  ring

/-- At a mean-zero point of positive density, complete block chords have a uniform lower bound. -/
theorem one_le_block_chord_of_mean_zero (z : ℍ) (hz : 0 < density N f z)
    (hm : sourceMean N f z=0) : 1 ≤ 16*blockChord N f z := by
  have h := density_le_blockEnergy_of_mean_zero N f z hm
  rw [blockEnergy_eq_density_mul_chord] at h
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassUnipotentBlocks
