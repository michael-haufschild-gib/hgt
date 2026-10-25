import GaloisForLFunctions.ArithmeticDefectRigidity.FiniteCofactorIndexCountsJointMultiplicity
import GaloisForLFunctions.ArithmeticDefectRigidity.CofactorEigencharacterMagnitudesArePowers
import GaloisForLFunctions.HTGeometry.FiniteCommutingFamiliesHaveCommonEigenvectors
import GaloisForLFunctions.ArithmeticOrientationTheory.TiedBohrToriAreLimitsOfVerticalCharacters

/-!
# Finite cofactor hulls approach the half-plane curve

Each hull character of a finite-dimensional actual module has a common eigenvector and therefore
augmentation or a tied radial modulus. One sequence of half-plane points
approaches its evaluations on the entire critical Wiener algebra.
-/

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticOrientationTheory

/-- Wiener evaluation on positive point masses is a multiplicative cofactor character. -/
def bohrCofactorCharacter (ω : BohrPoint) : ℕ+ →* ℂ where
  toFun p := WienerAlgebraAt.bohrCharacter (1 / 2) ω (pointMass p)
  map_one' := by
    change WienerAlgebraAt.bohrCharacter (1 / 2) ω (pointMass 1) = 1
    rw [pointMass_one, map_one]
  map_mul' p q := by
    rw [← map_mul, pointMass_mul]
    rfl

theorem norm_bohrCofactorCharacter (ω : BohrPoint) (p : ℕ+) :
    ‖bohrCofactorCharacter ω p‖ = ‖ω.ω p‖ / (p : ℝ) ^ (1 / 2 : ℝ) := by
  change ‖WienerAlgebraAt.bohrCharacter (1 / 2) ω (pointMass p)‖ = _
  rw [bohrCharacter_apply, toFn_pointMass,
    bohrEval_pointMass (σ := 1 / 2) (n := (p : ℕ)) p.property.ne' ω, norm_div,
    norm_natCast_cpow (p : ℕ) p.property.ne']

end GaloisForLFunctions.ArithmeticOrientationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- Every hull character of a finite-dimensional actual module occurs on a common eigenvector. -/
theorem exists_eigenvector_of_mem_finite_moduleHull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (ω : BohrPoint) (hω : ω ∈ moduleHull L) :
    ∃ x : Hilbert L, x ≠ 0 ∧ ∀ p : ℕ+,
      dilation L p x = bohrCofactorCharacter ω p • x := by
  let f := algebraRepresentation L
  let χ (a : WienerAlgebraAt (1 / 2)) := ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω
  let J := algebraJointSpace f χ
  have hJ : J ≠ ⊥ := (mem_moduleHull_iff_jointBohrSpace_ne_bot L ω).mp hω
  letI : Nontrivial J := Submodule.nontrivial_iff_ne_bot.mpr hJ
  let g (a : WienerAlgebraAt (1 / 2)) : Module.End ℂ J :=
    (f a).restrict (algebraJointSpace_mapsTo f χ a)
  have hcomm (a b : WienerAlgebraAt (1 / 2)) : Commute (g a) (g b) := by
    ext x
    exact LinearMap.congr_fun (algebraAction_commute f a b).eq x
  obtain ⟨x, ψ, hx, hψ⟩ := exists_common_eigenvector_family g hcomm
  have hxV : (x : Hilbert L) ≠ 0 := fun h => hx (Subtype.ext h)
  have heig (a : WienerAlgebraAt (1 / 2)) : f a (x : Hilbert L) = χ a • (x : Hilbert L) := by
    have ha : f a (x : Hilbert L) = ψ a • (x : Hilbert L) := congrArg Subtype.val (hψ a)
    have hgen : (x : Hilbert L) ∈ (f a).maxGenEigenspace (χ a) :=
      (Submodule.mem_iInf _).mp x.property a
    rw [eigenvalue_eq_of_mem_maxGenEigenspace (f a) hxV hgen ha] at ha
    exact ha
  refine ⟨x, hxV, fun p => ?_⟩
  have h := heig (pointMass p)
  change wienerRepresentation L (pointMass p) (x : Hilbert L) =
    bohrCofactorCharacter ω p • (x : Hilbert L) at h
  rwa [wienerRepresentation_pointMass] at h

/-- Hull points of finite-dimensional actual modules have augmentation modulus or one radial exponent. -/
theorem finite_moduleHull_modulus_classification {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (ω : BohrPoint) (hω : ω ∈ moduleHull L) :
    (∀ p : ℕ+, p ≠ 1 → ω.ω p = 0) ∨
      ∃ α : ℝ, 0 ≤ α ∧ ∀ p : ℕ+, ‖ω.ω p‖ = (p : ℝ) ^ (-α) := by
  obtain ⟨x, hx, heig⟩ := exists_eigenvector_of_mem_finite_moduleHull L ω hω
  rcases eigencharacter_norm_eq_augmentation_or_rpow L (bohrCofactorCharacter ω) hx heig with
    hzero | ⟨s, hs, hpower⟩
  · refine Or.inl fun p hp => norm_eq_zero.mp ?_
    have h := norm_bohrCofactorCharacter ω p
    rw [hzero p hp, norm_zero] at h
    have hpos : (0 : ℝ) < (p : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    exact (div_eq_zero_iff.mp h.symm).resolve_right hpos.ne'
  · refine Or.inr ⟨s - 1 / 2, sub_nonneg.mpr hs, fun p => ?_⟩
    have hp : (0 : ℝ) < p := by positivity
    have hpne := (Real.rpow_pos_of_pos hp (1 / 2 : ℝ)).ne'
    have hdiv : ‖ω.ω p‖ / (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) ^ (-s) :=
      (norm_bohrCofactorCharacter ω p).symm.trans (hpower p)
    rw [(div_eq_iff hpne).mp hdiv, ← Real.rpow_add hp]
    congr 1
    ring

open Filter Topology

/-- A hull character of a finite-dimensional actual module is approached on all Wiener elements. -/
theorem exists_halfPlane_sequence_of_mem_finite_moduleHull {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) [FiniteDimensional ℂ (Hilbert L)]
    (ω : BohrPoint) (hω : ω ∈ moduleHull L) :
    ∃ s : ℕ → ℂ, (∀ j, (1 / 2 : ℝ) ≤ (s j).re) ∧
      ∀ a : WienerAlgebraAt (1 / 2),
        Tendsto (fun j => LSeries (⇑a.toFn) (s j)) atTop
          (𝓝 (ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω)) :=
  exists_halfPlane_sequence_tendsto_bohrEval_of_radial_or_augmentation (1 / 2) ω
    (finite_moduleHull_modulus_classification L ω hω)

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_eigenvector_of_mem_finite_moduleHull
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.finite_moduleHull_modulus_classification
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_halfPlane_sequence_of_mem_finite_moduleHull
end
