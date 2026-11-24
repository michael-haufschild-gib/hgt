import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryBalls.AntipodalFiber
import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw
import GaloisForLFunctions.HTGeometry.UnitaryL2OperatorNorm

/-! # Lifting projective spectral visits to independent absolute phases -/
open Set MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
noncomputable section

private abbrev Config (N : ℕ) := Fin N → Bool
private abbrev Mat (N : ℕ) := Matrix (Config N) (Config N) ℂ

/-- Anchor the absolute phases in the specified spectral ordering. -/
def anchorMap {N d : ℕ} (e : Config N ≃ Fin (d+1)) : UnitAddTorus (Config N) →+ UnitAddTorus (Fin d) where
  toFun z j := z (e.symm j.succ)-z (e.symm 0)
  map_zero' := by ext j; simp
  map_add' z w := by ext j; simp only [Pi.add_apply]; abel

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

theorem anchor_preserving {N d : ℕ} (e : Config N ≃ Fin (d+1)) :
    MeasurePreserving (anchorMap e) volume volume := by
  letI : (volume : Measure (UnitAddTorus (Config N))).IsAddHaarMeasure := {}
  letI : (volume : Measure (UnitAddTorus (Fin d))).IsAddHaarMeasure := {}
  apply (anchorMap e).measurePreserving (continuous_pi fun j => (continuous_apply _).sub (continuous_apply _))
  · intro x
    refine ⟨fun q => RHTower.zeroAnchoredPhase d x (e q),?_⟩
    funext j
    change RHTower.zeroAnchoredPhase d x (e (e.symm j.succ))-
      RHTower.zeroAnchoredPhase d x (e (e.symm 0))=x j
    simp only [Equiv.apply_symm_apply,RHTower.zeroAnchoredPhase,Fin.cases_zero,Fin.cases_succ,sub_zero]
  · simp only [measure_univ]

private theorem anchor_value {N d : ℕ} (e : Config N ≃ Fin (d+1)) (z : UnitAddTorus (Config N)) (q : Config N) :
    RHTower.zeroAnchoredPhase d (anchorMap e z) (e q)=z q-z (e.symm 0) := by
  obtain ⟨j,rfl⟩ := e.symm.surjective q
  rw [Equiv.apply_symm_apply]
  exact Fin.cases (sub_self _).symm (fun _ => rfl) j

/-- In the laboratory eigenbasis, restoring the anchor multiplies the
projective representative by a scalar of modulus one. -/
theorem absolute_packet {N d : ℕ} (e : Config N ≃ Fin (d+1)) (V : unitaryGroup (Config N) ℂ)
    (z : UnitAddTorus (Config N)) :
    let c : ℂ := (z (e.symm 0)).toCircle
    (V:Mat N)*packet z*star (V:Mat N) = c • projectiveSpectralMatrix e V (anchorMap e z) := by
  intro c
  have hd : packet z = c • diagonal (fun q => fourier 1 (RHTower.zeroAnchoredPhase d (anchorMap e z) (e q))) := by
    ext i j
    by_cases h : i=j
    · subst j
      rw [packet,diagonal_apply_eq,Matrix.smul_apply,diagonal_apply_eq,anchor_value,
        fourier_apply,one_zsmul,smul_eq_mul]
      change ((z i).toCircle:ℂ)=(z (e.symm 0)).toCircle*((z i-z (e.symm 0)).toCircle:ℂ)
      rw [←Circle.coe_mul,←AddCircle.toCircle_add,show z (e.symm 0)+(z i-z (e.symm 0))=z i by abel]
    · simp only [packet,diagonal_apply_ne _ h,Matrix.smul_apply,smul_zero]
  rw [hd,Matrix.mul_smul,Matrix.smul_mul]
  rfl

#print axioms absolute_packet
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.UnitaryBalls
