import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.Eigenphases
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.ContinuousCircuitCompletedOccupationLaw

/-! # Same-error variation of physical gate count under a single phase change -/
open Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
open DiagonalSynthesis
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool

private theorem replace_eigenphase {n s : ℕ} (hn : 2 ≤ n) (V : unitaryGroup (Config n) ℂ)
    {p q : Config n → ℂ} (hp : ∀ x, ‖p x‖=1) (hq : ∀ x, ‖q x‖=1)
    (i : Config n) (hagree : ∀ j, j≠i → q j=p j) {ε : ℝ}
    (hs : HasProjectiveCircuitApproximation n ε s (V.val*diagonal p*star V.val)) :
    HasProjectiveCircuitApproximation n ε (eigenphaseCost n+s) (V.val*diagonal q*star V.val) := by
  let z := q i/p i
  have hz : ‖z‖=1 := by rw [show z=q i/p i from rfl,norm_div,hp,hq,div_one]
  let D := diagonal (pointPhase i z)
  have hdiag : D*diagonal p=diagonal q := by
    dsimp only [D]
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases h : j=i
    · subst j
      have hne : p i ≠ 0 := fun he => by have := hp i; simp [he] at this
      simp [pointPhase,z,hne]
    · simp [pointPhase,h,hagree j h]
  have hleft : (V.val*D*star V.val)*(V.val*diagonal p*star V.val) = V.val*diagonal q*star V.val := by
    calc _ = V.val*(D*(star V.val*V.val)*diagonal p)*star V.val := by simp only [mul_assoc]
         _ = _ := by rw [V.property.1,mul_one,hdiag]
  have hold : V.val*diagonal p*star V.val ∈ unitary (DiagonalSynthesis.Register n) :=
    mul_mem (mul_mem V.property (StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _ hp)) (V⁻¹).property
  have h := LocalPatches.approx_product hold ((eigenline_phase hn V i z hz).approx (le_refl (0:ℝ))) hs
  rw [zero_add] at h
  exact hleft ▸ h

/-- Replacing one relative phase adds at most one exact eigenline
rotation to a fitting physical circuit at its original tolerance. -/
theorem replace_coordinate {n d s : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {x y : Fin d → UnitAddCircle} (i : Fin d)
    (hxy : ∀ j, j≠i → y j=x j) {ε : ℝ}
    (hs : HasProjectiveCircuitApproximation n ε s (projectiveSpectralMatrix e V x)) :
    HasProjectiveCircuitApproximation n ε (eigenphaseCost n+s) (projectiveSpectralMatrix e V y) := by
  let p (u : Fin d → UnitAddCircle) (j : Config n) := fourier 1 (RHTower.zeroAnchoredPhase d u (e j))
  have hp u j : ‖p u j‖=1 := by dsimp only [p]; rw [fourier_apply,Circle.norm_coe]
  have ha (j : Fin (d+1)) : j ≠ i.succ → RHTower.zeroAnchoredPhase d y j=RHTower.zeroAnchoredPhase d x j := by
    refine Fin.cases (fun _ => rfl) (fun k h => ?_) j
    exact hxy k (fun he => h (congrArg Fin.succ he))
  apply replace_eigenphase hn V (hp x) (hp y) (e.symm i.succ) _ hs
  intro j hj
  exact congrArg (fourier 1) (ha (e j) (fun he => hj ((e.eq_symm_apply).mpr he)))

#print axioms replace_coordinate
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
