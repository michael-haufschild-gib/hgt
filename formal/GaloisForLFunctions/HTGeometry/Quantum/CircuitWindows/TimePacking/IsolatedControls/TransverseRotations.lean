import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IsolatedControls.PhysicalPulse
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.TimePacking.IsolatedControls.RotationDistance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.TransferCoefficient
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsolatedFieldDensity
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations

/-! # Distance of each transverse one-gate rotation from the frozen orbit -/
open Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
open private involution_evolution from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.TransferCoefficient
open private rotate_short_word from GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliRotations
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

private theorem phase_unitary {n : ℕ} {U : Reg n} (hU : U∈unitary (Reg n)) {z : ℂ}
    (hz : ‖z‖=1) : z • U∈unitary (Reg n) := by
  have h : conj z*z=1 := by rw [Complex.conj_mul',hz]; norm_num
  apply Unitary.mem_iff.mpr
  constructor <;> simp [star_smul,smul_smul,(Unitary.mem_iff.mp hU).1,(Unitary.mem_iff.mp hU).2,
    h,mul_comm z (conj z)]

private theorem spin_rotation {n : ℕ} (u : PathShell n) (s : Fin (n+2))
    {η : ℝ} (hη : 0≤η) (hs : isolatedLongitudinalSite u 1 η s) (θ : ℝ) :
    let W := unitaryEvolution (finitePauliMatrix (onsiteWord s 0)) θ
    let d := √(2-2*|cos θ|)
    (∃ c : ℂ, ‖c‖=1 ∧ ‖c • (1:Reg n)-W‖=d) ∧
    ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 → d≤‖z • unitaryEvolution (pathHamiltonian u) t-W‖+21*π*η := by
  intro W d
  let X := finitePauliMatrix (onsiteWord s 0)
  have hX : star X=X := finitePauliMatrix_isHermitian _
  have hW := unitaryEvolution_mem_unitary (show IsSelfAdjoint X from hX) θ
  have hw : W=(cos θ:ℂ) • 1+(-Complex.I*(sin θ:ℂ)) • X := involution_evolution X (finitePauliMatrix_mul_self _) θ
  have hw' : star W=(cos θ:ℂ) • 1+(Complex.I*(sin θ:ℂ)) • X := by
    rw [hw,star_add,star_smul,star_smul,star_one,hX]
    simp only [Complex.star_def,Complex.conj_ofReal,map_mul,map_neg,Complex.conj_I,neg_neg]
  have hreal : W+star W=(2*cos θ) • (1:Reg n) := by
    rw [hw',hw,neg_mul,neg_smul,show (2*cos θ) • (1:Reg n)=((cos θ:ℂ) • 1)+((cos θ:ℂ) • 1) by
      rw [two_mul,add_smul,Complex.coe_smul]]
    abel
  refine ⟨scalar_midpoint hW (abs_le.mpr ⟨neg_one_le_cos _,cos_le_one _⟩) hreal,?_⟩
  intro t z hz
  obtain ⟨V,hV,_,hanti,hv⟩ := isolated_interchange u s (by norm_num : (0:ℝ)<1) hη hs
  have hf : V*W=star W*V := by
    rw [hw',hw,mul_add,add_mul,Matrix.mul_smul,Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_mul,
      mul_one,one_mul,hanti,smul_neg,neg_mul,neg_smul,neg_neg]
  have ht := phase_unitary (unitaryEvolution_mem_unitary (isSelfAdjoint_pathHamiltonian u) t) hz
  have he := rotation_distance ht hW hV (pulse_commutes u _ t z) hf hreal
  refine he.trans (add_le_add_left ?_ _)
  linarith only [mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ)≤2)]

/-- At each prescribed slack a positive density of sites excludes, at every
physical date, the entire family of transverse rotations by their midpoint
distance minus that slack. The identity date attains the midpoint value. -/
theorem gaussian_transverse_rotation_distance (b : ℝ) (hb : 0<b) :
    ∃ p > (0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∃ S : Finset (Fin (n+2)), p*((n+2:ℕ):ℝ) ≤ S.card ∧ ∀ s∈S, ∀ θ : ℝ,
        let W := unitaryEvolution (finitePauliMatrix (onsiteWord s 0)) θ
        let d := √(2-2*|cos θ|)
        HasProjectiveCircuitApproximation (n+2) 0 1 W ∧
        (∃ c : ℂ, ‖c‖=1 ∧ ‖c • (1:Reg n)-W‖=d) ∧ ∀ t : ℝ, ∀ z : ℂ, ‖z‖=1 →
          d ≤ ‖z • unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t-W‖+b := by
  let η := b/(21*π)
  have hη : 0<η := div_pos hb (by positivity)
  obtain ⟨p,hp,h⟩ := gaussian_path_eventual_isolated_sites 1 η hη
  refine ⟨p,hp,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  obtain ⟨S,hS,hs⟩ := hn
  refine ⟨S,hS,fun s hmem θ => ?_⟩
  obtain ⟨c,hc,C,hC,he⟩ := rotate_short_word (by omega : 2≤n+2) (onsiteWord s 0)
    (finitePauliWeight_pathWord_le n (.inl (s,0))) θ
  refine ⟨⟨c,hc,C,hC,by rw [he,sub_self,norm_zero]⟩,?_⟩
  simpa only [show 21*π*η=b by dsimp only [η]; field_simp] using
    spin_rotation _ s hη.le (hs s hmem) θ

#print axioms gaussian_transverse_rotation_distance
end
end GaloisForLFunctions.HTGeometry.TimePacking.IsolatedControls
