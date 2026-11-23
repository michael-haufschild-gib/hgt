import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.DisjointMoments
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IncidentPauliTerms
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitDeletionBound
import GaloisForLFunctions.RHTower.InverseSquareChainCubicProjectiveFirstReturnLaw

/-! # Trace overlap after deleting the couplings incident to a circuit probe -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- Normalized trace on N qubits. -/
def regTrace {N : ℕ} (H : Reg N) := H.trace/(2:ℂ)^N

theorem norm_regTrace_le_one {N : ℕ} {V : Reg N} (hV : V∈unitary _) : ‖regTrace V‖≤1 := by
  rw [regTrace,norm_div,norm_pow,Complex.norm_ofNat,div_le_one (by positivity)]
  simpa only [CStarRing.norm_of_mem_unitary hV,mul_one,Fintype.card_fun,Fintype.card_bool,
    Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] using _root_.RHTower.norm_trace_le_card_mul_l2OpNorm V

/-- A unitary trace probe preserves the Hilbert–Schmidt deletion bound. -/
theorem trace_change {n : ℕ} (u v : PathShell n) (t : ℝ) (W : unitaryGroup (Fin (n+2)→Bool) ℂ) :
    ‖regTrace (W.valᴴ*unitaryEvolution (pathHamiltonian u) t)-
      regTrace (W.valᴴ*unitaryEvolution (pathHamiltonian v) t)‖ ≤
        |t| * Real.sqrt (∑ l : PathLabel n, (u l-v l)^2) := by
  rw [regTrace,regTrace,←sub_div,norm_div,norm_pow,Complex.norm_ofNat,
    div_le_iff₀ (by positivity)]
  exact (path_overlap_stability u v t W).trans_eq (by ring)

/-- Only terms meeting the probe support are removed. -/
theorem deleted_mass {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) :
    (∑ l : PathLabel n, (u l-pathShellOnSites Sᶜ u l)^2) ≤
      ∑ l ∈ S.biUnion pathIncidentLabels, (u l)^2 := by
  classical
  let L := S.biUnion pathIncidentLabels
  have hoff (l : PathLabel n) (_ : l∈univ) (hl : l∉L) :
      (u l-pathShellOnSites Sᶜ u l)^2=0 := by
    change (u l-(if PathWordSupportedIn Sᶜ l then u l else 0))^2=0
    rw [if_pos (path_supported_compl_of_not_incident S l hl),sub_self,zero_pow (by decide : 2≠0)]
  rw [←sum_subset (subset_univ L) hoff]
  apply sum_le_sum
  intro l _
  change (u l-(if PathWordSupportedIn Sᶜ l then u l else 0))^2 ≤ _
  split
  · simpa only [sub_self,zero_pow (by decide : 2≠0)] using sq_nonneg (u l)
  · rw [sub_zero]

/-- Normalized trace is multiplicative for operators on disjoint sites. -/
theorem disjoint_regTrace {N : ℕ} {S T : Finset (Fin N)} {A B : Reg N}
    (hd : Disjoint S T) (ha : IsSiteSupported S A) (hb : IsSiteSupported T B) :
    regTrace (A*B)=regTrace A*regTrace B := by
  let D := (2:ℂ)^N
  have hD : D≠0 := pow_ne_zero _ (by norm_num)
  have he := SpanningDensity.FixedHorizon.disjoint_trace_product hd ha hb
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at he
  change _/D=(_/D)*(_/D)
  rw [div_mul_div_comm,←he]
  exact (mul_div_mul_left _ _ hD).symm

/-- Every unitary probe supported on S has trace correlation bounded
by twice the time times the square root of the incident Pauli mass. -/
theorem supported_trace_covariance {n : ℕ} (S : Finset (Fin (n+2))) (u : PathShell n) (t : ℝ)
    (W : unitaryGroup (Fin (n+2)→Bool) ℂ) (hW : IsSiteSupported S W.val) :
    let U := unitaryEvolution (pathHamiltonian u) t
    ‖regTrace (W.valᴴ*U)-regTrace W.valᴴ*regTrace U‖ ≤
      2* |t| * Real.sqrt (∑ l ∈ S.biUnion pathIncidentLabels, (u l)^2) := by
  intro U
  let v := pathShellOnSites Sᶜ u
  let V := unitaryEvolution (pathHamiltonian v) t
  have hs : IsSiteSupported Sᶜ V := by
    apply isSiteSupported_unitaryEvolution
    rw [←pathHamiltonianOnSites_eq_pathHamiltonian_pathShellOnSites]
    exact pathHamiltonianOnSites_isSiteSupported _ _
  have hfac := disjoint_regTrace disjoint_compl_right hW.conjTranspose hs
  have h₁ := trace_change u v t W
  have h₂ := trace_change u v t 1
  simp only [OneMemClass.coe_one,Matrix.conjTranspose_one,one_mul] at h₂
  have hW₁ := norm_regTrace_le_one (Unitary.star_mem W.property)
  have h₃ := norm_sub_le_norm_sub_add_norm_sub (regTrace (W.valᴴ*U))
    (regTrace (W.valᴴ*V)) (regTrace W.valᴴ*regTrace U)
  rw [hfac,←mul_sub,norm_mul,norm_sub_rev (regTrace V)] at h₃
  have hm := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (deleted_mass S u)) (abs_nonneg t)
  have h₄ : ‖regTrace W.valᴴ‖*‖regTrace U-regTrace V‖ ≤ ‖regTrace U-regTrace V‖ :=
    mul_le_of_le_one_left (norm_nonneg _) hW₁
  change ‖regTrace (W.valᴴ*U)-regTrace (W.valᴴ*V)‖ ≤ _ at h₁
  change ‖regTrace U-regTrace V‖ ≤ _ at h₂
  change |t| * Real.sqrt (∑ l : PathLabel n, (u l-v l)^2) ≤ _ at hm
  rw [hfac] at h₁
  linarith only [h₃,h₁,h₂,h₄,hm]

#print axioms supported_trace_covariance
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk.SparseProbes
