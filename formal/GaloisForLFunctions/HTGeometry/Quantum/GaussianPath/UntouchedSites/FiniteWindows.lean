import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.CircuitReturns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.Aliasing
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw
import GaloisForLFunctions.HTGeometry.EternityOperatorReturnCorollary
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # Uniform gate lower bound on compact time windows away from zero -/
open Set MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.UntouchedSites
noncomputable section

/-- A scalar at a nonzero time would freeze every relative phase.
With three or more levels a maximally projective spectrum can freeze
at most one independent frequency at that time. -/
theorem no_scalar_time {I : Type} [Fintype I] [DecidableEq I] (ref : I)
    (hc : 3 ≤ Fintype.card I) (H : selfAdjoint (Matrix I I ℂ))
    (hi : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {t : ℝ} (ht : t ≠ 0) (z : ℂ) :
    unitaryEvolution H.val t ≠ z • (1 : Matrix I I ℂ) := by
  classical
  letI : Nonempty I := ⟨ref⟩
  intro hz
  let E := H.2.isHermitian.eigenvalues
  let J := {j : I // j ≠ ref}
  have hcJ : 1 < Fintype.card J := by
    have hcard : Fintype.card J = Fintype.card I - 1 := by simp [J,Fintype.card_subtype_compl]
    omega
  letI : Nontrivial J := Fintype.one_lt_card_iff_nontrivial.mp hcJ
  have hzero := norm_unitaryEvolution_sub_anchorPhase_le_two_mul_of_scalar H.2.isHermitian ref t z
  rw [hz,sub_self,norm_zero,mul_zero,←hz] at hzero
  have ha := (mem_anchoredProjectiveReturnTarget_zero_iff E ref t).mp
    ((mem_anchoredProjectiveReturnTarget_iff_l2_opNorm H.2.isHermitian ref t le_rfl).mpr hzero)
  obtain ⟨b,hb⟩ := AdaptiveSampling.exists_free_deletion (projectiveFrequency E ref)
    (maximallyProjectiveEnergy_projectiveFrequency_independent E hi ref) t ht
  obtain ⟨j,hj⟩ := exists_ne b
  let k : {j : J // j ≠ b} := ⟨j,hj⟩
  obtain ⟨m,hm⟩ := ha j
  let ch (l : {j : J // j ≠ b}) : ℤ := if l=k then 1 else 0
  have hf : finiteTorusCharacterDetuning ch (fun l => projectiveFrequency E ref l.val) =
      E j-E ref := by
    unfold finiteTorusCharacterDetuning
    rw [Finset.sum_eq_single k (fun l _ hl => by simp only [ch,if_neg hl,Int.cast_zero,zero_mul])
      (fun h => (h (Finset.mem_univ k)).elim)]
    simp only [ch,if_pos rfl,Int.cast_one,one_mul]
    rfl
  have hh := hb ch m (by rw [hf,mul_comm (m:ℝ)]; exact hm)
  have hh' := congrFun hh k
  simp [ch] at hh'

/-- On every nonzero compact positive-time interval of every Gaussian
prefix with at least three qubits, some strictly positive precision excludes
all circuits with fewer than half as many gates as qubits throughout. -/
theorem gaussian_compact_gate_floor :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let n := k+3
      let H := pathHamiltonian (pathPauliDisorderShell ω (k+1))
      ∀ a b : ℝ, 0 < a → a ≤ b → ∃ δ > 0, ∀ t ∈ Icc a b, ∀ s : ℕ, 2*s<n →
        ¬HasProjectiveCircuitApproximation n δ s (unitaryEvolution H t) := by
  filter_upwards [gaussian_few_gate_scalar_return,gaussian_path_all_prefixes_maximally_projective] with ω hω hm k
  intro n H a b hpos hab
  let M : selfAdjoint (SpinMatrix (Fin n)) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  let ref : Fin n → Bool := fun _ => false
  have hc : 3 ≤ Fintype.card (Fin n → Bool) := by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
    exact (by decide : 3 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp [n]; omega))
  let s := (n-1)/2
  have hs : 2*s<n := by dsimp [s,n]; omega
  obtain ⟨A,_,hA⟩ := hω (k+1)
  have hsep (t : ℝ) (ht : a ≤ t) : 0 < orbitCircuitDistance M s t := by
    by_contra! he
    have hcheap := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H t) s 0).mpr he
    obtain ⟨z,_,C,hC,hz⟩ := hA t 0 s hs hcheap
    rw [zeroGateCircuit_eval C hC,mul_zero,norm_le_zero_iff,sub_eq_zero] at hz
    exact no_scalar_time ref hc M (hm k) (hpos.trans_le ht).ne' z hz
  obtain ⟨t,ht,hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hab)
    (orbitCircuitDistance_lipschitz M s).continuous.continuousOn
  refine ⟨orbitCircuitDistance M s t/2,half_pos (hsep t ht.1),?_⟩
  rintro u hu j hj ⟨z,hz,C,hC,herr⟩
  have hj' : j ≤ s := by dsimp [s]; omega
  have hle := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H u) s _).mp
    ⟨z,hz,C,hC.trans hj',herr⟩
  have hmin' : orbitCircuitDistance M s t ≤ orbitCircuitDistance M s u := hmin hu
  exact (not_le_of_gt (half_lt_self (hsep t ht.1))) (hmin'.trans hle)

#print axioms no_scalar_time
#print axioms gaussian_compact_gate_floor
end
end GaloisForLFunctions.HTGeometry.UntouchedSites
