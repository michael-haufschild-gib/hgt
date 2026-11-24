import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.SpectralRatios
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ExactContacts.CoarseVisits.ContactSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.FirstVisit

/-! # Fine-error gate cost in every basis at a first physical return -/

open Set MeasureTheory Filter Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
open AccuracyScales.MaximumIntervals PrecisionReturns
noncomputable section

private abbrev Reg (N : ℕ) := DiagonalSynthesis.Register N
private abbrev Basis (N : ℕ) := unitaryGroup (Fin N → Bool) ℂ

private theorem spectrum_conj {N : ℕ} (W : Basis N) (M : Reg N) :
    spectrum ℂ (W.val*M*star W.val)=spectrum ℂ M := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly]
  rw [Matrix.charpoly_mul_comm (W.val*M),←mul_assoc,W.property.1,one_mul]

private theorem exact_spectral_bound (ω : PathPauliDisorder) (k : ℕ) (t : ℝ)
    (hi : AlgebraicIndependent ℚ (contactPhases ω k t)) (W : Basis (k+3))
    (C : TwoQubitCircuit (k+3)) (z : ℂ) (hz : ‖z‖=1)
    (he : W.val*unitaryEvolution (chainGenerator ω k).val t*star W.val=z • C.eval.val) :
    2^(k+3)-1 ≤ C.gateCount*16 := by
  classical
  let H := chainGenerator ω k
  let E := H.2.isHermitian.eigenvalues
  let r : Fin (k+3) → Bool := fun _ => false
  let p i := anchorPhase E i t
  let g i := z⁻¹*p i
  have hn : z≠0 := fun h => zero_ne_one (by simpa only [h,norm_zero] using hz)
  have hp (i) : p i ∈ spectrum ℂ (z • C.eval.val) := by
    rw [←he,spectrum_conj,unitaryEvolution_spectral H.2.isHermitian,spectrum_conj,spectrum_diagonal]
    exact ⟨i,rfl⟩
  have hg (i) : g i ∈ spectrum ℂ C.eval.val := by
    apply (spectrum.smul_mem_smul_iff (r:=Units.mk0 z hn)).mp
    change z*(z⁻¹*p i) ∈ spectrum ℂ (z • C.eval.val)
    rw [←mul_assoc,mul_inv_cancel₀ hn,one_mul]
    exact hp i
  have hrel (i : {i // i≠r}) : g i.val/g r=contactPhases ω k t i := by
    dsimp only [g]
    rw [mul_div_mul_left _ _ (inv_ne_zero hn)]
    simp only [p,anchorPhase,contactPhases,energyPhase,projectiveFrequency,←Complex.exp_sub]
    congr 1
    dsimp only [E,H,r]
    push_cast
    ring
  have hb := spectral_ratio_gate_bound C (g r) (hg r) (fun i : {i // i≠r} => g i.val)
    (fun i => hg i.val) (by simpa only [hrel] using hi)
  rw [Fintype.card_subtype_compl (fun i => i=r),Fintype.card_subtype_eq] at hb
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hb

/-- Absence of an exact fit in every basis gives one positive error
excluding every basis, by attainment of the least distance. -/
private theorem positive_basis_floor {N s : ℕ} (M : Reg N)
    (h : ∀ W : Basis N, ¬ HasProjectiveCircuitApproximation N 0 s (W.val*M*star W.val)) :
    ∃ δ > (0:ℝ), ∀ W : Basis N, ¬ HasProjectiveCircuitApproximation N δ s (W.val*M*star W.val) := by
  letI : CompactSpace (Basis N) := isCompact_iff_compactSpace.mp isCompact_matrixUnitaryGroup
  let f (W : Basis N) := Metric.infDist (W.val*M*star W.val) (phaseCircuitMatrixImageAtMost N s)
  have hf : Continuous f := (Metric.continuous_infDist_pt _).comp
    ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star)
  obtain ⟨V,_,hv⟩ := isCompact_univ.exists_isMinOn univ_nonempty hf.continuousOn
  have hp : 0 < f V := lt_of_not_ge fun hu =>
    h V ((hasProjectiveCircuitApproximation_iff_infDist ..).mpr hu)
  refine ⟨f V/2,half_pos hp,?_⟩
  intro W hw
  have hl := isMinOn_iff.mp hv W (mem_univ W)
  exact (half_lt_self hp).not_ge (hl.trans ((hasProjectiveCircuitApproximation_iff_infDist ..).mp hw))

/-- Away from countably many coarse tolerances on the entire frozen
chain, every genuine first physical visit requires exponentially many
gates at a finer positive error even with a free unitary change of basis. -/
theorem gaussian_first_visit_in_every_basis :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∃ E : Set ℝ, E.Countable ∧ ∀ e > (0:ℝ), e ∉ E →
      ∀ (k s : ℕ) (a : ℝ), let H := chainGenerator ω k
        e < orbitCircuitDistance H s a → let v := firstVisit H a s e
          ∃ δ > (0:ℝ), ∀ W : Basis (k+3), ¬ HasProjectiveCircuitApproximation (k+3) δ (fineBudget k)
            (W.val*unitaryEvolution H.val v*star W.val) := by
  filter_upwards [gaussian_first_visit_spectral_independence] with ω h
  obtain ⟨E,hE,hh⟩ := h
  refine ⟨E,hE,?_⟩
  intro e he hreg k s a H hout v
  apply positive_basis_floor
  rintro W ⟨z,hz,C,hC,herr⟩
  have hc := exact_spectral_bound ω k v (hh e he hreg k s a hout) W C z hz
    (sub_eq_zero.mp (norm_le_zero_iff.mp herr))
  have hd : 16*fineBudget k < 2^(k+3)-1 := by
    have h := Nat.div_mul_le_self (2^(k+3)-2) 16
    have hp : 2 ≤ 2^(k+3) := (show 2^1 ≤ 2^(k+3) from Nat.pow_le_pow_right (by decide) (by omega))
    dsimp only [fineBudget]; omega
  omega

#print axioms gaussian_first_visit_in_every_basis
end
end GaloisForLFunctions.HTGeometry.ExactContacts.CoarseVisits
