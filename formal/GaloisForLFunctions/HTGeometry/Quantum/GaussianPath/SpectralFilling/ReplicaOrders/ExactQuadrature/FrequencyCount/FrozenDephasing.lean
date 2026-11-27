import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.FrequencyCount.Interpolation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPauliPrefixPhaseLaw
import GaloisForLFunctions.HTGeometry.ReplicaCollisionExtremality

/-! # Duration of an exact dephasing measurement on one frozen chain -/
open Finset Real MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section

/-- For a maximally projective spectrum all off-diagonal coherences have
distinct signed frequencies. Erasing every coherence exactly incurs a
cost proportional to the number of ordered pairs of distinct levels. -/
theorem dephasing_count {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (E : I → ℝ) (hmax : MaximallyProjectiveEnergy E) (p t : J → ℝ)
    (hp : ∀ j, 0≤p j) (hm : ∑ j, p j=1) {a b W : ℝ} (hab : a≤b)
    (hr : ∀ j, t j∈Set.Icc a b) (hW : 0≤W) (he : ∀ i k, |E i-E k|≤W)
    (hz : ∀ i k, i≠k → ∑ j, (p j:ℂ)*wave (E i-E k) (t j)=0) :
    ((Fintype.card I*(Fintype.card I-1):ℕ):ℝ)*log 2 ≤ (b-a)*W := by
  classical
  let S := (univ : Finset I).offDiag
  let e := S.equivFin.symm
  let P (i : Fin S.card) : {p : I×I // p.1≠p.2} :=
    ⟨(e i).val,(mem_offDiag.mp (e i).property).2.2⟩
  have hi : Function.Injective P := by
    intro i j h
    have he := congrArg (fun x : {p : I×I // p.1≠p.2} => x.val) h
    exact e.injective (Subtype.ext he)
  let d (v : {p : I×I // p.1≠p.2}) := E v.val.1-E v.val.2
  have hd : Function.Injective d := maximallyProjectiveEnergy_orientedGap_injective E hmax
  have h := cancellation_count (d ∘ P) (hd.comp hi) p t hp hm hab hr hW
    (fun i => he _ _) (fun i => hz _ _ (P i).property)
  simpa only [S,offDiag_card,card_univ,Nat.mul_sub_left_distrib,Nat.mul_one] using h

/-- Every prefix of at least three qubits on a single typical Gaussian
path has the quadratic duration floor for all positive dephasing clocks. -/
theorem gaussian_dephasing_duration :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let K := k+3
      let D := 2^K
      let H : selfAdjoint (Matrix (Fin K → Bool) (Fin K → Bool) ℂ) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      ∀ m : ℕ, ∀ a b : ℝ, a≤b → ∀ p t : Fin m → ℝ, (∀ j, 0≤p j) → (∑ j, p j=1) →
        (∀ j, t j∈Set.Icc a b) →
        (∀ i k, i≠k → ∑ j, (p j:ℂ)*wave (E i-E k) (t j)=0) →
        ((D*(D-1):ℕ):ℝ)*log 2 ≤ (b-a)*circuitHamiltonianSpectralWidth H := by
  filter_upwards [gaussian_path_all_prefixes_maximally_projective] with ω hw k
  intro K D H E m a b hab p t hp hm hr hz
  have hband (i j : Fin K → Bool) : |E i-E j|≤circuitHamiltonianSpectralWidth H := by
    have hi := inf'_le E (mem_univ i)
    have hj := inf'_le E (mem_univ j)
    have hI := le_sup' E (mem_univ i)
    have hJ := le_sup' E (mem_univ j)
    rw [abs_le]
    unfold circuitHamiltonianSpectralWidth
    constructor <;> linarith only [hi,hj,hI,hJ]
  simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using
    dephasing_count E (hw k) p t hp hm hab hr (circuitHamiltonianSpectralWidth_nonneg H) hband hz

#print axioms gaussian_dephasing_duration
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
