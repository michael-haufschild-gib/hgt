import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.UniformPackets
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.PhaseClock
import Mathlib.Data.Int.Interval

/-! # An absolute Diophantine margin at every integer mode height -/
open Filter Set Finset MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
noncomputable section

private def box (k j : ℕ) : Finset (Fin (2^(k+3)) → ℤ) :=
  Fintype.piFinset fun _ => Finset.Icc (-(2^j:ℕ):ℤ) ((2^j:ℕ):ℤ)

private theorem card_box (k j : ℕ) : (box k j).card=(2*2^j+1)^(2^(k+3)) := by
  rw [box,Fintype.card_piFinset_const,Int.card_Icc]
  congr 1
  omega

/-- With D=2^(k+3), the inverse margin grows at most polynomially
in the height H, of degree (D+1)(D-2). Its prefactor is deterministic. -/
def heightMargin (k H : ℕ) : ℝ :=
  let D := 2^(k+3)
  let count := (4*(H+1)+1)^D
  let den := 2^(k+2)*(H+1)*(1+modeStripPrice D (D-2) count)
  prefixModeAmplitude k*((den:ℝ)⁻¹)^(D-2)

theorem heightMargin_pos (k H : ℕ) : 0 < heightMargin k H := by
  unfold heightMargin
  exact mul_pos (prefixModeAmplitude_pos k) (pow_pos (inv_pos.mpr (by positivity)) _)

private theorem box_price (k H : ℕ) :
    let j := Nat.log 2 (H+1)+1
    heightMargin k H ≤ packetMargin k j (box k j).card := by
  intro j
  let D := 2^(k+3)
  let price := modeStripPrice D (D-2)
  have hpow : 2^j ≤ 2*(H+1) := by
    rw [show j=Nat.log 2 (H+1)+1 from rfl,pow_succ,mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 (Nat.succ_ne_zero H))
  have hc : (box k j).card ≤ (4*(H+1)+1)^D := by
    rw [card_box]
    exact Nat.pow_le_pow_left (by omega) D
  have hp : price (box k j).card ≤ price ((4*(H+1)+1)^D) := by
    dsimp only [price,modeStripPrice]
    gcongr
  have htime : 2^(k+j+1) ≤ 2^(k+2)*(H+1) := by
    rw [show k+j+1=k+1+j by omega,pow_add]
    apply (Nat.mul_le_mul_left _ hpow).trans_eq
    rw [←Nat.mul_assoc,←pow_succ]
  have hden := Nat.mul_le_mul htime (Nat.add_le_add_left hp 1)
  apply mul_le_mul_of_nonneg_left _ (prefixModeAmplitude_pos k).le
  apply pow_le_pow_left₀ (inv_nonneg.mpr (Nat.cast_nonneg _))
  change _ ≤ (1/2:ℝ)^(k+j+1)/(1+(price (box k j).card:ℝ))
  rw [←one_div,one_div_pow,div_div]
  have ht : (0:ℝ) < 2^(k+j+1)*(1+(price (box k j).card:ℝ)) := by positivity
  apply one_div_le_one_div_of_le ht
  exact_mod_cast hden

/-- On all sufficiently large prefixes of one Gaussian chain, every balanced
nonzero integer combination of the physical energies obeys the same explicit
height law. The mode can be selected after the whole spectrum is known. -/
theorem gaussian_all_heights :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let E := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (k+1))).isHermitian.eigenvalues
      ∀ H : ℕ, ∀ m : (Fin N→Bool)→ℤ, m ≠ 0 → ∑ i, m i = 0 → (∀ i, (m i).natAbs ≤ H) →
        heightMargin k H ≤ |∑ i, (m i:ℝ)*E i| := by
  filter_upwards [gaussian_all_packets box,gaussian_path_all_prefixes_maximally_projective] with ω hw hs
  filter_upwards [hw] with k hk
  intro N E H m hne hbal hm
  let j := Nat.log 2 (H+1)+1
  let θ := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let F := sortedEnsembleSpectrum (chainPauliFin_isHermitian N) θ
  obtain ⟨e,he⟩ := physical_sorted_order k ω (hs k).injective
  let a := m ∘ e.symm
  have ha : a≠0 := by
    intro h
    apply hne
    funext i
    simpa only [a,Function.comp_apply,e.symm_apply_apply,Pi.zero_apply] using congrFun h (e i)
  have hc : a∈box k j := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have h := (hm (e.symm i)).trans ((Nat.le_succ H).trans (Nat.lt_pow_succ_log_self (by decide : 1<2) (H+1)).le)
    rw [Finset.mem_Icc]
    change (a i).natAbs ≤ 2^j at h
    omega
  have hb : ∑ i, a i = 0 := (Equiv.sum_comp e.symm m).trans hbal
  have hh := (box_price k H).trans (hk j a hc ha hb)
  change heightMargin k H ≤ |∑ i, (a i:ℝ)*F i| at hh
  rw [←Equiv.sum_comp e (fun i => (a i:ℝ)*F i)] at hh
  have hEF (i) : F (e i)=E i := (he i).symm
  simpa only [a,Function.comp_apply,e.symm_apply_apply,hEF] using hh

#print axioms gaussian_all_heights
end
end GaloisForLFunctions.HTGeometry.SpectralJets.AllHeights
