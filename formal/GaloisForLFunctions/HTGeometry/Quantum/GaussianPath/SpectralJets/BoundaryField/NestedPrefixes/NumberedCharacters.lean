import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.NestedPrefixes.JointActions
import GaloisForLFunctions.RHTower.StaticChoiProjectiveComplexityPlateau

/-! # Integer characters on the physical zero-anchored phase coordinates -/

open Filter MeasureTheory
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
noncomputable section

/-- Balanced weights representing a character of the numbered phase differences. -/
def numberedPacket {d : ℕ} (m : Fin d → ℤ) : Fin (d+1) → ℤ :=
  Fin.cases (∑ i, m i) (fun i => -m i)

theorem numberedPacket_sum {d : ℕ} (m : Fin d → ℤ) : ∑ i, numberedPacket m i=0 := by
  rw [Fin.sum_univ_succ]
  simp only [numberedPacket,Fin.cases_zero,Fin.cases_succ,Finset.sum_neg_distrib,add_neg_cancel]

theorem numberedPacket_action {d : ℕ} (E : Fin (d+1) → ℝ) (m : Fin d → ℤ) :
    (∑ i, (numberedPacket m i:ℝ)*E i)=finiteTorusCharacterDetuning m (RHTower.zeroProjectiveFrequency E) := by
  rw [Fin.sum_univ_succ]
  simp only [numberedPacket,Fin.cases_zero,Fin.cases_succ,Int.cast_sum,Int.cast_neg,neg_mul,Finset.sum_neg_distrib,
    finiteTorusCharacterDetuning,RHTower.zeroProjectiveFrequency,mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  rw [sub_eq_add_neg]

/-- Reindexing the jointly independent spectra in the physical eigenbases
gives independent numbered phase differences for every prefix simultaneously. -/
theorem gaussian_joint_numbered :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (n : ℕ) (d : Fin n → ℕ)
      (e : ∀ j, Config j.val ≃ Fin (d j+1)),
      let E (j : Fin n) := (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (j.val+1))).isHermitian.eigenvalues ∘ (e j).symm
      RationallyIndependentFrequency (fun z : (j : Fin n) × Fin (d j) => RHTower.zeroProjectiveFrequency (E z.1) z.2) := by
  classical
  filter_upwards [gaussian_nested_actions] with ω hω
  intro n d e E m hm
  choose b hsort using fun j : Fin n => ordered_at_zero j.val ω
  let q (j : Fin n) := numberedPacket (fun i => m ⟨j,i⟩)
  let p (j : Fin n) := (b j).trans (e j)
  have hs (j : Fin n) : (∑ i, q j (p j i))=0 :=
    (Equiv.sum_comp (p j) (q j)).trans (numberedPacket_sum _)
  have ha (j : Fin n) : action j.val (fun i => q j (p j i)) ω=
      finiteTorusCharacterDetuning (fun i => m ⟨j,i⟩) (RHTower.zeroProjectiveFrequency (E j)) := by
    unfold action
    rw [hsort j]
    have hE (i : Config j.val) : E j (p j i)=
        (isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω (j.val+1))).isHermitian.eigenvalues (b j i) := by
      simp only [E,p,Equiv.trans_apply,Function.comp_apply,Equiv.symm_apply_apply]
    calc
      _ = ∑ i, (q j (p j i):ℝ)*E j (p j i) := by simp only [hE,Function.comp_apply]
      _ = ∑ i, (q j i:ℝ)*E j i := Equiv.sum_comp (p j) (fun i => (q j i:ℝ)*E j i)
      _ = _ := numberedPacket_action (E j) _
  have hsum : (∑ j, action j.val (fun i => q j (p j i)) ω)=0 := by
    simpa only [ha,finiteTorusCharacterDetuning,Fintype.sum_sigma] using hm
  have h := hω n _ hs hsum
  funext z
  obtain ⟨j,i⟩ := z
  have hz := congrFun (h j) ((p j).symm i.succ)
  simpa only [Equiv.apply_symm_apply,q,numberedPacket,Fin.cases_succ,Pi.zero_apply,neg_eq_zero] using hz

#print axioms gaussian_joint_numbered
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.NestedPrefixes
