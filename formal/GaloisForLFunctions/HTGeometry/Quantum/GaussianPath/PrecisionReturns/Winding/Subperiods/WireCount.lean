import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.PhaseSeparation
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.ResidueCompression
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.TouchedSpectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! # Physical wires required by the residue spectrum at a subperiod -/

open Set Real Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
open ClockSpectrum SpectralApproximation
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ

private theorem conj_spectrum {I : Type*} [Fintype I] [DecidableEq I]
    (V : unitaryGroup I ℂ) (M : Matrix I I ℂ) : spectrum ℂ (V.val*M*star V.val)=spectrum ℂ M := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly]
  rw [Matrix.charpoly_mul_comm (V.val*M),←mul_assoc,V.property.1,one_mul]

private theorem phase_in_spectrum {N : ℕ} (H : selfAdjoint (Reg N)) (t : ℝ) (i : Fin N → Bool) :
    expTurns (t*(-H.2.isHermitian.eigenvalues i/(2*π))) ∈ spectrum ℂ (unitaryEvolution H.val t) := by
  let V := H.2.isHermitian.eigenvectorUnitary
  rw [unitaryEvolution_spectral H.2.isHermitian,conj_spectrum V,spectrum_diagonal]
  refine ⟨i,?_⟩
  have h : 2*π*(t*(-H.2.isHermitian.eigenvalues i/(2*π)))= -(t*H.2.isHermitian.eigenvalues i) := by
    field_simp [pi_ne_zero]
  rw [expTurns,h]
  apply congrArg Complex.exp
  push_cast
  ring

/-- A circuit approximating the physical evolution at a coprime
subdivision must accommodate every distinct winding residue in the
spectrum of its active register. This holds in every unitary basis. -/
theorem wire_count {N : ℕ} (H : selfAdjoint (Reg N)) {v R : ℝ} {b : Fin N → Bool} {z : (Fin N → Bool) → ℤ}
    (hz : Anchored (fun i => -H.2.isHermitian.eigenvalues i/(2*π)) v R b z) (hR : R<1)
    {d j : ℕ} (hd : 0<d) (hj : d.Coprime j) {ε : ℝ} (hε : 2*ε < 4*(1-(j:ℝ)*R)/d)
    (V : unitaryGroup (Fin N → Bool) ℂ) (C : TwoQubitCircuit N) (c : ℂ)
    (hfit : ‖V.val*unitaryEvolution H.val ((j:ℝ)/d*v)*star V.val-c • C.eval.val‖ ≤ ε) :
    (residues z d).card+1 ≤ 2^C.touchedSites.card := by
  classical
  let w := fun i => -H.2.isHermitian.eigenvalues i/(2*π)
  let t := (j:ℝ)/d*v
  let S := Finset.univ.image (fun i => z i%(d:ℤ))
  have hz₀ : z b=0 := by
    have hh := hz b
    simp only [sub_self,mul_zero,zero_sub] at hh
    have h₀ : z b≤0 := by exact_mod_cast (show (z b:ℝ)≤0 by linarith only [hh.1])
    have h₁ : (-1:ℤ)<z b := by exact_mod_cast (show (-1:ℝ)<(z b:ℝ) by linarith only [hh.2,hR])
    omega
  have hmem : 0∈S := Finset.mem_image.mpr ⟨b,Finset.mem_univ _,by rw [hz₀,Int.zero_emod]⟩
  have hsz : (residues z d).card+1=S.card := Finset.card_erase_add_one hmem
  let F := S.equivFin.symm
  have pre (k : Fin S.card) : ∃ i, z i%(d:ℤ)=(F k).val := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (F k).property
    exact ⟨i,hi⟩
  choose p hp using pre
  let y := fun k => expTurns (t*w (p k))
  let m := 4*(1-(j:ℝ)*R)/d
  have sep (k l : Fin S.card) (hkl : k≠l) : 2*(m/2) ≤ ‖y k-y l‖ := by
    have hn : z (p k)%(d:ℤ) ≠ z (p l)%(d:ℤ) := fun he => hkl
      (F.injective (Subtype.ext ((hp k).symm.trans (he.trans (hp l)))))
    rw [show 2*(m/2)=m by ring]
    exact divided_phase_separation hz hd hj hn
  have hspec (k : Fin S.card) : y k∈spectrum ℂ (V.val*unitaryEvolution H.val t*star V.val) := by
    rw [conj_spectrum]
    exact phase_in_spectrum H t (p k)
  letI : CStarAlgebra (Reg N) := {}
  letI : IsStarNormal (c • C.eval.val) := by
    constructor
    change star (c • C.eval.val)*(c • C.eval.val)=(c • C.eval.val)*star (c • C.eval.val)
    rw [star_smul,smul_mul_smul_comm,smul_mul_smul_comm,C.eval.property.1,C.eval.property.2,mul_comm]
  have hε' : ε < m/2 := by change 2*ε < m at hε; linarith only [hε]
  obtain ⟨f,hi,hf⟩ := separated_spectrum_count y hspec (hfit.trans_lt hε') sep
  rw [hsz]
  exact supported_spectrum_count (IsSiteSupported.complex_smul c C.isSiteSupported_touchedSites) f hi hf

#print axioms wire_count
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
