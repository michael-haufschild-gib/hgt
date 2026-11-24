import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.TouchedSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.PhaseComparison
import Mathlib.LinearAlgebra.Eigenspace.Matrix

/-! # Spectral centers of a circuit fit in an arbitrary basis -/

open Real Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
noncomputable section

private theorem spectrum_conj {I : Type*} [Fintype I] [DecidableEq I]
    (V : unitaryGroup I ℂ) (M : Matrix I I ℂ) : spectrum ℂ (V.val*M*star V.val)=spectrum ℂ M := by
  ext z
  simp only [Matrix.mem_spectrum_iff_isRoot_charpoly]
  rw [Matrix.charpoly_mul_comm (V.val*M),←mul_assoc,V.property.1,one_mul]

/-- Every eigenphase of the evolution is near a spectral point of a
normal approximant. A register supported on S has at most 2^|S|
distinct centers, including after an arbitrary basis change. -/
theorem centers_of_supported_fit {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ)
    (V : unitaryGroup (Fin N→Bool) ℂ) {S : Finset (Fin N)} {B : Register N}
    (hs : IsSiteSupported S B) (hB : star B*B=B*star B) {ε : ℝ} (he : 0<ε)
    (hfit : ‖V.val*unitaryEvolution H.val t*star V.val-B‖≤ε) :
    ∃ f : (Fin N→Bool) → ℂ, (univ.image f).card ≤ 2^S.card ∧
      ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f i‖ < 2*ε := by
  classical
  letI : CStarAlgebra (Register N) := {}
  letI : IsStarNormal B := ⟨hB⟩
  have hv (i : Fin N→Bool) : anchorPhase H.2.isHermitian.eigenvalues i t ∈
      spectrum ℂ (V.val*unitaryEvolution H.val t*star V.val) := by
    rw [spectrum_conj,unitaryEvolution_spectral H.2.isHermitian,
      spectrum_conj H.2.isHermitian.eigenvectorUnitary,spectrum_diagonal]
    exact ⟨i,rfl⟩
  choose f hf hdist using fun i => SpectralApproximation.nearby_spectral_point (hv i)
    (hfit.trans_lt (by linarith only [he] : ε<2*ε))
  let P := univ.image f
  let p := P.equivFin.symm
  refine ⟨f,?_,hdist⟩
  apply SpectralApproximation.supported_spectrum_count hs (fun k => (p k).val) (Subtype.val_injective.comp p.injective)
  intro k
  obtain ⟨i,_,hi⟩ := mem_image.mp (p k).property
  exact hi ▸ hf i

/-- A circuit's touched wires bound its number of centers by four to
the gate count. -/
theorem centers_of_fit {N : ℕ} (H : selfAdjoint (Register N)) (t : ℝ)
    (V : unitaryGroup (Fin N→Bool) ℂ) (C : TwoQubitCircuit N) (z : ℂ) {ε : ℝ} (he : 0<ε)
    (hfit : ‖V.val*unitaryEvolution H.val t*star V.val-z • C.eval.val‖≤ε) :
    ∃ f : (Fin N→Bool) → ℂ, (univ.image f).card ≤ 4^C.gateCount ∧
      ∀ i, ‖anchorPhase H.2.isHermitian.eigenvalues i t-f i‖ < 2*ε := by
  have hnorm : star (z • C.eval.val)*(z • C.eval.val)=(z • C.eval.val)*star (z • C.eval.val) := by
    rw [star_smul,smul_mul_smul_comm,smul_mul_smul_comm,C.eval.property.1,C.eval.property.2,mul_comm]
  obtain ⟨f,hf,hnear⟩ := centers_of_supported_fit H t V (C.isSiteSupported_touchedSites.complex_smul z) hnorm he hfit
  refine ⟨f,hf.trans ?_,hnear⟩
  calc 2^C.touchedSites.card ≤ 2^(2*C.gateCount) := Nat.pow_le_pow_right (by decide) C.card_touchedSites_le
       _ = _ := by rw [pow_mul]; rfl

private theorem phase_eq {I : Type*} (E : I → ℝ) (i : I) (t : ℝ) :
    anchorPhase E i t=Complex.exp ((-(t*E i):ℝ)*Complex.I) := by
  apply congrArg Complex.exp
  push_cast
  ring

/-- Two phase coordinates assigned to one center within twice the
tolerance force the corresponding gap to return within one tolerance
in turns. -/
theorem gap_of_shared_center {I : Type*} (E : I → ℝ) (i j : I) (t : ℝ)
    {z : ℂ} {ε : ℝ} (hi : ‖anchorPhase E i t-z‖<2*ε) (hj : ‖anchorPhase E j t-z‖<2*ε) :
    latticeClose (t*(E i-E j)/(2*π)) ε := by
  let a := -(t*E j)
  let b := -(t*E i)
  let m := round ((a-b)/(2*π))
  have hgap : a-b=t*(E i-E j) := by dsimp only [a,b]; ring
  have hh := four_mul_abs_sub_int_le_norm a b m (abs_sub_round _)
  have hd := norm_sub_le_norm_sub_add_norm_sub (anchorPhase E j t) z (anchorPhase E i t)
  rw [norm_sub_rev z,phase_eq E j t,phase_eq E i t] at hd
  refine ⟨m,?_⟩
  rw [←hgap]
  have hn := hh.trans hd
  rw [←phase_eq E j t,←phase_eq E i t] at hn
  linarith only [hn,hi,hj]

/-- A return of an energy gap in turns bounds the corresponding chord
error with its physical angular factor. -/
theorem chord_of_gap {I : Type*} (E : I → ℝ) (i j : I) (t : ℝ) {r : ℝ}
    (h : latticeClose (t*(E i-E j)/(2*π)) r) :
    ‖anchorPhase E i t-anchorPhase E j t‖ ≤ 2*π*r := by
  obtain ⟨m,hm⟩ := h
  rw [norm_sub_rev,phase_eq,phase_eq]
  have hb := norm_expI_sub_expI_le (-(t*E j)) (-(t*E i)) m
  apply hb.trans
  rw [show -(t*E j)- -(t*E i)-2*π*m=2*π*(t*(E i-E j)/(2*π)-m) by field_simp [pi_ne_zero]; ring,
    abs_mul,abs_of_pos two_pi_pos]
  exact mul_le_mul_of_nonneg_left hm.le two_pi_pos.le

#print axioms centers_of_fit
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.SpectatorReturns
