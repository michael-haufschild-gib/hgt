import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Interpolation.HarmonicGates
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.ShortWord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage

/-! # Ancilla-free fractional powers on a short spectral arc -/

open Matrix Complex
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
open private projectiveApproximation_smul from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
noncomputable section
private abbrev Reg (K : ℕ) := Matrix (Fin K → Bool) (Fin K → Bool) ℂ

/-- A circuit whose eigenangle span is at most one radian has uniformly
affordable fractional powers throughout the arc. The average eigenangle
contributes only a global phase. -/
theorem arc_power {K : ℕ} (hK : 2 ≤ K) (C : TwoQubitCircuit K)
    (V : unitary (Reg K)) (θ : (Fin K → Bool) → ℝ) (hC : C.eval.val=packet V θ)
    (hw : ∀ i j, |θ i-θ j| ≤ 1) (m : ℕ) (hm : 0 < m) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    HasProjectiveCircuitApproximation K (1/630+120/(m:ℝ)) (40*(K+1)*m^3*(C.gateCount+2*K+1))
      (packet V (fun i => u*θ i)) := by
  let G (l : ℕ) (t : ℝ) (i : Fin K → Bool) := 2*t*sineReading θ l i
  let a := G 1 (4*u/5)
  let b := G 2 (-u/5)
  let c := G 3 (4*u/105)
  let d := G 4 (-u/280)
  have fit (l : ℕ) (t : ℝ) (h : |t| ≤ 1) := harmonic_gate hK C V θ hC l m hm t h
  have h₁ := fit 1 (4*u/5) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have h₂ := fit 2 (-u/5) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have h₃ := fit 3 (4*u/105) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have h₄ := fit 4 (-u/280) (abs_le.mpr ⟨by linarith,by linarith⟩)
  have hprod := LocalPatches.approx_product (packet_unitary V d)
    (LocalPatches.approx_product (packet_unitary V c)
      (LocalPatches.approx_product (packet_unitary V b) h₁ h₂) h₃) h₄
  simp only [packet_add] at hprod
  obtain ⟨z,hz,D,hcost,hd⟩ := hprod
  let f (i : Fin K → Bool) := a i+b i+c i+d i
  change ‖packet V f-z • D.eval.val‖ ≤ _ at hd
  have hnear : ‖packet V (fun i => u*(θ i-angleMean θ))-packet V f‖ ≤ 1/630 := by
    apply packet_distance _ _ _ (by norm_num)
    intro i
    have hi := trace_angles θ hw i
    have he : u*(θ i-angleMean θ)-f i=u*((θ i-angleMean θ)-
        (8/5*sineReading θ 1 i-2/5*sineReading θ 2 i+8/105*sineReading θ 3 i-
        1/140*sineReading θ 4 i)) := by dsimp only [f,a,b,c,d,G]; ring
    rw [he,abs_mul,abs_of_nonneg hu]
    exact (mul_le_mul hu' hi (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hm' : HasProjectiveCircuitApproximation K (1/630+120/(m:ℝ))
      (40*(K+1)*m^3*(C.gateCount+2*K+1)) (packet V (fun i => u*(θ i-angleMean θ))) := by
    refine ⟨z,hz,D,?_,?_⟩
    · apply hcost.trans
      ring_nf
      omega
    · exact (norm_sub_le_norm_sub_add_norm_sub _ (packet V f) _).trans
        ((add_le_add hnear hd).trans_eq (by ring))
  have hshift := projectiveApproximation_smul
    (show ‖phaseValue (u*angleMean θ)‖=1 from Complex.norm_exp_ofReal_mul_I _) hm'
  rw [←packet_shift] at hshift
  have he : (fun i => u*angleMean θ+u*(θ i-angleMean θ))=(fun i => u*θ i) := funext fun _ => by ring
  rwa [he] at hshift

/-- The angular error and the circuit synthesis error together fit within
the $1/400$ allowance for interpolating two physical visits. -/
theorem arc_power_chord {K : ℕ} (hK : 2 ≤ K) (C : TwoQubitCircuit K)
    (V : unitary (Reg K)) (θ : (Fin K → Bool) → ℝ) (hC : C.eval.val=packet V θ)
    (hw : ∀ i j, |θ i-θ j| ≤ 1) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    HasProjectiveCircuitApproximation K (1/400) (40*(K+1)*200000^3*(C.gateCount+2*K+1))
      (packet V (fun i => u*θ i)) := by
  obtain ⟨z,hz,D,hD,hfit⟩ := arc_power hK C V θ hC hw 200000 (by norm_num) hu hu'
  exact ⟨z,hz,D,hD,hfit.trans (by norm_num)⟩

#print axioms arc_power_chord
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Interpolation
