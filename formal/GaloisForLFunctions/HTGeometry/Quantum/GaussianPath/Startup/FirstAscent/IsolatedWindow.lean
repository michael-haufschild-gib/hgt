import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.FieldDelay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ChordSlope

/-! # A whole interval affordable by rotations on isolated sites -/
open Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- For a nearly isolated field larger than 126 times the per-term error,
the gate word pays for an interval whose inverse time scale loses one
field strength per selected site. -/
theorem isolated_window {n : ℕ} (u : PathShell n) (S : Finset (Fin (n+2))) (q η : ℝ)
    (hη : 0≤η) (hq : 126*η≤|q|) (hs : ∀ s ∈ S, isolatedLongitudinalSite u q η s)
    (θ : ℝ) (hθ : θ≤π/4) (t : ℝ) (ht : 0≤t) :
    let H : selfAdjoint (Reg (n+2)) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    t*(circuitHamiltonianSpectralWidth H-(S.card:ℝ)* |q|) ≤ 4*θ →
      HasProjectiveCircuitApproximation (n+2) (2*sin θ) S.card (unitaryEvolution H.val t) := by
  intro H hbefore
  let J : selfAdjoint (Reg (n+2)) := ⟨_,isSelfAdjoint_pathHamiltonianOnSites Sᶜ u⟩
  let W := circuitHamiltonianSpectralWidth H
  let w := circuitHamiltonianSpectralWidth J
  let r := (S.card:ℝ)* |q|
  let B := 21*(S.card:ℝ)*η
  have hb : 0≤B := by dsimp [B]; positivity
  have hstrong : 6*B≤r := by
    dsimp only [B,r]
    nlinarith only [mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg S.card : (0:ℝ)≤S.card)]
  obtain ⟨hwidth,hword⟩ := isolated_field_delay u S q η hη hs
  change w+2*(S.card:ℝ)* |q| ≤ W+2*B at hwidth
  have hres : w+4*B ≤ W-r := by dsimp only [r] at *; linarith only [hwidth,hstrong]
  have hlag := (mul_le_mul_of_nonneg_left hres ht).trans hbefore
  have hwpos : 0≤t*w := mul_nonneg ht (circuitHamiltonianSpectralWidth_nonneg J)
  have hw : t*w/4≤θ := by nlinarith only [hlag,mul_nonneg ht hb]
  have hsemi : t*w≤π := by linarith only [hw,hθ]
  obtain ⟨z,hz,C,hc,he⟩ := hword t ht hsemi
  refine ⟨z,hz,C,hc,he.trans ?_⟩
  change 2*sin (t*w/4)+t*B≤2*sin θ
  have hchord := sine_chord_floor (div_nonneg hwpos (by norm_num)) hw hθ
  nlinarith only [hchord,hlag]

#print axioms isolated_window
end
end GaloisForLFunctions.HTGeometry.FirstAscent
