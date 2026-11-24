import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.FiniteRecords.Transfer
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.ArcMargins

/-! # Exact scalar mass bounds on finite windows -/
open Set Filter MeasureTheory Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
noncomputable section

/-- At an empty-circuit target the limiting fractions are known exactly.
The fine scalar clock shifts the two angular radii by at most δ. -/
theorem scalar_mass_bracket {N : ℕ} (H : selfAdjoint (Register N))
    (hmax : MaximallyProjectiveEnergy H.2.isHermitian.eigenvalues) {δ G x : ℝ}
    (hδ : 0 ≤ δ) (hx : δ ≤ x) (hx' : x+δ ≤ 1/2) (hG : 0 < G)
    (hclock : ∀ u : ℝ, ∃ τ ∈ Icc u (u+G), τ ∈ visitSet H 0 δ) (a T : ℝ) (hT : G < T) :
    let V := volume.real (visitSet H 0 (zeroGateArcTolerance x) ∩ Icc a (a+T))
    zeroGateArcDensity (2^N) (x-δ)*(T-G) ≤ V ∧ V ≤ zeroGateArcDensity (2^N) (x+δ)*(T+G) := by
  intro V
  let p := zeroGateArcDensity (2^N) (x-δ)
  let q := zeroGateArcDensity (2^N) (x+δ)
  have hxl : x-δ ∈ Icc (0:ℝ) (1/2) := ⟨sub_nonneg.mpr hx,by linarith only [hx',hδ]⟩
  have hxu : x+δ ∈ Icc (0:ℝ) (1/2) := ⟨add_nonneg (hδ.trans hx) hδ,hx'⟩
  have he := FluxOccupation.chord_margin hxl.1 (sub_le_self x hδ) (by linarith only [hx',hδ])
  rw [show x-(x-δ)=δ by ring] at he
  have hf := FluxOccupation.chord_margin (hδ.trans hx) (le_add_of_nonneg_right hδ) hx'
  rw [add_sub_cancel_left] at hf
  have hlo := zero_visitFraction_tendsto H hmax ⟨x-δ,hxl⟩ 0
  have hhi := zero_visitFraction_tendsto H hmax ⟨x+δ,hxu⟩ 0
  have h (p' q' : ℝ) (hp : p'<p) (hq : q<q') : p'*(T-G) ≤ V ∧ V ≤ q'*(T+G) :=
    circuit_window_transfer H 0 he hf hG hclock
      ((hlo.eventually_const_lt hp).mono fun _ hh => hh.le)
      ((hhi.eventually_lt_const hq).mono fun _ hh => hh.le) a T hT
  constructor
  · by_contra! hn
    obtain ⟨r,hr,hrp⟩ := exists_between ((div_lt_iff₀ (sub_pos.mpr hT)).mpr hn)
    exact ((div_lt_iff₀ (sub_pos.mpr hT)).mp hr).not_ge (h r (q+1) hrp (lt_add_one q)).1
  · by_contra! hn
    have hsum := add_pos (hG.trans hT) hG
    obtain ⟨r,hqr,hr⟩ := exists_between ((lt_div_iff₀ hsum).mpr hn)
    exact ((lt_div_iff₀ hsum).mp hr).not_ge (h (p-1) r (sub_lt_self _ one_pos) hqr).2

#print axioms scalar_mass_bracket
end
end GaloisForLFunctions.HTGeometry.SharpOccupation.FiniteRecords
