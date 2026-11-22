import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ChordSlope

/-! # A deadline for short circuits on the first ascent -/
open Real MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- At error 1/10 the entire part of the initial semicircle above the
displayed deadline excludes every s-gate circuit. Its denominator differs
from the energy width by an order statistic of the local Gaussian couplings. -/
theorem gaussian_short_circuit_deadline :
    ∃ a b B : ℝ, 0<a ∧ 0<b ∧ 0<B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let p := pathPauliDisorderShell ω n
      let H : selfAdjoint (Reg N) := ⟨pathHamiltonian p,isSelfAdjoint_pathHamiltonian p⟩
      let W := circuitHamiltonianSpectralWidth H
      a*N ≤ W ∧ W ≤ b*N ∧
        ∀ s : ℕ, 0<s → 42*s ≤ Fintype.card (PathLabel n) →
          let r : ℝ := 42*s
          let d := 16*r*sqrt (log (B*N/r))
          ∀ t ∈ Icc (0:ℝ) (π/W), HasProjectiveCircuitApproximation N (1/10) s (unitaryEvolution H.val t) →
            t*(W-d) ≤ 4*arcsin (1/20) := by
  obtain ⟨B,hB,hfloor⟩ := gaussian_initial_floor
  obtain ⟨a,b,ha,hb,hclock⟩ := gaussian_initial_clock
  refine ⟨a,b,B,ha,hb,hB,?_⟩
  filter_upwards [hfloor,hclock] with ω hf hc
  filter_upwards [hf,hc] with n hf hc
  intro N p H W
  refine ⟨hc.1,hc.2.1,?_⟩
  intro s hs hcap r d t ht hvisit
  have hW : 0<W := (show 0<a*(N:ℝ) by dsimp [N]; positivity).trans_le hc.1
  have hw : t*W ≤ π := (le_div_iff₀ hW).mp ht.2
  have hh := hf s hs hcap t ht.1 hw
  have hd : orbitCircuitDistance H s t ≤ 1/10 := (hasProjectiveCircuitApproximation_iff_infDist _ s _).mp hvisit
  let x := arcsin (1/20)
  let y := t*W/4
  have hx : 0≤x := arcsin_nonneg.mpr (by norm_num)
  have hy : y≤π/4 := div_le_div_of_nonneg_right hw (by norm_num)
  have hsx : sin x=1/20 := sin_arcsin (by norm_num) (by norm_num)
  have hnonneg : 0≤t*d := mul_nonneg ht.1 (by dsimp [d,r]; positivity)
  rcases le_total y x with h | h
  · dsimp only [y,x] at h
    nlinarith only [h,hnonneg]
  · have hl := sine_chord_floor hx h hy
    rw [hsx] at hl
    change 2*sin y ≤ orbitCircuitDistance H s t+4*t*r*sqrt (log (B*N/r)) at hh
    change t*(W-(16*r*sqrt (log (B*N/r)))) ≤ 4*x
    dsimp only [y] at hl
    change 2*sin (t*W/4) ≤ _ at hh
    nlinarith only [hl,hh,hd]

#print axioms gaussian_short_circuit_deadline
end
end GaloisForLFunctions.HTGeometry.FirstAscent
