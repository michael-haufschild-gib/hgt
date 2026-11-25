import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.FirstIndex
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.FirstGate.FirstVisit

/-! # The first fine return on multiples of a rational-width scalar entry -/

open Set Filter MeasureTheory Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ResonantReturns
open FirstGate EmptyVisitFlux PrecisionReturns SharpOccupation
noncomputable section

private theorem arc_inverse {r : ℝ} (hr : r∈Ioo (0:ℝ) (1/2)) :
    zeroGateArcTolerance r ∈ Ioo (0:ℝ) (sqrt 2) ∧ physicalArc (zeroGateArcTolerance r)=r := by
  have h0 : zeroGateArcTolerance 0=0 := by simp [zeroGateArcTolerance]
  have h1 : zeroGateArcTolerance (1/2)=sqrt 2 := by
    unfold zeroGateArcTolerance
    rw [show π*(1/2)/2=π/4 by ring,sin_pi_div_four]
    ring
  have hm := strictMonoOn_zeroGateArcTolerance
  have he : zeroGateArcTolerance r ∈ Ioo (0:ℝ) (sqrt 2) :=
    ⟨h0 ▸ hm (by norm_num) ⟨hr.1.le,hr.2.le⟩ hr.1,h1 ▸ hm ⟨hr.1.le,hr.2.le⟩ (by norm_num) hr.2⟩
  have hs := physicalArc_spec he.1 he.2
  exact ⟨he,hm.injOn ⟨hs.1.1.le,hs.1.2.le⟩ ⟨hr.1.le,hr.2.le⟩ hs.2⟩

/-- For every rational coarse arc width and every positive origin outside
the scalar target, sample at positive multiples of its first scalar entry.
The first tick admitting any fine circuit below the connected budget has
precision exponent D−2. The origin and width may be chosen after the draw. -/
theorem gaussian_rational_entry_first_index :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (PrecisionReturns.Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      ∀ r : ℚ, (r:ℝ)∈Ioo (0:ℝ) (1/2) → let e := zeroGateArcTolerance r
        ∀ a > (0:ℝ), e<orbitCircuitDistance H 0 a → let v := firstVisit H a 0 e
          ∀ s : ℕ, s+1<N → Tendsto (fun ε => log (firstIndex H v s ε)/log (1/ε))
            (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_rational_pair_first_index] with ω hω k
  intro N H r hr e a ha hout v
  obtain ⟨he,hinv⟩ := arc_inverse hr
  obtain ⟨hav,hface⟩ := first_empty_entry_of_outside H he.1 he.2 hout
  rw [hinv] at hface
  let E := H.2.isHermitian.eigenvalues
  let w := fun i => -E i/(2*π)
  obtain ⟨i,j,hij⟩ := (entry_iff_closed_face w hr.1.le hr.2).mp hface
  have hne : j≠i := fun hh => hij.1.ne (congrArg w hh)
  obtain ⟨z,hz⟩ := lift_gap (fun t => -E t) v i j hij.2.1
  rw [neg_sub_neg] at hz
  have hd : (r.den:ℝ)≠0 := by exact_mod_cast r.den_ne_zero
  have hden : (r.den:ℝ)*(r:ℝ)=r.num := by rw [Rat.cast_def,mul_comm,div_mul_cancel₀ _ hd]
  apply hω k v (ha.trans hav) j i hne r.den r.den_pos ((r.den:ℤ)*z+r.num)
  change (r.den:ℝ)*v*(E i-E j)/(2*π)=_
  rw [show (r.den:ℝ)*v*(E i-E j)/(2*π)=(r.den:ℝ)*(v*(E i-E j)/(2*π)) by ring,hz,
    mul_add,hden]
  push_cast
  rfl

#print axioms gaussian_rational_entry_first_index
end
end GaloisForLFunctions.HTGeometry.ResonantReturns
