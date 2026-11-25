import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.IntegerRow
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.ResonantReturns.FirstIndex

/-! # The first affordable index on every resonant period of the frozen chain -/

open Set MeasureTheory Filter Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ResonantReturns
open PrecisionReturns
noncomputable section

/-- If any nonzero integral combination of the anchored phases is an
integer in turns, the first positive affordable index has exponent D−2
at every disconnected budget. The period, anchor and relation can all
be chosen on the realized chain. -/
theorem gaussian_resonant_first_index :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let E := H.2.isHermitian.eigenvalues
      let d := 2^N-2
      ∀ e : (Fin N → Bool) ≃ Fin ((d+1)+1), ∀ τ > (0:ℝ),
        let β := fun i : Fin (d+1) => τ*(E (e.symm i.succ)-E (e.symm 0))/(2*π)
        ∀ m : Fin (d+1) → ℤ, m≠0 → ∀ z : ℤ, ∑ i, (m i:ℝ)*β i=z →
          ∀ s : ℕ, s+1 < N → Tendsto (fun ε => log (firstIndex H τ s ε)/log (1/ε))
            (𝓝[>] (0:ℝ)) (𝓝 (d:ℝ)) := by
  filter_upwards [DisconnectedReturns.gaussian_disconnected_first_wait] with ω hω k
  intro N H E d e τ hτ β m hm z hz s hs
  obtain ⟨L,hL,K,hK,hdeadline⟩ := integer_row_deadline β m hm z hz
  apply exponent_of_scalar_deadline H hτ s (hω k τ hτ s hs) hL (mul_pos (mul_pos two_pos pi_pos) hK)
  intro Q hQ
  obtain ⟨q,hq,hb,hgaps⟩ := hdeadline Q hQ
  refine ⟨q,hq,hb,?_⟩
  rw [mul_div_assoc]
  have htol : 0 < K/(Q:ℝ) := div_pos hK (Nat.cast_pos.mpr hQ)
  apply empty_of_anchored_gaps H (e.symm 0) _ htol.le
  intro a
  obtain ⟨j,rfl⟩ := e.symm.surjective a
  refine Fin.cases ?_ (fun i => ?_) j
  · exact ⟨0,by simpa only [sub_self,mul_zero,zero_div,Int.cast_zero,abs_zero] using htol⟩
  · have he : ((q:ℝ)*τ)*(E (e.symm i.succ)-E (e.symm 0))/(2*π)=(q:ℝ)*β i := by
      dsimp only [β]
      ring
    exact he.symm ▸ hgaps i

#print axioms gaussian_resonant_first_index
end
end GaloisForLFunctions.HTGeometry.ResonantReturns
