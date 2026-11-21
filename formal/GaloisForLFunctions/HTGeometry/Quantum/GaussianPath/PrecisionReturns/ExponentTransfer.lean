import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.FirstVisit
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ChangeOfRadius

/-! # The low-gate first-return exponent from full-support spectral fidelity -/
open Filter Topology Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

/-- If the low-gate return tube lies within a constant multiple of the empty
tube, its first return has the same logarithmic exponent. Full-support
fidelity at a constant times ε² bounds the first time on both sides. -/
theorem exponent_of_scalar_control {n d : ℕ} (H : selfAdjoint (Register n))
    (e : (Fin n → Bool) ≃ Fin (d+3)) (s : ℕ)
    {A : ℝ} (hA : 0 < A)
    (hcontrol : ∀ t ε, HasProjectiveCircuitApproximation n ε s (unitaryEvolution H.val t) →
      HasProjectiveCircuitApproximation n (A*ε) 0 (unitaryEvolution H.val t))
    (hg : 0 < (H.2.isHermitian.eigenvalues ∘ e.symm) 1 - (H.2.isHermitian.eigenvalues ∘ e.symm) 0)
    (hgap : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap (H.2.isHermitian.eigenvalues ∘ e.symm)
      0 1 (fun i => i.succ.succ))) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε => log (firstVisit H a s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((d+1:ℕ):ℝ)) := by
  let E := H.2.isHermitian.eigenvalues ∘ e.symm
  let c : ℝ := ((d:ℝ)+3)⁻¹
  let p := fun _ : Fin (d+3) => c
  have hc : 0 < c := by dsimp [c]; positivity
  have h1 : ∑ j, p j = 1 := by simp [p,c]; field_simp
  let F := fidelityReturnTime E p a
  have hlim := tendsto_log_fidelityReturnTime E p h1 (fun _ => hc) hc (fun _ => le_rfl) hg hgap ha
  let B := 8*π^2*A^2+1
  let b := (c/π)^2
  have hB : 0 < B := by dsimp [B]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hscale (K : ℝ) (hK : 0 < K) : Tendsto (fun ε => log (F (K*ε^2))/log (1/ε))
      (𝓝[>] (0:ℝ)) (𝓝 ((d+1:ℕ):ℝ)) := by
    have h := log_clock_quadratic hK hlim
    rw [show 2*(((d+1:ℕ):ℝ)/2) = ((d+1:ℕ):ℝ) by ring] at h
    exact h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (hscale B hB) (hscale b hb)
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    let v := firstVisit H a s ε
    have hv := (firstVisit_isLeast H a s hε.1).1
    have hD := deficit_of_empty_return H e 0 p h1 (fun _ => hc.le) (mul_pos hA hε.1)
      (hcontrol v ε hv.2)
    have hmem : v ∈ fidelityReturnSet E p a (B*ε^2) := ⟨hv.1,hD.trans_lt (by
      dsimp only [B]; nlinarith only [sq_pos_of_pos hε.1])⟩
    have hF := csInf_le (bddBelow_fidelityReturnSet E p a _) hmem
    have hpos := ha.trans_le (le_fidelityReturnTime ⟨v,hmem⟩)
    exact div_le_div_of_nonneg_right (log_le_log hpos hF)
      (log_pos ((one_lt_div hε.1).mpr hε.2)).le
  · have hne := eventually_fidelityReturnTime_le E p h1 (fun _ => hc.le) hg hgap a
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ),(quadratic_radius hb).eventually hne] with ε hε hne'
    have hv := firstVisit_isLeast H a s hε.1
    have hbound : firstVisit H a s ε ≤ F (b*ε^2) := by
      apply le_csInf hne'.1
      intro t ht
      obtain ⟨z,hz,C,hC,herr⟩ := empty_return_of_deficit H e 0 p h1 hc (fun _ => le_rfl) ht.2
      have he : π*sqrt (b*ε^2)/c=ε := by
        rw [sqrt_mul hb.le,Real.sqrt_sq hε.1.le,show sqrt b=c/π from Real.sqrt_sq (by positivity)]
        field_simp
      exact hv.2 ⟨ht.1,z,hz,C,by omega,he ▸ herr⟩
    exact div_le_div_of_nonneg_right (log_le_log (ha.trans_le hv.1.1) hbound)
      (log_pos ((one_lt_div hε.1).mpr hε.2)).le

#print axioms exponent_of_scalar_control
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
