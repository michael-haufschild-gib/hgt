import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.IndependentOmissions
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FiniteCeiling

/-! # Exact fourth-trace range at each finite omitted dimension

Assign each lane a fraction of its lowest-shell loss. Their independent
omissions realize the same fraction of the entire interlacing ceiling.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

theorem traceCeiling_pos {r : ℕ} (hr : 0 < r) : 0 < traceCeiling r :=
  Finset.sum_pos' (fun k _ => sq_nonneg (occupationWeight k)) ⟨0,Finset.mem_range.mpr hr,sq_pos_of_pos (occupationWeight_pos 0)⟩

/-- At every positive finite missing dimension exactly the open interval below the ceiling occurs. -/
theorem lossesAtRank_succ (r : ℕ) : lossesAtRank (r+1) = Set.Ioo 0 (traceCeiling (r+1)) := by
  apply Set.Subset.antisymm (lossesAtRank_subset _ (Nat.succ_pos r))
  intro y hy
  let t := y/traceCeiling (r+1)
  have hc := traceCeiling_pos (Nat.succ_pos r)
  have ht : 0 < t := div_pos hy.1 hc
  have ht₁ : t < 1 := (div_lt_one hc).mpr hy.2
  have hex (j : Fin (r+1)) : ∃ v : MissingWave,
      lineLoss (extendModes (progression j) v.val) = t*occupationWeight j.val^2 := by
    have hp := sq_pos_of_pos (occupationWeight_pos j.val)
    exact progression_realizes j ⟨mul_pos ht hp,mul_lt_of_lt_one_left hp ht₁⟩
  choose v hv using hex
  have h := sum_lane_losses_mem v
  change (∑ j, lineLoss (extendModes (progression j) (v j).val)) ∈ lossesAtRank (r+1) at h
  have hsum : (∑ j : Fin (r+1), occupationWeight j.val^2) = traceCeiling (r+1) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => occupationWeight k^2) (r+1)
  simp only [hv,← Finset.mul_sum,hsum] at h
  change y/traceCeiling (r+1)*traceCeiling (r+1) ∈ lossesAtRank (r+1) at h
  rwa [div_mul_cancel₀ _ hc.ne'] at h

/-- Differences between consecutive supremal losses determine each occupation weight squared. -/
theorem traceSup_difference (r : ℕ) :
    sSup (lossesAtRank (r+1))-sSup (lossesAtRank r) = (((r:ℝ)+1)⁻¹)^2 := by
  have hs (k : ℕ) : sSup (lossesAtRank k) = traceCeiling k := by
    cases k with
    | zero => simp [lossesAtRank_zero,traceCeiling]
    | succ k =>
      rw [lossesAtRank_succ,csSup_Ioo (traceCeiling_pos (Nat.succ_pos k))]
  rw [hs,hs,traceCeiling_succ]

#print axioms lossesAtRank_succ
#print axioms traceSup_difference

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
