import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.FiniteRange

/-! # Full trace-loss interval when the finite omitted dimension is unobserved -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap

/-- The squared occupation weights sum to the full fourth Gibbs trace. -/
theorem occupation_trace_sum : HasSum (fun k => occupationWeight k ^ 2) (riemannZeta 2).re := by
  have h := (_root_.RHTower.memSchattenClass_two_iff_isHilbertSchmidt squareHeat.val).mpr squareHeat.property.2
  change Summable (fun k => _root_.RHTower.approxNumber squareHeat.val k ^ (2:ℝ)) at h
  simp only [squareHeat_approxNumber,Real.rpow_two] at h
  have hs := _root_.RHTower.hsNormSq_eq_tsum_approxNumber_sq squareHeat.property.2
  simp only [squareHeat_approxNumber] at hs
  have hm := _root_.HTGeometry.opTrace_sq_eq_ofReal_hsNormSq squareHeat.property.2 squareHeat.property.1.star_eq
  change opTrace ((criticalOperator^2)^2) = _ at hm
  rw [critical_fourth_trace] at hm
  have he : (riemannZeta 2).re = hsNormSq squareHeat.val := congrArg Complex.re hm
  rw [he,hs]
  exact h.hasSum

theorem traceCeiling_lt_total (r : ℕ) : traceCeiling r < (riemannZeta 2).re := by
  have h := occupation_trace_sum.summable.sum_le_tsum (Finset.range (r+1)) (fun i _ => sq_nonneg _)
  rw [occupation_trace_sum.tsum_eq] at h
  change traceCeiling (r+1) ≤ _ at h
  have hd := traceCeiling_succ r
  have hp : 0 < (((r:ℝ)+1)⁻¹)^2 := by positivity
  linarith only [h,hd,hp]

/-- Finite-dimensional omissions alone attain every strictly submaximal loss. -/
theorem finite_loss_union : (⋃ r, lossesAtRank r) = Set.Ico 0 (riemannZeta 2).re := by
  ext y
  constructor
  · intro hy
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp hy
    cases r with
    | zero =>
      rw [lossesAtRank_zero,Set.mem_singleton_iff] at hr
      subst y
      exact ⟨le_rfl,by simpa [traceCeiling] using traceCeiling_lt_total 0⟩
    | succ k =>
      rw [lossesAtRank_succ] at hr
      exact ⟨hr.1.le,hr.2.trans (traceCeiling_lt_total _)⟩
  · rintro ⟨hy,ht⟩
    rcases hy.eq_or_lt with rfl | hy
    · exact Set.mem_iUnion.mpr ⟨0,lossesAtRank_zero.symm ▸ Set.mem_singleton _⟩
    have hl : Tendsto traceCeiling atTop (𝓝 (riemannZeta 2).re) := occupation_trace_sum.tendsto_sum_nat
    obtain ⟨r,hr⟩ := (hl.eventually_const_lt ht).exists
    cases r with
    | zero =>
      have h : y < 0 := by simpa [traceCeiling] using hr
      exact (lt_asymm hy h).elim
    | succ k =>
      exact Set.mem_iUnion.mpr ⟨k+1,(lossesAtRank_succ k).symm ▸ ⟨hy,hr⟩⟩

#print axioms occupation_trace_sum
#print axioms finite_loss_union

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
