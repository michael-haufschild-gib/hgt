import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.SquareClosure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OmittedModes.RankReadings
import GaloisForLFunctions.RHTower.ArithmeticDilationStageDeterminant

/-! # A strict gap identifies the index of each eigenvalue of a line omission -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set ContinuousLinearMap InnerProductSpace

/-- Every nonzero missing line can be approached in square-operator norm by conserving line omissions. -/
theorem line_square_mem_physical_closure {v : Gas} (hv : v ≠ 0) :
    projected (omitLine v)^2 ∈ closure (physicalSquares 1) := by
  obtain ⟨u,hu⟩ := exists_missingWave_tendsto v
  have ht := ((continuousAt_omitted_root hv).tendsto.comp hu).pow 2
  apply mem_closure_of_tendsto ht
  refine Eventually.of_forall fun n => ?_
  have hc := (nonzero_line_conserves_iff (u n).val).mpr (u n).property
  exact ⟨omitLine (u n).val,(missingDimension_one_iff _).mpr ⟨_,hc.1,rfl⟩,hc.2,rfl⟩

private theorem line_square_compact (v : Gas) : IsCompactOperator (projected (omitLine v)^2 : GasOp) := by
  rw [line_square]
  exact (squareHeat.property.2.sub ((HTGeometry.isHilbertSchmidt_rankOne _ _).smul _)).isCompactOperator

/-- For a nonzero eigenvalue in the kth open gap, no other interlacing interval can supply its approximation number. -/
theorem line_gap_index (v : Gas) {b : SpectralBand 1}
    (hb : ∀ i, (b i).val = _root_.RHTower.approxNumber (projected (omitLine v)^2) i)
    {k : ℕ} {x : ℝ} (hx : occupationWeight (k+1) < x ∧ x < occupationWeight k)
    {y : Gas} (hy : y ≠ 0) (he : (projected (omitLine v)^2) y = (x:ℂ) • y) : (b k).val = x := by
  have hp := (occupationWeight_pos _).trans hx.1
  have hc := line_square_compact v
  have hs := ((projected_positive (omitLine v)).isSelfAdjoint.pow 2).isSymmetric
  obtain ⟨n,hn⟩ := exists_sgVal_eq_of_eigenvalue hc hs hy he (Complex.ofReal_ne_zero.mpr hp.ne')
  have hv : (b n).val = x := by
    rw [hb,_root_.RHTower.approxNumber_eq_singVal hc,← _root_.RHTower.abs_sgVal_eq_singVal hc hs,
      Complex.ofReal_inj.mp hn,abs_of_pos hp]
  have hnk : n = k := by
    rcases lt_trichotomy n k with h | h | h
    · have hle := (occupationWeight_antitone (Nat.succ_le_of_lt h)).trans (b n).property.1
      exact False.elim (hx.2.not_ge (hle.trans_eq hv))
    · exact h
    · have hle := (b n).property.2.trans (occupationWeight_antitone (Nat.succ_le_of_lt h))
      exact False.elim (hx.1.not_ge (hv.symm.trans_le hle))
  subst n
  exact hv

#print axioms line_square_mem_physical_closure
#print axioms line_gap_index

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
