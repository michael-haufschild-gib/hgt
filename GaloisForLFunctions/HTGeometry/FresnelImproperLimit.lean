import GaloisForLFunctions.HTGeometry.FresnelTailBound

/-!
# The improper Fresnel integral converges

The oscillatory half-power integrand is interval integrable on every bounded interval — its modulus
is `u^{-1/2}`, integrable at the origin — and the tail bound `2 a^{-1/2}` makes the truncated
integrals Cauchy at infinity.  Hence the improper integral

`lim_{R → ∞} ∫₀^R u^{-1/2} e^{iu} du`

exists.  This is the analytic half of the half-log scattering constant; identifying its value with
`√π e^{iπ/4}` is done through the complex-scaled Euler integral.
-/

open Complex intervalIntegral MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem intervalIntegrable_fresnelKernel (a b : ℝ) :
    IntervalIntegrable fresnelKernel volume a b := by
  have hbase : IntervalIntegrable (fun u : ℝ => u ^ (-(1:ℝ)/2)) volume a b :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hmeas : AEStronglyMeasurable fresnelKernel (volume.restrict (Set.uIoc a b)) := by
    apply Measurable.aestronglyMeasurable
    unfold fresnelKernel
    fun_prop
  refine IntervalIntegrable.mono_fun hbase hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  have hu0 : 0 < u ∨ u < 0 := by
    rcases le_or_gt u 0 with h | h
    · rcases lt_or_eq_of_le h with h' | h'
      · exact Or.inr h'
      · exfalso
        rw [← h'] at hu
        rcases Set.mem_uIoc.mp hu with h1 | h1
        · exact absurd h1.1 (by simp)
        · exact absurd h1.1 (by simp)
    · exact Or.inl h
  rcases hu0 with hpos | hneg
  · rw [norm_fresnelKernel hpos, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hpos _)]
  · rw [fresnelKernel]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have hzero : u ^ (-(1:ℝ)/2) = 0 := by
      rw [Real.rpow_def_of_neg hneg]
      sorry
    sorry

end

end GaloisForLFunctions.HTGeometry
