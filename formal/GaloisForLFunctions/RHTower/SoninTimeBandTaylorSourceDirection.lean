import GaloisForLFunctions.RHTower.SoninPrimeSquareCoherentMonomials

noncomputable section
open MeasureTheory
namespace RHTower

/-- The literal zero-extended Taylor output is its coefficient times the
actual physical cutoff monomial. -/
theorem fullFourierTaylorOutput_eq_cutoffMonomial
    (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    let hab : -a ≤ a := neg_le_self ha
    let uBCF := projectClosedIntervalBCFCLM (-a) a hab ℂ
      (fourierTaylorOutputContinuous (-a) a n)
    let uOut := BoundedContinuousFunction.toLp 2
      ((volume : Measure ℝ).restrict (Set.Icc (-a) a)) ℂ uBCF
    lpExtendByZeroCLM (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc (-a) a) measurableSet_Icc uOut =
        ((n.factorial : ℂ)⁻¹ * (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I)^n) •
          soninCutoffMonomial a n := by
  let hab : -a ≤ a := neg_le_self ha
  let uBCF := projectClosedIntervalBCFCLM (-a) a hab ℂ
    (fourierTaylorOutputContinuous (-a) a n)
  let uOut := BoundedContinuousFunction.toLp 2
    ((volume : Measure ℝ).restrict (Set.Icc (-a) a)) ℂ uBCF
  let c : ℂ := (n.factorial : ℂ)⁻¹ * (((-(2 * Real.pi) : ℝ) : ℂ) * Complex.I)^n
  apply Lp.ext
  have hinner : ∀ᵐ x ∂volume, x ∈ Set.Icc (-a) a → uOut x = uBCF x :=
    (ae_restrict_iff' measurableSet_Icc).mp
      (BoundedContinuousFunction.coeFn_toLp 2
        ((volume : Measure ℝ).restrict (Set.Icc (-a) a)) ℂ uBCF)
  filter_upwards [lpExtendByZeroCLM_coeFn (F := ℂ) (𝕜 := ℂ) (volume : Measure ℝ) 2
      (Set.Icc (-a) a) measurableSet_Icc uOut,
    hinner, Lp.coeFn_smul c (soninCutoffMonomial a n), soninCutoffMonomial_ae a n]
      with x hext hin hsmul hmono
  change _ = c * soninCutoffMonomial a n x at hsmul
  change _ = (c • soninCutoffMonomial a n) x
  rw [hext, hsmul, hmono]
  by_cases hx : x ∈ Set.Icc (-a) a
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (show x ∈ centralInterval a from hx), hin hx]
    change fourierTaylorOutputContinuous (-a) a n (Set.projIcc (-a) a hab x) = _
    rw [Set.projIcc_of_mem hab hx]
    rfl
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (show x ∉ centralInterval a from hx), mul_zero]

/-- Every actual Taylor operator has the original cutoff monomial as its
output direction. This identifies the source expansion needed for coherent
prime dilation; an abstract rank bound alone would not do so. -/
theorem fullTimeBandFourierTaylorTerm_mem_span_cutoffMonomial
    (a c d : ℝ) (ha : 0 ≤ a) (n : ℕ) (f : SoninL2) :
    fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha) n f ∈
      Submodule.span ℂ ({soninCutoffMonomial a n} : Set SoninL2) := by
  rw [fullTimeBandFourierTaylorTerm, fourierPhaseTaylorTerm_eq_tensor,
    fullRectangleKernelOperatorMap_tensor_apply]
  rw [fullFourierTaylorOutput_eq_cutoffMonomial a ha n]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_singleton _)

private theorem norm_comp_le_of_output_direction
    (D T : SoninL2 →L[ℂ] SoninL2) (f : SoninL2) (ε : ℝ) (hε : 0 ≤ ε)
    (hT : ∀ x, T x ∈ Submodule.span ℂ ({f} : Set SoninL2))
    (hD : ‖D f‖ ≤ ε * ‖f‖) :
    ‖D ∘L T‖ ≤ ε * ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hε (norm_nonneg _))
  intro x
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hT x)
  change ‖D (T x)‖ ≤ (ε * ‖T‖) * ‖x‖
  calc
    _ = ‖c‖ * ‖D f‖ := by rw [← hc, map_smul, norm_smul]
    _ ≤ ‖c‖ * (ε * ‖f‖) := mul_le_mul_of_nonneg_left hD (norm_nonneg _)
    _ = ε * ‖T x‖ := by rw [← hc, norm_smul]; ring
    _ ≤ ε * (‖T‖ * ‖x‖) := mul_le_mul_of_nonneg_left (T.le_opNorm x) hε
    _ = _ := by ring

/-- The same finite prime exclusion controls every actual Fourier Taylor
operator relative to its own norm. This carries the unsquared tail estimate
onto the literal rank-one source expansion. -/
theorem soninPrimeSquare_timeBandTaylor_uniform_tail (a c d : ℝ) (ha : 0 ≤ a) :
    ∀ ε > 0, ∃ s : Finset Nat.Primes, ∀ t : Finset Nat.Primes, Disjoint t s →
      ∀ n : ℕ,
        ‖(∑ p ∈ t, soninLogPrimePowerCoefficient (p, 0) •
          dilationSum (soninPrimePowerScale (p, 0)) (one_lt_soninPrimePowerScale (p, 0))) ∘L
            fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha) n‖ ≤
          ε * ‖fullTimeBandFourierTaylorTerm (-a) a c d (neg_le_self ha) n‖ := by
  intro ε hε
  obtain ⟨s, hs⟩ := soninPrimeSquareWeightedDilationSum_monomial_uniform_tail a ε hε
  refine ⟨s, fun t ht n => ?_⟩
  apply norm_comp_le_of_output_direction _ _ (soninCutoffMonomial a n) ε hε.le
    (fullTimeBandFourierTaylorTerm_mem_span_cutoffMonomial a c d ha n)
  simpa only [sum_apply, smul_apply] using hs t ht n

end RHTower

