import GaloisForLFunctions.RHTower.PaperPrimeRotationCoherentOperator
import GaloisForLFunctions.HTGeometry.FinitePhasePacketPositivity

/-! # A strictly positive coherent Gram limit for every nonzero prime packet -/

namespace RHTower
open GaloisForLFunctions.HTGeometry HilbertSchmidt _root_.ContinuousLinearMap Filter Topology
noncomputable section

theorem paperPrimeCoherentFrequency_injective :
    Function.Injective (fun p : Nat.Primes => -Real.log p) := by
  intro p r h
  have hl : Real.log (p : ℝ) = Real.log (r : ℝ) := neg_injective h
  have he := Real.log_injOn_pos
    (by change (0 : ℝ) < (p : ℝ); exact_mod_cast p.2.pos)
    (by change (0 : ℝ) < (r : ℝ); exact_mod_cast r.2.pos) hl
  apply Subtype.ext
  exact_mod_cast he

theorem paperPrimeCoherentLimitCoefficient_eq_zero (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    paperPrimeCoherentLimitCoefficient a p = 0 ↔ a p = 0 := by
  simp only [paperPrimeCoherentLimitCoefficient, mul_eq_zero, Complex.I_ne_zero,
    Complex.ofReal_eq_zero, neg_eq_zero, p.2.log_ne_zero, or_false]

theorem paperPrimeCoherentEnergy_eq_zero_iff (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    paperPrimeCoherentEnergy s a = 0 ↔ ∀ p ∈ s, a p = 0 := by
  rw [paperPrimeCoherentEnergy, finitePhaseEnergy_eq_zero_iff s _ _
    paperPrimeCoherentFrequency_injective.injOn]
  simp only [paperPrimeCoherentLimitCoefficient_eq_zero]

theorem paperPrimeCoherentEnergy_pos_iff (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    0 < paperPrimeCoherentEnergy s a ↔ ∃ p ∈ s, a p ≠ 0 := by
  rw [paperPrimeCoherentEnergy, finitePhaseEnergy_pos_iff s _ _
    paperPrimeCoherentFrequency_injective.injOn]
  simp only [ne_eq, paperPrimeCoherentLimitCoefficient_eq_zero]

theorem paperPrimeCoherentGramLimit_gt_one_iff (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    1 < Real.exp (paperPrimeCoherentEnergy s a) ↔ ∃ p ∈ s, a p ≠ 0 := by
  rw [Real.one_lt_exp_iff, paperPrimeCoherentEnergy_pos_iff]

theorem paperPrimeCoherentOperator_norm_le (s : Finset Nat.Primes)
    (a : Nat.Primes → ℂ) (q : ℕ) :
    ‖paperPrimeCoherentOperator s a q‖ ≤
      paperPrimeCoherentBound s a / Real.sqrt ((q : ℝ) + 1) := by
  have hq : 0 < (q : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((q : ℝ) + 1) := Real.sqrt_pos.mpr hq
  rw [paperPrimeCoherentOperator, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ Real.sqrt ((q : ℝ) + 1) *
        ∑ p ∈ s, ‖a p‖ * (Real.log p / ((q : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (paperPrimeRotationCompression_norm_le p (q + 1) (q + 1)).trans
        (by simpa [paperPrimeRotationNormSlope] using
          paperPrimeRotationCommutator_norm_le_rate p q 0 1 1 0)
    _ = paperPrimeCoherentBound s a / Real.sqrt ((q : ℝ) + 1) := by
      have he : (∑ p ∈ s, ‖a p‖ * (Real.log p / ((q : ℝ) + 1))) =
          paperPrimeCoherentBound s a / ((q : ℝ) + 1) := by
        rw [paperPrimeCoherentBound, Finset.sum_div]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [he, ← mul_div_assoc, div_eq_div_iff hq.ne' hs.ne']
      calc
        _ = paperPrimeCoherentBound s a * Real.sqrt ((q : ℝ) + 1) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hq.le]

theorem paperPrimeCoherentOperator_tendsto_zero (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Tendsto (paperPrimeCoherentOperator s a) atTop (𝓝 0) := by
  have hn : Tendsto (fun q : ℕ => (q : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (paperPrimeCoherentOperator_norm_le s a)
    (tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hn))

/-- The native sequence vanishes in norm, has zero ideal cost and trivial ordinary
determinants, but its coherent Gram limit is greater than one exactly for nonzero input. -/
theorem paperPrimeCoherentCompletion (s : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Tendsto (paperPrimeCoherentOperator s a) atTop (𝓝 0) ∧
    (∀ q, compactOperatorTraceCost PaperRotationHilbert (paperPrimeCoherentOperator s a q) = 0) ∧
    (∀ (q : ℕ) (z : ℂ), fredholmDetOp (lpBasis ℤ) (z • paperPrimeCoherentOperator s a q) = 1) ∧
    Tendsto (fun q => fredholmDetOp (lpBasis ℤ)
      ((paperPrimeCoherentOperator s a q).adjoint ∘L paperPrimeCoherentOperator s a q))
      atTop (𝓝 (Real.exp (paperPrimeCoherentEnergy s a) : ℂ)) ∧
    (1 < Real.exp (paperPrimeCoherentEnergy s a) ↔ ∃ p ∈ s, a p ≠ 0) :=
  ⟨paperPrimeCoherentOperator_tendsto_zero s a,
    paperPrimeCoherentOperator_traceCost_zero s a,
    paperPrimeCoherentOperator_smul_fredholmDet s a,
    paperPrimeCoherentOperator_gram_tendsto s a,
    paperPrimeCoherentGramLimit_gt_one_iff s a⟩

end
end RHTower
