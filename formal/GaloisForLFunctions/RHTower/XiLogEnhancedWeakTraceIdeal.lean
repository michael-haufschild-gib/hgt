import GaloisForLFunctions.RHTower.XiOrderedPrimeSchattenThreshold
import GaloisForLFunctions.RHTower.WeakSchattenResidue

/-!
# Logarithmically enhanced weak trace ideal

The Xi singular-value law lies above ordinary weak `S₁`, but its extra logarithm is exact.  This
module defines the resulting compact-operator class and proves that the ordered reciprocal-Xi
operator lies on its nonzero boundary with residue `1 / π`.
-/

open Filter

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The endpoint profile `(n+1) a_n(T) / log(n+1)`.  Its value at `n = 0` is harmless. -/
def logEnhancedWeakTraceProfile (T : H →L[ℂ] H) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) * approxNumber T n) / Real.log ((n : ℝ) + 1)

/-- Compact operators with uniformly bounded logarithmically enhanced weak-trace profile. -/
def MemLogEnhancedWeakTraceClass (T : H →L[ℂ] H) : Prop :=
  IsCompactOperator T ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ n : ℕ, logEnhancedWeakTraceProfile T n ≤ C

/-- Honest boundary value of the logarithmically enhanced weak-trace profile. -/
def HasLogEnhancedWeakTraceResidue (T : H →L[ℂ] H) (R : ℝ) : Prop :=
  Tendsto (logEnhancedWeakTraceProfile T) atTop (nhds R)

/-- The reciprocal-Xi operator has the exact endpoint residue `1 / π`. -/
theorem hasLogEnhancedWeakTraceResidue_xiOrderedSignedPrimeOperator :
    HasLogEnhancedWeakTraceResidue xiOrderedSignedPrimeOperator Real.pi⁻¹ := by
  change Tendsto (logEnhancedWeakTraceProfile xiOrderedSignedPrimeOperator)
    atTop (nhds Real.pi⁻¹)
  have hscaled :=
    tendsto_xiOrderedSignedPrimeOperator_approxNumber_div_model.div_const Real.pi
  have hfinal : Tendsto
      (logEnhancedWeakTraceProfile xiOrderedSignedPrimeOperator)
      atTop (nhds (1 / Real.pi)) := by
    apply hscaled.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hlog : Real.log ((n : ℝ) + 1) ≠ 0 := by
      apply (Real.log_pos ?_).ne'
      exact_mod_cast Nat.succ_lt_succ hn
    rw [logEnhancedWeakTraceProfile]
    field_simp [hlog, Real.pi_ne_zero]
  simpa [one_div] using hfinal

/-- The reciprocal-Xi operator belongs to the logarithmically enhanced weak trace class. -/
theorem memLogEnhancedWeakTraceClass_xiOrderedSignedPrimeOperator :
    MemLogEnhancedWeakTraceClass xiOrderedSignedPrimeOperator := by
  refine ⟨xiOrderedSignedPrimeOperator_memSchattenClass_two.isCompactOperator
    (by norm_num), ?_⟩
  obtain ⟨C, hC⟩ :=
    hasLogEnhancedWeakTraceResidue_xiOrderedSignedPrimeOperator.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  exact (hC (Set.mem_range_self n)).trans (le_max_left _ _)

/-- The ordinary weak-`S₁` numerator diverges logarithmically. -/
theorem tendsto_succ_mul_xiOrderedSignedPrimeOperator_approxNumber_atTop :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      approxNumber xiOrderedSignedPrimeOperator n) atTop atTop := by
  have hres := hasLogEnhancedWeakTraceResidue_xiOrderedSignedPrimeOperator
  change Tendsto (logEnhancedWeakTraceProfile xiOrderedSignedPrimeOperator)
    atTop (nhds Real.pi⁻¹) at hres
  have hlog : Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hproduct := Filter.Tendsto.pos_mul_atTop (by positivity) hres hlog
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hlog0 : Real.log ((n : ℝ) + 1) ≠ 0 := by
    apply (Real.log_pos ?_).ne'
    exact_mod_cast Nat.succ_lt_succ hn
  rw [logEnhancedWeakTraceProfile]
  field_simp [hlog0]

/-- The reciprocal-Xi operator is not in ordinary weak trace class. -/
theorem xiOrderedSignedPrimeOperator_not_memWeakSchattenClass_one :
    ¬ MemWeakSchattenClass 1 xiOrderedSignedPrimeOperator := by
  rintro ⟨C, _hC, hbound⟩
  have hev :=
    tendsto_succ_mul_xiOrderedSignedPrimeOperator_approxNumber_atTop.eventually
      (eventually_gt_atTop C)
  obtain ⟨n, hn⟩ := hev.exists
  have hle := hbound n
  rw [Real.rpow_one, le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at hle
  exact (not_lt_of_ge hle) (by simpa [mul_comm] using hn)

end

end RHTower
