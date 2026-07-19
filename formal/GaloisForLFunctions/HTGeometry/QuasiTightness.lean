import GaloisForLFunctions.HTGeometry.QuasiMeasure
import GaloisForLFunctions.HTGeometry.GaussTightness

/-!
# Tightness of the quasi-orthogonal family

The second moment is reproduced from level `1` on, and it controls every tail at once: a node beyond
`R` contributes at least `R²` times its weight to `∑ w·ξ²  = s₂`.  The bound `s₂/R²` is uniform in
the level *and* in the parameter, so an arbitrary sequence of parameters still gives a tight family.

That last point is what makes the construction usable: the parameter that selects a leaf varies with
the level.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The quadrature sum of a monomial is the corresponding moment. -/
theorem quasiSum_pow (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) (k : ℕ) (hk : k ≤ 2 * n) :
    ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ * ξ ^ k = s k := by
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast hk
  have hq := momentFunctional_eq_quasiSum h n t (Polynomial.X ^ k) hdeg
  rw [momentFunctional_X_pow s k] at hq
  rw [hq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-- **Uniform tail bound**, independent of both the level and the parameter. -/
theorem quasiNodes_tail_weight_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {R : ℝ}
    (hR : 0 < R) :
    ∑ ξ ∈ (quasiNodes s n t).filter (fun ξ => R < |ξ|), quasiWeight s n t ξ ≤ s 2 / R ^ 2 := by
  classical
  have hmom : ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ * ξ ^ 2 = s 2 :=
    quasiSum_pow h n t 2 (by omega)
  have hstep : ∀ ξ ∈ (quasiNodes s n t).filter (fun ξ => R < |ξ|),
      quasiWeight s n t ξ ≤ quasiWeight s n t ξ * ξ ^ 2 / R ^ 2 := by
    intro ξ hξ
    have hmem : ξ ∈ quasiNodes s n t := (Finset.mem_filter.mp hξ).1
    have hRξ : R < |ξ| := (Finset.mem_filter.mp hξ).2
    have hpos : 0 < quasiWeight s n t ξ := quasiWeight_pos h n t hmem
    have hsq : R ^ 2 < ξ ^ 2 := by nlinarith [sq_abs ξ, abs_nonneg ξ]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hpos.le]
  calc ∑ ξ ∈ (quasiNodes s n t).filter (fun ξ => R < |ξ|), quasiWeight s n t ξ
      ≤ ∑ ξ ∈ (quasiNodes s n t).filter (fun ξ => R < |ξ|),
          quasiWeight s n t ξ * ξ ^ 2 / R ^ 2 := Finset.sum_le_sum hstep
    _ ≤ ∑ ξ ∈ quasiNodes s n t, quasiWeight s n t ξ * ξ ^ 2 / R ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro ξ hξ _
        have hpos : 0 < quasiWeight s n t ξ := quasiWeight_pos h n t hξ
        positivity
    _ = s 2 / R ^ 2 := by rw [← Finset.sum_div, hmom]

/-- The quasi measure of the complement of `[-R, R]`. -/
theorem quasiMeasure_compl_Icc_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {R : ℝ}
    (hR : 0 < R) :
    quasiMeasure s n t ((Set.Icc (-R) R)ᶜ) ≤ ENNReal.ofReal (s 2 / R ^ 2) := by
  classical
  have hA : MeasurableSet ((Set.Icc (-R) R)ᶜ) := measurableSet_Icc.compl
  have hset : ((Set.Icc (-R) R)ᶜ) = {x : ℝ | R < |x|} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
  have hterm : ∀ ξ ∈ quasiNodes s n t,
      ENNReal.ofReal (quasiWeight s n t ξ) * ({x : ℝ | R < |x|}).indicator 1 ξ
        = if R < |ξ| then ENNReal.ofReal (quasiWeight s n t ξ) else 0 := by
    intro ξ _
    by_cases hc : R < |ξ|
    · simp [Set.indicator_of_mem, hc]
    · simp [Set.indicator_of_notMem, hc]
  rw [quasiMeasure, finsetWeightedDirac_apply _ _ hA, hset,
    Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    ← ENNReal.ofReal_sum_of_nonneg fun ξ hξ => (quasiWeight_pos h n t
      (Finset.mem_filter.mp hξ).1).le]
  exact ENNReal.ofReal_le_ofReal (quasiNodes_tail_weight_le h hn t hR)

/-- The total mass of the quasi measure. -/
theorem quasiMeasure_univ (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    quasiMeasure s n t Set.univ = ENNReal.ofReal (s 0) := by
  classical
  rw [quasiMeasure, finsetWeightedDirac_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ξ hξ => (quasiWeight_pos h n t hξ).le]
  congr 1
  simpa using quasiSum_pow h n t 0 (by omega)

/-- The quasi measure rescaled to unit mass. -/
noncomputable def quasiProb (s : ℕ → ℝ) (n : ℕ) (t : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (s 0))⁻¹ • quasiMeasure s n t

theorem quasiProb_univ (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    quasiProb s n t Set.univ = 1 := by
  rw [quasiProb, Measure.smul_apply, quasiMeasure_univ h n t, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by simp [ENNReal.ofReal_eq_zero, not_le, moment_zero_pos h]) ENNReal.ofReal_ne_top

theorem isProbabilityMeasure_quasiProb (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    IsProbabilityMeasure (quasiProb s n t) :=
  ⟨quasiProb_univ h n t⟩

/-- The normalised tail bound. -/
theorem quasiProb_compl_Icc_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) (t : ℝ) {R : ℝ}
    (hR : 0 < R) :
    quasiProb s n t ((Set.Icc (-R) R)ᶜ) ≤ ENNReal.ofReal ((s 0)⁻¹ * (s 2 / R ^ 2)) := by
  have hstep : quasiProb s n t ((Set.Icc (-R) R)ᶜ)
      ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s 2 / R ^ 2) := by
    rw [quasiProb, Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right (quasiMeasure_compl_Icc_le h hn t hR) _
  refine le_trans hstep ?_
  rw [← ENNReal.ofReal_inv_of_pos (moment_zero_pos h),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (moment_zero_pos h).le)]

/-- **The normalised quasi measures form a tight family**, for *any* sequence of parameters. -/
theorem isTightMeasureSet_quasiProb (h : PositiveMomentForm s) (τ : ℕ → ℝ) :
    IsTightMeasureSet (Set.range fun n : ℕ => quasiProb s (n + 1) (τ n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨Set.Icc (-1) 1, isCompact_Icc, fun μ _ => le_top⟩
  · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hs0 : 0 < s 0 := moment_zero_pos h
    have hs2 : 0 < s 2 := moment_two_pos h
    have hcpos : 0 < s 2 / (s 0 * ε.toReal) := div_pos hs2 (mul_pos hs0 he0)
    refine ⟨Set.Icc (-Real.sqrt (s 2 / (s 0 * ε.toReal)))
      (Real.sqrt (s 2 / (s 0 * ε.toReal))), isCompact_Icc, ?_⟩
    rintro μ ⟨n, rfl⟩
    have hRpos : 0 < Real.sqrt (s 2 / (s 0 * ε.toReal)) := Real.sqrt_pos.mpr hcpos
    refine le_trans (quasiProb_compl_Icc_le h (Nat.le_add_left 1 n) (τ n) hRpos) ?_
    rw [Real.sq_sqrt hcpos.le]
    have hval : (s 0)⁻¹ * (s 2 / (s 2 / (s 0 * ε.toReal))) = ε.toReal := by
      have hs0' : s 0 ≠ 0 := hs0.ne'
      have hs2' : s 2 ≠ 0 := hs2.ne'
      have he0' : ε.toReal ≠ 0 := he0.ne'
      field_simp
    rw [hval, ENNReal.ofReal_toReal hεtop]

/-- The normalised quasi measure packaged as a `ProbabilityMeasure`. -/
noncomputable def quasiProbMeasure (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) :
    ProbabilityMeasure ℝ :=
  ⟨quasiProb s n t, isProbabilityMeasure_quasiProb h n t⟩

/-- **Prokhorov applies to the quasi family.** -/
theorem isCompact_closure_quasiProbMeasure (h : PositiveMomentForm s) (τ : ℕ → ℝ) :
    IsCompact (closure (Set.range fun n : ℕ => quasiProbMeasure h (n + 1) (τ n))) := by
  refine isCompact_closure_of_isTightMeasureSet ?_
  have hcoe : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) |
        μ ∈ Set.range fun n : ℕ => quasiProbMeasure h (n + 1) (τ n)}
      = Set.range fun n : ℕ => quasiProb s (n + 1) (τ n) := by
    ext ν
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨quasiProbMeasure h (n + 1) (τ n), ⟨n, rfl⟩, rfl⟩
  rw [hcoe]
  exact isTightMeasureSet_quasiProb h τ

end HTGeometry
