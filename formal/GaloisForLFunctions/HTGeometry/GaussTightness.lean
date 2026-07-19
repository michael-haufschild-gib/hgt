import GaloisForLFunctions.HTGeometry.GaussMeasure

/-!
# Tightness of the Gauss measure family

The Gauss measures all carry the same second moment `s₂`, and that single uniform bound keeps their
mass from escaping to infinity: the total weight sitting outside `[-R, R]` is at most `s₂ / R²`,
uniformly in the level `n`.

The estimate is elementary here rather than measure-theoretic.  Because each Gauss measure is a
finite weighted sum of point masses, the mass outside a ball is a finite sum of Christoffel weights,
and Chebyshev's inequality becomes the observation that `1 ≤ ξ² / R²` on the nodes being summed.

Uniform control of this kind is exactly the hypothesis of Prokhorov's theorem, which mathlib carries
in `Mathlib/MeasureTheory/Measure/Prokhorov.lean`.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- Evaluation of a finite weighted Dirac sum on a measurable set. -/
theorem finsetWeightedDirac_apply (t : Finset ℝ) (w : ℝ → ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∑ y ∈ t, ENNReal.ofReal (w y) • Measure.dirac y) A
      = ∑ y ∈ t, ENNReal.ofReal (w y) * A.indicator 1 y := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.add_apply, ih,
        Measure.smul_apply, Measure.dirac_apply' a hA, smul_eq_mul]

/-- The quadrature sum of a monomial is the corresponding moment. -/
theorem gaussSum_pow (h : PositiveMomentForm s) (n k : ℕ) (hk : k ≤ 2 * n + 1) :
    ∑ ξ ∈ gaussNodes s n, christoffel s n ξ * ξ ^ k = s k := by
  have hdeg : (Polynomial.X ^ k : Polynomial ℝ).degree < ((2 * n + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast (by omega : k < 2 * n + 2)
  have hq := momentFunctional_eq_gaussSum h n (Polynomial.X ^ k) hdeg
  rw [momentFunctional_X_pow s k] at hq
  rw [hq]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

/-- **Uniform tail bound.**  The Christoffel weight carried by nodes outside `[-R, R]` is at most
`s₂ / R²`, with no dependence on the level. -/
theorem gaussNodes_tail_weight_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    (hR : 0 < R) :
    ∑ ξ ∈ (gaussNodes s n).filter (fun ξ => R < |ξ|), christoffel s n ξ ≤ s 2 / R ^ 2 := by
  classical
  have hmom : ∑ ξ ∈ gaussNodes s n, christoffel s n ξ * ξ ^ 2 = s 2 :=
    gaussSum_pow h n 2 (by omega)
  have hstep : ∀ ξ ∈ (gaussNodes s n).filter (fun ξ => R < |ξ|),
      christoffel s n ξ ≤ christoffel s n ξ * ξ ^ 2 / R ^ 2 := by
    intro ξ hξ
    have hRξ : R < |ξ| := (Finset.mem_filter.mp hξ).2
    have hpos : 0 < christoffel s n ξ := christoffel_pos h n ξ
    have hsq : R ^ 2 < ξ ^ 2 := by
      nlinarith [sq_abs ξ, abs_nonneg ξ]
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hpos.le]
  calc ∑ ξ ∈ (gaussNodes s n).filter (fun ξ => R < |ξ|), christoffel s n ξ
      ≤ ∑ ξ ∈ (gaussNodes s n).filter (fun ξ => R < |ξ|),
          christoffel s n ξ * ξ ^ 2 / R ^ 2 := Finset.sum_le_sum hstep
    _ ≤ ∑ ξ ∈ gaussNodes s n, christoffel s n ξ * ξ ^ 2 / R ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
        intro ξ _ _
        have hpos : 0 < christoffel s n ξ := christoffel_pos h n ξ
        positivity
    _ = s 2 / R ^ 2 := by
        rw [← Finset.sum_div, hmom]

/-! ## Tightness of the family -/

/-- The Gauss measure of the complement of `[-R, R]`, bounded by the uniform tail estimate. -/
theorem gaussMeasure_compl_Icc_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    (hR : 0 < R) :
    gaussMeasure s n ((Set.Icc (-R) R)ᶜ) ≤ ENNReal.ofReal (s 2 / R ^ 2) := by
  classical
  have hA : MeasurableSet ((Set.Icc (-R) R)ᶜ) := measurableSet_Icc.compl
  have hset : ((Set.Icc (-R) R)ᶜ) = {x : ℝ | R < |x|} := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_Icc, Set.mem_setOf_eq, ← abs_le, not_le]
  have hterm : ∀ ξ ∈ gaussNodes s n,
      ENNReal.ofReal (christoffel s n ξ) * ({x : ℝ | R < |x|}).indicator 1 ξ
        = if R < |ξ| then ENNReal.ofReal (christoffel s n ξ) else 0 := by
    intro ξ _
    by_cases hc : R < |ξ|
    · simp [Set.indicator_of_mem, hc]
    · simp [Set.indicator_of_notMem, hc]
  rw [gaussMeasure, finsetWeightedDirac_apply _ _ hA, hset,
    Finset.sum_congr rfl hterm, ← Finset.sum_filter,
    ← ENNReal.ofReal_sum_of_nonneg fun ξ _ => (christoffel_pos h n ξ).le]
  exact ENNReal.ofReal_le_ofReal (gaussNodes_tail_weight_le h hn hR)

/-- The second moment is strictly positive. -/
theorem moment_two_pos (h : PositiveMomentForm s) : 0 < s 2 := by
  have hX : momentInner s Polynomial.X Polynomial.X = s 2 := by
    rw [momentInner_def]
    have hsq : (Polynomial.X : Polynomial ℝ) * Polynomial.X = Polynomial.X ^ 2 := by ring
    rw [hsq, momentFunctional_X_pow]
  rw [← hX]
  exact h.pos_of_ne_zero _ Polynomial.X_ne_zero

/-- **The Gauss measures form a tight family.**  A single uniform second moment controls every tail
at once, which is exactly the hypothesis Prokhorov's theorem consumes. -/
theorem isTightMeasureSet_gaussMeasure (h : PositiveMomentForm s) :
    IsTightMeasureSet (Set.range fun n : ℕ => gaussMeasure s (n + 1)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨Set.Icc (-1) 1, isCompact_Icc, fun μ _ => le_top⟩
  · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hs2 : 0 < s 2 := moment_two_pos h
    have hquot : 0 < s 2 / ε.toReal := div_pos hs2 he0
    refine ⟨Set.Icc (-Real.sqrt (s 2 / ε.toReal)) (Real.sqrt (s 2 / ε.toReal)), isCompact_Icc, ?_⟩
    rintro μ ⟨n, rfl⟩
    have hRpos : 0 < Real.sqrt (s 2 / ε.toReal) := Real.sqrt_pos.mpr hquot
    refine le_trans (gaussMeasure_compl_Icc_le h (Nat.le_add_left 1 n) hRpos) ?_
    have hsq : Real.sqrt (s 2 / ε.toReal) ^ 2 = s 2 / ε.toReal :=
      Real.sq_sqrt hquot.le
    rw [hsq]
    have hval : s 2 / (s 2 / ε.toReal) = ε.toReal := by
      field_simp
    rw [hval, ENNReal.ofReal_toReal hεtop]

/-! ## Normalisation to a probability measure

Prokhorov's theorem is stated in mathlib for `ProbabilityMeasure`, while the Gauss measures carry
mass `s₀`.  Dividing by `s₀`, which is positive because the moment form is, turns each of them
into a probability measure without disturbing the tail estimate. -/

/-- The total mass of the Gauss measure, as a measure of the whole line. -/
theorem gaussMeasure_univ (h : PositiveMomentForm s) (n : ℕ) :
    gaussMeasure s n Set.univ = ENNReal.ofReal (s 0) := by
  classical
  rw [gaussMeasure, finsetWeightedDirac_apply _ _ MeasurableSet.univ]
  simp only [Set.indicator_univ, Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg fun ξ _ => (christoffel_pos h n ξ).le]
  congr 1
  simpa using gaussSum_pow h n 0 (by omega)

/-- The zeroth moment is strictly positive. -/
theorem moment_zero_pos (h : PositiveMomentForm s) : 0 < s 0 := by
  have h1 : momentInner s 1 1 = s 0 := by
    rw [momentInner_def, one_mul]
    have hx : (1 : Polynomial ℝ) = Polynomial.X ^ 0 := by simp
    rw [hx, momentFunctional_X_pow]
  rw [← h1]
  exact h.pos_of_ne_zero 1 one_ne_zero

/-- The Gauss measure rescaled to unit mass. -/
noncomputable def gaussProb (s : ℕ → ℝ) (n : ℕ) : Measure ℝ :=
  (ENNReal.ofReal (s 0))⁻¹ • gaussMeasure s n

theorem gaussProb_univ (h : PositiveMomentForm s) (n : ℕ) : gaussProb s n Set.univ = 1 := by
  rw [gaussProb, Measure.smul_apply, gaussMeasure_univ h n, smul_eq_mul]
  exact ENNReal.inv_mul_cancel
    (by simp [ENNReal.ofReal_eq_zero, not_le, moment_zero_pos h]) ENNReal.ofReal_ne_top

theorem isProbabilityMeasure_gaussProb (h : PositiveMomentForm s) (n : ℕ) :
    IsProbabilityMeasure (gaussProb s n) :=
  ⟨gaussProb_univ h n⟩

/-- The normalised tail bound. -/
theorem gaussProb_compl_Icc_le (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    (hR : 0 < R) :
    gaussProb s n ((Set.Icc (-R) R)ᶜ)
      ≤ (ENNReal.ofReal (s 0))⁻¹ * ENNReal.ofReal (s 2 / R ^ 2) := by
  rw [gaussProb, Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_right (gaussMeasure_compl_Icc_le h hn hR) _

/-- The normalised tail bound with the scalar folded inside. -/
theorem gaussProb_compl_Icc_le' (h : PositiveMomentForm s) {n : ℕ} (hn : 1 ≤ n) {R : ℝ}
    (hR : 0 < R) :
    gaussProb s n ((Set.Icc (-R) R)ᶜ) ≤ ENNReal.ofReal ((s 0)⁻¹ * (s 2 / R ^ 2)) := by
  refine le_trans (gaussProb_compl_Icc_le h hn hR) ?_
  rw [← ENNReal.ofReal_inv_of_pos (moment_zero_pos h),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (moment_zero_pos h).le)]

/-- **The normalised Gauss measures form a tight family.** -/
theorem isTightMeasureSet_gaussProb (h : PositiveMomentForm s) :
    IsTightMeasureSet (Set.range fun n : ℕ => gaussProb s (n + 1)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨Set.Icc (-1) 1, isCompact_Icc, fun μ _ => le_top⟩
  · have he0 : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    have hs0 : 0 < s 0 := moment_zero_pos h
    have hs2 : 0 < s 2 := moment_two_pos h
    have hs0' : s 0 ≠ 0 := hs0.ne'
    have hs2' : s 2 ≠ 0 := hs2.ne'
    have he0' : ε.toReal ≠ 0 := he0.ne'
    have hcpos : 0 < s 2 / (s 0 * ε.toReal) := div_pos hs2 (mul_pos hs0 he0)
    refine ⟨Set.Icc (-Real.sqrt (s 2 / (s 0 * ε.toReal)))
      (Real.sqrt (s 2 / (s 0 * ε.toReal))), isCompact_Icc, ?_⟩
    rintro μ ⟨n, rfl⟩
    have hRpos : 0 < Real.sqrt (s 2 / (s 0 * ε.toReal)) := Real.sqrt_pos.mpr hcpos
    refine le_trans (gaussProb_compl_Icc_le' h (Nat.le_add_left 1 n) hRpos) ?_
    rw [Real.sq_sqrt hcpos.le]
    have hval : (s 0)⁻¹ * (s 2 / (s 2 / (s 0 * ε.toReal))) = ε.toReal := by
      field_simp
    rw [hval, ENNReal.ofReal_toReal hεtop]

/-- The normalised Gauss measure packaged as a `ProbabilityMeasure`. -/
noncomputable def gaussProbMeasure (h : PositiveMomentForm s) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨gaussProb s n, isProbabilityMeasure_gaussProb h n⟩

/-- **Prokhorov applies: the Gauss family is relatively compact.**  Tightness of the normalised
measures is exactly the hypothesis of `isCompact_closure_of_isTightMeasureSet`, so the family of
Gauss probability measures has compact closure in the weak topology. -/
theorem isCompact_closure_gaussProbMeasure (h : PositiveMomentForm s) :
    IsCompact (closure (Set.range fun n : ℕ => gaussProbMeasure h (n + 1))) := by
  refine isCompact_closure_of_isTightMeasureSet ?_
  have hcoe : {((μ : ProbabilityMeasure ℝ) : Measure ℝ) |
        μ ∈ Set.range fun n : ℕ => gaussProbMeasure h (n + 1)}
      = Set.range fun n : ℕ => gaussProb s (n + 1) := by
    ext ν
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨gaussProbMeasure h (n + 1), ⟨n, rfl⟩, rfl⟩
  rw [hcoe]
  exact isTightMeasureSet_gaussProb h

end HTGeometry
