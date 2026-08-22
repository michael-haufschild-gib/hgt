import GaloisForLFunctions.HilbertMetric.GradedPartition
import GaloisForLFunctions.HTGeometry.ReplicaObserverJacobianCompensationLaw
import GaloisForLFunctions.HTGeometry.GaussianDeterminantTubeUpperBound

/-!
# Observer-Jacobian active-minor Gaussian law

The determinant of a rectangular observer's Gram matrix is the exact sum of the squares of its
canonical maximal minors.  Consequently either the observer is rank deficient, or one active
coefficient block carries at least the average Gram volume.  Conditioning on every coefficient
outside that block turns those coefficients into an arbitrary translation, so the same minor
controls the full affine Gaussian tube without a union factor.

This module makes that compiler quantitative.  For an `N`-row, `v`-direction observer, the sharp
finite selection loss is `N.choose v`.  Both coordinate boxes and approximate sup-norm tubes are
covered.  The singular branch is explicit; no nonsingularity assumption is hidden in the capstone.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Observer columns, viewed as the feature rows consumed by finite Gram--Cauchy--Binet. -/
def observerFeatureRows {N v : ℕ} (J : Fin N → Fin v → ℝ) :
    Fin v → Fin N → ℝ := fun i a => J a i

/-- Canonical maximal observer minor selected by one unordered active row set. -/
def observerActiveMinor {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) : ℝ :=
  HilbertMetric.standardFeatureMinor (observerFeatureRows J) s

/-- Matrix of the square active observer selected by `s`. -/
def observerActiveMatrix {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) : Matrix (Fin v) (Fin v) ℝ :=
  Matrix.of fun i j => J (Set.powersetCard.ofFinEmbEquiv.symm s j) i

/-- Square active observer as a linear map on the selected Gaussian coefficients. -/
def observerActiveMap {N v : ℕ} (J : Fin N → Fin v → ℝ)
    (s : Set.powersetCard (Fin N) v) :
    (Fin v → ℝ) →ₗ[ℝ] (Fin v → ℝ) :=
  Matrix.toLin' (observerActiveMatrix J s)

theorem observerJacobianGram_eq_standardFeatureGram {N v : ℕ}
    (J : Fin N → Fin v → ℝ) :
    observerJacobianGram J =
      HilbertMetric.standardFeatureGram (observerFeatureRows J) := by
  ext i j
  simp [observerJacobianGram, HilbertMetric.standardFeatureGram,
    observerFeatureRows]

theorem observerActiveMinor_eq_det_activeMatrix {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v) :
    observerActiveMinor J s = (observerActiveMatrix J s).det := by
  rfl

theorem det_observerActiveMap {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (s : Set.powersetCard (Fin N) v) :
    LinearMap.det (observerActiveMap J s) = observerActiveMinor J s := by
  simp [observerActiveMap, observerActiveMinor, observerActiveMatrix,
    observerFeatureRows, HilbertMetric.standardFeatureMinor]

/-- Exact observer Gram--Cauchy--Binet identity over unordered canonical active blocks. -/
theorem det_observerJacobianGram_eq_sum_activeMinor_sq {N v : ℕ}
    (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram J).det =
      ∑ s : Set.powersetCard (Fin N) v, observerActiveMinor J s ^ 2 := by
  rw [observerJacobianGram_eq_standardFeatureGram,
    HilbertMetric.det_standardFeatureGram_eq_pluckerVolumeSq]
  rfl

theorem det_observerJacobianGram_nonneg {N v : ℕ}
    (J : Fin N → Fin v → ℝ) : 0 ≤ (observerJacobianGram J).det := by
  rw [det_observerJacobianGram_eq_sum_activeMinor_sq]
  positivity

/-- More visible directions than observer rows force exact Gram singularity. -/
theorem det_observerJacobianGram_zero_of_lt {N v : ℕ}
    (hNv : N < v) (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram J).det = 0 := by
  rw [det_observerJacobianGram_eq_sum_activeMinor_sq]
  apply Fintype.sum_eq_zero
  intro s
  have hle : v ≤ N := by
    rw [← Set.powersetCard.card_eq s]
    simpa using Finset.card_le_univ (s : Finset (Fin N))
  omega

/-- At least one canonical active minor carries the average Gram volume.  The loss is exactly the
number `N.choose v` of maximal unordered minors. -/
theorem exists_activeMinor_average_of_le {N v : ℕ}
    (hvN : v ≤ N) (J : Fin N → Fin v → ℝ) :
    ∃ s : Set.powersetCard (Fin N) v,
      (observerJacobianGram J).det ≤
        (N.choose v : ℝ) * observerActiveMinor J s ^ 2 := by
  classical
  obtain ⟨t, _ht, hcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin N)))
      (n := v) (by simpa using hvN)
  let s0 : Set.powersetCard (Fin N) v := Set.powersetCard.ofCard hcard
  have hnonempty : (Finset.univ :
      Finset (Set.powersetCard (Fin N) v)).Nonempty :=
    ⟨s0, Finset.mem_univ _⟩
  have hcardType : Fintype.card (Set.powersetCard (Fin N) v) = N.choose v := by
    simpa [Nat.card_eq_fintype_card] using
      (Set.powersetCard.card (Fin N) v)
  obtain ⟨s, _hs, hs⟩ := Finset.exists_le_of_sum_le hnonempty
    (f := fun _s : Set.powersetCard (Fin N) v =>
      (observerJacobianGram J).det)
    (g := fun s => (N.choose v : ℝ) * observerActiveMinor J s ^ 2)
    (by
      rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
        ← det_observerJacobianGram_eq_sum_activeMinor_sq]
      simp [hcardType])
  exact ⟨s, hs⟩

/-- Unconditional algebraic dichotomy: exact rank failure or a canonical large active minor. -/
theorem observerJacobianGram_zero_or_exists_activeMinor_average {N v : ℕ}
    (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram J).det = 0 ∨
      ∃ s : Set.powersetCard (Fin N) v,
        (observerJacobianGram J).det ≤
          (N.choose v : ℝ) * observerActiveMinor J s ^ 2 := by
  by_cases hvN : v ≤ N
  · exact Or.inr (exists_activeMinor_average_of_le hvN J)
  · exact Or.inl (det_observerJacobianGram_zero_of_lt (by omega) J)

/-- In the nonsingular branch, one active determinant is at least the square root of the average
Gram volume. -/
theorem exists_activeMinor_sqrt_lower_of_det_ne_zero {N v : ℕ}
    (J : Fin N → Fin v → ℝ)
    (hdet : (observerJacobianGram J).det ≠ 0) :
    ∃ s : Set.powersetCard (Fin N) v,
      Real.sqrt ((observerJacobianGram J).det / (N.choose v : ℝ)) ≤
        |observerActiveMinor J s| := by
  have hvN : v ≤ N := by
    by_contra h
    exact hdet (det_observerJacobianGram_zero_of_lt (by omega) J)
  obtain ⟨s, hs⟩ := exists_activeMinor_average_of_le hvN J
  have hcpos : (0 : ℝ) < N.choose v := by
    exact_mod_cast Nat.choose_pos hvN
  refine ⟨s, (Real.sqrt_le_iff).2 ⟨abs_nonneg _, ?_⟩⟩
  rw [sq_abs]
  exact (div_le_iff₀ hcpos).2 (by simpa [mul_comm] using hs)

/-- Reciprocal form of the active-minor average law, ready for change of variables. -/
theorem inv_abs_activeMinor_le_sqrt_choose_div_det {N v : ℕ}
    (J : Fin N → Fin v → ℝ)
    (hdet : (observerJacobianGram J).det ≠ 0)
    (s : Set.powersetCard (Fin N) v)
    (hs : (observerJacobianGram J).det ≤
      (N.choose v : ℝ) * observerActiveMinor J s ^ 2) :
    |(observerActiveMinor J s)⁻¹| ≤
      Real.sqrt ((N.choose v : ℝ) / (observerJacobianGram J).det) := by
  have hD : 0 < (observerJacobianGram J).det :=
    lt_of_le_of_ne (det_observerJacobianGram_nonneg J) (Ne.symm hdet)
  have hm : 0 < |observerActiveMinor J s| := by
    rw [abs_pos]
    intro hm0
    rw [hm0] at hs
    norm_num at hs
    nlinarith
  rw [abs_inv]
  apply (Real.le_sqrt (inv_nonneg.mpr (abs_nonneg _))
    (div_nonneg (by positivity) hD.le)).2
  rw [inv_pow]
  apply (le_div_iff₀ hD).2
  have hquot : (observerJacobianGram J).det /
      |observerActiveMinor J s| ^ 2 ≤ (N.choose v : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hm)).2
    simpa [sq_abs, mul_comm] using hs
  simpa [div_eq_mul_inv, mul_comm] using hquot

/-- A nonsingular Gram determinant selects one active block controlling every inactive-drift box
tube by the explicit reciprocal square-root Gram budget. -/
theorem exists_activeMinor_gaussianTube_le_gramBudget {N v : ℕ}
    (J : Fin N → Fin v → ℝ)
    (hdet : (observerJacobianGram J).det ≠ 0) :
    ∃ s : Set.powersetCard (Fin N) v,
      ∀ (k : ℕ) (B : (Fin k → ℝ) →ₗ[ℝ] (Fin v → ℝ))
        (center : Fin v → ℝ) (radius : ℝ),
      ((Measure.pi fun _ : Fin k => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin v => gaussianReal 0 1))
          (gaussianConditionedLinearBoxTube (observerActiveMap J s)
            B center radius) ≤
        gaussianDensityPeakENN ^ v *
          ENNReal.ofReal
            (Real.sqrt ((N.choose v : ℝ) / (observerJacobianGram J).det)) *
          ENNReal.ofReal (2 * radius) ^ v := by
  have hvN : v ≤ N := by
    by_contra h
    exact hdet (det_observerJacobianGram_zero_of_lt (by omega) J)
  obtain ⟨s, hs⟩ := exists_activeMinor_average_of_le hvN J
  have hminor : observerActiveMinor J s ≠ 0 := by
    intro hm
    rw [hm] at hs
    norm_num at hs
    exact hdet (le_antisymm hs (det_observerJacobianGram_nonneg J))
  refine ⟨s, fun k B center radius => ?_⟩
  have hbase := measure_gaussianConditionedLinearBoxTube_le
    (observerActiveMap J s) B center radius
  rw [gaussianLinearBoxTubeBudget, activeObserverPseudodeterminant,
    if_neg (abs_ne_zero.mpr (by simpa [det_observerActiveMap] using hminor))] at hbase
  refine hbase.trans ?_
  gcongr
  rw [det_observerActiveMap]
  exact inv_abs_activeMinor_le_sqrt_choose_div_det J hdet s hs

/-- Total observer-Gram tube budget.  Singular observers pay the exact probability cap `1`; the
nonsingular branch pays the Cauchy--Binet active-minor bound. -/
def observerJacobianGramTubeBudget {N v : ℕ}
    (J : Fin N → Fin v → ℝ) (radius : ℝ) : ℝ≥0∞ :=
  if (observerJacobianGram J).det = 0 then 1
  else gaussianDensityPeakENN ^ v *
    ENNReal.ofReal
      (Real.sqrt ((N.choose v : ℝ) / (observerJacobianGram J).det)) *
    ENNReal.ofReal (2 * radius) ^ v

/-- **Observer pseudodeterminant-to-Gaussian-tube compiler.**  Unconditionally, the rectangular
observer is singular, or one canonical active coefficient block simultaneously carries the sharp
Cauchy--Binet average determinant and controls every affine box and approximate sup-norm tube,
uniformly over arbitrary inactive Gaussian drift. -/
theorem observerJacobianGram_activeMinor_gaussianTube_dichotomy {N v : ℕ}
    (J : Fin N → Fin v → ℝ) :
    (observerJacobianGram J).det = 0 ∨
      ∃ s : Set.powersetCard (Fin N) v,
        Real.sqrt ((observerJacobianGram J).det / (N.choose v : ℝ)) ≤
            |observerActiveMinor J s| ∧
        ∀ (k : ℕ) (B : (Fin k → ℝ) →ₗ[ℝ] (Fin v → ℝ))
          (center : Fin v → ℝ) (radius : ℝ),
          ((Measure.pi fun _ : Fin k => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin v => gaussianReal 0 1))
              (gaussianConditionedLinearBoxTube (observerActiveMap J s)
                B center radius) ≤ observerJacobianGramTubeBudget J radius ∧
          ((Measure.pi fun _ : Fin k => gaussianReal 0 1).prod
            (Measure.pi fun _ : Fin v => gaussianReal 0 1))
              (gaussianConditionedObserverNormTube (observerActiveMap J s)
                B center radius) ≤ observerJacobianGramTubeBudget J radius := by
  by_cases hdet : (observerJacobianGram J).det = 0
  · exact Or.inl hdet
  · right
    have hvN : v ≤ N := by
      by_contra h
      exact hdet (det_observerJacobianGram_zero_of_lt (by omega) J)
    obtain ⟨s, hs⟩ := exists_activeMinor_average_of_le hvN J
    have hcpos : (0 : ℝ) < N.choose v := by
      exact_mod_cast Nat.choose_pos hvN
    have hsqrt : Real.sqrt
        ((observerJacobianGram J).det / (N.choose v : ℝ)) ≤
        |observerActiveMinor J s| := by
      apply (Real.sqrt_le_iff).2
      refine ⟨abs_nonneg _, ?_⟩
      rw [sq_abs]
      exact (div_le_iff₀ hcpos).2 (by simpa [mul_comm] using hs)
    have hminor : observerActiveMinor J s ≠ 0 := by
      intro hm
      rw [hm] at hs
      norm_num at hs
      exact hdet (le_antisymm hs (det_observerJacobianGram_nonneg J))
    refine ⟨s, hsqrt, fun k B center radius => ?_⟩
    have hinv := inv_abs_activeMinor_le_sqrt_choose_div_det J hdet s hs
    have hbox := measure_gaussianConditionedLinearBoxTube_le
      (observerActiveMap J s) B center radius
    have hnorm := measure_gaussianConditionedObserverNormTube_le
      (observerActiveMap J s) B center radius
    rw [gaussianLinearBoxTubeBudget, activeObserverPseudodeterminant,
      if_neg (abs_ne_zero.mpr (by simpa [det_observerActiveMap] using hminor))]
      at hbox hnorm
    rw [observerJacobianGramTubeBudget, if_neg hdet]
    constructor
    · refine hbox.trans ?_
      gcongr
      rw [det_observerActiveMap]
      exact hinv
    · refine hnorm.trans ?_
      gcongr
      rw [det_observerActiveMap]
      exact hinv

end GaloisForLFunctions.HTGeometry
