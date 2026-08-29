import GaloisForLFunctions.HTGeometry.ComplexGaussianCoefficientProbability
import GaloisForLFunctions.HTGeometry.InfinitePiSumSplit
import Mathlib.Analysis.PSeries

/-!
# The Gaussian coefficient sequence is almost surely polynomially bounded

Chebyshev's inequality makes the tail of one complex Gaussian coordinate quadratically small, so
the first Borel–Cantelli lemma gives `‖xₙ‖ ≤ n` for all large `n`, almost surely.  That is exactly
the decay needed for the planar Gaussian series to be entire.
-/

open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The law of the coefficient sequence of the planar Gaussian entire function. -/
def gaussianCoefficientLaw : Measure (ℕ → ℂ) :=
  Measure.infinitePi (fun _ : ℕ => complexGaussianProbability)

instance : IsProbabilityMeasure gaussianCoefficientLaw := by
  rw [gaussianCoefficientLaw]
  infer_instance

/-- The event that the `n`-th coordinate is larger than `n`. -/
def gaussianLargeCoordinate (n : ℕ) : Set (ℕ → ℂ) := {x | (n : ℝ) ≤ ‖x n‖}

theorem measurableSet_gaussianLargeCoordinate (n : ℕ) :
    MeasurableSet (gaussianLargeCoordinate n) := by
  refine measurableSet_le measurable_const ?_
  exact (measurable_pi_apply (X := fun _ : ℕ => ℂ) n).norm

theorem measure_gaussianLargeCoordinate_le {n : ℕ} (hn : 0 < n) :
    gaussianCoefficientLaw (gaussianLargeCoordinate n)
      ≤ ENNReal.ofReal (((n / 2 : ℝ) ^ 2)⁻¹) + ENNReal.ofReal (((n / 2 : ℝ) ^ 2)⁻¹) := by
  have hmap : Measure.map (fun x : ℕ → ℂ => x n) gaussianCoefficientLaw
      = complexGaussianProbability := by
    rw [gaussianCoefficientLaw]
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => complexGaussianProbability) n).map_eq
  have hset : MeasurableSet {z : ℂ | (n : ℝ) ≤ ‖z‖} :=
    measurableSet_le measurable_const measurable_norm
  have hpre : gaussianLargeCoordinate n
      = (fun x : ℕ → ℂ => x n) ⁻¹' {z : ℂ | (n : ℝ) ≤ ‖z‖} := rfl
  rw [hpre, ← Measure.map_apply (measurable_pi_apply (X := fun _ : ℕ => ℂ) n) hset, hmap]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact measure_norm_ge_le hnpos

theorem summable_gaussianTailBound :
    ∑' n : ℕ, gaussianCoefficientLaw (gaussianLargeCoordinate n) ≠ ⊤ := by
  have hbound : ∀ n : ℕ, gaussianCoefficientLaw (gaussianLargeCoordinate (n + 1))
      ≤ ENNReal.ofReal (8 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    have h := measure_gaussianLargeCoordinate_le (n := n + 1) (by omega)
    refine le_trans h ?_
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) := by positivity
    have hval : (((n + 1 : ℕ) : ℝ) / 2) ^ 2 = ((n : ℝ) + 1) ^ 2 / 4 := by
      push_cast
      ring
    rw [hval]
    rw [show (((n : ℝ) + 1) ^ 2 / 4)⁻¹ = 4 / ((n : ℝ) + 1) ^ 2 by
      field_simp]
    have hid : (4 : ℝ) / ((n : ℝ) + 1) ^ 2 + 4 / ((n : ℝ) + 1) ^ 2
        = 8 / ((n : ℝ) + 1) ^ 2 := by ring
    rw [hid]
  have hsum : ∑' n : ℕ, ENNReal.ofReal (8 / ((n : ℝ) + 1) ^ 2) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)]
    · exact ENNReal.ofReal_ne_top
    · have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
        Real.summable_one_div_nat_pow.2 one_lt_two
      have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ)) : ℝ) ^ 2) :=
        (summable_nat_add_iff 1).2 hbase
      refine (hshift.mul_left 8).congr fun n => ?_
      push_cast
      ring
  intro htop
  apply hsum
  have hshift : ∑' n : ℕ, gaussianCoefficientLaw (gaussianLargeCoordinate n)
      = gaussianCoefficientLaw (gaussianLargeCoordinate 0)
        + ∑' n : ℕ, gaussianCoefficientLaw (gaussianLargeCoordinate (n + 1)) :=
    tsum_eq_zero_add' (by exact ENNReal.summable)
  rw [hshift] at htop
  have h1 : gaussianCoefficientLaw (gaussianLargeCoordinate 0) ≠ ⊤ := measure_ne_top _ _
  have h2 : ∑' n : ℕ, gaussianCoefficientLaw (gaussianLargeCoordinate (n + 1)) = ⊤ := by
    by_contra h
    exact (ENNReal.add_ne_top.2 ⟨h1, h⟩) htop
  refine top_le_iff.1 ?_
  rw [← h2]
  exact ENNReal.tsum_le_tsum hbound

/-- **Almost-sure polynomial bound on the Gaussian coefficients.** -/
theorem ae_eventually_norm_le_index :
    ∀ᵐ x ∂gaussianCoefficientLaw, ∀ᶠ n : ℕ in atTop, ‖x n‖ < (n : ℝ) := by
  have hBC := measure_limsup_atTop_eq_zero (μ := gaussianCoefficientLaw)
    (s := gaussianLargeCoordinate) summable_gaussianTailBound
  rw [ae_iff]
  refine measure_mono_null ?_ hBC
  intro x hx
  rw [Set.mem_setOf_eq, not_eventually] at hx
  rw [limsup_eq_iInf_iSup_of_nat]
  simp only [Set.iInf_eq_iInter, Set.iSup_eq_iUnion, Set.mem_iInter, Set.mem_iUnion,
    exists_prop]
  intro k
  obtain ⟨n, hn, hxn⟩ := (frequently_atTop.1 hx) k
  exact ⟨n, hn, not_lt.1 hxn⟩

end

end GaloisForLFunctions.HTGeometry
