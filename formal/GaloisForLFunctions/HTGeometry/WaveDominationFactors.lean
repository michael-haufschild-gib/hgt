import GaloisForLFunctions.HTGeometry.WaveDominationL2
import GaloisForLFunctions.HTGeometry.WaveEnergyDerivative

/-!
# The dominating function from factor-wise bounds

The time derivative of the energy density is a sum of products of two factors, so square-integrable
dominating functions for the factors — uniform on a time interval — assemble into an integrable
dominating function for it. With this the last hypothesis of the square-integrable uniqueness
theorem becomes an `L²` statement about the solution.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Factors

variable {d : ℕ} {u : ℝ × (Fin d → ℝ) → ℝ}

/-- **Factor-wise square-integrable domination gives the dominating function the estimate needs.** -/
theorem exists_bound_of_factor_memLp (hu : ContDiff ℝ ∞ u) (t : ℝ)
    {gT gTT gU : (Fin d → ℝ) → ℝ} {gS gST : Fin d → (Fin d → ℝ) → ℝ}
    (hgT : MemLp gT 2 (volume : Measure (Fin d → ℝ)))
    (hgTT : MemLp gTT 2 (volume : Measure (Fin d → ℝ)))
    (hgU : MemLp gU 2 (volume : Measure (Fin d → ℝ)))
    (hgS : ∀ i : Fin d, MemLp (gS i) 2 (volume : Measure (Fin d → ℝ)))
    (hgST : ∀ i : Fin d, MemLp (gST i) 2 (volume : Measure (Fin d → ℝ)))
    (hT : ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
      |waveDirDeriv (timeDir d) u (s, x)| ≤ gT x)
    (hTT : ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
      |waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x)| ≤ gTT x)
    (hU : ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ, |u (s, x)| ≤ gU x)
    (hS : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
      |waveDirDeriv (spaceDir d i) u (s, x)| ≤ gS i x)
    (hST : ∀ (i : Fin d), ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
      |waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x)| ≤ gST i x) :
    ∃ bound : (Fin d → ℝ) → ℝ, Integrable bound (volume : Measure (Fin d → ℝ)) ∧
      ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
        ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖ ≤ bound x := by
  classical
  refine ⟨fun x => 2 * (gT x * gTT x) + (∑ i : Fin d, 2 * (gS i x * gST i x))
      + 2 * (gU x * gT x), ?_, ?_⟩
  · have h1 : Integrable (fun x : Fin d → ℝ => 2 * (gT x * gTT x))
        (volume : Measure (Fin d → ℝ)) := (MemLp.integrable_mul hgT hgTT).const_mul 2
    have h2 : Integrable (fun x : Fin d → ℝ => ∑ i : Fin d, 2 * (gS i x * gST i x))
        (volume : Measure (Fin d → ℝ)) :=
      integrable_finsetSum _ fun i _ => (MemLp.integrable_mul (hgS i) (hgST i)).const_mul 2
    have h3 : Integrable (fun x : Fin d → ℝ => 2 * (gU x * gT x))
        (volume : Measure (Fin d → ℝ)) := (MemLp.integrable_mul hgU hgT).const_mul 2
    exact (h1.add h2).add h3
  · intro s hs x
    rw [Real.norm_eq_abs, waveDirDeriv_energyDensity hu (s, x)]
    have habs : |2 * (waveDirDeriv (timeDir d) u (s, x)
          * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x))
        + (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
            * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x)))
        + 2 * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))|
        ≤ |2 * (waveDirDeriv (timeDir d) u (s, x)
            * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x))|
          + |∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
              * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x))|
          + |2 * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))| := by
      have hA : |2 * (waveDirDeriv (timeDir d) u (s, x)
            * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x))
          + (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
              * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x)))|
          ≤ |2 * (waveDirDeriv (timeDir d) u (s, x)
              * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x))|
            + |∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
                * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x))| :=
        abs_add_le _ _
      have hB := abs_add_le (2 * (waveDirDeriv (timeDir d) u (s, x)
            * waveDirDeriv (timeDir d) (waveDirDeriv (timeDir d) u) (s, x))
          + (∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
              * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x))))
        (2 * (u (s, x) * waveDirDeriv (timeDir d) u (s, x)))
      linarith
    refine le_trans habs ?_
    have hprod : ∀ (a b p q : ℝ), |a| ≤ p → |b| ≤ q → |2 * (a * b)| ≤ 2 * (p * q) := by
      intro a b p q ha hb
      rw [abs_mul, abs_two, abs_mul]
      have hp : 0 ≤ p := le_trans (abs_nonneg a) ha
      exact mul_le_mul_of_nonneg_left (mul_le_mul ha hb (abs_nonneg b) hp) (by norm_num)
    have h1 := hprod _ _ _ _ (hT s hs x) (hTT s hs x)
    have h3 := hprod _ _ _ _ (hU s hs x) (hT s hs x)
    have h2 : |∑ i : Fin d, 2 * (waveDirDeriv (spaceDir d i) u (s, x)
          * waveDirDeriv (timeDir d) (waveDirDeriv (spaceDir d i) u) (s, x))|
        ≤ ∑ i : Fin d, 2 * (gS i x * gST i x) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum fun i _ => hprod _ _ _ _ (hS i s hs x) (hST i s hs x)
    linarith

end Factors

end GaloisForLFunctions.HTGeometry
