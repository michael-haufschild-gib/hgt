import GaloisForLFunctions.RHTower.ZetaChiDisplacedSubintervalOscillatoryIntegral
import GaloisForLFunctions.RHTower.ZetaChiDisplacedDirichletCross

/-!
# Displaced Dirichlet crosses on dyadic subintervals

Finite positive/negative Dirichlet crosses inherit the displaced stationary-phase estimate on
every subinterval of a fixed dyadic block.  The coefficient cost remains the exact factorized
`ell^1` mass.
-/

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

theorem integral_zetaChiDisplacedDirichletCross_eq_sum_subinterval
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (P N : ℕ) (c : Fin P → ℂ) (e : Fin N → ℂ) (a b : ℝ) :
    (∫ t in a..b, zetaChiDisplacedDirichletCross d P N c e t) =
      ∑ i : Fin P, ∑ j : Fin N, (c i * e j) *
        (∫ t in a..b, zetaChi (displacedLinePt d t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
  have hchi := continuous_zetaChi_displacedLinePt hd hdhalf
  have hatom : ∀ i : Fin P, ∀ j : Fin N, Continuous (fun t : ℝ =>
      zetaChi (displacedLinePt d t) *
        Complex.exp ((((t *
          (Real.log (((i : ℕ) : ℝ) + 1) -
            Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
    intro i j
    exact hchi.mul (Complex.continuous_exp.comp
      (((Complex.continuous_ofReal.comp
        (continuous_id.mul continuous_const)).mul continuous_const)))
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChiDisplacedDirichletCross_eq_sum d P N c e t)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact intervalIntegral.integral_const_mul _ _
    · intro j hj
      exact ((hatom i j).intervalIntegrable a b).const_mul _
  · intro i hi
    have hs := IntervalIntegrable.sum (μ := volume)
      (Finset.univ : Finset (Fin N)) (fun j _ =>
        ((hatom i j).intervalIntegrable a b).const_mul (c i * e j))
    have heq : (∑ j : Fin N, fun x : ℝ => (c i * e j) *
        (zetaChi (displacedLinePt d x) *
          Complex.exp ((((x *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))) =
        fun x : ℝ => ∑ j : Fin N, (c i * e j) *
          (zetaChi (displacedLinePt d x) *
            Complex.exp ((((x *
              (Real.log (((i : ℕ) : ℝ) + 1) -
                Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
      funext x
      simp [Finset.sum_apply]
    rw [← heq]
    exact hs

/-- Factorized `ell^1` bound for a displaced finite Dirichlet cross on any dyadic subinterval. -/
theorem exists_norm_integral_zetaChiDisplacedDirichletCross_le_l1_subinterval
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T a b : ℝ, 4 ≤ T → T ≤ a → a ≤ b → b ≤ 2 * T →
      ∀ (P N : ℕ) (c : Fin P → ℂ) (e : Fin N → ℂ),
        ‖∫ t in a..b, zetaChiDisplacedDirichletCross d P N c e t‖ ≤
          (6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
            (∑ i : Fin P, ‖c i‖) * (∑ j : Fin N, ‖e j‖) := by
  obtain ⟨K, hK, hatom⟩ :=
    exists_norm_integral_zetaChi_displacedLinePt_mul_exp_le_subinterval
      hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T a b hT ha hab hb P N c e
  have hdhalf : d < 1 / 2 :=
    lt_of_le_of_lt (hdd₀.trans hd₀quarter) (by norm_num)
  rw [integral_zetaChiDisplacedDirichletCross_eq_sum_subinterval hd hdhalf]
  calc
    ‖∑ i : Fin P, ∑ j : Fin N, (c i * e j) *
        (∫ t in a..b, zetaChi (displacedLinePt d t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖
        ≤ ∑ i : Fin P, ∑ j : Fin N, ‖(c i * e j) *
            (∫ t in a..b, zetaChi (displacedLinePt d t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ := by
      calc
        _ ≤ ∑ i : Fin P, ‖∑ j : Fin N, (c i * e j) *
            (∫ t in a..b, zetaChi (displacedLinePt d t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ :=
          norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin P, ∑ j : Fin N,
        (‖c i‖ * ‖e j‖) *
          ((6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      gcongr
      simpa [mul_comm] using hatom d hd hdd₀ T a b hT ha hab hb
        (Real.log (((i : ℕ) : ℝ) + 1) - Real.log (((j : ℕ) : ℝ) + 1))
    _ = (6 / Real.sqrt (1 / (100 * T))) *
          ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
          (∑ i : Fin P, ‖c i‖) * (∑ j : Fin N, ‖e j‖) := by
      calc
        (∑ i : Fin P, ∑ j : Fin N,
            (‖c i‖ * ‖e j‖) *
              ((6 / Real.sqrt (1 / (100 * T))) *
                ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) =
          ∑ i : Fin P, (‖c i‖ * (∑ j : Fin N, ‖e j‖)) *
            ((6 / Real.sqrt (1 / (100 * T))) *
              ((K * (2 * T) ^ d) * (9 + 4 * Real.pi))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = _ := by
          rw [show (∑ i : Fin P, (‖c i‖ * (∑ j : Fin N, ‖e j‖)) *
              ((6 / Real.sqrt (1 / (100 * T))) *
                ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) =
            (∑ i : Fin P, ‖c i‖) *
              ((∑ j : Fin N, ‖e j‖) *
                ((6 / Real.sqrt (1 / (100 * T))) *
                  ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) by
            rw [← Finset.sum_mul]
            rw [← Finset.sum_mul]
            ring]
          ring

end

end RHTower
