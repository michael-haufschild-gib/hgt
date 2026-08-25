import GaloisForLFunctions.RHTower.ZetaChiDisplacedCriticalRatioOscillatoryIntegral
import GaloisForLFunctions.RHTower.Sieve.DirichletPairing

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Displaced-line chi cross of one positive- and one negative-frequency Dirichlet polynomial. -/
def zetaChiDisplacedDirichletCross
    (d : ℝ) (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) * (Sieve.dirPoly P a t * Sieve.dirPoly N b (-t))

theorem zetaChiDisplacedDirichletCross_eq_sum
    (d : ℝ) (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (t : ℝ) :
    zetaChiDisplacedDirichletCross d P N a b t =
      ∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (zetaChi (displacedLinePt d t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
  unfold zetaChiDisplacedDirichletCross Sieve.dirPoly
  rw [Finset.sum_mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hphase :
      Complex.exp (((t * Real.log ((i : ℕ) + 1) : ℝ) : ℂ) * I) *
          Complex.exp (((-t * Real.log ((j : ℕ) + 1) : ℝ) : ℂ) * I) =
        Complex.exp ((((t *
          (Real.log (((i : ℕ) : ℝ) + 1) -
            Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hphase]
  ring

theorem integral_zetaChiDisplacedDirichletCross_eq_sum
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2)
    (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (T : ℝ) :
    (∫ t in T..(2 * T), zetaChiDisplacedDirichletCross d P N a b t) =
      ∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (∫ t in T..(2 * T), zetaChi (displacedLinePt d t) *
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
    zetaChiDisplacedDirichletCross_eq_sum d P N a b t)]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j hj
      exact intervalIntegral.integral_const_mul _ _
    · intro j hj
      exact ((hatom i j).intervalIntegrable T (2 * T)).const_mul _
  · intro i hi
    have hs := IntervalIntegrable.sum (μ := volume)
      (Finset.univ : Finset (Fin N)) (fun j _ =>
        ((hatom i j).intervalIntegrable T (2 * T)).const_mul (a i * b j))
    have heq : (∑ j : Fin N, fun x : ℝ => (a i * b j) *
        (zetaChi (displacedLinePt d x) *
          Complex.exp ((((x *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))) =
        fun x : ℝ => ∑ j : Fin N, (a i * b j) *
          (zetaChi (displacedLinePt d x) *
            Complex.exp ((((x *
              (Real.log (((i : ℕ) : ℝ) + 1) -
                Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
      funext x
      simp [Finset.sum_apply]
    rw [← heq]
    exact hs

/-- Factorized `ell^1` bound for the full displaced direct/reflected finite cross. -/
theorem exists_norm_integral_zetaChiDisplacedDirichletCross_le_l1
    {d₀ : ℝ} (hd₀0 : 0 ≤ d₀) (hd₀quarter : d₀ ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ d : ℝ, 0 < d → d ≤ d₀ →
      ∀ T : ℝ, 4 ≤ T →
      ∀ (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ),
        ‖∫ t in T..(2 * T), zetaChiDisplacedDirichletCross d P N a b t‖ ≤
          (6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
            (∑ i : Fin P, ‖a i‖) * (∑ j : Fin N, ‖b j‖) := by
  obtain ⟨K, hK, hatom⟩ :=
    exists_norm_integral_zetaChi_displacedLinePt_mul_exp_le_dyadic hd₀0 hd₀quarter
  refine ⟨K, hK, ?_⟩
  intro d hd hdd₀ T hT P N a b
  have hdhalf : d < 1 / 2 :=
    lt_of_le_of_lt (hdd₀.trans hd₀quarter) (by norm_num)
  rw [integral_zetaChiDisplacedDirichletCross_eq_sum hd hdhalf]
  calc
    ‖∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (∫ t in T..(2 * T), zetaChi (displacedLinePt d t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖
        ≤ ∑ i : Fin P, ∑ j : Fin N, ‖(a i * b j) *
            (∫ t in T..(2 * T), zetaChi (displacedLinePt d t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ := by
      calc
        _ ≤ ∑ i : Fin P, ‖∑ j : Fin N, (a i * b j) *
            (∫ t in T..(2 * T), zetaChi (displacedLinePt d t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ := norm_sum_le _ _
        _ ≤ _ := Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin P, ∑ j : Fin N,
        (‖a i‖ * ‖b j‖) *
          ((6 / Real.sqrt (1 / (100 * T))) *
            ((K * (2 * T) ^ d) * (9 + 4 * Real.pi))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      gcongr
      simpa [mul_comm] using hatom d hd hdd₀ T hT
        (Real.log (((i : ℕ) : ℝ) + 1) - Real.log (((j : ℕ) : ℝ) + 1))
    _ = (6 / Real.sqrt (1 / (100 * T))) *
          ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)) *
          (∑ i : Fin P, ‖a i‖) * (∑ j : Fin N, ‖b j‖) := by
      calc
        (∑ i : Fin P, ∑ j : Fin N,
            (‖a i‖ * ‖b j‖) *
              ((6 / Real.sqrt (1 / (100 * T))) *
                ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) =
          ∑ i : Fin P, (‖a i‖ * (∑ j : Fin N, ‖b j‖)) *
            ((6 / Real.sqrt (1 / (100 * T))) *
              ((K * (2 * T) ^ d) * (9 + 4 * Real.pi))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = _ := by
          rw [show (∑ i : Fin P, (‖a i‖ * (∑ j : Fin N, ‖b j‖)) *
              ((6 / Real.sqrt (1 / (100 * T))) *
                ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) =
            (∑ i : Fin P, ‖a i‖) *
              ((∑ j : Fin N, ‖b j‖) *
                ((6 / Real.sqrt (1 / (100 * T))) *
                  ((K * (2 * T) ^ d) * (9 + 4 * Real.pi)))) by
            rw [← Finset.sum_mul]
            rw [← Finset.sum_mul]
            ring]
          ring

end

end RHTower
