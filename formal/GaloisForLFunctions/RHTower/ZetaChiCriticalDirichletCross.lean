import GaloisForLFunctions.RHTower.ZetaChiCriticalLineOscillatoryIntegral
import GaloisForLFunctions.RHTower.Sieve.DirichletPairing

open Complex MeasureTheory Set

namespace RHTower

noncomputable section

/-- Critical-line chi cross of one positive- and one negative-frequency Dirichlet polynomial. -/
def zetaChiCriticalDirichletCross
    (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (t : ℝ) : ℂ :=
  zetaChi (linePt t) * (Sieve.dirPoly P a t * Sieve.dirPoly N b (-t))

theorem zetaChiCriticalDirichletCross_eq_sum
    (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (t : ℝ) :
    zetaChiCriticalDirichletCross P N a b t =
      ∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (zetaChi (linePt t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
  unfold zetaChiCriticalDirichletCross Sieve.dirPoly
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

theorem integral_zetaChiCriticalDirichletCross_eq_sum
    (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) (T : ℝ) :
    (∫ t in T..(2 * T), zetaChiCriticalDirichletCross P N a b t) =
      ∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (∫ t in T..(2 * T), zetaChi (linePt t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
  have hatom : ∀ i : Fin P, ∀ j : Fin N, Continuous (fun t : ℝ =>
      zetaChi (linePt t) *
        Complex.exp ((((t *
          (Real.log (((i : ℕ) : ℝ) + 1) -
            Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
    intro i j
    let ω := Real.log (((i : ℕ) : ℝ) + 1) - Real.log (((j : ℕ) : ℝ) + 1)
    have heq : (fun t : ℝ => zetaChi (linePt t) *
        Complex.exp ((((t *
          (Real.log (((i : ℕ) : ℝ) + 1) -
            Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) =
        fun t : ℝ => Complex.exp
          (((zetaChiCriticalTwistPhase ω t : ℝ) : ℂ) * I) := by
      funext t
      simpa [ω, mul_comm] using zetaChi_line_mul_exp_eq_exp_twistPhase ω t
    rw [heq]
    have hphase : Continuous (zetaChiCriticalTwistPhase ω) :=
      continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_zetaChiCriticalTwistPhase ω t).continuousAt
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp hphase).mul continuous_const)
  rw [intervalIntegral.integral_congr (fun t _ =>
    zetaChiCriticalDirichletCross_eq_sum P N a b t)]
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
        (zetaChi (linePt x) *
          Complex.exp ((((x *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))) =
        fun x : ℝ => ∑ j : Fin N, (a i * b j) *
          (zetaChi (linePt x) *
            Complex.exp ((((x *
              (Real.log (((i : ℕ) : ℝ) + 1) -
                Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I)) := by
      funext x
      simp [Finset.sum_apply]
    rw [← heq]
    exact hs

/-- Full finite direct/reflected cross bound after summing all stationary frequencies. -/
theorem norm_integral_zetaChiCriticalDirichletCross_le
    {T : ℝ} (hT : 4 ≤ T) (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) :
    ‖∫ t in T..(2 * T), zetaChiCriticalDirichletCross P N a b t‖ ≤
      ∑ i : Fin P, ∑ j : Fin N,
        (‖a i‖ * ‖b j‖) * (6 / Real.sqrt (1 / (100 * T))) := by
  rw [integral_zetaChiCriticalDirichletCross_eq_sum]
  calc
    ‖∑ i : Fin P, ∑ j : Fin N, (a i * b j) *
        (∫ t in T..(2 * T), zetaChi (linePt t) *
          Complex.exp ((((t *
            (Real.log (((i : ℕ) : ℝ) + 1) -
              Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖
        ≤ ∑ i : Fin P, ‖∑ j : Fin N, (a i * b j) *
            (∫ t in T..(2 * T), zetaChi (linePt t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ :=
          norm_sum_le _ _
    _ ≤ ∑ i : Fin P, ∑ j : Fin N, ‖(a i * b j) *
            (∫ t in T..(2 * T), zetaChi (linePt t) *
              Complex.exp ((((t *
                (Real.log (((i : ℕ) : ℝ) + 1) -
                  Real.log (((j : ℕ) : ℝ) + 1)) : ℝ) : ℂ)) * I))‖ := by
          exact Finset.sum_le_sum fun i _ => norm_sum_le _ _
    _ ≤ ∑ i : Fin P, ∑ j : Fin N,
        (‖a i‖ * ‖b j‖) * (6 / Real.sqrt (1 / (100 * T))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_mul]
      gcongr
      simpa [mul_comm] using norm_integral_zetaChi_line_mul_exp_le hT
        (Real.log (((i : ℕ) : ℝ) + 1) - Real.log (((j : ℕ) : ℝ) + 1))

/-- Factorized `ell^1` form of the full critical direct/reflected cross estimate. -/
theorem norm_integral_zetaChiCriticalDirichletCross_le_l1
    {T : ℝ} (hT : 4 ≤ T) (P N : ℕ) (a : Fin P → ℂ) (b : Fin N → ℂ) :
    ‖∫ t in T..(2 * T), zetaChiCriticalDirichletCross P N a b t‖ ≤
      (6 / Real.sqrt (1 / (100 * T))) *
        (∑ i : Fin P, ‖a i‖) * (∑ j : Fin N, ‖b j‖) := by
  refine (norm_integral_zetaChiCriticalDirichletCross_le hT P N a b).trans_eq ?_
  calc
    (∑ i : Fin P, ∑ j : Fin N,
        (‖a i‖ * ‖b j‖) * (6 / Real.sqrt (1 / (100 * T)))) =
      ∑ i : Fin P, (‖a i‖ * (∑ j : Fin N, ‖b j‖)) *
        (6 / Real.sqrt (1 / (100 * T))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ = (6 / Real.sqrt (1 / (100 * T))) *
        (∑ i : Fin P, ‖a i‖) * (∑ j : Fin N, ‖b j‖) := by
      rw [show (∑ i : Fin P, (‖a i‖ * (∑ j : Fin N, ‖b j‖)) *
          (6 / Real.sqrt (1 / (100 * T)))) =
        (∑ i : Fin P, ‖a i‖) *
          ((∑ j : Fin N, ‖b j‖) * (6 / Real.sqrt (1 / (100 * T)))) by
        rw [← Finset.sum_mul]
        rw [← Finset.sum_mul]
        ring]
      ring

end

end RHTower
