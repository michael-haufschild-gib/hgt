import GaloisForLFunctions.RHTower.FZZCigarPunctureWeightedSourceClassification
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDampingSemigroup
import GaloisForLFunctions.HTGeometry.FZZCigarScatteringSpectralAsymmetry

/-!
# Protected FZZ continuum-delay point-mode no-go

The exact protected cigar continuum delay is the positive-half-line Bose kernel

`v(x) = 1 / (exp x - 1)`.

This file inserts that literal corpus source—not a fitted local germ—into the universal scalar
puncture equation.  At every real target energy `E`, the canonical state energy dominates

`c(E) x⁻²` on `(0,1)` away from the null point `x=E`, where
`c(E) = 1 / (4 (|E|+1)²) > 0`.

Consequently the canonical state is never `L²`, and the protected delay source creates no scalar
puncture point mode at any real energy.  The no-go does not exclude an interacting Hamiltonian,
singular domain extension, generalized resonance, or a coefficient-faithful source modified by
winding-condensate backreaction.

`[NEW] [NO-GO] [QUANTITATIVE RIGIDITY] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- Positive-half-line extension of the exact protected FZZ continuum delay. -/
def fzzCigarProtectedContinuumDelaySource (t : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator
    (fun u => ((HTGeometry.fzzCigarContinuumDelay u : ℝ) : ℂ)) t

/-- On physical positive delay, source is exactly cigar Bose delay `(exp t - 1)⁻¹`. -/
theorem fzzCigarProtectedContinuumDelaySource_eq {t : ℝ} (ht : 0 < t) :
    fzzCigarProtectedContinuumDelaySource t =
      ((HTGeometry.fzzCigarContinuumDelay t : ℝ) : ℂ) := by
  simp [fzzCigarProtectedContinuumDelaySource, ht]

/-- Exact norm of canonical protected-delay state away from target pole. -/
theorem norm_fzzCigarProtectedContinuumDelayResolventState
    (E : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxE : x ≠ E) :
    ‖fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource x‖ =
      1 / ((Real.exp x - 1) * |x - E|) := by
  have hd : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1)
  have hxe : 0 < |x - E| := abs_pos.mpr (sub_ne_zero.mpr hxE)
  rw [fzzPunctureWeightedResolventState, fzzCigarProtectedContinuumDelaySource,
    indicator_of_mem (mem_Ioi.mpr hx.1), HTGeometry.fzzCigarContinuumDelay,
    norm_div, norm_neg, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hd)]
  rw [Real.norm_eq_abs]
  field_simp

/-- Positive target-dependent coefficient in inverse-square energy obstruction. -/
def fzzCigarProtectedDelayPoleConstant (E : ℝ) : ℝ :=
  (4 * (|E| + 1) ^ 2)⁻¹

/-- Protected-delay pole coefficient is strictly positive at every target energy. -/
theorem fzzCigarProtectedDelayPoleConstant_pos (E : ℝ) :
    0 < fzzCigarProtectedDelayPoleConstant E := by
  unfold fzzCigarProtectedDelayPoleConstant
  positivity

/--
Quantitative obstruction: canonical state energy dominates positive inverse-square pole throughout
physical unit delay interval, except at null resonant singleton.
-/
theorem fzzCigarProtectedContinuumDelayStateEnergy_lower
    (E : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxE : x ≠ E) :
    fzzCigarProtectedDelayPoleConstant E * x ^ (-2 : ℝ) ≤
      ‖fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource x‖ ^ 2 := by
  have hd : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx.1)
  have hExp := Real.abs_exp_sub_one_le (x := x) (by
    rw [abs_of_pos hx.1]
    exact hx.2.le)
  rw [abs_of_pos hd, abs_of_pos hx.1] at hExp
  have hdist : |x - E| ≤ |E| + 1 := by
    calc
      |x - E| ≤ |x| + |E| := abs_sub x E
      _ = x + |E| := by rw [abs_of_pos hx.1]
      _ ≤ 1 + |E| := by linarith [hx.2]
      _ = |E| + 1 := by ring
  have hdistPos : 0 < |x - E| := abs_pos.mpr (sub_ne_zero.mpr hxE)
  have hApos : 0 < |E| + 1 := by positivity
  have hprod : (Real.exp x - 1) * |x - E| ≤ (2 * x) * (|E| + 1) :=
    mul_le_mul hExp hdist hdistPos.le (mul_pos (by norm_num) hx.1).le
  have hnormLower : 1 / ((2 * x) * (|E| + 1)) ≤
      ‖fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource x‖ := by
    rw [norm_fzzCigarProtectedContinuumDelayResolventState E hx hxE]
    exact one_div_le_one_div_of_le (mul_pos hd hdistPos) hprod
  have hleft : 0 ≤ 1 / ((2 * x) * (|E| + 1)) :=
    (one_div_pos.mpr (mul_pos (mul_pos (by norm_num) hx.1) hApos)).le
  calc
    fzzCigarProtectedDelayPoleConstant E * x ^ (-2 : ℝ) =
        (1 / ((2 * x) * (|E| + 1))) ^ 2 := by
      rw [Real.rpow_neg (le_of_lt hx.1)]
      norm_num [fzzCigarProtectedDelayPoleConstant, Real.rpow_two]
      field_simp
      ring
    _ ≤ ‖fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource x‖ ^ 2 :=
      (sq_le_sq₀ hleft (norm_nonneg _)).mpr hnormLower

/-- Canonical state of exact protected FZZ delay source is never square-integrable. -/
theorem fzzCigarProtectedContinuumDelayState_not_memLp (E : ℝ) :
    ¬ MemLp
      (fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource)
      2 volume := by
  intro hmem
  have henergy : Integrable
      (fun x : ℝ =>
        ‖fzzPunctureWeightedResolventState E fzzCigarProtectedContinuumDelaySource x‖ ^ 2) :=
    hmem.integrable_norm_pow (by norm_num)
  have hscaled : IntegrableOn
      (fun x : ℝ => fzzCigarProtectedDelayPoleConstant E * x ^ (-2 : ℝ))
      (Ioo (0 : ℝ) 1) := by
    apply henergy.integrableOn.mono'
    · exact (continuousOn_const.mul
        (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable
          measurableSet_Ioo
    · filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae ((volume : Measure ℝ).ae_ne E)] with x hx hxE
      have hnonneg : 0 ≤ fzzCigarProtectedDelayPoleConstant E * x ^ (-2 : ℝ) :=
        mul_nonneg (fzzCigarProtectedDelayPoleConstant_pos E).le
          (Real.rpow_nonneg hx.1.le _)
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact fzzCigarProtectedContinuumDelayStateEnergy_lower E hx hxE
  have hc : fzzCigarProtectedDelayPoleConstant E ≠ 0 :=
    ne_of_gt (fzzCigarProtectedDelayPoleConstant_pos E)
  have hinverse : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ)) (Ioo (0 : ℝ) 1) := by
    have hmul := hscaled.const_mul (fzzCigarProtectedDelayPoleConstant E)⁻¹
    change Integrable (fun x : ℝ => x ^ (-2 : ℝ))
      (volume.restrict (Ioo (0 : ℝ) 1))
    simpa [hc] using hmul
  exact routeP_not_integrableOn_translated_inverseSquare 0 (by simpa using hinverse)

/-- Exact protected FZZ continuum delay creates no scalar `L²` puncture mode at any energy. -/
theorem not_FZZPunctureProtectedContinuumDelayPointMode (E : ℝ) :
    ¬ FZZPunctureWeightedSourcePointMode E fzzCigarProtectedContinuumDelaySource := by
  intro hmode
  exact fzzCigarProtectedContinuumDelayState_not_memLp E
    ((fzzPunctureWeightedSourcePointMode_iff E
      fzzCigarProtectedContinuumDelaySource).mp hmode).1

end

end RHTower
