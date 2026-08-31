import GaloisForLFunctions.HTGeometry.PolynomialMagnitudeBalance

/-!
# The proximity function of a polynomial composition

`log⁺‖p(y)‖` differs from `deg p · log⁺‖y‖` by a bounded amount: above by the `log⁺` of the sum of
the coefficient norms, below by a constant depending on the leading coefficient and the radius past
which the leading term dominates.  Averaging over a circle turns this into

```text
| m(r, p ∘ f) − deg p · m(r, f) | = O(1)
```

for every continuous `f`, with constants independent of the radius.  This is the elementary half of
Valiron's theorem on the characteristic of a polynomial in a meromorphic function; for entire `f`
the characteristic *is* the proximity, so it is the whole statement.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Real

/-- **`log⁺` of a polynomial value, above.**  `log⁺‖p(y)‖ ≤ deg p · log⁺‖y‖ + log⁺(∑‖coeff‖)`. -/
theorem posLog_norm_polyEval_le (p : ℂ[X]) (y : ℂ) :
    Real.posLog ‖p.eval y‖
      ≤ (p.natDegree : ℝ) * Real.posLog ‖y‖
        + Real.posLog (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) := by
  set B : ℝ := ∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖ with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => norm_nonneg _
  set m : ℝ := max 1 ‖y‖ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hm0 : (0 : ℝ) ≤ m := by linarith
  have hnorm : ‖p.eval y‖ ≤ B * m ^ p.natDegree := by
    rw [eval_eq_sum_range, hB, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    rw [norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    calc ‖y‖ ^ i ≤ m ^ i := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) i
      _ ≤ m ^ p.natDegree := pow_le_pow_right₀ hm1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  have hstep : Real.posLog ‖p.eval y‖ ≤ Real.posLog (B * m ^ p.natDegree) :=
    Real.posLog_le_posLog (norm_nonneg _) hnorm
  have hsplit : Real.posLog (B * m ^ p.natDegree)
      ≤ Real.posLog B + Real.posLog (m ^ p.natDegree) := Real.posLog_mul
  have hpow : Real.posLog (m ^ p.natDegree) = (p.natDegree : ℝ) * Real.posLog m :=
    Real.posLog_pow _ _
  have hmax : Real.posLog m = Real.posLog ‖y‖ := by
    rcases le_or_gt ‖y‖ 1 with hle | hgt
    · have : m = 1 := by rw [hm]; exact max_eq_left hle
      rw [this]
      have h1 : Real.posLog 1 = 0 := (Real.posLog_eq_zero_iff 1).mpr (by norm_num)
      have h2 : Real.posLog ‖y‖ = 0 := by
        refine (Real.posLog_eq_zero_iff _).mpr ?_
        rw [abs_of_nonneg (norm_nonneg y)]
        exact hle
      rw [h1, h2]
    · have : m = ‖y‖ := by rw [hm]; exact max_eq_right hgt.le
      rw [this]
  rw [hmax] at hpow
  linarith [hstep, hsplit, hpow]

/-- **`log⁺` of a polynomial value, below.**  Beyond a radius depending on the coefficients,
`log⁺‖p(y)‖ ≥ deg p · log⁺‖y‖ − C`. -/
theorem exists_le_posLog_norm_polyEval (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℂ,
      (p.natDegree : ℝ) * Real.posLog ‖y‖ - C ≤ Real.posLog ‖p.eval y‖ := by
  obtain ⟨R, hR1, hR⟩ := exists_le_norm_eval p hp
  have hlc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp)
  refine ⟨|Real.log (‖p.leadingCoeff‖ / 2)| + (p.natDegree : ℝ) * Real.log R, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
    have h2 : (0 : ℝ) ≤ |Real.log (‖p.leadingCoeff‖ / 2)| := abs_nonneg _
    positivity
  · intro y
    rcases le_or_gt R ‖y‖ with hge | hlt
    · have hy1 : (1 : ℝ) ≤ ‖y‖ := le_trans hR1 hge
      have hbound := hR y hge
      have hpos : (0 : ℝ) < ‖p.leadingCoeff‖ / 2 * ‖y‖ ^ p.natDegree := by
        have : (0 : ℝ) < ‖y‖ ^ p.natDegree := by positivity
        positivity
      have hlog : Real.log (‖p.leadingCoeff‖ / 2 * ‖y‖ ^ p.natDegree)
          ≤ Real.posLog ‖p.eval y‖ := by
        refine le_trans (Real.log_le_log hpos hbound) ?_
        rw [Real.posLog_def]
        simp only [Pi.sup_apply, Pi.zero_apply]
        exact le_max_right _ _
      have hexp : Real.log (‖p.leadingCoeff‖ / 2 * ‖y‖ ^ p.natDegree)
          = Real.log (‖p.leadingCoeff‖ / 2) + (p.natDegree : ℝ) * Real.log ‖y‖ := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
      have hposy : Real.posLog ‖y‖ = Real.log ‖y‖ := by
        refine Real.posLog_eq_log ?_
        rw [abs_of_nonneg (norm_nonneg y)]
        exact hy1
      have habs : -|Real.log (‖p.leadingCoeff‖ / 2)| ≤ Real.log (‖p.leadingCoeff‖ / 2) :=
        neg_abs_le _
      have hlogR : (0 : ℝ) ≤ (p.natDegree : ℝ) * Real.log R := by
        have : (0 : ℝ) ≤ Real.log R := Real.log_nonneg hR1
        positivity
      rw [hposy]
      linarith [hlog, hexp, habs, hlogR]
    · have hy : Real.posLog ‖y‖ ≤ Real.log R := by
        rcases le_or_gt ‖y‖ 1 with hle | hgt
        · have hz : Real.posLog ‖y‖ = 0 := by
            refine (Real.posLog_eq_zero_iff _).mpr ?_
            rw [abs_of_nonneg (norm_nonneg y)]
            exact hle
          rw [hz]
          exact Real.log_nonneg hR1
        · have hposy : Real.posLog ‖y‖ = Real.log ‖y‖ := by
            refine Real.posLog_eq_log ?_
            rw [abs_of_nonneg (norm_nonneg y)]
            exact hgt.le
          rw [hposy]
          exact Real.log_le_log (by linarith) hlt.le
      have hdeg : (p.natDegree : ℝ) * Real.posLog ‖y‖ ≤ (p.natDegree : ℝ) * Real.log R :=
        mul_le_mul_of_nonneg_left hy (Nat.cast_nonneg _)
      have hnn : (0 : ℝ) ≤ Real.posLog ‖p.eval y‖ := Real.posLog_nonneg
      have habs : (0 : ℝ) ≤ |Real.log (‖p.leadingCoeff‖ / 2)| := abs_nonneg _
      linarith

/-! ## The proximity function of a polynomial composition -/

open MeasureTheory

theorem circleIntegrable_posLog_norm_of_continuous {f : ℂ → ℂ} (hf : Continuous f) (c : ℂ) (r : ℝ) :
    CircleIntegrable (fun z => Real.posLog ‖f z‖) c r :=
  ((Real.continuous_posLog.comp (continuous_norm.comp hf)).comp
    (continuous_circleMap c r)).intervalIntegrable 0 (2 * Real.pi)

/-- **The proximity of `p ∘ f` is `deg p` times that of `f`, up to a constant.**  The upper half. -/
theorem proximity_comp_polynomial_le (p : ℂ[X]) {f : ℂ → ℂ} (hf : Continuous f) (r : ℝ) :
    ValueDistribution.proximity (fun z => p.eval (f z)) ⊤ r
      ≤ (p.natDegree : ℝ) * ValueDistribution.proximity f ⊤ r
        + Real.posLog (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) := by
  set C : ℝ := Real.posLog (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) with hC
  have hcomp : Continuous fun z => p.eval (f z) := p.continuous_aeval.comp hf
  have hint₁ : CircleIntegrable (fun z => Real.posLog ‖p.eval (f z)‖) 0 r :=
    circleIntegrable_posLog_norm_of_continuous hcomp 0 r
  have hintf : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 r :=
    circleIntegrable_posLog_norm_of_continuous hf 0 r
  have hintsmul : CircleIntegrable (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r := by
    exact ((continuous_const.mul
      (Real.continuous_posLog.comp (continuous_norm.comp hf))).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hintC : CircleIntegrable (fun _ : ℂ => C) 0 r := circleIntegrable_const C 0 r
  have hint₂ : CircleIntegrable
      (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + C) 0 r := hintsmul.add hintC
  have hle := circleAverage_mono hint₁ hint₂
    (fun z _ => posLog_norm_polyEval_le p (f z))
  have hsplit : circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + C) 0 r
      = (p.natDegree : ℝ) * circleAverage (fun z => Real.posLog ‖f z‖) 0 r + C := by
    have hadd : circleAverage
        ((fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) + fun _ : ℂ => C) 0 r
        = circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r
          + circleAverage (fun _ : ℂ => C) 0 r := circleAverage_add hintsmul hintC
    have hsm : circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r
        = (p.natDegree : ℝ) * circleAverage (fun z => Real.posLog ‖f z‖) 0 r := by
      simpa [smul_eq_mul] using
        circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (f := fun z => Real.posLog ‖f z‖)
          (c := (0 : ℂ)) (R := r) (a := (p.natDegree : ℝ))
    rw [show (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + C)
        = ((fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) + fun _ : ℂ => C) from rfl, hadd,
      hsm, circleAverage_const]
  rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]
  rw [hsplit] at hle
  exact hle

/-- **The proximity of `p ∘ f` is `deg p` times that of `f`, up to a constant.**  The lower half. -/
theorem exists_le_proximity_comp_polynomial (p : ℂ[X]) (hp : p ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f : ℂ → ℂ}, Continuous f → ∀ r : ℝ,
      (p.natDegree : ℝ) * ValueDistribution.proximity f ⊤ r - C
        ≤ ValueDistribution.proximity (fun z => p.eval (f z)) ⊤ r := by
  obtain ⟨C, hC0, hC⟩ := exists_le_posLog_norm_polyEval p hp
  refine ⟨C, hC0, ?_⟩
  intro f hf r
  have hcomp : Continuous fun z => p.eval (f z) := p.continuous_aeval.comp hf
  have hint₁ : CircleIntegrable (fun z => Real.posLog ‖p.eval (f z)‖) 0 r :=
    circleIntegrable_posLog_norm_of_continuous hcomp 0 r
  have hintf : CircleIntegrable (fun z => Real.posLog ‖f z‖) 0 r :=
    circleIntegrable_posLog_norm_of_continuous hf 0 r
  have hintsmul : CircleIntegrable (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r :=
    ((continuous_const.mul
      (Real.continuous_posLog.comp (continuous_norm.comp hf))).comp
      (continuous_circleMap 0 r)).intervalIntegrable 0 (2 * Real.pi)
  have hintC : CircleIntegrable (fun _ : ℂ => -C) 0 r := circleIntegrable_const (-C) 0 r
  have hint₂ : CircleIntegrable
      (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + -C) 0 r := hintsmul.add hintC
  have hle := circleAverage_mono hint₂ hint₁
    (fun z _ => by simpa [sub_eq_add_neg] using hC (f z))
  have hsplit : circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + -C) 0 r
      = (p.natDegree : ℝ) * circleAverage (fun z => Real.posLog ‖f z‖) 0 r + -C := by
    have hadd : circleAverage
        ((fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) + fun _ : ℂ => -C) 0 r
        = circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r
          + circleAverage (fun _ : ℂ => -C) 0 r := circleAverage_add hintsmul hintC
    have hsm : circleAverage (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) 0 r
        = (p.natDegree : ℝ) * circleAverage (fun z => Real.posLog ‖f z‖) 0 r := by
      simpa [smul_eq_mul] using
        circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (f := fun z => Real.posLog ‖f z‖)
          (c := (0 : ℂ)) (R := r) (a := (p.natDegree : ℝ))
    rw [show (fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖ + -C)
        = ((fun z => (p.natDegree : ℝ) * Real.posLog ‖f z‖) + fun _ : ℂ => -C) from rfl, hadd,
      hsm, circleAverage_const]
  rw [ValueDistribution.proximity_top, ValueDistribution.proximity_top]
  rw [hsplit] at hle
  linarith [hle]

end GaloisForLFunctions.HTGeometry
