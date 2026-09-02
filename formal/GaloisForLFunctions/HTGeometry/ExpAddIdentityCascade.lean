import GaloisForLFunctions.HTGeometry.PairCascadeOrder
import GaloisForLFunctions.HTGeometry.PoincareRecession
import GaloisForLFunctions.HTGeometry.TranscendentalEntireClosure
import GaloisForLFunctions.HTGeometry.CompositionDepth

/-!
# Exact differential order of iterated `exp z + z`

The map `z ↦ exp z + z` is the smallest nonautonomous example in the Newton-corner card.  Its
first-order equation is linear in the output,

`f' = f - z + 1`.

The polynomial two-coordinate cascade theorem therefore proves, without an asymptotic branch
choice, that its `n`-fold iterate has minimal algebraic-differential order exactly `n`.
-/

open GaloisForLFunctions
open Filter

namespace GaloisForLFunctions.HTGeometry

/-- The nonautonomous first-order map `z ↦ exp z + z`. -/
noncomputable def expAddId (z : ℂ) : ℂ := Complex.exp z + z

theorem differentiable_expAddId : Differentiable ℂ expAddId := by
  exact Complex.differentiable_exp.add differentiable_id

theorem transcendentalEntire_expAddId : TranscendentalEntire expAddId := by
  change TranscendentalEntire (fun z => Complex.exp z + z)
  simpa only [Polynomial.eval_X] using
    transcendentalEntire_add_polynomial transcendentalEntire_exp Polynomial.X

/-- The exact nonautonomous first-order equation `f' = f - z + 1`. -/
theorem deriv_expAddId (z : ℂ) :
    deriv expAddId z = (1 : Polynomial ℂ).eval z * expAddId z
      + (-Polynomial.X + 1 : Polynomial ℂ).eval z := by
  have h := (Complex.hasDerivAt_exp z).add (hasDerivAt_id' z)
  change deriv (Complex.exp + fun w : ℂ => w) z =
    (1 : Polynomial ℂ).eval z * (Complex.exp z + z)
      + (-Polynomial.X + 1 : Polynomial ℂ).eval z
  rw [h.deriv]
  simp only [Polynomial.eval_one, Polynomial.eval_add, Polynomial.eval_neg,
    Polynomial.eval_X, one_mul]
  ring

/-- A cascade of `m+1` copies of `expAddId` has differential order exactly `m+1`. -/
theorem exactDifferentialOrder_expAddIdCascade (m : ℕ) :
    ExactDifferentialOrder (entireCascade (fun _ => expAddId) (m + 1)) (m + 1) := by
  exact exactDifferentialOrder_linearCascade
    (h := fun _ => expAddId) (a := fun _ => 1) (b := fun _ => -Polynomial.X + 1)
    (fun _ => transcendentalEntire_expAddId) (fun _ z => deriv_expAddId z)
    (fun _ => one_ne_zero) m

/-- The `m+1`-fold iterate of `z ↦ exp z + z` has differential order exactly `m+1`. -/
theorem exactDifferentialOrder_expAddId_iterate (m : ℕ) :
    ExactDifferentialOrder (expAddId^[m + 1]) (m + 1) := by
  rw [← entireCascade_const]
  exact exactDifferentialOrder_expAddIdCascade m

/-- The exponential term gives `expAddId` positive lower order. -/
theorem positiveLowerOrder_expAddId : PositiveLowerOrder expAddId := by
  refine ⟨1, one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  refine ⟨(r : ℂ), ?_, ?_⟩
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  · rw [iterExp_succ, iterExp_zero, Real.rpow_one]
    change Real.exp r ≤ ‖Complex.exp (r : ℂ) + (r : ℂ)‖
    have hvalue : Complex.exp (r : ℂ) + (r : ℂ) = ((Real.exp r + r : ℝ) : ℂ) := by
      rw [← Complex.ofReal_exp]
      push_cast
      rfl
    rw [hvalue, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · linarith
    · positivity

/-- The transcendental entire map `expAddId` is nonconstant. -/
theorem nonconstant_expAddId : ∃ z₁ z₂ : ℂ, expAddId z₁ ≠ expAddId z₂ :=
  exists_ne_of_transcendentalEntire transcendentalEntire_expAddId

/-- A length-`n` `expAddId` cascade has growth height at most `n`. -/
theorem exists_bound_entireCascade_expAddId (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ r →
      ‖entireCascade (fun _ => expAddId) n z‖ ≤ iterExp n (r ^ C) := by
  induction n with
  | zero =>
      refine ⟨1, one_pos, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr z hz
      rw [entireCascade_zero, id_eq, iterExp_zero, Real.rpow_one]
      exact hz
  | succ n ih =>
      obtain ⟨C, hC, hev⟩ := ih
      refine ⟨C + 1, by linarith, ?_⟩
      have hX0 : ∀ᶠ r : ℝ in atTop, (0 : ℝ) ≤ iterExp n (r ^ C) :=
        (tendsto_iterExp_rpow n hC).eventually_ge_atTop 0
      have hadd := eventually_iterExp_add_le n hC (Real.log 2)
      filter_upwards [hev, hX0, hadd] with r hr hX0r hadd z hz
      set W : ℂ := entireCascade (fun _ => expAddId) n z
      set X : ℝ := iterExp n (r ^ C)
      have hW : ‖W‖ ≤ X := hr z hz
      have hXexp : X ≤ Real.exp X := by
        linarith [Real.add_one_le_exp X]
      rw [entireCascade_succ, iterExp_succ]
      change ‖Complex.exp W + W‖ ≤ Real.exp (iterExp n (r ^ (C + 1)))
      calc
        ‖Complex.exp W + W‖ ≤ ‖Complex.exp W‖ + ‖W‖ := norm_add_le _ _
        _ = Real.exp W.re + ‖W‖ := by rw [Complex.norm_exp]
        _ ≤ Real.exp ‖W‖ + ‖W‖ := by
          gcongr
          exact Complex.re_le_norm W
        _ ≤ Real.exp X + X := by gcongr
        _ ≤ 2 * Real.exp X := by linarith
        _ = Real.exp (X + Real.log 2) := by
          rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
          ring
        _ ≤ Real.exp (iterExp n (r ^ (C + 1))) := Real.exp_le_exp.mpr hadd

/-- Growth-height form of the `expAddId` cascade bound. -/
theorem growthHeightAtMost_entireCascade_expAddId (n : ℕ) :
    GrowthHeightAtMost (entireCascade (fun _ => expAddId) n) n := by
  obtain ⟨C, -, hev⟩ := exists_bound_entireCascade_expAddId n
  exact ⟨C, hev⟩

/-- The positive-lower-order composition depth of the `m+1`-fold iterate is exactly `m+1`. -/
theorem compositionDepth_expAddId_iterate (m : ℕ) :
    CompositionDepthAtLeast (expAddId^[m + 1]) (m + 1) ∧
      ¬ CompositionDepthAtLeast (expAddId^[m + 1]) (m + 2) := by
  rw [← entireCascade_const]
  constructor
  · exact ⟨m + 1, fun _ => expAddId, Finset.range (m + 1),
      fun _ => differentiable_expAddId, fun _ => nonconstant_expAddId,
      Finset.Subset.rfl, fun _ _ => positiveLowerOrder_expAddId,
      by simp, fun _ => rfl⟩
  · intro hdepth
    exact not_growthHeightAtLeast_succ_of_atMost
      (growthHeightAtMost_entireCascade_expAddId (m + 1))
      (growthHeightAtLeast_of_compositionDepth hdepth)

/-- Exact differential order and exact positive-lower-order composition depth of `exp z + z`. -/
theorem exactOrder_and_compositionDepth_expAddId_iterate (m : ℕ) :
    ExactDifferentialOrder (expAddId^[m + 1]) (m + 1) ∧
      CompositionDepthAtLeast (expAddId^[m + 1]) (m + 1) ∧
      ¬ CompositionDepthAtLeast (expAddId^[m + 1]) (m + 2) :=
  ⟨exactDifferentialOrder_expAddId_iterate m,
    (compositionDepth_expAddId_iterate m).1,
    (compositionDepth_expAddId_iterate m).2⟩

end GaloisForLFunctions.HTGeometry
