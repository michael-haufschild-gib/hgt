import GaloisForLFunctions.RHTower.Suzuki.SuzukiObserverJetFormation
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorOneSided

/-!
# Positive observer curvature and the signed Abel upper bound

The completed Riesz clock has strictly positive discrete curvature, bounded above
by `3 / (8 * sqrt (j + 1))`. Absolute summability of the completed source charge
controls the mass and drift boundary terms by a constant times the aperture.
Consequently only the positive parts of the residual history enter the remaining
one-sided upper estimate. A linear bound for that positive-history action implies
RH; this module does not prove that growth bound.
-/

open Set Filter Topology
open scoped BigOperators
noncomputable section

namespace GaloisForLFunctions.HTGeometry


theorem observerJetClockRealSecondDeriv_eq_cancelled {x : ℝ} (hx : 0 < x) :
    observerJetClockRealSecondDeriv x =
      3 * (3 * Real.sqrt x * Real.sqrt (x + 1) - (2 * x + 1)) /
        (4 * Real.sqrt x * Real.sqrt (x + 1) * (Real.sqrt x + Real.sqrt (x + 1))) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hab : a + b ≠ 0 := by positivity
  have hxp : x + 1 ≠ 0 := by linarith
  unfold observerJetClockRealSecondDeriv observerJetSqrtGap observerJetSqrtGapDeriv
    observerJetSqrtGapSecondDeriv
  change 2 * (b - a) + 2 * (2 * x + 1) * (1 / (2 * b) - 1 / (2 * a)) +
    x * (x + 1) * ((1 / (x * a) - 1 / ((x + 1) * b)) / 4) =
    3 * (3 * a * b - (2 * x + 1)) / (4 * a * b * (a + b))
  field_simp [hx.ne', hxp, ha.ne', hb.ne', hab]
  ring_nf
  rw [ha2, hb2]
  rw [show a ^ 3 = a * a ^ 2 by ring, show b ^ 3 = b * b ^ 2 by ring, ha2, hb2]
  ring

theorem observerJetClockRealSecondDeriv_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < observerJetClockRealSecondDeriv x := by
  have hx0 : 0 < x := by linarith
  have ha : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hb : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  have ha2 := Real.sq_sqrt hx0.le
  have hb2 := Real.sq_sqrt (show 0 ≤ x + 1 by linarith)
  have hlt : Real.sqrt x < Real.sqrt (x + 1) := by nlinarith
  have hp : x < Real.sqrt x * Real.sqrt (x + 1) := by
    nlinarith [mul_pos ha (sub_pos.mpr hlt)]
  rw [observerJetClockRealSecondDeriv_eq_cancelled hx0]
  apply div_pos
  · nlinarith
  · positivity

theorem observerJetClockRealSecondDeriv_le_three_eighths {x : ℝ} (hx : 0 < x) :
    observerJetClockRealSecondDeriv x ≤ 3 / (8 * Real.sqrt x) := by
  let a := Real.sqrt x
  let b := Real.sqrt (x + 1)
  have ha : 0 < a := Real.sqrt_pos.mpr hx
  have hb : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a ^ 2 = x := Real.sq_sqrt hx.le
  have hb2 : b ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have hp : a * b ≤ x + 1 / 2 := by nlinarith [sq_nonneg (a - b)]
  rw [observerJetClockRealSecondDeriv_eq_cancelled hx]
  change 3 * (3 * a * b - (2 * x + 1)) / (4 * a * b * (a + b)) ≤ 3 / (8 * a)
  apply (div_le_iff₀ (by positivity : 0 < 4 * a * b * (a + b))).2
  have heq : 3 / (8 * a) * (4 * a * b * (a + b)) = (3 / 2 : ℝ) * b * (a + b) := by
    field_simp [ha.ne']
    ring
  rw [heq]
  nlinarith

theorem observerJetClockReal_secondDifference_eq_secondDeriv {x : ℝ} (hx : 0 < x) :
    ∃ d : ℝ, x < d ∧ d < x + 2 ∧
      observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) + observerJetClockReal x =
        observerJetClockRealSecondDeriv d := by
  let g : ℝ → ℝ := fun y => observerJetClockReal (y + 1) - observerJetClockReal y
  let g' : ℝ → ℝ := fun y => observerJetClockRealDeriv (y + 1) - observerJetClockRealDeriv y
  have hgAt (y : ℝ) (hy : 0 < y) : HasDerivAt g (g' y) y := by
    have hshift : HasDerivAt (fun z : ℝ => z + 1) 1 y := (hasDerivAt_id y).add_const 1
    have h := ((hasDerivAt_observerJetClockReal (by linarith : 0 < y + 1)).comp y hshift).sub
      (hasDerivAt_observerJetClockReal hy)
    apply (h.congr_deriv (by simp only [g', mul_one])).congr_of_eventuallyEq
    filter_upwards with z
    simp only [g, Function.comp_def, Pi.sub_apply]
  have hgder : ∀ y ∈ Ioo x (x + 1), HasDerivAt g (g' y) y :=
    fun y hy => hgAt y (hx.trans hy.1)
  have hgcont : ContinuousOn g (Icc x (x + 1)) :=
    fun y hy => (hgAt y (hx.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcSlope⟩ := exists_hasDerivAt_eq_slope g g'
    (by linarith : x < x + 1) hgcont hgder
  have hc0 : 0 < c := hx.trans hc.1
  have hf'der : ∀ y ∈ Ioo c (c + 1),
      HasDerivAt observerJetClockRealDeriv (observerJetClockRealSecondDeriv y) y :=
    fun y hy => hasDerivAt_observerJetClockRealDeriv (hc0.trans hy.1)
  have hf'cont : ContinuousOn observerJetClockRealDeriv (Icc c (c + 1)) :=
    fun y hy => (hasDerivAt_observerJetClockRealDeriv
      (hc0.trans_le hy.1)).continuousAt.continuousWithinAt
  obtain ⟨d, hd, hdSlope⟩ := exists_hasDerivAt_eq_slope
    observerJetClockRealDeriv observerJetClockRealSecondDeriv
    (by linarith : c < c + 1) hf'cont hf'der
  refine ⟨d, hc.1.trans hd.1, by linarith [hc.2, hd.2], ?_⟩
  dsimp [g, g'] at hcSlope
  simp only [add_sub_cancel_left, div_one] at hcSlope hdSlope
  calc
    observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) + observerJetClockReal x =
        observerJetClockRealDeriv (c + 1) - observerJetClockRealDeriv c := by
      rw [hcSlope]
      ring
    _ = observerJetClockRealSecondDeriv d := hdSlope.symm

theorem observerJetClockReal_secondDifference_pos_le {x : ℝ} (hx : 1 ≤ x) :
    0 < observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) + observerJetClockReal x ∧
    observerJetClockReal (x + 2) - 2 * observerJetClockReal (x + 1) + observerJetClockReal x ≤
      3 / (8 * Real.sqrt x) := by
  obtain ⟨d, hdx, _, heq⟩ := observerJetClockReal_secondDifference_eq_secondDeriv
    (lt_of_lt_of_le zero_lt_one hx)
  have hd1 := hx.trans hdx.le
  rw [heq]
  refine ⟨observerJetClockRealSecondDeriv_pos hd1,
    (observerJetClockRealSecondDeriv_le_three_eighths (lt_of_lt_of_le zero_lt_one hd1)).trans ?_⟩
  gcongr

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower GaloisForLFunctions.HTGeometry

theorem observerJetCurvature_completedRieszHarmonicClockRatio_pos (j : ℕ) :
    0 < observerJetCurvature completedRieszHarmonicClockRatio j := by
  rw [observerJetCurvature, completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal]
  push_cast
  have h := (observerJetClockReal_secondDifference_pos_le (x := (j : ℝ) + 1)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))).1
  simpa only [show (j : ℝ) + 2 + 1 = (j : ℝ) + 1 + 2 by ring] using h

theorem observerJetCurvature_completedRieszHarmonicClockRatio_le_three_eighths (j : ℕ) :
    observerJetCurvature completedRieszHarmonicClockRatio j ≤ 3 / (8 * Real.sqrt (j + 1 : ℕ)) := by
  rw [observerJetCurvature, completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal,
    completedRieszHarmonicClockRatio_eq_observerJetClockReal]
  push_cast
  have h := (observerJetClockReal_secondDifference_pos_le (x := (j : ℝ) + 1)
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))).2
  simpa only [show (j : ℝ) + 2 + 1 = (j : ℝ) + 1 + 2 by ring] using h

def completedSourceObserverJetPositiveHistoryAction (M : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (M - 3), max (completedSourceObserverJetHistory M j) 0 /
    Real.sqrt (j + 1 : ℕ)

theorem mobiusDivisorSquareRootAbelMoment_le_boundary_add_positiveHistory
    {M : ℕ} (hM : 3 ≤ M) :
    mobiusDivisorSquareRootAbelMoment M ≤
      completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
      completedSourceObserverJetDrift M *
        (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) +
      (3 / 8 : ℝ) * completedSourceObserverJetPositiveHistoryAction M := by
  rw [mobiusDivisorSquareRootAbelMoment_eq_completedSourceObserverJet hM,
    completedSourceObserverJetPositiveHistoryAction, Finset.mul_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j _
  have hk0 := (observerJetCurvature_completedRieszHarmonicClockRatio_pos j).le
  have hku := observerJetCurvature_completedRieszHarmonicClockRatio_le_three_eighths j
  calc
    completedSourceObserverJetHistory M j * observerJetCurvature completedRieszHarmonicClockRatio j ≤
        max (completedSourceObserverJetHistory M j) 0 *
          observerJetCurvature completedRieszHarmonicClockRatio j :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hk0
    _ ≤ max (completedSourceObserverJetHistory M j) 0 * (3 / (8 * Real.sqrt (j + 1 : ℕ))) :=
      mul_le_mul_of_nonneg_left hku (le_max_right _ _)
    _ = (3 / 8 : ℝ) * (max (completedSourceObserverJetHistory M j) 0 / Real.sqrt (j + 1 : ℕ)) := by ring

theorem exists_completedSourceObserverJetBoundary_linear_upper :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 +
        completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) ≤ B * M := by
  let q := completedPrimePolarGammaHarmonicCharge
  let S : ℝ := ∑' k : ℕ, |q k|
  have hq : Summable q := summable_completedPrimePolarGammaHarmonicCharge
  have habs : Summable (fun k => |q k|) := by simpa only [Real.norm_eq_abs] using hq.norm
  have hS : 0 ≤ S := tsum_nonneg (fun _ => abs_nonneg _)
  have hfinite (N : ℕ) : (∑ k ∈ Finset.range (N + 1), |q k|) ≤ S :=
    habs.sum_le_tsum _ (fun _ _ => abs_nonneg _)
  have hmass (M : ℕ) : |completedSourceObserverJetMass M| ≤ S := by
    change |∑ k ∈ Finset.range (M - 2 + 1), q k| ≤ S
    exact (Finset.abs_sum_le_sum_abs _ _).trans (hfinite (M - 2))
  have hdrift (M : ℕ) : |completedSourceObserverJetDrift M| ≤ (M : ℝ) * S := by
    change |∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * q k| ≤ (M : ℝ) * S
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ k ∈ Finset.range (M - 2 + 1), |(k : ℝ) * q k|) =
          ∑ k ∈ Finset.range (M - 2 + 1), (k : ℝ) * |q k| := by
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      _ ≤ ∑ k ∈ Finset.range (M - 2 + 1), (M : ℝ) * |q k| := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact_mod_cast (show k ≤ M by have := Finset.mem_range.mp hk; omega)
      _ = (M : ℝ) * ∑ k ∈ Finset.range (M - 2 + 1), |q k| := by rw [Finset.mul_sum]
      _ ≤ (M : ℝ) * S := mul_le_mul_of_nonneg_left (hfinite (M - 2)) (Nat.cast_nonneg M)
  refine ⟨S * (|completedRieszHarmonicClockRatio 0| +
    |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0|),
    by positivity, fun M hM => ?_⟩
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hSM : S ≤ (M : ℝ) * S := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hMone hS
  have hmassTerm : completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0 ≤
      (M : ℝ) * S * |completedRieszHarmonicClockRatio 0| := by
    calc
      _ ≤ |completedSourceObserverJetMass M * completedRieszHarmonicClockRatio 0| := le_abs_self _
      _ = |completedSourceObserverJetMass M| * |completedRieszHarmonicClockRatio 0| := abs_mul _ _
      _ ≤ S * |completedRieszHarmonicClockRatio 0| :=
        mul_le_mul_of_nonneg_right (hmass M) (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hSM (abs_nonneg _)
  have hdriftTerm : completedSourceObserverJetDrift M *
      (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0) ≤
      (M : ℝ) * S * |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| := by
    calc
      _ ≤ |completedSourceObserverJetDrift M *
          (completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0)| := le_abs_self _
      _ = |completedSourceObserverJetDrift M| *
          |completedRieszHarmonicClockRatio 1 - completedRieszHarmonicClockRatio 0| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (hdrift M) (abs_nonneg _)
  nlinarith only [hmassTerm, hdriftTerm]

theorem exists_mobiusDivisorSquareRootAbel_upper_positiveHistory :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, 3 ≤ M →
      mobiusDivisorSquareRootAbelMoment M ≤ B * M +
        (3 / 8 : ℝ) * completedSourceObserverJetPositiveHistoryAction M := by
  obtain ⟨B, hB, hboundary⟩ := exists_completedSourceObserverJetBoundary_linear_upper
  refine ⟨B, hB, fun M hM => ?_⟩
  linarith [mobiusDivisorSquareRootAbelMoment_le_boundary_add_positiveHistory hM, hboundary M hM]

theorem riemannHypothesis_of_completedSourceObserverJetPositiveHistory_linear
    {C : ℝ} (hC : ∀ M : ℕ, 3 ≤ M →
      completedSourceObserverJetPositiveHistoryAction M ≤ C * M) : RiemannHypothesis := by
  obtain ⟨B, _, hB⟩ := exists_mobiusDivisorSquareRootAbel_upper_positiveHistory
  apply riemannHypothesis_iff_mobiusDivisorSquareRootAbel_eventually_boundedAbove.mpr
  refine ⟨B + (3 / 8 : ℝ) * C, 3, fun M hM => ?_⟩
  have hM3 : 3 ≤ M := by omega
  have hMR : (0 : ℝ) < M := by positivity
  apply (div_le_iff₀ hMR).2
  nlinarith only [hB M hM3, hC M hM3]

end GaloisForLFunctions.RHTower
