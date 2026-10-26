import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheLambdaRingOfTheScalingSurface

/-!
# The first gauge-charged window off the edge

The odd-sector positivity of Weil's functional on `[−A, A]`, `A = 181/500`, is the first window
theorem that meets a prime: `2A > log 2`. Its Liouville twin flips the atom at `2`
(`λ(2)Λ(2) = −log 2`), and the corpus certificate gives
`W_λ(F) ≥ (1/1000)∫F² + √2 log 2 · a(F)` with the atom `a = Re(k(log 2) + k(−log 2))`,
`k = F ⋆ F̃` (`re_weilFullFunctional_liouvilleTwist_odd_window`). The question (the report's W8) is
what happens when `a < 0`.

* **The atom lives on the edge** (`abs_atom_le_edge`). The correlation `k(±log 2)` only sees pairs
  `u, u ∓ log 2` that both lie in `[−A, A]`, hence both in the edge strips
  `E = {log 2 − A ≤ |x| ≤ A}` of width `2A − log 2 ≈ 0.031`. By `|bc| ≤ (b² + c²)/2` and translation
  invariance, `|a| ≤ 2 ∫_E F²`.
* **The twin off the edge** (`re_weilFullFunctional_liouvilleTwist_ge_sub_edge`,
  `re_weilFullFunctional_liouvilleTwist_nonneg_of_edge_le`). For every odd `C²` test supported in
  `[−A, A]`, `W_λ(F) ≥ (1/1000)∫F² − 2√2 log 2 ∫_E F²`; so the Liouville twin is Weil-positive on
  every test whose mass in the edge strips is at most `1/1961` of its total mass.

So the first gauge-charged window can separate `ζ` from its Liouville twin only on tests that put
more than `1/1961` of their mass within `0.031` of the window's edge; on all other tests the twin is
positive as well. W8 is reduced to an edge-concentrated eigenvalue problem.
-/

open MeasureTheory Set
open GaloisForLFunctions.RHTower RHTower Zeta23
open GaloisForLFunctions.SquareRootThreshold (liouvilleTwistedVonMangoldt
  re_weilFullFunctional_liouvilleTwist_odd_window)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The edge strips `{log 2 − 181/500 ≤ |x|}` of the window. -/
def windowEdge : Set ℝ := {x | Real.log 2 - 181 / 500 ≤ |x|}

theorem measurableSet_windowEdge : MeasurableSet windowEdge :=
  (isClosed_le continuous_const continuous_abs).measurableSet

/-- The edge mass density `1_E F²`. -/
def edgeDensity (F : ℝ → ℝ) : ℝ → ℝ := windowEdge.indicator fun x => F x ^ 2

theorem edgeDensity_nonneg (F : ℝ → ℝ) (x : ℝ) : 0 ≤ edgeDensity F x :=
  indicator_nonneg (fun _ _ => sq_nonneg _) x

theorem log_two_sub_window_pos : 0 < Real.log 2 - 181 / 500 := by
  have := Real.log_two_gt_d9; norm_num at this ⊢; linarith

/-- On the support overlap both points lie in the edge: `|F(u)F(v)| ≤ (1_E F²(u) + 1_E F²(v))/2`
whenever `|u − v| = log 2`. -/
theorem abs_mul_le_edge {F : ℝ → ℝ} (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) {u v : ℝ}
    (huv : |u - v| = Real.log 2) :
    |F u * F v| ≤ (edgeDensity F u + edgeDensity F v) / 2 := by
  have h0 := edgeDensity_nonneg F u
  have h1 := edgeDensity_nonneg F v
  by_cases hu : F u = 0
  · rw [hu, zero_mul, abs_zero]; linarith
  by_cases hv : F v = 0
  · rw [hv, mul_zero, abs_zero]; linarith
  have hu' : |u| ≤ 181 / 500 := not_lt.mp fun h => hu (hsupp u h)
  have hv' : |v| ≤ 181 / 500 := not_lt.mp fun h => hv (hsupp v h)
  -- both points are at distance `≥ log 2 − A` from the origin
  -- `log 2 = |u − v| ≤ |u| + |v|`
  have htri : Real.log 2 ≤ |u| + |v| := by
    have := abs_add_le u (-v)
    rw [← sub_eq_add_neg, abs_neg, huv] at this
    exact this
  have hEu : u ∈ windowEdge := by
    show Real.log 2 - 181 / 500 ≤ |u|
    linarith
  have hEv : v ∈ windowEdge := by
    show Real.log 2 - 181 / 500 ≤ |v|
    linarith
  rw [edgeDensity, indicator_of_mem hEu, indicator_of_mem hEv, abs_mul]
  nlinarith [sq_nonneg (|F u| - |F v|), sq_abs (F u), sq_abs (F v)]

theorem integrable_edgeDensity {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable (edgeDensity F) := by
  have hc : HasCompactSupport fun x => F x ^ 2 :=
    hFc.mono fun x hx h0 => hx (by simp [h0])
  have h2 : Integrable fun x => F x ^ 2 := (hF.pow 2).integrable_of_hasCompactSupport hc
  unfold edgeDensity
  exact h2.indicator measurableSet_windowEdge

/-- `|∫ F(u) F(u − t)| ≤ ∫_E F²` for `|t| = log 2`. -/
theorem abs_integral_shift_le_edge {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) {t : ℝ} (ht : |t| = Real.log 2) :
    |∫ u, F u * F (u - t)| ≤ ∫ u, edgeDensity F u := by
  have hE := integrable_edgeDensity hF hFc
  have hg : Integrable fun u => (edgeDensity F u + edgeDensity F (u - t)) / 2 :=
    (hE.add (hE.comp_sub_right t)).div_const 2
  have hle := norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs]
    exact abs_mul_le_edge hsupp (by rw [sub_sub_cancel, ht]))
  rw [Real.norm_eq_abs] at hle
  refine hle.trans (le_of_eq ?_)
  rw [integral_div, integral_add hE (hE.comp_sub_right t), integral_sub_right_eq_self]
  ring

/-- **The atom lives on the edge**: `|Re(k(log 2) + k(−log 2))| ≤ 2 ∫_E F²`. -/
theorem abs_atom_le_edge {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    |(EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
        EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re| ≤
      2 * ∫ u, edgeDensity F u := by
  have h1 : EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) =
      ((∫ u, F u * F (u - Real.log 2) : ℝ) : ℂ) :=
    ArithmeticCastelnuovoSeveri.weilTest_ofReal F F _
  have h2 : EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2) =
      ((∫ u, F u * F (u - -Real.log 2) : ℝ) : ℂ) :=
    ArithmeticCastelnuovoSeveri.weilTest_ofReal F F _
  have hl : |Real.log 2| = Real.log 2 := abs_of_pos (Real.log_pos (by norm_num))
  rw [h1, h2, Complex.add_re, Complex.ofReal_re, Complex.ofReal_re]
  have a1 := abs_integral_shift_le_edge hF hFc hsupp (t := Real.log 2) hl
  have a2 := abs_integral_shift_le_edge hF hFc hsupp (t := -Real.log 2) (by rw [abs_neg, hl])
  refine (abs_add_le _ _).trans ?_
  linarith

/-- **The Liouville twin off the edge**: `W_λ(F) ≥ (1/1000)∫F² − 2√2 log 2 ∫_E F²`. -/
theorem re_weilFullFunctional_liouvilleTwist_ge_sub_edge {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0) :
    1 / 1000 * (∫ x, F x ^ 2) - 2 * Real.sqrt 2 * Real.log 2 * ∫ u, edgeDensity F u ≤
      (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  have hcert := re_weilFullFunctional_liouvilleTwist_odd_window hF hFc hodd hsupp
  have hatom := abs_atom_le_edge hF.continuous hFc hsupp
  have hc : 0 ≤ Real.sqrt 2 * Real.log 2 :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg (by norm_num))
  set a := (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (Real.log 2) +
    EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)) (-Real.log 2)).re
  have hneg : -(2 * ∫ u, edgeDensity F u) ≤ a := (abs_le.mp hatom).1
  nlinarith [mul_le_mul_of_nonneg_left hneg hc]

/-- **The twin is positive off the edge**: if at most `1/1961` of the mass of `F` lies in the edge
strips, the Liouville-twisted Weil functional is nonnegative at `F`. -/
theorem re_weilFullFunctional_liouvilleTwist_nonneg_of_edge_le {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ x, 181 / 500 < |x| → F x = 0)
    (hedge : 1961 * ∫ u, edgeDensity F u ≤ ∫ x, F x ^ 2) :
    0 ≤ (weilFullFunctional liouvilleTwistedVonMangoldt
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by
  refine le_trans ?_ (re_weilFullFunctional_liouvilleTwist_ge_sub_edge hF hFc hodd hsupp)
  have hE : 0 ≤ ∫ u, edgeDensity F u := integral_nonneg (edgeDensity_nonneg F)
  -- `2√2 log 2 < 1.961`
  have hs : Real.sqrt 2 < 1.4143 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconst : 2 * Real.sqrt 2 * Real.log 2 ≤ 1.961 := by
    have := mul_lt_mul'' hs hl (Real.sqrt_nonneg 2) hl0.le
    norm_num at this ⊢
    linarith
  nlinarith [mul_le_mul_of_nonneg_right hconst hE]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
