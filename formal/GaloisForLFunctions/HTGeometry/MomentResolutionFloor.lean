/-
The resolution floor of a moment, and why `1/8` is distinguished.

For `k = 1, 2` the `2k`-th moment of `ζ` on the critical line has a genuine asymptotic formula with
error term `E_k(T)`.  A bound `E_k(T) ≪ T^θ` makes the short `2k`-th moment sharp on intervals of
length `T^θ`, and Sobolev then gives `μ(1/2) ≤ θ/(2k)`.  Since `θ` cannot be taken below the
`Ω`-result for `E_k`, each moment carries an intrinsic **resolution floor**

  `resolutionFloor k = θ_k / (2k)`,   `θ_k = (2k-1)/(2k+2)`,

`θ_k` being the conjecturally optimal exponent, sharp by `E(T) = Ω(T^{1/4})` for `k = 1` and
`E_2(T) = Ω(T^{1/2})` for `k = 2`.

The floor equals `1/8` at `k = 1` **and** at `k = 2`, and is strictly smaller for every `k > 2`.
This is an exact algebraic fact rather than a coincidence:

  `resolutionFloor k ≥ 1/8  ⟺  8(2k-1) ≥ 2k(2k+2)  ⟺  (k-1)(k-2) ≤ 0  ⟺  1 ≤ k ≤ 2`,

so the two indices at which the floor attains `1/8` are exactly the roots of `k² - 3k + 2`, and
exactly the two indices at which an asymptotic formula is known.  The floor tends to `0`, so the
moment hierarchy's conjectural resolution does reach the Lindelöf prediction; what stops it is the
absence of asymptotic formulas for `k ≥ 3`, not the value `1/8`.

The module is source-independent: it is arithmetic of the floor function.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Field

open Filter Topology

namespace HTGeometry

/-- The conjecturally optimal error exponent for the `2k`-th moment, `θ_k = (2k-1)/(2k+2)`;
sharp at `k = 1` (`E(T) = Ω(T^{1/4})`) and at `k = 2` (`E₂(T) = Ω(T^{1/2})`). -/
noncomputable def momentErrorExponent (k : ℝ) : ℝ := (2*k - 1) / (2*k + 2)

/-- The resolution floor of the `2k`-th moment: the smallest pointwise exponent derivable from it
even with its error term evaluated optimally. -/
noncomputable def resolutionFloor (k : ℝ) : ℝ := momentErrorExponent k / (2*k)

theorem momentErrorExponent_one : momentErrorExponent 1 = 1/4 := by
  unfold momentErrorExponent; norm_num

theorem momentErrorExponent_two : momentErrorExponent 2 = 1/2 := by
  unfold momentErrorExponent; norm_num

theorem resolutionFloor_one : resolutionFloor 1 = 1/8 := by
  unfold resolutionFloor momentErrorExponent; norm_num

theorem resolutionFloor_two : resolutionFloor 2 = 1/8 := by
  unfold resolutionFloor momentErrorExponent; norm_num

theorem resolutionFloor_three : resolutionFloor 3 = 5/48 := by
  unfold resolutionFloor momentErrorExponent; norm_num

theorem resolutionFloor_four : resolutionFloor 4 = 7/80 := by
  unfold resolutionFloor momentErrorExponent; norm_num

/-- **The pivot is exactly the double root.**  The resolution floor reaches `1/8` precisely on
`[1,2]`, because `8(2k-1) - 2k(2k+2) = -4(k-1)(k-2)`.  The two indices where it *equals* `1/8` are
the roots `k = 1, 2` — exactly the two moments of `ζ` with a known asymptotic formula. -/
theorem resolutionFloor_ge_eighth_iff {k : ℝ} (hk : 0 < k) :
    1/8 ≤ resolutionFloor k ↔ 1 ≤ k ∧ k ≤ 2 := by
  have h2k : (0:ℝ) < 2*k := by linarith
  have hden : (0:ℝ) < 2*k + 2 := by linarith
  unfold resolutionFloor momentErrorExponent
  rw [div_div, le_div_iff₀ (by positivity : (0:ℝ) < (2*k + 2) * (2*k))]
  constructor
  · intro h
    have hfac : (k - 1) * (k - 2) ≤ 0 := by nlinarith [h]
    constructor
    · nlinarith [hfac, hk]
    · nlinarith [hfac, hk]
  · rintro ⟨h1, h2⟩
    nlinarith [h1, h2, hk]

/-- The exact factorisation behind the previous theorem. -/
theorem eighth_gap_factorisation (k : ℝ) :
    8 * (2*k - 1) - 2*k*(2*k + 2) = -4 * (k - 1) * (k - 2) := by ring

/-- **Strictly below the pivot beyond `k = 2`.** -/
theorem resolutionFloor_lt_eighth {k : ℝ} (hk : 2 < k) : resolutionFloor k < 1/8 := by
  have hk0 : (0:ℝ) < k := by linarith
  by_contra h
  rw [not_lt] at h
  exact absurd ((resolutionFloor_ge_eighth_iff hk0).mp h).2 (by linarith)

/-- The floor tends to `0`, so the conjectural resolution of the moment hierarchy does reach the
Lindelöf prediction; the obstruction is the absence of asymptotics for `k ≥ 3`. -/
theorem resolutionFloor_tendsto_zero :
    Tendsto resolutionFloor atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℝ => 1/(2*k)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := (1:ℝ)) (f := atTop (α := ℝ))).div_atTop
      (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with k hk
    unfold resolutionFloor momentErrorExponent
    apply div_nonneg
    · apply div_nonneg <;> linarith
    · linarith
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with k hk
    unfold resolutionFloor momentErrorExponent
    rw [div_div, div_le_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith


section IndependentSignsModel

/-- The moment-error exponent predicted by the **independent-signs model**: modelling the
`k`-ary divisor-correlation errors `Δ_k(M,h)` at their conjectured size `M^{1-1/k}` with signs
uncorrelated across the shift `h`, the off-diagonal error of the `2k`-th moment is
`(1/M)(∑_h K(h)^(2 : ℕ))^{1/2} M^{1-1/k} ≍ T^{k/4}` at `M = T^{k/2}`. -/
noncomputable def modelErrorExponent (k : ℝ) : ℝ := k/4

/-- **The unification.**  The model exponent `k/4` and the conjectured true exponent
`θ_k = (2k-1)/(2k+2)` differ by exactly `(k-1)(k-2)/(4(k+1))`. -/
theorem model_sub_conjecture (k : ℝ) (hk : k + 1 ≠ 0) :
    modelErrorExponent k - momentErrorExponent k = (k-1)*(k-2)/(4*(k+1)) := by
  unfold modelErrorExponent momentErrorExponent
  have h2 : 2*k + 2 = 2*(k+1) := by ring
  rw [h2]
  field_simp
  ring

/-- **Correlations are required for every `k > 2`.**  For `k ≥ 2` the conjectured true error
exponent is at most the independent-signs prediction, with equality **only** at `k = 2`.  The gap
`(k-1)(k-2)/(4(k+1))` is the strength of the correlation among the `Δ_k(M,h)` across shifts that the
conjectured truth demands. -/
theorem conjecture_le_model {k : ℝ} (hk : 2 ≤ k) :
    momentErrorExponent k ≤ modelErrorExponent k := by
  have hpos : (0:ℝ) < 4*(k+1) := by linarith
  rw [← sub_nonneg, model_sub_conjecture k (by linarith), le_div_iff₀ hpos]
  nlinarith [hk]

theorem conjecture_lt_model {k : ℝ} (hk : 2 < k) :
    momentErrorExponent k < modelErrorExponent k := by
  have hpos : (0:ℝ) < 4*(k+1) := by linarith
  rw [← sub_pos, model_sub_conjecture k (by linarith), lt_div_iff₀ hpos]
  nlinarith [hk]

/-- Conversely the model **under**-predicts on `[1,2]`: the two exponents agree exactly at the roots
`k = 1, 2`, which are exactly the two indices at which the moment of `ζ` has a known asymptotic. -/
theorem model_le_conjecture_iff {k : ℝ} (hk : 0 < k) :
    modelErrorExponent k ≤ momentErrorExponent k ↔ 1 ≤ k ∧ k ≤ 2 := by
  have hpos : (0:ℝ) < 4*(k+1) := by linarith
  rw [← sub_nonneg, ← neg_sub, model_sub_conjecture k (by linarith), neg_nonneg,
    div_le_iff₀ hpos]
  constructor
  · intro h
    have hfac : (k-1)*(k-2) ≤ 0 := by nlinarith [h]
    constructor <;> nlinarith [hfac, hk]
  · rintro ⟨h1, h2⟩
    nlinarith [h1, h2]

/-- The two statements the campaign kept meeting are the same computation: `1/8` is the model's
resolution floor `(k/4)/(2k)`, and the true floor `θ_k/(2k)` attains it exactly on `[1,2]`. -/
theorem model_floor_is_eighth {k : ℝ} (hk : 0 < k) : modelErrorExponent k / (2*k) = 1/8 := by
  unfold modelErrorExponent
  field_simp
  ring

end IndependentSignsModel


section CorrelationErrorHeuristics

/-- The **"square of the ordinary divisor error"** heuristic for the `k`-ary correlation error:
`Δ_k(x) ≍ x^{(k-1)/(2k)}`, so its square has exponent `(k-1)/k`.  This is Ivić's conjectured
`Ω(x^{1-1/k})`. -/
noncomputable def squaredDivisorExponent (k : ℝ) : ℝ := (k - 1) / k

/-- The **random / square-root-of-the-number-of-terms** heuristic: exponent `1/2`, independent of
`k`.  This is Conrey–Gonek's `O(x^{1/2+ε})`. -/
noncomputable def randomExponent : ℝ := 1/2

/-- **The two heuristics coincide exactly at `k = 2`.**  This is why the case where the answer is
known — Motohashi's `Ω(x^{1/2})` for the binary correlation — cannot discriminate between them, and
why extrapolating from `k = 2` is ambiguous. -/
theorem heuristics_agree_iff {k : ℝ} (hk : 0 < k) :
    squaredDivisorExponent k = randomExponent ↔ k = 2 := by
  unfold squaredDivisorExponent randomExponent
  rw [div_eq_div_iff (by linarith) (by norm_num : (2:ℝ) ≠ 0)]
  constructor <;> intro h <;> linarith

/-- For `k > 2` the squared-divisor heuristic is strictly larger, so the two conjectures genuinely
conflict there; the gap is `(k-2)/(2k)`. -/
theorem heuristics_gap (k : ℝ) (hk : 0 < k) :
    squaredDivisorExponent k - randomExponent = (k - 2)/(2*k) := by
  unfold squaredDivisorExponent randomExponent
  field_simp
  ring

theorem squaredDivisor_gt_random {k : ℝ} (hk : 2 < k) :
    randomExponent < squaredDivisorExponent k := by
  have hk0 : (0:ℝ) < k := by linarith
  rw [← sub_pos, heuristics_gap k hk0]
  apply div_pos <;> linarith

end CorrelationErrorHeuristics

end HTGeometry
