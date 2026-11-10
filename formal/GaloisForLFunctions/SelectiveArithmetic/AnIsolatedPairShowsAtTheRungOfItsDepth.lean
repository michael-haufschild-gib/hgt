import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# An isolated pair shows at the rung of its depth

The second one-structure fake of the conductor ladder has the functional equation and no Euler
product: the doubled lattice of zeros on the line with the density of a conductor `q`,
`L = ½ log q`, and one reflected pair of depth `δ` (corpus: `isolatedPairConfig`). Its Weil form
at aperture `a ≤ L/2` is nonnegative exactly when `sinh(2δa)/δ ≤ 2L + 2a`.

On the ladder `a = κ log log q` this reads:

* **Below the rung of the depth** (`isolatedPair_nonneg_of_rung`): if `2δκ < 1`, then for
  `log q` large the configuration is Weil-nonnegative at every aperture `a ≤ κ log log q`.
* **Above the rung of the depth** (`isolatedPair_neg_of_rung`): if `2δκ > 1`, then for `log q`
  large it has a negative direction at every aperture `κ log log q ≤ a ≤ ¼ log q`.

So a pair of depth `δ` shows at the rung `κ = 1/(2δ)`: the rate at which a saving
`n^{1/2 + δ}` in the contacts pays for the sign on the prime side
(`exists_cancellation_margin`). For `δ = ½`, a pair at `0` and `1`, the rung is `κ = 1`: the
functional equation without the Euler product fails at the aperture `log log q`, where the Euler
product without the functional equation, the Liouville twist, fails too. Beyond the trivial
aperture a statement must use both structures.
-/

open Filter Topology Set
open Zeta23

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open SquareRootThreshold

/-- For `c > 0`, eventually `B ≤ c log x` and `κ log x ≤ x/4`. -/
theorem eventually_log_budget {c : ℝ} (hc : 0 < c) (B κ : ℝ) :
    ∀ᶠ x : ℝ in atTop, B ≤ c * Real.log x ∧ κ * Real.log x ≤ x / 4 ∧ 1 ≤ x := by
  have h1 : ∀ᶠ x : ℝ in atTop, B / c ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (B / c)
  have h2 : (fun x : ℝ => Real.log x) =o[atTop] (id : ℝ → ℝ) := Real.isLittleO_log_id_atTop
  have h3 := (h2.const_mul_left κ).def (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h1, h3, eventually_ge_atTop (1 : ℝ)] with x hx1 hx3 hx
  refine ⟨?_, ?_, hx⟩
  · have := (div_le_iff₀ hc).mp hx1
    linarith
  · rw [Real.norm_eq_abs, id, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)]
      at hx3
    have := (le_abs_self _).trans hx3
    linarith

/-- **Below the rung of its depth an isolated pair is invisible.** If `2δκ < 1`, then for `x`
large the lattice of density `L = x/2` with one pair of depth `δ` is Weil-nonnegative at every
aperture `0 < a ≤ κ log x`. -/
theorem isolatedPair_nonneg_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hκ : 2 * δ * κ < 1) :
    ∃ M₀ : ℝ, ∀ (x : ℝ) (hx : 0 < x / 2), M₀ ≤ x → ∀ (γ₀ a : ℝ), 0 < a →
      a ≤ κ * Real.log x → ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
        0 ≤ ((isolatedPairConfig hx hδ hδ' γ₀).W f f).re := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_log_budget (sub_pos.mpr hκ) (-Real.log (2 * δ)) κ)
  refine ⟨M₀, fun x hx hxM γ₀ a ha hak f hf hfs => ?_⟩
  obtain ⟨h1, h2, hx1⟩ := hM₀ x hxM
  have hx0 : 0 < x := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  refine isolatedPairConfig_weil_nonneg_of_le_log hx hδ hδ' γ₀ ha (by linarith) ?_ f hf hfs
  -- `2δa ≤ 2δκ log x ≤ log(2δ) + log x = log(4δ · x/2)`
  have hlog : Real.log (4 * δ * (x / 2)) = Real.log (2 * δ) + Real.log x := by
    rw [show 4 * δ * (x / 2) = 2 * δ * x by ring,
      Real.log_mul (by positivity) hx0.ne']
  rw [hlog]
  have h3 : 2 * δ * a ≤ 2 * δ * (κ * Real.log x) :=
    mul_le_mul_of_nonneg_left hak (by positivity)
  nlinarith

/-- **Above the rung of its depth an isolated pair is visible.** If `2δκ > 1`, then for `x`
large the lattice of density `L = x/2` with one pair of depth `δ` has a negative direction at
every aperture `κ log x ≤ a ≤ x/4`. -/
theorem isolatedPair_neg_of_rung {δ κ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hκ : 1 < 2 * δ * κ) :
    ∃ M₀ : ℝ, ∀ (x : ℝ) (hx : 0 < x / 2), M₀ ≤ x → ∀ (γ₀ a : ℝ), κ * Real.log x ≤ a →
      a ≤ x / 4 → ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
        ((isolatedPairConfig hx hδ hδ' γ₀).W f f).re < 0 := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp
    (eventually_log_budget (sub_pos.mpr hκ) (Real.log 4) 0)
  refine ⟨max M₀ 2, fun x hx hxM γ₀ a hak hax => ?_⟩
  obtain ⟨h1, -, hx1⟩ := hM₀ x ((le_max_left _ _).trans hxM)
  have hx2 : 2 ≤ x := (le_max_right _ _).trans hxM
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hκ0 : 0 < κ := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hδ.le (neg_nonneg.mpr h)]
  have ha : 0 < a := lt_of_lt_of_le (mul_pos hκ0 hlogx) hak
  refine exists_re_W_isolatedPairConfig_neg_of_log_le hx hδ hδ' γ₀ ha (by linarith) ?_
  -- `log(4δ(x/2 + a) + 2) ≤ log(4x) ≤ 2δκ log x ≤ 2δa`
  have hle : 4 * δ * (x / 2 + a) + 2 ≤ 4 * x := by nlinarith
  have hlog4 : Real.log (4 * x) = Real.log 4 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  have h2 : Real.log (4 * δ * (x / 2 + a) + 2) ≤ Real.log 4 + Real.log x := by
    rw [← hlog4]
    exact Real.log_le_log (by positivity) hle
  have h3 : 2 * δ * (κ * Real.log x) ≤ 2 * δ * a :=
    mul_le_mul_of_nonneg_left hak (by positivity)
  nlinarith

end GaloisForLFunctions.SelectiveArithmetic
