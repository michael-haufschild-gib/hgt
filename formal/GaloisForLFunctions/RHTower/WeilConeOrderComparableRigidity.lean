import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# Order-comparable rigidity of the full Weil cone

Let `W` be the full Weil cone: weights `lam` whose Weil functional, with ζ's archimedean datum and
pole weight `1`, is nonnegative on every autocorrelation of a `C²` compactly supported test
(`WeilPositiveFull`).

**Theorem C.** If `lam ∈ W` and `lam − Λ` has constant sign on `n ≥ 2`, then `lam = Λ` there, and
RH holds (`eq_vonMangoldt_and_riemannHypothesis_of_constant_sign`).  Both directions are
unconditional: upward is the Riemann-kernel null-vector argument, downward the log-shift difference
test.

**Corollaries.**
* `riemannHypothesis_iff_exists_le` / `_exists_ge`: RH holds iff `W` meets `{lam ≤ Λ}` (resp.
  `{lam ≥ Λ}`), and each of these sets is then `{Λ}` on `n ≥ 2`.
* `eq_vonMangoldt_of_constant_sign_add_summable` (**constant sign up to a summable error**): if
  `lam − Λ = u₀ + e` on `n ≥ 2` with `u₀` of constant sign and `Σ |e(n)| n^{−1/2} < ∞`, then
  `lam = Λ`.  Upward the deficit, downward the excess, is dominated by `|e|`.
* `eq_vonMangoldt_of_ge_of_positiveOnNonnegCone` (**majorants give no freedom**): a majorant
  `lam ≥ Λ` that is nonnegative on the nonnegative cone is `Λ`.
* `infinite_setOf_gt_and_lt_of_ne`: a second point of `W` differs from `Λ` with both signs
  infinitely often.
-/

open Filter

namespace RHTower.WeilOrderComparable

noncomputable section

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-- A system agreeing with `Λ` on `n ≥ 2` forces RH once it is Weil-positive. -/
theorem riemannHypothesis_of_eqOn {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (heq : ∀ n, 2 ≤ n → lam n = Λ n) : RiemannHypothesis := by
  refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hc => ?_
  have := hW f hf hc
  rwa [weilFullFunctional_congr heq] at this

/-- **Theorem C, upward.** -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_ge {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hge : ∀ n, 2 ≤ n → (Λ n : ℝ) ≤ lam n) :
    (∀ n, 2 ≤ n → lam n = Λ n) ∧ RiemannHypothesis :=
  ⟨eq_vonMangoldt_of_weilPositiveFull_of_ge hW hge,
    riemannHypothesis_of_eqOn hW (eq_vonMangoldt_of_weilPositiveFull_of_ge hW hge)⟩

/-- **Theorem C, downward.**  A Weil-positive deletion `Λ − d`, `d ≥ 0`, is `Λ`. -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (Λ n : ℝ)) :
    (∀ n, 2 ≤ n → lam n = Λ n) ∧ RiemannHypothesis :=
  ⟨eq_vonMangoldt_of_weilPositiveFull_of_le hW hle,
    riemannHypothesis_of_eqOn hW (eq_vonMangoldt_of_weilPositiveFull_of_le hW hle)⟩

/-- **Theorem C.**  A Weil-positive system whose difference from `Λ` has constant sign on `n ≥ 2`
equals `Λ` there, and RH holds. -/
theorem eq_vonMangoldt_and_riemannHypothesis_of_constant_sign {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam)
    (hsign : (∀ n, 2 ≤ n → (Λ n : ℝ) ≤ lam n) ∨ ∀ n, 2 ≤ n → lam n ≤ (Λ n : ℝ)) :
    (∀ n, 2 ≤ n → lam n = Λ n) ∧ RiemannHypothesis :=
  hsign.elim (eq_vonMangoldt_and_riemannHypothesis_of_ge hW)
    (eq_vonMangoldt_and_riemannHypothesis_of_le hW)

/-- **Corollary.**  RH holds iff the Weil cone meets `{lam ≤ Λ}`; that set is then `{Λ}` on
`n ≥ 2`. -/
theorem riemannHypothesis_iff_exists_le :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∀ n, 2 ≤ n → lam n ≤ (Λ n : ℝ) :=
  ⟨fun hRH => ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, fun _ _ => le_rfl⟩,
    fun ⟨_, hW, hle⟩ => (eq_vonMangoldt_and_riemannHypothesis_of_le hW hle).2⟩

/-- **Corollary.**  RH holds iff the Weil cone meets `{lam ≥ Λ}`; that set is then `{Λ}` on
`n ≥ 2`. -/
theorem riemannHypothesis_iff_exists_ge :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∀ n, 2 ≤ n → (Λ n : ℝ) ≤ lam n :=
  ⟨fun hRH => ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, fun _ _ => le_rfl⟩,
    fun ⟨_, hW, hge⟩ => (eq_vonMangoldt_and_riemannHypothesis_of_ge hW hge).2⟩

/-- Each comparable part of the Weil cone is the single point `Λ` (on `n ≥ 2`) when nonempty,
and it contains `Λ` exactly under RH. -/
theorem comparable_parts_eq_singleton :
    (RiemannHypothesis ↔ WeilPositiveFull fun n => (Λ n : ℝ)) ∧
    (∀ lam : ℕ → ℝ, WeilPositiveFull lam →
      ((∀ n, 2 ≤ n → lam n ≤ (Λ n : ℝ)) ∨ ∀ n, 2 ≤ n → (Λ n : ℝ) ≤ lam n) →
        ∀ n, 2 ≤ n → lam n = Λ n) :=
  ⟨riemannHypothesis_iff_weilPositiveFull_vonMangoldt, fun _ hW h =>
    (eq_vonMangoldt_and_riemannHypothesis_of_constant_sign hW h.symm).1⟩

private theorem summable_of_dominated_eventually {f g : ℕ → ℝ} (hg : Summable g)
    (hf0 : ∀ n, 0 ≤ f n) (hfg : ∀ n, 2 ≤ n → f n ≤ g n) : Summable f :=
  Summable.of_norm_bounded_eventually hg (by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop 2] with n hn
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 n)]
    exact hfg n hn)

/-- **Constant sign up to a summable error.**  If `lam − Λ = u₀ + e` on `n ≥ 2`, where `u₀` has
constant sign and `Σ |e(n)| n^{−1/2} < ∞`, then `lam = Λ` on `n ≥ 2`. -/
theorem eq_vonMangoldt_of_constant_sign_add_summable {lam u₀ e : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (hdec : ∀ n, 2 ≤ n → lam n - Λ n = u₀ n + e n)
    (hsign : (∀ n, 2 ≤ n → 0 ≤ u₀ n) ∨ ∀ n, 2 ≤ n → u₀ n ≤ 0)
    (he : Summable fun n => |e n| / Real.sqrt n) :
    ∀ n, 2 ≤ n → lam n = Λ n := by
  rcases hsign with hpos | hneg
  · refine eq_vonMangoldt_of_weilPositiveFull_of_summable_deficit hW
      (summable_of_dominated_eventually he
        (fun n => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) fun n hn => ?_)
    refine div_le_div_of_nonneg_right (max_le ?_ (abs_nonneg _)) (Real.sqrt_nonneg _)
    have := hdec n hn
    have := hpos n hn
    linarith [neg_abs_le (e n)]
  · refine WeilExcess.eq_vonMangoldt_of_weilPositiveFull_of_summable_excess hW
      (summable_of_dominated_eventually he
        (fun n => div_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)) fun n hn => ?_)
    refine div_le_div_of_nonneg_right (max_le ?_ (abs_nonneg _)) (Real.sqrt_nonneg _)
    have := hdec n hn
    have := hneg n hn
    linarith [le_abs_self (e n)]

/-- **Majorants give no freedom.**  A majorant `lam ≥ Λ` whose Weil functional is nonnegative on
the nonnegative cone is `Λ`; its completion by duality is a Weil-positive majorant, hence `Λ`. -/
theorem eq_vonMangoldt_of_ge_of_positiveOnNonnegCone {lam : ℕ → ℝ}
    (hge : ∀ n, 2 ≤ n → (Λ n : ℝ) ≤ lam n) (h : WeilOneSided.PositiveOnNonnegCone lam) :
    ∀ n, 2 ≤ n → lam n = Λ n := by
  obtain ⟨lam', hW', hle', -⟩ := WeilOneSided.exists_weilPositiveFull_ge_of_positiveOnNonnegCone h
  have heq := eq_vonMangoldt_of_weilPositiveFull_of_ge hW' fun n hn => (hge n hn).trans (hle' n hn)
  exact fun n hn => le_antisymm (by linarith [hle' n hn, heq n hn]) (hge n hn)

/-- A full-cone Weil-positive `lam ≠ Λ` exceeds `Λ` at infinitely many `n` and falls short of it
at infinitely many `n`. -/
theorem infinite_setOf_gt_and_lt_of_ne {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {n₀ : ℕ}
    (hn₀ : 2 ≤ n₀) (hne : lam n₀ ≠ Λ n₀) :
    {n | (Λ n : ℝ) < lam n}.Infinite ∧ {n | lam n < (Λ n : ℝ)}.Infinite := by
  constructor
  · intro hfin
    apply WeilExcess.not_summable_excess_of_ne hW hn₀ hne
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    rw [max_eq_right (by linarith), zero_div]
  · intro hfin
    apply WeilExcess.not_summable_deficit_of_ne hW hn₀ hne
    refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hn
    rw [max_eq_right (by linarith), zero_div]

end

end RHTower.WeilOrderComparable
