import GaloisForLFunctions.BiScaleUncertainty.PrimePowerDeletionPairThreshold
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilings

/-!
# The window spectrum of a node and its square: `log 4` against `log 6`

Delete a prime power `m` together with its square `m²` from the prime-power blind cone and require
every test to live in an open window of length `L`. Put `ℓ = log m`, `w(m) = Λ(m)/√m` and
`s = √(1 + 8m)`. The deviations `(A − W)/‖c‖²` are:

* `0` only, for `L ≤ ℓ` (`towerWindowDeviations_subset_zero`);
* exactly the single price range `[−w(m), w(m)]`, both ends attained, for `ℓ < L ≤ 2ℓ`
  (`isGreatest_towerWindowDeviations_of_le`, `isLeast_towerWindowDeviations_of_le`);
* exactly the joint range `[−Λ(m)(s − 1)/(2m), Λ(m)(s + 1)/(2m)]` of
  `PrimePowerTowerDeletionInteraction`, both ends attained, for `L > 2ℓ`
  (`isGreatest_towerWindowDeviations_of_lt`, `isLeast_towerWindowDeviations_of_lt`).

The single range lies strictly inside the joint range (`single_price_lt_tower_prices`), so the joint
prices are attained iff `L > log m²` (`towerGainPrice_mem_towerWindowDeviations_iff`,
`towerLossPrice_mem_towerWindowDeviations_iff`). For `m = 2` the window spectrum jumps at `log 4`
from `±(log 2)/√2` to `[−(√17 − 1)/4 · log 2, (√17 + 1)/4 · log 2]`.

**`log 4` against `log 6`.** The threshold of the tower pair `{2, 4}` is the lag of the deleted node
`4` itself. The threshold of the coprime pair `{2, 3}` is `log 6` (`PrimePowerDeletionPairThreshold`),
the lag of a node that is never deleted and never charged. On every window length in
`(log 4, log 6]` the joint price of `{2, 4}` is attained and that of `{2, 3}` is not
(`log_four_attains_and_log_six_does_not`).

**Mechanism.** A lag longer than the window is invisible (`logValue_eq_zero_of_window`). Below
`log m²` the square is blind for free (`nodeVector_eq_zero_of_window`), the cone is the
single-deletion cone of `m`, and the tower Fejér bound gives `w(m)`. Past `log m²` the narrow triple
`b + βb(· − ℓ) + b(· − 2ℓ)`, with a bump narrower than `L − 2ℓ` (`indexedTriple`), attains the joint
prices. The square of a node closes its tower on its own lag; two independent primes interact only
through the composite lag.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Short windows hide the square -/

/-- The deviations `(A − W)/‖c‖²` on the cone blind at every prime power except `m` and `m²`, with
every test supported in an open interval of length `L`. -/
def towerWindowDeviations (m : ℕ) (L : ℝ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ {m, m ^ 2}) c ∧
    (∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem towerWindowDeviations_subset (m : ℕ) (L : ℝ) :
    towerWindowDeviations m L ⊆ deletionDeviations₂ m (m ^ 2) := by
  rintro x ⟨c, hc, hb, -, hpos, rfl⟩
  exact ⟨c, hc, hb, hpos, rfl⟩

/-- A node whose lag does not fit into the windows is blind. -/
theorem nodeVector_eq_zero_of_window {c : WeilTestFn →₀ ℝ} {L : ℝ}
    (hw : ∀ f ∈ c.support, ∃ a, ∀ u, f.1 u ≠ 0 → u ∈ Ioo a (a + L)) {n : ℕ} (hn : 2 ≤ n)
    (hL : L ≤ Real.log n) : nodeVector c ⟨n, hn⟩ = 0 := by
  have h := nodeAt_eq_sum c hn
  rw [nodeAt, dif_pos hn] at h
  rw [h, Finsupp.sum]
  refine Finset.sum_eq_zero fun f hf => ?_
  obtain ⟨a, ha⟩ := hw f hf
  rw [logValue_eq_zero_of_window ha (by omega) hL, mul_zero]

/-- The single price lies strictly inside the joint range: `1/√m < (s − 1)/(2m) < (s + 1)/(2m)`. -/
theorem single_price_lt_tower_prices {m : ℝ} (hm : 2 ≤ m) :
    1 / Real.sqrt m < (Real.sqrt (1 + 8 * m) - 1) / (2 * m) ∧
      (Real.sqrt (1 + 8 * m) - 1) / (2 * m) < (Real.sqrt (1 + 8 * m) + 1) / (2 * m) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 + 8 * m) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = Real.sqrt m := ⟨_, rfl⟩
  rw [← hs, ← hq]
  have hs2 : s ^ 2 = 1 + 8 * m := by rw [hs]; exact Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hq2 : q ^ 2 = m := by rw [hq]; exact Real.sq_sqrt (by linarith)
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hq1 : 1 < q := by nlinarith
  have hsq : 1 + 2 * q < s := by nlinarith
  constructor
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith [mul_pos (by linarith : 0 < s - 1 - 2 * q) (by linarith : 0 < q)]
  · exact div_lt_div_of_pos_right (by linarith) (by linarith)

/-- **Windows no longer than `log m`: nothing is seen.** -/
theorem towerWindowDeviations_subset_zero {m : ℕ} (hm : 2 ≤ m) {L : ℝ} (hL : L ≤ Real.log m) :
    towerWindowDeviations m L ⊆ {0} := by
  rintro x ⟨c, hc, hb, hw, hpos, rfl⟩
  have h2' : 2 ≤ m ^ 2 := by nlinarith
  have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
  have hℓ : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  rw [nodeArchEnergy_eq_weilEnergy_add_two hm h2' hm2 hb, add_sub_cancel_left,
    nodeVector_eq_zero_of_window hw hm hL,
    nodeVector_eq_zero_of_window hw h2' (by rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith)]
  simp

/-- **Windows no longer than `log m²`: the single price.** Every deviation lies in
`[−w(m), w(m)]`, because the square is blind for free. -/
theorem abs_le_of_mem_towerWindowDeviations {m : ℕ} (hm : IsPrimePow m) {L x : ℝ}
    (hL : L ≤ 2 * Real.log m) (hx : x ∈ towerWindowDeviations m L) :
    |x| ≤ ArithmeticFunction.vonMangoldt m / Real.sqrt m := by
  obtain ⟨c, hc, hb, hw, hpos, rfl⟩ := hx
  have h2 := hm.two_le
  have h2' : 2 ≤ m ^ 2 := by nlinarith
  have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
  have hsq : nodeVector c ⟨m ^ 2, h2'⟩ = 0 :=
    nodeVector_eq_zero_of_window hw h2' (by rw [Nat.cast_pow, Real.log_pow]; push_cast; linarith)
  -- every power `m^k`, `k ≥ 2`, is blind: `k = 2` by the window, `k ≥ 3` by the cone
  have hA := abs_nodeVector_le_massOf_div_sqrt hc h2 fun j ⟨k, hk, hj⟩ => by
    rcases Nat.lt_or_ge k 3 with hk3 | hk3
    · have hk2 : k = 2 := by omega
      subst hk2
      rw [show j = ⟨m ^ 2, h2'⟩ from Subtype.ext hj, hsq]
    · exact hb j (hj ▸ pow_mem_primePowerNodes_diff_sq hm hk3)
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
  have h1 : |nodeVector c ⟨m, h2⟩| * Real.sqrt m ≤ massOf c := (le_div_iff₀ hs).mp hA
  rw [nodeArchEnergy_eq_weilEnergy_add_two h2 h2' hm2 hb, add_sub_cancel_left, hsq, mul_zero,
    add_zero, abs_div, abs_mul, abs_of_pos hpos, abs_of_nonneg hΛ, div_le_div_iff₀ hpos hs]
  nlinarith [mul_le_mul_of_nonneg_left h1 hΛ]

/-! ### 2. The narrow triple of any index -/

/-- The narrow triple `b + βb(· − log m) + b(· − 2 log m)` with the bump of index `m·M`. -/
def indexedTriple (m M : ℕ) (β : ℝ) (u : ℝ) : ℂ :=
  narrowBumpC (m * M) u + (β : ℂ) * narrowBumpC (m * M) (u - Real.log m) +
    narrowBumpC (m * M) (u - 2 * Real.log m)

theorem indexedTriple_eq_sum (m M : ℕ) (β : ℝ) : indexedTriple m M β = fun u => ∑ a ∈ Finset.range 3,
    (if a = 1 then (β : ℂ) else 1) * narrowBumpC (m * M) (u - (a : ℝ) * Real.log m) := by
  funext u
  simp [indexedTriple, Finset.sum_range_succ]

theorem contDiff_indexedTriple (m M : ℕ) (β : ℝ) : ContDiff ℝ 2 (indexedTriple m M β) := by
  have hb : ContDiff ℝ 2 (narrowBumpC (m * M)) := (contDiff_narrowBumpC _).of_le (by norm_cast)
  exact (hb.add (contDiff_const.mul (hb.comp (contDiff_id.sub contDiff_const)))).add
    (hb.comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_indexedTriple (m M : ℕ) (β : ℝ) :
    HasCompactSupport (indexedTriple m M β) := by
  have hb := hasCompactSupport_narrowBumpC (m * M)
  exact (hb.add ((hb.comp_homeomorph (Homeomorph.subRight (Real.log m))).mul_left)).add
    (hb.comp_homeomorph (Homeomorph.subRight (2 * Real.log m)))

/-- The indexed triple as a Weil test. -/
def indexedTripleFn (m M : ℕ) (β : ℝ) : WeilTestFn :=
  ⟨indexedTriple m M β, contDiff_indexedTriple m M β, hasCompactSupport_indexedTriple m M β⟩

/-- The triple lives in `[−r, 2 log m + r]`, `r = 1/(4(mM + 1))`. -/
theorem indexedTriple_support {m M : ℕ} {β u : ℝ} (hu : indexedTriple m M β u ≠ 0) :
    u ∈ Icc (-(1 / (4 * (((m * M : ℕ) : ℝ) + 1))))
      (2 * Real.log m + 1 / (4 * (((m * M : ℕ) : ℝ) + 1))) := by
  have hℓ : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have key : ∀ v, narrowBumpC (m * M) v ≠ 0 → |v| ≤ 1 / (4 * (((m * M : ℕ) : ℝ) + 1)) :=
    fun v hv => by
      by_contra h
      push Not at h
      exact hv (narrowBumpC_eq_zero _ h)
  by_cases h0 : narrowBumpC (m * M) u = 0
  · by_cases h1 : narrowBumpC (m * M) (u - Real.log m) = 0
    · have h2 : narrowBumpC (m * M) (u - 2 * Real.log m) ≠ 0 := fun h2 => hu (by
        simp only [indexedTriple, h0, h1, h2]; ring)
      have := abs_le.mp (key _ h2)
      constructor <;> linarith [this.1, this.2]
    · have := abs_le.mp (key _ h1)
      constructor <;> linarith [this.1, this.2]
  · have := abs_le.mp (key _ h0)
    constructor <;> linarith [this.1, this.2]

/-- The autocorrelation of the indexed triple. -/
theorem weilTest_indexedTriple (m M : ℕ) (β y : ℝ) :
    EF.weilTest (indexedTriple m M β) (indexedTriple m M β) y =
      ((2 + β ^ 2 : ℝ) : ℂ) * EF.weilTest (narrowBumpC (m * M)) (narrowBumpC (m * M)) y +
        (2 * β : ℝ) * (EF.weilTest (narrowBumpC (m * M)) (narrowBumpC (m * M)) (y + Real.log m) +
          EF.weilTest (narrowBumpC (m * M)) (narrowBumpC (m * M)) (y - Real.log m)) +
        EF.weilTest (narrowBumpC (m * M)) (narrowBumpC (m * M)) (y + 2 * Real.log m) +
        EF.weilTest (narrowBumpC (m * M)) (narrowBumpC (m * M)) (y - 2 * Real.log m) := by
  rw [indexedTriple_eq_sum, weilTest_sum_translates (contDiff_narrowBumpC _).continuous
    (hasCompactSupport_narrowBumpC _)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero, Nat.cast_one,
    zero_mul, one_mul, sub_zero, add_zero, Complex.conj_ofReal, map_one, mul_one, one_mul,
    show (0 : ℕ) ≠ 1 by norm_num, show (2 : ℕ) ≠ 1 by norm_num, if_true, if_false]
  have e1 : y - Real.log m + ((2 : ℕ) : ℝ) * Real.log m = y + Real.log m := by push_cast; ring
  have e2 : y - ((2 : ℕ) : ℝ) * Real.log m + Real.log m = y - Real.log m := by push_cast; ring
  have e3 : y - Real.log m + Real.log m = y := by ring
  have e4 : y - ((2 : ℕ) : ℝ) * Real.log m + ((2 : ℕ) : ℝ) * Real.log m = y := by ring
  have e5 : y + ((2 : ℕ) : ℝ) * Real.log m = y + 2 * Real.log m := by push_cast; ring
  have e6 : y - ((2 : ℕ) : ℝ) * Real.log m = y - 2 * Real.log m := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  push_cast
  ring

section IndexedTripleNodes

variable {m M : ℕ} (hm : 2 ≤ m) {β : ℝ}

omit hm in
theorem pairRadius_lt_of_log_two (m M : ℕ) {t : ℝ} (ht : Real.log 2 ≤ t ∨ t ≤ -Real.log 2) :
    pairRadius m M < |t| := by
  rcases ht with ht | ht
  · exact pairRadius_lt_of_le m M ht
  · exact pairRadius_lt_of_le_neg m M ht

include hm in
theorem weilTest_indexedTriple_zero :
    EF.weilTest (indexedTriple m M β) (indexedTriple m M β) 0 =
      (((2 + β ^ 2) * ∫ t, (narrowBump (m * M) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_indexedTriple, zero_add, zero_sub, zero_add, zero_sub, weilTest_narrowBumpC_zero,
    narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl ha)),
    narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
    narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
    narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith)))]
  push_cast; ring

include hm in
theorem weilTest_indexedTriple_log (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (indexedTriple m M β) (indexedTriple m M β) (s * Real.log m) =
      ((2 * β * ∫ t, (narrowBump (m * M) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_indexedTriple]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl ha)),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith)))]
    push_cast; ring
  · rw [neg_one_mul, neg_add_cancel, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith)))]
    push_cast; ring

include hm in
theorem weilTest_indexedTriple_two_log (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (indexedTriple m M β) (indexedTriple m M β) (s * (2 * Real.log m)) =
      ((∫ t, (narrowBump (m * M) t) ^ 2 : ℝ) : ℂ) := by
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  rw [weilTest_indexedTriple]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith)))]
    push_cast; ring
  · rw [neg_one_mul, neg_add_cancel, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith)))]
    push_cast; ring

include hm in
/-- The indexed triple vanishes at `±log n` for every `n ≥ 2` other than `m`, `m²`, once `M ≥ m`. -/
theorem weilTest_indexedTriple_log_eq_zero (hM : m ≤ M) {n : ℕ} (hn : 2 ≤ n) (hn₁ : n ≠ m)
    (hn₂ : n ≠ m ^ 2) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (indexedTriple m M β) (indexedTriple m M β) (s * Real.log n) = 0 := by
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have ha : Real.log 2 ≤ Real.log m := Real.log_le_log two_pos (by exact_mod_cast hm)
  have hl := Real.log_pos one_lt_two
  have g1 : pairRadius m M < |Real.log n - Real.log m| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (Nat.le_mul_of_pos_right _ (by omega)) hn₁
  have g2 : pairRadius m M < |Real.log n - 2 * Real.log m| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m) (m₂ := M) (a := n) (b := m * m) (by omega)
      (by nlinarith) (Nat.mul_le_mul_left m hM) (by rwa [← sq])
    rwa [log_natCast_mul (by omega) (by omega), ← two_mul] at this
  rw [weilTest_indexedTriple]
  rcases hs with rfl | rfl
  · rw [one_mul, narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl hL)),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))), narrowCorr_eq_zero g1,
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inl (by linarith))), narrowCorr_eq_zero g2]
    ring
  · rw [neg_one_mul, narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (lt_abs_of_eq_or_eq_neg g1 (Or.inr (by ring))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith))),
      narrowCorr_eq_zero (lt_abs_of_eq_or_eq_neg g2 (Or.inr (by ring))),
      narrowCorr_eq_zero (pairRadius_lt_of_log_two m M (Or.inr (by linarith)))]
    ring

include hm in
theorem massOf_single_indexedTripleFn :
    massOf (Finsupp.single (indexedTripleFn m M β) 1) =
      (2 + β ^ 2) * ∫ t, (narrowBump (m * M) t) ^ 2 := by
  have hk := weilTest_indexedTriple_zero (M := M) (β := β) hm
  rw [RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact_mod_cast hk

include hm in
theorem nodeVector_single_indexedTripleFn_log :
    nodeVector (Finsupp.single (indexedTripleFn m M β) 1) ⟨m, hm⟩ =
      4 * β * (∫ t, (narrowBump (m * M) t) ^ 2) / Real.sqrt m := by
  have e1 := weilTest_indexedTriple_log (M := M) (β := β) hm 1 (Or.inl rfl)
  have e2 := weilTest_indexedTriple_log (M := M) (β := β) hm (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (indexedTriple m M β) m = _
  rw [logValue, e1, e2, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

include hm in
theorem nodeVector_single_indexedTripleFn_sq :
    nodeVector (Finsupp.single (indexedTripleFn m M β) 1) ⟨m ^ 2, by nlinarith⟩ =
      2 * (∫ t, (narrowBump (m * M) t) ^ 2) / m := by
  have e1 := weilTest_indexedTriple_two_log (M := M) (β := β) hm 1 (Or.inl rfl)
  have e2 := weilTest_indexedTriple_two_log (M := M) (β := β) hm (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (indexedTriple m M β) (m ^ 2) = _
  have hl : Real.log ((m ^ 2 : ℕ) : ℝ) = 2 * Real.log m := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hs : Real.sqrt ((m ^ 2 : ℕ) : ℝ) = m := by
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg m)]
  rw [logValue, hl, hs, e1, e2, ← Complex.ofReal_add, Complex.ofReal_re]
  ring

include hm in
theorem blindOn_single_indexedTripleFn (hM : m ≤ M) :
    BlindOn (primePowerNodes \ {m, m ^ 2}) (Finsupp.single (indexedTripleFn m M β) 1) := by
  intro j hj
  obtain ⟨-, hne⟩ := hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  rw [nodeVector_single_test, logVector_apply]
  change logValue (indexedTriple m M β) j = 0
  have e1 := weilTest_indexedTriple_log_eq_zero (β := β) hm hM j.2 hne.1 hne.2 1 (Or.inl rfl)
  have e2 := weilTest_indexedTriple_log_eq_zero (β := β) hm hM j.2 hne.1 hne.2 (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [logValue, e1, e2]
  simp

end IndexedTripleNodes

/-- **The narrow triple fits every window longer than `log m²`.** With `1/(mM + 1) < L − 2 log m`
its deviation `Λ(m)(4β/√m + 2/m)/(2 + β²)` is a window deviation of length `L`. -/
theorem tripleDeviation_mem_towerWindowDeviations {m M : ℕ} (hm : 2 ≤ m) (hM : m ≤ M) (β : ℝ)
    {L : ℝ} (hL : 2 * Real.log m + 1 / (((m * M : ℕ) : ℝ) + 1) < L) :
    ArithmeticFunction.vonMangoldt m * ((4 * β / Real.sqrt m + 2 / m) / (2 + β ^ 2)) ∈
      towerWindowDeviations m L := by
  classical
  have h2' : 2 ≤ m ^ 2 := by nlinarith
  have hm2 : m ≠ m ^ 2 := by intro h; nlinarith
  have hI := integral_narrowBump_sq_pos (m * M)
  have hpos : 0 < massOf (Finsupp.single (indexedTripleFn m M β) 1) := by
    rw [massOf_single_indexedTripleFn hm]; positivity
  have hb := blindOn_single_indexedTripleFn (β := β) hm hM
  set r := 1 / (4 * (((m * M : ℕ) : ℝ) + 1)) with hr
  have hr0 : 0 < r := by positivity
  have h4r : 4 * r = 1 / (((m * M : ℕ) : ℝ) + 1) := by rw [hr]; field_simp
  refine ⟨_, fun f => ?_, hb, fun g hg => ?_, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hg
    split_ifs at hg with hfg
    · rw [← hfg]
      refine ⟨-(2 * r), fun u hu => ?_⟩
      have := indexedTriple_support (β := β) hu
      rw [← hr] at this
      constructor <;> linarith [this.1, this.2]
    · exact absurd rfl hg
  · rw [nodeArchEnergy_eq_weilEnergy_add_two hm h2' hm2 hb, add_sub_cancel_left, vonMangoldt_sq,
      nodeVector_single_indexedTripleFn_log hm, nodeVector_single_indexedTripleFn_sq hm,
      massOf_single_indexedTripleFn hm]
    have hq : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < m))
    have hm' : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    field_simp

/-- Every window longer than `log m²` admits a triple index. -/
theorem exists_index_of_lt {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 2 * Real.log m < L) :
    ∃ M : ℕ, m ≤ M ∧ 2 * Real.log m + 1 / (((m * M : ℕ) : ℝ) + 1) < L := by
  have hpos : 0 < L - 2 * Real.log m := by linarith
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / (L - 2 * Real.log m))
  refine ⟨max m k, le_max_left _ _, ?_⟩
  have hk' : 1 < k * (L - 2 * Real.log m) := (div_lt_iff₀ hpos).mp hk
  have hMk : (k : ℝ) ≤ ((m * max m k : ℕ) : ℝ) := by
    have : k ≤ m * max m k := le_trans (le_max_right m k) (Nat.le_mul_of_pos_left _ (by omega))
    exact_mod_cast this
  have hden : 0 < ((m * max m k : ℕ) : ℝ) + 1 := by positivity
  have : 1 / (((m * max m k : ℕ) : ℝ) + 1) < L - 2 * Real.log m := by
    rw [div_lt_iff₀ hden]
    nlinarith
  linarith

/-! ### 3. The window spectrum -/

/-- A single-node Euler window deviation is a tower window deviation. -/
theorem eulerWindowDeviations_single_subset (p k : ℕ) (L : ℝ) :
    eulerWindowDeviations {p} (fun _ => k) L ⊆ towerWindowDeviations (p ^ k) L := by
  rintro x ⟨c, hc, hb, hw, hpos, rfl⟩
  refine ⟨c, hc, fun j hj => hb j ⟨hj.1, fun h => hj.2 ?_⟩, hw, hpos, rfl⟩
  have h' : (j : ℕ) = p ^ k := by simpa [eulerNodes] using h
  exact Or.inl h'

/-- On windows longer than `log m` the single prices `±w(m)` are tower window deviations. -/
theorem singlePrice_mem_towerWindowDeviations {m : ℕ} (hm : IsPrimePow m) {L : ℝ}
    (hL : Real.log m < L) {s : ℝ} (hs : s ^ 2 = 1) :
    s * (ArithmeticFunction.vonMangoldt m / Real.sqrt m) ∈ towerWindowDeviations m L := by
  classical
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff m).mp hm
  have hP : ∀ q ∈ ({p} : Finset ℕ), q.Prime := fun q hq => by
    rw [Finset.mem_singleton] at hq; rw [hq]; exact hp
  have he : ∀ q ∈ ({p} : Finset ℕ), 1 ≤ (fun _ : ℕ => k) q := fun _ _ => hk
  have h := deviation_mem_eulerWindowDeviations hP he (L := L)
    (by rw [subProd, Finset.prod_singleton]; exact hL) hs
  rw [eulerPrice, Finset.sum_singleton] at h
  exact eulerWindowDeviations_single_subset p k L h

/-- **Between `log m` and `log m²` the top of the spectrum is the single price `w(m)`.** -/
theorem isGreatest_towerWindowDeviations_of_le {m : ℕ} (hm : IsPrimePow m) {L : ℝ}
    (h₁ : Real.log m < L) (h₂ : L ≤ 2 * Real.log m) :
    IsGreatest (towerWindowDeviations m L)
      (ArithmeticFunction.vonMangoldt m / Real.sqrt m) := by
  refine ⟨by simpa using singlePrice_mem_towerWindowDeviations hm h₁ (s := 1) (by norm_num),
    fun x hx => ?_⟩
  exact (abs_le.mp (abs_le_of_mem_towerWindowDeviations hm h₂ hx)).2

/-- **Between `log m` and `log m²` the bottom of the spectrum is `−w(m)`.** -/
theorem isLeast_towerWindowDeviations_of_le {m : ℕ} (hm : IsPrimePow m) {L : ℝ}
    (h₁ : Real.log m < L) (h₂ : L ≤ 2 * Real.log m) :
    IsLeast (towerWindowDeviations m L)
      (-(ArithmeticFunction.vonMangoldt m / Real.sqrt m)) := by
  refine ⟨by simpa using singlePrice_mem_towerWindowDeviations hm h₁ (s := -1) (by norm_num),
    fun x hx => ?_⟩
  exact (abs_le.mp (abs_le_of_mem_towerWindowDeviations hm h₂ hx)).1

/-- **The joint gain price is attained iff `L > log m²`.** -/
theorem towerGainPrice_mem_towerWindowDeviations_iff {m : ℕ} (hm : IsPrimePow m) (L : ℝ) :
    ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * m)) ∈
      towerWindowDeviations m L ↔ 2 * Real.log m < L := by
  have h2 := hm.two_le
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h2
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hm
  have hsep := single_price_lt_tower_prices hm'
  constructor
  · intro hx
    by_contra hL
    push Not at hL
    have h := abs_le_of_mem_towerWindowDeviations hm hL hx
    have hp : 0 < (Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * m) :=
      div_pos (by positivity) (by linarith)
    rw [abs_of_pos (mul_pos hΛ hp)] at h
    have e : (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m =
        ArithmeticFunction.vonMangoldt m * (1 / Real.sqrt m) := by ring
    linarith [mul_lt_mul_of_pos_left (hsep.1.trans hsep.2) hΛ]
  · intro hL
    obtain ⟨M, hM, hML⟩ := exists_index_of_lt (by omega) hL
    have h := tripleDeviation_mem_towerWindowDeviations h2 hM
      ((Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * Real.sqrt m)) hML
    rwa [(triple_deviation_values hm').1] at h

/-- **The joint loss price is attained iff `L > log m²`.** -/
theorem towerLossPrice_mem_towerWindowDeviations_iff {m : ℕ} (hm : IsPrimePow m) (L : ℝ) :
    -(ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * m))) ∈
      towerWindowDeviations m L ↔ 2 * Real.log m < L := by
  have h2 := hm.two_le
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast h2
  have hΛ : 0 < (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_pos_iff.mpr hm
  have hsep := single_price_lt_tower_prices hm'
  constructor
  · intro hx
    by_contra hL
    push Not at hL
    have h := abs_le_of_mem_towerWindowDeviations hm hL hx
    have hp : 0 < (Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * m) :=
      lt_trans (by have := Real.sqrt_pos.mpr (show (0 : ℝ) < m by linarith); positivity) hsep.1
    rw [abs_neg, abs_of_pos (mul_pos hΛ hp)] at h
    have e : (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m =
        ArithmeticFunction.vonMangoldt m * (1 / Real.sqrt m) := by ring
    linarith [mul_lt_mul_of_pos_left hsep.1 hΛ]
  · intro hL
    obtain ⟨M, hM, hML⟩ := exists_index_of_lt (by omega) hL
    have h := tripleDeviation_mem_towerWindowDeviations h2 hM
      (-(Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * Real.sqrt m)) hML
    rwa [(triple_deviation_values hm').2, mul_neg] at h

/-- **Past `log m²` the top of the spectrum is the joint gain price.** -/
theorem isGreatest_towerWindowDeviations_of_lt {m : ℕ} (hm : IsPrimePow m) {L : ℝ}
    (hL : 2 * Real.log m < L) :
    IsGreatest (towerWindowDeviations m L)
      (ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) + 1) / (2 * m))) :=
  ⟨(towerGainPrice_mem_towerWindowDeviations_iff hm L).mpr hL, fun _ hx =>
    (isGreatest_deletionDeviations₂_sq hm).2 (towerWindowDeviations_subset m L hx)⟩

/-- **Past `log m²` the bottom of the spectrum is minus the joint loss price.** -/
theorem isLeast_towerWindowDeviations_of_lt {m : ℕ} (hm : IsPrimePow m) {L : ℝ}
    (hL : 2 * Real.log m < L) :
    IsLeast (towerWindowDeviations m L)
      (-(ArithmeticFunction.vonMangoldt m * ((Real.sqrt (1 + 8 * (m : ℝ)) - 1) / (2 * m)))) :=
  ⟨(towerLossPrice_mem_towerWindowDeviations_iff hm L).mpr hL, fun _ hx =>
    (isLeast_deletionDeviations₂_sq hm).2 (towerWindowDeviations_subset m L hx)⟩

/-! ### 4. `log 4` against `log 6` -/

/-- **`log 4` against `log 6`.** On every window length `L ∈ (log 4, log 6]` the joint gain price
`(√17 + 1)/4 · log 2` of `{2, 4}` is attained, and the joint price `w(2) + w(3)` of `{2, 3}` is not. -/
theorem log_four_attains_and_log_six_does_not {L : ℝ} (h₁ : Real.log 4 < L)
    (h₂ : L ≤ Real.log 6) :
    (Real.sqrt 17 + 1) / 4 * Real.log 2 ∈ towerWindowDeviations 2 L ∧
      eulerPrice {2, 3} (fun _ => 1) ∉ eulerWindowDeviations {2, 3} (fun _ => 1) L := by
  constructor
  · have h := (towerGainPrice_mem_towerWindowDeviations_iff Nat.prime_two.isPrimePow L).mpr (by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
      push_cast; linarith)
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at h
    convert h using 1
    push_cast
    rw [show (1 : ℝ) + 8 * 2 = 17 by norm_num]
    ring
  · rw [eulerPrice_mem_eulerWindowDeviations_iff Nat.prime_two Nat.prime_three (by norm_num) le_rfl
      le_rfl L]
    norm_num
    exact h₂

end

end GaloisForLFunctions.BiScaleUncertainty
