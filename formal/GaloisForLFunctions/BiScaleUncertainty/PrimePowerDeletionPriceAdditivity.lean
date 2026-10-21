import GaloisForLFunctions.BiScaleUncertainty.PrimePowerNodeDeletionPrice

/-!
# Deletion prices add across towers, and the composite node pays nothing

`PrimePowerNodeDeletionPrice` shows that deleting one prime power `m` from the prime-power blind
cone moves the archimedean energy against the Weil functional by exactly `±Λ(m)/√m` per unit mass.
Here two prime powers `m₁`, `m₂` of different primes (`gcd(m₁, m₂) = 1`) are deleted together.

**Theorem** (`isLeast_deletionDeviations₂`, `isGreatest_deletionDeviations₂`). On the combinations
blind at every prime power except `m₁` and `m₂`, the exact range of `(A − W)/‖c‖²` is

`[−(Λ(m₁)/√m₁ + Λ(m₂)/√m₂), Λ(m₁)/√m₁ + Λ(m₂)/√m₂]`:

the prices add. For `{2, 3}` the price is `log 2/√2 + log 3/√3`
(`isLeast_deletionDeviations₂_two_three`).

**Mechanism.**
* Upper bound: `A − W = Λ(m₁)L_{m₁} + Λ(m₂)L_{m₂}`, and the tower Fejér bound applies to each node
  separately, because the powers `m_i^k`, `k ≥ 2`, are prime powers different from both deleted
  nodes.
* Attainment: the double pair `b ∗ (δ₀ + σ₁δ_{log m₁}) ∗ (δ₀ + σ₂δ_{log m₂})` of a narrow bump puts
  the extremal correlation `σ_i/2` at both `log m_i` at once. Its only other integer lag is the cross
  lag `log(m₁m₂)`, where it carries the node value `σ₁σ₂ ‖·‖²/(2√(m₁m₂))`
  (`logValue_doublePair_mul`). The cone does not ask for blindness there because `m₁m₂` is not a
  prime power: deleting `{2, 3}` charges `log 6`, and `Λ(6) = 0` makes it free.

So additivity across towers is the redundancy of the composite nodes: the integer-grid blind cone,
which also asks for blindness at `log(m₁m₂)`, does not admit the double pair.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. A source with one signed translate -/

/-- A source together with a signed translate: `h(u) + σ h(u − ℓ)`. -/
def pairOf (h : ℝ → ℂ) (ℓ σ : ℝ) (u : ℝ) : ℂ := h u + (σ : ℂ) * h (u - ℓ)

theorem pairOf_eq_sum (h : ℝ → ℂ) (ℓ σ : ℝ) :
    pairOf h ℓ σ = fun u => ∑ m ∈ Finset.range 2,
      (if m = 0 then (1 : ℂ) else (σ : ℂ)) * h (u - if m = 0 then 0 else ℓ) := by
  funext u
  simp [pairOf, Finset.sum_range_succ]

theorem continuous_pairOf {h : ℝ → ℂ} (hc : Continuous h) (ℓ σ : ℝ) :
    Continuous (pairOf h ℓ σ) :=
  hc.add (continuous_const.mul (hc.comp (continuous_id.sub continuous_const)))

theorem hasCompactSupport_pairOf {h : ℝ → ℂ} (hcs : HasCompactSupport h) (ℓ σ : ℝ) :
    HasCompactSupport (pairOf h ℓ σ) :=
  hcs.add ((hcs.comp_homeomorph (Homeomorph.subRight ℓ)).mul_left)

theorem contDiff_pairOf {h : ℝ → ℂ} (hh : ContDiff ℝ 2 h) (ℓ σ : ℝ) :
    ContDiff ℝ 2 (pairOf h ℓ σ) :=
  hh.add (contDiff_const.mul (hh.comp (contDiff_id.sub contDiff_const)))

/-- The autocorrelation of a source with one signed translate. -/
theorem weilTest_pairOf {h : ℝ → ℂ} (hc : Continuous h) (hcs : HasCompactSupport h)
    (ℓ σ y : ℝ) :
    EF.weilTest (pairOf h ℓ σ) (pairOf h ℓ σ) y =
      ((1 + σ ^ 2 : ℝ) : ℂ) * EF.weilTest h h y +
        (σ : ℂ) * (EF.weilTest h h (y + ℓ) + EF.weilTest h h (y - ℓ)) := by
  rw [pairOf_eq_sum, weilTest_sum_translates hc hcs]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, if_true, one_ne_zero,
    if_false, Complex.conj_ofReal, map_one, mul_one, one_mul, sub_zero, add_zero, sub_add_cancel]
  push_cast
  ring

/-! ### 2. The double pair -/

/-- The inner pair `b(u) + σ₂ b(u − log m₂)` of the narrow bump of index `m₁m₂`. -/
def innerPair (m₁ m₂ : ℕ) (σ₂ : ℝ) : ℝ → ℂ := pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂

/-- The double pair `b ∗ (δ₀ + σ₁δ_{log m₁}) ∗ (δ₀ + σ₂δ_{log m₂})`. -/
def doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : ℝ → ℂ := pairOf (innerPair m₁ m₂ σ₂) (Real.log m₁) σ₁

theorem contDiff_doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : ContDiff ℝ 2 (doublePair m₁ m₂ σ₁ σ₂) :=
  contDiff_pairOf (contDiff_pairOf ((contDiff_narrowBumpC _).of_le (by norm_cast)) _ _) _ _

theorem hasCompactSupport_doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) :
    HasCompactSupport (doublePair m₁ m₂ σ₁ σ₂) :=
  hasCompactSupport_pairOf (hasCompactSupport_pairOf (hasCompactSupport_narrowBumpC _) _ _) _ _

/-- The double pair as a Weil test. -/
def doublePairTestFn (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : WeilTestFn :=
  ⟨doublePair m₁ m₂ σ₁ σ₂, contDiff_doublePair m₁ m₂ σ₁ σ₂,
    hasCompactSupport_doublePair m₁ m₂ σ₁ σ₂⟩

/-- The autocorrelation of the inner pair. -/
def innerCorr (m₁ m₂ : ℕ) (σ₂ t : ℝ) : ℂ := EF.weilTest (innerPair m₁ m₂ σ₂) (innerPair m₁ m₂ σ₂) t

/-- The correlation radius `1/(2(m₁m₂ + 1))` of the narrow bump of index `m₁m₂`. -/
def pairRadius (m₁ m₂ : ℕ) : ℝ := 1 / (2 * (((m₁ * m₂ : ℕ) : ℝ) + 1))

theorem weilTest_doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ y : ℝ) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) y =
      ((1 + σ₁ ^ 2 : ℝ) : ℂ) * innerCorr m₁ m₂ σ₂ y +
        (σ₁ : ℂ) * (innerCorr m₁ m₂ σ₂ (y + Real.log m₁) + innerCorr m₁ m₂ σ₂ (y - Real.log m₁)) :=
  weilTest_pairOf (continuous_pairOf (contDiff_narrowBumpC _).continuous _ _)
    (hasCompactSupport_pairOf (hasCompactSupport_narrowBumpC _) _ _) _ _ y

theorem innerCorr_eq (m₁ m₂ : ℕ) (σ₂ t : ℝ) :
    innerCorr m₁ m₂ σ₂ t =
      ((1 + σ₂ ^ 2 : ℝ) : ℂ) * EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) t +
        (σ₂ : ℂ) * (EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) (t + Real.log m₂) +
          EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) (t - Real.log m₂)) :=
  weilTest_pairOf (contDiff_narrowBumpC _).continuous (hasCompactSupport_narrowBumpC _) _ _ t

theorem narrowCorr_eq_zero {m₁ m₂ : ℕ} {t : ℝ} (ht : pairRadius m₁ m₂ < |t|) :
    EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) t = 0 :=
  weilTest_narrowBumpC_eq_zero _ ht

/-- The inner correlation vanishes away from the lags `0, ±log m₂`. -/
theorem innerCorr_eq_zero {m₁ m₂ : ℕ} {σ₂ t : ℝ} (h0 : pairRadius m₁ m₂ < |t|)
    (h1 : pairRadius m₁ m₂ < |t + Real.log m₂|) (h2 : pairRadius m₁ m₂ < |t - Real.log m₂|) :
    innerCorr m₁ m₂ σ₂ t = 0 := by
  rw [innerCorr_eq, narrowCorr_eq_zero h0, narrowCorr_eq_zero h1, narrowCorr_eq_zero h2]
  ring

/-! ### 3. Gaps -/

/-- Integer logarithm gaps beat the radius when the comparison integer is at most `m₁m₂`. -/
theorem pairRadius_lt_abs_log_sub {m₁ m₂ a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbj : b ≤ m₁ * m₂) (hab : a ≠ b) : pairRadius m₁ m₂ < |Real.log a - Real.log b| := by
  refine lt_of_lt_of_le ?_ (WeilExcess.inv_succ_le_abs_log_sub ha hb hab)
  have hb' : (b : ℝ) ≤ ((m₁ * m₂ : ℕ) : ℝ) := by exact_mod_cast hbj
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [pairRadius, div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem pairRadius_lt_of_log_two_le (m₁ m₂ : ℕ) {t : ℝ} (ht : Real.log 2 ≤ |t|) :
    pairRadius m₁ m₂ < |t| := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le WeilExcess.seventeen_div_twentyfive_lt_log_two ht)
  rw [pairRadius, div_le_iff₀ (by positivity)]
  nlinarith [(Nat.cast_nonneg (m₁ * m₂) : (0 : ℝ) ≤ ((m₁ * m₂ : ℕ) : ℝ))]

theorem pairRadius_lt_of_le (m₁ m₂ : ℕ) {t : ℝ} (ht : Real.log 2 ≤ t) : pairRadius m₁ m₂ < |t| :=
  pairRadius_lt_of_log_two_le m₁ m₂ (by rw [abs_of_pos (by linarith [Real.log_pos one_lt_two])]; exact ht)

theorem pairRadius_lt_of_le_neg (m₁ m₂ : ℕ) {t : ℝ} (ht : t ≤ -Real.log 2) :
    pairRadius m₁ m₂ < |t| :=
  pairRadius_lt_of_log_two_le m₁ m₂ (by
    rw [abs_of_neg (by linarith [Real.log_pos one_lt_two])]; linarith)

theorem lt_abs_of_eq_or_eq_neg {δ X Y : ℝ} (h : δ < |Y|) (e : X = Y ∨ X = -Y) : δ < |X| := by
  rcases e with rfl | rfl
  · exact h
  · rwa [abs_neg]

/-- Coprimality excludes every divisibility the double pair could collide on. -/
theorem mul_ne_of_coprime {m₁ m₂ : ℕ} (hco : Nat.Coprime m₁ m₂) (h₁ : 2 ≤ m₁) (n : ℕ) :
    n * m₁ ≠ m₂ := by
  intro h
  have := Nat.Coprime.eq_one_of_dvd hco ⟨n, by rw [← h, mul_comm]⟩
  omega

/-- The product of two coprime integers `≥ 2` is not a prime power. -/
theorem not_isPrimePow_mul_of_coprime {m₁ m₂ : ℕ} (hco : Nat.Coprime m₁ m₂) (h₁ : 2 ≤ m₁)
    (h₂ : 2 ≤ m₂) : ¬ IsPrimePow (m₁ * m₂) := by
  intro h
  rcases (Nat.Coprime.isPrimePow_dvd_mul hco h).mp dvd_rfl with h' | h'
  · have := Nat.le_of_dvd (by omega) h'; nlinarith
  · have := Nat.le_of_dvd (by omega) h'; nlinarith

theorem log_natCast_mul {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Real.log ((a * b : ℕ) : ℝ) = Real.log a + Real.log b := by
  rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]

/-! ### 4. The correlation of the double pair at the nodes -/

section Evaluation

variable {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) (hco : Nat.Coprime m₁ m₂) {σ₁ σ₂ : ℝ}

include h₂ in
theorem le_mul_left' : m₁ ≤ m₁ * m₂ := Nat.le_mul_of_pos_right _ (by omega)

include h₁ in
theorem le_mul_right' : m₂ ≤ m₁ * m₂ := Nat.le_mul_of_pos_left _ (by omega)

include h₁ h₂ hco in
/-- The inner correlation vanishes at `±log m₁`. -/
theorem innerCorr_pm_log_one_eq_zero (s : ℝ) (hs : s = 1 ∨ s = -1) :
    innerCorr m₁ m₂ σ₂ (s * Real.log m₁) = 0 := by
  have ha : Real.log 2 ≤ Real.log m₁ := Real.log_le_log two_pos (by exact_mod_cast h₁)
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have g : pairRadius m₁ m₂ < |Real.log m₁ - Real.log m₂| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (le_mul_right' h₁)
      (by simpa using mul_ne_of_coprime hco h₁ 1)
  rcases hs with rfl | rfl
  · rw [one_mul]
    exact innerCorr_eq_zero (pairRadius_lt_of_le _ _ ha) (pairRadius_lt_of_le _ _ (by linarith)) g
  · rw [neg_one_mul]
    exact innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
      (lt_abs_of_eq_or_eq_neg g (Or.inr (by ring))) (pairRadius_lt_of_le_neg _ _ (by linarith))

include h₂ in
/-- At the origin the inner correlation is `(1 + σ₂²) ∫ h²`. -/
theorem innerCorr_zero :
    innerCorr m₁ m₂ σ₂ 0 = ((1 + σ₂ ^ 2 : ℝ) : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ) := by
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  rw [innerCorr_eq, zero_add, zero_sub, weilTest_narrowBumpC_zero,
    narrowCorr_eq_zero (pairRadius_lt_of_le _ _ hb),
    narrowCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))]
  ring

include h₂ in
/-- At `±log m₂` the inner correlation is `σ₂ ∫ h²`. -/
theorem innerCorr_pm_log_two (s : ℝ) (hs : s = 1 ∨ s = -1) :
    innerCorr m₁ m₂ σ₂ (s * Real.log m₂) = (σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ) := by
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  rw [innerCorr_eq]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero, narrowCorr_eq_zero (pairRadius_lt_of_le _ _ hb),
      narrowCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith))]
    ring
  · rw [neg_one_mul, neg_add_cancel, weilTest_narrowBumpC_zero,
      narrowCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith)),
      narrowCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring

include h₁ h₂ hco in
/-- **Blind off the three lags.** The double pair vanishes at `±log n` for every `n ≥ 2` other than
`m₁`, `m₂`, `m₁m₂`. -/
theorem weilTest_doublePair_log_eq_zero {n : ℕ} (hn : 2 ≤ n) (hn₁ : n ≠ m₁) (hn₂ : n ≠ m₂)
    (hn₁₂ : n ≠ m₁ * m₂) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) (s * Real.log n) = 0 := by
  have hL : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
  have ha : Real.log 2 ≤ Real.log m₁ := Real.log_le_log two_pos (by exact_mod_cast h₁)
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have gn2 : pairRadius m₁ m₂ < |Real.log n - Real.log m₂| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (le_mul_right' h₁) hn₂
  have gn1 : pairRadius m₁ m₂ < |Real.log n - Real.log m₁| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (le_mul_left' h₂) hn₁
  have gn12 : pairRadius m₁ m₂ < |Real.log n - (Real.log m₁ + Real.log m₂)| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m₁) (m₂ := m₂) (a := n) (b := m₁ * m₂) (by omega)
      (by nlinarith) le_rfl hn₁₂
    rwa [log_natCast_mul (by omega) (by omega)] at this
  have gnm1 : pairRadius m₁ m₂ < |Real.log n + Real.log m₁ - Real.log m₂| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m₁) (m₂ := m₂) (a := n * m₁) (b := m₂) (by nlinarith)
      (by omega) (le_mul_right' h₁) (mul_ne_of_coprime hco h₁ n)
    rwa [log_natCast_mul (by omega) (by omega)] at this
  have gnm2 : pairRadius m₁ m₂ < |Real.log n + Real.log m₂ - Real.log m₁| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m₁) (m₂ := m₂) (a := n * m₂) (b := m₁) (by nlinarith)
      (by omega) (le_mul_left' h₂) (mul_ne_of_coprime hco.symm h₂ n)
    rwa [log_natCast_mul (by omega) (by omega)] at this
  rw [weilTest_doublePair]
  rcases hs with rfl | rfl
  · rw [one_mul,
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ hL) (pairRadius_lt_of_le _ _ (by linarith)) gn2,
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith))
        (pairRadius_lt_of_le _ _ (by linarith)) gnm1,
      innerCorr_eq_zero gn1 (lt_abs_of_eq_or_eq_neg gnm2 (Or.inl (by ring)))
        (lt_abs_of_eq_or_eq_neg gn12 (Or.inl (by ring)))]
    ring
  · rw [neg_one_mul,
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg gn2 (Or.inr (by ring))) (pairRadius_lt_of_le_neg _ _ (by linarith)),
      innerCorr_eq_zero (lt_abs_of_eq_or_eq_neg gn1 (Or.inr (by ring)))
        (lt_abs_of_eq_or_eq_neg gn12 (Or.inr (by ring)))
        (lt_abs_of_eq_or_eq_neg gnm2 (Or.inr (by ring))),
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg gnm1 (Or.inr (by ring))) (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring

include h₁ h₂ hco in
/-- At `±log m₁` the double pair is `σ₁(1 + σ₂²) ∫ h²`. -/
theorem weilTest_doublePair_log_one (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) (s * Real.log m₁) =
      (σ₁ : ℂ) * (((1 + σ₂ ^ 2 : ℝ) : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) := by
  have ha : Real.log 2 ≤ Real.log m₁ := Real.log_le_log two_pos (by exact_mod_cast h₁)
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have g : pairRadius m₁ m₂ < |Real.log m₁ + Real.log m₁ - Real.log m₂| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m₁) (m₂ := m₂) (a := m₁ * m₁) (b := m₂) (by nlinarith)
      (by omega) (le_mul_right' h₁) (mul_ne_of_coprime hco h₁ m₁)
    rwa [log_natCast_mul (by omega) (by omega)] at this
  rw [weilTest_doublePair, innerCorr_pm_log_one_eq_zero h₁ h₂ hco s hs]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, innerCorr_zero h₂,
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith))
        (pairRadius_lt_of_le _ _ (by linarith)) g]
    ring
  · rw [neg_one_mul, neg_add_cancel, innerCorr_zero h₂,
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg g (Or.inr (by ring))) (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring

include h₁ h₂ hco in
/-- At `±log m₂` the double pair is `(1 + σ₁²)σ₂ ∫ h²`. -/
theorem weilTest_doublePair_log_two (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) (s * Real.log m₂) =
      ((1 + σ₁ ^ 2 : ℝ) : ℂ) * ((σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) := by
  have ha : Real.log 2 ≤ Real.log m₁ := Real.log_le_log two_pos (by exact_mod_cast h₁)
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have g : pairRadius m₁ m₂ < |Real.log m₂ - Real.log m₁| :=
    pairRadius_lt_abs_log_sub (by omega) (by omega) (le_mul_left' h₂)
      (by simpa using mul_ne_of_coprime hco.symm h₂ 1)
  have g' : pairRadius m₁ m₂ < |Real.log m₂ + Real.log m₂ - Real.log m₁| := by
    have := pairRadius_lt_abs_log_sub (m₁ := m₁) (m₂ := m₂) (a := m₂ * m₂) (b := m₁) (by nlinarith)
      (by omega) (le_mul_left' h₂) (mul_ne_of_coprime hco.symm h₂ m₂)
    rwa [log_natCast_mul (by omega) (by omega)] at this
  rw [weilTest_doublePair, innerCorr_pm_log_two h₂ s hs]
  rcases hs with rfl | rfl
  · rw [one_mul,
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith)) (pairRadius_lt_of_le _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg (pairRadius_lt_of_le m₁ m₂ ha) (Or.inl (by ring))),
      innerCorr_eq_zero g (lt_abs_of_eq_or_eq_neg g' (Or.inl (by ring)))
        (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring
  · rw [neg_one_mul,
      innerCorr_eq_zero (lt_abs_of_eq_or_eq_neg g (Or.inr (by ring)))
        (lt_abs_of_eq_or_eq_neg (pairRadius_lt_of_le m₁ m₂ ha) (Or.inl (by ring)))
        (lt_abs_of_eq_or_eq_neg g' (Or.inr (by ring))),
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (pairRadius_lt_of_le_neg _ _ (by linarith)) (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring

include h₁ h₂ hco in
/-- At the origin the double pair is `(1 + σ₁²)(1 + σ₂²) ∫ h²`. -/
theorem weilTest_doublePair_zero :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) 0 =
      ((1 + σ₁ ^ 2 : ℝ) : ℂ) * (((1 + σ₂ ^ 2 : ℝ) : ℂ) *
        ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) := by
  have h1 := innerCorr_pm_log_one_eq_zero (σ₂ := σ₂) h₁ h₂ hco 1 (Or.inl rfl)
  have h2 := innerCorr_pm_log_one_eq_zero (σ₂ := σ₂) h₁ h₂ hco (-1) (Or.inr rfl)
  rw [one_mul] at h1
  rw [neg_one_mul] at h2
  rw [weilTest_doublePair, zero_add, zero_sub, h1, h2, innerCorr_zero h₂]
  ring

include h₁ h₂ in
/-- At the cross lag `±log(m₁m₂)` the double pair is `σ₁σ₂ ∫ h²`. -/
theorem weilTest_doublePair_log_mul (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂)
        (s * (Real.log m₁ + Real.log m₂)) =
      (σ₁ : ℂ) * ((σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) := by
  have ha : Real.log 2 ≤ Real.log m₁ := Real.log_le_log two_pos (by exact_mod_cast h₁)
  have hb : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  rw [weilTest_doublePair]
  rcases hs with rfl | rfl
  · have e : 1 * (Real.log m₁ + Real.log m₂) - Real.log m₁ = 1 * Real.log m₂ := by ring
    rw [e, innerCorr_pm_log_two h₂ 1 (Or.inl rfl), one_mul,
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith)) (pairRadius_lt_of_le _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg (pairRadius_lt_of_le m₁ m₂ ha) (Or.inl (by ring))),
      innerCorr_eq_zero (pairRadius_lt_of_le _ _ (by linarith)) (pairRadius_lt_of_le _ _ (by linarith))
        (pairRadius_lt_of_le _ _ (by linarith))]
    ring
  · have e : -1 * (Real.log m₁ + Real.log m₂) + Real.log m₁ = -1 * Real.log m₂ := by ring
    rw [e, innerCorr_pm_log_two h₂ (-1) (Or.inr rfl), neg_one_mul,
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (lt_abs_of_eq_or_eq_neg (pairRadius_lt_of_le m₁ m₂ ha) (Or.inr (by ring)))
        (pairRadius_lt_of_le_neg _ _ (by linarith)),
      innerCorr_eq_zero (pairRadius_lt_of_le_neg _ _ (by linarith))
        (pairRadius_lt_of_le_neg _ _ (by linarith)) (pairRadius_lt_of_le_neg _ _ (by linarith))]
    ring

end Evaluation

/-! ### 5. Node values and mass of the double pair -/

section DoublePairNodes

variable {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) (hco : Nat.Coprime m₁ m₂) {σ₁ σ₂ : ℝ}
  (hσ₁ : σ₁ ^ 2 = 1) (hσ₂ : σ₂ ^ 2 = 1)

include h₁ h₂ hco hσ₁ hσ₂ in
/-- The mass of the double pair is `4 ∫ h²`. -/
theorem massOf_single_doublePairTestFn :
    massOf (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) =
      4 * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2 := by
  have hk := weilTest_doublePair_zero (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco
  rw [RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm : ∫ u, ‖doublePair m₁ m₂ σ₁ σ₂ u‖ ^ 2 =
      (1 + σ₁ ^ 2) * ((1 + σ₂ ^ 2) * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2) := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  change ∫ u, ‖doublePair m₁ m₂ σ₁ σ₂ u‖ ^ 2 = _
  rw [hm, hσ₁, hσ₂]; ring

include h₁ h₂ hco in
/-- The double pair is blind at every `n ≥ 2` other than `m₁`, `m₂`, `m₁m₂`. -/
theorem logValue_doublePair_eq_zero {n : ℕ} (hn : 2 ≤ n) (hn₁ : n ≠ m₁) (hn₂ : n ≠ m₂)
    (hn₁₂ : n ≠ m₁ * m₂) : logValue (doublePair m₁ m₂ σ₁ σ₂) n = 0 := by
  have e1 := weilTest_doublePair_log_eq_zero (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco hn hn₁ hn₂ hn₁₂ 1
    (Or.inl rfl)
  have e2 := weilTest_doublePair_log_eq_zero (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco hn hn₁ hn₂ hn₁₂ (-1)
    (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [logValue, e1, e2]
  simp

include h₁ h₂ hco hσ₁ hσ₂ in
/-- At `m₁` the double pair carries `L_{m₁} = σ₁ ‖·‖²/√m₁`, the tower Fejér extreme. -/
theorem nodeVector_single_doublePairTestFn_one :
    nodeVector (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) ⟨m₁, h₁⟩ =
      σ₁ * massOf (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) / Real.sqrt m₁ := by
  have e1 := weilTest_doublePair_log_one (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco 1 (Or.inl rfl)
  have e2 := weilTest_doublePair_log_one (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply, massOf_single_doublePairTestFn h₁ h₂ hco hσ₁ hσ₂]
  change logValue (doublePair m₁ m₂ σ₁ σ₂) m₁ = _
  have e : (σ₁ : ℂ) * (((1 + σ₂ ^ 2 : ℝ) : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) =
      ((σ₁ * ((1 + σ₂ ^ 2) * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [logValue, e1, e2, e, ← Complex.ofReal_add, Complex.ofReal_re, hσ₂]
  ring

include h₁ h₂ hco hσ₁ hσ₂ in
/-- At `m₂` the double pair carries `L_{m₂} = σ₂ ‖·‖²/√m₂`. -/
theorem nodeVector_single_doublePairTestFn_two :
    nodeVector (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) ⟨m₂, h₂⟩ =
      σ₂ * massOf (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) / Real.sqrt m₂ := by
  have e1 := weilTest_doublePair_log_two (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco 1 (Or.inl rfl)
  have e2 := weilTest_doublePair_log_two (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ hco (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  rw [nodeVector_single_test, logVector_apply, massOf_single_doublePairTestFn h₁ h₂ hco hσ₁ hσ₂]
  change logValue (doublePair m₁ m₂ σ₁ σ₂) m₂ = _
  have e : ((1 + σ₁ ^ 2 : ℝ) : ℂ) * ((σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) =
      (((1 + σ₁ ^ 2) * (σ₂ * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [logValue, e1, e2, e, ← Complex.ofReal_add, Complex.ofReal_re, hσ₁]
  ring

include h₁ h₂ in
/-- **The cross node is charged.** At the composite node `m₁m₂` the double pair carries
`L_{m₁m₂} = 2σ₁σ₂ ∫h²/√(m₁m₂) = σ₁σ₂ ‖·‖²/(2√(m₁m₂))`; it is free only because `Λ(m₁m₂) = 0`. -/
theorem logValue_doublePair_mul :
    logValue (doublePair m₁ m₂ σ₁ σ₂) (m₁ * m₂) =
      2 * (σ₁ * σ₂ * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2) / Real.sqrt ((m₁ * m₂ : ℕ) : ℝ) := by
  have e1 := weilTest_doublePair_log_mul (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ 1 (Or.inl rfl)
  have e2 := weilTest_doublePair_log_mul (σ₁ := σ₁) (σ₂ := σ₂) h₁ h₂ (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul] at e2
  have e : (σ₁ : ℂ) * ((σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ)) =
      ((σ₁ * σ₂ * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ) := by push_cast; ring
  rw [logValue, log_natCast_mul (by omega) (by omega), e1, e2, e, ← Complex.ofReal_add,
    Complex.ofReal_re]
  ring

include h₁ h₂ hco in
/-- The double pair is blind at every prime power other than `m₁`, `m₂`. -/
theorem blindOn_single_doublePairTestFn :
    BlindOn (primePowerNodes \ {m₁, m₂}) (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) := by
  intro j hj
  obtain ⟨hpp, hne⟩ := hj
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  rw [nodeVector_single_test, logVector_apply]
  exact logValue_doublePair_eq_zero h₁ h₂ hco j.2 hne.1 hne.2
    fun h => not_isPrimePow_mul_of_coprime hco h₁ h₂ (h ▸ hpp)

end DoublePairNodes

/-! ### 6. Two deleted nodes -/

/-- **The two-node deletion identity.** On the cone blind at every prime power except `m₁ ≠ m₂`,
`A(c) = W(c) + Λ(m₁)L_{m₁}(c) + Λ(m₂)L_{m₂}(c)`. -/
theorem nodeArchEnergy_eq_weilEnergy_add_two {c : WeilTestFn →₀ ℝ} {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁)
    (h₂ : 2 ≤ m₂) (h₁₂ : m₁ ≠ m₂) (hb : BlindOn (primePowerNodes \ {m₁, m₂}) c) :
    nodeArchEnergy c = weilEnergy c +
      (ArithmeticFunction.vonMangoldt m₁ * nodeVector c ⟨m₁, h₁⟩ +
        ArithmeticFunction.vonMangoldt m₂ * nodeVector c ⟨m₂, h₂⟩) := by
  classical
  set a₁ : LogIndex := ⟨m₁, h₁⟩
  set a₂ : LogIndex := ⟨m₂, h₂⟩
  have ha : a₁ ≠ a₂ := fun h => h₁₂ (congrArg Subtype.val h)
  set g : LogIndex → ℝ := fun j => nodeVector c j • (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)
  have hg : ∀ j, j ≠ a₁ → j ≠ a₂ → g j = 0 := by
    intro j hj1 hj2
    by_cases hp : IsPrimePow (j : ℕ)
    · have : (j : ℕ) ∈ primePowerNodes \ {m₁, m₂} := ⟨hp, by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun h => hj1 (Subtype.ext h), fun h => hj2 (Subtype.ext h)⟩⟩
      simp only [g, hb j this, zero_smul]
    · simp only [g, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, smul_zero]
  rw [nodeArchEnergy_eq_weilEnergy_add, linearCombination_apply, Finsupp.sum]
  congr 1
  change ∑ j ∈ (nodeVector c).support, g j = _
  have hs1 : ∑ j ∈ (nodeVector c).support, g j =
      ∑ j ∈ (nodeVector c).support ∪ {a₁, a₂}, g j :=
    Finset.sum_subset Finset.subset_union_left fun j _ hj => by
      simp only [g, Finsupp.notMem_support_iff.mp hj, zero_smul]
  have hs2 : ∑ j ∈ ({a₁, a₂} : Finset LogIndex), g j =
      ∑ j ∈ (nodeVector c).support ∪ {a₁, a₂}, g j :=
    Finset.sum_subset Finset.subset_union_right fun j _ hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hg j hj.1 hj.2
  rw [hs1, ← hs2, Finset.sum_pair ha]
  simp only [g, smul_eq_mul, a₁, a₂]
  ring

/-- **Additive upper bound.** On the cone blind at every prime power except the coprime prime
powers `m₁`, `m₂`: `|A − W| ≤ (Λ(m₁)/√m₁ + Λ(m₂)/√m₂) ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_two {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    {m₁ m₂ : ℕ} (hm₁ : IsPrimePow m₁) (hm₂ : IsPrimePow m₂) (hco : Nat.Coprime m₁ m₂)
    (hb : BlindOn (primePowerNodes \ {m₁, m₂}) c) :
    |nodeArchEnergy c - weilEnergy c| ≤
      (ArithmeticFunction.vonMangoldt m₁ / Real.sqrt m₁ +
        ArithmeticFunction.vonMangoldt m₂ / Real.sqrt m₂) * massOf c := by
  have h₁ := hm₁.two_le
  have h₂ := hm₂.two_le
  have h₁₂ : m₁ ≠ m₂ := by simpa using mul_ne_of_coprime hco h₁ 1
  -- the tower of each deleted node stays blind
  have tower : ∀ {m m' : ℕ}, IsPrimePow m → Nat.Coprime m m' → 2 ≤ m →
      BlindOn (primePowerNodes \ {m, m'}) c → ∀ j : LogIndex,
        (∃ k : ℕ, 2 ≤ k ∧ (j : ℕ) = m ^ k) → nodeVector c j = 0 := by
    intro m m' hm hmm' h2 hb' j ⟨k, hk, hj⟩
    refine hb' j ⟨hj ▸ (pow_mem_primePowerNodes_diff hm hk).1, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h => (pow_mem_primePowerNodes_diff hm hk).2 (hj ▸ h), fun h => ?_⟩
    have hdvd : m ∣ m' := ⟨m ^ (k - 1), by rw [← h, hj, ← pow_succ']; congr 1; omega⟩
    have := Nat.Coprime.eq_one_of_dvd hmm' hdvd
    omega
  have hb₂ : BlindOn (primePowerNodes \ {m₂, m₁}) c := by rwa [Set.pair_comm]
  have f₁ := abs_nodeVector_le_massOf_div_sqrt hc h₁ (tower hm₁ hco h₁ hb)
  have f₂ := abs_nodeVector_le_massOf_div_sqrt hc h₂ (tower hm₂ hco.symm h₂ hb₂)
  rw [nodeArchEnergy_eq_weilEnergy_add_two h₁ h₂ h₁₂ hb, add_sub_cancel_left]
  have hΛ₁ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m₁ := ArithmeticFunction.vonMangoldt_nonneg
  have hΛ₂ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m₂ := ArithmeticFunction.vonMangoldt_nonneg
  calc |ArithmeticFunction.vonMangoldt m₁ * nodeVector c ⟨m₁, h₁⟩ +
        ArithmeticFunction.vonMangoldt m₂ * nodeVector c ⟨m₂, h₂⟩|
      ≤ ArithmeticFunction.vonMangoldt m₁ * |nodeVector c ⟨m₁, h₁⟩| +
          ArithmeticFunction.vonMangoldt m₂ * |nodeVector c ⟨m₂, h₂⟩| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hΛ₁, abs_of_nonneg hΛ₂]
    _ ≤ ArithmeticFunction.vonMangoldt m₁ * (massOf c / Real.sqrt m₁) +
          ArithmeticFunction.vonMangoldt m₂ * (massOf c / Real.sqrt m₂) :=
        add_le_add (mul_le_mul_of_nonneg_left f₁ hΛ₁) (mul_le_mul_of_nonneg_left f₂ hΛ₂)
    _ = _ := by ring

/-- The normalized deviations `(A − W)/‖·‖²` on the cone blind at every prime power except `m₁`,
`m₂`. -/
def deletionDeviations₂ (m₁ m₂ : ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ {m₁, m₂}) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem deviation_single_doublePairTestFn {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂)
    (hco : Nat.Coprime m₁ m₂) {σ : ℝ} (hσ : σ ^ 2 = 1) :
    σ * (ArithmeticFunction.vonMangoldt m₁ / Real.sqrt m₁ +
      ArithmeticFunction.vonMangoldt m₂ / Real.sqrt m₂) ∈ deletionDeviations₂ m₁ m₂ := by
  classical
  have h₁₂ : m₁ ≠ m₂ := by simpa using mul_ne_of_coprime hco h₁ 1
  have hmass := massOf_single_doublePairTestFn h₁ h₂ hco hσ hσ
  have hpos : 0 < massOf (Finsupp.single (doublePairTestFn m₁ m₂ σ σ) 1) := by
    rw [hmass]; linarith [integral_narrowBump_sq_pos (m₁ * m₂)]
  refine ⟨_, fun f => ?_, blindOn_single_doublePairTestFn h₁ h₂ hco, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [nodeArchEnergy_eq_weilEnergy_add_two h₁ h₂ h₁₂ (blindOn_single_doublePairTestFn h₁ h₂ hco),
      add_sub_cancel_left, nodeVector_single_doublePairTestFn_one h₁ h₂ hco hσ hσ,
      nodeVector_single_doublePairTestFn_two h₁ h₂ hco hσ hσ]
    field_simp

/-- **Prices add across towers: the least deviation.** -/
theorem isLeast_deletionDeviations₂ {m₁ m₂ : ℕ} (hm₁ : IsPrimePow m₁) (hm₂ : IsPrimePow m₂)
    (hco : Nat.Coprime m₁ m₂) :
    IsLeast (deletionDeviations₂ m₁ m₂)
      (-(ArithmeticFunction.vonMangoldt m₁ / Real.sqrt m₁ +
        ArithmeticFunction.vonMangoldt m₂ / Real.sqrt m₂)) := by
  have hmem := deviation_single_doublePairTestFn hm₁.two_le hm₂.two_le hco
    (σ := -1) (by norm_num)
  rw [neg_one_mul] at hmem
  refine ⟨hmem, ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_two hc hm₁ hm₂ hco hb
  rw [le_div_iff₀ hpos]
  linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]

/-- **Prices add across towers: the greatest deviation.** -/
theorem isGreatest_deletionDeviations₂ {m₁ m₂ : ℕ} (hm₁ : IsPrimePow m₁) (hm₂ : IsPrimePow m₂)
    (hco : Nat.Coprime m₁ m₂) :
    IsGreatest (deletionDeviations₂ m₁ m₂)
      (ArithmeticFunction.vonMangoldt m₁ / Real.sqrt m₁ +
        ArithmeticFunction.vonMangoldt m₂ / Real.sqrt m₂) := by
  have hmem := deviation_single_doublePairTestFn hm₁.two_le hm₂.two_le hco
    (σ := 1) (by norm_num)
  rw [one_mul] at hmem
  refine ⟨hmem, ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_two hc hm₁ hm₂ hco hb
  rw [div_le_iff₀ hpos]
  linarith [le_abs_self (nodeArchEnergy c - weilEnergy c)]

/-- Deleting `log 2` and `log 3` together costs `log 2/√2 + log 3/√3`; the attaining double pair
charges the composite node `log 6`. -/
theorem isLeast_deletionDeviations₂_two_three :
    IsLeast (deletionDeviations₂ 2 3)
      (-(Real.log 2 / Real.sqrt 2 + Real.log 3 / Real.sqrt 3)) := by
  have h := isLeast_deletionDeviations₂ (m₁ := 2) (m₂ := 3) Nat.prime_two.isPrimePow
    Nat.prime_three.isPrimePow (by norm_num)
  rwa [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three, Nat.cast_ofNat,
    Nat.cast_ofNat] at h

end

end GaloisForLFunctions.BiScaleUncertainty
