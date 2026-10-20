import GaloisForLFunctions.BiScaleUncertainty.PrimePowerNodeDeletionPrice

/-!
# Deletion prices add across towers, and the composite node pays nothing

`PrimePowerNodeDeletionPrice` shows that deleting one prime power `m` from the prime-power blind
cone moves the archimedean energy against the Weil functional by exactly `±Λ(m)/√m` per unit mass.
Here two prime powers `m₁`, `m₂` of different primes (`gcd(m₁, m₂) = 1`) are deleted together.

**Theorem** (`isLeast_deletionDeviations₂`, `isGreatest_deletionDeviations₂`). On the combinations
blind at every prime power except `m₁` and `m₂`, the exact range of `(A − W)/‖c‖²` is

`[−(Λ(m₁)/√m₁ + Λ(m₂)/√m₂), Λ(m₁)/√m₁ + Λ(m₂)/√m₂]`:

the prices add. For `{2, 3}` the price is `log 2/√2 + log 3/√3` (`isLeast_deletionDeviations₂_two_three`).

**Mechanism.**
* Upper bound: `A − W = Λ(m₁)L_{m₁} + Λ(m₂)L_{m₂}` and the tower Fejér bound applies to each node
  separately, because the powers `m_i^k`, `k ≥ 2`, are prime powers different from both deleted nodes.
* Attainment: the double pair `b ∗ (δ₀ + σ₁δ_{log m₁}) ∗ (δ₀ + σ₂δ_{log m₂})` of a narrow bump puts
  the extremal correlation `σ_i/2` at both `log m_i` at once. Its only other integer lag is the cross
  lag `log(m₁m₂)`, where it carries the node value `σ₁σ₂ ‖·‖²/(2√(m₁m₂))`
  (`nodeVector_single_doublePairTestFn_mul`). The cone does not ask for blindness there because
  `m₁m₂` is not a prime power: deleting `{2, 3}` charges `log 6`, and `Λ(6) = 0` makes it free.

So additivity across towers is exactly the redundancy of the composite nodes. On the integer-grid
blind cone the cross node would have to be blind as well, and the double pair is not admissible.
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

/-- The double pair `b ∗ (δ₀ + σ₁δ_{log m₁}) ∗ (δ₀ + σ₂δ_{log m₂})` with the narrow bump of index
`m₁m₂`. -/
def doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : ℝ → ℂ :=
  pairOf (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) (Real.log m₁) σ₁

theorem contDiff_doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : ContDiff ℝ 2 (doublePair m₁ m₂ σ₁ σ₂) :=
  contDiff_pairOf (contDiff_pairOf ((contDiff_narrowBumpC _).of_le (by norm_cast)) _ _) _ _

theorem hasCompactSupport_doublePair (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) :
    HasCompactSupport (doublePair m₁ m₂ σ₁ σ₂) :=
  hasCompactSupport_pairOf (hasCompactSupport_pairOf (hasCompactSupport_narrowBumpC _) _ _) _ _

/-- The double pair as a Weil test. -/
def doublePairTestFn (m₁ m₂ : ℕ) (σ₁ σ₂ : ℝ) : WeilTestFn :=
  ⟨doublePair m₁ m₂ σ₁ σ₂, contDiff_doublePair m₁ m₂ σ₁ σ₂, hasCompactSupport_doublePair m₁ m₂ σ₁ σ₂⟩

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

section Computation

variable {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) (hco : Nat.Coprime m₁ m₂)
  {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ^ 2 = 1) (hσ₂ : σ₂ ^ 2 = 1)

include h₁ h₂ in
/-- Every gap the computation uses exceeds the correlation radius `1/(2(m₁m₂+1))` of the bump. -/
theorem radius_lt_abs_log_sub {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hbj : b ≤ m₁ * m₂)
    (hab : a ≠ b) : 1 / (2 * (((m₁ * m₂ : ℕ) : ℝ) + 1)) < |Real.log a - Real.log b| := by
  refine lt_of_lt_of_le ?_ (WeilExcess.inv_succ_le_abs_log_sub ha hb hab)
  have hb' : (b : ℝ) ≤ ((m₁ * m₂ : ℕ) : ℝ) := by exact_mod_cast hbj
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem radius_lt_of_log_two_le (j : ℕ) {t : ℝ} (ht : Real.log 2 ≤ |t|) :
    1 / (2 * ((j : ℝ) + 1)) < |t| := by
  refine lt_of_le_of_lt ?_ (lt_of_lt_of_le WeilExcess.seventeen_div_twentyfive_lt_log_two ht)
  rw [div_le_iff₀ (by positivity)]
  nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]

theorem lt_abs_of_eq_or_eq_neg {δ X Y : ℝ} (h : δ < |Y|) (e : X = Y ∨ X = -Y) : δ < |X| := by
  rcases e with rfl | rfl
  · exact h
  · rwa [abs_neg]

/-- The autocorrelation of the inner pair `h(u) + σ₂ h(u − log m₂)`. -/
theorem weilTest_innerPair (t : ℝ) :
    EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
        (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) t =
      ((1 + σ₂ ^ 2 : ℝ) : ℂ) * EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) t +
        (σ₂ : ℂ) * (EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) (t + Real.log m₂) +
          EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) (t - Real.log m₂)) :=
  weilTest_pairOf (contDiff_narrowBumpC _).continuous (hasCompactSupport_narrowBumpC _) _ _ t

/-- The autocorrelation of the double pair through the inner pair. -/
theorem weilTest_doublePair (y : ℝ) :
    EF.weilTest (doublePair m₁ m₂ σ₁ σ₂) (doublePair m₁ m₂ σ₁ σ₂) y =
      ((1 + σ₁ ^ 2 : ℝ) : ℂ) * EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
          (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) y +
        (σ₁ : ℂ) * (EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
            (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) (y + Real.log m₁) +
          EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
            (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) (y - Real.log m₁)) :=
  weilTest_pairOf (continuous_pairOf (contDiff_narrowBumpC _).continuous _ _)
    (hasCompactSupport_pairOf (hasCompactSupport_narrowBumpC _) _ _) _ _ y

/-- The inner pair vanishes away from the lags `0, ±log m₂`. -/
theorem weilTest_innerPair_eq_zero {t : ℝ} (h0 : 1 / (2 * (((m₁ * m₂ : ℕ) : ℝ) + 1)) < |t|)
    (h1 : 1 / (2 * (((m₁ * m₂ : ℕ) : ℝ) + 1)) < |t + Real.log m₂|)
    (h2 : 1 / (2 * (((m₁ * m₂ : ℕ) : ℝ) + 1)) < |t - Real.log m₂|) :
    EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
      (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) t = 0 := by
  rw [weilTest_innerPair, weilTest_narrowBumpC_eq_zero _ h0, weilTest_narrowBumpC_eq_zero _ h1,
    weilTest_narrowBumpC_eq_zero _ h2]
  ring

include h₂ in
/-- At the origin the inner pair is `(1 + σ₂²) ∫ h²`. -/
theorem weilTest_innerPair_zero :
    EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
      (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) 0 =
      ((1 + σ₂ ^ 2 : ℝ) : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ) := by
  have hl : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have hp : Real.log 2 ≤ |Real.log m₂| := by rw [abs_of_pos (by linarith)]; exact hl
  have hn : Real.log 2 ≤ |-Real.log m₂| := by rw [abs_neg]; exact hp
  rw [weilTest_innerPair, zero_add, zero_sub, weilTest_narrowBumpC_zero,
    weilTest_narrowBumpC_eq_zero _ (radius_lt_of_log_two_le _ hp),
    weilTest_narrowBumpC_eq_zero _ (radius_lt_of_log_two_le _ hn)]
  ring

include h₂ in
/-- At `±log m₂` the inner pair is `σ₂ ∫ h²`. -/
theorem weilTest_innerPair_pm_log (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂)
      (pairOf (narrowBumpC (m₁ * m₂)) (Real.log m₂) σ₂) (s * Real.log m₂) =
      (σ₂ : ℂ) * ((∫ t, (narrowBump (m₁ * m₂) t) ^ 2 : ℝ) : ℂ) := by
  have hl : Real.log 2 ≤ Real.log m₂ := Real.log_le_log two_pos (by exact_mod_cast h₂)
  have hl2 := Real.log_pos one_lt_two
  have hbig : ∀ t : ℝ, Real.log 2 ≤ |t| →
      EF.weilTest (narrowBumpC (m₁ * m₂)) (narrowBumpC (m₁ * m₂)) t = 0 :=
    fun t ht => weilTest_narrowBumpC_eq_zero _ (radius_lt_of_log_two_le _ ht)
  rw [weilTest_innerPair]
  rcases hs with rfl | rfl
  · rw [one_mul, sub_self, weilTest_narrowBumpC_zero, hbig _ (by rw [abs_of_pos (by linarith)]; linarith),
      hbig _ (by rw [abs_of_pos (by linarith)]; linarith)]
    ring
  · rw [show -1 * Real.log m₂ + Real.log m₂ = 0 by ring, weilTest_narrowBumpC_zero,
      hbig (-1 * Real.log m₂) (by rw [neg_one_mul, abs_neg, abs_of_pos (by linarith)]; linarith),
      hbig (-1 * Real.log m₂ - Real.log m₂) (by
        rw [show -1 * Real.log m₂ - Real.log m₂ = -(2 * Real.log m₂) by ring, abs_neg,
          abs_of_pos (by linarith)]; linarith)]
    ring

end Computation

end

end GaloisForLFunctions.BiScaleUncertainty
