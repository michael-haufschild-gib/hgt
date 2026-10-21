import GaloisForLFunctions.BiScaleUncertainty.PrimeTwoThreeDecouplingLength

/-!
# Composite nodes are free on the integer grid: staircase trains

`PrimePowerDeletionPriceAdditivity` deletes two prime powers `m₁ = p^e`, `m₂ = q^f` of different
primes from the prime-power blind cone; the price `w(m₁) + w(m₂)`, `w(m) = Λ(m)/√m`, is attained by
the double pair, whose cross lag `log(m₁m₂)` is free there because `m₁m₂` is not a prime power.
Here the cone is blind at **every** integer `n ≥ 2` except `m₁, m₂` (composites included).

**Theorem** (`isLUB_gridDeviations₂`, `isGLB_gridDeviations₂`). On the cone blind at every integer
`n ≥ 2` outside `{m₁, m₂}`, the deviations `(A − W)/‖c‖²` have supremum `w(m₁) + w(m₂)` and infimum
`−(w(m₁) + w(m₂))`: the same price as on the prime-power cone. Imposing blindness at the composite
nodes `m₁m₂, m₁²m₂, …` costs nothing, while imposing it at a prime power changes the price
(`PrimePowerTowerDeletionInteraction`): for `{2, 3}`, blindness at `log 6` is free and blindness at
`log 4` is not.

**Mechanism.** The staircase train has narrow bumps at `k log(m₂/m₁)` and `k log(m₂/m₁) + log m₁`,
`0 ≤ k ≤ M`, with signs `τ^k` and `στ^k`. In the exponent lattice of `(m₁, m₂)` its positions lie on
the slab of coordinate sum `0` and `1`; a lag `log n` with `n ≥ 2` integer needs nonnegative
exponents of coordinate sum one, so the only integer lags are `log m₁` (the `M + 1` rungs) and
`log m₂` (the `M` steps), and every composite `m₁^i m₂^j`, `i + j ≥ 2`, is avoided
(`staircase_lag_cases`). The node values are `(M+1)σ` and `Mστ` against mass `2(M+1)`, so the
deviation is `σ w(m₁) + στ w(m₂) M/(M+1)`. The double pair, the only kind of attaining test, lives on
the cube `{0,1}²` and charges `log(m₁m₂)` (`not_gridBlind_doublePair`); the staircase gives up
attainment and keeps the price.
-/

open MeasureTheory Set Complex Finsupp Filter
open Zeta23
open RHTower RHTower.WeilOneSided

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. The integer-grid deletion cone -/

/-- The deviations `(A − W)/‖c‖²` on the cone blind at every integer `n ≥ 2` outside `{m₁, m₂}`. -/
def gridDeviations₂ (m₁ m₂ : ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn ({n | 2 ≤ n} \ {m₁, m₂}) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem gridDeviations₂_subset (m₁ m₂ : ℕ) : gridDeviations₂ m₁ m₂ ⊆ deletionDeviations₂ m₁ m₂ := by
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  exact ⟨c, hc, fun j hj => hb j ⟨j.2, hj.2⟩, hpos, rfl⟩

/-! ### 2. Lags of the staircase -/

section Staircase

variable {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (he : 1 ≤ e) (hf : 1 ≤ f)

/-- The numerator `m₂^{k_a} m₁^{ε_a + k_b}` of the lag between `(k_a, ε_a)` and `(k_b, ε_b)`. -/
def stairNum (m₁ m₂ : ℕ) (a b : ℕ × ℕ) : ℕ := m₂ ^ a.1 * m₁ ^ (a.2 + b.1)

/-- The denominator `m₁^{k_a + ε_b} m₂^{k_b}`. -/
def stairDen (m₁ m₂ : ℕ) (a b : ℕ × ℕ) : ℕ := m₁ ^ (a.1 + b.2) * m₂ ^ b.1

/-- The position `k log(m₂/m₁) + ε log m₁` of the vertex `(k, ε)`. -/
def stairPos (m₁ m₂ : ℕ) (a : ℕ × ℕ) : ℝ :=
  a.1 * (Real.log m₂ - Real.log m₁) + a.2 * Real.log m₁

theorem stairPos_sub {m₁ m₂ : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) (a b : ℕ × ℕ) :
    stairPos m₁ m₂ a - stairPos m₁ m₂ b =
      Real.log (stairNum m₁ m₂ a b) - Real.log (stairDen m₁ m₂ a b) := by
  have h₁' : (0 : ℝ) < m₁ := by exact_mod_cast h₁
  have h₂' : (0 : ℝ) < m₂ := by exact_mod_cast h₂
  simp only [stairPos, stairNum, stairDen]
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  ring

include hp hq hpq in
/-- The `q`-adic and `p`-adic valuations of `m₂^i m₁^j`. -/
theorem factorization_stair (i j : ℕ) :
    ((q ^ f) ^ i * (p ^ e) ^ j).factorization q = f * i ∧
      ((q ^ f) ^ i * (p ^ e) ^ j).factorization p = e * j := by
  have hp0 : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hq0 : q ^ f ≠ 0 := pow_ne_zero _ hq.ne_zero
  rw [Nat.factorization_mul (pow_ne_zero _ hq0) (pow_ne_zero _ hp0), ← pow_mul, ← pow_mul,
    hp.factorization_pow, hq.factorization_pow]
  simp [hpq, Ne.symm hpq]

include hp hq hpq he hf in
/-- **The only integer lags of the staircase are `m₁` and `m₂`.** If the lag from `b` to `a` is
`log n` with `n ≥ 1`, then either `a = b` and `n = 1`, or `a = (k, 1)`, `b = (k, 0)` and `n = m₁`,
or `a = (k + 1, 1)`, `b = (k, 0)` and `n = m₂`. -/
theorem staircase_lag_cases {a b : ℕ × ℕ} (ha : a.2 < 2) (hb : b.2 < 2) {n : ℕ} (hn : 1 ≤ n)
    (h : stairNum (p ^ e) (q ^ f) a b = n * stairDen (p ^ e) (q ^ f) a b) :
    (a = b ∧ n = 1) ∨ (a.1 = b.1 ∧ a.2 = 1 ∧ b.2 = 0 ∧ n = p ^ e) ∨
      (a.1 = b.1 + 1 ∧ a.2 = 1 ∧ b.2 = 0 ∧ n = q ^ f) := by
  have hn0 : n ≠ 0 := by omega
  have hden0 : stairDen (p ^ e) (q ^ f) a b ≠ 0 := by
    simp only [stairDen]; exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))
      (pow_ne_zero _ (pow_ne_zero _ hq.ne_zero))
  have hfac := congrArg Nat.factorization h
  rw [Nat.factorization_mul hn0 hden0] at hfac
  have hq1 := congrArg (fun g => g q) hfac
  have hp1 := congrArg (fun g => g p) hfac
  simp only [Finsupp.add_apply] at hq1 hp1
  have hden : stairDen (p ^ e) (q ^ f) a b = (q ^ f) ^ b.1 * (p ^ e) ^ (a.1 + b.2) := by
    simp only [stairDen]; ring
  rw [stairNum, hden] at hq1 hp1
  rw [(factorization_stair hp hq hpq a.1 (a.2 + b.1)).1,
    (factorization_stair hp hq hpq b.1 (a.1 + b.2)).1] at hq1
  rw [(factorization_stair hp hq hpq a.1 (a.2 + b.1)).2,
    (factorization_stair hp hq hpq b.1 (a.1 + b.2)).2] at hp1
  -- `f k_a = v_q(n) + f k_b` and `e(ε_a + k_b) = v_p(n) + e(k_a + ε_b)`
  have hk : b.1 ≤ a.1 := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt (show 0 < f by omega)
    omega
  have hε : a.1 + b.2 ≤ a.2 + b.1 := by
    by_contra hlt
    push Not at hlt
    have := mul_lt_mul_of_pos_left hlt (show 0 < e by omega)
    omega
  have hden_pos : 0 < stairDen (p ^ e) (q ^ f) a b := Nat.pos_of_ne_zero hden0
  -- the three cases of `d = k_a − k_b` and `ε_a − ε_b`
  rcases Nat.lt_or_ge a.2 1 with ha0 | ha1
  · -- `ε_a = 0` forces `k_a = k_b`, `ε_b = 0`: the trivial lag
    left
    have e1 : a.1 = b.1 := by omega
    have e2 : a.2 = b.2 := by omega
    refine ⟨Prod.ext e1 e2, ?_⟩
    have hnd : stairNum (p ^ e) (q ^ f) a b = stairDen (p ^ e) (q ^ f) a b := by
      simp only [stairNum, stairDen]; rw [e1, e2]; ring
    rw [hnd] at h
    exact (Nat.eq_of_mul_eq_mul_right hden_pos (by rw [one_mul]; exact h)).symm
  · have ha2 : a.2 = 1 := by omega
    rcases Nat.lt_or_ge b.2 1 with hb0 | hb1
    · have hb2 : b.2 = 0 := by omega
      rcases Nat.lt_or_ge b.1 a.1 with hlt | hge
      · -- `k_a = k_b + 1`: the step `m₂`
        right; right
        have hk1 : a.1 = b.1 + 1 := by omega
        refine ⟨hk1, ha2, hb2, ?_⟩
        have hnd : stairNum (p ^ e) (q ^ f) a b = q ^ f * stairDen (p ^ e) (q ^ f) a b := by
          simp only [stairNum, stairDen]; rw [hk1, ha2, hb2]; ring
        rw [hnd] at h
        exact (Nat.eq_of_mul_eq_mul_right hden_pos h).symm
      · -- `k_a = k_b`: the rung `m₁`
        right; left
        have hk0 : a.1 = b.1 := by omega
        refine ⟨hk0, ha2, hb2, ?_⟩
        have hnd : stairNum (p ^ e) (q ^ f) a b = p ^ e * stairDen (p ^ e) (q ^ f) a b := by
          simp only [stairNum, stairDen]; rw [hk0, ha2, hb2]; ring
        rw [hnd] at h
        exact (Nat.eq_of_mul_eq_mul_right hden_pos h).symm
    · -- `ε_a = ε_b = 1` forces `k_a = k_b`: the trivial lag
      left
      have hb2 : b.2 = 1 := by omega
      have e1 : a.1 = b.1 := by omega
      refine ⟨Prod.ext e1 (by omega), ?_⟩
      have hnd : stairNum (p ^ e) (q ^ f) a b = stairDen (p ^ e) (q ^ f) a b := by
        simp only [stairNum, stairDen]; rw [e1, ha2, hb2]; ring
      rw [hnd] at h
      exact (Nat.eq_of_mul_eq_mul_right hden_pos (by rw [one_mul]; exact h)).symm

/-- The vertex set `{0, …, M} × {0, 1}`. -/
def stairIndex (M : ℕ) : Finset (ℕ × ℕ) := Finset.range (M + 1) ×ˢ Finset.range 2

/-- The staircase signs `τ^k σ^ε`. -/
def stairCoeff (σ τ : ℝ) (a : ℕ × ℕ) : ℝ := τ ^ a.1 * σ ^ a.2

/-- The bound `(m₁m₂)^{M+1}` on all numerators and denominators. -/
def stairBound (m₁ m₂ M : ℕ) : ℕ := (m₁ * m₂) ^ (M + 1)

theorem stairNum_le {m₁ m₂ M : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) {a b : ℕ × ℕ}
    (ha : a ∈ stairIndex M) (hb : b ∈ stairIndex M) : stairNum m₁ m₂ a b ≤ stairBound m₁ m₂ M := by
  simp only [stairIndex, Finset.mem_product, Finset.mem_range] at ha hb
  simp only [stairNum, stairBound, mul_pow]
  rw [mul_comm]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right h₁ (by omega)) (Nat.pow_le_pow_right h₂ (by omega))

theorem stairDen_le {m₁ m₂ M : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) {a b : ℕ × ℕ}
    (ha : a ∈ stairIndex M) (hb : b ∈ stairIndex M) : stairDen m₁ m₂ a b ≤ stairBound m₁ m₂ M := by
  simp only [stairIndex, Finset.mem_product, Finset.mem_range] at ha hb
  simp only [stairDen, stairBound, mul_pow]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right h₁ (by omega)) (Nat.pow_le_pow_right h₂ (by omega))

theorem stairNum_pos {m₁ m₂ : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) (a b : ℕ × ℕ) :
    1 ≤ stairNum m₁ m₂ a b := Nat.one_le_iff_ne_zero.mpr (by
  simp only [stairNum]; exact mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))

theorem stairDen_pos {m₁ m₂ : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂) (a b : ℕ × ℕ) :
    1 ≤ stairDen m₁ m₂ a b := Nat.one_le_iff_ne_zero.mpr (by
  simp only [stairDen]; exact mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))

/-- **Separation of the lags** at `±log n` for a bump of index `N ≥ (m₁m₂)^{M+1}`. -/
theorem staircase_sep {m₁ m₂ M N : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂)
    (hN : stairBound m₁ m₂ M ≤ N) {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∀ a ∈ stairIndex M, ∀ b ∈ stairIndex M,
      stairPos m₁ m₂ a - stairPos m₁ m₂ b ≠ s * Real.log n →
        1 / (2 * ((N : ℝ) + 1)) < |s * Real.log n - stairPos m₁ m₂ a + stairPos m₁ m₂ b| := by
  intro a ha b hb hne
  have hN' : (stairBound m₁ m₂ M : ℝ) ≤ N := by exact_mod_cast hN
  have hU := stairNum_pos h₁ h₂ a b
  have hV := stairDen_pos h₁ h₂ a b
  have hUB0 : (stairNum m₁ m₂ a b : ℝ) ≤ stairBound m₁ m₂ M := by
    exact_mod_cast stairNum_le h₁ h₂ ha hb
  have hVB0 : (stairDen m₁ m₂ a b : ℝ) ≤ stairBound m₁ m₂ M := by
    exact_mod_cast stairDen_le h₁ h₂ ha hb
  have hUB := hUB0.trans hN'
  have hVB := hVB0.trans hN'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hrad : ∀ X : ℕ, (X : ℝ) ≤ N → 1 / (2 * ((N : ℝ) + 1)) < 1 / ((X : ℝ) + 1) := by
    intro X hX
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ N := by positivity
    linarith
  rw [stairPos_sub h₁ h₂] at hne
  rw [show s * Real.log n - stairPos m₁ m₂ a + stairPos m₁ m₂ b =
    s * Real.log n - (stairPos m₁ m₂ a - stairPos m₁ m₂ b) by ring, stairPos_sub h₁ h₂]
  rcases hs with rfl | rfl
  · rw [one_mul] at hne ⊢
    have hne' : n * stairDen m₁ m₂ a b ≠ stairNum m₁ m₂ a b := by
      intro h
      apply hne
      rw [← h]; push_cast
      rw [Real.log_mul hn'.ne' (by positivity)]; ring
    have := RHTower.WeilExcess.inv_succ_le_abs_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity))
      hU hne'
    refine (hrad _ hUB).trans_le (this.trans (le_of_eq ?_))
    push_cast
    rw [Real.log_mul hn'.ne' (by positivity)]; ring_nf
  · rw [neg_one_mul] at hne ⊢
    have hne' : n * stairNum m₁ m₂ a b ≠ stairDen m₁ m₂ a b := by
      intro h
      apply hne
      have : Real.log (stairDen m₁ m₂ a b) = Real.log n + Real.log (stairNum m₁ m₂ a b) := by
        rw [← h]; push_cast; rw [Real.log_mul hn'.ne' (by positivity)]
      rw [this]; ring
    have := RHTower.WeilExcess.inv_succ_le_abs_log_sub (Nat.one_le_iff_ne_zero.mpr (by positivity))
      hV hne'
    refine (hrad _ hVB).trans_le (this.trans (le_of_eq ?_))
    push_cast
    rw [Real.log_mul hn'.ne' (by positivity), abs_sub_comm]; ring_nf

/-! ### 3. The staircase train -/

/-- The staircase train `Σ_{(k,ε)} τ^k σ^ε h_N(u − k log(m₂/m₁) − ε log m₁)`. -/
def staircase (m₁ m₂ M N : ℕ) (σ τ : ℝ) (u : ℝ) : ℂ :=
  ∑ a ∈ stairIndex M, ((stairCoeff σ τ a : ℝ) : ℂ) * narrowBumpC N (u - stairPos m₁ m₂ a)

theorem contDiff_staircase (m₁ m₂ M N : ℕ) (σ τ : ℝ) : ContDiff ℝ 2 (staircase m₁ m₂ M N σ τ) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (((contDiff_narrowBumpC _).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_staircase (m₁ m₂ M N : ℕ) (σ τ : ℝ) :
    HasCompactSupport (staircase m₁ m₂ M N σ τ) :=
  hasCompactSupport_finsetSum _ fun _ _ =>
    ((hasCompactSupport_narrowBumpC _).comp_homeomorph (Homeomorph.subRight _)).mul_left

/-- The staircase as a Weil test. -/
def staircaseTestFn (m₁ m₂ M N : ℕ) (σ τ : ℝ) : WeilTestFn :=
  ⟨staircase m₁ m₂ M N σ τ, contDiff_staircase m₁ m₂ M N σ τ,
    hasCompactSupport_staircase m₁ m₂ M N σ τ⟩

/-- The lag coefficient of the staircase at `y`. -/
def stairLagCoeff (m₁ m₂ M : ℕ) (σ τ y : ℝ) : ℝ :=
  ∑ a ∈ stairIndex M, ∑ b ∈ stairIndex M,
    if stairPos m₁ m₂ a - stairPos m₁ m₂ b = y then stairCoeff σ τ a * stairCoeff σ τ b else 0

theorem weilTest_staircase {m₁ m₂ M N : ℕ} (h₁ : 1 ≤ m₁) (h₂ : 1 ≤ m₂)
    (hN : stairBound m₁ m₂ M ≤ N) {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) (σ τ : ℝ) :
    EF.weilTest (staircase m₁ m₂ M N σ τ) (staircase m₁ m₂ M N σ τ) (s * Real.log n) =
      (stairLagCoeff m₁ m₂ M σ τ (s * Real.log n) : ℂ) *
        ((∫ t, (narrowBump N t) ^ 2 : ℝ) : ℂ) :=
  weilTest_train_select _ (stairCoeff σ τ) (stairPos m₁ m₂) N _
    (staircase_sep h₁ h₂ hN hn s hs)

include hp hq in
/-- The lag `log n` occurs exactly when the numerator is `n` times the denominator. -/
theorem stairPos_sub_eq_log_iff {a b : ℕ × ℕ} {n : ℕ} (hn : 1 ≤ n) :
    stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log n ↔
      stairNum (p ^ e) (q ^ f) a b = n * stairDen (p ^ e) (q ^ f) a b := by
  have h₁ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have h₂ : 1 ≤ q ^ f := Nat.one_le_pow _ _ hq.pos
  have hU := stairNum_pos h₁ h₂ a b
  have hV := stairDen_pos h₁ h₂ a b
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [stairPos_sub h₁ h₂, sub_eq_iff_eq_add, ← Real.log_mul hn'.ne' (by positivity)]
  constructor
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < stairNum _ _ a b))
      (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < n * stairDen _ _ a b)) h
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring_nf

include hp hq hpq he hf in
/-- The diagonal coefficient is the number of vertices. -/
theorem stairLagCoeff_zero {M : ℕ} {σ τ : ℝ} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    stairLagCoeff (p ^ e) (q ^ f) M σ τ (Real.log (1 : ℕ)) = 2 * (M + 1) := by
  classical
  unfold stairLagCoeff
  have key : ∀ a ∈ stairIndex M, (∑ b ∈ stairIndex M,
      if stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log (1 : ℕ) then
        stairCoeff σ τ a * stairCoeff σ τ b else 0) = 1 := by
    intro a ha
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log (1 : ℕ) ↔ b = a from ?_)
        rfl rfl, Finset.sum_ite_eq' _ a, if_pos ha]
    · simp only [stairCoeff]
      rw [← mul_mul_mul_comm, ← pow_add, ← pow_add, ← two_mul, ← two_mul, pow_mul, pow_mul, hτ, hσ]
      simp
    · have hb' := (Finset.mem_product.mp hb).2
      have ha' := (Finset.mem_product.mp ha).2
      rw [stairPos_sub_eq_log_iff hp hq le_rfl]
      constructor
      · intro h
        rcases staircase_lag_cases hp hq hpq he hf (Finset.mem_range.mp ha')
            (Finset.mem_range.mp hb') le_rfl h with ⟨hab, -⟩ | ⟨-, -, -, h1⟩ | ⟨-, -, -, h1⟩
        · exact hab.symm
        · exact absurd h1 (Nat.one_lt_pow (by omega) hp.one_lt).ne
        · exact absurd h1 (Nat.one_lt_pow (by omega) hq.one_lt).ne
      · rintro rfl; simp [stairNum, stairDen]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul, mul_one, stairIndex,
    Finset.card_product, Finset.card_range, Finset.card_range]
  push_cast; ring

end Staircase

/-- Reversing the lag reverses the pair. -/
theorem stairLagCoeff_neg (m₁ m₂ M : ℕ) (σ τ y : ℝ) :
    stairLagCoeff m₁ m₂ M σ τ (-y) = stairLagCoeff m₁ m₂ M σ τ y := by
  unfold stairLagCoeff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : stairPos m₁ m₂ a - stairPos m₁ m₂ b = y
  · rw [if_pos h, if_pos (by linarith), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (by linarith)]

theorem stairCoeff_rung {σ τ : ℝ} (hτ : τ ^ 2 = 1) (k : ℕ) :
    stairCoeff σ τ (k, 1) * stairCoeff σ τ (k, 0) = σ := by
  simp only [stairCoeff, pow_one, pow_zero, mul_one]
  rw [mul_comm (τ ^ k) σ, mul_assoc, ← pow_add, ← two_mul, pow_mul, hτ, one_pow, mul_one]

theorem stairCoeff_step {σ τ : ℝ} (hτ : τ ^ 2 = 1) (k : ℕ) :
    stairCoeff σ τ (k + 1, 1) * stairCoeff σ τ (k, 0) = σ * τ := by
  simp only [stairCoeff, pow_one, pow_zero, mul_one]
  rw [pow_succ, show τ ^ k * τ * σ * τ ^ k = σ * τ * (τ ^ k) ^ 2 by ring, ← pow_mul, mul_comm k 2,
    pow_mul, hτ, one_pow, mul_one]

/-- `Σ_{a ∈ {0..M} × {0,1}} [a.2 = 1 ∧ P a.1] g = Σ_{k ≤ M} [P k] g`. -/
theorem sum_stairIndex_ite (M : ℕ) (P : ℕ → Prop) [DecidablePred P] (g : ℝ) :
    (∑ a ∈ stairIndex M, if a.2 = 1 ∧ P a.1 then g else 0) =
      ∑ k ∈ Finset.range (M + 1), if P k then g else 0 := by
  rw [stairIndex, Finset.sum_product]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Finset.sum_range_succ]

section Values

variable {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (he : 1 ≤ e) (hf : 1 ≤ f)
  {σ τ : ℝ} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1)

omit hf in
include hp hq hpq he in
theorem pow_ne_pow_of_prime_ne : p ^ e ≠ q ^ f := fun h =>
  hpq (eq_of_prime_pow_eq hp hq he h).1

omit hσ in
include hp hq hpq he hf hτ in
/-- **The rungs.** The coefficient at `log m₁` is `(M+1)σ`. -/
theorem stairLagCoeff_log_one (M : ℕ) :
    stairLagCoeff (p ^ e) (q ^ f) M σ τ (Real.log ((p ^ e : ℕ) : ℝ)) = (M + 1) * σ := by
  classical
  have h2 : 2 ≤ p ^ e := (hp.isPrimePow.pow (by omega)).two_le
  have hne := pow_ne_pow_of_prime_ne (f := f) hp hq hpq he
  unfold stairLagCoeff
  have key : ∀ a ∈ stairIndex M, (∑ b ∈ stairIndex M,
      if stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log ((p ^ e : ℕ) : ℝ) then
        stairCoeff σ τ a * stairCoeff σ τ b else 0) = if a.2 = 1 ∧ True then σ else 0 := by
    intro a ha
    have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have ha1 := Finset.mem_range.mp (Finset.mem_product.mp ha).1
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log ((p ^ e : ℕ) : ℝ) ↔
          a.2 = 1 ∧ b = (a.1, 0) from ?_) rfl rfl]
    · by_cases h1 : a.2 = 1
      · simp only [h1, true_and, and_true, if_true]
        simp only [Finset.sum_ite_eq']
        rw [if_pos (show (a.1, 0) ∈ stairIndex M by
          simp only [stairIndex, Finset.mem_product, Finset.mem_range]; omega)]
        have : a = (a.1, 1) := Prod.ext rfl h1
        rw [this]; exact stairCoeff_rung hτ a.1
      · simp [h1]
    · have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      rw [stairPos_sub_eq_log_iff hp hq (by omega)]
      constructor
      · intro h
        rcases staircase_lag_cases hp hq hpq he hf ha2 hb2 (by omega) h with
          ⟨-, h1⟩ | ⟨hk, h1, h2', -⟩ | ⟨-, -, -, h1⟩
        · omega
        · exact ⟨h1, Prod.ext hk.symm h2'⟩
        · exact absurd h1.symm (by simpa [eq_comm] using hne)
      · rintro ⟨h1, rfl⟩
        simp only [stairNum, stairDen, h1]; ring
  rw [Finset.sum_congr rfl key, sum_stairIndex_ite M (fun _ => True) σ]
  simp

omit hσ in
include hp hq hpq he hf hτ in
/-- **The steps.** The coefficient at `log m₂` is `Mστ`. -/
theorem stairLagCoeff_log_two (M : ℕ) :
    stairLagCoeff (p ^ e) (q ^ f) M σ τ (Real.log ((q ^ f : ℕ) : ℝ)) = M * (σ * τ) := by
  classical
  have h2 : 2 ≤ q ^ f := (hq.isPrimePow.pow (by omega)).two_le
  have hne := pow_ne_pow_of_prime_ne (f := f) hp hq hpq he
  unfold stairLagCoeff
  have key : ∀ a ∈ stairIndex M, (∑ b ∈ stairIndex M,
      if stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log ((q ^ f : ℕ) : ℝ) then
        stairCoeff σ τ a * stairCoeff σ τ b else 0) = if a.2 = 1 ∧ 1 ≤ a.1 then σ * τ else 0 := by
    intro a ha
    have ha2 := Finset.mem_range.mp (Finset.mem_product.mp ha).2
    have ha1 := Finset.mem_range.mp (Finset.mem_product.mp ha).1
    rw [Finset.sum_congr rfl fun b hb => if_congr (show
        stairPos (p ^ e) (q ^ f) a - stairPos (p ^ e) (q ^ f) b = Real.log ((q ^ f : ℕ) : ℝ) ↔
          (a.2 = 1 ∧ 1 ≤ a.1) ∧ b = (a.1 - 1, 0) from ?_) rfl rfl]
    · by_cases h1 : a.2 = 1 ∧ 1 ≤ a.1
      · simp only [h1, true_and, if_true]
        simp only [Finset.sum_ite_eq']
        rw [if_pos (show (a.1 - 1, 0) ∈ stairIndex M by
          simp only [stairIndex, Finset.mem_product, Finset.mem_range]; omega)]
        have : a = (a.1 - 1 + 1, 1) := Prod.ext (by omega) h1.1
        rw [this]; exact stairCoeff_step hτ (a.1 - 1)
      · simp [h1]
    · have hb2 := Finset.mem_range.mp (Finset.mem_product.mp hb).2
      rw [stairPos_sub_eq_log_iff hp hq (by omega)]
      constructor
      · intro h
        rcases staircase_lag_cases hp hq hpq he hf ha2 hb2 (by omega) h with
          ⟨-, h1⟩ | ⟨-, -, -, h1⟩ | ⟨hk, h1, h2', -⟩
        · omega
        · exact absurd h1 (by simpa using hne.symm)
        · exact ⟨⟨h1, by omega⟩, Prod.ext (by omega) h2'⟩
      · rintro ⟨⟨h1, h1'⟩, rfl⟩
        have hk : a.1 = a.1 - 1 + 1 := by omega
        simp only [stairNum, stairDen, h1]
        rw [hk]; simp only [Nat.add_sub_cancel]; ring
  rw [Finset.sum_congr rfl key, sum_stairIndex_ite M (fun k => 1 ≤ k) (σ * τ),
    Finset.sum_range_succ', if_neg (by norm_num), add_zero]
  simp only [show ∀ i : ℕ, (1 ≤ i + 1) = True from fun i => eq_true (by omega), if_true,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]

include hp hq hpq he hf in
/-- **No other integer lag.** At every `n ≥ 2` other than `m₁`, `m₂` the coefficient vanishes. -/
theorem stairLagCoeff_log_eq_zero (M : ℕ) {n : ℕ} (hn : 2 ≤ n) (h₁ : n ≠ p ^ e) (h₂ : n ≠ q ^ f) :
    stairLagCoeff (p ^ e) (q ^ f) M σ τ (Real.log n) = 0 := by
  unfold stairLagCoeff
  refine Finset.sum_eq_zero fun a ha => Finset.sum_eq_zero fun b hb => if_neg fun h => ?_
  rw [stairPos_sub_eq_log_iff hp hq (by omega)] at h
  rcases staircase_lag_cases hp hq hpq he hf (Finset.mem_range.mp (Finset.mem_product.mp ha).2)
      (Finset.mem_range.mp (Finset.mem_product.mp hb).2) (by omega) h with
    ⟨-, h1⟩ | ⟨-, -, -, h1⟩ | ⟨-, -, -, h1⟩
  · omega
  · exact h₁ h1
  · exact h₂ h1

end Values

/-! ### 4. The staircase on the integer-grid cone -/

section Deviation

variable {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (he : 1 ≤ e) (hf : 1 ≤ f)
  {M N : ℕ} (hN : stairBound (p ^ e) (q ^ f) M ≤ N) {σ τ : ℝ} (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1)

include hp hq hN in
theorem logValue_staircase {n : ℕ} (hn : 1 ≤ n) :
    logValue (staircase (p ^ e) (q ^ f) M N σ τ) n =
      2 * stairLagCoeff (p ^ e) (q ^ f) M σ τ (Real.log n) * (∫ t, (narrowBump N t) ^ 2) /
        Real.sqrt n := by
  have h₁ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have h₂ : 1 ≤ q ^ f := Nat.one_le_pow _ _ hq.pos
  have e1 := weilTest_staircase h₁ h₂ hN hn 1 (Or.inl rfl) σ τ
  have e2 := weilTest_staircase h₁ h₂ hN hn (-1) (Or.inr rfl) σ τ
  rw [one_mul] at e1
  rw [neg_one_mul, stairLagCoeff_neg] at e2
  rw [logValue, e1, e2, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

include hp hq hpq he hf hN hσ hτ in
theorem massOf_single_staircaseTestFn :
    massOf (Finsupp.single (staircaseTestFn (p ^ e) (q ^ f) M N σ τ) 1) =
      2 * (M + 1) * ∫ t, (narrowBump N t) ^ 2 := by
  have h₁ : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
  have h₂ : 1 ≤ q ^ f := Nat.one_le_pow _ _ hq.pos
  have hk := weilTest_staircase h₁ h₂ hN le_rfl 1 (Or.inl rfl) σ τ
  rw [one_mul, stairLagCoeff_zero hp hq hpq he hf hσ hτ, Nat.cast_one, Real.log_one,
    RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm : ∫ u, ‖staircase (p ^ e) (q ^ f) M N σ τ u‖ ^ 2 =
      2 * (M + 1) * ∫ t, (narrowBump N t) ^ 2 := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact hm

include hp hq hpq he hf hN in
/-- **The staircase is blind at every integer `n ≥ 2` outside `{m₁, m₂}`**, composites included. -/
theorem gridBlind_single_staircaseTestFn :
    BlindOn ({n | 2 ≤ n} \ {p ^ e, q ^ f})
      (Finsupp.single (staircaseTestFn (p ^ e) (q ^ f) M N σ τ) 1) := by
  intro j ⟨hj2, hj⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hj
  rw [nodeVector_single_test, logVector_apply]
  change logValue (staircase (p ^ e) (q ^ f) M N σ τ) j = 0
  rw [logValue_staircase hp hq hN (by omega),
    stairLagCoeff_log_eq_zero hp hq hpq he hf M hj2 hj.1 hj.2]
  simp

include hp hq hpq he hf hN hσ hτ in
/-- **The staircase deviation**: `σ w(m₁) + στ w(m₂) M/(M+1)`. -/
theorem staircase_mem_gridDeviations₂ :
    σ * (ArithmeticFunction.vonMangoldt (p ^ e) / Real.sqrt ((p ^ e : ℕ) : ℝ)) +
        σ * τ * (ArithmeticFunction.vonMangoldt (q ^ f) / Real.sqrt ((q ^ f : ℕ) : ℝ)) *
          (M / (M + 1)) ∈ gridDeviations₂ (p ^ e) (q ^ f) := by
  classical
  have h₁ : 2 ≤ p ^ e := (hp.isPrimePow.pow (by omega)).two_le
  have h₂ : 2 ≤ q ^ f := (hq.isPrimePow.pow (by omega)).two_le
  have hne := pow_ne_pow_of_prime_ne (f := f) hp hq hpq he
  have hmass := massOf_single_staircaseTestFn hp hq hpq he hf hN hσ hτ
  have hI := integral_narrowBump_sq_pos N
  have hpos : 0 < massOf (Finsupp.single (staircaseTestFn (p ^ e) (q ^ f) M N σ τ) 1) := by
    rw [hmass]; positivity
  have hb := gridBlind_single_staircaseTestFn hp hq hpq he hf hN (σ := σ) (τ := τ)
  refine ⟨_, fun g => ?_, hb, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [nodeArchEnergy_eq_weilEnergy_add_two h₁ h₂ hne (fun j hj => hb j ⟨j.2, hj.2⟩),
      add_sub_cancel_left, nodeVector_single_test, logVector_apply, logVector_apply, hmass]
    change _ = (ArithmeticFunction.vonMangoldt (p ^ e) *
        logValue (staircase (p ^ e) (q ^ f) M N σ τ) (p ^ e) +
      ArithmeticFunction.vonMangoldt (q ^ f) *
        logValue (staircase (p ^ e) (q ^ f) M N σ τ) (q ^ f)) / _
    rw [logValue_staircase hp hq hN (by omega), logValue_staircase hp hq hN (by omega),
      stairLagCoeff_log_one hp hq hpq he hf hτ, stairLagCoeff_log_two hp hq hpq he hf hτ]
    have hs1 : 0 < Real.sqrt ((p ^ e : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hs2 : 0 < Real.sqrt ((q ^ f : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
    field_simp

end Deviation

/-- A bump index adequate for the staircase of length `M`. -/
theorem exists_stair_index (m₁ m₂ M : ℕ) : ∃ N : ℕ, stairBound m₁ m₂ M ≤ N := ⟨_, le_rfl⟩

/-- **Composite nodes are free on the integer grid: the supremum.** On the cone blind at every
integer `n ≥ 2` outside `{p^e, q^f}` the deviations have least upper bound `w(p^e) + w(q^f)`. -/
theorem isLUB_gridDeviations₂ {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 1 ≤ e) (hf : 1 ≤ f) :
    IsLUB (gridDeviations₂ (p ^ e) (q ^ f))
      (ArithmeticFunction.vonMangoldt (p ^ e) / Real.sqrt ((p ^ e : ℕ) : ℝ) +
        ArithmeticFunction.vonMangoldt (q ^ f) / Real.sqrt ((q ^ f : ℕ) : ℝ)) := by
  have hm₁ : IsPrimePow (p ^ e) := hp.isPrimePow.pow (by omega)
  have hm₂ : IsPrimePow (q ^ f) := hq.isPrimePow.pow (by omega)
  have hco : Nat.Coprime (p ^ e) (q ^ f) :=
    Nat.Coprime.pow e f ((Nat.coprime_primes hp hq).mpr hpq)
  set w₁ := ArithmeticFunction.vonMangoldt (p ^ e) / Real.sqrt ((p ^ e : ℕ) : ℝ)
  set w₂ := ArithmeticFunction.vonMangoldt (q ^ f) / Real.sqrt ((q ^ f : ℕ) : ℝ)
  have hw₂ : 0 ≤ w₂ := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  refine ⟨fun x hx => (isGreatest_deletionDeviations₂ hm₁ hm₂ hco).2
    (gridDeviations₂_subset _ _ hx), fun b hb => ?_⟩
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (w₂ / ε)
  obtain ⟨N, hN⟩ := exists_stair_index (p ^ e) (q ^ f) M
  have hmem := staircase_mem_gridDeviations₂ hp hq hpq he hf hN (σ := 1) (τ := 1) (by norm_num)
    (by norm_num)
  have hle := hb hmem
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hfrac : w₂ * (M / (M + 1)) = w₂ - w₂ / (M + 1) := by field_simp; ring
  have hsmall : w₂ / (M + 1) < ε := by
    rw [div_lt_iff₀ hM1]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  simp only [one_mul] at hle
  rw [hfrac] at hle
  linarith

/-- **Composite nodes are free on the integer grid: the infimum** `−(w(p^e) + w(q^f))`. -/
theorem isGLB_gridDeviations₂ {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (he : 1 ≤ e) (hf : 1 ≤ f) :
    IsGLB (gridDeviations₂ (p ^ e) (q ^ f))
      (-(ArithmeticFunction.vonMangoldt (p ^ e) / Real.sqrt ((p ^ e : ℕ) : ℝ) +
        ArithmeticFunction.vonMangoldt (q ^ f) / Real.sqrt ((q ^ f : ℕ) : ℝ))) := by
  have hm₁ : IsPrimePow (p ^ e) := hp.isPrimePow.pow (by omega)
  have hm₂ : IsPrimePow (q ^ f) := hq.isPrimePow.pow (by omega)
  have hco : Nat.Coprime (p ^ e) (q ^ f) :=
    Nat.Coprime.pow e f ((Nat.coprime_primes hp hq).mpr hpq)
  set w₁ := ArithmeticFunction.vonMangoldt (p ^ e) / Real.sqrt ((p ^ e : ℕ) : ℝ)
  set w₂ := ArithmeticFunction.vonMangoldt (q ^ f) / Real.sqrt ((q ^ f : ℕ) : ℝ)
  have hw₂ : 0 ≤ w₂ := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  refine ⟨fun x hx => (isLeast_deletionDeviations₂ hm₁ hm₂ hco).2
    (gridDeviations₂_subset _ _ hx), fun b hb => ?_⟩
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨M, hM⟩ := exists_nat_gt (w₂ / ε)
  obtain ⟨N, hN⟩ := exists_stair_index (p ^ e) (q ^ f) M
  have hmem := staircase_mem_gridDeviations₂ hp hq hpq he hf hN (σ := -1) (τ := 1) (by norm_num)
    (by norm_num)
  have hle := hb hmem
  have hM1 : (0 : ℝ) < M + 1 := by positivity
  have hfrac : w₂ * (M / (M + 1)) = w₂ - w₂ / (M + 1) := by field_simp; ring
  have hsmall : w₂ / (M + 1) < ε := by
    rw [div_lt_iff₀ hM1]
    rw [div_lt_iff₀ hε] at hM
    nlinarith
  have : -1 * w₁ + -1 * 1 * w₂ * (M / (M + 1)) = -w₁ - (w₂ - w₂ / (M + 1)) := by rw [← hfrac]; ring
  rw [this] at hle
  linarith

/-- **The double pair is not grid-blind**: it charges the composite node `m₁m₂`. -/
theorem not_gridBlind_doublePair {m₁ m₂ : ℕ} (h₁ : 2 ≤ m₁) (h₂ : 2 ≤ m₂) {σ₁ σ₂ : ℝ} (hσ₁ : σ₁ ≠ 0) (hσ₂ : σ₂ ≠ 0) :
    ¬ BlindOn ({n | 2 ≤ n} \ {m₁, m₂}) (Finsupp.single (doublePairTestFn m₁ m₂ σ₁ σ₂) 1) := by
  intro hb
  have h12 : 2 ≤ m₁ * m₂ := by nlinarith
  have hne₁ : m₁ * m₂ ≠ m₁ := by
    intro h; have : m₁ * m₂ = m₁ * 1 := by rw [mul_one]; exact h
    have := Nat.eq_of_mul_eq_mul_left (by omega) this; omega
  have hne₂ : m₁ * m₂ ≠ m₂ := by
    intro h; have : m₁ * m₂ = 1 * m₂ := by rw [one_mul]; exact h
    have := Nat.eq_of_mul_eq_mul_right (by omega) this; omega
  have h0 := hb ⟨m₁ * m₂, h12⟩ ⟨h12, by simp [hne₁, hne₂]⟩
  rw [nodeVector_single_test, logVector_apply] at h0
  change logValue (doublePair m₁ m₂ σ₁ σ₂) (m₁ * m₂) = 0 at h0
  rw [logValue_doublePair_mul h₁ h₂] at h0
  have hI := integral_narrowBump_sq_pos (m₁ * m₂)
  have hs : 0 < Real.sqrt ((m₁ * m₂ : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have : σ₁ * σ₂ * ∫ t, (narrowBump (m₁ * m₂) t) ^ 2 ≠ 0 := by positivity
    exact this (by linarith)
  · linarith

end

end GaloisForLFunctions.BiScaleUncertainty
