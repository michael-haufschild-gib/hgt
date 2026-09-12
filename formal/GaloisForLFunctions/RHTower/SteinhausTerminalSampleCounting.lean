import GaloisForLFunctions.RHTower.SteinhausLargestPrimePowerMass

/-!
# Counting terminal prime--cofactor samples in normalized intervals

For a fixed normalized interval `(a,b]`, the `p`-channel contributes the integers `m` satisfying
`a N / p < m ≤ b N / p`.  Its cardinality is at least `(b-a)N/p - 1`.  Summing over terminal
primes produces a linear main term because their reciprocal mass tends to `log (4/3)`; the one-unit
floor loss per prime is negligible because the whole terminal window has `o(N)` elements.

This is the arithmetic multiplicity input needed to replace one `N⁻ᴶ` terminal determinant by
linearly many choices in each of `J` disjoint stable determinant neighborhoods.
-/

namespace RHTower

open Filter Finset Nat Topology

noncomputable section

/-- Cofactors whose product with `p`, after normalization by `N`, lies in `(a,b]`. -/
def normalizedProductCofactorBlock (a b : ℝ) (N p : ℕ) : Finset ℕ :=
  Finset.Icc (⌊a * (N : ℝ) / (p : ℝ)⌋₊ + 1)
    ⌊b * (N : ℝ) / (p : ℝ)⌋₊

theorem mem_normalizedProductCofactorBlock {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    {N p m : ℕ} (hp : 0 < p) :
    m ∈ normalizedProductCofactorBlock a b N p ↔
      a * (N : ℝ) / (p : ℝ) < (m : ℝ) ∧
        (m : ℝ) ≤ b * (N : ℝ) / (p : ℝ) := by
  have hA : 0 ≤ a * (N : ℝ) / (p : ℝ) := by positivity
  have hB : 0 ≤ b * (N : ℝ) / (p : ℝ) := by positivity
  rw [normalizedProductCofactorBlock, Finset.mem_Icc]
  constructor
  · intro hm
    exact ⟨(Nat.floor_lt hA).mp (by omega), (Nat.le_floor_iff hB).mp hm.2⟩
  · intro hm
    exact ⟨by have := (Nat.floor_lt hA).mpr hm.1; omega,
      (Nat.le_floor_iff hB).mpr hm.2⟩

/-- One prime channel has interval count at least its real length minus one. -/
theorem normalizedProductCofactorBlock_card_lower
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {N p : ℕ} (hp : 0 < p) :
    (b - a) * (N : ℝ) / (p : ℝ) - 1 ≤
      ((normalizedProductCofactorBlock a b N p).card : ℝ) := by
  let A : ℝ := a * (N : ℝ) / (p : ℝ)
  let B : ℝ := b * (N : ℝ) / (p : ℝ)
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAB : A ≤ B := by
    dsimp [A, B]
    gcongr
  have htarget : (b - a) * (N : ℝ) / (p : ℝ) - 1 = B - A - 1 := by
    dsimp [A, B]
    ring
  rw [htarget]
  by_cases hwidth : 1 ≤ B - A
  · have hfloor : ⌊A⌋₊ ≤ ⌊B⌋₊ := Nat.floor_mono hAB
    have hcard : (normalizedProductCofactorBlock a b N p).card = ⌊B⌋₊ - ⌊A⌋₊ := by
      unfold normalizedProductCofactorBlock
      dsimp [A, B] at hfloor ⊢
      rw [Nat.card_Icc]
      omega
    rw [hcard, Nat.cast_sub hfloor]
    have hAfloor : ((⌊A⌋₊ : ℕ) : ℝ) ≤ A := Nat.floor_le hA
    have hBfloor : B - 1 < ((⌊B⌋₊ : ℕ) : ℝ) := Nat.sub_one_lt_floor B
    linarith
  · have hsmall : B - A - 1 ≤ 0 := by linarith
    exact hsmall.trans (Nat.cast_nonneg _)

/-- The two-thirds power cutoff is sublinear relative to `N`. -/
theorem tendsto_twoThirdsPowerWindowIndex_div_natCast_zero :
    Tendsto (fun N : ℕ =>
      ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun T : ℝ => T ^ (2 / 3 : ℝ) / T)
      atTop (nhds 0) := by
    have h := tendsto_rpow_neg_atTop (y := 1 - (2 / 3 : ℝ)) (by norm_num)
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [show -(1 - (2 / 3 : ℝ)) = (2 / 3 : ℝ) - 1 by ring,
      Real.rpow_sub hT, Real.rpow_one]
  have hupperlim : Tendsto
      (fun N : ℕ => 2 * ((N : ℝ) ^ (2 / 3 : ℝ) / (N : ℝ)))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      (hreal.comp tendsto_natCast_atTop_atTop).const_mul 2
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hupperlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hindex := powerWindowIndex_le_two_mul hpow
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hdiv := (div_le_div_iff_of_pos_right hNR).2 hindex
  calc
    ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) / (N : ℝ) ≤
        2 * (N : ℝ) ^ (2 / 3 : ℝ) / (N : ℝ) := hdiv
    _ = 2 * ((N : ℝ) ^ (2 / 3 : ℝ) / (N : ℝ)) := by ring

/-- The number of primes in the terminal power window is `o(N)`. -/
theorem tendsto_terminalPrimePowerWindow_card_div_natCast_zero :
    Tendsto (fun N : ℕ =>
      ((terminalPrimePowerWindow N).card : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_
    tendsto_twoThirdsPowerWindowIndex_div_natCast_zero
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hcard : (terminalPrimePowerWindow N).card ≤
      powerWindowIndex (2 / 3 : ℝ) N := by
    rw [← Finset.card_range (powerWindowIndex (2 / 3 : ℝ) N)]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_range]
    exact (mem_terminalPrimePowerWindow.mp hp).2.2
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcardR : ((terminalPrimePowerWindow N).card : ℝ) ≤
      ((powerWindowIndex (2 / 3 : ℝ) N : ℕ) : ℝ) := by exact_mod_cast hcard
  exact (div_le_div_iff_of_pos_right hNR).2 hcardR

/-- Summed interval count before absorbing the one-unit floor loss in each prime channel. -/
theorem terminalPrimePowerWindow_normalizedProductCofactorBlock_card_lower
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (N : ℕ) :
    (b - a) * (N : ℝ) * terminalPrimePowerWindowMass N -
        ((terminalPrimePowerWindow N).card : ℝ) ≤
      ∑ p ∈ terminalPrimePowerWindow N,
        ((normalizedProductCofactorBlock a b N p).card : ℝ) := by
  calc
    (b - a) * (N : ℝ) * terminalPrimePowerWindowMass N -
        ((terminalPrimePowerWindow N).card : ℝ) =
      ∑ p ∈ terminalPrimePowerWindow N,
        ((b - a) * (N : ℝ) / (p : ℝ) - 1) := by
          unfold terminalPrimePowerWindowMass
          rw [Finset.mul_sum, Finset.sum_sub_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          congr 1
    _ ≤ ∑ p ∈ terminalPrimePowerWindow N,
        ((normalizedProductCofactorBlock a b N p).card : ℝ) := by
          exact Finset.sum_le_sum fun p hp =>
            normalizedProductCofactorBlock_card_lower ha hab
              (mem_terminalPrimePowerWindow.mp hp).1.pos

/-- **Linear terminal sample supply.** Every fixed normalized interval contains at least `cN`
terminal prime--cofactor samples for all sufficiently large `N`. -/
theorem exists_eventually_terminalPrimePowerWindow_normalizedProductCofactorBlock_card_linear
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ ∑ p ∈ terminalPrimePowerWindow N,
        ((normalizedProductCofactorBlock a b N p).card : ℝ) := by
  let L : ℝ := -Real.log (1 / 2 : ℝ) - (-Real.log (2 / 3 : ℝ))
  have hL : 0 < L := terminalPrimePowerWindowMass_limit_pos
  let c : ℝ := (b - a) * L / 4
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  have hmass : ∀ᶠ N : ℕ in atTop, L / 2 < terminalPrimePowerWindowMass N :=
    tendsto_terminalPrimePowerWindowMass.eventually_const_lt (by linarith)
  have hdelta : 0 < (b - a) * L / 4 := by positivity
  have hcard : ∀ᶠ N : ℕ in atTop,
      ((terminalPrimePowerWindow N).card : ℝ) / (N : ℝ) <
        (b - a) * L / 4 :=
    tendsto_terminalPrimePowerWindow_card_div_natCast_zero.eventually_lt_const hdelta
  filter_upwards [hmass, hcard, eventually_ge_atTop 1] with N hmassN hcardN hN
  have hNR : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hcardMul : ((terminalPrimePowerWindow N).card : ℝ) ≤
      (b - a) * L / 4 * (N : ℝ) :=
    ((div_lt_iff₀ hNR).mp hcardN).le
  have hmain : (b - a) * (N : ℝ) * (L / 2) ≤
      (b - a) * (N : ℝ) * terminalPrimePowerWindowMass N :=
    mul_le_mul_of_nonneg_left hmassN.le
      (mul_nonneg (sub_nonneg.mpr hab.le) (Nat.cast_nonneg N))
  calc
    c * (N : ℝ) =
        (b - a) * (N : ℝ) * (L / 2) -
          (b - a) * L / 4 * (N : ℝ) := by dsimp [c]; ring
    _ ≤ (b - a) * (N : ℝ) * terminalPrimePowerWindowMass N -
          ((terminalPrimePowerWindow N).card : ℝ) :=
      sub_le_sub hmain hcardMul
    _ ≤ ∑ p ∈ terminalPrimePowerWindow N,
          ((normalizedProductCofactorBlock a b N p).card : ℝ) :=
      terminalPrimePowerWindow_normalizedProductCofactorBlock_card_lower ha hab N

end

end RHTower
