import GaloisForLFunctions.RHTower.Sieve.MarkerLadder
import GaloisForLFunctions.RHTower.Sieve.BadOuterUniformWindow

/-!
# The growing reciprocal-marker count at one physical scale

The window `(Z, Z+H]` is served by `I` super-blocks of `K₀+1` dyadic marker blocks each.  The start
ladder is `m = 2^{I(K₀+1)} u`, `m/2, …, u`; block `k` has start scale `2^{I(K₀+1)-k} u` and window
`H · 2^{I(K₀+1)-k} u /(4Z)`, which is exactly the cofactor length that keeps its products inside the
window.  Every super-block keeps half its harmonic mass `≥ multiHarmConst K₀/log Z`, so the window
receives

`(3ϱ/256) · (H · I · multiHarmConst K₀ /(2 log Z) − Z/u)`

integers of each Möbius sign.  All hypotheses are explicit inequalities in `Z, H, u, I`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

/-- Start scales of a ladder based at `2^n u`. -/
theorem freeStart_two_pow_mul {n u k : ℕ} (hk : k ≤ n) :
    freeStart (2 ^ n * u) k = 2 ^ (n - k) * u := by
  rw [freeStart, show (2 : ℕ) ^ n = 2 ^ k * 2 ^ (n - k) by
    rw [← pow_add]; congr 1; omega, mul_assoc, Nat.mul_div_cancel_left _ (by positivity)]

/-- The geometric sum of the start scales of consecutive blocks. -/
theorem sum_two_pow_Ico_add {n a b : ℕ} (hab : a ≤ b) (hbn : b ≤ n) :
    ∑ k ∈ Finset.Ico a b, 2 ^ (n - k) + 2 ^ (n - b + 1) = 2 ^ (n - a + 1) := by
  induction b with
  | zero =>
      have ha : a = 0 := by omega
      subst ha
      simp
  | succ b ih =>
      rcases Nat.eq_or_lt_of_le hab with hEq | hlt
      · subst hEq
        simp
      have hb : a ≤ b := by omega
      rw [Finset.sum_Ico_succ_top hb, ← ih hb (by omega)]
      have h1 : n - b = (n - (b + 1)) + 1 := by omega
      rw [h1, pow_succ]
      ring

/-- The exceptional starts of a block interval, blockwise. -/
theorem card_ladderBad_le (win : ℕ → ℝ) (m a b : ℕ) :
    (((ladderBad win m a b).card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Ico a b, (((badOuter (freeScale m k) (win k)).card : ℕ) : ℝ) := by
  classical
  have h := Finset.card_biUnion_le (s := Finset.Ico a b)
    (t := fun k => badStart (freeScale m k) (win k))
  have hcast : (((ladderBad win m a b).card : ℕ) : ℝ)
      ≤ ((∑ k ∈ Finset.Ico a b, (badStart (freeScale m k) (win k)).card : ℕ) : ℝ) := by
    rw [ladderBad]
    exact_mod_cast h
  refine hcast.trans ?_
  push_cast
  exact Finset.sum_le_sum fun k _ => by exact_mod_cast card_badStart_le_card_badOuter _ _

/-- The window of block `k` of a ladder serving `(Z, Z+H]`. -/
def ladderWin (Z H m : ℕ) (k : ℕ) : ℝ := (H : ℝ) * ((freeStart m k : ℕ) : ℝ) / (4 * (Z : ℝ))

/-- A marker of block `k` exceeds `Z/m_k`. -/
theorem lt_mul_freeStart_of_mem_freeBlock {Z m k p : ℕ} (hk : 0 < freeStart m k)
    (hp : p ∈ freeBlock Z m k) : (Z : ℝ) < (p : ℝ) * ((freeStart m k : ℕ) : ℝ) := by
  have hlt : Z / freeStart m k < p := lt_of_mem_bigPrimeSet hp
  have hnat : Z < p * freeStart m k := by
    have := (Nat.div_lt_iff_lt_mul hk).1 hlt
    exact this
  exact_mod_cast hnat

/-- A marker of block `k` is at most `Z/m_{k+1}`. -/
theorem le_div_freeStart_of_mem_freeBlock {Z m k p : ℕ} (hp : p ∈ freeBlock Z m k) :
    p ≤ Z / freeStart m (k + 1) :=
  (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2

/-- **The fit.**  A marker's cell holds its block's window. -/
theorem ladder_fit {Z H m k p u : ℕ} (hZ : 0 < Z) (hk1 : 0 < freeStart m (k + 1))
    (hhalf : 2 * freeStart m (k + 1) = freeStart m k) (hu : u ≤ freeStart m (k + 1))
    (hu0 : 0 < u) (hZu : ((Z / u : ℕ) : ℝ) ≤ (H : ℝ) / 2) (hp : p ∈ freeBlock Z m k) :
    (ladderWin Z H m k + 1) * (p : ℝ) ≤ (H : ℝ) := by
  have hple := le_div_freeStart_of_mem_freeBlock hp
  have hZR : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZ
  have hk1R : (0 : ℝ) < ((freeStart m (k + 1) : ℕ) : ℝ) := by exact_mod_cast hk1
  have hpR : (p : ℝ) ≤ (Z : ℝ) / ((freeStart m (k + 1) : ℕ) : ℝ) := by
    have : ((Z / freeStart m (k + 1) : ℕ) : ℝ) ≤ (Z : ℝ) / ((freeStart m (k + 1) : ℕ) : ℝ) :=
      Nat.cast_div_le
    exact le_trans (by exact_mod_cast hple) this
  have hkR : ((freeStart m k : ℕ) : ℝ) = 2 * ((freeStart m (k + 1) : ℕ) : ℝ) := by
    rw [← hhalf]; push_cast; ring
  have hwin : ladderWin Z H m k * (p : ℝ) ≤ (H : ℝ) / 2 := by
    rw [ladderWin, hkR]
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    calc (H : ℝ) * (2 * ((freeStart m (k + 1) : ℕ) : ℝ)) / (4 * (Z : ℝ)) * (p : ℝ)
        ≤ (H : ℝ) * (2 * ((freeStart m (k + 1) : ℕ) : ℝ)) / (4 * (Z : ℝ))
          * ((Z : ℝ) / ((freeStart m (k + 1) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hpR (by positivity)
      _ = (H : ℝ) / 2 := by field_simp; ring
  have hpu : (p : ℝ) ≤ ((Z / u : ℕ) : ℝ) := by
    exact_mod_cast le_trans hple (Nat.div_le_div_left hu hu0)
  nlinarith [hwin, hpu, hZu]

/-- **The supply.**  A marker's cell is at most four windows long. -/
theorem ladder_supply {Z H m k p : ℕ} (hk : 0 < freeStart m k) (hZ : 0 < Z)
    (hw4 : 4 ≤ ladderWin Z H m k) (hp : p ∈ freeBlock Z m k) :
    3 * squarefreeDensity / 256 * ((H : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (ladderWin Z H m k / 2 - 1) := by
  have hD := squarefreeDensity_pos
  have hlt := lt_mul_freeStart_of_mem_freeBlock hk hp
  have hZR : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZ
  have hkR : (0 : ℝ) < ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast hk
  have hp0 : (0 : ℝ) < (p : ℝ) := by
    by_contra hcon
    push Not at hcon
    nlinarith [hcon, hkR, hlt]
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  -- `H/p ≤ 4·window`
  have hcell : (H : ℝ) / (p : ℝ) ≤ 4 * ladderWin Z H m k := by
    rw [ladderWin, div_le_iff₀ hp0]
    have : (H : ℝ) * (Z : ℝ) ≤ (H : ℝ) * ((p : ℝ) * ((freeStart m k : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hlt.le hH0
    have hval : 4 * ((H : ℝ) * ((freeStart m k : ℕ) : ℝ) / (4 * (Z : ℝ))) * (p : ℝ)
        = (H : ℝ) * ((p : ℝ) * ((freeStart m k : ℕ) : ℝ)) / (Z : ℝ) := by
      field_simp
    rw [hval, le_div_iff₀ hZR]
    linarith
  nlinarith [hcell, hw4, hD]

/-- **The window of every block lies in the uniform range of the exceptional-set bound.** -/
theorem ladderWin_mem_range {Z H m k u : ℕ} (hu2 : 2 ≤ u) (huk : u ≤ freeStart m k)
    (hmZ : freeStart m k * freeStart m k ≤ Z)
    (hlo : 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) ≤ (H : ℝ) * (u : ℝ))
    (hhi : (H : ℝ) * Real.log Z ≤ 4 * (Z : ℝ)) :
    (Real.log (freeScale m k)) ^ (4 : ℕ) ≤ ladderWin Z H m k
      ∧ ladderWin Z H m k ≤ Real.sqrt (freeScale m k) / Real.log (freeScale m k) := by
  have hkR : (2 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast le_trans hu2 huk
  have hZ : (4 : ℝ) ≤ (Z : ℝ) := by
    have : 4 ≤ Z := le_trans (by nlinarith [le_trans hu2 huk]) hmZ
    exact_mod_cast this
  have hZ0 : (0 : ℝ) < (Z : ℝ) := by linarith
  have hy : freeScale m k ≤ (Z : ℝ) := by
    rw [freeScale]
    have : ((freeStart m k * freeStart m k : ℕ) : ℝ) ≤ (Z : ℝ) := by exact_mod_cast hmZ
    push_cast at this
    nlinarith [this]
  have hy4 : (4 : ℝ) ≤ freeScale m k := by rw [freeScale]; nlinarith [hkR]
  have hlogy0 : 0 < Real.log (freeScale m k) := Real.log_pos (by linarith)
  have hlogy : Real.log (freeScale m k) ≤ Real.log Z := Real.log_le_log (by linarith) hy
  have huR : (u : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast huk
  have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  constructor
  · have h1 : (Real.log (freeScale m k)) ^ (4 : ℕ) ≤ (Real.log Z) ^ (4 : ℕ) :=
      pow_le_pow_left₀ hlogy0.le hlogy 4
    have h2 : (Real.log Z) ^ (4 : ℕ) ≤ ladderWin Z H m k := by
      rw [ladderWin, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left huR hH0]
    linarith
  · rw [sqrt_freeScale, le_div_iff₀ hlogy0, ladderWin]
    have hkey : (H : ℝ) * Real.log (freeScale m k) ≤ 4 * (Z : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hlogy hH0) hhi
    have hk0 : (0 : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hkey hk0]

/-- **The exceptional starts of one super-block have density `ε` against its top start.** -/
theorem card_ladderBad_le_density {Z H n u a b : ℕ} {ε y₀ : ℝ} (hu2 : 2 ≤ u) (hab : a ≤ b)
    (hbn : b ≤ n) (hε : 0 ≤ ε)
    (hbad : ∀ y : ℝ, y₀ ≤ y → ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L →
      L ≤ Real.sqrt y / Real.log y → (((badOuter y L).card : ℕ) : ℝ) ≤ ε / 2 * Real.sqrt y)
    (hy₀ : y₀ ≤ (u : ℝ) ^ (2 : ℕ))
    (hmZ : (2 ^ n * u) * (2 ^ n * u) ≤ Z)
    (hlo : 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) ≤ (H : ℝ) * (u : ℝ))
    (hhi : (H : ℝ) * Real.log Z ≤ 4 * (Z : ℝ)) :
    (((ladderBad (ladderWin Z H (2 ^ n * u)) (2 ^ n * u) a b).card : ℕ) : ℝ)
      ≤ ε * ((freeStart (2 ^ n * u) a : ℕ) : ℝ) := by
  set m : ℕ := 2 ^ n * u with hm
  refine (card_ladderBad_le _ m a b).trans ?_
  have hterm : ∀ k ∈ Finset.Ico a b,
      (((badOuter (freeScale m k) (ladderWin Z H m k)).card : ℕ) : ℝ)
        ≤ ε / 2 * (((2 ^ (n - k) * u : ℕ) : ℕ) : ℝ) := by
    intro k hk
    have hkn : k ≤ n := by have := (Finset.mem_Ico.1 hk).2; omega
    have hfs : freeStart m k = 2 ^ (n - k) * u := freeStart_two_pow_mul hkn
    have huk : u ≤ freeStart m k := by
      rw [hfs]; exact Nat.le_mul_of_pos_left u (by positivity)
    have hkm : freeStart m k ≤ m := by
      have := freeStart_anti m (Nat.zero_le k)
      rwa [freeStart_zero] at this
    have hkZ : freeStart m k * freeStart m k ≤ Z := le_trans (Nat.mul_le_mul hkm hkm) hmZ
    obtain ⟨hr1, hr2⟩ := ladderWin_mem_range hu2 huk hkZ hlo hhi
    have hy : y₀ ≤ freeScale m k := by
      refine le_trans hy₀ ?_
      rw [freeScale]
      have : (u : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast huk
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
    have := hbad _ hy _ hr1 hr2
    rw [sqrt_freeScale, hfs] at this
    exact this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeom := sum_two_pow_Ico_add (n := n) hab hbn
  have hfa : freeStart m a = 2 ^ (n - a) * u := freeStart_two_pow_mul (le_trans hab hbn)
  have hsum : ∑ k ∈ Finset.Ico a b, (((2 ^ (n - k) * u : ℕ) : ℕ) : ℝ)
      ≤ 2 * ((freeStart m a : ℕ) : ℝ) := by
    rw [hfa]
    have hnat : ∑ k ∈ Finset.Ico a b, 2 ^ (n - k) * u ≤ 2 * (2 ^ (n - a) * u) := by
      rw [← Finset.sum_mul]
      have h2 : ∑ k ∈ Finset.Ico a b, 2 ^ (n - k) ≤ 2 * 2 ^ (n - a) := by
        have h22 : 2 * 2 ^ (n - a) = 2 ^ (n - a + 1) := by rw [pow_succ]; ring
        rw [h22, ← hgeom]
        exact Nat.le_add_right _ _
      calc (∑ k ∈ Finset.Ico a b, 2 ^ (n - k)) * u ≤ 2 * 2 ^ (n - a) * u :=
            Nat.mul_le_mul_right u h2
        _ = 2 * (2 ^ (n - a) * u) := by ring
    exact_mod_cast hnat
  nlinarith [hsum, hε]

/-- **One super-block keeps the harmonic mass `multiHarmConst K₀/(2 log Z)`.** -/
theorem ladder_superblock_mass_ge {K₀ Z H u I i : ℕ} {ε y₀ Mstar : ℝ}
    (hu2 : 2 ≤ u) (hi : i < I) (hε : 0 ≤ ε) (hharm : 0 < multiHarmConst K₀)
    (hbad : ∀ y : ℝ, y₀ ≤ y → ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L →
      L ≤ Real.sqrt y / Real.log y → (((badOuter y L).card : ℕ) : ℝ) ≤ ε / 2 * Real.sqrt y)
    (hy₀ : y₀ ≤ (u : ℝ) ^ (2 : ℕ))
    (hMstar : ∀ M : ℕ, Mstar ≤ (M : ℝ) → 2 ≤ M ∧ markerLogBound K₀ ≤ Real.log (M : ℝ)
      ∧ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)
      ∧ 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
          ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4))
    (hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2)
    (hZm : Mstar ≤ ((Z / (2 ^ (I * (K₀ + 1)) * u) : ℕ) : ℝ))
    (hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((2 ^ (I * (K₀ + 1)) * u : ℕ) : ℝ)
        * Real.log (Z : ℝ)
      ≤ ((Z / (2 ^ (I * (K₀ + 1)) * u) : ℕ) : ℝ) * (multiHarmConst K₀ / 2) ^ 2)
    (hlo : 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) ≤ (H : ℝ) * (u : ℝ))
    (hhi : (H : ℝ) * Real.log Z ≤ 4 * (Z : ℝ))
    (hmZ : (2 ^ (I * (K₀ + 1)) * u) * (2 ^ (I * (K₀ + 1)) * u) ≤ Z) :
    multiHarmConst K₀ / (2 * Real.log (Z : ℝ))
      ≤ ∑ p ∈ ladderGood (ladderWin Z H (2 ^ (I * (K₀ + 1)) * u)) Z
          (2 ^ (I * (K₀ + 1)) * u) (i * (K₀ + 1)) ((i + 1) * (K₀ + 1)), (1 : ℝ) / (p : ℝ) := by
  classical
  set n : ℕ := I * (K₀ + 1) with hn
  set m : ℕ := 2 ^ n * u with hm
  set a : ℕ := i * (K₀ + 1) with ha
  set b : ℕ := (i + 1) * (K₀ + 1) with hb
  have hbn : b ≤ n := Nat.mul_le_mul_right _ (by omega)
  have hab : a ≤ b := Nat.mul_le_mul_right _ (by omega)
  set ui : ℕ := 2 ^ (n - b) * u with hui
  have hui0 : 0 < ui := by rw [hui]; positivity
  have hfb : freeStart m b = ui := freeStart_two_pow_mul hbn
  have hfa : freeStart m a = 2 ^ (K₀ + 1) * ui := by
    rw [freeStart_two_pow_mul (le_trans hab hbn), hui, ← mul_assoc, ← pow_add]
    congr 2
    rw [ha, hb]
    have : (i + 1) * (K₀ + 1) = i * (K₀ + 1) + (K₀ + 1) := by ring
    omega
  set M : ℕ := Z / (2 ^ (K₀ + 1) * ui) with hMdef
  -- the base of the super-block dominates the base of the whole ladder
  have ham : freeStart m a ≤ m := by
    have := freeStart_anti m (Nat.zero_le a)
    rwa [freeStart_zero] at this
  have hMge : Z / m ≤ M := by
    rw [hMdef, ← hfa]
    exact Nat.div_le_div_left ham (by rw [hfa]; positivity)
  have hMstarM : Mstar ≤ (M : ℝ) := le_trans hZm (by exact_mod_cast hMge)
  obtain ⟨hM2, hlogM, hbt, hT3⟩ := hMstar M hMstarM
  -- exceptional starts
  have hEbad := card_ladderBad_le_density (Z := Z) (H := H) (n := n) (u := u) (a := a) (b := b)
    (ε := ε) (y₀ := y₀) hu2 hab hbn hε hbad hy₀ hmZ hlo hhi
  rw [hfa] at hEbad
  -- `T₁` for the super-block
  have hMR0 : (0 : ℝ) < (M : ℝ) := by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith
  have hMZ : M ≤ Z := Nat.div_le_self _ _
  have hlogM0 : 0 < Real.log (M : ℝ) := Real.log_pos (by
    have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    linarith)
  have hlogMZ : Real.log (M : ℝ) ≤ Real.log (Z : ℝ) :=
    Real.log_le_log hMR0 (by exact_mod_cast hMZ)
  have huim : (ui : ℝ) ≤ ((m : ℕ) : ℝ) := by
    have : ui ≤ m := by
      rw [← hfb]
      have := freeStart_anti m (Nat.zero_le b)
      rwa [freeStart_zero] at this
    exact_mod_cast this
  have hT1i : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (ui : ℝ) * Real.log (M : ℝ)
      ≤ (M : ℝ) * (multiHarmConst K₀ / 2) ^ 2 := by
    have hc : (0 : ℝ) ≤ 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) := by positivity
    have hstep : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (ui : ℝ) * Real.log (M : ℝ)
        ≤ 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((m : ℕ) : ℝ) * Real.log (Z : ℝ) := by
      have h1 : (ui : ℝ) * Real.log (M : ℝ) ≤ ((m : ℕ) : ℝ) * Real.log (Z : ℝ) :=
        mul_le_mul huim hlogMZ hlogM0.le (Nat.cast_nonneg _)
      calc 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (ui : ℝ) * Real.log (M : ℝ)
          = 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((ui : ℝ) * Real.log (M : ℝ)) := by ring
        _ ≤ 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (((m : ℕ) : ℝ) * Real.log (Z : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hc
        _ = 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((m : ℕ) : ℝ) * Real.log (Z : ℝ) := by ring
    refine hstep.trans (hT1.trans ?_)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hMge) (sq_nonneg _)
  have hmass := good_mass_ge_of_budget (K₀ := K₀) (X := Z) (u := ui) (M := M) (Mt := Z / ui)
    (K := Z / (ui * ui)) (S := ladderBad (ladderWin Z H m) m a b) (ε := ε) hMdef rfl rfl
    hui0 hε hharm hM2 hlogM hbt (by exact_mod_cast hEbad) hT1i hT2 hT3
  have hgood : ladderGood (ladderWin Z H m) Z m a b
      = (bigPrimeSet M (Z / ui)).filter
          (fun p => Z / p ∉ ladderBad (ladderWin Z H m) m a b) := by
    rw [ladderGood, ladderRange, hfa, hfb]
  rw [hgood]
  refine le_trans ?_ hmass
  have hZ0 : 0 < Real.log (Z : ℝ) := lt_of_lt_of_le hlogM0 hlogMZ
  exact div_le_div_of_nonneg_left hharm.le (by positivity) (by linarith)

open Classical in
/-- **The growing reciprocal-marker count at one physical scale.** -/
theorem growingMarker_count_explicit {K₀ Z H u I : ℕ} {σ : ℤ} {ε y₀ Mstar : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hu2 : 2 ≤ u) (hI : 0 < I) (hε : 0 ≤ ε)
    (hharm : 0 < multiHarmConst K₀)
    (hbad : ∀ y : ℝ, y₀ ≤ y → ∀ L : ℝ, (Real.log y) ^ (4 : ℕ) ≤ L →
      L ≤ Real.sqrt y / Real.log y → (((badOuter y L).card : ℕ) : ℝ) ≤ ε / 2 * Real.sqrt y)
    (hy₀ : y₀ ≤ (u : ℝ) ^ (2 : ℕ))
    (hMstar : ∀ M : ℕ, Mstar ≤ (M : ℝ) → 2 ≤ M ∧ markerLogBound K₀ ≤ Real.log (M : ℝ)
      ∧ Real.exp (4 * mertensSecondUpperConst) * (Real.log (M : ℝ)) ^ 5
          ≤ 32 * 2 ^ (K₀ + 2) * (M : ℝ) ^ ((3 : ℝ) / 4)
      ∧ 12 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * (Real.log (M : ℝ)) ^ 2
          ≤ (multiHarmConst K₀ / 2) ^ 2 * (M : ℝ) ^ ((1 : ℝ) / 4))
    (hT2 : 6 * ε * pairMainConst * (2 : ℝ) ^ (3 * K₀ + 6) ≤ (multiHarmConst K₀ / 2) ^ 2)
    (hZm : Mstar ≤ ((Z / (2 ^ (I * (K₀ + 1)) * u) : ℕ) : ℝ))
    (hT1 : 192 * ε * (2 : ℝ) ^ (2 * K₀ + 4) * ((2 ^ (I * (K₀ + 1)) * u : ℕ) : ℝ)
        * Real.log (Z : ℝ)
      ≤ ((Z / (2 ^ (I * (K₀ + 1)) * u) : ℕ) : ℝ) * (multiHarmConst K₀ / 2) ^ 2)
    (hlo : 4 * (Z : ℝ) * (Real.log Z) ^ (4 : ℕ) ≤ (H : ℝ) * (u : ℝ))
    (hhi : (H : ℝ) * Real.log Z ≤ 4 * (Z : ℝ)) (hL : 2 ≤ Real.log (Z : ℝ))
    (hmZ : (2 ^ (I * (K₀ + 1)) * u) * (2 ^ (I * (K₀ + 1)) * u) ≤ Z)
    (hXH : Z + H ≤ (Z / (2 ^ (I * (K₀ + 1)) * u)) * (Z / (2 ^ (I * (K₀ + 1)) * u))) :
    (3 * squarefreeDensity / 256)
        * ((H : ℝ) * ((I : ℝ) * (multiHarmConst K₀ / (2 * Real.log (Z : ℝ))))
          - ((Z / u : ℕ) : ℝ))
      ≤ ((((Finset.Ioc Z (Z + H)).filter (fun n => moebius n = σ
          ∧ MarkerDecoded (Z / (2 ^ (I * (K₀ + 1)) * u)) σ n)).card : ℕ) : ℝ) := by
  classical
  set n : ℕ := I * (K₀ + 1) with hn
  set m : ℕ := 2 ^ n * u with hm
  have hn0 : 0 < n := Nat.mul_pos hI (by omega)
  have hu0 : 0 < u := by omega
  have hfs : ∀ k, k ≤ n → freeStart m k = 2 ^ (n - k) * u :=
    fun k hk => freeStart_two_pow_mul hk
  have hfsu : ∀ k, k ≤ n → u ≤ freeStart m k := by
    intro k hk
    rw [hfs k hk]
    exact Nat.le_mul_of_pos_left u (by positivity)
  have hhalf : ∀ k, k < n → 2 * freeStart m (k + 1) = freeStart m k := by
    intro k hk
    rw [hfs k hk.le, hfs (k + 1) hk]
    have : n - k = (n - (k + 1)) + 1 := by omega
    rw [this, pow_succ]
    ring
  have hLR : (0 : ℝ) < Real.log (Z : ℝ) := by linarith
  have hZ0 : 0 < Z := by
    by_contra hcon
    have : Z = 0 := by omega
    rw [this] at hL
    simp at hL
    linarith
  have hZR : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZ0
  have huR : (2 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu2
  have hL4 : (16 : ℝ) ≤ (Real.log (Z : ℝ)) ^ (4 : ℕ) := by
    have : (2 : ℝ) ^ (4 : ℕ) ≤ (Real.log (Z : ℝ)) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hL 4
    norm_num at this
    linarith
  have hHu : 64 * (Z : ℝ) ≤ (H : ℝ) * (u : ℝ) := by nlinarith [hlo, hL4, hZR]
  have hZu : ((Z / u : ℕ) : ℝ) ≤ (H : ℝ) / 2 := by
    have h1 : ((Z / u : ℕ) : ℝ) ≤ (Z : ℝ) / (u : ℝ) := Nat.cast_div_le
    refine h1.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hHu]
  have hwin4 : ∀ k, k ≤ n → 4 ≤ ladderWin Z H m k := by
    intro k hk
    have huk := hfsu k hk
    have hukR : (u : ℝ) ≤ ((freeStart m k : ℕ) : ℝ) := by exact_mod_cast huk
    rw [ladderWin, le_div_iff₀ (by positivity)]
    have hH0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hukR hH0, hHu]
  have hmass := fun i (hi : i < I) => ladder_superblock_mass_ge (K₀ := K₀) (Z := Z) (H := H)
    (u := u) (I := I) (i := i) (ε := ε) (y₀ := y₀) (Mstar := Mstar) hu2 hi hε hharm hbad hy₀
    hMstar hT2 hZm hT1 hlo hhi hmZ
  have hsum : ((I : ℝ) * (multiHarmConst K₀ / (2 * Real.log (Z : ℝ))))
      = ∑ _i ∈ Finset.range I, multiHarmConst K₀ / (2 * Real.log (Z : ℝ)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  refine ladder_card_sign_window_ge (win := ladderWin Z H m) (X := Z) (m := m)
    (g := K₀ + 1) (I := I) (H := H) (σ := σ) (rho := 3 * squarefreeDensity / 256)
    (B := ((Z / u : ℕ) : ℝ)) (c := fun _ => multiHarmConst K₀ / (2 * Real.log (Z : ℝ)))
    hn0 (Dvd.intro u rfl) hσ ?_ ?_ (by have := squarefreeDensity_pos; positivity) ?_ ?_ ?_ ?_
    hmass ?_ |>.trans (le_of_eq (by rw [freeStart_zero]))
  · rw [hfs n le_rfl, Nat.sub_self, pow_zero, one_mul]; exact hu0
  · rw [freeStart_zero]; exact hXH
  · intro k hk; exact le_trans hu2 (hfsu k hk.le)
  · intro k hk; linarith [hwin4 k hk.le]
  · intro k hk p hp
    have hk1 : 0 < freeStart m (k + 1) := lt_of_lt_of_le hu0 (hfsu (k + 1) hk)
    exact ladder_fit hZ0 hk1 (hhalf k hk) (hfsu (k + 1) hk) hu0 hZu hp
  · intro k hk p hp
    have hk0 : 0 < freeStart m k := lt_of_lt_of_le hu0 (hfsu k hk.le)
    exact ladder_supply hk0 hZ0 (hwin4 k hk.le) hp
  · -- every marker is at most `Z/u`
    have hsub : ladderMarkers (ladderWin Z H m) Z m (K₀ + 1) I ⊆ Finset.Icc 1 (Z / u) := by
      intro p hp
      rw [ladderMarkers, Finset.mem_biUnion] at hp
      obtain ⟨i, hi, hpi⟩ := hp
      rw [Finset.mem_range] at hi
      have hpr := (Finset.mem_filter.1 hpi).1
      rw [ladderRange, bigPrimeSet, Finset.mem_filter, Finset.mem_Icc] at hpr
      obtain ⟨⟨-, hple⟩, hpp⟩ := hpr
      have hb : (i + 1) * (K₀ + 1) ≤ n := Nat.mul_le_mul_right _ (by omega)
      have hdiv : Z / freeStart m ((i + 1) * (K₀ + 1)) ≤ Z / u :=
        Nat.div_le_div_left (hfsu _ hb) hu0
      exact Finset.mem_Icc.2 ⟨hpp.one_lt.le, le_trans hple hdiv⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this

end

end RHTower.Sieve
