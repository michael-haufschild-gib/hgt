import GaloisForLFunctions.RHTower.Sieve.FreeScaleFitSupply
import GaloisForLFunctions.RHTower.Sieve.CardLengthDilation

/-!
# One tile of the free-scale marker construction

A single start modulus `m = 2^{K₀+1}u` serves every physical scale `X` in the dyadic range
`[P, 2P]`, where `P = m²⌊log m⌋`.  The window length is the same natural number `h` throughout the
range, chosen so that the fit condition (at the top of the range) and the supply condition (at the
bottom) hold simultaneously.
-/

namespace RHTower.Sieve

open Finset Filter

noncomputable section

/-- The start modulus of the tile family. -/
def tileM (K₀ u : ℕ) : ℕ := 2 ^ (K₀ + 1) * u

/-- The integer part of the logarithm of the start modulus. -/
def tileLog (K₀ u : ℕ) : ℕ := ⌊Real.log ((tileM K₀ u : ℕ) : ℝ)⌋₊

/-- The bottom of the physical range served by one start modulus. -/
def tileBase (K₀ u : ℕ) : ℕ := tileM K₀ u * tileM K₀ u * tileLog K₀ u

/-- The base window length of the tile family. -/
def tileC (β : ℝ) (K₀ u : ℕ) : ℝ := cardLength β (freeScale (tileM K₀ u) 0)

/-- The window length of one tile. -/
def tileLen (β : ℝ) (K₀ u : ℕ) : ℕ :=
  ⌈(2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
     / ((tileM K₀ u : ℕ) : ℝ)⌉₊

theorem tileC_pos (β : ℝ) (K₀ u : ℕ) : 0 < tileC β K₀ u := cardLength_pos _ _

theorem tileM_pos {K₀ u : ℕ} (hu : 0 < u) : 0 < tileM K₀ u := by
  rw [tileM]; positivity

theorem tileM_dvd (K₀ u : ℕ) : 2 ^ (K₀ + 1) ∣ tileM K₀ u := dvd_pow_mul K₀ u

/-- **Every start of the ladder is at least two.** -/
theorem tile_start_two {K₀ u k : ℕ} (hu : 0 < u) (hk : k ≤ K₀) : 2 ≤ freeStart (tileM K₀ u) k := by
  rw [tileM, freeStart_pow_mul (by omega)]
  have h1 : 1 ≤ K₀ + 1 - k := by omega
  have h2 : (2 : ℕ) ^ (1 : ℕ) ≤ 2 ^ (K₀ + 1 - k) := Nat.pow_le_pow_right (by norm_num) h1
  have h3 : 1 ≤ u := hu
  calc (2 : ℕ) = 2 ^ (1 : ℕ) * 1 := by norm_num
    _ ≤ 2 ^ (K₀ + 1 - k) * u := Nat.mul_le_mul h2 h3

/-- **The smallest start is positive.** -/
theorem tile_startK_pos {K₀ u : ℕ} (hu : 0 < u) : 0 < freeStart (tileM K₀ u) (K₀ + 1) := by
  rw [tileM]
  exact freeStart_pow_mul_pos hu (le_refl _)

/-- **The window at the `k`-th block, undilated.** -/
theorem freeWindow_mul_pow (β : ℝ) (m k : ℕ) :
    freeWindow β m k * (2 : ℝ) ^ k = cardLength β (freeScale m k) := by
  rw [freeWindow, scaledLength, div_pow, one_pow]
  field_simp

/-- **The start modulus does not exceed the bottom of its range.** -/
theorem tileM_le_base {K₀ u : ℕ} (hu : 0 < u) (hlog : 1 ≤ tileLog K₀ u) :
    tileM K₀ u ≤ tileBase K₀ u := by
  have hm := tileM_pos (K₀ := K₀) hu
  rw [tileBase]
  calc tileM K₀ u = tileM K₀ u * 1 * 1 := by ring
    _ ≤ tileM K₀ u * tileM K₀ u * tileLog K₀ u := Nat.mul_le_mul (Nat.mul_le_mul_left _ hm) hlog

/-- **The fit condition holds at every scale of the tile range.** -/
theorem tile_fit {β : ℝ} (hβ : 0 < β) {K₀ u X k p : ℕ} (hu : 0 < u) (hk : k ≤ K₀)
    (hX : X ≤ 2 * tileBase K₀ u) (hp : p ∈ freeBlock X (tileM K₀ u) k) :
    (freeWindow β (tileM K₀ u) k + 1) * (p : ℝ) ≤ ((tileLen β K₀ u : ℕ) : ℝ) := by
  have hm := tileM_pos (K₀ := K₀) hu
  have hmR : (0 : ℝ) < ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm
  have hC := tileC_pos β K₀ u
  have hcoef : (0 : ℝ) < 2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1) := by positivity
  refine free_fit_of_le hβ hk (tile_startK_pos hu) (tileM_dvd K₀ u) (tile_start_two hu hk) hp ?_
  refine le_trans ?_ (Nat.le_ceil _)
  have hXR : (X : ℝ) ≤ 2 * ((tileBase K₀ u : ℕ) : ℝ) := by exact_mod_cast hX
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hXR hcoef.le) hmR.le

/-- **The supply condition holds at every scale of the tile range.** -/
theorem tile_supply {β : ℝ} {K₀ u X k p : ℕ} (hu : 0 < u) (hk : k ≤ K₀)
    (hlog : 1 ≤ tileLog K₀ u) (hX : tileBase K₀ u ≤ X)
    (hhalf : tileC β K₀ u / 2 ≤ cardLength β (freeScale (tileM K₀ u) k))
    (hgap : (2 : ℝ) ^ (K₀ + 2) + 48 * (2 : ℝ) ^ K₀ + 1 ≤ 8 * tileC β K₀ u)
    (hp : p ∈ freeBlock X (tileM K₀ u) k) :
    (squarefreeDensity / 256) * (((tileLen β K₀ u : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity * (freeWindow β (tileM K₀ u) k / 2 - 1) := by
  have hm := tileM_pos (K₀ := K₀) hu
  have hmR : (0 : ℝ) < ((tileM K₀ u : ℕ) : ℝ) := by exact_mod_cast hm
  have hC := tileC_pos β K₀ u
  have hcoef : (0 : ℝ) < 2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1) := by positivity
  set A2 : ℝ := 2 * (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) + 1 with hA2def
  have hA2 : 0 < A2 := by rw [hA2def]; positivity
  have hmX : tileM K₀ u ≤ X := le_trans (tileM_le_base hu hlog) hX
  have hXR : ((tileBase K₀ u : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hone : (1 : ℝ) ≤ (X : ℝ) / ((tileM K₀ u : ℕ) : ℝ) := by
    rw [le_div_iff₀ hmR, one_mul]
    exact_mod_cast hmX
  refine free_supply_of_le hk (tile_startK_pos hu) (tileM_dvd K₀ u) hp hA2 ?_ ?_
  · -- the ceiling is below `A₂·X/m`
    have hceil : ((tileLen β K₀ u : ℕ) : ℝ)
        ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
            / ((tileM K₀ u : ℕ) : ℝ) + 1 := by
      rw [tileLen]
      have hnn : (0 : ℝ) ≤ (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1))
          * (2 * ((tileBase K₀ u : ℕ) : ℝ)) / ((tileM K₀ u : ℕ) : ℝ) := by
        have : (0 : ℝ) ≤ ((tileBase K₀ u : ℕ) : ℝ) := Nat.cast_nonneg _
        positivity
      linarith [Nat.ceil_lt_add_one hnn]
    refine hceil.trans ?_
    have hstep : (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (2 * ((tileBase K₀ u : ℕ) : ℝ))
          / ((tileM K₀ u : ℕ) : ℝ)
        ≤ 2 * (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (X : ℝ) / ((tileM K₀ u : ℕ) : ℝ) := by
      refine div_le_div_of_nonneg_right ?_ hmR.le
      nlinarith [hXR, hcoef]
    have hval : A2 * (X : ℝ) / ((tileM K₀ u : ℕ) : ℝ)
        = 2 * (2 * tileC β K₀ u + (2 : ℝ) ^ (K₀ + 1)) * (X : ℝ) / ((tileM K₀ u : ℕ) : ℝ)
          + (X : ℝ) / ((tileM K₀ u : ℕ) : ℝ) := by
      rw [hA2def]
      field_simp
      try ring
    rw [hval]
    linarith [hstep, hone]
  · -- the gap condition
    rw [freeWindow_mul_pow]
    have hpk : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K₀ := pow_le_pow_right₀ (by norm_num) hk
    have hp2 : (2 : ℝ) ^ (K₀ + 2) = 4 * (2 : ℝ) ^ K₀ := by rw [pow_add]; ring
    have hp1 : (2 : ℝ) ^ (K₀ + 1) = 2 * (2 : ℝ) ^ K₀ := by rw [pow_add]; ring
    rw [hA2def, hp1]
    rw [hp2] at hgap
    linarith [hhalf, hgap, hpk]

end

end RHTower.Sieve
