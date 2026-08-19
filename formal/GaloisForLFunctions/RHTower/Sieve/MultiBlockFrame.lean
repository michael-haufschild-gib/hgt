import GaloisForLFunctions.RHTower.Sieve.MarkerBlockSignCount
import GaloisForLFunctions.RHTower.Sieve.CardLengthDilation

/-!
# The parameters of a family of dyadic marker blocks

A single dyadic block of markers carries harmonic mass `log 2/log M₀`, which the explicit constant
in Mertens' second theorem swamps.  A family of `K₀` consecutive dyadic blocks carries
`K₀·log 2/log M₀` against the same constant, so its net mass — and with it the constant in the
target count — grows without bound in `K₀`.

The `k`-th block sits at markers `(2^k M₀, 2^{k+1} M₀]`, whose reciprocal starts fill
`[m/2^{k+1}, m/2^k]`; the cofactor scale of that block is therefore `(m/2^k)²` and its window is
`2^{-k}` times the window of the zeroth block.  All blocks share the physical scale and window.
-/

namespace RHTower.Sieve

open Finset

/-! ## The start range of one dyadic block -/

/-- **Every marker of the `k`-th block has a start above `w`.** -/
theorem block_start_ge {w M₀ k p : ℕ} (hp : 0 < p) (hM₀ : 0 < M₀)
    (hple : p ≤ 2 ^ (k + 1) * M₀) :
    w ≤ 2 ^ k * (2 * w) * M₀ / p := by
  have hd : 0 < 2 ^ (k + 1) * M₀ := by positivity
  have h1 : 2 ^ k * (2 * w) * M₀ / (2 ^ (k + 1) * M₀) ≤ 2 ^ k * (2 * w) * M₀ / p :=
    Nat.div_le_div_left hple hp
  have h2 : 2 ^ k * (2 * w) * M₀ / (2 ^ (k + 1) * M₀) = w := by
    rw [show 2 ^ k * (2 * w) * M₀ = w * (2 ^ (k + 1) * M₀) by rw [pow_succ]; ring]
    exact Nat.mul_div_cancel _ hd
  omega

/-- **Every marker of the `k`-th block has a start below `2w`.** -/
theorem block_start_lt {w M₀ k p : ℕ} (hw : 0 < w) (hp : 2 ^ k * M₀ < p) :
    2 ^ k * (2 * w) * M₀ / p < 2 * w := by
  have hp0 : 0 < p := by omega
  refine (Nat.div_lt_iff_lt_mul hp0).2 ?_
  calc 2 ^ k * (2 * w) * M₀ = (2 * w) * (2 ^ k * M₀) := by ring
    _ < (2 * w) * p := mul_lt_mul_of_pos_left hp (by omega : 0 < 2 * w)

/-! ## The parameters -/

noncomputable section

/-- Half of the `k`-th block's cofactor square root. -/
def multiHalf (K₀ v k : ℕ) : ℕ := 2 ^ (K₀ - k) * v

/-- The `k`-th block's cofactor square root. -/
def multiBlockLen (K₀ v k : ℕ) : ℕ := 2 * multiHalf K₀ v k

/-- The base cofactor square root. -/
def multiScale (K₀ v : ℕ) : ℕ := multiBlockLen K₀ v 0

theorem multiScale_eq (K₀ v : ℕ) : multiScale K₀ v = 2 ^ (K₀ + 1) * v := by
  rw [multiScale, multiBlockLen, multiHalf, Nat.sub_zero, pow_succ]
  ring

/-- The lift factor. -/
def multiFactor (K₀ v : ℕ) : ℕ := ⌊Real.log (((multiScale K₀ v : ℕ) : ℝ) ^ 2)⌋₊

/-- The bottom of the marker range. -/
def multiBase (K₀ v : ℕ) : ℕ := multiScale K₀ v * multiFactor K₀ v

/-- The physical scale. -/
def multiPhys (K₀ v : ℕ) : ℕ := multiScale K₀ v * multiBase K₀ v

/-- The cell-length parameter. -/
def multiCell (β : ℝ) (K₀ v : ℕ) : ℕ :=
  ⌈cardLength β (((multiScale K₀ v : ℕ) : ℝ) ^ 2)⌉₊ + 2 ^ K₀

/-- The physical window. -/
def multiWindow (β : ℝ) (K₀ v : ℕ) : ℕ := 2 * multiCell β K₀ v * multiBase K₀ v

/-- **The physical scale, seen from the `k`-th block.** -/
theorem multiPhys_block (K₀ v : ℕ) {k : ℕ} (hk : k ≤ K₀) :
    multiPhys K₀ v = 2 ^ k * (2 * multiHalf K₀ v k) * multiBase K₀ v := by
  rw [multiPhys, multiScale_eq, multiHalf]
  have : 2 ^ k * (2 * (2 ^ (K₀ - k) * v)) = 2 ^ (K₀ + 1) * v := by
    rw [show (2 : ℕ) ^ k * (2 * (2 ^ (K₀ - k) * v)) = 2 * (2 ^ k * 2 ^ (K₀ - k)) * v by ring,
      ← pow_add, show k + (K₀ - k) = K₀ from by omega,
      show (2 : ℕ) ^ (K₀ + 1) = 2 * 2 ^ K₀ by rw [pow_succ]; ring]
  rw [this]

/-- The `k`-th block's cofactor scale. -/
def multiBlockScale (K₀ v k : ℕ) : ℝ := ((multiBlockLen K₀ v k : ℕ) : ℝ) ^ 2

theorem sqrt_multiBlockScale (K₀ v k : ℕ) :
    Real.sqrt (multiBlockScale K₀ v k) = ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
  rw [multiBlockScale, Real.sqrt_sq (by positivity)]

/-- The `k`-th block's window: the base window shrunk by `2^{-k}`. -/
def multiBlockWindow (β : ℝ) (K₀ v k : ℕ) : ℝ :=
  scaledLength (((1 : ℝ) / 2) ^ k) β (multiBlockScale K₀ v k)

theorem multiBlockWindow_pos (β : ℝ) (K₀ v k : ℕ) : 0 < multiBlockWindow β K₀ v k := by
  rw [multiBlockWindow]
  exact scaledLength_pos (by positivity) _ _

/-! ## The fit and the supply, block by block -/

/-- The window length is monotone in the scale. -/
theorem cardLength_mono {β : ℝ} (hβ : 0 < β) {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    cardLength β y ≤ cardLength β z := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : Real.log y ≤ Real.log z := Real.log_le_log hy0 hyz
  have hlog0 : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy
  rw [cardLength, cardLength]
  exact Real.exp_le_exp.2 (Real.rpow_le_rpow hlog0 hlog hβ.le)

/-- The `k`-th block's cofactor scale is below the base one. -/
theorem multiBlockScale_le {K₀ v k : ℕ} (hk : k ≤ K₀) :
    multiBlockScale K₀ v k ≤ multiBlockScale K₀ v 0 := by
  have hle : multiBlockLen K₀ v k ≤ multiBlockLen K₀ v 0 := by
    rw [multiBlockLen, multiBlockLen, multiHalf, multiHalf, Nat.sub_zero]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num)
      (by omega)))
  have hleR : ((multiBlockLen K₀ v k : ℕ) : ℝ) ≤ ((multiBlockLen K₀ v 0 : ℕ) : ℝ) := by
    exact_mod_cast hle
  rw [multiBlockScale, multiBlockScale]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hleR 2

/-- **The fibre of the `k`-th block fits inside the marker's cell.** -/
theorem multi_fit {β : ℝ} {K₀ v k p : ℕ} (hβ : 0 < β) (hv : 0 < v) (hk : k ≤ K₀)
    (hpl : 2 ^ k * multiBase K₀ v < p) (hpu : p ≤ 2 ^ (k + 1) * multiBase K₀ v) :
    (multiBlockWindow β K₀ v k
          * (((multiPhys K₀ v / p : ℕ) : ℝ) + 1) / ((multiBlockLen K₀ v k : ℕ) : ℝ) + 1)
        * (p : ℝ)
      ≤ ((multiWindow β K₀ v : ℕ) : ℝ) := by
  have hw : 0 < multiHalf K₀ v k := by
    rw [multiHalf]
    positivity
  have hM0 : (0 : ℕ) < multiBase K₀ v := by
    by_contra hc
    push Not at hc
    interval_cases h : multiBase K₀ v
    · simp at hpl
      omega
  have hp0 : 0 < p := by omega
  have hlen : multiBlockLen K₀ v k = 2 * multiHalf K₀ v k := rfl
  have hstart := block_start_lt (w := multiHalf K₀ v k) (M₀ := multiBase K₀ v) (k := k)
    hw (by rw [← multiPhys_block K₀ v hk] at *; exact hpl)
  rw [← multiPhys_block K₀ v hk] at hstart
  have hstartR : ((multiPhys K₀ v / p : ℕ) : ℝ) + 1 ≤ ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
    have : multiPhys K₀ v / p + 1 ≤ multiBlockLen K₀ v k := by rw [hlen]; omega
    exact_mod_cast this
  have hmk0 : (0 : ℝ) < ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
    have : (0 : ℕ) < multiBlockLen K₀ v k := by rw [hlen]; omega
    exact_mod_cast this
  have hy0 : (0 : ℝ) < multiBlockWindow β K₀ v k := multiBlockWindow_pos β K₀ v k
  have hquot : multiBlockWindow β K₀ v k * (((multiPhys K₀ v / p : ℕ) : ℝ) + 1)
      / ((multiBlockLen K₀ v k : ℕ) : ℝ) ≤ multiBlockWindow β K₀ v k := by
    rw [div_le_iff₀ hmk0]
    exact mul_le_mul_of_nonneg_left hstartR hy0.le
  -- the block window against the cell parameter
  have hone : (1 : ℝ) ≤ multiBlockScale K₀ v k := by
    rw [multiBlockScale]
    have : (2 : ℝ) ≤ ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
      have : 2 ≤ multiBlockLen K₀ v k := by rw [hlen]; omega
      exact_mod_cast this
    nlinarith
  have hmono : cardLength β (multiBlockScale K₀ v k) ≤ cardLength β (multiBlockScale K₀ v 0) :=
    cardLength_mono hβ hone (multiBlockScale_le hk)
  have hbase : multiBlockScale K₀ v 0 = ((multiScale K₀ v : ℕ) : ℝ) ^ 2 := rfl
  have hCbig : cardLength β (multiBlockScale K₀ v 0) + (2 : ℝ) ^ K₀
      ≤ ((multiCell β K₀ v : ℕ) : ℝ) := by
    rw [multiCell, hbase]
    push_cast
    have := Nat.le_ceil (cardLength β (((multiScale K₀ v : ℕ) : ℝ) ^ 2))
    rw [← hbase]
    linarith
  have hshrink : multiBlockWindow β K₀ v k
      ≤ ((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) := by
    rw [multiBlockWindow, scaledLength]
    refine mul_le_mul_of_nonneg_left (by linarith [hmono, hCbig]) (by positivity)
  -- assemble
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hpu' : (p : ℝ) ≤ (2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ) := by
    exact_mod_cast hpu
  have hMR : (0 : ℝ) ≤ ((multiBase K₀ v : ℕ) : ℝ) := Nat.cast_nonneg _
  have hwin : ((multiWindow β K₀ v : ℕ) : ℝ)
      = 2 * ((multiCell β K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiWindow]
    push_cast
    ring
  have hstep : (multiBlockWindow β K₀ v k + 1) * (p : ℝ)
      ≤ (((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + 1)
        * ((2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ)) := by
    refine mul_le_mul (by linarith [hshrink]) hpu' hpR.le (by positivity)
  have hpow : ((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ (k + 1) = 2 := by
    rw [div_pow, one_pow, pow_succ]
    field_simp
  have hK : (2 : ℝ) ^ (k + 1) ≤ (2 : ℝ) ^ (K₀ + 1) := by
    refine pow_le_pow_right₀ (by norm_num) (by omega)
  have hfinal : (((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + 1)
      * ((2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ))
      ≤ 2 * ((multiCell β K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    have hexp : (((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + 1)
        * ((2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ))
        = (2 * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + (2 : ℝ) ^ (k + 1))
          * ((multiBase K₀ v : ℕ) : ℝ) := by
      rw [show (((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + 1)
            * ((2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ))
          = (((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ (k + 1)
              * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀)
            + (2 : ℝ) ^ (k + 1)) * ((multiBase K₀ v : ℕ) : ℝ) by ring, hpow]
    rw [hexp]
    refine mul_le_mul_of_nonneg_right ?_ hMR
    have h2 : (2 : ℝ) ^ (K₀ + 1) = 2 * (2 : ℝ) ^ K₀ := by rw [pow_succ]; ring
    linarith [hK, h2]
  rw [hwin]
  calc (multiBlockWindow β K₀ v k * (((multiPhys K₀ v / p : ℕ) : ℝ) + 1)
          / ((multiBlockLen K₀ v k : ℕ) : ℝ) + 1) * (p : ℝ)
      ≤ (multiBlockWindow β K₀ v k + 1) * (p : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith [hquot]) hpR.le
    _ ≤ (((1 : ℝ) / 2) ^ k * (((multiCell β K₀ v : ℕ) : ℝ) - (2 : ℝ) ^ K₀) + 1)
        * ((2 : ℝ) ^ (k + 1) * ((multiBase K₀ v : ℕ) : ℝ)) := hstep
    _ ≤ 2 * ((multiCell β K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := hfinal

/-- **The fibre of the `k`-th block fills a definite fraction of the marker's cell.** -/
theorem multi_supply {β : ℝ} {K₀ v k p : ℕ} (hk : k ≤ K₀) (hv : 0 < v)
    (hM0 : 0 < multiBase K₀ v) (hpl : 2 ^ k * multiBase K₀ v < p)
    (hpu : p ≤ 2 ^ (k + 1) * multiBase K₀ v)
    (hC : ((multiCell β K₀ v : ℕ) : ℝ)
      ≤ 12 * cardLength β (multiBlockScale K₀ v k) - 24 * (2 : ℝ) ^ k) :
    (squarefreeDensity / 256) * (((multiWindow β K₀ v : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (multiBlockWindow β K₀ v k * ((multiPhys K₀ v / p : ℕ) : ℝ)
              / ((multiBlockLen K₀ v k : ℕ) : ℝ) - 1) := by
  have hD : (0 : ℝ) < squarefreeDensity := squarefreeDensity_pos
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hMR : (0 : ℝ) < ((multiBase K₀ v : ℕ) : ℝ) := by exact_mod_cast hM0
  have ht0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hw : 0 < multiHalf K₀ v k := by
    rw [multiHalf]
    positivity
  have hlen : multiBlockLen K₀ v k = 2 * multiHalf K₀ v k := rfl
  have hmk0 : (0 : ℝ) < ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
    have : (0 : ℕ) < multiBlockLen K₀ v k := by rw [hlen]; omega
    exact_mod_cast this
  have hwin : ((multiWindow β K₀ v : ℕ) : ℝ)
      = 2 * ((multiCell β K₀ v : ℕ) : ℝ) * ((multiBase K₀ v : ℕ) : ℝ) := by
    rw [multiWindow]
    push_cast
    ring
  -- the cell of a marker of the block is at most `2C/2^k`
  have hplR : (2 : ℝ) ^ k * ((multiBase K₀ v : ℕ) : ℝ) < (p : ℝ) := by
    exact_mod_cast hpl
  have hcellR : ((multiWindow β K₀ v : ℕ) : ℝ) / (p : ℝ)
      ≤ 2 * ((multiCell β K₀ v : ℕ) : ℝ) / (2 : ℝ) ^ k := by
    rw [hwin, div_le_div_iff₀ hpR ht0]
    have hCnn : (0 : ℝ) ≤ 2 * ((multiCell β K₀ v : ℕ) : ℝ) := by positivity
    nlinarith [hplR, hCnn]
  -- the fibre of the block is at least half its window
  have hstart := block_start_ge (w := multiHalf K₀ v k) (M₀ := multiBase K₀ v) (k := k)
    hp0 hM0 (by rw [← multiPhys_block K₀ v hk] at *; exact hpu)
  rw [← multiPhys_block K₀ v hk] at hstart
  have hstartR : ((multiBlockLen K₀ v k : ℕ) : ℝ) / 2 ≤ ((multiPhys K₀ v / p : ℕ) : ℝ) := by
    have hcast : ((multiHalf K₀ v k : ℕ) : ℝ) ≤ ((multiPhys K₀ v / p : ℕ) : ℝ) := by
      exact_mod_cast hstart
    rw [hlen]
    push_cast
    linarith
  have hy0 : (0 : ℝ) < multiBlockWindow β K₀ v k := multiBlockWindow_pos β K₀ v k
  have hfib : multiBlockWindow β K₀ v k / 2
      ≤ multiBlockWindow β K₀ v k * ((multiPhys K₀ v / p : ℕ) : ℝ)
          / ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
    rw [le_div_iff₀ hmk0, div_mul_eq_mul_div, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [hstartR, hy0, hmk0]
  -- the block window in terms of the base window
  have hWk : multiBlockWindow β K₀ v k
      = ((1 : ℝ) / 2) ^ k * cardLength β (multiBlockScale K₀ v k) := by
    rw [multiBlockWindow, scaledLength]
  have hpowinv : ((1 : ℝ) / 2) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [div_pow, one_pow]
    field_simp
  -- the numeric comparison
  have hkey : (squarefreeDensity / 256) * (2 * ((multiCell β K₀ v : ℕ) : ℝ) / (2 : ℝ) ^ k)
      ≤ (3 / 16) * squarefreeDensity * (multiBlockWindow β K₀ v k / 2 - 1) := by
    rw [hWk]
    rw [div_le_iff₀ ht0] at *
    have hmul : ((1 : ℝ) / 2) ^ k = 1 / (2 : ℝ) ^ k := by
      rw [div_pow, one_pow]
    rw [hmul]
    rw [ge_iff_le, ← sub_nonneg]
    have hexp : (3 / 16) * squarefreeDensity
          * (1 / (2 : ℝ) ^ k * cardLength β (multiBlockScale K₀ v k) / 2 - 1)
        - squarefreeDensity / 256 * (2 * ((multiCell β K₀ v : ℕ) : ℝ) / (2 : ℝ) ^ k)
        = squarefreeDensity / (256 * (2 : ℝ) ^ k)
          * (3 * cardLength β (multiBlockScale K₀ v k)
            - 6 * (2 : ℝ) ^ k * 8 - 2 * ((multiCell β K₀ v : ℕ) : ℝ)) := by
      field_simp
      ring
    rw [hexp]
    have hpos : (0 : ℝ) < squarefreeDensity / (256 * (2 : ℝ) ^ k) := by positivity
    have hbig : 0 ≤ 3 * cardLength β (multiBlockScale K₀ v k)
        - 6 * (2 : ℝ) ^ k * 8 - 2 * ((multiCell β K₀ v : ℕ) : ℝ) := by
      linarith [hC]
    positivity
  have hstep1 : (squarefreeDensity / 256) * (((multiWindow β K₀ v : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ (squarefreeDensity / 256) * (2 * ((multiCell β K₀ v : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
    refine mul_le_mul_of_nonneg_left (by linarith [hcellR]) (by positivity)
  have hstep2 : (3 / 16) * squarefreeDensity * (multiBlockWindow β K₀ v k / 2 - 1)
      ≤ (3 / 16) * squarefreeDensity
          * (multiBlockWindow β K₀ v k * ((multiPhys K₀ v / p : ℕ) : ℝ)
              / ((multiBlockLen K₀ v k : ℕ) : ℝ) - 1) := by
    refine mul_le_mul_of_nonneg_left (by linarith [hfib]) (by positivity)
  linarith [hstep1, hkey, hstep2]

/-- **The cell bound at one good marker of the `k`-th block.** -/
theorem multi_cell_bound {β : ℝ} {K₀ v k p : ℕ} {σ : ℤ} (hβ : 0 < β) (hv : 0 < v)
    (hk : k ≤ K₀) (hσ : σ = 1 ∨ σ = -1) (hM0 : 0 < multiBase K₀ v)
    (hpl : 2 ^ k * multiBase K₀ v < p) (hpu : p ≤ 2 ^ (k + 1) * multiBase K₀ v)
    (hC : ((multiCell β K₀ v : ℕ) : ℝ)
      ≤ 12 * cardLength β (multiBlockScale K₀ v k) - 24 * (2 : ℝ) ^ k)
    (hnot : multiPhys K₀ v / p
      ∉ badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)) :
    (squarefreeDensity / 256) * (((multiWindow β K₀ v : ℕ) : ℝ) / (p : ℝ) - 1)
      ≤ ((((windowCell (multiPhys K₀ v) (multiWindow β K₀ v) p).filter
          (fun b => moebius b = -σ)).card : ℕ) : ℝ) := by
  have hp0 : 0 < p := by omega
  have hw : 0 < multiHalf K₀ v k := by
    rw [multiHalf]
    positivity
  have hlen : multiBlockLen K₀ v k = 2 * multiHalf K₀ v k := rfl
  have hstart := block_start_ge (w := multiHalf K₀ v k) (M₀ := multiBase K₀ v) (k := k)
    hp0 hM0 (by rw [← multiPhys_block K₀ v hk] at *; exact hpu)
  rw [← multiPhys_block K₀ v hk] at hstart
  have hend := block_start_lt (w := multiHalf K₀ v k) (M₀ := multiBase K₀ v) (k := k)
    hw (by rw [← multiPhys_block K₀ v hk] at *; exact hpl)
  rw [← multiPhys_block K₀ v hk] at hend
  have ht1 : 1 ≤ multiPhys K₀ v / p := by omega
  have htlow : ((multiBlockLen K₀ v k : ℕ) : ℝ) / 2 ≤ ((multiPhys K₀ v / p : ℕ) : ℝ) := by
    have hcast : ((multiHalf K₀ v k : ℕ) : ℝ) ≤ ((multiPhys K₀ v / p : ℕ) : ℝ) := by
      exact_mod_cast hstart
    rw [hlen]
    push_cast
    linarith
  have hthigh : ((multiPhys K₀ v / p : ℕ) : ℝ) + 1 ≤ ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
    have : multiPhys K₀ v / p + 1 ≤ multiBlockLen K₀ v k := by rw [hlen]; omega
    exact_mod_cast this
  have hy4 : (4 : ℝ) ≤ multiBlockScale K₀ v k := by
    rw [multiBlockScale]
    have h2 : (2 : ℝ) ≤ ((multiBlockLen K₀ v k : ℕ) : ℝ) := by
      have : 2 ≤ multiBlockLen K₀ v k := by rw [hlen]; omega
      exact_mod_cast this
    nlinarith
  exact cell_bound_of_good_start hy4 (multiBlockWindow_pos β K₀ v k)
    (sqrt_multiBlockScale K₀ v k) hp0 hσ ht1 htlow hthigh hnot
    (multi_fit hβ hv hk hpl hpu) (multi_supply hk hv hM0 hpl hpu hC)

/-! ## The family of blocks -/

/-- Every marker of the range lies in exactly one dyadic block. -/
theorem exists_block {M₀ p : ℕ} (K : ℕ) (hpl : M₀ < p) (hpu : p ≤ 2 ^ (K + 1) * M₀) :
    ∃ k, k ≤ K ∧ 2 ^ k * M₀ < p ∧ p ≤ 2 ^ (k + 1) * M₀ := by
  induction K with
  | zero =>
      exact ⟨0, le_rfl, by simpa using hpl, by simpa using hpu⟩
  | succ K ih =>
      by_cases hle : p ≤ 2 ^ (K + 1) * M₀
      · obtain ⟨k, hk, h1, h2⟩ := ih hle
        exact ⟨k, by omega, h1, h2⟩
      · refine ⟨K + 1, le_rfl, by omega, hpu⟩

open Classical in
/-- The exceptional starts of the whole family. -/
noncomputable def badStartUnion (β : ℝ) (K₀ v : ℕ) : Finset ℕ :=
  (Finset.range (K₀ + 1)).biUnion
    (fun k => badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k))

open Classical in
/-- The good markers of the family. -/
noncomputable def goodMarkers (β : ℝ) (K₀ v : ℕ) : Finset ℕ :=
  (bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).filter
    (fun p => multiPhys K₀ v / p ∉ badStartUnion β K₀ v)

/-- **The sign count of the physical window, from the whole family of blocks.** -/
theorem card_sign_window_ge_multi {β : ℝ} {K₀ v : ℕ} {σ : ℤ} {S B : ℝ}
    (hβ : 0 < β) (hv : 0 < v) (hσ : σ = 1 ∨ σ = -1) (hM0 : 0 < multiBase K₀ v)
    (hXH : multiPhys K₀ v + multiWindow β K₀ v ≤ multiBase K₀ v * multiBase K₀ v)
    (hC : ∀ k, k ≤ K₀ → ((multiCell β K₀ v : ℕ) : ℝ)
      ≤ 12 * cardLength β (multiBlockScale K₀ v k) - 24 * (2 : ℝ) ^ k)
    (hS : S ≤ ∑ p ∈ goodMarkers β K₀ v, 1 / (p : ℝ))
    (hB : (((goodMarkers β K₀ v).card : ℕ) : ℝ) ≤ B) :
    (squarefreeDensity / 256) * (((multiWindow β K₀ v : ℕ) : ℝ) * S - B)
      ≤ ((((Finset.Ioc (multiPhys K₀ v) (multiPhys K₀ v + multiWindow β K₀ v)).filter
          (fun n => moebius n = σ)).card : ℕ) : ℝ) := by
  classical
  have hsub : goodMarkers β K₀ v
      ⊆ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v) :=
    Finset.filter_subset _ _
  refine card_sign_window_ge (M₀ := multiBase K₀ v) (Q := 2 ^ (K₀ + 1))
    (goodMarkers β K₀ v) hsub hXH (by positivity) ?_ hS hB
  intro p hp
  have hpM : p ∈ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v) := hsub hp
  have hpl : multiBase K₀ v < p := lt_of_mem_bigPrimeSet hpM
  have hpu : p ≤ 2 ^ (K₀ + 1) * multiBase K₀ v :=
    (Finset.mem_Icc.1 (Finset.mem_filter.1 hpM).1).2
  obtain ⟨k, hk, h1, h2⟩ := exists_block K₀ hpl hpu
  have hnot : multiPhys K₀ v / p ∉ badStartUnion β K₀ v := (Finset.mem_filter.1 hp).2
  have hnotk : multiPhys K₀ v / p
      ∉ badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k) := by
    intro hc
    exact hnot (Finset.mem_biUnion.2 ⟨k, Finset.mem_range.2 (by omega), hc⟩)
  exact multi_cell_bound hβ hv hk hσ hM0 h1 h2 (hC k hk) hnotk

/-! ## The device on the whole family -/

/-- The minimal start of the family. -/
theorem multi_start_ge_base {K₀ v p : ℕ} (hp : 0 < p) (hM0 : 0 < multiBase K₀ v)
    (hpu : p ≤ 2 ^ (K₀ + 1) * multiBase K₀ v) :
    v ≤ multiPhys K₀ v / p := by
  have h1 : multiPhys K₀ v / (2 ^ (K₀ + 1) * multiBase K₀ v) ≤ multiPhys K₀ v / p :=
    Nat.div_le_div_left hpu hp
  have h2 : multiPhys K₀ v / (2 ^ (K₀ + 1) * multiBase K₀ v) = v := by
    rw [multiPhys, multiScale_eq,
      show 2 ^ (K₀ + 1) * v * multiBase K₀ v = v * (2 ^ (K₀ + 1) * multiBase K₀ v) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  omega

/-- The separation constant of the family. -/
theorem multi_sep_const (K₀ v : ℕ) (hv : 0 < v) :
    multiPhys K₀ v / (v * v) = 4 ^ (K₀ + 1) * multiFactor K₀ v := by
  rw [multiPhys, multiBase, multiScale_eq,
    show 2 ^ (K₀ + 1) * v * (2 ^ (K₀ + 1) * v * multiFactor K₀ v)
        = (4 ^ (K₀ + 1) * multiFactor K₀ v) * (v * v) by
      rw [show (4 : ℕ) ^ (K₀ + 1) = 2 ^ (K₀ + 1) * 2 ^ (K₀ + 1) by
        rw [← mul_pow]; norm_num]
      ring]
  exact Nat.mul_div_cancel _ (by positivity)

/-- **Markers of the family sharing a start are close.** -/
theorem multi_separation {K₀ v p q : ℕ} (hv : 0 < v) (hM0 : 0 < multiBase K₀ v)
    (hp : 0 < p) (hpq : p < q) (hpu : p ≤ 2 ^ (K₀ + 1) * multiBase K₀ v)
    (heq : multiPhys K₀ v / q = multiPhys K₀ v / p) :
    q ≤ p + 4 ^ (K₀ + 1) * multiFactor K₀ v := by
  have hAt : v ≤ multiPhys K₀ v / p := multi_start_ge_base hp hM0 hpu
  have := reciprocal_separation (X := multiPhys K₀ v) (A := v) hv hp hpq hAt heq
  rw [multi_sep_const K₀ v hv] at this
  exact this

/-- **The harmonic mass and the count of the good markers.** -/
theorem sum_inv_goodMarkers_ge {β : ℝ} {K₀ v K : ℕ} {Pi b : ℝ} (hv : 0 < v)
    (hM0 : 0 < multiBase K₀ v) (hK : 4 ^ (K₀ + 1) * multiFactor K₀ v ≤ K)
    (hpair : ∑ d ∈ Finset.Icc 1 K,
        ((((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).filter
          (fun p => p + d ∈ bigPrimeSet (multiBase K₀ v)
            (2 ^ (K₀ + 1) * multiBase K₀ v))).card : ℕ) : ℝ) ≤ Pi)
    (hbthr : (((badStartUnion β K₀ v).card : ℕ) : ℝ)
      * ((((bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v)).card : ℕ) : ℝ)
        + 2 * Pi) ≤ b ^ 2) (hb0 : 0 ≤ b) :
    (∑ p ∈ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v), 1 / (p : ℝ))
        - b / ((multiBase K₀ v : ℕ) : ℝ)
      ≤ ∑ p ∈ goodMarkers β K₀ v, 1 / (p : ℝ) := by
  classical
  have hsep : ∀ p ∈ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v),
      ∀ q ∈ bigPrimeSet (multiBase K₀ v) (2 ^ (K₀ + 1) * multiBase K₀ v), p < q →
      multiPhys K₀ v / q = multiPhys K₀ v / p → q ≤ p + K := by
    intro p hp q _ hpq heq
    have hp0 : 0 < p := (prime_of_mem_bigPrimeSet hp).pos
    have hpu : p ≤ 2 ^ (K₀ + 1) * multiBase K₀ v :=
      (Finset.mem_Icc.1 (Finset.mem_filter.1 hp).1).2
    have := multi_separation hv hM0 hp0 hpq hpu heq
    omega
  exact sum_inv_good_markers_ge (X := multiPhys K₀ v) (M₀ := multiBase K₀ v) (K := K)
    (S := badStartUnion β K₀ v) hM0 (fun p hp => lt_of_mem_bigPrimeSet hp) hsep hpair
    hbthr hb0

/-- The exceptional starts of the family are the union of the blocks'. -/
theorem card_badStartUnion_le (β : ℝ) (K₀ v : ℕ) :
    (((badStartUnion β K₀ v).card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.range (K₀ + 1),
          (((badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ) := by
  classical
  have h := Finset.card_biUnion_le (s := Finset.range (K₀ + 1))
    (t := fun k => badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k))
  have hcast : (((badStartUnion β K₀ v).card : ℕ) : ℝ)
      ≤ ((∑ k ∈ Finset.range (K₀ + 1),
          (badStart (multiBlockScale K₀ v k) (multiBlockWindow β K₀ v k)).card : ℕ) : ℝ) := by
    rw [badStartUnion]
    exact_mod_cast h
  refine hcast.trans (le_of_eq ?_)
  push_cast
  ring

end

end RHTower.Sieve
