import GaloisForLFunctions.RHTower.ZetaNotchTwistedOffDiagonal
import GaloisForLFunctions.RHTower.Sieve.TwistedOffDiagonalSum

/-!
# Full reciprocal-square gap budget for an integer twist

For conductor `T ≥ 1` and integer twist `n ≥ 1`, the complete positive-pair sum

`Σ_(r,m≥1) (rm)^(-1/2) min(1,T/(rm))² / (log(m/r)-log n)²`

is at most `(48 n² integerGapBudget + 16 pairZeta) T`. Diagonal terms are zero,
using the field convention for division by zero. Near the diagonal, distinct
integer gaps give a summable reciprocal-square row; far pairs use the existing
full pair-weight estimate. No pair cutoff or unproved arithmetic estimate enters.

This is the arithmetic input for two integrations by parts on a square-root
window. It does not itself prove a twisted zeta moment, a derivative-correlation
sign, positive cancellation, or the spectral-deficit target.
-/

noncomputable section
open scoped BigOperators
open RHTower.ZetaNotch
namespace RHTower.WeilWorkDeficitGap

/-- Total reciprocal-square mass of the integer lattice; its zero term is zero. -/
def integerGapBudget : ℝ := ∑' z : ℤ, 1 / (z : ℝ) ^ 2

private theorem integer_gap_summable : Summable (fun z : ℤ => 1 / (z : ℝ) ^ 2) :=
  Real.summable_one_div_int_pow.mpr (by norm_num)

private theorem integer_gap_nonneg : 0 ≤ integerGapBudget :=
  tsum_nonneg fun _ => by positivity

private def rowGap (n a b : ℕ) : ℝ :=
  1 / (((b : ℝ) + 1) - ((a : ℝ) + 1) * n) ^ 2

private theorem row_gap_summable (n a : ℕ) : Summable (rowGap n a) := by
  let e : ℕ → ℤ := fun b => (b : ℤ) + 1 - ((a : ℤ) + 1) * n
  have he : Function.Injective e := by
    intro b c h
    dsimp [e] at h
    exact_mod_cast (by omega : (b : ℤ) = c)
  apply (integer_gap_summable.comp_injective he).congr
  intro b
  dsimp [e, rowGap]
  push_cast
  rfl

private theorem row_gap_le (n a : ℕ) : ∑' b, rowGap n a b ≤ integerGapBudget := by
  let e : ℕ → ℤ := fun b => (b : ℤ) + 1 - ((a : ℤ) + 1) * n
  have he : Function.Injective e := by
    intro b c h
    dsimp [e] at h
    exact_mod_cast (by omega : (b : ℤ) = c)
  apply Summable.tsum_le_tsum_of_inj e he (fun _ _ => by positivity)
    (fun b => ?_) (row_gap_summable n a) integer_gap_summable
  dsimp [rowGap, e]
  push_cast
  rfl

private def radialWeight (a : ℝ) (r : ℕ) : ℝ :=
  ((r : ℝ) + 1) * min 1 (a / ((r : ℝ) + 1) ^ 2) ^ 2

private theorem radial_weight_le {a : ℝ} (ha : 0 ≤ a) (r : ℕ) :
    radialWeight a r ≤ Real.sqrt a * min 1 (a / ((r : ℝ) + 1) ^ 2) := by
  set m : ℝ := r + 1
  have hm : 0 < m := by positivity
  have hq : 0 ≤ min 1 (a / m ^ 2) := by positivity
  have hbound : m * min 1 (a / m ^ 2) ≤ Real.sqrt a := by
    rcases le_or_gt (m ^ 2) a with h | h
    · rw [min_eq_left ((le_div_iff₀ (sq_pos_of_pos hm)).mpr (by simpa using h)), mul_one]
      exact (Real.le_sqrt hm.le ha).mpr h
    · rw [min_eq_right ((div_le_one (sq_pos_of_pos hm)).mpr h.le)]
      have hs : Real.sqrt a ≤ m := Real.sqrt_le_iff.mpr ⟨hm.le, h.le⟩
      have heq : m * (a / m ^ 2) = a / m := by field_simp
      rw [heq, div_le_iff₀ hm]
      nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]
  dsimp [radialWeight]
  change m * min 1 (a / m ^ 2) ^ 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hbound hq]

private theorem radial_weight_summable {a : ℝ} (ha : 0 ≤ a) :
    Summable (radialWeight a) :=
  Summable.of_nonneg_of_le (fun r => by dsimp [radialWeight]; positivity)
    (radial_weight_le ha) ((summable_min_one_div_sq a).mul_left (Real.sqrt a))

private theorem radial_weight_tsum_le {a : ℝ} (ha : 0 ≤ a) :
    ∑' r, radialWeight a r ≤ 3 * a := by
  calc ∑' r, radialWeight a r
      ≤ ∑' r : ℕ, Real.sqrt a * min 1 (a / ((r : ℝ) + 1) ^ 2) :=
        (radial_weight_summable ha).tsum_le_tsum (radial_weight_le ha)
          ((summable_min_one_div_sq a).mul_left (Real.sqrt a))
    _ = Real.sqrt a * ∑' r : ℕ, min 1 (a / ((r : ℝ) + 1) ^ 2) := tsum_mul_left
    _ ≤ Real.sqrt a * (3 * Real.sqrt a) :=
      mul_le_mul_of_nonneg_left (tsum_min_one_div_sq_le_three_sqrt ha) (Real.sqrt_nonneg a)
    _ = 3 * a := by nlinarith [Real.sq_sqrt ha]

private def nearMajorant (T : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  8 * (n : ℝ) ^ 2 * radialWeight (2 * T) p.1 * rowGap n p.1 p.2

private theorem near_majorant_nonneg {T : ℝ} (_hT : 0 ≤ T) (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ nearMajorant T n p := by
  dsimp [nearMajorant, radialWeight, rowGap]
  positivity

private theorem near_majorant_summable {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    Summable (nearMajorant T n) := by
  apply (summable_prod_of_nonneg (near_majorant_nonneg hT n)).mpr
  constructor
  · intro a
    exact (row_gap_summable n a).mul_left (8 * (n : ℝ)^2 * radialWeight (2*T) a)
  · refine Summable.of_nonneg_of_le (fun a => tsum_nonneg fun b => near_majorant_nonneg hT n (a,b))
      (fun a => ?_) (((radial_weight_summable (by positivity : 0 ≤ 2*T)).mul_left
        (8 * (n : ℝ)^2)).mul_right integerGapBudget)
    change (∑' b, (8 * (n : ℝ)^2 * radialWeight (2*T) a) * rowGap n a b) ≤ _
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (row_gap_le n a) (by dsimp [radialWeight]; positivity)

private theorem near_majorant_tsum_le {T : ℝ} (hT : 0 ≤ T) (n : ℕ) :
    ∑' p, nearMajorant T n p ≤ 48 * (n : ℝ)^2 * integerGapBudget * T := by
  have hS := near_majorant_summable hT n
  rw [hS.tsum_prod]
  calc ∑' a, ∑' b, nearMajorant T n (a,b)
      ≤ ∑' a, (8 * (n : ℝ)^2 * radialWeight (2*T) a) * integerGapBudget := by
        apply hS.prod.tsum_le_tsum _ (((radial_weight_summable (by positivity : 0 ≤ 2*T)).mul_left
          (8 * (n : ℝ)^2)).mul_right integerGapBudget)
        intro a
        dsimp [nearMajorant]
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (row_gap_le n a) (by dsimp [radialWeight]; positivity)
    _ = (8 * (n : ℝ)^2 * (∑' a, radialWeight (2*T) a)) * integerGapBudget := by
        rw [tsum_mul_right, tsum_mul_left]
    _ ≤ (8 * (n : ℝ)^2 * (3 * (2*T))) * integerGapBudget := by
        gcongr
        · exact integer_gap_nonneg
        · exact radial_weight_tsum_le (by positivity)
    _ = 48 * (n : ℝ)^2 * integerGapBudget * T := by ring

/-- Literal reciprocal-square frequency budget. On a diagonal the summand is zero. -/
def twistedGapWeight (T : ℝ) (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  pairAmp p * min 1 (T / pairProd p) ^ 2 / (pairFreq p - Real.log n) ^ 2

private theorem twisted_gap_nonneg {T : ℝ} (_hT : 0 ≤ T) (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ twistedGapWeight T n p := by
  unfold twistedGapWeight
  exact div_nonneg (mul_nonneg (pairAmp_pos p).le (sq_nonneg _)) (sq_nonneg _)

private theorem twisted_gap_pointwise {T : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 1 ≤ n)
    (p : ℕ × ℕ) :
    twistedGapWeight T n p ≤ nearMajorant T n p + 16 * pairWeight T p := by
  have hfar0 := mul_nonneg (by norm_num : (0:ℝ) ≤ 16) (pairWeight_nonneg hT p)
  have hnear0 := near_majorant_nonneg hT n p
  by_cases hz : pairFreq p - Real.log n = 0
  · simp only [twistedGapWeight, hz, zero_pow (by decide : 2 ≠ 0), div_zero]
    exact add_nonneg hnear0 hfar0
  have hlpos : 0 < (pairFreq p - Real.log n)^2 := sq_pos_of_ne_zero hz
  have hq : 0 ≤ min 1 (T / pairProd p) := le_min zero_le_one (div_nonneg hT (pairProd_pos p).le)
  have hq1 : min 1 (T / pairProd p) ≤ 1 := min_le_left _ _
  by_cases hsmall : |pairFreq p - Real.log n| < 1/4
  · set r : ℝ := (p.1 : ℝ) + 1
    set m : ℝ := (p.2 : ℝ) + 1
    have hr : 0 < r := by positivity
    have hm : 0 < m := by positivity
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hres : nearRes n 1 (1/4) p := by
      constructor
      · intro h
        have he : m = r*n := by
          dsimp [m, r]
          simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, mul_one] using congrArg (fun x : ℕ => (x : ℝ)) h
        apply hz
        dsimp [pairFreq]
        change Real.log m - Real.log r - Real.log n = 0
        rw [he, Real.log_mul hr.ne' hn0.ne']
        ring
      · simp only [Nat.cast_one, div_one]
        change |Real.log (m/r) - Real.log n| < 1/4
        rw [Real.log_div hm.ne' hr.ne']
        exact hsmall
    obtain ⟨hlo, hgap, hhi⟩ := nearRes_bounds hn (by omega : 1 ≤ (1:ℕ)) (by norm_num) hres
    norm_num only [Nat.cast_one, mul_one] at hlo hgap hhi
    change r * n / 2 ≤ m at hlo
    change 1 ≤ |m - r*n| at hgap
    change |m - r*n| ≤ (1/2:ℝ) * (r*n) at hhi
    have hmhi : m ≤ 2*r*n := by have := (abs_le.mp hhi).2; nlinarith
    have hprod : r^2 / 2 ≤ pairProd p := by
      change r^2 / 2 ≤ r*m
      nlinarith [mul_le_mul_of_nonneg_left hnR hr.le]
    have hmax : max m (r*n) ≤ 2*r*n := max_le hmhi (by nlinarith)
    have hlogeq : Real.log m - Real.log (r*n) = pairFreq p - Real.log n := by
      rw [Real.log_mul hr.ne' hn0.ne']
      dsimp [pairFreq, r, m]
      ring
    have hlog := Sieve.abs_sub_div_max_le_abs_log_sub_log hm (mul_pos hr hn0)
    rw [hlogeq] at hlog
    have hmaxpos : 0 < max m (r*n) := lt_of_lt_of_le hm (le_max_left _ _)
    have hg_le : |m-r*n| ≤ 2*r*n * |pairFreq p - Real.log n| := by
      have h1 := (div_le_iff₀ hmaxpos).mp hlog
      exact h1.trans ((mul_le_mul_of_nonneg_left hmax (abs_nonneg _)).trans_eq (mul_comm _ _))
    have hgpos : 0 < (m-r*n)^2 := by nlinarith [sq_abs (m-r*n)]
    have hinv : 1 / (pairFreq p - Real.log n)^2 ≤ (2*r*n)^2 / (m-r*n)^2 := by
      rw [div_le_div_iff₀ hlpos hgpos]
      have hh := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2*r*n*|pairFreq p-Real.log n|) |>.mpr hg_le
      simpa only [sq_abs, mul_pow, one_mul] using hh
    have hamp : pairAmp p ≤ 2/r := by
      rw [pairAmp_eq]
      have hs : r/2 ≤ Real.sqrt (pairProd p) :=
        (Real.le_sqrt (by positivity) (pairProd_pos p).le).mpr (by nlinarith)
      calc (Real.sqrt (pairProd p))⁻¹ ≤ (r/2)⁻¹ := inv_anti₀ (by positivity) hs
        _ = 2/r := by field_simp
    have hqle : min 1 (T / pairProd p) ≤ min 1 (2*T/r^2) := by
      apply min_le_min_left
      rw [div_le_div_iff₀ (pairProd_pos p) (sq_pos_of_pos hr)]
      nlinarith [mul_le_mul_of_nonneg_left hprod hT]
    have hnear : twistedGapWeight T n p ≤ nearMajorant T n p := by
      calc twistedGapWeight T n p
          = (pairAmp p * min 1 (T / pairProd p)^2) * (1 / (pairFreq p - Real.log n)^2) := by
            unfold twistedGapWeight; ring
        _ ≤ ((2/r) * min 1 (2*T/r^2)^2) * ((2*r*n)^2 / (m-r*n)^2) := by
          exact mul_le_mul (mul_le_mul hamp (pow_le_pow_left₀ hq hqle 2) (sq_nonneg _)
            (by positivity)) hinv (by positivity) (by positivity)
        _ = nearMajorant T n p := by
          dsimp [nearMajorant, radialWeight, rowGap]
          change (2/r * min 1 (2*T/r^2)^2) * ((2*r*n)^2/(m-r*n)^2) =
            8*(n:ℝ)^2*(r*min 1 (2*T/r^2)^2)*(1/(m-r*n)^2)
          field_simp; ring
    exact hnear.trans (le_add_of_nonneg_right hfar0)
  · have hbig : 1/4 ≤ |pairFreq p - Real.log n| := le_of_not_gt hsmall
    have hsq : (1:ℝ)/16 ≤ (pairFreq p - Real.log n)^2 := by
      nlinarith [sq_abs (pairFreq p - Real.log n)]
    have hq2 : min 1 (T / pairProd p)^2 ≤ min 1 (T / pairProd p) := by nlinarith
    have hfar : twistedGapWeight T n p ≤ 16 * pairWeight T p := by
      rw [twistedGapWeight, div_le_iff₀ hlpos, pairWeight_eq]
      have ha := (pairAmp_pos p).le
      nlinarith [mul_le_mul_of_nonneg_left hq2 ha,
        mul_le_mul_of_nonneg_left hsq (mul_nonneg ha hq)]
    exact hfar.trans (le_add_of_nonneg_left hnear0)

/-- All actual rational-twist reciprocal-square gaps are summable. -/
theorem summable_twistedGapWeight {T : ℝ} (hT : 0 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    Summable (twistedGapWeight T n) :=
  Summable.of_nonneg_of_le (twisted_gap_nonneg hT n) (twisted_gap_pointwise hT hn)
    ((near_majorant_summable hT n).add ((summable_pairWeight hT).mul_left 16))

/-- Full gap budget at conductor T, including every positive factor pair. -/
theorem tsum_twistedGapWeight_le {T : ℝ} (hT : 1 ≤ T) {n : ℕ} (hn : 1 ≤ n) :
    ∑' p, twistedGapWeight T n p ≤
      (48 * (n : ℝ)^2 * integerGapBudget + 16 * pairZeta) * T := by
  have hT0 : 0 ≤ T := by linarith
  calc ∑' p, twistedGapWeight T n p
      ≤ ∑' p, (nearMajorant T n p + 16 * pairWeight T p) :=
        (summable_twistedGapWeight hT0 hn).tsum_le_tsum (twisted_gap_pointwise hT0 hn)
          ((near_majorant_summable hT0 n).add ((summable_pairWeight hT0).mul_left 16))
    _ = (∑' p, nearMajorant T n p) + 16 * ∑' p, pairWeight T p := by
        rw [Summable.tsum_add (near_majorant_summable hT0 n) ((summable_pairWeight hT0).mul_left 16), tsum_mul_left]
    _ ≤ 48 * (n:ℝ)^2 * integerGapBudget * T + 16 * (pairZeta * T^(3/4:ℝ)) := by
        gcongr
        · exact near_majorant_tsum_le hT0 n
        · exact tsum_pairWeight_le hT0
    _ ≤ (48 * (n:ℝ)^2 * integerGapBudget + 16 * pairZeta) * T := by
        have hp : T^(3/4:ℝ) ≤ T := by
          simpa using Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (3/4:ℝ) ≤ 1)
        nlinarith [mul_le_mul_of_nonneg_left hp pairZeta_nonneg]

end RHTower.WeilWorkDeficitGap
