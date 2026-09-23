import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegRouteTUniform
import GaloisForLFunctions.RHTower.Sieve.RouteTWidthExplicit
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

/-!
# The Route-T zero-free width from above

`Sieve/RouteTWidthExplicit.routeTWidthPolylogLower` bounds the Route-T width from *below* by an
explicit reciprocal polylogarithm, which is what makes the contour saving `x^{-w/3}` beat every power
of the logarithm.  The Perron truncation term of the same envelope moves in the opposite direction:
it carries `x^{+2w/3}`, so it needs the width from *above*.

The width is built from `routeTStripWidth V = 1/(D(V+1)^(9 : ℕ))` at `V = routeTBandShell t =
⌊¹⁰√(clog₂⌈t⌉)⌋ + 2`, so an upper bound for it is a *lower* bound for `V`, and that is exactly
`Nat.lt_pow_nthRoot_add_one` together with `Nat.le_pow_clog`.  The result is the matching

`routeTUniformRegWidth A delta (3|τ|/2) ≤ 1/(K·(log|τ|)^{9/10})`,

with `K` an explicit absolute constant.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- The ninth power of the band shell dominates the nine-tenths power of the binary height. -/
theorem rpow_nine_tenths_le_bandShell_pow (n : ℕ) :
    (n : ℝ) ^ ((9 : ℝ) / 10) ≤ ((Nat.nthRoot 10 n + 3 : ℕ) : ℝ) ^ (9 : ℕ) := by
  have hlt : n < (Nat.nthRoot 10 n + 1) ^ 10 := Nat.lt_pow_nthRoot_add_one (by norm_num) n
  have hmono : (Nat.nthRoot 10 n + 1) ^ 10 ≤ (Nat.nthRoot 10 n + 3) ^ 10 :=
    Nat.pow_le_pow_left (by omega) 10
  have hnle : (n : ℝ) ≤ ((Nat.nthRoot 10 n + 3 : ℕ) : ℝ) ^ (10 : ℕ) := by
    have : n ≤ (Nat.nthRoot 10 n + 3) ^ 10 := le_trans hlt.le hmono
    exact_mod_cast this
  set V : ℝ := ((Nat.nthRoot 10 n + 3 : ℕ) : ℝ) with hV
  have hV0 : (0 : ℝ) ≤ V := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hstep : (n : ℝ) ^ ((9 : ℝ) / 10) ≤ (V ^ (10 : ℕ)) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow hn0 hnle (by norm_num)
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_natCast V 10, ← Real.rpow_mul hV0, ← Real.rpow_natCast V 9]
  norm_num

/-- The binary height dominates the base-two logarithm. -/
theorem log_div_log_two_le_binaryHeight {t : ℝ} (ht : 1 ≤ t) :
    Real.log t / Real.log 2 ≤ (routeTBinaryHeight t : ℝ) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hceil : t ≤ ((⌈t⌉₊ : ℕ) : ℝ) := Nat.le_ceil t
  have hclog : (⌈t⌉₊ : ℕ) ≤ 2 ^ Nat.clog 2 ⌈t⌉₊ := Nat.le_pow_clog (by norm_num) _
  have hcast : ((⌈t⌉₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 ⌈t⌉₊) := by exact_mod_cast hclog
  have hle : t ≤ (2 : ℝ) ^ (Nat.clog 2 ⌈t⌉₊) := le_trans hceil hcast
  have hlog := Real.log_le_log (by linarith) hle
  rw [Real.log_pow] at hlog
  rw [routeTBinaryHeight, div_le_iff₀ hlog2]
  linarith [hlog]

/-- **The Route-T strip width at the band shell, from above.** -/
theorem routeTStripWidth_bandShell_le {t : ℝ} (ht : 2 ≤ t) :
    routeTStripWidth (routeTBandShell t)
      ≤ 1 / ((routeTStripDenominator : ℝ) * (Real.log t / Real.log 2) ^ ((9 : ℝ) / 10)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden : (0 : ℝ) < (routeTStripDenominator : ℝ) := by
    have : 0 < routeTStripDenominator := routeTStripDenominator_pos
    exact_mod_cast this
  set n : ℕ := routeTBinaryHeight t with hn
  have hVeq : routeTBandShell t = Nat.nthRoot 10 n + 2 := rfl
  have hpow := rpow_nine_tenths_le_bandShell_pow n
  have hlogle : Real.log t / Real.log 2 ≤ (n : ℝ) :=
    log_div_log_two_le_binaryHeight (by linarith)
  have hlogtpos : (0 : ℝ) < Real.log t := by
    have h2 : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    linarith
  have hlogpos : (0 : ℝ) < Real.log t / Real.log 2 := by positivity
  have hmono : (Real.log t / Real.log 2) ^ ((9 : ℝ) / 10) ≤ (n : ℝ) ^ ((9 : ℝ) / 10) :=
    Real.rpow_le_rpow hlogpos.le hlogle (by norm_num)
  have hshell : (Real.log t / Real.log 2) ^ ((9 : ℝ) / 10)
      ≤ ((routeTBandShell t : ℝ) + 1) ^ (9 : ℕ) := by
    have hcast : ((routeTBandShell t : ℝ) + 1) = ((Nat.nthRoot 10 n + 3 : ℕ) : ℝ) := by
      rw [hVeq]; push_cast; ring
    rw [hcast]
    exact le_trans hmono hpow
  have hprod : (routeTStripDenominator : ℝ) * (Real.log t / Real.log 2) ^ ((9 : ℝ) / 10)
      ≤ ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hshell hden.le
  have hstrip : routeTStripWidth (routeTBandShell t)
      = 1 / ((routeTStripDenominator * (routeTBandShell t + 1) ^ 9 : ℕ) : ℝ) := rfl
  rw [hstrip]
  refine one_div_le_one_div_of_le ?_ hprod
  have hrp : (0 : ℝ) < (Real.log t / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos hlogpos _
  exact mul_pos hden hrp

/-- The absolute constant of the width upper bound. -/
def routeTWidthUpperConst : ℝ := 4 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2

theorem routeTStripDenominator_cast_pos : (0 : ℝ) < (routeTStripDenominator : ℝ) := by
  have : 0 < routeTStripDenominator := routeTStripDenominator_pos
  exact_mod_cast this

theorem routeTWidthUpperConst_pos : 0 < routeTWidthUpperConst := by
  have := routeTStripDenominator_cast_pos
  rw [routeTWidthUpperConst]
  positivity

/-- **The Landau radius, from above.** -/
theorem routeTLandauRadius_le {γ : ℝ} (hγ : 2 ≤ γ) :
    routeTLandauRadius γ
      ≤ 1 / (2 * (routeTStripDenominator : ℝ)
            * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden := routeTStripDenominator_cast_pos
  have hγ4 : (2 : ℝ) ≤ 4 * γ := by linarith
  have hbase := routeTStripWidth_bandShell_le hγ4
  have hlogγ : (0 : ℝ) < Real.log γ := Real.log_pos (by linarith)
  have hmono : (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10)
      ≤ (Real.log (4 * γ) / Real.log 2) ^ ((9 : ℝ) / 10) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have : Real.log γ ≤ Real.log (4 * γ) := Real.log_le_log (by linarith) (by linarith)
    exact div_le_div_of_nonneg_right this hlog2.le
  have hp1 : (0 : ℝ) < (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hstep : 1 / ((routeTStripDenominator : ℝ) * (Real.log (4 * γ) / Real.log 2) ^ ((9 : ℝ) / 10))
      ≤ 1 / ((routeTStripDenominator : ℝ) * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hmono hden.le
  have hR : routeTLandauRadius γ = routeTStripWidth (routeTBandShell (4 * γ)) / 2 := rfl
  rw [hR]
  have hhalf : routeTStripWidth (routeTBandShell (4 * γ)) / 2
      ≤ (1 / ((routeTStripDenominator : ℝ)
            * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10))) / 2 := by
    have := le_trans hbase hstep
    linarith
  refine hhalf.trans (le_of_eq ?_)
  field_simp

/-- **The Route-T zero-free width, from above.** -/
theorem routeTZeroFreeWidth_le_polylog {A γ : ℝ} (hγ : 2 ≤ γ) :
    routeTZeroFreeWidth A γ
      ≤ 1 / (2 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2
            * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogγ : (0 : ℝ) < Real.log γ := Real.log_pos (by linarith)
  have hden := routeTStripDenominator_cast_pos
  have hp1 : (0 : ℝ) < (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hB := routeTZeroFreeBudget_ge A γ
  have hB0 : (0 : ℝ) < routeTZeroFreeBudget A γ := by linarith
  have hBsq : (10001 : ℝ) ^ 2 ≤ routeTZeroFreeBudget A γ ^ 2 := by nlinarith [hB, hB0]
  have hRpos : (0 : ℝ) < routeTLandauRadius γ := routeTLandauRadius_pos γ
  have hRle := routeTLandauRadius_le hγ
  have hdef : routeTZeroFreeWidth A γ
      = routeTLandauRadius γ / (10000 * routeTZeroFreeBudget A γ ^ 2) / 10 := rfl
  rw [hdef]
  have hstep1 : routeTLandauRadius γ / (10000 * routeTZeroFreeBudget A γ ^ 2) / 10
      ≤ routeTLandauRadius γ / (10000 * (10001 : ℝ) ^ 2) / 10 := by
    have hd1 : (0 : ℝ) < 10000 * (10001 : ℝ) ^ 2 := by norm_num
    have hd2 : (10000 : ℝ) * (10001 : ℝ) ^ 2 ≤ 10000 * routeTZeroFreeBudget A γ ^ 2 := by
      nlinarith [hBsq]
    have := div_le_div_of_nonneg_left hRpos.le hd1 hd2
    linarith
  refine hstep1.trans ?_
  have hstep2 : routeTLandauRadius γ / (10000 * (10001 : ℝ) ^ 2) / 10
      ≤ (1 / (2 * (routeTStripDenominator : ℝ)
            * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10))) / (10000 * (10001 : ℝ) ^ 2) / 10 := by
    have hd : (0 : ℝ) < 10000 * (10001 : ℝ) ^ 2 := by norm_num
    have h1 : routeTLandauRadius γ / (10000 * (10001 : ℝ) ^ 2)
        ≤ (1 / (2 * (routeTStripDenominator : ℝ)
              * (Real.log γ / Real.log 2) ^ ((9 : ℝ) / 10))) / (10000 * (10001 : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hRle hd.le
    linarith
  refine hstep2.trans (le_of_eq ?_)
  field_simp
  ring

/-- **The Route-T uniform regularity width, from above.**  This is the bound the Perron truncation
term of `routeTTwistEnvelope` needs. -/
theorem routeTUniformRegWidth_le_polylog {A delta τ : ℝ} (hτ : 2 ≤ |τ|) :
    routeTUniformRegWidth A delta (3 * |τ| / 2)
      ≤ 1 / (routeTWidthUpperConst * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hden := routeTStripDenominator_cast_pos
  have hK : (2 : ℝ) ≤ 3 * |τ| / 2 + 1 := by linarith
  have hlogτ : (0 : ℝ) < Real.log |τ| := Real.log_pos (by linarith)
  have hp1 : (0 : ℝ) < (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hbase := routeTZeroFreeWidth_le_polylog (A := A) hK
  have hmono : (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10)
      ≤ (Real.log (3 * |τ| / 2 + 1) / Real.log 2) ^ ((9 : ℝ) / 10) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by norm_num)
    have : Real.log |τ| ≤ Real.log (3 * |τ| / 2 + 1) :=
      Real.log_le_log (by linarith) (by linarith)
    exact div_le_div_of_nonneg_right this hlog2.le
  have hswap : 1 / (2 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2
        * (Real.log (3 * |τ| / 2 + 1) / Real.log 2) ^ ((9 : ℝ) / 10))
      ≤ 1 / (2 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2
        * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10)) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hc : (0 : ℝ) ≤ 2 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left hmono hc
  have hmin : routeTUniformRegWidth A delta (3 * |τ| / 2)
      ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) / 2 := by
    rw [routeTUniformRegWidth]
    have : min delta (routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
        ≤ routeTZeroFreeWidth A (3 * |τ| / 2 + 1) := min_le_right _ _
    linarith
  refine hmin.trans ?_
  have hchain := le_trans hbase hswap
  have hhalf : routeTZeroFreeWidth A (3 * |τ| / 2 + 1) / 2
      ≤ (1 / (2 * (routeTStripDenominator : ℝ) * 100000 * 10001 ^ 2
            * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10))) / 2 := by linarith
  refine hhalf.trans (le_of_eq ?_)
  rw [routeTWidthUpperConst]
  field_simp
  ring

/-! ## The envelope with both regimes made explicit -/

/-- **The Route-T twisted envelope between a lower and an upper bound for the width.**  The contour
regime improves as the width grows and the truncation regime worsens, so the envelope needs the
width from both sides. -/
theorem routeTTwistEnvelope_le_two_sided {A delta C τ x L U : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hL : L ≤ routeTUniformRegWidth A delta (3 * |τ| / 2))
    (hU : routeTUniformRegWidth A delta (3 * |τ| / 2) ≤ U) :
    routeTTwistEnvelope A delta C τ x
      ≤ C * ((3 * x) ^ (1 - L / 3) * (routeTTwistHeightFactor A τ + Real.log (2 * x))
            + (3 * x) ^ (1 + 2 * U / 3)
                * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|))
        + 2 * Real.sqrt x * Real.log x := by
  set w : ℝ := routeTUniformRegWidth A delta (3 * |τ| / 2) with hw
  have h3x : (1 : ℝ) ≤ 3 * x := by linarith
  have hHF : (0 : ℝ) ≤ routeTTwistHeightFactor A τ := routeTTwistHeightFactor_nonneg A τ
  have hlog2x : (0 : ℝ) ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hfac1 : (0 : ℝ) ≤ routeTTwistHeightFactor A τ + Real.log (2 * x) := by linarith
  have hfac2 : (0 : ℝ) ≤ 1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ := by positivity
  have hτ0 : (0 : ℝ) < 1 + |τ| := by have := abs_nonneg τ; linarith
  have hterm1 : (3 * x) ^ (1 - w / 3) * (routeTTwistHeightFactor A τ + Real.log (2 * x))
      ≤ (3 * x) ^ (1 - L / 3) * (routeTTwistHeightFactor A τ + Real.log (2 * x)) := by
    refine mul_le_mul_of_nonneg_right ?_ hfac1
    exact Real.rpow_le_rpow_of_exponent_le h3x (by linarith)
  have hterm2 : (3 * x) ^ (1 + 2 * w / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|)
      ≤ (3 * x) ^ (1 + 2 * U / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|) := by
    refine div_le_div_of_nonneg_right ?_ hτ0.le
    refine mul_le_mul_of_nonneg_right ?_ hfac2
    exact Real.rpow_le_rpow_of_exponent_le h3x (by linarith)
  rw [routeTTwistEnvelope, ← hw]
  have hsum : (3 * x) ^ (1 - w / 3) * (routeTTwistHeightFactor A τ + Real.log (2 * x))
        + (3 * x) ^ (1 + 2 * w / 3)
            * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|)
      ≤ (3 * x) ^ (1 - L / 3) * (routeTTwistHeightFactor A τ + Real.log (2 * x))
        + (3 * x) ^ (1 + 2 * U / 3)
            * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|) := by
    linarith
  have := mul_le_mul_of_nonneg_left hsum hC
  linarith

/-- **The Route-T twisted envelope with both regimes polylogarithmic.**  The contour exponent uses
the corpus's lower bound for the width and the truncation exponent the upper bound of this file. -/
theorem routeTTwistEnvelope_le_polylog {A delta C τ x : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hτ : 16 * Real.pi / 3 ≤ |τ|) :
    routeTTwistEnvelope A delta C τ x
      ≤ C * ((3 * x) ^ (1 - min delta (routeTWidthPolylogLower A τ) / 2 / 3)
              * (routeTTwistHeightFactor A τ + Real.log (2 * x))
            + (3 * x) ^ (1 + 2 * (1 / (routeTWidthUpperConst
                  * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
                * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ) / (1 + |τ|))
        + 2 * Real.sqrt x * Real.log x := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hτ2 : (2 : ℝ) ≤ |τ| := by linarith
  exact routeTTwistEnvelope_le_two_sided hC hx
    (routeTUniformRegWidth_ge (A := A) (delta := delta) hτ)
    (routeTUniformRegWidth_le_polylog (A := A) (delta := delta) hτ2)

end

end RHTower.Sieve
