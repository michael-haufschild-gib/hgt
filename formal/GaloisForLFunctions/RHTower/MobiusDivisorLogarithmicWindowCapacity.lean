import GaloisForLFunctions.RHTower.MobiusDivisorCoupledTwoPrimeBatches

/-!
# PNT-scale capacity of the coupled two-plane reserve

The three literal reserve windows used by the two-plane repair are not merely
unbounded or square-root sized.  Quantitative prime-window density gives a
common logarithmic-scale lower bound for their minimum cardinality.  This
is the source capacity available to a changing-core construction: it is
mesoscopic, but it is still finite and does not by itself complete a prime
order.
-/

noncomputable section
open Finset Filter Topology

namespace RHTower

private theorem coupled_window_pnt_lower
    (b a : ℕ) (hb : 1 ≤ b) (ha : 1 ≤ a) :
    ∀ᶠ N : ℕ in atTop,
      (a * N : ℝ) / (2 * Real.log ((b * (a * N) : ℕ) : ℝ)) ≤
        (GaloisForLFunctions.HTGeometry.primesInIoc (b * (a * N))
          ((b + 1) * (a * N))).card := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hratio : (1 : ℝ) < ((b : ℝ) + 1) / b := by
    rw [lt_div_iff₀ hbR]
    linarith
  have haR : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hscaled : Tendsto (fun N : ℕ => ((a * N : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using
      tendsto_natCast_atTop_atTop.const_mul_atTop haR
  have hcast : Tendsto (fun N : ℕ => (b : ℝ) * (a * N)) atTop atTop := by
    simpa only [Nat.cast_mul] using hscaled.const_mul_atTop hbR
  have hcount := hcast.eventually
    (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hratio)
  filter_upwards [hcount, eventually_ge_atTop (2 : ℕ)] with N hcount hN
  have harg : (((b : ℝ) + 1) / b) * ((b : ℝ) * (a * N)) =
      ((b + 1) * (a * N) : ℕ) := by
    push_cast
    field_simp
  have hbN : (b : ℝ) * (a * N) = (b * (a * N) : ℕ) := by
    push_cast
    rfl
  rw [harg, hbN, Nat.floor_natCast, Nat.floor_natCast,
    ← GaloisForLFunctions.HTGeometry.card_primesInIoc
      (show b * (a * N) ≤ (b + 1) * (a * N) by nlinarith)] at hcount
  have hcoef : (((b : ℝ) + 1) / b - 1) / 2 = 1 / (2 * b) := by
    field_simp
    ring
  rw [hcoef] at hcount
  convert hcount using 1 <;> push_cast <;> field_simp

/-- The smallest of the three physical quotient-two/seven/fourteen reserve
windows has PNT-scale cardinality.  This is a literal source-supply bound;
it makes no claim about a bounded completion order. -/
theorem eventually_mobiusDivisorCoupledTwoCapacity_ge_logarithmic
    (b : ℕ) (hb : 1 ≤ b) :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
        (mobiusDivisorCoupledTwoCapacity b N : ℝ) := by
  have h1 := coupled_window_pnt_lower b 1 hb (by omega)
  have h2 := coupled_window_pnt_lower b 2 hb (by omega)
  have h7 := coupled_window_pnt_lower b 7 hb (by omega)
  filter_upwards [h1, h2, h7, eventually_ge_atTop (2 : ℕ)] with N h1 h2 h7 hN
  have hbN : 1 < (b * N : ℕ) := by
    nlinarith [show 1 ≤ b from hb]
  have hbase : 0 < Real.log ((b * N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast hbN)
  have hbig : 0 < Real.log ((14 * b * N : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < 14 * b * N by nlinarith))
  have hlog1 : Real.log ((b * N : ℕ) : ℝ) ≤
      Real.log ((14 * b * N : ℕ) : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show b * N ≤ 14 * b * N by nlinarith)
  have hlog2 : Real.log ((b * (2 * N) : ℕ) : ℝ) ≤
      Real.log ((14 * b * N : ℕ) : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show b * (2 * N) ≤ 14 * b * N by nlinarith)
  have hlog7 : Real.log ((b * (7 * N) : ℕ) : ℝ) ≤
      Real.log ((14 * b * N : ℕ) : ℝ) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast (show b * (7 * N) ≤ 14 * b * N by nlinarith)
  have hwin1 : (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (b * N) ((b + 1) * N)).card := by
    have hden : 2 * Real.log ((b * N : ℕ) : ℝ) ≤
        14 * Real.log ((14 * b * N : ℕ) : ℝ) := by
      nlinarith
    have hfrac := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ N by positivity)
      (by linarith only [hbase] : 0 < 2 * Real.log ((b * N : ℕ) : ℝ)) hden
    exact hfrac.trans (by simpa using h1)
  have hwin2 : (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (b * (2 * N)) ((b + 1) * (2 * N))).card := by
    have hden : 2 * Real.log ((b * (2 * N) : ℕ) : ℝ) ≤
        14 * Real.log ((14 * b * N : ℕ) : ℝ) := by
      nlinarith
    have hsmall : 0 < Real.log ((b * (2 * N) : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < b * (2 * N) by nlinarith))
    have hfrac := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (2 * N : ℕ) by positivity)
      (by linarith only [hsmall] : 0 < 2 * Real.log ((b * (2 * N) : ℕ) : ℝ)) hden
    have hNle : (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
        ((2 * N : ℕ) : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) := by
      apply (div_le_div_iff_of_pos_right (by linarith only [hbig] :
        0 < 14 * Real.log ((14 * b * N : ℕ) : ℝ))).mpr
      exact_mod_cast (show N ≤ 2 * N by omega)
    exact hNle.trans (hfrac.trans (by simpa using h2))
  have hwin7 : (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (b * (7 * N)) ((b + 1) * (7 * N))).card := by
    have hden : 2 * Real.log ((b * (7 * N) : ℕ) : ℝ) ≤
        14 * Real.log ((14 * b * N : ℕ) : ℝ) := by
      nlinarith
    have hsmall : 0 < Real.log ((b * (7 * N) : ℕ) : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < b * (7 * N) by nlinarith))
    have hfrac := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ (7 * N : ℕ) by positivity)
      (by linarith only [hsmall] : 0 < 2 * Real.log ((b * (7 * N) : ℕ) : ℝ)) hden
    have hNle : (N : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) ≤
        ((7 * N : ℕ) : ℝ) / (14 * Real.log ((14 * b * N : ℕ) : ℝ)) := by
      apply (div_le_div_iff_of_pos_right (by linarith only [hbig] :
        0 < 14 * Real.log ((14 * b * N : ℕ) : ℝ))).mpr
      exact_mod_cast (show N ≤ 7 * N by omega)
    exact hNle.trans (hfrac.trans (by simpa using h7))
  simpa only [mobiusDivisorCoupledTwoCapacity, mobiusDivisorCoupledTwoWindow,
    Nat.reduceDiv, one_mul, Nat.cast_min] using le_min hwin7 (le_min hwin2 hwin1)

end RHTower
