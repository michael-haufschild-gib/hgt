import GaloisForLFunctions.RHTower.RayleighScalarShift
import Mathlib

/-!
# The countable log-chirp weight is summable, and the leading term is a scalar

Two exact mechanisms of the card are formalized.

*The countable almost-orthogonality weight converges.*  Equation `(8)` of the card is the
convergence of `∑_{k≥1} (1 + log(1+k))/k²`, which is what makes the cross-branch sum uniform in the
truncation.  It is proved here from `log t ≤ 2√t` and the `3/2`-power comparison.

*The leading archimedean term is a scalar identity.*  Equations `(13)`–`(14)` say exactly that
subtracting `log c` times the squared norm turns the archimedean value into the renormalized
remainder; the consumer of that renormalization is `RHTower/RayleighScalarShift.lean`, which proves
that a real scalar identity shift leaves Rayleigh excess, spectral gap and their ratio unchanged.

The semiclassical conjugation `(6)`, Dunster's radial expansions, and the PSWF symbol bounds
`(10)`–`(11)` are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The countable almost-orthogonality weight -/

theorem log_le_two_mul_sqrt {t : ℝ} (ht : 0 < t) : Real.log t ≤ 2 * Real.sqrt t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
    Real.log_le_sub_one_of_pos hs
  have hhalf : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt (le_of_lt ht)
  rw [hhalf] at hlog
  linarith

/-- **Equation (8).**  The countable log-chirp weight is summable, so the cross-branch sums are
uniform in the truncation. -/
theorem summable_logChirp_weight :
    Summable (fun k : ℕ => (1 + Real.log (1 + (k : ℝ))) / (1 + (k : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmul : Summable (fun k : ℕ => 3 * (1 / (((k + 1 : ℕ) : ℝ)) ^ (3 / 2 : ℝ))) :=
    hshift.mul_left 3
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hmul
  · have h1 : (0 : ℝ) < 1 + (k : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ Real.log (1 + (k : ℝ)) := by
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    positivity
  · have hcast : (((k + 1 : ℕ) : ℝ)) = 1 + (k : ℝ) := by push_cast; ring
    have h1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have hpos : (0 : ℝ) < 1 + (k : ℝ) := by linarith
    have hsq : Real.sqrt (1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ)) = 1 + (k : ℝ) :=
      Real.mul_self_sqrt (le_of_lt hpos)
    have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + (k : ℝ)) := by
      have hmono := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_one] at hmono
    have hlog := log_le_two_mul_sqrt hpos
    have hnum : 1 + Real.log (1 + (k : ℝ)) ≤ 3 * Real.sqrt (1 + (k : ℝ)) := by linarith
    have hrpow : ((1 + (k : ℝ))) ^ (3 / 2 : ℝ)
        = (1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ)) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hpos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    have hden : (0 : ℝ) < (1 + (k : ℝ)) * Real.sqrt (1 + (k : ℝ)) := by
      have : (0 : ℝ) < Real.sqrt (1 + (k : ℝ)) := by linarith
      positivity
    rw [hcast, hrpow, mul_one_div, div_le_div_iff₀ (by positivity) hden]
    nlinarith [mul_le_mul_of_nonneg_right hnum (le_of_lt hden), hsq, hs1, hpos]

/-! ## The scalar leading term -/

/-- **Equations (13)–(14).**  The archimedean law is exactly the statement that the renormalized
remainder is the deviation from the scalar identity term. -/
theorem scalar_renormalized_form (A N E c : ℝ) :
    A = Real.log c * N + E ↔ A - Real.log c * N = E := by
  constructor
  · intro h
    rw [h]
    ring
  · intro h
    rw [← h]
    ring

/-- **Equation (10), consumer.**  A diagonal bound `C/k²` is summable. -/
theorem summable_radialDiagonal_bound (C : ℝ) :
    Summable (fun k : ℕ => C / (1 + (k : ℝ)) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ)) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ)) ^ 2) :=
    (summable_nat_add_iff 1).mpr hbase
  have hmul := hshift.mul_left C
  refine hmul.congr fun k => ?_
  have hcast : (((k + 1 : ℕ) : ℝ)) = 1 + (k : ℝ) := by push_cast; ring
  rw [hcast]
  ring

end GaloisForLFunctions.RHTower

end
