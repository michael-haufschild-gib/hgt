import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import GaloisForLFunctions.RHTower.Sieve.InverseSquareTail

/-!
# The Dirichlet tail of the Riemann zeta function

Far to the right of the critical strip the zeta function is `1` up to an exponentially small tail:

`‖ζ(s) - 1‖ ≤ 4 · 2^{-Re s}`   whenever `Re s ≥ 2`.

The Dirichlet series is compared term by term with the telescoping series `∑ 1/(k+2)²`: writing
`(k+2)^{-Re s} = 2^{-Re s}·(2/(k+2))^{Re s}` and using that `u ↦ u^σ` is antitone in `σ` on `(0,1]`
turns the tail into `4 · 2^{-Re s} · ∑ (k+2)^{-2}`, and the latter sum is at most one.
-/

open Complex Filter

namespace GaloisForLFunctions.HTGeometry

/-- Summability of the comparison weights `(k+2)^{-2}`. -/
theorem summable_zetaTailWeight : Summable fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 2) ^ 2 := by
  refine (RHTower.Sieve.summable_inv_sq_shift 1).congr fun n => ?_
  norm_num
  ring

/-- The comparison weights sum to at most one. -/
theorem tsum_zetaTailWeight_le : ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 2) ^ 2 ≤ 1 := by
  have h := RHTower.Sieve.tsum_inv_sq_shift_le (R := 1) le_rfl
  have hcongr : ∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + ((1 : ℕ) : ℝ) + 1) ^ 2
      = ∑' k : ℕ, (1 : ℝ) / ((k : ℝ) + 2) ^ 2 := by
    refine tsum_congr fun n => ?_
    norm_num
    ring
  rw [hcongr] at h
  simpa using h

/-- Each Dirichlet tail term is dominated by the corresponding square term. -/
theorem inv_rpow_shift_le {σ : ℝ} (hσ : 2 ≤ σ) (k : ℕ) :
    (1 : ℝ) / ((k : ℝ) + 2) ^ σ ≤ 4 * (2 : ℝ) ^ (-σ) * ((1 : ℝ) / ((k : ℝ) + 2) ^ 2) := by
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have h2k : (2 : ℝ) ≤ (k : ℝ) + 2 := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  set u : ℝ := 2 / ((k : ℝ) + 2) with hu
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu1 : u ≤ 1 := by
    rw [hu, div_le_one hk]
    exact h2k
  have hmono : u ^ σ ≤ u ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hσ
  have hleft : u ^ σ = (2 : ℝ) ^ σ / ((k : ℝ) + 2) ^ σ := by
    rw [hu, Real.div_rpow (by norm_num) (le_of_lt hk)]
  have hright : u ^ (2 : ℝ) = 4 / ((k : ℝ) + 2) ^ 2 := by
    have hnat : u ^ (2 : ℝ) = u ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hnat, hu, div_pow]
    norm_num
  rw [hleft, hright] at hmono
  have h2σ : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
  have hden : (0 : ℝ) < ((k : ℝ) + 2) ^ σ := Real.rpow_pos_of_pos hk σ
  have hneg : (4 : ℝ) * (2 : ℝ) ^ (-σ) * ((1 : ℝ) / ((k : ℝ) + 2) ^ 2)
      = (4 / ((k : ℝ) + 2) ^ 2) / (2 : ℝ) ^ σ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hself : (1 : ℝ) / ((k : ℝ) + 2) ^ σ
      = ((2 : ℝ) ^ σ / ((k : ℝ) + 2) ^ σ) / (2 : ℝ) ^ σ := by
    field_simp
  rw [hneg, hself]
  exact (div_le_div_iff_of_pos_right h2σ).mpr hmono

/-- Summability of the shifted Dirichlet tail. -/
theorem summable_norm_tail {s : ℂ} (hs : 2 ≤ s.re) :
    Summable fun k : ℕ => ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_)
    ((summable_zetaTailWeight.mul_left (4 * (2 : ℝ) ^ (-s.re))))
  have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hcast : (((k : ℝ) + 2 : ℝ) : ℂ) = (k : ℂ) + 2 := by push_cast; ring
  rw [norm_div, norm_one, ← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hk]
  exact inv_rpow_shift_le hs k

/-- **The zeta tail bound.** -/
theorem norm_riemannZeta_sub_one_le_rpow {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta s - 1‖ ≤ 4 * (2 : ℝ) ^ (-s.re) := by
  have hs1 : 1 < s.re := by linarith
  have hsum0 : Summable fun n : ℕ => (1 : ℂ) / (n : ℂ) ^ s :=
    Complex.summable_one_div_nat_cpow.mpr hs1
  have hsum : Summable fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1) ^ s := by
    have hshift : Summable fun n : ℕ => (1 : ℂ) / ((n + 1 : ℕ) : ℂ) ^ s :=
      (summable_nat_add_iff 1).mpr hsum0
    refine hshift.congr fun n => ?_
    norm_num
  have hsplit : riemannZeta s - 1 = ∑' k : ℕ, (1 : ℂ) / ((k : ℂ) + 2) ^ s := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs1, hsum.tsum_eq_zero_add]
    have hterm : ∀ k : ℕ, (1 : ℂ) / (((k + 1 : ℕ) : ℂ) + 1) ^ s = 1 / ((k : ℂ) + 2) ^ s := by
      intro k
      norm_num
      ring_nf
    rw [tsum_congr hterm]
    simp only [Nat.cast_zero, zero_add, Complex.one_cpow, div_one]
    ring
  rw [hsplit]
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_tail hs)) ?_
  have hbound : ∀ k : ℕ, ‖(1 : ℂ) / ((k : ℂ) + 2) ^ s‖
      ≤ 4 * (2 : ℝ) ^ (-s.re) * ((1 : ℝ) / ((k : ℝ) + 2) ^ 2) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hcast : (((k : ℝ) + 2 : ℝ) : ℂ) = (k : ℂ) + 2 := by push_cast; ring
    rw [norm_div, norm_one, ← hcast, Complex.norm_cpow_eq_rpow_re_of_pos hk]
    exact inv_rpow_shift_le hs k
  refine le_trans (Summable.tsum_mono (summable_norm_tail hs)
    (summable_zetaTailWeight.mul_left _) hbound) ?_
  rw [tsum_mul_left]
  have hc : (0 : ℝ) ≤ 4 * (2 : ℝ) ^ (-s.re) := by positivity
  nlinarith [tsum_zetaTailWeight_le, hc]

end GaloisForLFunctions.HTGeometry
