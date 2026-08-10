import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DepthDilation
import GaloisForLFunctions.HTGeometry.EulerQGammaGlobalLaw

/-!
# The depth ladder of mode means telescopes

A geometric mode with ratio `r` has mean `r/(1−r)`.  At a prime `p` the depth-`j` mode of the gas
at temperature `σ` has ratio `q^{j+1}` with `q = p^{−σ}`, and the socle tilt `τ ↦ τ + σ` shifts the
depth by one.  The difference of the two ladders of mode means is therefore the single depth-one
term `q/(1−q) = ∑_{a≥1} qᵃ`, which is the local von Mangoldt factor `∑_{a≥1} p^{−aσ}`.

This is the mechanism behind (GAS.12): the symmetrised information cost of the canonical unit tilt
is the depth-one residue of the mode-mean ladder, prime by prime.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The mean of the depth-`j` geometric mode with base ratio `q`. -/
def modeMean (q : ℝ) (j : ℕ) : ℝ := q ^ (j + 1) / (1 - q ^ (j + 1))

theorem one_sub_pow_pos {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    0 < 1 - q ^ (j + 1) := by
  have h : q ^ (j + 1) < 1 := pow_lt_one₀ hq0 hq1 (Nat.succ_ne_zero j)
  linarith

theorem modeMean_nonneg {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) : 0 ≤ modeMean q j := by
  rw [modeMean]
  exact div_nonneg (pow_nonneg hq0 _) (one_sub_pow_pos hq0 hq1 j).le

theorem modeMean_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    modeMean q j ≤ q ^ (j + 1) / (1 - q) := by
  rw [modeMean]
  have hden : 0 < 1 - q := by linarith
  have hmono : 1 - q ≤ 1 - q ^ (j + 1) := by
    have : q ^ (j + 1) ≤ q := by
      calc q ^ (j + 1) = q ^ j * q := pow_succ q j
        _ ≤ 1 * q := by
            refine mul_le_mul_of_nonneg_right (pow_le_one₀ hq0 hq1.le) hq0
        _ = q := one_mul q
    linarith
  exact div_le_div_of_nonneg_left (pow_nonneg hq0 _) hden hmono

theorem summable_modeMean {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) : Summable (modeMean q) := by
  have hgeom : Summable fun j : ℕ => q ^ (j + 1) / (1 - q) := by
    refine Summable.div_const ?_ _
    exact (summable_geometric_of_lt_one hq0 hq1).comp_injective (add_left_injective 1)
  exact Summable.of_nonneg_of_le (modeMean_nonneg hq0 hq1) (modeMean_le hq0 hq1) hgeom

/-- **The mode-mean ladder telescopes.**  Shifting the depth by one removes exactly the depth-one
term. -/
theorem tsum_modeMean_sub_shift {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' j : ℕ, modeMean q j) - (∑' j : ℕ, modeMean q (j + 1)) = modeMean q 0 := by
  have hsum := summable_modeMean hq0 hq1
  have hsplit := hsum.tsum_eq_zero_add
  rw [hsplit]
  ring

/-- The depth-one mode mean is the local von Mangoldt factor `∑_{a≥1} qᵃ`. -/
theorem modeMean_zero_eq_tsum {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    modeMean q 0 = ∑' a : ℕ, q ^ (a + 1) := by
  have hgeom : (∑' a : ℕ, q ^ (a + 1)) = q * ∑' a : ℕ, q ^ a := by
    rw [← tsum_mul_left]
    exact tsum_congr fun a => by rw [pow_succ, mul_comm]
  rw [modeMean, hgeom, tsum_geometric_of_lt_one hq0 hq1, pow_one, div_eq_mul_inv]

/-! ## The local von Mangoldt factor -/

theorem eqgQ_pow_succ (σ : EulerSigma) (p : Nat.Primes) (a : ℕ) :
    (eqgQ σ (p : ℕ)) ^ (a + 1) = ((p : ℕ) : ℝ) ^ (-(((a : ℝ) + 1) * σ.val)) := by
  have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [eqgQ, ← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-σ.val)) (a + 1), ← Real.rpow_mul hp]
  congr 1
  push_cast
  ring

/-- **(GAS.12), local form.**  At the prime `p` the difference of the mode-mean ladders of the
untilted and the unit-tilted gas is the local von Mangoldt factor `∑_{a≥1} p^{−aσ}`. -/
theorem tsum_modeMean_sub_shift_prime (σ : EulerSigma) (p : Nat.Primes) :
    (∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) j)
        - (∑' j : ℕ, modeMean (eqgQ σ (p : ℕ)) (j + 1))
      = ∑' a : ℕ, ((p : ℕ) : ℝ) ^ (-(((a : ℝ) + 1) * σ.val)) := by
  have hq0 : (0 : ℝ) ≤ eqgQ σ (p : ℕ) := (eqgQ_pos σ p.2.pos).le
  have hq1 : eqgQ σ (p : ℕ) < 1 := eqgQ_lt_one σ p.2.two_le
  rw [tsum_modeMean_sub_shift hq0 hq1, modeMean_zero_eq_tsum hq0 hq1]
  exact tsum_congr fun a => eqgQ_pow_succ σ p a

end

end GaloisForLFunctions.HTGeometry
