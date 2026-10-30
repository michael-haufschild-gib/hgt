import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons

/-!
# The horizon charge is blind to the real parts of the zeros

The Möbius horizon `H_a(s) = Σ_{d≤N} a_d d^{-s} B_{⌊N/d⌋}(s)` of an atomic vector splits into its
**horizon charge** `P_a(s) = Σ_{d≤N} a_d d^{-s} N_d^{1-s}/(s-1)·d^{s-1}`, the Euler–Maclaurin pole
parts, and the Euler–Maclaurin tails (`mobiusHorizon_eq_mobiusPole_sub`). Writing
`N_d = d⌊N/d⌋ ≤ N` for the last multiple of `d` in the horizon (`mobiusPole_eq`),

`P_a(s) = (s − 1)⁻¹ Σ_{d≤N} (a_d/d) N_d^{1−s}`.

* **Blindness** (`norm_mobiusPole_mul_le`): on `0 ≤ Re s ≤ 1`,
  `‖P_a(s) P_a(1−s)‖ ≤ N (Σ_d |a_d|/d)² / ‖s(1−s)‖`. The real part `β` of a zero enters only through
  `N_d^{1−β} N_e^{β} ≤ N`: an off-line zero produces no growth `N^{|β−1/2|}` in the charge.
* **The pole charge is a pair of Poisson kernels** (`re_one_div_mul_one_sub_eq`,
  `re_emPole_mul_emPole_one_sub_pos`): for the pole mode the charge product is `N/(ρ(1−ρ))` and
  `Re 1/(ρ(1−ρ)) = β/(β²+γ²) + (1−β)/((1−β)²+γ²) > 0` for every zero in the open strip, on or off
  the critical line.
-/

noncomputable section

open Complex Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- The **horizon charge** `P_a(s) = Σ_{d≤N} a_d d^{-s} emPole ⌊N/d⌋ s`. -/
def mobiusPole (N : ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ) ^ (-s) * RHTower.emPole (N / d) s

/-- The Euler–Maclaurin tail part of the Möbius horizon. -/
def mobiusTail (N : ℕ) (a : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ) ^ (-s) * (s * RHTower.emTail (N / d) s)

theorem mobiusHorizon_eq_mobiusPole_sub (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    mobiusHorizon N a s = mobiusPole N a s - mobiusTail N a s := by
  unfold mobiusHorizon mobiusPole mobiusTail horizonBoundary
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun d _ => ?_
  ring

/-- `d^{-s} M^{1-s} = d⁻¹ (dM)^{1-s}` for `d ≥ 1`. -/
theorem natCast_cpow_neg_mul_cpow_one_sub {d : ℕ} (hd : 1 ≤ d) (M : ℕ) (s : ℂ) :
    (d : ℂ) ^ (-s) * (M : ℂ) ^ (1 - s) = (d : ℂ)⁻¹ * ((d * M : ℕ) : ℂ) ^ (1 - s) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, show (1 : ℂ) - s = 1 + -s by ring,
    cpow_add _ _ hd0, cpow_one]
  field_simp

/-- **The horizon charge** `P_a(s) = (s − 1)⁻¹ Σ_{d≤N} (a_d/d) N_d^{1−s}`, `N_d = d⌊N/d⌋`. -/
theorem mobiusPole_eq (N : ℕ) (a : ℕ → ℝ) (s : ℂ) :
    mobiusPole N a s =
      (∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ)⁻¹ * ((d * (N / d) : ℕ) : ℂ) ^ (1 - s)) / (s - 1) := by
  unfold mobiusPole RHTower.emPole
  rw [sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  rw [mul_div_assoc', mul_assoc (a d : ℂ), natCast_cpow_neg_mul_cpow_one_sub hd1]
  ring

/-- `‖Σ_d (a_d/d) N_d^{1−s}‖ ≤ (Σ_d |a_d|/d) N^{1−Re s}` for `Re s ≤ 1`. -/
theorem norm_sum_charge_le (N : ℕ) (a : ℕ → ℝ) {s : ℂ} (hs : s.re ≤ 1) :
    ‖∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ)⁻¹ * ((d * (N / d) : ℕ) : ℂ) ^ (1 - s)‖ ≤
      (∑ d ∈ Icc 1 N, |a d| / d) * (N : ℝ) ^ (1 - s.re) := by
  rw [sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd => ?_)
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  have hdN : d ≤ N := (mem_Icc.mp hd).2
  have hq : 1 ≤ N / d := (Nat.one_le_div_iff (by omega)).mpr hdN
  have hm : 0 < d * (N / d) := Nat.mul_pos (by omega) (by omega)
  have hmN : ((d * (N / d) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
  rw [norm_mul, norm_mul, Complex.norm_real, norm_inv, Complex.norm_natCast,
    Complex.norm_natCast_cpow_of_pos hm, Complex.sub_re, Complex.one_re, Real.norm_eq_abs]
  have hpow : ((d * (N / d) : ℕ) : ℝ) ^ (1 - s.re) ≤ (N : ℝ) ^ (1 - s.re) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hmN (by linarith)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- **Blindness of the horizon charge.** On the closed strip, the product of the charges at `s` and
`1 − s` is at most `N (Σ_d |a_d|/d)² / ‖s(1−s)‖`, uniformly in the real part of `s`. -/
theorem norm_mobiusPole_mul_le {N : ℕ} (hN1 : 1 ≤ N) (a : ℕ → ℝ) {s : ℂ} (h0 : 0 ≤ s.re)
    (h1 : s.re ≤ 1) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    ‖mobiusPole N a s * mobiusPole N a (1 - s)‖ ≤
      N * (∑ d ∈ Icc 1 N, |a d| / d) ^ 2 / ‖s * (1 - s)‖ := by
  have hA := norm_sum_charge_le N a h1
  have hB := norm_sum_charge_le N a (s := 1 - s) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hsub1 : (1 : ℂ) - s - 1 = -s := by ring
  have hden1 : ‖s - 1‖ = ‖1 - s‖ := by rw [← norm_neg, neg_sub]
  have hn1 : 0 < ‖1 - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hs1))
  have hn0 : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  rw [mobiusPole_eq, mobiusPole_eq, hsub1, norm_mul, norm_div, norm_div, norm_neg, hden1,
    norm_mul]
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hS : 0 ≤ ∑ d ∈ Icc 1 N, |a d| / (d : ℝ) :=
    sum_nonneg fun d _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg d)
  have hpow : (N : ℝ) ^ (1 - s.re) * (N : ℝ) ^ (1 - (1 - s).re) = N := by
    rw [← Real.rpow_add (by exact_mod_cast hN1)]
    simp only [Complex.sub_re, Complex.one_re]
    rw [show (1 - s.re + (1 - (1 - s.re))) = (1 : ℝ) by ring, Real.rpow_one]
  calc ‖∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ)⁻¹ * ((d * (N / d) : ℕ) : ℂ) ^ (1 - s)‖ / ‖1 - s‖ *
        (‖∑ d ∈ Icc 1 N, (a d : ℂ) * (d : ℂ)⁻¹ * ((d * (N / d) : ℕ) : ℂ) ^ (1 - (1 - s))‖ /
          ‖s‖)
      ≤ ((∑ d ∈ Icc 1 N, |a d| / d) * (N : ℝ) ^ (1 - s.re)) / ‖1 - s‖ *
        (((∑ d ∈ Icc 1 N, |a d| / d) * (N : ℝ) ^ (1 - (1 - s).re)) / ‖s‖) := by
        gcongr
    _ = (∑ d ∈ Icc 1 N, |a d| / d) ^ 2 *
          ((N : ℝ) ^ (1 - s.re) * (N : ℝ) ^ (1 - (1 - s).re)) / (‖s‖ * ‖1 - s‖) := by
        field_simp
    _ = N * (∑ d ∈ Icc 1 N, |a d| / d) ^ 2 / (‖s‖ * ‖1 - s‖) := by
        rw [hpow]; ring

/-! ### The pole charge is a pair of Poisson kernels -/

/-- `Re 1/(ρ(1−ρ)) = β/(β²+γ²) + (1−β)/((1−β)²+γ²)`: the Poisson kernels of `ρ` and of its
reflection, at abscissa `1` and height `0`. -/
theorem re_one_div_mul_one_sub_eq (ρ : ℂ) (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (1 / (ρ * (1 - ρ))).re =
      ρ.re / (ρ.re ^ 2 + ρ.im ^ 2) + (1 - ρ.re) / ((1 - ρ.re) ^ 2 + ρ.im ^ 2) := by
  have h1' : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hsplit : 1 / (ρ * (1 - ρ)) = ρ⁻¹ + (1 - ρ)⁻¹ := by field_simp; ring
  rw [hsplit, Complex.add_re, Complex.inv_re, Complex.inv_re, Complex.normSq_apply,
    Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub]
  ring

/-- Every zero in the open strip, on or off the line, carries a positive pole charge. -/
theorem re_one_div_mul_one_sub_pos {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < (1 / (ρ * (1 - ρ))).re := by
  have hne0 : ρ ≠ 0 := fun h => by rw [h, Complex.zero_re] at h0; exact lt_irrefl _ h0
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  rw [re_one_div_mul_one_sub_eq ρ hne0 hne1]
  have ha : 0 < ρ.re ^ 2 + ρ.im ^ 2 := by positivity
  have hb : 0 < (1 - ρ.re) ^ 2 + ρ.im ^ 2 := by
    have : 0 < 1 - ρ.re := by linarith
    positivity
  have := div_pos h0 ha
  have := div_pos (by linarith : (0 : ℝ) < 1 - ρ.re) hb
  linarith

/-- **The pole-mode charge is positive at every nontrivial zero**:
`Re (emPole N ρ · emPole N (1−ρ)) = N · Re 1/(ρ(1−ρ)) > 0`. -/
theorem re_emPole_mul_emPole_one_sub_pos {N : ℕ} (hN : 1 ≤ N) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < (RHTower.emPole N ρ * RHTower.emPole N (1 - ρ)).re := by
  have hne1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at h1; exact lt_irrefl _ h1
  rw [emPole_mul_emPole_one_sub hN hne1, div_eq_mul_one_div, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
  exact mul_pos (by exact_mod_cast hN) (re_one_div_mul_one_sub_pos h0 h1)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
