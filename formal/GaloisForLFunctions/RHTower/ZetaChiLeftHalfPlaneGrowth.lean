import GaloisForLFunctions.RHTower.ZetaChiCriticalModulus
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# Growth of the functional-equation factor on left half-planes

For `χ(z) = Γ_ℝ(1 − z)/Γ_ℝ(z)`: the recursion `χ(z − 2) = χ(z)(1 − z)(z − 2)/(4π²)` gives, from
`|χ(1/2 + iy)| = 1`, the sharp bound `|χ(1/2 − 2j + iy)| ≤ (|y| + 2j + 2)^{2j}` on the lines
`Re z = 1/2 − 2j`; and on every strip `1/2 − 2j ≤ Re z ≤ 1/2` a polynomial bound holds, through
`χ(z) = ζ(z)/ζ(1 − z)` and the lower bound `|ζ(s)| ≥ c > 0` on `Re s ≥ 3/2` (from `1/ζ = L(μ, ·)`).
-/

namespace RHTower

open Complex

noncomputable section

/-- **The recursion of the functional-equation factor.** -/
theorem zetaChi_sub_two {z : ℂ} (hz1 : z ≠ 1) (hz2 : z ≠ 2) (hΓ : Gammaℝ z ≠ 0) :
    zetaChi (z - 2) = zetaChi z * ((1 - z) * (z - 2) / (4 * (Real.pi : ℂ) ^ 2)) := by
  have h1z : (1 : ℂ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz1)
  have hz2' : z - 2 ≠ 0 := sub_ne_zero.2 hz2
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hnum : Gammaℝ (1 - (z - 2)) = Gammaℝ (1 - z) * (1 - z) / 2 / Real.pi := by
    rw [show (1 : ℂ) - (z - 2) = (1 - z) + 2 by ring, Gammaℝ_add_two h1z]
  have hden : Gammaℝ z = Gammaℝ (z - 2) * (z - 2) / 2 / Real.pi := by
    rw [← Gammaℝ_add_two hz2', show z - 2 + 2 = z by ring]
  have hΓ2 : Gammaℝ (z - 2) ≠ 0 := by
    intro h; apply hΓ; rw [hden, h]; simp
  unfold zetaChi
  rw [hnum, hden]
  field_simp
  ring

/-- **Sharp growth on the lines `Re z = 1/2 − 2j`.** -/
theorem norm_zetaChi_deep_line_le (j : ℕ) (y : ℝ) :
    ‖zetaChi (((1 / 2 - 2 * j : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ (|y| + 2 * j + 2) ^ (2 * j) := by
  induction j with
  | zero =>
    have := norm_zetaChi_critical y
    simp only [Nat.cast_zero, mul_zero, sub_zero, pow_zero] at this ⊢
    rw [show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring]
    exact this.le
  | succ j ih =>
    set z : ℂ := (((1 / 2 - 2 * j : ℝ) : ℂ) + (y : ℂ) * I) with hz
    have hzre : z.re = 1 / 2 - 2 * j := by simp [hz]
    have hz1 : z ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hz2 : z ≠ 2 := by
      intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      linarith
    have hΓ : Gammaℝ z ≠ 0 := by
      unfold Gammaℝ
      refine mul_ne_zero (by simp [Real.pi_ne_zero]) (Complex.Gamma_ne_zero ?_)
      intro m hm
      have := congrArg Complex.re hm
      simp [hz] at this
      -- `1/4 − j = −m` is impossible
      have h4 : (4 : ℝ) * ((j : ℝ) - m) = 1 := by linarith
      have hint : ((4 * ((j : ℤ) - m) : ℤ) : ℝ) = 1 := by push_cast; linarith
      have : (4 * ((j : ℤ) - m) : ℤ) = 1 := by exact_mod_cast hint
      omega
    have hrec := zetaChi_sub_two hz1 hz2 hΓ
    have hzeq : ((1 / 2 - 2 * ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) + (y : ℂ) * I = z - 2 := by
      rw [hz]; push_cast; ring
    rw [hzeq, hrec, norm_mul]
    have hfac : ‖(1 - z) * (z - 2) / (4 * (Real.pi : ℂ) ^ 2)‖ ≤ (|y| + 2 * j + 2) ^ 2 := by
      rw [norm_div, norm_mul]
      have h1 : ‖(1 : ℂ) - z‖ ≤ |y| + 2 * j + 2 := by
        have : (1 : ℂ) - z = ((1 / 2 + 2 * j : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I := by
          rw [hz]; push_cast; ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2 + 2 * j)]
        linarith
      have h2 : ‖z - 2‖ ≤ |y| + 2 * j + 2 := by
        have : z - 2 = ((-(3 / 2 + 2 * j) : ℝ) : ℂ) + (y : ℂ) * I := by
          rw [hz]; push_cast; ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        rw [Complex.norm_real, Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 3 / 2 + 2 * j)]
        linarith
      have h4 : (1 : ℝ) ≤ ‖4 * (Real.pi : ℂ) ^ 2‖ := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
        norm_num
        nlinarith [Real.pi_gt_three]
      have hnum : ‖(1 : ℂ) - z‖ * ‖z - 2‖ ≤ (|y| + 2 * j + 2) ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      calc ‖(1 : ℂ) - z‖ * ‖z - 2‖ / ‖4 * (Real.pi : ℂ) ^ 2‖
          ≤ ‖(1 : ℂ) - z‖ * ‖z - 2‖ := div_le_self (by positivity) h4
        _ ≤ _ := hnum
    have hmono : (|y| + 2 * j + 2) ^ (2 * j) ≤ (|y| + 2 * ((j + 1 : ℕ) : ℝ) + 2) ^ (2 * j) := by
      gcongr; linarith
    have hmono2 : (|y| + 2 * j + 2) ^ 2 ≤ (|y| + 2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2 := by
      gcongr; linarith
    calc ‖zetaChi z‖ * ‖(1 - z) * (z - 2) / (4 * (Real.pi : ℂ) ^ 2)‖
        ≤ (|y| + 2 * j + 2) ^ (2 * j) * (|y| + 2 * j + 2) ^ 2 :=
          mul_le_mul ih hfac (norm_nonneg _) (by positivity)
      _ ≤ (|y| + 2 * ((j + 1 : ℕ) : ℝ) + 2) ^ (2 * j) *
            (|y| + 2 * ((j + 1 : ℕ) : ℝ) + 2) ^ 2 :=
          mul_le_mul hmono hmono2 (by positivity) (by positivity)
      _ = (|y| + 2 * ((j + 1 : ℕ) : ℝ) + 2) ^ (2 * (j + 1)) := by ring

/-- **`ζ` is bounded below on `Re s ≥ 3/2`**, through `ζ · L(μ, ·) = 1`. -/
theorem exists_norm_riemannZeta_ge_three_halves :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, 3 / 2 ≤ s.re → c ≤ ‖riemannZeta s‖ := by
  set f : ℕ → ℝ := fun n => if n = 0 then 0 else 1 / (n : ℝ) ^ ((3 : ℝ) / 2) with hf
  have hfsum : Summable f := by
    have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)
    refine h.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · simp only [hf]; split_ifs <;> positivity
    · simp only [hf]; split_ifs with h0
      · subst h0; simp
      · exact le_rfl
  set B : ℝ := ∑' n, f n with hB
  have hB1 : 1 ≤ B := by
    have h1 : f 1 = 1 := by simp [hf]
    rw [← h1]
    exact hfsum.le_tsum 1 (fun n _ => by simp only [hf]; split_ifs <;> positivity)
  refine ⟨1 / B, by positivity, fun s hs => ?_⟩
  have hs1 : 1 < s.re := by linarith
  have hprod := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs1
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs1] at hprod
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => (ArithmeticFunction.moebius n : ℂ)) s n‖ ≤ f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf]
    · rw [LSeries.norm_term_eq, if_neg hn]
      simp only [hf, if_neg hn]
      have hμ : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hpow : (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (n : ℝ) ^ s.re :=
        Real.rpow_le_rpow_of_exponent_le hn1 hs
      calc ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ / (n : ℝ) ^ s.re
          ≤ 1 / (n : ℝ) ^ s.re := div_le_div_of_nonneg_right hμ (by positivity)
        _ ≤ 1 / (n : ℝ) ^ ((3 : ℝ) / 2) := one_div_le_one_div_of_le (by positivity) hpow
  have hL : ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ ≤ B := by
    unfold LSeries
    have hs' := hfsum.of_nonneg_of_le (fun n => norm_nonneg _) hterm
    exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hterm hfsum)
  have hne : LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact zero_ne_one hprod
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_one] at hnorm
  have hLpos : 0 < ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ := norm_pos_iff.2 hne
  rw [div_le_iff₀ (by linarith)]
  calc 1 = ‖riemannZeta s‖ * ‖LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) s‖ := hnorm.symm
    _ ≤ ‖riemannZeta s‖ * B := mul_le_mul_of_nonneg_left hL (norm_nonneg _)

/-- **Polynomial growth on the strip `1/2 − 2j ≤ Re z ≤ 1/2`.** -/
theorem exists_norm_zetaChi_strip_le (j : ℕ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, 1 / 2 - 2 * j ≤ σ → σ ≤ 1 / 2 → 2 ≤ |t| →
      ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨Cz, Nz, hCz, hz⟩ := exists_bound_norm_riemannZeta_strip (1 / 2 + 2 * j)
  obtain ⟨c, hc, hlow⟩ := exists_norm_riemannZeta_ge_three_halves
  refine ⟨max (Real.exp 2) (Cz / c), max 1 Nz, by positivity, ?_⟩
  intro σ t hσ1 hσ2 ht
  have ht1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hpowN : (1 + |t|) ^ 1 ≤ (1 + |t|) ^ (max 1 Nz) := pow_le_pow_right₀ ht1 (le_max_left _ _)
  have hpowNz : (1 + |t|) ^ Nz ≤ (1 + |t|) ^ (max 1 Nz) := pow_le_pow_right₀ ht1 (le_max_right _ _)
  rcases le_or_gt (-1 / 2) σ with hσ | hσ
  · -- the corpus half strip
    have := norm_zetaChi_le_half_strip hσ hσ2 ht
    calc ‖zetaChi ((σ : ℂ) + (t : ℂ) * I)‖ ≤ Real.exp 2 * (1 + |t|) := this
      _ ≤ max (Real.exp 2) (Cz / c) * (1 + |t|) ^ (max 1 Nz) := by
          rw [pow_one] at hpowN
          exact mul_le_mul (le_max_left _ _) hpowN (by positivity) (by positivity)
  · -- `χ = ζ(z)/ζ(1 − z)` with `Re(1 − z) ≥ 3/2`
    set z : ℂ := (σ : ℂ) + (t : ℂ) * I with hzdef
    have hzre : z.re = σ := by simp [hzdef]
    have hzim : z.im = t := by simp [hzdef]
    have hz0 : z ≠ 0 := by intro h; rw [h] at hzim; simp at hzim; rw [← hzim] at ht; norm_num at ht
    have hz1 : z ≠ 1 := by
      intro h; have := congrArg Complex.re h; rw [hzre] at this; simp at this; linarith
    have hG : Gammaℝ (1 - z) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hzre]; linarith)
    have hfe := zeta_eq_zetaChi_mul hz0 hz1 hG
    have h1z : 3 / 2 ≤ (1 - z).re := by simp [hzre]; linarith
    have hlow' := hlow (1 - z) h1z
    have hζ := hz σ t (by rw [abs_le]; constructor <;> linarith) (by linarith)
    have hchi : ‖zetaChi z‖ = ‖riemannZeta z‖ / ‖riemannZeta (1 - z)‖ := by
      rw [hfe, norm_mul, mul_div_assoc, div_self (by linarith : ‖riemannZeta (1 - z)‖ ≠ 0),
        mul_one]
    rw [hchi]
    have htt : |t| ^ Nz ≤ (1 + |t|) ^ Nz := pow_le_pow_left₀ (abs_nonneg t) (by linarith) Nz
    calc ‖riemannZeta z‖ / ‖riemannZeta (1 - z)‖ ≤ (Cz * |t| ^ Nz) / c :=
          div_le_div₀ (by positivity) hζ hc hlow'
      _ ≤ (Cz / c) * (1 + |t|) ^ Nz := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left htt hCz) hc.le
      _ ≤ max (Real.exp 2) (Cz / c) * (1 + |t|) ^ (max 1 Nz) :=
          mul_le_mul (le_max_right _ _) hpowNz (by positivity) (by positivity)

end

end RHTower
