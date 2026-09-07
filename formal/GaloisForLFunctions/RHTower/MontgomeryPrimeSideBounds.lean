import GaloisForLFunctions.RHTower.MontgomeryPrimeSideIdentity

/-!
# Bounds for the remainder blocks of Montgomery's lemma

The three non-prime blocks of `tsum_montgomeryZeroTerm_eq_primeSide` are bounded, for `x ≥ 1`:

* `‖polarRemainder x t‖ ≤ 4x/(1+t²)`;
* `‖xbBlock x t‖ ≤ x^{−1/2} (C + log(|t|+4))` with an explicit constant `C`;
* `‖trivialBlock x t‖ ≤ 16 x^{−2}/(1+|t|)`.

Hence the zero side of Montgomery's lemma is the prime side up to
`O(x/(1+t²) + x^{−1/2} log(|t|+4) + x^{−2}/(1+|t|))`, which is Lemma 1 of
Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh in the normalisation of `montgomeryZeroTerm`.
-/

open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open ArithmeticFunction (vonMangoldt)

namespace RHTower

/-! ## The polar remainder -/

theorem polarRemainder_eq (x t : ℝ) :
    polarRemainder x t = 2 * (x : ℂ) / ((1 - montgomeryPoleUp t) * montgomeryPoleUp (-t)) := by
  unfold polarRemainder
  have h1 := one_sub_montgomeryPoleUp_ne_zero t
  have h2 := montgomeryPoleUp_ne_zero (-t)
  rw [div_sub_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
  simp only [montgomeryPoleUp]
  push_cast
  ring

theorem normSq_one_sub_montgomeryPoleUp (t : ℝ) :
    Complex.normSq (1 - montgomeryPoleUp t) = 1 / 4 + t ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [montgomeryPoleUp, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

theorem normSq_montgomeryPoleUp (t : ℝ) :
    Complex.normSq (montgomeryPoleUp t) = 9 / 4 + t ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [montgomeryPoleUp, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

/-- `‖polarRemainder x t‖ ≤ 4x/(1+t²)` for `x ≥ 0`. -/
theorem norm_polarRemainder_le {x : ℝ} (hx : 0 ≤ x) (t : ℝ) :
    ‖polarRemainder x t‖ ≤ 4 * x / (1 + t ^ 2) := by
  rw [polarRemainder_eq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hx]
  have hn1 : ‖1 - montgomeryPoleUp t‖ = Real.sqrt (1 / 4 + t ^ 2) := by
    rw [Complex.norm_def, normSq_one_sub_montgomeryPoleUp]
  have hn2 : ‖montgomeryPoleUp (-t)‖ = Real.sqrt (9 / 4 + t ^ 2) := by
    rw [Complex.norm_def, normSq_montgomeryPoleUp]; congr 1; ring
  rw [hn1, hn2, ← Real.sqrt_mul (by positivity)]
  have hkey : ((1 + t ^ 2) / 2) ^ 2 ≤ (1 / 4 + t ^ 2) * (9 / 4 + t ^ 2) := by
    nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
  have hsq : (1 + t ^ 2) / 2 ≤ Real.sqrt ((1 / 4 + t ^ 2) * (9 / 4 + t ^ 2)) := by
    rw [Real.le_sqrt (by positivity) (by positivity)]; exact hkey
  have hpos : 0 < Real.sqrt ((1 / 4 + t ^ 2) * (9 / 4 + t ^ 2)) := Real.sqrt_pos.mpr (by positivity)
  rw [div_le_div_iff₀ hpos (by positivity)]
  nlinarith

/-! ## The trivial-zero block -/

theorem norm_ge_half_abs_re_add_abs_im (z : ℂ) : (|z.re| + |z.im|) / 2 ≤ ‖z‖ := by
  have h1 := Complex.abs_re_le_norm z
  have h2 := Complex.abs_im_le_norm z
  linarith

theorem trivialPole_sub_montgomeryPoleUp_re (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleUp t).re = -(2 * (k : ℝ) + 7 / 2) := by
  rw [Complex.sub_re, trivialPole_re, montgomeryPoleUp_re]; ring

theorem trivialPole_sub_montgomeryPoleUp_im (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleUp t).im = -t := by
  simp [trivialPole, montgomeryPoleUp]

theorem trivialPole_sub_montgomeryPoleDown_re (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleDown t).re = -(2 * (k : ℝ) + 3 / 2) := by
  rw [Complex.sub_re, trivialPole_re, montgomeryPoleDown_re]; ring

theorem trivialPole_sub_montgomeryPoleDown_im (k : ℕ) (t : ℝ) :
    (trivialPole k - montgomeryPoleDown t).im = -t := by
  simp [trivialPole, montgomeryPoleDown]

/-- `‖T_k‖ ≤ 4 x^{−2} / (2k + 3/2 + |t|)²` for `x ≥ 1`. -/
theorem norm_montgomeryTrivialTerm_le_height {x : ℝ} (hx : 1 ≤ x) (t : ℝ) (k : ℕ) :
    ‖montgomeryTrivialTerm x t k‖ ≤ 4 * (x ^ 2)⁻¹ / (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 := by
  have hx0 : 0 < x := by linarith
  unfold montgomeryTrivialTerm
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, trivialPole_re]
  have hpow : x ^ (-(2 * ((k : ℝ) + 1))) ≤ (x ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hx0.le]
    apply Real.rpow_le_rpow_of_exponent_le hx
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hA : (2 * (k : ℝ) + 7 / 2 + |t|) / 2 ≤ ‖trivialPole k - montgomeryPoleUp t‖ := by
    have := norm_ge_half_abs_re_add_abs_im (trivialPole k - montgomeryPoleUp t)
    rw [trivialPole_sub_montgomeryPoleUp_re, trivialPole_sub_montgomeryPoleUp_im, abs_neg, abs_neg,
      abs_of_nonneg (by positivity)] at this
    exact this
  have hB : (2 * (k : ℝ) + 3 / 2 + |t|) / 2 ≤ ‖trivialPole k - montgomeryPoleDown t‖ := by
    have := norm_ge_half_abs_re_add_abs_im (trivialPole k - montgomeryPoleDown t)
    rw [trivialPole_sub_montgomeryPoleDown_re, trivialPole_sub_montgomeryPoleDown_im, abs_neg,
      abs_neg, abs_of_nonneg (by positivity)] at this
    exact this
  have hc : 0 < 2 * (k : ℝ) + 3 / 2 + |t| := by linarith [abs_nonneg t, Nat.cast_nonneg (α := ℝ) k]
  have hprod : (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4
      ≤ ‖trivialPole k - montgomeryPoleUp t‖ * ‖trivialPole k - montgomeryPoleDown t‖ := by
    calc (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4
        = ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) * ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) := by ring
      _ ≤ ((2 * (k : ℝ) + 7 / 2 + |t|) / 2) * ((2 * (k : ℝ) + 3 / 2 + |t|) / 2) := by
          gcongr; linarith
      _ ≤ _ := mul_le_mul hA hB (by positivity) (norm_nonneg _)
  have hprodpos : 0 < ‖trivialPole k - montgomeryPoleUp t‖ * ‖trivialPole k - montgomeryPoleDown t‖ :=
    lt_of_lt_of_le (by positivity) hprod
  rw [div_le_div_iff₀ hprodpos (pow_pos hc 2)]
  have hp := Real.rpow_nonneg hx0.le (-(2 * ((k : ℝ) + 1)))
  calc x ^ (-(2 * ((k : ℝ) + 1))) * (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2
      ≤ (x ^ 2)⁻¹ * (2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 := by gcongr
    _ = 4 * (x ^ 2)⁻¹ * ((2 * (k : ℝ) + 3 / 2 + |t|) ^ 2 / 4) := by ring
    _ ≤ 4 * (x ^ 2)⁻¹ * (‖trivialPole k - montgomeryPoleUp t‖
        * ‖trivialPole k - montgomeryPoleDown t‖) := by gcongr

/-- `Σ_{k<M} 1/(2k+c)² ≤ 2/c` for `c ≥ 1`. -/
theorem sum_range_inv_sq_two_mul_add_le {c : ℝ} (hc : 1 ≤ c) (M : ℕ) :
    ∑ k ∈ Finset.range M, 1 / (2 * (k : ℝ) + c) ^ 2 ≤ 2 / c := by
  have hc0 : 0 < c := by linarith
  rcases M with _ | M
  · simp; positivity
  rw [Finset.sum_range_succ']
  have hshift : ∀ j : ℕ, 1 / (2 * ((j + 1 : ℕ) : ℝ) + c) ^ 2 = (1 / 4) * (1 / (c / 2 + j + 1) ^ 2) := by
    intro j; push_cast; field_simp; ring
  simp_rw [hshift]
  rw [← Finset.mul_sum]
  have h := GaloisForLFunctions.HTGeometry.sum_inv_sq_shift_le (a := c / 2) (by positivity) M
  have h0 : 1 / (2 * ((0 : ℕ) : ℝ) + c) ^ 2 = 1 / c ^ 2 := by norm_num
  rw [h0]
  have hc2 : 1 / c ^ 2 ≤ 1 / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]; nlinarith
  have : (1 / 4 : ℝ) * ∑ j ∈ Finset.range M, 1 / (c / 2 + j + 1) ^ 2 ≤ (1 / 4) * (1 / (c / 2)) := by
    gcongr
  rw [show (1 / 4 : ℝ) * (1 / (c / 2)) = 1 / (2 * c) by ring] at this
  have : 1 / (2 * c) ≤ 1 / c := by
    rw [div_le_div_iff₀ (by positivity) hc0]; linarith
  have : (2 : ℝ) / c = 1 / c + 1 / c := by ring
  linarith

theorem summable_inv_sq_two_mul_add {c : ℝ} (hc : 1 ≤ c) :
    Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + c) ^ 2) :=
  summable_of_sum_range_le (fun k => by positivity) (sum_range_inv_sq_two_mul_add_le hc)

/-- `Σ_{k≥0} 1/(2k+c)² ≤ 2/c` for `c ≥ 1`. -/
theorem tsum_inv_sq_two_mul_add_le {c : ℝ} (hc : 1 ≤ c) :
    ∑' k : ℕ, 1 / (2 * (k : ℝ) + c) ^ 2 ≤ 2 / c :=
  (summable_inv_sq_two_mul_add hc).tsum_le_of_sum_range_le (sum_range_inv_sq_two_mul_add_le hc)

/-- `‖Σ_k T_k‖ ≤ 8 x^{−2}/(3/2 + |t|)`. -/
theorem norm_tsum_montgomeryTrivialTerm_le {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ‖∑' k : ℕ, montgomeryTrivialTerm x t k‖ ≤ 8 * (x ^ 2)⁻¹ / (3 / 2 + |t|) := by
  have hs := (summable_montgomeryTrivialTerm hx t).norm
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  have hc : 1 ≤ 3 / 2 + |t| := by linarith [abs_nonneg t]
  have hmaj : Summable (fun k : ℕ => 4 * (x ^ 2)⁻¹ / (2 * (k : ℝ) + (3 / 2 + |t|)) ^ 2) := by
    have := (summable_inv_sq_two_mul_add hc).mul_left (4 * (x ^ 2)⁻¹)
    refine this.congr fun k => ?_
    ring
  calc ∑' k : ℕ, ‖montgomeryTrivialTerm x t k‖
      ≤ ∑' k : ℕ, 4 * (x ^ 2)⁻¹ / (2 * (k : ℝ) + (3 / 2 + |t|)) ^ 2 := by
        refine Summable.tsum_le_tsum (fun k => ?_) hs hmaj
        have := norm_montgomeryTrivialTerm_le_height hx.le t k
        rwa [show 2 * (k : ℝ) + 3 / 2 + |t| = 2 * (k : ℝ) + (3 / 2 + |t|) by ring] at this
    _ = 4 * (x ^ 2)⁻¹ * ∑' k : ℕ, 1 / (2 * (k : ℝ) + (3 / 2 + |t|)) ^ 2 := by
        rw [← tsum_mul_left]
        refine tsum_congr fun k => ?_
        ring
    _ ≤ 4 * (x ^ 2)⁻¹ * (2 / (3 / 2 + |t|)) := by
        gcongr
        exact tsum_inv_sq_two_mul_add_le hc
    _ = 8 * (x ^ 2)⁻¹ / (3 / 2 + |t|) := by ring

/-- `‖trivialBlock x t‖ ≤ 16 x^{−2}/(1 + |t|)`. -/
theorem norm_trivialBlock_le {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ‖trivialBlock x t‖ ≤ 16 * (x ^ 2)⁻¹ / (1 + |t|) := by
  unfold trivialBlock
  rw [norm_mul, norm_neg, Complex.norm_ofNat]
  have h := norm_tsum_montgomeryTrivialTerm_le hx t
  have h2 : 8 * (x ^ 2)⁻¹ / (3 / 2 + |t|) ≤ 8 * (x ^ 2)⁻¹ / (1 + |t|) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  calc (2 : ℝ) * ‖∑' k : ℕ, montgomeryTrivialTerm x t k‖
      ≤ 2 * (8 * (x ^ 2)⁻¹ / (1 + |t|)) := by gcongr; exact h.trans h2
    _ = 16 * (x ^ 2)⁻¹ / (1 + |t|) := by ring

/-! ## The `x^b` block -/

/-- `Σ_n Λ(n)/n^{3/2}`. -/
noncomputable def vonMangoldtThreeHalvesMass : ℝ := ∑' n : ℕ, vonMangoldt n / (n : ℝ) ^ ((3 / 2 : ℝ))

theorem vonMangoldt_div_rpow_le (n : ℕ) :
    vonMangoldt n / (n : ℝ) ^ ((3 / 2 : ℝ)) ≤ 4 * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : vonMangoldt n ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := by
    refine (ArithmeticFunction.vonMangoldt_le_log).trans ?_
    have := Real.log_le_rpow_div hn'.le (show (0 : ℝ) < 1 / 4 by norm_num)
    rw [div_eq_mul_inv, show ((1 / 4 : ℝ))⁻¹ = 4 by norm_num] at this
    linarith
  rw [div_le_iff₀ (by positivity)]
  calc vonMangoldt n ≤ 4 * (n : ℝ) ^ ((1 / 4 : ℝ)) := hΛ
    _ = 4 * ((n : ℝ) ^ ((5 / 4 : ℝ)))⁻¹ * (n : ℝ) ^ ((3 / 2 : ℝ)) := by
        rw [← Real.rpow_neg hn'.le, mul_assoc, ← Real.rpow_add hn']; norm_num

theorem summable_vonMangoldt_div_threeHalves :
    Summable (fun n : ℕ => vonMangoldt n / (n : ℝ) ^ ((3 / 2 : ℝ))) :=
  Summable.of_nonneg_of_le (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
    vonMangoldt_div_rpow_le
    ((Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4)).mul_left 4)

theorem vonMangoldtThreeHalvesMass_nonneg : 0 ≤ vonMangoldtThreeHalvesMass :=
  tsum_nonneg fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)

/-- `‖L(Λ, s)‖ ≤ Σ Λ(n)/n^{3/2}` for `Re s ≥ 3/2`. -/
theorem norm_LSeries_vonMangoldt_le_of_re {s : ℂ} (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) s‖ ≤ vonMangoldtThreeHalvesMass := by
  rw [LSeries]
  have hterm : ∀ n : ℕ, ‖LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) s n‖
      ≤ vonMangoldt n / (n : ℝ) ^ ((3 / 2 : ℝ)) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with h0
    · subst h0; simp
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      gcongr
  have hsum : Summable (fun n => ‖LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) s n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm summable_vonMangoldt_div_threeHalves
  refine (norm_tsum_le_tsum_norm hsum).trans ?_
  exact Summable.tsum_le_tsum hterm hsum summable_vonMangoldt_div_threeHalves

/-- `‖ψ(z)‖ ≤ log(‖z‖ + 3) + C + 2` for `Re z ≥ 1/2`. -/
theorem norm_digamma_le_of_half_le_re {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    ‖Complex.digamma z‖ ≤ Real.log (‖z‖ + 3) + digammaLineOneConstant + 2 := by
  have hz1 : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
  have hrec := Complex.digamma_apply_add_one z hz1
  have hψ : Complex.digamma z = Complex.digamma (z + 1) - z⁻¹ := by rw [hrec]; ring
  have hz1re : 1 ≤ (z + 1).re := by simp; linarith
  have h1 := norm_digamma_le_of_one_le_re hz1re
  have hnz : 1 / 2 ≤ ‖z‖ := (Complex.re_le_norm z).trans' hz
  have hinv : ‖z⁻¹‖ ≤ 2 := by
    rw [norm_inv, inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hlog : Real.log (‖z + 1‖ + 2) ≤ Real.log (‖z‖ + 3) := by
    apply Real.log_le_log (by positivity)
    have := norm_add_le z 1; rw [norm_one] at this; linarith
  rw [hψ]
  calc ‖Complex.digamma (z + 1) - z⁻¹‖ ≤ ‖Complex.digamma (z + 1)‖ + ‖z⁻¹‖ := norm_sub_le _ _
    _ ≤ (Real.log (‖z‖ + 3) + digammaLineOneConstant) + 2 := by
        gcongr
        exact h1.trans (by linarith)
    _ = Real.log (‖z‖ + 3) + digammaLineOneConstant + 2 := by ring

/-- The constant in the bound for the `x^b` block. -/
noncomputable def xbBlockConstant : ℝ :=
  vonMangoldtThreeHalvesMass + digammaLineOneConstant + 2 + Real.log Real.pi + 2

theorem norm_half_le (t : ℝ) : ‖montgomeryPoleUp (-t) / 2‖ ≤ 3 / 4 + |t| / 2 := by
  rw [norm_div, Complex.norm_ofNat]
  have := Complex.norm_le_abs_re_add_abs_im (montgomeryPoleUp (-t))
  rw [montgomeryPoleUp_re] at this
  have him : (montgomeryPoleUp (-t)).im = -t := by simp [montgomeryPoleUp]
  rw [him, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this
  linarith

theorem norm_down_half_add_one_le (t : ℝ) :
    ‖montgomeryPoleDown t / 2 + 1‖ ≤ 3 / 4 + |t| / 2 := by
  have := Complex.norm_le_abs_re_add_abs_im (montgomeryPoleDown t / 2 + 1)
  have hre : (montgomeryPoleDown t / 2 + 1).re = 3 / 4 := by
    simp [montgomeryPoleDown]; norm_num
  have him : (montgomeryPoleDown t / 2 + 1).im = t / 2 := by
    simp [montgomeryPoleDown]
  rw [hre, him, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4), abs_div, abs_two] at this
  linarith

/-- `‖xbBlock x t‖ ≤ x^{−1/2} (C + log(|t| + 4))` for `x ≥ 1`. -/
theorem norm_xbBlock_le {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ‖xbBlock x t‖ ≤ x ^ (-(1 / 2 : ℝ)) * (xbBlockConstant + Real.log (|t| + 4)) := by
  have hx0 : 0 < x := by linarith
  unfold xbBlock
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, montgomeryPoleDown_re]
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by norm_num]
  gcongr
  have hL := norm_LSeries_vonMangoldt_le_of_re (s := montgomeryPoleUp (-t))
    (by rw [montgomeryPoleUp_re])
  have hψ1 := norm_digamma_le_of_half_le_re (z := montgomeryPoleUp (-t) / 2)
    (by simp [montgomeryPoleUp]; norm_num)
  have hψ2 := norm_digamma_le_of_half_le_re (z := montgomeryPoleDown t / 2 + 1)
    (by simp [montgomeryPoleDown]; norm_num)
  have hlog1 : Real.log (‖montgomeryPoleUp (-t) / 2‖ + 3) ≤ Real.log (|t| + 4) := by
    apply Real.log_le_log (by positivity)
    have := norm_half_le t; linarith [abs_nonneg t]
  have hlog2 : Real.log (‖montgomeryPoleDown t / 2 + 1‖ + 3) ≤ Real.log (|t| + 4) := by
    apply Real.log_le_log (by positivity)
    have := norm_down_half_add_one_le t; linarith [abs_nonneg t]
  have hinv : ‖1 / (montgomeryPoleUp (-t) - 1)‖ ≤ 2 := by
    rw [norm_div, norm_one]
    have hre : (montgomeryPoleUp (-t) - 1).re = 1 / 2 := by
      rw [Complex.sub_re, montgomeryPoleUp_re]; norm_num
    have : 1 / 2 ≤ ‖montgomeryPoleUp (-t) - 1‖ := by
      have := Complex.re_le_norm (montgomeryPoleUp (-t) - 1); rw [hre] at this; exact this
    rw [div_le_iff₀ (by linarith)]; linarith
  have hπ : ‖(Real.log Real.pi : ℂ)‖ = Real.log Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
  calc ‖LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (montgomeryPoleUp (-t))
        - Complex.digamma (montgomeryPoleUp (-t) / 2) / 2
        - Complex.digamma (montgomeryPoleDown t / 2 + 1) / 2
        + (Real.log Real.pi : ℂ) - 1 / (montgomeryPoleUp (-t) - 1)‖
      ≤ ‖LSeries (fun n => ((vonMangoldt n : ℝ) : ℂ)) (montgomeryPoleUp (-t))‖
        + ‖Complex.digamma (montgomeryPoleUp (-t) / 2) / 2‖
        + ‖Complex.digamma (montgomeryPoleDown t / 2 + 1) / 2‖
        + ‖(Real.log Real.pi : ℂ)‖ + ‖1 / (montgomeryPoleUp (-t) - 1)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_sub_le _ _
    _ ≤ vonMangoldtThreeHalvesMass
        + (Real.log (|t| + 4) + digammaLineOneConstant + 2) / 2
        + (Real.log (|t| + 4) + digammaLineOneConstant + 2) / 2
        + Real.log Real.pi + 2 := by
        rw [hπ]
        have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        have hψ1' : ‖Complex.digamma (montgomeryPoleUp (-t) / 2) / 2‖
            ≤ (Real.log (|t| + 4) + digammaLineOneConstant + 2) / 2 := by
          rw [norm_div, h2]; linarith [hψ1, hlog1]
        have hψ2' : ‖Complex.digamma (montgomeryPoleDown t / 2 + 1) / 2‖
            ≤ (Real.log (|t| + 4) + digammaLineOneConstant + 2) / 2 := by
          rw [norm_div, h2]; linarith [hψ2, hlog2]
        gcongr
    _ = xbBlockConstant + Real.log (|t| + 4) := by
        unfold xbBlockConstant; ring

/-! ## The combined remainder -/

/-- The remainder `E = polarRemainder + xbBlock + trivialBlock`. -/
noncomputable def montgomeryRemainder (x t : ℝ) : ℂ :=
  polarRemainder x t + xbBlock x t + trivialBlock x t

/-- **BGSTB Lemma 1.** `Σ_ρ 2x^ρ/((ρ−a)(ρ−b)) = primeSide + E` with
`‖E‖ ≤ 4x/(1+t²) + x^{−1/2}(C + log(|t|+4)) + 16x^{−2}/(1+|t|)`. -/
theorem tsum_montgomeryZeroTerm_eq_primeSide_add_remainder {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ∑' q : XiZeroCopy, montgomeryZeroTerm x t q = primeSide x t + montgomeryRemainder x t := by
  rw [tsum_montgomeryZeroTerm_eq_primeSide hx t, montgomeryRemainder]; ring

theorem norm_montgomeryRemainder_le {x : ℝ} (hx : 1 < x) (t : ℝ) :
    ‖montgomeryRemainder x t‖ ≤ 4 * x / (1 + t ^ 2)
      + x ^ (-(1 / 2 : ℝ)) * (xbBlockConstant + Real.log (|t| + 4))
      + 16 * (x ^ 2)⁻¹ / (1 + |t|) := by
  unfold montgomeryRemainder
  have h1 := norm_polarRemainder_le (by linarith : (0 : ℝ) ≤ x) t
  have h2 := norm_xbBlock_le hx.le t
  have h3 := norm_trivialBlock_le hx t
  calc ‖polarRemainder x t + xbBlock x t + trivialBlock x t‖
      ≤ ‖polarRemainder x t‖ + ‖xbBlock x t‖ + ‖trivialBlock x t‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

end RHTower
