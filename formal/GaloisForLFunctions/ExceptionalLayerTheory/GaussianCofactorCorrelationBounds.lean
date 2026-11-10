import GaloisForLFunctions.ExceptionalLayerTheory.GaussianMomentCofactorCorrelations

/-!
# Uniform lattice errors for Gaussian cofactor correlations

The integer Gamma grid bounds every derivative branch before summation.
Relative to the diagonal continuum scale, the lattice error costs at most
`(2048 r³ α t² W²)^r` for cofactors at most `W`.
-/

open Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem gamma_nat_mono {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    Real.Gamma (i : ℝ) ≤ Real.Gamma (j : ℝ) := by
  have hj : 1 ≤ j := hi.trans hij
  have hi' : (i : ℝ) = ((i - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hi).symm
  have hj' : (j : ℝ) = ((j - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hj).symm
  rw [hi', hj', Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  exact_mod_cast Nat.factorial_le (Nat.sub_le_sub_right hij 1)

private theorem gamma_add_nat_le {q : ℝ} (hq : 0 < q) (j : ℕ) {P : ℝ}
    (hP : q + j ≤ P) : Real.Gamma (q + j) ≤ Real.Gamma q * P ^ j := by
  induction j generalizing P with
  | zero => simp
  | succ j ih =>
    have harg : 0 < q + j := by positivity
    have hP' : q + j ≤ P := by push_cast at hP; linarith only [hP]
    have hP0 : 0 < P := harg.trans_le hP'
    rw [Nat.cast_succ, show q + ((j : ℝ) + 1) = (q + j) + 1 by ring,
      Real.Gamma_add_one harg.ne']
    calc
      _ ≤ P * (Real.Gamma q * P ^ j) :=
        mul_le_mul hP' (ih hP') (Real.Gamma_pos_of_pos harg).le hP0.le
      _ = _ := by rw [pow_succ]; ring

/-- Every branch lies on the same positive integer Gamma grid. -/
theorem gaussianMellinJetConstant_odd_le (p k j : ℕ) (hj : 1 ≤ j) (hkj : k + j ≤ p) :
    gaussianMellinJetConstant k ((k : ℝ) + 2 * j - 1) ≤
      Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k := by
  have hp : 1 ≤ p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hG := Real.Gamma_pos_of_pos hpR
  induction k generalizing j with
  | zero =>
    simp only [gaussianMellinJetConstant, Nat.cast_zero, zero_add, pow_zero, mul_one]
    rw [show (2 * (j : ℝ) - 1 + 1) / 2 = j by ring]
    exact div_le_div_of_nonneg_right (gamma_nat_mono hj (by omega)) (by norm_num)
  | succ k ih =>
    have hlo := ih j hj (by omega : k + j ≤ p)
    have hhi := ih (j + 1) (by omega) (by omega : k + (j + 1) ≤ p)
    have ha : 0 ≤ ((k + 1 : ℕ) : ℝ) + 2 * j - 1 := by
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
      push_cast
      nlinarith only [hjR, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hcoef : |((k + 1 : ℕ) : ℝ) + 2 * j - 1| + 1 ≤ 2 * p := by
      rw [abs_of_nonneg ha]
      have hh : (k : ℝ) + 1 + j ≤ p := by exact_mod_cast hkj
      push_cast
      linarith only [hh, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hm : (((k + 1 : ℕ) : ℝ) + 2 * j - 1) - 1 = (k : ℝ) + 2 * j - 1 := by
      push_cast
      ring
    have hu : (((k + 1 : ℕ) : ℝ) + 2 * j - 1) + 1 = (k : ℝ) + 2 * (j + 1 : ℕ) - 1 := by
      push_cast
      ring
    rw [gaussianMellinJetConstant, hm, hu]
    have hE : 0 ≤ Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k := by positivity
    calc
      _ ≤ (|((k + 1 : ℕ) : ℝ) + 2 * j - 1| + 1) *
            (Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k) +
          8 * (Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_left hlo (by positivity))
          (mul_le_mul_of_nonneg_left hhi (by norm_num))
      _ ≤ (2 * p) * (Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k) +
          8 * (Real.Gamma (p : ℝ) / 2 * (2 * p + 8) ^ k) :=
        add_le_add (mul_le_mul_of_nonneg_right hcoef hE) (le_refl _)
      _ = _ := by rw [pow_succ]; ring

/-- Relative to the correlation's Gamma mass, all derivative constants cost
at most three powers of the order per moment. -/
theorem gaussianMellinJetConstant_pair_le (r : ℕ) (hr : r ≠ 0) :
    gaussianMellinJetConstant (2 * r) (((4 * r : ℕ) : ℝ) - 1) ≤
      Real.Gamma ((2 * r : ℕ) : ℝ) / 2 * (1024 * (r : ℝ) ^ 3) ^ r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  have hr0 : (0 : ℝ) < r := by linarith only [hr1]
  have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((2 * r : ℕ) : ℝ) by positivity)
  have hG3 := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((3 * r : ℕ) : ℝ) by positivity)
  have hC := gaussianMellinJetConstant_odd_le (3 * r) (2 * r) r (by omega) (by omega)
  have harg : ((2 * r : ℕ) : ℝ) + 2 * r - 1 = ((4 * r : ℕ) : ℝ) - 1 := by
    push_cast
    ring
  rw [harg] at hC
  have hratio := gamma_add_nat_le (show (0 : ℝ) < ((2 * r : ℕ) : ℝ) by positivity) r
    (P := ((3 * r : ℕ) : ℝ)) (by push_cast; linarith)
  have hsum : ((2 * r : ℕ) : ℝ) + r = ((3 * r : ℕ) : ℝ) := by push_cast; ring
  rw [hsum] at hratio
  have hfac : 2 * ((3 * r : ℕ) : ℝ) + 8 ≤ 14 * r := by push_cast; linarith only [hr1]
  calc
    _ ≤ Real.Gamma ((3 * r : ℕ) : ℝ) / 2 * (2 * ((3 * r : ℕ) : ℝ) + 8) ^ (2 * r) := hC
    _ ≤ (Real.Gamma ((2 * r : ℕ) : ℝ) * ((3 * r : ℕ) : ℝ) ^ r) / 2 *
        (14 * (r : ℝ)) ^ (2 * r) := by gcongr
    _ = Real.Gamma ((2 * r : ℕ) : ℝ) / 2 * (588 * (r : ℝ) ^ 3) ^ r := by
      push_cast
      rw [pow_mul (14 * (r : ℝ)) 2 r]
      have hp : (3 * (r : ℝ)) ^ r * ((14 * (r : ℝ)) ^ 2) ^ r =
          (588 * (r : ℝ) ^ 3) ^ r := by
        rw [← mul_pow]
        congr 1
        ring
      calc
        _ = Real.Gamma (2 * (r : ℝ)) / 2 *
            ((3 * (r : ℝ)) ^ r * ((14 * (r : ℝ)) ^ 2) ^ r) := by ring
        _ = _ := by rw [hp]
    _ ≤ _ := by gcongr; norm_num

private theorem bernoulli_quotient_le {r : ℕ} (hr : r ≠ 0) :
    |((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ) ≤ 1 := by
  have hF : (0 : ℝ) < ((2 * r).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpow : (4 : ℝ) ≤ 2 ^ (2 * r) := by
    have hh := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 2 ≤ 2 * r by omega)
    norm_num at hh
    exact hh
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
  have hden : (4 : ℝ) ≤ (2 * Real.pi) ^ (2 * r) :=
    hpow.trans (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hpi _)
  have hd0 : (0 : ℝ) < (2 * Real.pi) ^ (2 * r) := by positivity
  have hf : (2 : ℝ) / 2 ^ (2 * r) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 * r))).mpr (by linarith only [hpow])
  have he : (0 : ℝ) < 1 - 2 / 2 ^ (2 * r) := by linarith only [hf]
  have hi : ((1 : ℝ) - 2 / 2 ^ (2 * r))⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ he).mpr (by linarith only [hf])
  have hn : 2 * ((2 * r).factorial : ℝ) / (2 * Real.pi) ^ (2 * r) ≤
      ((2 * r).factorial : ℝ) / 2 := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hden hF.le]
  apply (div_le_iff₀ hF).mpr
  calc
    _ ≤ 2 * ((2 * r).factorial : ℝ) / (2 * Real.pi) ^ (2 * r) *
        ((1 : ℝ) - 2 / 2 ^ (2 * r))⁻¹ := (RHTower.DQPT.dqpt_abs_bernoulli_bounds hr).2
    _ ≤ (((2 * r).factorial : ℝ) / 2) * 2 :=
      mul_le_mul hn hi (by positivity) (by positivity)
    _ = _ := by ring

private theorem norm_half_gamma_double {r : ℕ} (hr : r ≠ 0) :
    ‖(1 / 2 : ℂ) * Complex.Gamma ((2 * r : ℕ) : ℂ)‖ =
      Real.Gamma ((2 * r : ℕ) : ℝ) / 2 := by
  have hG := Real.Gamma_pos_of_pos (show (0 : ℝ) < ((2 * r : ℕ) : ℝ) by
    exact_mod_cast (show 0 < 2 * r by omega))
  rw [← Complex.ofReal_natCast, Complex.Gamma_ofReal, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hG.le]
  norm_num only [norm_div, norm_one, norm_ofNat]
  ring

private theorem pair_sector {ε : ℂ} {t m k : ℝ}
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) :
    ‖gaussianCofactorPairDamping ε m k‖ ≤
      4 * (gaussianCofactorPairDamping ε m k).re * t := by
  calc
    _ ≤ ‖ε * (m : ℂ) ^ 2‖ + ‖(starRingEnd ℂ) ε * (k : ℂ) ^ 2‖ := norm_add_le _ _
    _ = ‖ε‖ * (m ^ 2 + k ^ 2) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs]
      ring
    _ ≤ (4 * ε.re * t) * (m ^ 2 + k ^ 2) :=
      mul_le_mul_of_nonneg_right hsector (by positivity)
    _ = _ := by rw [gaussianCofactorPairDamping_re]; ring

private theorem pair_normalized_scale_le {ε : ℂ} (hε : 0 < ε.re)
    {m k W : ℝ} (hm : 0 < m) (hk : 0 < k) (hmW : m ≤ W) (hkW : k ≤ W) :
    (2 * ε.re * m * k) ^ 2 / (gaussianCofactorPairDamping ε m k).re ≤ 2 * ε.re * W ^ 2 := by
  apply (div_le_iff₀ (gaussianCofactorPairDamping_re_pos hε hm hk)).mpr
  rw [gaussianCofactorPairDamping_re]
  have hm2 := pow_le_pow_left₀ hm.le hmW 2
  have hk2 := pow_le_pow_left₀ hk.le hkW 2
  have hs := add_le_add (mul_le_mul_of_nonneg_right hm2 (sq_nonneg k))
    (mul_le_mul_of_nonneg_right hk2 (sq_nonneg m))
  nlinarith only [mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * ε.re ^ 2)]

private theorem scale_mul_power (r : ℕ) (A s t d z : ℝ) (hd : d ≠ 0) (hz : z ≠ 0) :
    (A / d ^ (2 * r)) * (s * t ^ 2 * d ^ 2 / z) ^ r =
      A * s ^ r * t ^ (2 * r) / z ^ r := by
  simp only [mul_pow, div_pow, ← pow_mul]
  field_simp [hd, hz]

/-- Uniform relative error for the literal complete lattice correlation. -/
theorem norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le_scale {r : ℕ}
    (hr : r ≠ 0) {t W : ℝ} (ht : 1 ≤ t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmW : (m : ℝ) ≤ W) (hkW : (k : ℝ) ≤ W) :
    ‖(∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
        (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))) -
      gaussianCofactorCorrelationMain r t ε m k‖ ≤
      gaussianCofactorCorrelationScale r t ε m k *
        (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * W ^ 2) ^ r := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hrR : (0 : ℝ) < r := by exact_mod_cast (Nat.pos_of_ne_zero hr)
  have hz := gaussianCofactorPairDamping_re_pos hε hmR hkR
  have hD : 2 * ε.re * (m : ℝ) * k ≠ 0 := ne_of_gt (by positivity)
  have hre : (((4 * r : ℕ) : ℂ) - 1).re = ((4 * r : ℕ) : ℝ) - 1 := by simp
  have hw : ((2 * r : ℕ) : ℝ) - 1 < (((4 * r : ℕ) : ℂ) - 1).re := by
    rw [hre]
    push_cast
    linarith only [hrR]
  have hV := gaussianMellinJetVariation_le (2 * r) hw hz ht
    (by simpa using (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht)) (pair_sector hsector)
  rw [hre, show (((2 * r : ℕ) : ℝ) - (((4 * r : ℕ) : ℝ) - 1) - 1) / 2 =
    -(r : ℝ) by push_cast; ring, Real.rpow_neg hz.le, Real.rpow_natCast] at hV
  have hC0 := gaussianMellinJetConstant_nonneg (2 * r) (by rwa [hre] at hw)
  have hBC : (|((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ)) *
      gaussianMellinJetConstant (2 * r) (((4 * r : ℕ) : ℝ) - 1) ≤
      Real.Gamma ((2 * r : ℕ) : ℝ) / 2 * (1024 * (r : ℝ) ^ 3) ^ r := by
    simpa only [one_mul] using mul_le_mul (bernoulli_quotient_le hr)
      (gaussianMellinJetConstant_pair_le r hr) hC0 (by norm_num : (0 : ℝ) ≤ 1)
  have hbase : (1024 * (r : ℝ) ^ 3) * t ^ 2 * (2 * ε.re * (m : ℝ) * k) ^ 2 /
      (gaussianCofactorPairDamping ε m k).re ≤
      2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * W ^ 2 := by
    calc
      _ = ((1024 * (r : ℝ) ^ 3) * t ^ 2) *
          ((2 * ε.re * (m : ℝ) * k) ^ 2 / (gaussianCofactorPairDamping ε m k).re) := by ring
      _ ≤ ((1024 * (r : ℝ) ^ 3) * t ^ 2) * (2 * ε.re * W ^ 2) :=
        mul_le_mul_of_nonneg_left (pair_normalized_scale_le hε hmR hkR hmW hkW) (by positivity)
      _ = _ := by ring
  have hraw := norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le hr t hε hm hk
  simp only [norm_mul, Complex.norm_conj] at hraw
  calc
    _ ≤ _ := hraw
    _ ≤ (‖gaussianCofactorAmplitude r t ε m‖ * ‖gaussianCofactorAmplitude r t ε k‖) *
        (|((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ)) *
        (gaussianMellinJetConstant (2 * r) (((4 * r : ℕ) : ℝ) - 1) * t ^ (2 * r) *
          ((gaussianCofactorPairDamping ε m k).re ^ r)⁻¹) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (‖gaussianCofactorAmplitude r t ε m‖ * ‖gaussianCofactorAmplitude r t ε k‖) *
        ((|((bernoulli (2 * r) : ℚ) : ℝ)| / ((2 * r).factorial : ℝ)) *
          gaussianMellinJetConstant (2 * r) (((4 * r : ℕ) : ℝ) - 1)) *
        t ^ (2 * r) / (gaussianCofactorPairDamping ε m k).re ^ r := by ring
    _ ≤ (‖gaussianCofactorAmplitude r t ε m‖ * ‖gaussianCofactorAmplitude r t ε k‖) *
        (Real.Gamma ((2 * r : ℕ) : ℝ) / 2 * (1024 * (r : ℝ) ^ 3) ^ r) *
        t ^ (2 * r) / (gaussianCofactorPairDamping ε m k).re ^ r := by gcongr
    _ = gaussianCofactorCorrelationScale r t ε m k *
        ((1024 * (r : ℝ) ^ 3) * t ^ 2 * (2 * ε.re * (m : ℝ) * k) ^ 2 /
          (gaussianCofactorPairDamping ε m k).re) ^ r := by
      rw [gaussianCofactorCorrelationScale, norm_half_gamma_double hr,
        scale_mul_power r _ _ _ _ _ hD hz.ne']
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hbase r)
      (gaussianCofactorCorrelationScale_nonneg r t hε hmR hkR)

/-- Complete lattice cancellation, with the near-diagonal profile and its
uniform discretization cost both explicit. -/
theorem norm_tsum_gaussianHigherPrimeMoment_pair_le {r : ℕ} (hr : r ≠ 0)
    {t W : ℝ} (ht : 1 ≤ t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (hmW : (m : ℝ) ≤ W) (hkW : (k : ℝ) ≤ W) :
    ‖∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
      (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))‖ ≤
      gaussianCofactorCorrelationScale r t ε m k *
        (gaussianCofactorOverlap r ε m k + (2048 * (r : ℝ) ^ 3 * ε.re * t ^ 2 * W ^ 2) ^ r) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hE := norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le_scale hr ht hε hsector hm hk hmW hkW
  have htri := norm_add_le
    ((∑' d : ℕ, gaussianHigherPrimeMomentWeight r (1 / 2) t ε (m * (d + 1)) *
      (starRingEnd ℂ) (gaussianHigherPrimeMomentWeight r (1 / 2) t ε (k * (d + 1)))) -
        gaussianCofactorCorrelationMain r t ε m k) (gaussianCofactorCorrelationMain r t ε m k)
  rw [sub_add_cancel, norm_gaussianCofactorCorrelationMain r t hε hmR hkR] at htri
  apply htri.trans
  nlinarith only [hE]

private theorem gamma_double_le_order {r : ℕ} (hr : r ≠ 0) :
    Real.Gamma ((2 * r : ℕ) : ℝ) / 2 ≤ ((2 * r : ℕ) : ℝ) ^ (2 * r) := by
  have htwo : 1 ≤ 2 * r := by omega
  have harg : (1 : ℝ) + ((2 * r - 1 : ℕ) : ℝ) = ((2 * r : ℕ) : ℝ) := by
    rw [Nat.cast_sub htwo, Nat.cast_one]
    ring
  have hg := gamma_add_nat_le (by norm_num : (0 : ℝ) < 1) (2 * r - 1)
    (P := ((2 * r : ℕ) : ℝ)) (by rw [harg])
  rw [harg] at hg
  have hg1 : Real.Gamma 1 = 1 := by simp
  rw [hg1, one_mul] at hg
  have hp := pow_le_pow_right₀ (by exact_mod_cast htwo : (1 : ℝ) ≤ ((2 * r : ℕ) : ℝ))
    (Nat.sub_le (2 * r) 1)
  have hG := (Real.Gamma_pos_of_pos
    (by exact_mod_cast (show 0 < 2 * r by omega) : (0 : ℝ) < ((2 * r : ℕ) : ℝ))).le
  linarith only [hg, hp, hG]

private theorem norm_cofactorAmplitude_le (r : ℕ) {t : ℝ} (ht : 1 ≤ t)
    (ε : ℂ) {m : ℝ} (hm : 1 ≤ m) :
    ‖gaussianCofactorAmplitude r t ε m‖ ≤ (‖ε‖ / t) ^ r * m ^ (2 * r) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  rw [gaussianCofactorAmplitude, norm_mul, norm_pow, norm_div, Complex.norm_real,
    Real.norm_of_nonneg ht0.le, Complex.norm_cpow_eq_rpow_re_of_pos hm0]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hre : (gaussianCriticalMomentExponent r t).re = ((2 * r : ℕ) : ℝ) - 1 / 2 := by
    simp [gaussianCriticalMomentExponent]
  rw [hre]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hm
    (show ((2 * r : ℕ) : ℝ) - 1 / 2 ≤ ((2 * r : ℕ) : ℝ) by linarith)

/-- The diagonal normalization has no exponential-scale factor. -/
theorem gaussianCofactorCorrelationScale_le_order {r : ℕ} (hr : r ≠ 0)
    {t : ℝ} (ht : 1 ≤ t) {ε : ℂ} (hε : 0 < ε.re)
    (hsector : ‖ε‖ ≤ 4 * ε.re * t) {m k : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k) :
    gaussianCofactorCorrelationScale r t ε m k ≤ (4 * (r : ℝ)) ^ (2 * r) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hG := (Real.Gamma_pos_of_pos
    (by exact_mod_cast (show 0 < 2 * r by omega) : (0 : ℝ) < ((2 * r : ℕ) : ℝ))).le
  have hratio : ‖ε‖ / (2 * ε.re * t) ≤ 2 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith only [hsector])
  unfold gaussianCofactorCorrelationScale
  rw [norm_half_gamma_double hr]
  calc
    _ ≤ ((‖ε‖ / t) ^ r * m ^ (2 * r)) * ((‖ε‖ / t) ^ r * k ^ (2 * r)) *
        (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) / (2 * ε.re * m * k) ^ (2 * r) := by
      gcongr
      · exact norm_cofactorAmplitude_le r ht ε hm
      · exact norm_cofactorAmplitude_le r ht ε hk
    _ = (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) * (‖ε‖ / (2 * ε.re * t)) ^ (2 * r) := by
      rw [show 2 * r = r + r by omega]
      simp only [pow_add, mul_pow, div_pow]
      field_simp [ht0.ne', hm0.ne', hk0.ne', hε.ne']
    _ ≤ (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) * (2 : ℝ) ^ (2 * r) := by gcongr
    _ ≤ ((2 * r : ℕ) : ℝ) ^ (2 * r) * (2 : ℝ) ^ (2 * r) :=
      mul_le_mul_of_nonneg_right (gamma_double_le_order hr) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; push_cast; ring

/-- Away from the cofactor diagonal, the continuous correlation has a
rapidly decreasing absolute bound when the order is sublinear in height. -/
theorem norm_gaussianCofactorCorrelationMain_le_order_ratio {r : ℕ} (hr : r ≠ 0)
    {t : ℝ} (ht : 1 ≤ t) {ε : ℂ} (hε : 0 < ε.re) {m k : ℝ} (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hsep : 2 * k ≤ m) (hrot : ε.re * t ≤ |ε.im|) :
    ‖gaussianCofactorCorrelationMain r t ε m k‖ ≤ (4 * (r : ℝ) / t) ^ (2 * r) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hzre := gaussianCofactorPairDamping_re_pos hε hm0 hk0
  have hz0 : 0 < ‖gaussianCofactorPairDamping ε m k‖ := by
    exact hzre.trans_le (Complex.re_le_norm _)
  have hdiff : m * k ≤ m ^ 2 - k ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hsep) hm0.le,
      mul_nonneg (sub_nonneg.mpr hsep) hk0.le, sq_nonneg k]
  have hdiff2 := pow_le_pow_left₀ (mul_pos hm0 hk0).le hdiff 2
  have hnormsq : (|ε.im| * (m * k)) ^ 2 ≤ ‖gaussianCofactorPairDamping ε m k‖ ^ 2 := by
    rw [mul_pow, sq_abs, norm_sq_gaussianCofactorPairDamping]
    nlinarith only [mul_le_mul_of_nonneg_left hdiff2 (sq_nonneg ε.im),
      sq_nonneg (2 * ε.re * m * k),
      mul_nonneg (sq_nonneg ε.re) (sq_nonneg (m ^ 2 - k ^ 2))]
  have hnorm : |ε.im| * (m * k) ≤ ‖gaussianCofactorPairDamping ε m k‖ := by
    nlinarith only [hnormsq, norm_nonneg (gaussianCofactorPairDamping ε m k),
      mul_nonneg (abs_nonneg ε.im) (mul_pos hm0 hk0).le]
  have hα : ε.re ≤ |ε.im| := by
    nlinarith only [hrot, mul_le_mul_of_nonneg_left ht hε.le]
  have hnε : ‖ε‖ ≤ 2 * |ε.im| := by
    have hh := Complex.norm_le_abs_re_add_abs_im ε
    rw [abs_of_pos hε] at hh
    linarith only [hh, hα]
  have hnum : ‖ε‖ * m * k ≤ 2 * ‖gaussianCofactorPairDamping ε m k‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right hnε (mul_pos hm0 hk0).le, hnorm]
  have hratio : (‖ε‖ * m * k) / (t * ‖gaussianCofactorPairDamping ε m k‖) ≤ 2 / t := by
    apply (div_le_div_iff₀ (mul_pos ht0 hz0) ht0).mpr
    nlinarith only [mul_le_mul_of_nonneg_right hnum ht0.le]
  have hG := (Real.Gamma_pos_of_pos
    (by exact_mod_cast (show 0 < 2 * r by omega) : (0 : ℝ) < ((2 * r : ℕ) : ℝ))).le
  unfold gaussianCofactorCorrelationMain
  rw [norm_div, norm_mul, norm_mul, Complex.norm_conj, norm_pow, norm_half_gamma_double hr]
  calc
    _ ≤ ((‖ε‖ / t) ^ r * m ^ (2 * r)) * ((‖ε‖ / t) ^ r * k ^ (2 * r)) *
        (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) / ‖gaussianCofactorPairDamping ε m k‖ ^ (2 * r) := by
      gcongr
      · exact norm_cofactorAmplitude_le r ht ε hm
      · exact norm_cofactorAmplitude_le r ht ε hk
    _ = (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) *
        ((‖ε‖ * m * k) / (t * ‖gaussianCofactorPairDamping ε m k‖)) ^ (2 * r) := by
      rw [show 2 * r = r + r by omega]
      simp only [pow_add, mul_pow, div_pow]
      ring
    _ ≤ (Real.Gamma ((2 * r : ℕ) : ℝ) / 2) * (2 / t) ^ (2 * r) := by gcongr
    _ ≤ ((2 * r : ℕ) : ℝ) ^ (2 * r) * (2 / t) ^ (2 * r) :=
      mul_le_mul_of_nonneg_right (gamma_double_le_order hr) (by positivity)
    _ = _ := by rw [← mul_pow]; congr 1; push_cast; ring

#print axioms gaussianMellinJetConstant_pair_le
#print axioms norm_tsum_gaussianHigherPrimeMoment_pair_sub_main_le_scale
#print axioms norm_tsum_gaussianHigherPrimeMoment_pair_le
#print axioms gaussianCofactorCorrelationScale_le_order
#print axioms norm_gaussianCofactorCorrelationMain_le_order_ratio

end GaloisForLFunctions.ExceptionalLayerTheory
