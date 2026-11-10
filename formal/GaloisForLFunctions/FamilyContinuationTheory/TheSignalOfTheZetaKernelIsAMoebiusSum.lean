import GaloisForLFunctions.FamilyContinuationTheory.TheTwoLegsGiveTheRiemannHypothesis

/-!
# The signal of the zeta kernel is a Möbius sum

On `Re s > 1` the zeta kernel `exp((s − c)²)/((s − 1)ζ(s))` is the pole kernel
`exp((s − c)²)/(s − 1)` times the Dirichlet series of the Möbius function. Read on the line
`Re s = 2`, and integrated term by term:

`signal (zetaKernel c) 2 Z = Σ_n μ(n) · signal (poleKernel c) 2 (Z / n)` (`signal_zetaKernel_eq_tsum`).

The signal of the pole kernel is a smooth cutoff. So the first input of the route, a bound
`O(Z^b)` with `b < 1` for the signal of the zeta kernel, is a power saving for one smoothed
Möbius sum (`riemannHypothesis_of_moebiusSum_le_of_jasDressedPSD_one`).
-/

noncomputable section

open Complex MeasureTheory

namespace GaloisForLFunctions.FamilyContinuationTheory

open _root_.RHTower

/-- The point `2 − iy` of the line of integration. -/
def linePoint (y : ℝ) : ℂ := -(((-2 : ℝ) : ℂ) + y * I)

theorem linePoint_re (y : ℝ) : (linePoint y).re = 2 := by simp [linePoint]

theorem linePoint_im (y : ℝ) : (linePoint y).im = -y := by simp [linePoint]

theorem continuous_linePoint : Continuous linePoint := by
  unfold linePoint
  fun_prop

/-- The signal as an integral over the line `Re s = 2`. -/
theorem signal_two_eq_integral (G : ℂ → ℂ) (Z : ℝ) :
    signal G 2 Z =
      (1 / (2 * Real.pi) : ℝ) • ∫ y : ℝ, (Z : ℂ) ^ linePoint y • G (linePoint y) := by
  unfold signal linePoint
  rw [mellinInv]

/-- The pole kernel with Gaussian centre `c`: `exp((s − c)²)/(s − 1)`. -/
def poleKernel (c : ℝ) (s : ℂ) : ℂ := cexp ((s - c) ^ 2) / (s - 1)

/-- The Dirichlet series of the Möbius function. -/
def moebiusSeries (s : ℂ) : ℂ := LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) s

/-- On `Re s > 1` the zeta kernel is the pole kernel times the Möbius series. -/
theorem zetaKernel_eq_poleKernel_mul {c : ℝ} {s : ℂ} (hs : 1 < s.re) :
    zetaKernel c s = poleKernel c s * moebiusSeries s := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hL : moebiusSeries s = (riemannZeta s)⁻¹ := by
    have h := LSeries_zeta_mul_Lseries_moebius hs
    rw [LSeries_zeta_eq_riemannZeta hs] at h
    exact eq_inv_of_mul_eq_one_right h
  unfold zetaKernel poleKernel
  rw [zetaEntire_eq hs1, hL]
  field_simp

/-- The pole kernel decays like `C/(1+y²)` on the line. -/
theorem norm_poleKernel_linePoint_le (c : ℝ) (y : ℝ) :
    ‖poleKernel c (linePoint y)‖ ≤ Real.exp ((2 - c) ^ 2) * (1 + y ^ 2)⁻¹ := by
  have h1 : (1 : ℝ) ≤ ‖linePoint y - 1‖ := by
    have hre : (1 : ℝ) ≤ (linePoint y - 1).re := by rw [sub_re, one_re, linePoint_re]; norm_num
    exact le_trans hre (le_trans (le_abs_self _) (abs_re_le_norm _))
  have hexp : Real.exp (-(y ^ 2)) ≤ (1 + y ^ 2)⁻¹ := by
    rw [Real.exp_neg]
    refine inv_anti₀ (by positivity) ?_
    linarith [Real.add_one_le_exp (y ^ 2)]
  unfold poleKernel
  rw [norm_div, norm_cexp_sub_sq, linePoint_re, linePoint_im, neg_sq, sub_eq_add_neg,
    Real.exp_add]
  calc Real.exp ((2 - c) ^ 2) * Real.exp (-(y ^ 2)) / ‖linePoint y - 1‖
      ≤ Real.exp ((2 - c) ^ 2) * Real.exp (-(y ^ 2)) / 1 :=
        div_le_div_of_nonneg_left (by positivity) one_pos h1
    _ = Real.exp ((2 - c) ^ 2) * Real.exp (-(y ^ 2)) := div_one _
    _ ≤ Real.exp ((2 - c) ^ 2) * (1 + y ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le

theorem continuous_poleKernel_linePoint (c : ℝ) :
    Continuous fun y : ℝ => poleKernel c (linePoint y) := by
  unfold poleKernel
  refine Continuous.div (by have := continuous_linePoint; fun_prop)
    (continuous_linePoint.sub continuous_const) fun y h => ?_
  have hre := congrArg Complex.re h
  rw [sub_re, one_re, linePoint_re, zero_re] at hre
  norm_num at hre

/-- A power of a quotient of positive reals. -/
theorem ofReal_div_natCast_cpow {Z : ℝ} (hZ : 0 ≤ Z) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    ((Z / n : ℝ) : ℂ) ^ s = (Z : ℂ) ^ s / (n : ℂ) ^ s := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hmul := mul_cpow_ofReal_nonneg (div_nonneg hZ hnpos.le) hnpos.le s
  have hZn : ((Z / n : ℝ) : ℂ) * ((n : ℝ) : ℂ) = (Z : ℂ) := by
    rw [← ofReal_mul, div_mul_cancel₀ _ hnpos.ne']
  rw [hZn, ofReal_natCast] at hmul
  have hne : (n : ℂ) ^ s ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => (Nat.cast_ne_zero.mpr hn) h.1
  exact eq_div_of_mul_eq hne hmul.symm

/-- The term of index `n` of the signal: `μ(n) (Z/n)^s K(s)` on the line. -/
def moebiusTerm (c Z : ℝ) (n : ℕ) (y : ℝ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) *
    (((Z / n : ℝ) : ℂ) ^ linePoint y • poleKernel c (linePoint y))

theorem norm_moebiusTerm_le {c Z : ℝ} (hZ : 0 < Z) (n : ℕ) (y : ℝ) :
    ‖moebiusTerm c Z n y‖ ≤
      Z ^ 2 * Real.exp ((2 - c) ^ 2) * (1 / (n : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [moebiusTerm]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [← Int.cast_abs, Complex.norm_intCast] <;>
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hpow : ‖((Z / n : ℝ) : ℂ) ^ linePoint y‖ = Z ^ 2 * (1 / (n : ℝ) ^ 2) := by
    rw [norm_cpow_eq_rpow_re_of_pos (div_pos hZ hnpos), linePoint_re]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_pow]
    ring
  unfold moebiusTerm
  rw [norm_mul, norm_smul, hpow]
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ *
        (Z ^ 2 * (1 / (n : ℝ) ^ 2) * ‖poleKernel c (linePoint y)‖)
      ≤ 1 * (Z ^ 2 * (1 / (n : ℝ) ^ 2) * (Real.exp ((2 - c) ^ 2) * (1 + y ^ 2)⁻¹)) :=
        mul_le_mul hμ
          (mul_le_mul_of_nonneg_left (norm_poleKernel_linePoint_le c y) (by positivity))
          (by positivity) zero_le_one
    _ = Z ^ 2 * Real.exp ((2 - c) ^ 2) * (1 / (n : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ := by ring

theorem continuous_moebiusTerm {c Z : ℝ} (hZ : 0 < Z) (n : ℕ) :
    Continuous (moebiusTerm c Z n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : moebiusTerm c Z 0 = fun _ => 0 := by
      funext y
      simp [moebiusTerm]
    rw [this]
    exact continuous_const
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hbase : ((Z / n : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (div_pos hZ hnpos).ne'
  unfold moebiusTerm
  refine continuous_const.mul (Continuous.smul ?_ (continuous_poleKernel_linePoint c))
  exact continuous_linePoint.const_cpow (Or.inl hbase)

theorem integrable_moebiusTerm {c Z : ℝ} (hZ : 0 < Z) (n : ℕ) :
    Integrable (moebiusTerm c Z n) := by
  have hdom : Integrable fun y : ℝ =>
      Z ^ 2 * Real.exp ((2 - c) ^ 2) * (1 / (n : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  exact hdom.mono' (continuous_moebiusTerm hZ n).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_moebiusTerm_le hZ n))

/-- On the line the integrand of the zeta signal is the sum of the Möbius terms. -/
theorem hasSum_moebiusTerm {c Z : ℝ} (hZ : 0 < Z) (y : ℝ) :
    HasSum (fun n : ℕ => moebiusTerm c Z n y)
      ((Z : ℂ) ^ linePoint y • zetaKernel c (linePoint y)) := by
  have hre : 1 < (linePoint y).re := by rw [linePoint_re]; norm_num
  have hsum : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (linePoint y) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hre
  have hL := hsum.LSeriesHasSum
  rw [zetaKernel_eq_poleKernel_mul hre, smul_eq_mul]
  have h := (hL.mul_left ((Z : ℂ) ^ linePoint y * poleKernel c (linePoint y)))
  have hfun : (fun n : ℕ => (Z : ℂ) ^ linePoint y * poleKernel c (linePoint y) *
      LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (linePoint y) n) =
      fun n : ℕ => moebiusTerm c Z n y := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [moebiusTerm, LSeries.term_def]
    · rw [LSeries.term_def, if_neg hn, moebiusTerm, smul_eq_mul,
        ofReal_div_natCast_cpow hZ.le hn]
      have hne : (n : ℂ) ^ linePoint y ≠ 0 := by
        rw [Ne, cpow_eq_zero_iff]
        exact fun h => (Nat.cast_ne_zero.mpr hn) h.1
      field_simp
  rw [hfun] at h
  unfold moebiusSeries
  convert h using 1
  ring

/-- **The signal of the zeta kernel is a Möbius sum.** -/
theorem signal_zetaKernel_eq_tsum (c : ℝ) {Z : ℝ} (hZ : 0 < Z) :
    signal (zetaKernel c) 2 Z =
      ∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * signal (poleKernel c) 2 (Z / n) := by
  have hint : ∀ n : ℕ, Integrable (moebiusTerm c Z n) := integrable_moebiusTerm hZ
  have hsumm : Summable fun n : ℕ => ∫ y : ℝ, ‖moebiusTerm c Z n y‖ := by
    have hbound : ∀ n : ℕ, ∫ y : ℝ, ‖moebiusTerm c Z n y‖ ≤
        Z ^ 2 * Real.exp ((2 - c) ^ 2) * Real.pi * (1 / (n : ℝ) ^ 2) := by
      intro n
      have hdom : Integrable fun y : ℝ =>
          Z ^ 2 * Real.exp ((2 - c) ^ 2) * (1 / (n : ℝ) ^ 2) * (1 + y ^ 2)⁻¹ :=
        integrable_inv_one_add_sq.const_mul _
      have h := integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
        hdom (Filter.Eventually.of_forall (norm_moebiusTerm_le hZ n))
      rw [integral_const_mul, integral_univ_inv_one_add_sq] at h
      calc ∫ y : ℝ, ‖moebiusTerm c Z n y‖
          ≤ Z ^ 2 * Real.exp ((2 - c) ^ 2) * (1 / (n : ℝ) ^ 2) * Real.pi := h
        _ = Z ^ 2 * Real.exp ((2 - c) ^ 2) * Real.pi * (1 / (n : ℝ) ^ 2) := by ring
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun y => norm_nonneg _) hbound ?_
    exact (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _
  have hswap := integral_tsum_of_summable_integral_norm hint hsumm
  have hpoint : (fun y : ℝ => ∑' n : ℕ, moebiusTerm c Z n y) =
      fun y : ℝ => (Z : ℂ) ^ linePoint y • zetaKernel c (linePoint y) := by
    funext y
    exact (hasSum_moebiusTerm hZ y).tsum_eq
  rw [hpoint] at hswap
  rw [signal_two_eq_integral, ← hswap, ← tsum_const_smul'']
  refine tsum_congr fun n => ?_
  rw [signal_two_eq_integral]
  unfold moebiusTerm
  rw [integral_const_mul, smul_mul_assoc, mul_smul_comm]

/-- **The route with an arithmetic first input.** A power saving `O(Z^b)`, `½ ≤ b < 1`, for the
smoothed Möbius sum `Σ_n μ(n) · signal (poleKernel c) 2 (Z/n)`, together with positivity of the
dressed lag aggregate at level one, gives the Riemann hypothesis. -/
theorem riemannHypothesis_of_moebiusSum_le_of_jasDressedPSD_one {c b K Z₀ : ℝ} (hb₀ : 1 / 2 ≤ b)
    (hb : b < 1) (hZ₀ : 0 < Z₀)
    (hK : ∀ Z : ℝ, Z₀ ≤ Z →
      ‖∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * signal (poleKernel c) 2 (Z / n)‖ ≤
        K * Z ^ b)
    (hPSD : JasDressedPSD 1) : RiemannHypothesis := by
  refine riemannHypothesis_of_signal_le_of_jasDressedPSD_one (c := c) hb₀ hb hZ₀ (fun Z hZ => ?_)
    hPSD
  rw [signal_zetaKernel_eq_tsum c (lt_of_lt_of_le hZ₀ hZ)]
  exact hK Z hZ

end GaloisForLFunctions.FamilyContinuationTheory
