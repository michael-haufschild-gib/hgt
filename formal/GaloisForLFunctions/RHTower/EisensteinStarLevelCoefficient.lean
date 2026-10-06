import GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes
import GaloisForLFunctions.RHTower.MaassWhittakerUniqueness

/-!
# Level-period Fourier coefficients of the continued non-constant Eisenstein part

For `Re s > 1/2` the Fourier series `E^*_σ(z, s) = Σ_{n≠0} N^{-s} W_s(n, y/N) e(nx/N) D_n(s)` converges
absolutely, uniformly in `x` (`summable_norm_termX`), so its `n`-th Fourier coefficient over the period
`N` is the single term `N^{-s} W_s(n, y/N) D_n(s)` (`levelCoeff_EstarExt`).
-/

open Complex UpperHalfPlane MeasureTheory Filter Topology
open scoped MatrixGroups FourierTransform

namespace GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
open GaloisForLFunctions.RHTower.SelbergPoincareKernel GaloisForLFunctions.RHTower.SelbergEisensteinCuspSlice
  GaloisForLFunctions.RHTower.SelbergEisensteinCuspFourier GaloisForLFunctions.RHTower.SelbergEisensteinCoefficientSeries
  GaloisForLFunctions.RHTower.SelbergKernelBessel GaloisForLFunctions.RHTower.SelbergMoebiusUnitClassL
  GaloisForLFunctions.RHTower.SelbergEisensteinStar GaloisForLFunctions.RHTower.SelbergPoincareContinuation

noncomputable section

variable (N : ℕ) [NeZero N] (σ : SL(2, ℤ))

/-- The `x`-independent coefficient of the `n`-th term. -/
def termCoeff (n : ℤ) (s : ℂ) (y : ℝ) : ℂ :=
  if n = 0 then 0 else cexp (-s * (Real.log N : ℂ)) * kerBessel (y / N) s n * Dn N σ n s

theorem termX_eq (n : ℤ) (s : ℂ) (z : ℍ) :
    termX N σ n s z = termCoeff N σ n s z.im * cexp (2 * Real.pi * Complex.I * n * z.re / N) := by
  unfold termX termCoeff
  split_ifs <;> ring

/-- **Absolute convergence** of the Fourier series of the continued non-constant part. -/
theorem summable_norm_termCoeff {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℤ => ‖termCoeff N σ n s y‖ := by
  have hs1 : 2 * s ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hne : ∀ χ : DirichletCharacter ℂ N, DirichletCharacter.LFunction χ (2 * s) ≠ 0 := fun χ =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) (by simp; linarith)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  set Y := y / N
  have hY : 0 < Y := div_pos hy hN0
  set B1 := ‖2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹‖
  set B2 := ∑ u : (ZMod N)ˣ, ‖LU N u (2 * s)‖
  set lo := s.re - 1 / 2
  set k : ℕ := ⌈|lo|⌉₊
  have hlo : lo ≤ k := (le_abs_self lo).trans (Nat.le_ceil _)
  set R := ‖s‖ + 1 / 2
  set E0 := Real.exp (R ^ 2 / (2 * (2 * Real.pi * Y))) * Real.sqrt (2 * Real.pi / (2 * Real.pi * Y))
  set C := (Y ^ s.re + Y ^ s.re) * B1 * ((Y ^ lo)⁻¹ + (Y ^ lo)⁻¹) * E0 * (B2 * 2)
  have hC : 0 ≤ C := by simp only [C, E0]; positivity
  set bound : ℤ → ℝ := fun n => if n = 0 then 0 else
    C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * Y) * n.natAbs)
  have hle : ∀ n, ‖termCoeff N σ n s y‖ ≤ bound n := fun n => by
    by_cases hn : n = 0
    · simp [termCoeff, bound, hn]
    simp only [termCoeff, bound, if_neg hn]
    have hEN : ‖cexp (-s * (Real.log N : ℂ))‖ ≤ 1 := by
      have := norm_exp_neg_mul_log (s := s) (σ := 0) hN1 (by linarith)
      rwa [neg_zero, Real.rpow_zero] at this
    have hK : ‖kerBessel Y s n‖ ≤ (Y ^ s.re + Y ^ s.re) * B1 *
        (((Y ^ lo)⁻¹ + (Y ^ lo)⁻¹) * (n.natAbs : ℝ) ^ k) *
        (Real.exp (-(2 * Real.pi * Y * |(n : ℝ)|)) * E0) := by
      unfold kerBessel
      rw [norm_mul, norm_mul, norm_mul]
      have e1 : ‖((Y : ℝ) : ℂ) ^ s‖ ≤ Y ^ s.re + Y ^ s.re := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        linarith [Real.rpow_nonneg hY.le s.re]
      have hx : 0 < |((n : ℤ) : ℝ)| / Y := div_pos (abs_pos.mpr (by exact_mod_cast hn)) hY
      have e3 : ‖(((|((n : ℤ) : ℝ)| / Y : ℝ)) : ℂ) ^ (s - 1 / 2)‖ ≤
          ((Y ^ lo)⁻¹ + (Y ^ lo)⁻¹) * (n.natAbs : ℝ) ^ k := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
        have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
        rw [hre]
        exact rpow_natAbs_div_le hY hn le_rfl le_rfl hlo hlo
      have e4 := norm_bessel_le hY hn (ν := s - 1 / 2) (R := R) (by
        calc ‖s - 1 / 2‖ ≤ ‖s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
          _ = ‖s‖ + 1 / 2 := by norm_num)
      gcongr
    have hD : ‖Dn N σ n s‖ ≤ B2 * (2 * (n.natAbs : ℝ) ^ 2) :=
      norm_Dn_le_sq N σ n (by linarith)
    rw [norm_mul, norm_mul]
    have habs : |((n : ℤ) : ℝ)| = (n.natAbs : ℝ) := by simp [Nat.cast_natAbs]
    calc ‖cexp (-s * (Real.log N : ℂ))‖ * ‖kerBessel Y s n‖ * ‖Dn N σ n s‖
        ≤ 1 * ((Y ^ s.re + Y ^ s.re) * B1 * (((Y ^ lo)⁻¹ + (Y ^ lo)⁻¹) * (n.natAbs : ℝ) ^ k) *
            (Real.exp (-(2 * Real.pi * Y * |(n : ℝ)|)) * E0)) * (B2 * (2 * (n.natAbs : ℝ) ^ 2)) := by
          gcongr
      _ = C * (n.natAbs : ℝ) ^ (k + 2) * Real.exp (-(2 * Real.pi * Y) * n.natAbs) := by
          rw [habs]; simp only [C]; rw [pow_add]; ring_nf
  have hbase := (Real.summable_pow_mul_exp_neg_nat_mul (k + 2) (r := 2 * Real.pi * Y)
    (by positivity)).mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hle ?_
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hbase
    · simp only [bound]; split_ifs <;> positivity
    · simp only [bound]
      split_ifs
      · positivity
      · simp only [Int.natAbs_natCast]; ring_nf; exact le_rfl
  · refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hbase
    · simp only [bound]; split_ifs <;> positivity
    · simp only [bound]
      split_ifs
      · positivity
      · simp only [Int.natAbs_neg, Int.natAbs_natCast]; ring_nf; exact le_rfl

theorem integral_exp_two_pi_int_mul {T : ℝ} (hT : 0 < T) (k : ℤ) :
    ∫ x in (0 : ℝ)..T, cexp (2 * Real.pi * Complex.I * k * x / T) = if k = 0 then (T : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * Real.pi * Complex.I * k / T : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) this) hT'
    have h := integral_exp_mul_complex (a := 0) (b := T) hc
    have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
    have e : (2 * Real.pi * Complex.I * k / T : ℂ) * T = k * (2 * Real.pi * Complex.I) := by
      field_simp
    rw [e, Complex.exp_int_mul_two_pi_mul_I, sub_self, zero_div] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun x _ => ?_
    congr 1
    ring

theorem integral_exp_two_pi_int_mul_nat (k : ℤ) :
    ∫ x in (0 : ℝ)..N, cexp (2 * Real.pi * Complex.I * k * x / N) =
      if k = 0 then ((N : ℝ) : ℂ) else 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [← integral_exp_two_pi_int_mul hN0 k]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp

/-- **The level-period Fourier coefficient** of the continued non-constant part. -/
theorem levelCoeff_EstarExt {s : ℂ} (hs : 1 / 2 < s.re) {n : ℤ} {y : ℝ} (hy : 0 < y) :
    (1 / ((N : ℝ) : ℂ)) * ∫ x in (0 : ℝ)..N, _root_.RHTower.deningerFourierKernel N n x *
      EstarExt N σ s (ofComplex (SelbergMaassMean.point x y)) = termCoeff N σ n s y := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
  have hpt : ∀ x : ℝ, EstarExt N σ s (ofComplex (SelbergMaassMean.point x y)) =
      ∑' m : ℤ, termCoeff N σ m s y * cexp (2 * Real.pi * Complex.I * m * x / N) := fun x => by
    have hp : 0 < (SelbergMaassMean.point x y).im := by simpa [SelbergMaassMean.point] using hy
    unfold EstarExt
    refine tsum_congr fun m => ?_
    rw [termX_eq, ofComplex_apply_of_im_pos hp]
    simp [SelbergMaassMean.point]
  set F : ℤ → ℝ → ℂ := fun m x => termCoeff N σ m s y *
    cexp (2 * Real.pi * Complex.I * (m - n : ℤ) * x / N)
  have hker : ∀ (m : ℤ) (x : ℝ), _root_.RHTower.deningerFourierKernel N n x *
      (termCoeff N σ m s y * cexp (2 * Real.pi * Complex.I * m * x / N)) = F m x := fun m x => by
    simp only [F, _root_.RHTower.deningerFourierKernel]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hFc : ∀ m, Continuous (F m) := fun m => continuous_const.mul
    (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).div_const _))
  have hnormF : ∀ m x, ‖F m x‖ = ‖termCoeff N σ m s y‖ := fun m x => by
    simp only [F, norm_mul]
    rw [show 2 * Real.pi * Complex.I * ((m - n : ℤ) : ℂ) * x / N =
      ((2 * Real.pi * (m - n : ℤ) * x / N : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hsum := summable_norm_termCoeff N σ hs hy
  have hint : ∫ x in (0 : ℝ)..N, ∑' m : ℤ, F m x = ∑' m : ℤ, ∫ x in (0 : ℝ)..N, F m x := by
    rw [intervalIntegral.integral_of_le hN0.le]
    simp_rw [intervalIntegral.integral_of_le hN0.le]
    refine (integral_tsum_of_summable_integral_norm (fun m => (hFc m).integrableOn_Ioc) ?_).symm
    refine (Summable.mul_right (N : ℝ) hsum).congr fun m => ?_
    simp_rw [hnormF]
    rw [MeasureTheory.integral_const, smul_eq_mul, Measure.real,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal hN0.le, mul_comm]
  have hval : ∀ m, ∫ x in (0 : ℝ)..N, F m x = if m = n then termCoeff N σ m s y * N else 0 :=
    fun m => by
      simp only [F]
      rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_int_mul_nat]
      split_ifs with h1 h2 h2
      · push_cast; ring
      · exact absurd (sub_eq_zero.1 h1) h2
      · exact absurd (sub_eq_zero.2 h2) h1
      · ring
  simp_rw [hpt]
  rw [show (fun x : ℝ => _root_.RHTower.deningerFourierKernel N n x *
      ∑' m : ℤ, termCoeff N σ m s y * cexp (2 * Real.pi * Complex.I * m * x / N)) =
      fun x => ∑' m : ℤ, F m x from funext fun x => by
    rw [← tsum_mul_left]; exact tsum_congr fun m => hker m x]
  rw [hint, tsum_congr hval, tsum_ite_eq]
  field_simp
  push_cast
  ring

/-- The horizontal slices of the continued non-constant part are continuous. -/
theorem continuous_EstarExt_slice {s : ℂ} (hs : 1 / 2 < s.re) {y : ℝ} (hy : 0 < y) :
    Continuous fun x : ℝ => EstarExt N σ s (ofComplex (SelbergMaassMean.point x y)) := by
  have hpt : ∀ x : ℝ, EstarExt N σ s (ofComplex (SelbergMaassMean.point x y)) =
      ∑' m : ℤ, termCoeff N σ m s y * cexp (2 * Real.pi * Complex.I * m * x / N) := fun x => by
    have hp : 0 < (SelbergMaassMean.point x y).im := by simpa [SelbergMaassMean.point] using hy
    unfold EstarExt
    refine tsum_congr fun m => ?_
    rw [termX_eq, ofComplex_apply_of_im_pos hp]
    simp [SelbergMaassMean.point]
  simp_rw [hpt]
  refine continuous_tsum (fun m => continuous_const.mul (Complex.continuous_exp.comp
    ((continuous_const.mul Complex.continuous_ofReal).div_const _)))
    (summable_norm_termCoeff N σ hs hy) fun m x => le_of_eq ?_
  rw [norm_mul, show 2 * Real.pi * Complex.I * (m : ℂ) * x / N =
    ((2 * Real.pi * m * x / N : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **Whittaker form of the Bessel kernel**:
`W_s(n, y/L) = 2π^s Γ(s)⁻¹ |n|^{s−½} L^{−½} √y K_{s−½}(2π|n|y/L)`. -/
theorem kerBessel_div_eq_whittaker {L y : ℝ} (hL : 0 < L) (hy : 0 < y) (s : ℂ) {n : ℤ}
    (hn : n ≠ 0) :
    kerBessel (y / L) s n = 2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹ *
      (((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (((L : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)))) *
        MaassWhittaker.whittakerW (2 * Real.pi * |(n : ℝ)| / L) (s - 1 / 2) y := by
  have ha : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hY : 0 < y / L := div_pos hy hL
  unfold kerBessel MaassWhittaker.whittakerW MaassWhittaker.besK
  have harg : 2 * Real.pi * (y / L) * |(n : ℝ)| = 2 * Real.pi * |(n : ℝ)| / L * y := by
    field_simp
  rw [harg]
  have hcp : ((y / L : ℝ) : ℂ) ^ s * (((|(n : ℝ)| / (y / L) : ℝ)) : ℂ) ^ (s - 1 / 2) =
      ((|(n : ℝ)| : ℝ) : ℂ) ^ (s - 1 / 2) * (((L : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) *
        ((Real.sqrt y : ℝ) : ℂ) := by
    have h1 : ((y / L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
    have h2 : (((|(n : ℝ)| / (y / L) : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (div_pos ha hY).ne'
    have h3 : ((|(n : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have h4 : ((L : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
      Complex.cpow_def_of_ne_zero h3, Complex.cpow_def_of_ne_zero h4,
      ← Complex.ofReal_log hY.le, ← Complex.ofReal_log (div_pos ha hY).le,
      ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hL.le,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos hy, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_add, ← Complex.exp_add, Real.log_div ha.ne' hY.ne',
      Real.log_div hy.ne' hL.ne']
    congr 1
    push_cast
    ring
  rw [show ((y / L : ℝ) : ℂ) ^ s * (2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) *
      (((|(n : ℝ)| / (y / L) : ℝ)) : ℂ) ^ (s - 1 / 2) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| / L * y)
          (s - 1 / 2) =
      (2 * (Real.pi : ℂ) ^ s * (Complex.Gamma s)⁻¹) * (((y / L : ℝ) : ℂ) ^ s *
        (((|(n : ℝ)| / (y / L) : ℝ)) : ℂ) ^ (s - 1 / 2)) *
        GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| / L * y)
          (s - 1 / 2) by ring, hcp]
  ring

end

end GaloisForLFunctions.RHTower.SelbergEisensteinStarCriticalLine
