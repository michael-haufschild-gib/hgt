import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicMellinAnalytic
import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevPacket
import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevMellin
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform comparison of discrete and continuous first-mode packets

Linear vanishing of the cyclotomic kernel makes each integer-cell error
`O(1/x)`. Summing complete cells and bounding the two endpoint pieces gives
`‖C(x)-B(x)‖ ≤ 80π` for every real horizon `x ≥ 2`.
-/

noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- Weighted kernel in the continuous Chebyshev packet. -/
def firstCyclotomicWeightedKernel (x t : ℝ) : ℂ :=
  ((t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * firstCyclotomicKernel (t / x)

private def firstCyclotomicWeightedKernelDerivative (x t : ℝ) : ℂ :=
  (((-3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * firstCyclotomicKernel (t / x) -
    ((t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (2 * Real.pi) * (t / x)) *
      (Complex.I * (2 * Real.pi) / x)

private theorem hasDerivAt_firstCyclotomicWeightedKernel (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (firstCyclotomicWeightedKernel x)
      (firstCyclotomicWeightedKernelDerivative x t) t := by
  have hp := (Real.hasDerivAt_rpow_const (p := (-3 / 2 : ℝ)) (Or.inl ht.ne')).ofReal_comp
  rw [show (-3 / 2 : ℝ) - 1 = -5 / 2 by norm_num] at hp
  have he : HasDerivAt (fun u : ℝ => Complex.exp (Complex.I * (2 * Real.pi) * (u / x)))
      (Complex.exp (Complex.I * (2 * Real.pi) * (t / x)) *
        (Complex.I * (2 * Real.pi) / x)) t := by
    convert! ((((hasDerivAt_id t).div_const x).ofReal_comp).const_mul
      (Complex.I * (2 * Real.pi))).cexp using 1
    · funext u
      simp only [id_eq, Complex.ofReal_div]
    · simp only [id_eq, Complex.ofReal_div, Complex.ofReal_one, mul_one_div]
  unfold firstCyclotomicWeightedKernel firstCyclotomicKernel
  convert! hp.mul ((hasDerivAt_const t (1 : ℂ)).sub he) using 1
  · funext u
    simp only [Pi.mul_apply, Pi.sub_apply, Complex.ofReal_div]
  · dsimp only [firstCyclotomicWeightedKernelDerivative, firstCyclotomicKernel, Pi.sub_apply]
    push_cast
    ring

private theorem norm_firstCyclotomicWeightedKernelDerivative_le {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) :
    ‖firstCyclotomicWeightedKernelDerivative x t‖ ≤
      5 * Real.pi / x * t ^ (-3 / 2 : ℝ) := by
  have hr3 : 0 ≤ t ^ (-3 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hr5 : 0 ≤ t ^ (-5 / 2 : ℝ) := Real.rpow_nonneg ht.le _
  have hkernel := norm_firstCyclotomicKernel_le (t / x)
  rw [abs_of_pos (div_pos ht hx)] at hkernel
  have hphase : ‖Complex.exp (Complex.I * (2 * Real.pi) * (t / x))‖ = 1 := by
    simp [Complex.norm_exp]
  have hcoeff : ‖Complex.I * (2 * Real.pi) / (x : ℂ)‖ = 2 * Real.pi / x := by
    simp [abs_of_pos Real.pi_pos, abs_of_pos hx]
  have hpow : t ^ (-5 / 2 : ℝ) * t = t ^ (-3 / 2 : ℝ) := by
    rw [← Real.rpow_add_one ht.ne']
    norm_num
  unfold firstCyclotomicWeightedKernelDerivative
  calc
    _ ≤ ‖(((-3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ) : ℝ) : ℂ) * firstCyclotomicKernel (t / x)‖ +
        ‖((t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) * Complex.exp (Complex.I * (2 * Real.pi) * (t / x)) *
          (Complex.I * (2 * Real.pi) / x)‖ := norm_sub_le _ _
    _ = (3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ) * ‖firstCyclotomicKernel (t / x)‖ +
        t ^ (-3 / 2 : ℝ) * (2 * Real.pi / x) := by
      rw [norm_mul, norm_mul, norm_mul, hphase, hcoeff, mul_one]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr3,
        abs_of_nonneg hr5]
      norm_num
    _ ≤ (3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ) * (2 * Real.pi * (t / x)) +
        t ^ (-3 / 2 : ℝ) * (2 * Real.pi / x) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hkernel
        (by positivity : 0 ≤ (3 / 2 : ℝ) * t ^ (-5 / 2 : ℝ))) le_rfl
    _ = _ := by
      calc
        _ = (3 * Real.pi / x) * (t ^ (-5 / 2 : ℝ) * t) +
            (2 * Real.pi / x) * t ^ (-3 / 2 : ℝ) := by ring
        _ = _ := by rw [hpow]; ring

/-- One cell has uniformly small weighted-kernel variation. -/
theorem norm_firstCyclotomicWeightedKernel_sub_left_le {x n t : ℝ}
    (hx : 0 < x) (hn : 1 ≤ n) (ht : t ∈ Icc n (n + 1)) :
    ‖firstCyclotomicWeightedKernel x t - firstCyclotomicWeightedKernel x n‖ ≤
      5 * Real.pi / (x * n) := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hbound (u : ℝ) (hu : u ∈ Icc n (n + 1)) :
      ‖firstCyclotomicWeightedKernelDerivative x u‖ ≤ 5 * Real.pi / (x * n) := by
    have hu0 : 0 < u := hn0.trans_le hu.1
    have hu1 : 1 ≤ u := hn.trans hu.1
    have hpow : u ^ (-3 / 2 : ℝ) ≤ 1 / n := by
      calc
        _ ≤ u ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
        _ = 1 / u := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / n := div_le_div_of_nonneg_left zero_le_one hn0 hu.1
    calc
      _ ≤ 5 * Real.pi / x * u ^ (-3 / 2 : ℝ) :=
        norm_firstCyclotomicWeightedKernelDerivative_le hx hu0
      _ ≤ 5 * Real.pi / x * (1 / n) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by ring
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (hu : u ∈ Icc n (n + 1)) =>
      (hasDerivAt_firstCyclotomicWeightedKernel x (hn0.trans_le hu.1)).hasDerivWithinAt)
    hbound (convex_Icc n (n + 1)) (show n ∈ Icc n (n + 1) by constructor <;> linarith) ht
  have hdist : ‖t - n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith only [ht.2]
  exact hmv.trans (by nlinarith only [hdist, show 0 ≤ 5 * Real.pi / (x * n) by positivity])

#print axioms norm_firstCyclotomicWeightedKernel_sub_left_le


private theorem norm_firstCyclotomicWeightedKernel_le {x t : ℝ}
    (hx : 0 < x) (ht : 1 ≤ t) :
    ‖firstCyclotomicWeightedKernel x t‖ ≤ 2 * Real.pi / x := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hkernel := norm_firstCyclotomicKernel_le (t / x)
  rw [abs_of_pos (div_pos ht0 hx)] at hkernel
  have hpow : t ^ (-3 / 2 : ℝ) * t = t ^ (-1 / 2 : ℝ) := by
    rw [← Real.rpow_add_one ht0.ne']
    norm_num
  have hpow_le : t ^ (-1 / 2 : ℝ) ≤ 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  rw [firstCyclotomicWeightedKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
  calc
    _ ≤ t ^ (-3 / 2 : ℝ) * (2 * Real.pi * (t / x)) :=
      mul_le_mul_of_nonneg_left hkernel (Real.rpow_nonneg ht0.le _)
    _ = (2 * Real.pi / x) * t ^ (-1 / 2 : ℝ) := by
      calc
        _ = (2 * Real.pi / x) * (t ^ (-3 / 2 : ℝ) * t) := by ring
        _ = _ := by rw [hpow]
    _ ≤ 2 * Real.pi / x := by
      exact mul_le_of_le_one_right (by positivity) hpow_le

private theorem abs_chebyshev_error_nat_le (n : ℕ) :
    |Chebyshev.psi n - n| ≤ 6 * n := by
  have hu := _root_.RHTower.psi_nat_le_six_mul n
  have hl := _root_.RHTower.psi_nat_nonneg n
  have hn := Nat.cast_nonneg (α := ℝ) n
  exact abs_le.mpr ⟨by linarith only [hl, hn], by linarith only [hu, hn]⟩

private theorem chebyshev_error_on_cell {n : ℕ} {t : ℝ}
    (ht : t ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    Chebyshev.psi t - t = (Chebyshev.psi n - n) - (t - n) := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff (hn0.trans ht.1)).mpr ht
  rw [Chebyshev.psi_eq_psi_coe_floor t, hf]
  ring

/-- The weighted error changes by at most `32π/x` inside one integer cell. -/
theorem norm_chebyshev_weighted_cell_sub_left_le {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : t ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    ‖((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t -
      ((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n‖ ≤
        32 * Real.pi / x := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnr
  have hdiff : ‖((Chebyshev.psi t - t : ℝ) : ℂ) -
      ((Chebyshev.psi n - n : ℝ) : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      chebyshev_error_on_cell ht]
    rw [show (Chebyshev.psi n - n) - (t - n) - (Chebyshev.psi n - n) = -(t - n) by ring,
      abs_neg, abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith only [ht.2]
  have hleft : ‖((Chebyshev.psi n - n : ℝ) : ℂ)‖ ≤ 6 * n := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_chebyshev_error_nat_le n
  have hvariation := norm_firstCyclotomicWeightedKernel_sub_left_le hx hnr ⟨ht.1, ht.2.le⟩
  have hkernel := norm_firstCyclotomicWeightedKernel_le hx (hnr.trans ht.1)
  have hsplit : ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t -
      ((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n =
      (((Chebyshev.psi t - t : ℝ) : ℂ) - ((Chebyshev.psi n - n : ℝ) : ℂ)) *
        firstCyclotomicWeightedKernel x t +
      ((Chebyshev.psi n - n : ℝ) : ℂ) *
        (firstCyclotomicWeightedKernel x t - firstCyclotomicWeightedKernel x n) := by ring
  rw [hsplit]
  calc
    _ ≤ ‖(((Chebyshev.psi t - t : ℝ) : ℂ) - ((Chebyshev.psi n - n : ℝ) : ℂ)) *
        firstCyclotomicWeightedKernel x t‖ +
        ‖((Chebyshev.psi n - n : ℝ) : ℂ) *
          (firstCyclotomicWeightedKernel x t - firstCyclotomicWeightedKernel x n)‖ := norm_add_le _ _
    _ ≤ 1 * (2 * Real.pi / x) + (6 * n) * (5 * Real.pi / (x * n)) := by
      rw [norm_mul, norm_mul]
      exact add_le_add (mul_le_mul hdiff hkernel (norm_nonneg _) (by norm_num))
        (mul_le_mul hleft hvariation (norm_nonneg _) (by positivity))
    _ = _ := by field_simp [hx.ne', hn0.ne']; ring

#print axioms norm_chebyshev_weighted_cell_sub_left_le


private theorem rpow_neg_three_halves_eq {t : ℝ} (ht : 0 < t) :
    t ^ (-3 / 2 : ℝ) = 1 / (t * Real.sqrt t) := by
  rw [show (-3 / 2 : ℝ) = -1 - 1 / 2 by norm_num,
    Real.rpow_sub ht, Real.rpow_neg_one, ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The denominator shift and phase shift each cost at most `12π/x`. -/
theorem norm_chebyshev_weighted_left_sub_coeff_le {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n -
      (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ ≤
        24 * Real.pi / x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hsqrtC : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsqrt
  have hn1C : (n : ℂ) + 1 ≠ 0 := by
    exact_mod_cast (show (n : ℝ) + 1 ≠ 0 by positivity)
  have hcoeff : chebyshevConductorCoeff (n + 1) =
      (Chebyshev.psi n - n) / Real.sqrt (n : ℝ) / ((n : ℝ) + 1) := by
    rw [chebyshevConductorCoeff, chebyshevCesaroIncrement_eq (by omega),
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hsplit : ((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n -
      (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x) =
      (chebyshevConductorCoeff (n + 1) : ℂ) * ((1 / (n : ℝ) : ℝ) : ℂ) *
        firstCyclotomicKernel (n / x) +
      (chebyshevConductorCoeff (n + 1) : ℂ) *
        (firstCyclotomicKernel (n / x) - firstCyclotomicKernel ((n + 1 : ℕ) / x)) := by
    rw [firstCyclotomicWeightedKernel, rpow_neg_three_halves_eq hn0, hcoeff]
    push_cast
    field_simp [hnC, hsqrtC, hn1C]
    ring
  have hcoefnorm := norm_chebyshevConductorCoeff_le_six (j := n + 1) (by omega)
  have hkernel := norm_firstCyclotomicKernel_le ((n : ℝ) / x)
  rw [abs_of_pos (div_pos hn0 hx)] at hkernel
  have hdelta : ‖firstCyclotomicKernel ((n : ℝ) / x) -
      firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ ≤ 2 * Real.pi / x := by
    have h := norm_firstCyclotomicKernel_sub_le ((n : ℝ) / x) (((n + 1 : ℕ) : ℝ) / x)
    rw [Nat.cast_add, Nat.cast_one,
      show (n : ℝ) / x - ((n : ℝ) + 1) / x = -(1 / x) by ring,
      abs_neg, abs_of_pos (one_div_pos.mpr hx), mul_one_div] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  rw [hsplit]
  calc
    _ ≤ ‖(chebyshevConductorCoeff (n + 1) : ℂ) * ((1 / (n : ℝ) : ℝ) : ℂ) *
        firstCyclotomicKernel (n / x)‖ +
        ‖(chebyshevConductorCoeff (n + 1) : ℂ) *
          (firstCyclotomicKernel (n / x) - firstCyclotomicKernel ((n + 1 : ℕ) / x))‖ := norm_add_le _ _
    _ ≤ 6 * (1 / (n : ℝ)) * (2 * Real.pi * ((n : ℝ) / x)) +
        6 * (2 * Real.pi / x) := by
      have hinvnorm : ‖((1 / (n : ℝ) : ℝ) : ℂ)‖ = 1 / (n : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hn0)]
      rw [norm_mul, norm_mul, norm_mul, hinvnorm]
      exact add_le_add
        (mul_le_mul (mul_le_mul_of_nonneg_right hcoefnorm (by positivity)) hkernel
          (norm_nonneg _) (by positivity))
        (mul_le_mul hcoefnorm hdelta (norm_nonneg _) (by norm_num))
    _ = _ := by field_simp [hx.ne', hn0.ne']; ring

/-- Each integer cell pays its actual right-endpoint conductor coefficient with `56π/x`. -/
theorem norm_chebyshev_weighted_cell_sub_coeff_le {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Ico (n : ℝ) ((n : ℝ) + 1)) :
    ‖((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t -
      (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ ≤
        56 * Real.pi / x := by
  calc
    _ ≤ ‖((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t -
        ((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n‖ +
        ‖((Chebyshev.psi n - n : ℝ) : ℂ) * firstCyclotomicWeightedKernel x n -
          (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 32 * Real.pi / x + 24 * Real.pi / x :=
      add_le_add (norm_chebyshev_weighted_cell_sub_left_le hx (by omega) ht)
        (norm_chebyshev_weighted_left_sub_coeff_le hx hn)
    _ = _ := by ring

#print axioms norm_chebyshev_weighted_cell_sub_coeff_le


private theorem intervalIntegrable_chebyshevWeightedKernel (x : ℝ) {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t)
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hc : ContinuousOn (firstCyclotomicWeightedKernel x) (Icc a b) := by
    intro t ht
    exact (hasDerivAt_firstCyclotomicWeightedKernel x
      (lt_of_lt_of_le zero_lt_one (ha.trans ht.1))).continuousAt.continuousWithinAt
  have hstep := integrableOn_mul_sum_Icc (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
    (m := 0) (show 0 ≤ a by linarith only [ha]) hc.integrableOn_Icc
  have hlin : MeasureTheory.IntegrableOn
      (fun t : ℝ => (t : ℂ) * firstCyclotomicWeightedKernel x t) (Icc a b) :=
    (Complex.continuous_ofReal.continuousOn.mul hc).integrableOn_Icc
  refine (hstep.sub hlin).congr_fun ?_ measurableSet_Icc
  intro t _
  dsimp only [Pi.sub_apply]
  rw [Chebyshev.psi_eq_sum_Icc]
  push_cast
  ring

/-- Integrated cell error retains the same `56π/x` bound. -/
theorem norm_chebyshev_weighted_cell_integral_sub_coeff_le {x : ℝ} (hx : 0 < x)
    {n : ℕ} (hn : 2 ≤ n) :
    ‖(∫ t in (n : ℝ)..((n : ℝ) + 1),
        ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t) -
      (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ ≤
        56 * Real.pi / x := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hi := intervalIntegrable_chebyshevWeightedKernel x hnr (by linarith : (n : ℝ) ≤ n + 1)
  have heq : (∫ t in (n : ℝ)..((n : ℝ) + 1),
      ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t -
        (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x)) =
      (∫ t in (n : ℝ)..((n : ℝ) + 1),
        ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t) -
      (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const]
    simp
  rw [← heq]
  have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ (n : ℝ) + 1 := by
    rw [MeasureTheory.ae_iff]
    simp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae (C := 56 * Real.pi / x) (by
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le (by linarith : (n : ℝ) ≤ n + 1)] at hmem
    exact norm_chebyshev_weighted_cell_sub_coeff_le hx hn
      ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩)
  simpa using h

#print axioms norm_chebyshev_weighted_cell_integral_sub_coeff_le


private theorem abs_chebyshev_error_le {t : ℝ} (ht : 0 ≤ t) :
    |Chebyshev.psi t - t| ≤ 6 * t := by
  have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht
  have hu := _root_.RHTower.psi_nat_le_six_mul ⌊t⌋₊
  have hl := _root_.RHTower.psi_nat_nonneg ⌊t⌋₊
  rw [Chebyshev.psi_eq_psi_coe_floor t]
  exact abs_le.mpr ⟨by linarith only [hl, ht], by linarith only [hu, hfloor, ht]⟩

/-- A partial cell inside the horizon costs at most `12π`. -/
theorem norm_integral_chebyshevWeightedKernel_short_le {x a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) (hbx : b ≤ x) (hlen : b - a ≤ 1) :
    ‖∫ t in a..b, ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t‖ ≤
      12 * Real.pi := by
  have hx : 0 < x := lt_of_lt_of_le zero_lt_one ((ha.trans hab).trans hbx)
  have hbound (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t‖ ≤
        12 * Real.pi := by
    rw [uIoc_of_le hab] at ht
    have ht1 : 1 ≤ t := ha.trans ht.1.le
    have ht0 : 0 ≤ t := zero_le_one.trans ht1
    have herror : ‖((Chebyshev.psi t - t : ℝ) : ℂ)‖ ≤ 6 * t := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_chebyshev_error_le ht0
    rw [norm_mul]
    calc
      _ ≤ (6 * t) * (2 * Real.pi / x) :=
        mul_le_mul herror (norm_firstCyclotomicWeightedKernel_le hx ht1)
          (norm_nonneg _) (by positivity)
      _ = 12 * Real.pi * (t / x) := by ring
      _ ≤ 12 * Real.pi :=
        mul_le_of_le_one_right (by positivity) ((div_le_one hx).mpr (ht.2.trans hbx))
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at h
  exact h.trans (mul_le_of_le_one_right (by positivity) hlen)

#print axioms norm_integral_chebyshevWeightedKernel_short_le

private theorem chebyshevFirstCyclotomicPacket_eq_cell_sum (x : ℝ) :
    chebyshevFirstCyclotomicPacket x =
      ∑ n ∈ Finset.Ico 2 ⌊x⌋₊,
        (chebyshevConductorCoeff (n + 1) : ℂ) * firstCyclotomicKernel ((n + 1 : ℕ) / x) := by
  classical
  rw [chebyshevFirstCyclotomicPacket]
  have hlow : (∑ j ∈ Finset.Icc 1 ⌊x⌋₊,
      (chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / x)) =
      ∑ j ∈ Finset.Icc 3 ⌊x⌋₊,
        (chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / x) := by
    symm
    apply Finset.sum_subset
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj hjnot
      have hj2 : j ≤ 2 := by
        simp only [Finset.mem_Icc] at hj hjnot
        omega
      rw [chebyshevConductorCoeff, chebyshevCesaroIncrement_zero_of_le_two hj2, zero_div,
        Complex.ofReal_zero, zero_mul]
  rw [hlow]
  symm
  apply Finset.sum_bij (fun n _ => n + 1)
  · intro n hn
    simp only [Finset.mem_Icc, Finset.mem_Ico] at hn ⊢
    omega
  · intro n hn m hm hnm
    omega
  · intro j hj
    refine ⟨j - 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc, Finset.mem_Ico] at hj ⊢
      omega
    · have := (Finset.mem_Icc.mp hj).1
      omega
  · intro n hn
    rfl

private theorem chebyshevFirstCyclotomicContinuous_eq_weighted_integral {x : ℝ} (hx : 1 ≤ x) :
    chebyshevFirstCyclotomicContinuous x =
      ∫ t in (1 : ℝ)..x,
        ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t := by
  rw [chebyshevFirstCyclotomicContinuous_eq_integral hx]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hx] at ht
  have ht0 : 0 ≤ t := zero_le_one.trans ht.1
  have herr : _root_.RHTower.criticalMellinError
      (fun n => ArithmeticFunction.vonMangoldt n) t = Chebyshev.psi t - t := by
    rw [_root_.RHTower.criticalMellinError, _root_.RHTower.criticalCumulative,
      Chebyshev.psi_eq_sum_Icc]
  have hpow : (t : ℂ) ^ (-3 / 2 : ℂ) = ((t ^ (-3 / 2 : ℝ) : ℝ) : ℂ) := by
    convert! (Complex.ofReal_cpow ht0 (-3 / 2 : ℝ)).symm using 1; push_cast; rfl
  dsimp only
  rw [herr, hpow, firstCyclotomicWeightedKernel]
  ring

/-- Summing the cell errors gives a horizon-independent comparison with the actual packet. -/
theorem norm_chebyshevFirstCyclotomicContinuous_sub_packet_le {x : ℝ} (hx : 2 ≤ x) :
    ‖chebyshevFirstCyclotomicContinuous x - chebyshevFirstCyclotomicPacket x‖ ≤
      80 * Real.pi := by
  classical
  let Q := ⌊x⌋₊
  let f : ℝ → ℂ := fun t =>
    ((Chebyshev.psi t - t : ℝ) : ℂ) * firstCyclotomicWeightedKernel x t
  have hx0 : 0 < x := by linarith only [hx]
  have hQ : 2 ≤ Q := (Nat.le_floor_iff hx0.le).mpr (by simpa using hx)
  have hQr : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQx : (Q : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxQ : x - (Q : ℝ) ≤ 1 := by linarith only [Nat.lt_floor_add_one x]
  have hcells : (∑ n ∈ Finset.Ico 2 Q, ∫ t in (n : ℝ)..((n : ℝ) + 1), f t) =
      ∫ t in (2 : ℝ)..(Q : ℝ), f t := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun n : ℕ => (n : ℝ)) hQ
        (fun n hn => intervalIntegrable_chebyshevWeightedKernel x
          (by exact_mod_cast (show 1 ≤ n by have := hn.1; omega))
          (by norm_cast; omega))
  have hmiddle : ‖(∫ t in (2 : ℝ)..(Q : ℝ), f t) - chebyshevFirstCyclotomicPacket x‖ ≤
      56 * Real.pi := by
    rw [← hcells, chebyshevFirstCyclotomicPacket_eq_cell_sum, ← Finset.sum_sub_distrib]
    have hcard : (Finset.Ico 2 Q).card ≤ Q := by
      calc
        _ ≤ (Finset.range Q).card := Finset.card_le_card (by
          intro n hn
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2)
        _ = Q := Finset.card_range Q
    calc
      _ ≤ ∑ n ∈ Finset.Ico 2 Q,
          ‖(∫ t in (n : ℝ)..((n : ℝ) + 1), f t) -
            (chebyshevConductorCoeff (n + 1) : ℂ) *
              firstCyclotomicKernel ((n + 1 : ℕ) / x)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ico 2 Q, 56 * Real.pi / x :=
        Finset.sum_le_sum (fun n hn =>
          norm_chebyshev_weighted_cell_integral_sub_coeff_le hx0 (Finset.mem_Ico.mp hn).1)
      _ = ((Finset.Ico 2 Q).card : ℝ) * (56 * Real.pi / x) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (56 * Real.pi / x) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ ≤ 56 * Real.pi := by
        calc
          _ = 56 * Real.pi * ((Q : ℝ) / x) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) ((div_le_one hx0).mpr hQx)
  have hi12 := intervalIntegrable_chebyshevWeightedKernel x (a := 1) (b := 2)
    (by norm_num) (by norm_num)
  have hi2Q := intervalIntegrable_chebyshevWeightedKernel x (a := 2) (b := Q)
    (by norm_num) hQr
  have hiQx := intervalIntegrable_chebyshevWeightedKernel x (a := Q) (b := x)
    (by linarith only [hQr]) hQx
  have hsplit : chebyshevFirstCyclotomicContinuous x =
      (∫ t in (1 : ℝ)..2, f t) + (∫ t in (2 : ℝ)..(Q : ℝ), f t) +
        (∫ t in (Q : ℝ)..x, f t) := by
    rw [chebyshevFirstCyclotomicContinuous_eq_weighted_integral (by linarith only [hx]),
      intervalIntegral.integral_add_adjacent_intervals hi12 hi2Q,
      intervalIntegral.integral_add_adjacent_intervals (hi12.trans hi2Q) hiQx]
  have hfirst : ‖∫ t in (1 : ℝ)..2, f t‖ ≤ 12 * Real.pi :=
    norm_integral_chebyshevWeightedKernel_short_le (by norm_num) (by norm_num) hx (by norm_num)
  have hlast : ‖∫ t in (Q : ℝ)..x, f t‖ ≤ 12 * Real.pi :=
    norm_integral_chebyshevWeightedKernel_short_le (by linarith only [hQr]) hQx le_rfl hxQ
  rw [hsplit]
  calc
    _ = ‖(∫ t in (1 : ℝ)..2, f t) +
        ((∫ t in (2 : ℝ)..(Q : ℝ), f t) - chebyshevFirstCyclotomicPacket x) +
        (∫ t in (Q : ℝ)..x, f t)‖ := by congr 1; ring
    _ ≤ (‖∫ t in (1 : ℝ)..2, f t‖ +
        ‖(∫ t in (2 : ℝ)..(Q : ℝ), f t) - chebyshevFirstCyclotomicPacket x‖) +
        ‖∫ t in (Q : ℝ)..x, f t‖ := (norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 12 * Real.pi + 56 * Real.pi + 12 * Real.pi :=
      add_le_add (add_le_add hfirst hmiddle) hlast
    _ = _ := by ring

#print axioms norm_chebyshevFirstCyclotomicContinuous_sub_packet_le

end GaloisForLFunctions.CompletedArithmeticForms
