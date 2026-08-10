/- C50: continuous Chebyshev source / finite-order divisor-current weld. -/
import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailSamplingAnomalyWeld
import GaloisForLFunctions.RHTower.MertensFirst
import Mathlib.NumberTheory.LSeries.SumCoeff

open Complex Filter MeasureTheory Set Finset Asymptotics ArithmeticFunction

namespace RHTower

noncomputable section

theorem vonMangoldt_partialSums_isBigO :
    (fun n : ℕ => ∑ k ∈ Icc 1 n, vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
  refine IsBigO.of_bound (Real.log 4 + 4) (Eventually.of_forall fun n => ?_)
  have hnon : 0 ≤ ∑ k ∈ Icc 1 n, vonMangoldt k :=
    Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
  calc
    ‖∑ k ∈ Icc 1 n, vonMangoldt k‖ = ∑ k ∈ Icc 1 n, vonMangoldt k := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    _ ≤ (Real.log 4 + 4) * n := Mertens.sum_vonMangoldt_Icc_le n
    _ = (Real.log 4 + 4) * ‖(n : ℝ) ^ (1 : ℝ)‖ := by
      rw [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

theorem vonMangoldtLSeries_eq_mul_integral_criticalCumulative
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (vonMangoldt n : ℂ)) s =
      s * ∫ t in Ioi (1 : ℝ),
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1)) := by
  have hmain := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => vonMangoldt n) (r := 1) zero_le_one hs
    vonMangoldt_partialSums_isBigO (fun n => vonMangoldt_nonneg)
  rw [hmain]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  congr 1
  rw [criticalCumulative]
  have hzero : vonMangoldt 0 = 0 := by simp
  rw [show Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega]
  rw [sum_insert (by simp), hzero, zero_add]
  push_cast
  rfl

theorem measurable_criticalCumulative_vonMangoldt :
    Measurable (criticalCumulative (fun n => vonMangoldt n)) := by
  let C : ℕ → ℝ := fun m => ∑ k ∈ Finset.Icc 0 m, vonMangoldt k
  have hC : Measurable C := measurable_of_countable C
  change Measurable (fun t : ℝ => C ⌊t⌋₊)
  exact hC.comp measurable_id.nat_floor

theorem integrableOn_criticalCumulative_mul_cpow
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
        (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  let C : ℝ := Real.log 4 + 4
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
    rw [Complex.neg_re]
    linarith
  have hcoeffMeas : Measurable (fun t : ℝ =>
      ((criticalCumulative (fun n => vonMangoldt n) t / t : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      (measurable_criticalCumulative_vonMangoldt.div measurable_id)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi (1 : ℝ)),
      ‖((criticalCumulative (fun n => vonMangoldt n) t / t : ℝ) : ℂ)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le ht0.le
    have hcum0 : 0 ≤ criticalCumulative (fun n => vonMangoldt n) t :=
      Finset.sum_nonneg fun _ _ => vonMangoldt_nonneg
    have hsum : criticalCumulative (fun n => vonMangoldt n) t ≤ C * ⌊t⌋₊ := by
      rw [criticalCumulative]
      have hzero : vonMangoldt 0 = 0 := by simp
      rw [show Finset.Icc 0 ⌊t⌋₊ = insert 0 (Finset.Icc 1 ⌊t⌋₊) by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega]
      rw [sum_insert (by simp), hzero, zero_add]
      exact Mertens.sum_vonMangoldt_Icc_le ⌊t⌋₊
    have hcum : criticalCumulative (fun n => vonMangoldt n) t ≤ C * t := by
      exact hsum.trans (mul_le_mul_of_nonneg_left hfloor hC0)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hcum0 ht0.le)]
    exact (div_le_iff₀ ht0).mpr (by simpa [C] using hcum)
  have hratio := hpow.bdd_mul hcoeffMeas.aestronglyMeasurable hbound
  have hratioOn : IntegrableOn (fun t : ℝ =>
      ((criticalCumulative (fun n => vonMangoldt n) t / t : ℝ) : ℂ) *
        (t : ℂ) ^ (-s)) (Ioi 1) := hratio
  refine hratioOn.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
  have hpowShift : (t : ℂ) ^ (-(s + 1)) = (t : ℂ)⁻¹ * (t : ℂ) ^ (-s) := by
    rw [show (-(s + 1) : ℂ) = (-1) + (-s) by ring,
      Complex.cpow_add _ _ htne, Complex.cpow_neg_one]
  dsimp only
  rw [hpowShift]
  push_cast
  field_simp

theorem integrableOn_linear_mul_cpow
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hpow : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) := by
    refine integrableOn_Ioi_cpow_of_lt ?_ one_pos
    rw [Complex.neg_re]
    linarith
  refine hpow.congr_fun ?_ measurableSet_Ioi
  intro t ht
  have ht0 : (0 : ℝ) < t := lt_trans one_pos ht
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
  dsimp only
  rw [show (-s : ℂ) = 1 + (-(s + 1)) by ring,
    Complex.cpow_add _ _ htne, Complex.cpow_one]

theorem integral_Ioi_one_linear_mul_cpow
    {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1))) =
      1 / (s - 1) := by
  have hpoint : ∀ t ∈ Ioi (1 : ℝ),
      (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
    intro t ht
    have htne : ((t : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans one_pos ht))
    rw [show (-s : ℂ) = 1 + (-(s + 1)) by ring,
      Complex.cpow_add _ _ htne, Complex.cpow_one]
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint]
  rw [integral_Ioi_cpow_of_lt (by rw [Complex.neg_re]; linarith) one_pos,
    Complex.ofReal_one, Complex.one_cpow,
    show (-s + 1 : ℂ) = -(s - 1) by ring]
  field_simp

/-- Mellin transform of continuous Chebyshev error `psi(x)-x` on `x>1`. -/
def criticalContinuousChebyshevErrorMellinRay (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ),
    (criticalMellinError (fun n => vonMangoldt n) t : ℂ) *
      (t : ℂ) ^ (-(s + 1))

theorem integrableOn_criticalContinuousChebyshevErrorMellinRay
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (criticalMellinError (fun n => vonMangoldt n) t : ℂ) *
        (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hcum := integrableOn_criticalCumulative_mul_cpow hs
  have hlin := integrableOn_linear_mul_cpow hs
  have hsub := hcum.sub hlin
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro t _ht
  change
    (criticalCumulative (fun n => vonMangoldt n) t : ℂ) * (t : ℂ) ^ (-(s + 1)) -
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ((criticalCumulative (fun n => vonMangoldt n) t - t : ℝ) : ℂ) *
        (t : ℂ) ^ (-(s + 1))
  push_cast
  ring

theorem criticalContinuousChebyshevErrorMellinRay_eq_LSeries
    {s : ℂ} (hs : 1 < s.re) :
    criticalContinuousChebyshevErrorMellinRay s =
      LSeries (fun n => (vonMangoldt n : ℂ)) s / s - 1 / (s - 1) := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hcum := integrableOn_criticalCumulative_mul_cpow hs
  have hlin := integrableOn_linear_mul_cpow hs
  have hsplit : ∀ t ∈ Ioi (1 : ℝ),
      (criticalMellinError (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1)) =
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
            (t : ℂ) ^ (-(s + 1)) -
          (t : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    intro t _ht
    rw [criticalMellinError]
    push_cast
    ring
  rw [criticalContinuousChebyshevErrorMellinRay,
    setIntegral_congr_fun measurableSet_Ioi hsplit, integral_sub hcum hlin,
    integral_Ioi_one_linear_mul_cpow hs]
  have habel := vonMangoldtLSeries_eq_mul_integral_criticalCumulative hs
  have hI :
      (∫ t in Ioi (1 : ℝ),
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1))) =
        LSeries (fun n => (vonMangoldt n : ℂ)) s / s := by
    rw [habel]
    field_simp
  rw [hI]

/-- **C50 divisor-current weld in Mellin coordinates.**  Continuous Chebyshev error carries only
the finite-order logarithmic divisor current of `G(s)=(s-1)ζ(s)`, plus universal constant `1`. -/
theorem criticalContinuousChebyshevErrorMellinRay_eq_logDeriv
    {s : ℂ} (hs : 1 < s.re) :
    criticalContinuousChebyshevErrorMellinRay s =
      -(logDeriv zetaResidueUnit s + 1) / s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (lt_trans zero_lt_one hs)
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl 1 hs
  have hG : zetaResidueUnit s ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [criticalContinuousChebyshevErrorMellinRay_eq_LSeries hs,
    ← infinitePrimeFlux_eq_vonMangoldtLSeries hs, infinitePrimeFlux,
    logDeriv_zeta_eq hs1 hG]
  field_simp
  ring

/-- Laplace transform of square-root-normalized continuous Chebyshev error in logarithmic time. -/
def criticalNormalizedChebyshevErrorLaplace (z : ℂ) : ℂ :=
  ∫ h in Ioi (0 : ℝ),
    Complex.exp (-(z * (h : ℂ))) *
      (criticalMellinNormalizedChebyshevError h : ℂ)

theorem exp_smul_chebyshevMellin_eq_laplaceNormalized (z : ℂ) (h : ℝ) :
    (Real.exp h) •
        ((criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
          ((Real.exp h : ℝ) : ℂ) ^ (-((z + 1 / 2) + 1))) =
      Complex.exp (-(z * (h : ℂ))) *
        (criticalMellinNormalizedChebyshevError h : ℂ) := by
  have hexp0 : (0 : ℝ) < Real.exp h := Real.exp_pos h
  have hexpne : ((Real.exp h : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hexp0)
  have hlog : Complex.log ((Real.exp h : ℝ) : ℂ) = (h : ℂ) := by
    rw [← Complex.ofReal_log hexp0.le, Real.log_exp]
  have hsqrt : Real.sqrt (Real.exp h) = Real.exp (h / 2) := by
    rw [← Real.exp_half]
  rw [criticalMellinNormalizedChebyshevError, hsqrt, Complex.real_smul]
  rw [Complex.cpow_def_of_ne_zero hexpne, hlog]
  push_cast
  rw [show
    (criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) /
        Complex.exp ((h : ℂ) / 2) =
      (criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
        (Complex.exp ((h : ℂ) / 2))⁻¹ by
    exact div_eq_mul_inv _ _]
  rw [← Complex.exp_neg]
  have hexpEq :
      Complex.exp (h : ℂ) *
          Complex.exp ((h : ℂ) * (-((z + 1 / 2) + 1))) =
        Complex.exp (-(z * (h : ℂ))) * Complex.exp (-((h : ℂ) / 2)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    Complex.exp (h : ℂ) *
          ((criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
            Complex.exp ((h : ℂ) * (-((z + 1 / 2) + 1)))) =
        (criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
          (Complex.exp (h : ℂ) *
            Complex.exp ((h : ℂ) * (-((z + 1 / 2) + 1)))) := by ring
    _ = (criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
          (Complex.exp (-(z * (h : ℂ))) * Complex.exp (-((h : ℂ) / 2))) := by
      rw [hexpEq]
    _ = Complex.exp (-(z * (h : ℂ))) *
          ((criticalMellinError (fun n => vonMangoldt n) (Real.exp h) : ℂ) *
            Complex.exp (-((h : ℂ) / 2))) := by ring

/-- Exact logarithmic-coordinate conversion from the Route T source to its Mellin ray. -/
theorem criticalNormalizedChebyshevErrorLaplace_eq_mellinRay (z : ℂ) :
    criticalNormalizedChebyshevErrorLaplace z =
      criticalContinuousChebyshevErrorMellinRay (z + 1 / 2) := by
  let F : ℝ → ℂ := fun x =>
    (criticalMellinError (fun n => vonMangoldt n) x : ℂ) *
      (x : ℂ) ^ (-((z + 1 / 2) + 1))
  let g : ℝ → ℂ := Set.indicator (Ioi (1 : ℝ)) F
  have hcv := integral_Ioi_eq_integral_exp_smul g
  have hsub : Set.Ioi (0 : ℝ) ∩ Set.Ioi 1 = Set.Ioi 1 := by
    rw [Set.inter_eq_right]
    exact fun t ht => lt_trans one_pos (Set.mem_Ioi.mp ht)
  have hleft : (∫ x in Ioi (0 : ℝ), g x) =
      ∫ x in Ioi (1 : ℝ), F x := by
    simp only [g]
    rw [setIntegral_indicator measurableSet_Ioi, hsub]
  have hpoint : ∀ h : ℝ,
      Real.exp h • g (Real.exp h) =
        Set.indicator (Ioi (0 : ℝ))
          (fun h : ℝ => Complex.exp (-(z * (h : ℂ))) *
            (criticalMellinNormalizedChebyshevError h : ℂ)) h := by
    intro h
    by_cases hh : h ∈ Ioi (0 : ℝ)
    · have hexp : Real.exp h ∈ Ioi (1 : ℝ) := by
        exact Real.one_lt_exp_iff.mpr hh
      simp only [g]
      rw [Set.indicator_of_mem hexp, Set.indicator_of_mem hh]
      exact exp_smul_chebyshevMellin_eq_laplaceNormalized z h
    · have hnonpos : h ≤ 0 := le_of_not_gt hh
      have hexp : Real.exp h ∉ Ioi (1 : ℝ) := by
        intro hbad
        have := (Real.exp_le_one_iff.mpr hnonpos)
        exact (not_lt_of_ge this) hbad
      simp only [g]
      rw [Set.indicator_of_notMem hexp, Set.indicator_of_notMem hh, smul_zero]
  rw [criticalNormalizedChebyshevErrorLaplace,
    criticalContinuousChebyshevErrorMellinRay]
  rw [← hleft, hcv]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_indicator measurableSet_Ioi]

/-- **C50 logarithmic Route T weld.**  In its honest half-plane, normalized continuous Chebyshev
error is exactly finite-order divisor propagation; sampling and gauge residues have disappeared. -/
theorem criticalNormalizedChebyshevErrorLaplace_eq_logDeriv
    {z : ℂ} (hz : 1 / 2 < z.re) :
    criticalNormalizedChebyshevErrorLaplace z =
      -(logDeriv zetaResidueUnit (z + 1 / 2) + 1) / (z + 1 / 2) := by
  rw [criticalNormalizedChebyshevErrorLaplace_eq_mellinRay]
  apply criticalContinuousChebyshevErrorMellinRay_eq_logDeriv
  rw [Complex.add_re]
  norm_num
  linarith

end

end RHTower
