import GaloisForLFunctions.RHTower.SuzukiCanonicalKernelMellin
import GaloisForLFunctions.RHTower.SuzukiCanonicalShiftRatio
import GaloisForLFunctions.RHTower.SuzukiPacketCoefficientSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open ArithmeticFunction Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Inverse multiplicative dilation with Suzuki's additional `x⁻¹` weight. -/
def inverseMellinDilate (g : ℝ → ℂ) (a x : ℝ) : ℂ := g (a / x) / x

theorem measurable_positiveMellinConvolution
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (positiveMellinConvolution f g) := by
  rw [show positiveMellinConvolution f g = fun x : ℝ =>
      ∫ y, indicator (Ioi (0 : ℝ))
        (fun y => f y * g (x / y) / y) y by
    funext x
    rw [positiveMellinConvolution, integral_indicator measurableSet_Ioi]]
  have hjoint : Measurable fun p : ℝ × ℝ =>
      if p.2 ∈ Ioi (0 : ℝ) then f p.2 * g (p.1 / p.2) / p.2 else 0 := by
    apply Measurable.ite
    · exact measurableSet_Ioi.preimage measurable_snd
    · fun_prop
    · fun_prop
  have heq : (fun p : ℝ × ℝ =>
      indicator (Ioi (0 : ℝ))
        (fun y => f y * g (p.1 / y) / y) p.2) =
      fun p : ℝ × ℝ =>
        if p.2 ∈ Ioi (0 : ℝ) then f p.2 * g (p.1 / p.2) / p.2 else 0 := by
    funext p
    rw [Set.indicator_apply]
  have hmeas : Measurable fun p : ℝ × ℝ =>
      indicator (Ioi (0 : ℝ))
        (fun y => f y * g (p.1 / y) / y) p.2 := by
    rw [heq]
    exact hjoint
  exact (hmeas.stronglyMeasurable.integral_prod_right').measurable

theorem hasMellin_inverseMellinDilate
    {g : ℝ → ℂ} {s : ℂ} (hg : MellinConvergent g s) {a : ℝ} (ha : 0 < a) :
    HasMellin (inverseMellinDilate g a) (1 - s)
      ((a : ℂ) ^ (-s) * mellin g s) := by
  let q : ℝ → ℂ := fun u => g (a * u)
  have hq : MellinConvergent q s :=
    (MellinConvergent.comp_mul_left ha).2 hg
  have hinvR : MellinConvergent (fun x : ℝ => q (x ^ (-1 : ℝ))) (-s) := by
    refine (MellinConvergent.comp_rpow (f := q) (s := -s) (a := -1) (by norm_num)).2 ?_
    simpa using hq
  have hinv : MellinConvergent (fun x : ℝ => q x⁻¹) (-s) := by
    rw [MellinConvergent] at hinvR ⊢
    refine hinvR.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.rpow_neg_one]
  have hweighted : MellinConvergent
      (fun x : ℝ => (x : ℂ) ^ (-1 : ℂ) • q x⁻¹) (1 - s) := by
    refine (MellinConvergent.cpow_smul (f := fun x : ℝ => q x⁻¹)
      (s := 1 - s) (a := -1)).2 ?_
    convert hinv using 1
    ring
  constructor
  · rw [MellinConvergent] at hweighted ⊢
    refine hweighted.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [inverseMellinDilate, q, smul_eq_mul, Complex.cpow_neg_one,
      div_eq_mul_inv]
    ring
  · rw [show inverseMellinDilate g a = fun x : ℝ =>
        (x : ℂ) ^ (-1 : ℂ) • q x⁻¹ by
      funext x
      by_cases hx : x = 0
      · subst hx
        simp [inverseMellinDilate, q]
      · simp only [inverseMellinDilate, q, smul_eq_mul, Complex.cpow_neg_one]
        simp only [div_eq_mul_inv]
        ring,
      mellin_cpow_smul]
    rw [show 1 - s + -1 = -s by ring, mellin_comp_inv, neg_neg]
    change mellin (fun u : ℝ => g (a * u)) s = _
    rw [mellin_comp_mul_left g s ha]
    simp only [smul_eq_mul]

/-- Absolute convergence counterpart of the exact Suzuki coefficient L-series theorem. -/
theorem LSeriesSummable_suzukiShiftedCoefficient
    (omega : ℝ) {s : ℂ}
    (h1 : 1 < (s - (omega : ℂ)).re) (h2 : 1 < (s + (omega : ℂ)).re) :
    LSeriesSummable (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s := by
  have hminus : s + (-(omega : ℝ) : ℂ) = s - (omega : ℂ) := by ring
  have hplus : s + ((omega : ℝ) : ℂ) = s + (omega : ℂ) := rfl
  have hcoeZ : (fun n => (((ArithmeticFunction.zeta : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) n)) =
      fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ) := by
    funext n
    simp
  have hcoeM : (fun n => (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
      ArithmeticFunction ℂ) n)) =
      fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ) := by
    funext n
    simp
  have hsF : LSeriesSummable
      (fun n => dirichletShift (-(omega : ℝ) : ℂ)
        ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n) s := by
    rw [dirichletShift_LSeriesSummable_iff, hminus, hcoeZ]
    exact LSeriesSummable_zeta_iff.mpr h1
  have hsG : LSeriesSummable
      (fun n => dirichletShift ((omega : ℝ) : ℂ)
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) n) s := by
    rw [dirichletShift_LSeriesSummable_iff, hplus, hcoeM]
    exact LSeriesSummable_moebius_iff.mpr h2
  have hconv : (fun n => ((suzukiCoeffAF omega) n)) =
      LSeries.convolution
        (fun n => dirichletShift (-(omega : ℝ) : ℂ)
          ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n)
        (fun n => dirichletShift ((omega : ℝ) : ℂ)
          ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) n) := by
    funext n
    rw [suzukiCoeffAF_eq_convolution omega, ArithmeticFunction.mul_apply,
      LSeries.convolution_def]
  have hAF : LSeriesSummable (fun n => ((suzukiCoeffAF omega) n)) s := by
    rw [hconv]
    exact hsF.convolution hsG
  exact (LSeriesSummable_congr s (fun {n} hn => suzukiCoeffAF_apply omega hn)).mp hAF

/-- Exact absolute norm integral of one inverse-dilation term. -/
theorem integral_norm_mellin_inverseMellinDilate
    {g : ℝ → ℂ} {s : ℂ} (hg : MellinConvergent g s)
    {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ),
        ‖(x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g a x‖) =
      a ^ (-s.re) *
        ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • g y‖ := by
  let N : ℝ → ℝ := fun y => ‖(y : ℂ) ^ (s - 1) • g y‖
  have hN : IntegrableOn N (Ioi (0 : ℝ)) := hg.norm
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi N 0 ha
  rw [mul_zero] at hscale
  have hInv := MeasureTheory.integral_comp_rpow_Ioi
    (g := fun u : ℝ => N (a * u)) (p := (-1 : ℝ)) (by norm_num)
  norm_num at hInv
  simp only [Real.rpow_neg_one] at hInv
  have hInv' :
      (∫ x in Ioi (0 : ℝ), (x ^ (-2 : ℝ)) * N (a * x⁻¹)) =
        a⁻¹ * ∫ y in Ioi (0 : ℝ), N y := by
    calc
      (∫ x in Ioi (0 : ℝ), (x ^ (-2 : ℝ)) * N (a * x⁻¹)) =
          ∫ x in Ioi (0 : ℝ), (x ^ (2 : ℕ))⁻¹ * N (a * x⁻¹) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            have hp : x ^ (-2 : ℝ) = (x ^ (2 : ℕ))⁻¹ := by
              rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num,
                Real.rpow_neg hx.le, Real.rpow_two]
            change x ^ (-2 : ℝ) * N (a * x⁻¹) =
              (x ^ (2 : ℕ))⁻¹ * N (a * x⁻¹)
            rw [hp]
      _ = ∫ y in Ioi (0 : ℝ), N (a * y) := hInv
      _ = a⁻¹ * ∫ y in Ioi (0 : ℝ), N y := by
            simpa only [smul_eq_mul] using hscale
  have hpoint : ∀ x : ℝ, 0 < x →
      ‖(x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g a x‖ =
        a ^ (1 - s.re) *
          ((x ^ (-2 : ℝ)) * N (a * x⁻¹)) := by
    intro x hx
    rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
      inverseMellinDilate, norm_div, norm_real, Real.norm_of_nonneg hx.le]
    dsimp only [N]
    rw [div_eq_mul_inv]
    have hsre : ((1 - s) - 1).re = -s.re := by norm_num
    rw [hsre]
    have hnorm :
        ‖((a * x⁻¹ : ℝ) : ℂ) ^ (s - 1)‖ =
          a ^ (s.re - 1) * x ^ (1 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (mul_pos ha (inv_pos.mpr hx))]
      norm_num
      rw [Real.mul_rpow ha.le (inv_nonneg.mpr hx.le),
        Real.inv_rpow hx.le]
      have hinvpow : (x ^ (s.re - 1))⁻¹ = x ^ (1 - s.re) := by
        rw [← Real.rpow_neg hx.le]
        congr 1
        ring
      rw [hinvpow]
    rw [norm_smul, hnorm]
    have hpow :
        x ^ (-s.re) / x = x ^ (-s.re - 1) := by
      calc
        x ^ (-s.re) / x = x ^ (-s.re) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = x ^ (-s.re - 1) := (Real.rpow_sub hx (-s.re) 1).symm
    have haid : a ^ (1 - s.re) * a ^ (s.re - 1) = 1 := by
      rw [← Real.rpow_add ha]
      norm_num
    have hxid : x ^ (-2 : ℝ) * x ^ (1 - s.re) = x ^ (-s.re - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hdiv : ‖g (a / x)‖ = ‖g (a * x⁻¹)‖ := by rw [div_eq_mul_inv]
    rw [hdiv]
    calc
      x ^ (-s.re) * (‖g (a * x⁻¹)‖ / x) =
          (x ^ (-s.re) / x) * ‖g (a * x⁻¹)‖ := by ring
      _ = x ^ (-s.re - 1) * ‖g (a * x⁻¹)‖ := by rw [hpow]
      _ = a ^ (1 - s.re) *
          (x ^ (-2 : ℝ) *
            (a ^ (s.re - 1) * x ^ (1 - s.re) * ‖g (a * x⁻¹)‖)) := by
            symm
            calc
              a ^ (1 - s.re) *
                    (x ^ (-2 : ℝ) *
                      (a ^ (s.re - 1) * x ^ (1 - s.re) * ‖g (a * x⁻¹)‖)) =
                  (a ^ (1 - s.re) * a ^ (s.re - 1)) *
                    (x ^ (-2 : ℝ) * x ^ (1 - s.re)) * ‖g (a * x⁻¹)‖ := by ring
              _ = x ^ (-s.re - 1) * ‖g (a * x⁻¹)‖ := by rw [haid, hxid, one_mul]
  calc
    (∫ x in Ioi (0 : ℝ),
        ‖(x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g a x‖) =
        ∫ x in Ioi (0 : ℝ), a ^ (1 - s.re) *
          ((x ^ (-2 : ℝ)) * N (a * x⁻¹)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            exact hpoint x hx
    _ = a ^ (1 - s.re) *
        ∫ x in Ioi (0 : ℝ), (x ^ (-2 : ℝ)) * N (a * x⁻¹) := by
          rw [integral_const_mul]
    _ = a ^ (1 - s.re) *
        (a⁻¹ * ∫ y in Ioi (0 : ℝ), N y) := by rw [hInv']
    _ = a ^ (-s.re) *
        ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • g y‖ := by
          dsimp only [N]
          rw [show a⁻¹ = a ^ (-1 : ℝ) by
            rw [Real.rpow_neg_one]]
          have haexp : a ^ (1 - s.re) * a ^ (-1 : ℝ) = a ^ (-s.re) := by
            rw [← Real.rpow_add ha]
            congr 1
            ring
          rw [← mul_assoc, haexp]

/-- Arithmetic inverse-dilation sum attached to a Mellin kernel. -/
def suzukiArithmeticH (omega : ℝ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
    inverseMellinDilate g n x

/-- General Fubini/Tonelli theorem for Suzuki's arithmetic inverse-dilation sum. -/
theorem hasMellin_suzukiArithmeticH
    {omega : ℝ} {g : ℝ → ℂ} {s M : ℂ}
    (hg0 : g 0 = 0) (hg : HasMellin g s M)
    (hcoeff : LSeriesSummable
      (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s) :
    HasMellin (suzukiArithmeticH omega g) (1 - s)
      (LSeries (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s * M) := by
  let c : ℕ → ℂ := fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)
  let C : ℝ := ∫ y in Ioi (0 : ℝ), ‖(y : ℂ) ^ (s - 1) • g y‖
  let F : ℕ → ℝ → ℂ := fun n x =>
    (x : ℂ) ^ ((1 - s) - 1) • (c n * inverseMellinDilate g n x)
  change LSeriesSummable c s at hcoeff
  have hFint : ∀ n : ℕ, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hzero : F 0 = 0 := by
        funext x
        simp [F, c, inverseMellinDilate, hg0]
      rw [hzero]
      exact integrable_zero ℝ ℂ (volume.restrict (Ioi (0 : ℝ)))
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hinv := hasMellin_inverseMellinDilate hg.1 hnpos
      have hc := hinv.1.const_smul (c n)
      change Integrable (F n) (volume.restrict (Ioi (0 : ℝ)))
      change IntegrableOn (fun x : ℝ =>
        (x : ℂ) ^ ((1 - s) - 1) •
          (c n • inverseMellinDilate g n x)) (Ioi (0 : ℝ)) at hc
      rw [IntegrableOn] at hc
      simpa only [F, smul_eq_mul, mul_assoc] using hc
  have hFnorm : ∀ n : ℕ,
      (∫ x, ‖F n x‖ ∂(volume.restrict (Ioi (0 : ℝ)))) =
        C * ‖LSeries.term c s n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [F, c, inverseMellinDilate, hg0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnorm := integral_norm_mellin_inverseMellinDilate hg.1 hnpos
      rw [LSeries.norm_term_eq, if_neg hn]
      have hnreal : ((n : ℕ) : ℝ) ^ (-s.re) = 1 / ((n : ℕ) : ℝ) ^ s.re := by
        rw [Real.rpow_neg (Nat.cast_nonneg n)]
        rw [one_div]
      have hpoint : ∀ x : ℝ,
          ‖(x : ℂ) ^ ((1 - s) - 1) •
              (c n * inverseMellinDilate g n x)‖ =
            ‖c n‖ *
              ‖(x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g n x‖ := by
        intro x
        simp only [smul_eq_mul, norm_mul]
        ring
      change (∫ x in Ioi (0 : ℝ), ‖F n x‖) = _
      calc
        (∫ x in Ioi (0 : ℝ), ‖F n x‖) =
            ‖c n‖ * ∫ x in Ioi (0 : ℝ),
              ‖(x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g n x‖ := by
                simp_rw [F, hpoint]
                rw [integral_const_mul]
        _ = ‖c n‖ * (((n : ℝ) ^ (-s.re)) * C) := by
              rw [hnorm]
        _ = C * (‖c n‖ / (n : ℝ) ^ s.re) := by
              rw [hnreal]
              ring
  have hFsum : Summable fun n =>
      ∫ x, ‖F n x‖ ∂(volume.restrict (Ioi (0 : ℝ))) := by
    rw [funext hFnorm]
    exact hcoeff.norm.mul_left C
  have hswap := integral_tsum_of_summable_integral_norm hFint hFsum
  constructor
  · rw [MellinConvergent]
    have hint : Integrable (fun x => ∑' n, F n x)
        (volume.restrict (Ioi (0 : ℝ))) := by
      constructor
      · exact AEStronglyMeasurable.tsum fun n => (hFint n).1
      · rw [hasFiniteIntegral_iff_enorm]
        refine lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) ?_
        rw [lintegral_tsum fun n => (hFint n).1.enorm]
        have hnonneg : ∀ n : ℕ, 0 ≤ ∫ x,
            ‖F n x‖ ∂(volume.restrict (Ioi (0 : ℝ))) :=
          fun n => integral_nonneg fun _ => norm_nonneg _
        have hfinite : ∑' n : ℕ, ENNReal.ofReal
            (∫ x, ‖F n x‖ ∂(volume.restrict (Ioi (0 : ℝ)))) < ⊤ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hFsum]
          exact ENNReal.ofReal_lt_top
        convert hfinite using 1
        apply tsum_congr
        intro n
        exact (ofReal_integral_norm_eq_lintegral_enorm (hFint n)).symm
    change IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ ((1 - s) - 1) • suzukiArithmeticH omega g t) (Ioi (0 : ℝ))
    change Integrable (fun t : ℝ =>
      (t : ℂ) ^ ((1 - s) - 1) • suzukiArithmeticH omega g t)
        (volume.restrict (Ioi (0 : ℝ)))
    convert hint using 1
    funext x
    rw [suzukiArithmeticH]
    simp only [smul_eq_mul]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [F, c, smul_eq_mul]
  · rw [mellin]
    change (∫ x, (x : ℂ) ^ ((1 - s) - 1) • suzukiArithmeticH omega g x
        ∂(volume.restrict (Ioi (0 : ℝ)))) = _
    have hfun : (fun x : ℝ => (x : ℂ) ^ ((1 - s) - 1) • suzukiArithmeticH omega g x) =
        fun x => ∑' n, F n x := by
      funext x
      rw [suzukiArithmeticH]
      simp only [smul_eq_mul]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      simp only [F, c, smul_eq_mul]
    rw [hfun, ← hswap]
    have hFintegral : ∀ n : ℕ, (∫ x, F n x ∂(volume.restrict (Ioi (0 : ℝ)))) =
        LSeries.term c s n * mellin g s := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · simp [F, c, inverseMellinDilate, hg0]
      · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hinv := hasMellin_inverseMellinDilate hg.1 hnpos
        have hinvval := hinv.2
        rw [mellin] at hinvval
        change (∫ x in Ioi (0 : ℝ),
          (x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g n x) =
            (n : ℂ) ^ (-s) * mellin g s at hinvval
        change (∫ x in Ioi (0 : ℝ), F n x) = _
        rw [show F n = fun x : ℝ => c n •
            ((x : ℂ) ^ ((1 - s) - 1) • inverseMellinDilate g n x) by
          funext x
          simp only [F, smul_eq_mul]
          ring,
          integral_smul, hinvval, LSeries.term_of_ne_zero hn]
        simp only [smul_eq_mul]
        have hpow : ((n : ℂ) ^ s)⁻¹ = (n : ℂ) ^ (-s) := by
          rw [Complex.cpow_neg]
        rw [div_eq_mul_inv, hpow]
        ring
    simp_rw [hFintegral]
    rw [tsum_mul_right, hg.2]
    rfl

/-- Source equation (204), represented as a locally finite series. -/
def suzukiSourceH (omega : ℝ) : ℝ → ℂ :=
  suzukiArithmeticH omega (suzukiSourceG omega)

/-- Fubini/Tonelli for Suzuki's arithmetic kernel, including absolute convergence. -/
theorem hasMellin_suzukiSourceH
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceH omega) (1 - s)
      (LSeries (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s *
        (suzukiArchimedeanFactor (s - (omega : ℂ)) /
          suzukiArchimedeanFactor (s + (omega : ℂ)))) := by
  apply hasMellin_suzukiArithmeticH
  · rw [suzukiSourceG, if_neg]
    simp
  · exact hasMellin_suzukiSourceG homega hs
  · exact LSeriesSummable_suzukiShiftedCoefficient omega
      (by norm_num; linarith) (by norm_num; linarith)

/-- The pole-cleared archimedean factor used in Suzuki's paper is the corpus `archFactor`. -/
theorem suzukiArchimedeanFactor_eq_archFactor (s : ℂ) :
    suzukiArchimedeanFactor s = archFactor s := by
  rw [suzukiArchimedeanFactor, archFactor, Complex.Gammaℝ_def]
  ring

/-- Product of the arithmetic and archimedean quotients is the literal Xi quotient on Suzuki's
absolute-convergence half-plane. -/
theorem suzuki_LSeries_mul_archimedeanRatio_eq_xiRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    LSeries (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s *
        (suzukiArchimedeanFactor (s - (omega : ℂ)) /
          suzukiArchimedeanFactor (s + (omega : ℂ))) =
      xi (s - (omega : ℂ)) / xi (s + (omega : ℂ)) := by
  have hsm0 : s - (omega : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsp0 : s + (omega : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsm1 : s - (omega : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hsp1 : s + (omega : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
    linarith
  have hGm : Complex.Gammaℝ (s - (omega : ℂ)) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num; linarith)
  have hGp : Complex.Gammaℝ (s + (omega : ℂ)) ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num; linarith)
  have harchP : archFactor (s + (omega : ℂ)) ≠ 0 :=
    archFactor_ne_zero hsp0 hsp1 hGp
  have hzetaP : riemannZeta (s + (omega : ℂ)) ≠ 0 := by
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num; linarith)
  rw [LSeries_suzukiShiftedCoefficient omega (by norm_num; linarith)
      (by norm_num; linarith),
    suzukiArchimedeanFactor_eq_archFactor,
    suzukiArchimedeanFactor_eq_archFactor,
    xi_eq_archFactor_mul_zeta hsm0 hsm1 hGm,
    xi_eq_archFactor_mul_zeta hsp0 hsp1 hGp]
  field_simp

/-- **Suzuki (2012), Proposition 1 in the source variable `s`.**  The integral is absolutely
convergent because this is a `HasMellin` statement. -/
theorem hasMellin_suzukiSourceH_eq_xiRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceH omega) (1 - s)
      (xi (s - (omega : ℂ)) / xi (s + (omega : ℂ))) := by
  rw [← suzuki_LSeries_mul_archimedeanRatio_eq_xiRatio homega hs]
  exact hasMellin_suzukiSourceH homega hs

/-- Source equation (204): the locally finite arithmetic sum printed with `floor x`. -/
def suzukiSourceHFinite (omega : ℝ) (x : ℝ) : ℂ :=
  if 1 < x then
    (1 / (x : ℂ)) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceG omega (n / x)
  else 0

theorem suzukiSourceG_eq_zero_of_nonpos
    (omega : ℝ) {x : ℝ} (hx : x ≤ 0) :
    suzukiSourceG omega x = 0 := by
  rw [suzukiSourceG, if_neg]
  exact fun h => (not_lt_of_ge hx) h.1

theorem suzukiSourceH_eq_zero_of_le_one
    (omega : ℝ) {x : ℝ} (hx : x ≤ 1) :
    suzukiSourceH omega x = 0 := by
  rw [suzukiSourceH, suzukiArithmeticH]
  rw [show (fun n : ℕ => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
      inverseMellinDilate (suzukiSourceG omega) n x) = 0 by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · have hg0 : suzukiSourceG omega 0 = 0 :=
        suzukiSourceG_eq_zero_of_nonpos omega le_rfl
      simp [inverseMellinDilate, hg0]
    · by_cases hx0 : x ≤ 0
      · have harg : (n : ℝ) / x ≤ 0 := by
          exact div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hx0
        rw [inverseMellinDilate, suzukiSourceG_eq_zero_of_nonpos omega harg]
        simp
      · have hxpos : 0 < x := lt_of_not_ge hx0
        have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hxpos).2 (by
          simpa using (le_trans hx hnOne))
        have hgzero : suzukiSourceG omega ((n : ℝ) / x) = 0 := by
          rw [suzukiSourceG, if_neg]
          exact fun h => (not_lt_of_ge hratio) h.2
        rw [inverseMellinDilate, hgzero]
        simp]
  exact tsum_zero

/-- The series definition is pointwise equal to Suzuki's literal floor-truncated equation (204). -/
theorem suzukiSourceH_eq_finite
    (omega : ℝ) (x : ℝ) :
    suzukiSourceH omega x = suzukiSourceHFinite omega x := by
  by_cases hx : 1 < x
  · rw [suzukiSourceH, suzukiArithmeticH, suzukiSourceHFinite, if_pos hx]
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (by
      intro n hn
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn0 | hnlarge
      · have hnzero : n = 0 := by omega
        subst n
        have hg0 : suzukiSourceG omega 0 = 0 :=
          suzukiSourceG_eq_zero_of_nonpos omega le_rfl
        simp [inverseMellinDilate, hg0]
      · have hxlt : x < (n : ℝ) := (Nat.floor_lt hx0.le).mp hnlarge
        have hratio : 1 < (n : ℝ) / x := (one_lt_div hx0).2 hxlt
        have hgzero : suzukiSourceG omega ((n : ℝ) / x) = 0 := by
          rw [suzukiSourceG, if_neg]
          exact fun h => (not_lt_of_ge hratio.le) h.2
        rw [inverseMellinDilate, hgzero]
        simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [inverseMellinDilate]
    ring
  · rw [suzukiSourceHFinite, if_neg hx,
      suzukiSourceH_eq_zero_of_le_one omega (le_of_not_gt hx)]

/-- Exact source proposition with the printed floor-truncated kernel, not merely its series model. -/
theorem hasMellin_suzukiSourceHFinite_eq_xiRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceHFinite omega) (1 - s)
      (xi (s - (omega : ℂ)) / xi (s + (omega : ℂ))) := by
  rw [← funext (suzukiSourceH_eq_finite omega)]
  exact hasMellin_suzukiSourceH_eq_xiRatio homega hs

/-- **Suzuki (2012), Proposition 1, equation (206), verbatim in the spectral variable.**
For `omega > 0` and `Im z > 1/2 + omega`, the floor-truncated source kernel has absolutely
convergent Mellin transform `Theta_omega(z)`. -/
theorem suzuki2012_proposition_one
    {omega : ℝ} (homega : 0 < omega) {z : ℂ}
    (hz : 1 / 2 + omega < z.im) :
    HasMellin (suzukiSourceHFinite omega)
      (1 / 2 + z * I)
      (suzukiCanonicalTheta omega z) := by
  let s : ℂ := 1 / 2 - z * I
  have hs : 1 + omega < s.re := by
    dsimp only [s]
    norm_num
    linarith
  have h := hasMellin_suzukiSourceHFinite_eq_xiRatio homega hs
  convert h using 1
  · dsimp only [s]
    ring
  · rw [suzukiCanonicalTheta]
    dsimp only [s]
    congr 2 <;> ring

/-! ### Suzuki's once-integrated kernel -/

/-- Weighted kernel `g_omega^{<1>}` in convolution coordinates. -/
def suzukiIntegratedG (omega : ℝ) : ℝ → ℂ :=
  positiveMellinConvolution (suzukiCanonicalG omega) (suzukiPoleKernel (1 / 2))

/-- Literal source definition (a202), with the irrelevant endpoint totalized to zero. -/
def suzukiSourceGOne (omega : ℝ) (x : ℝ) : ℂ :=
  if 0 < x ∧ x < 1 then
    ∫ y in Ioc x 1,
      (Real.sqrt (y / x) : ℂ) * suzukiSourceG omega y / y
  else 0

private theorem cpow_neg_half_div_eq_sqrt_div
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    ((x / y : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ) =
      (Real.sqrt (y / x) : ℂ) := by
  rw [← Complex.ofReal_cpow (div_nonneg hx.le hy.le) (-1 / 2),
    Real.sqrt_eq_rpow, Real.div_rpow hx.le hy.le,
    Real.div_rpow hy.le hx.le]
  have hneg : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  rw [hneg, Real.rpow_neg hx.le, Real.rpow_neg hy.le]
  push_cast
  have hxpow : x ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  have hypow : y ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  field_simp

/-- Convolution coordinate is exactly Suzuki's displayed weighted integral on `0 < x < 1`. -/
theorem suzukiIntegratedG_eq_source
    (omega : ℝ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    suzukiIntegratedG omega x = suzukiSourceGOne omega x := by
  rw [suzukiIntegratedG, positiveMellinConvolution,
    suzukiSourceGOne, if_pos ⟨hx0, hx1⟩,
    ← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne x, volume.ae_ne 1] with y hyx hyone
  by_cases hy0 : 0 < y
  · have hy0mem : y ∈ Ioi (0 : ℝ) := hy0
    by_cases hyxlt : x < y
    · by_cases hy1 : y < 1
      · have hymem : y ∈ Ioc x 1 := ⟨hyxlt, hy1.le⟩
        have hratio : x / y ∈ Ioc (0 : ℝ) 1 := by
          exact ⟨div_pos hx0 hy0, (div_le_one hy0).2 hyxlt.le⟩
        rw [Set.indicator_of_mem hy0mem, Set.indicator_of_mem hymem,
          suzukiPoleKernel, Set.indicator_of_mem hratio]
        rw [suzukiCanonicalG_eq_source omega hy0 hy1]
        rw [show (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) = ((-1 / 2 : ℝ) : ℂ) by
          push_cast
          ring,
          cpow_neg_half_div_eq_sqrt_div hx0 hy0]
        rw [suzukiSourceG, if_pos ⟨hy0, hy1⟩]
        ring
      · have hygt : 1 < y := lt_of_le_of_ne (le_of_not_gt hy1) (Ne.symm hyone)
        have hnot : y ∉ Ioc x 1 := fun h => (not_lt_of_ge h.2) hygt
        rw [Set.indicator_of_mem hy0mem, Set.indicator_of_notMem hnot,
          suzukiCanonicalG_eq_zero_of_one_lt omega hygt]
        simp
    · have hylt : y < x := lt_of_le_of_ne (le_of_not_gt hyxlt) hyx
      have hnot : y ∉ Ioc x 1 := fun h => (not_lt_of_ge h.1.le) hylt
      have hratio : x / y ∉ Ioc (0 : ℝ) 1 := by
        intro h
        have : 1 < x / y := (one_lt_div hy0).2 hylt
        linarith [h.2]
      rw [Set.indicator_of_mem hy0mem, Set.indicator_of_notMem hnot,
        suzukiPoleKernel, Set.indicator_of_notMem hratio]
      simp
  · have hy0mem : y ∉ Ioi (0 : ℝ) := hy0
    have hnot : y ∉ Ioc x 1 := fun h => hy0 (lt_trans hx0 h.1)
    rw [Set.indicator_of_notMem hy0mem, Set.indicator_of_notMem hnot]

/-- The convolution kernel and literal weighted integral agree almost everywhere on the Mellin
half-line; only the source's undefined endpoint can differ. -/
theorem suzukiIntegratedG_ae_eq_sourceGOne (omega : ℝ) :
    suzukiIntegratedG omega =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      suzukiSourceGOne omega := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    MeasureTheory.ae_restrict_of_ae (volume.ae_ne 1)] with x hx0 hx1
  by_cases hxlt : x < 1
  · exact suzukiIntegratedG_eq_source omega hx0 hxlt
  · have hxgt : 1 < x := lt_of_le_of_ne (le_of_not_gt hxlt) (Ne.symm hx1)
    have hsource : suzukiSourceGOne omega x = 0 := by
      rw [suzukiSourceGOne, if_neg]
      exact fun h => (not_lt_of_ge hxgt.le) h.2
    have hconv : suzukiIntegratedG omega x = 0 := by
      rw [suzukiIntegratedG, positiveMellinConvolution,
        ← integral_indicator measurableSet_Ioi]
      apply integral_eq_zero_of_ae
      filter_upwards [volume.ae_ne 1] with y hy1
      by_cases hy0 : 0 < y
      · have hy0mem : y ∈ Ioi (0 : ℝ) := hy0
        rw [Set.indicator_of_mem hy0mem]
        by_cases hylt : y < 1
        · have hratio : x / y ∉ Ioc (0 : ℝ) 1 := by
            intro h
            have : 1 < x / y := (one_lt_div hy0).2 (lt_trans hylt hxgt)
            linarith [h.2]
          rw [suzukiPoleKernel, Set.indicator_of_notMem hratio]
          simp
        · have hygt : 1 < y := lt_of_le_of_ne (le_of_not_gt hylt) (Ne.symm hy1)
          rw [suzukiCanonicalG_eq_zero_of_one_lt omega hygt]
          simp
      · have hy0mem : y ∉ Ioi (0 : ℝ) := hy0
        rw [Set.indicator_of_notMem hy0mem]
        rfl
    rw [hconv, hsource]

theorem measurable_suzukiCanonicalG (omega : ℝ) :
    Measurable (suzukiCanonicalG omega) := by
  unfold suzukiCanonicalG
  have hc := measurable_positiveMellinConvolution
    (measurable_suzukiPrimaryBetaKernel omega)
    (measurable_suzukiPoleKernel omega)
  exact (measurable_const.mul (measurable_suzukiPrimaryBetaKernel omega)).sub
    ((measurable_const.mul measurable_const).mul hc)

/-- Equation (a202) multiplies the kernel Mellin transform by `(s-1/2)⁻¹`. -/
theorem hasMellin_suzukiIntegratedG
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiIntegratedG omega) s
      ((suzukiArchimedeanFactor (s - (omega : ℂ)) /
          suzukiArchimedeanFactor (s + (omega : ℂ))) *
        (1 / (s - 1 / 2))) := by
  have hg := hasMellin_suzukiCanonicalG homega hs
  have hp := hasMellin_suzukiPoleKernel (omega := (1 / 2 : ℝ)) (s := s) (by
    norm_num
    linarith)
  have hc := hasMellin_positiveMellinConvolution
    (measurable_suzukiCanonicalG omega)
    (measurable_suzukiPoleKernel (1 / 2)) hg.1 hp.1
  rw [suzukiIntegratedG]
  constructor
  · exact hc.1
  · rw [hc.2, hg.2, hp.2]
    congr 2
    push_cast
    ring

/-- Literal equation (a202), with absolute convergence and exact Mellin transform. -/
theorem hasMellin_suzukiSourceGOne
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceGOne omega) s
      ((suzukiArchimedeanFactor (s - (omega : ℂ)) /
          suzukiArchimedeanFactor (s + (omega : ℂ))) *
        (1 / (s - 1 / 2))) := by
  have h := hasMellin_suzukiIntegratedG homega hs
  have hae := suzukiIntegratedG_ae_eq_sourceGOne omega
  constructor
  · refine h.1.congr ?_
    filter_upwards [hae] with x hx
    rw [hx]
  · rw [mellin]
    calc
      (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • suzukiSourceGOne omega t) =
          ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • suzukiIntegratedG omega t := by
            apply integral_congr_ae
            filter_upwards [hae] with x hx
            rw [hx]
      _ = _ := h.2

/-- Arithmetic series for Suzuki's `h_omega^{<1>}`. -/
def suzukiSourceHOne (omega : ℝ) : ℝ → ℂ :=
  suzukiArithmeticH omega (suzukiSourceGOne omega)

/-- Absolute-convergence form of Proposition `prop_a1` before simplifying the Xi quotient. -/
theorem hasMellin_suzukiSourceHOne
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceHOne omega) (1 - s)
      (LSeries (fun n => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ)) s *
        ((suzukiArchimedeanFactor (s - (omega : ℂ)) /
            suzukiArchimedeanFactor (s + (omega : ℂ))) *
          (1 / (s - 1 / 2)))) := by
  apply hasMellin_suzukiArithmeticH
  · rw [suzukiSourceGOne, if_neg]
    simp
  · exact hasMellin_suzukiSourceGOne homega hs
  · exact LSeriesSummable_suzukiShiftedCoefficient omega
      (by norm_num; linarith) (by norm_num; linarith)

theorem hasMellin_suzukiSourceHOne_eq_xiRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceHOne omega) (1 - s)
      ((1 / (s - 1 / 2)) *
        (xi (s - (omega : ℂ)) / xi (s + (omega : ℂ)))) := by
  have h := hasMellin_suzukiSourceHOne homega hs
  convert h using 1
  rw [← suzuki_LSeries_mul_archimedeanRatio_eq_xiRatio homega hs]
  ring

/-- Literal floor-truncated equation (a204). -/
def suzukiSourceHOneFinite (omega : ℝ) (x : ℝ) : ℂ :=
  if 1 < x then
    (1 / (x : ℂ)) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
      ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
        suzukiSourceGOne omega (n / x)
  else 0

theorem suzukiSourceGOne_eq_zero_of_nonpos
    (omega : ℝ) {x : ℝ} (hx : x ≤ 0) :
    suzukiSourceGOne omega x = 0 := by
  rw [suzukiSourceGOne, if_neg]
  exact fun h => (not_lt_of_ge hx) h.1

theorem suzukiSourceGOne_eq_zero_of_one_le
    (omega : ℝ) {x : ℝ} (hx : 1 ≤ x) :
    suzukiSourceGOne omega x = 0 := by
  rw [suzukiSourceGOne, if_neg]
  exact fun h => (not_lt_of_ge hx) h.2

theorem suzukiSourceHOne_eq_zero_of_le_one
    (omega : ℝ) {x : ℝ} (hx : x ≤ 1) :
    suzukiSourceHOne omega x = 0 := by
  rw [suzukiSourceHOne, suzukiArithmeticH]
  rw [show (fun n : ℕ => ((suzukiShiftedCoefficient omega n : ℝ) : ℂ) *
      inverseMellinDilate (suzukiSourceGOne omega) n x) = 0 by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · have hg0 : suzukiSourceGOne omega 0 = 0 :=
        suzukiSourceGOne_eq_zero_of_nonpos omega le_rfl
      simp [inverseMellinDilate, hg0]
    · by_cases hx0 : x ≤ 0
      · have harg : (n : ℝ) / x ≤ 0 :=
          div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) hx0
        rw [inverseMellinDilate,
          suzukiSourceGOne_eq_zero_of_nonpos omega harg]
        simp
      · have hxpos : 0 < x := lt_of_not_ge hx0
        have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
        have hratio : 1 ≤ (n : ℝ) / x := (le_div_iff₀ hxpos).2 (by
          simpa using (le_trans hx hnOne))
        rw [inverseMellinDilate,
          suzukiSourceGOne_eq_zero_of_one_le omega hratio]
        simp]
  exact tsum_zero

/-- Series equation and floor-truncated equation (a204) agree pointwise. -/
theorem suzukiSourceHOne_eq_finite
    (omega : ℝ) (x : ℝ) :
    suzukiSourceHOne omega x = suzukiSourceHOneFinite omega x := by
  by_cases hx : 1 < x
  · rw [suzukiSourceHOne, suzukiArithmeticH,
      suzukiSourceHOneFinite, if_pos hx]
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (by
      intro n hn
      simp only [Finset.mem_Icc, not_and_or, not_le] at hn
      rcases hn with hn0 | hnlarge
      · have hnzero : n = 0 := by omega
        subst n
        have hg0 : suzukiSourceGOne omega 0 = 0 :=
          suzukiSourceGOne_eq_zero_of_nonpos omega le_rfl
        simp [inverseMellinDilate, hg0]
      · have hxlt : x < (n : ℝ) := (Nat.floor_lt hx0.le).mp hnlarge
        have hratio : 1 ≤ (n : ℝ) / x :=
          (one_lt_div hx0).2 hxlt |>.le
        rw [inverseMellinDilate,
          suzukiSourceGOne_eq_zero_of_one_le omega hratio]
        simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [inverseMellinDilate]
    ring
  · rw [suzukiSourceHOneFinite, if_neg hx,
      suzukiSourceHOne_eq_zero_of_le_one omega (le_of_not_gt hx)]

theorem hasMellin_suzukiSourceHOneFinite_eq_xiRatio
    {omega : ℝ} (homega : 0 < omega) {s : ℂ} (hs : 1 + omega < s.re) :
    HasMellin (suzukiSourceHOneFinite omega) (1 - s)
      ((1 / (s - 1 / 2)) *
        (xi (s - (omega : ℂ)) / xi (s + (omega : ℂ)))) := by
  rw [← funext (suzukiSourceHOne_eq_finite omega)]
  exact hasMellin_suzukiSourceHOne_eq_xiRatio homega hs

/-- **Suzuki (2012), Proposition `prop_a1`, equation (a207), verbatim.** -/
theorem suzuki2012_proposition_a1
    {omega : ℝ} (homega : 0 < omega) {z : ℂ}
    (hz : 1 / 2 + omega < z.im) :
    HasMellin (suzukiSourceHOneFinite omega)
      (1 / 2 + z * I)
      ((I / z) * suzukiCanonicalTheta omega z) := by
  let s : ℂ := 1 / 2 - z * I
  have hs : 1 + omega < s.re := by
    dsimp only [s]
    norm_num
    linarith
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
    linarith
  have h := hasMellin_suzukiSourceHOneFinite_eq_xiRatio homega hs
  convert h using 1
  · dsimp only [s]
    ring
  · rw [suzukiCanonicalTheta]
    dsimp only [s]
    have hfac : 1 / ((1 / 2 - z * I) - 1 / 2) = I / z := by
      rw [show (1 / 2 - z * I) - 1 / 2 = -z * I by ring]
      field_simp
      norm_num [pow_two, Complex.I_mul_I]
    rw [hfac]
    congr 2 <;> ring

end RHTower
