import GaloisForLFunctions.RHTower.CCMFirstClockLandauAnalytic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

private theorem integrableOn_sq_mul_cexp_neg
    {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun L : ℝ =>
      (L : ℂ) ^ 2 * Complex.exp (-a * (L : ℂ))) (Ioi 0) := by
  have hreal : IntegrableOn
      (fun L : ℝ => L ^ 2 * Real.exp (-(a.re * L))) (Ioi 0) := by
    simpa only [Real.rpow_two, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (2 : ℝ)) (b := a.re)
        (by norm_num) (by norm_num) ha)
  apply Integrable.mono' hreal
  · exact (by fun_prop : Continuous (fun L : ℝ =>
      (L : ℂ) ^ 2 * Complex.exp (-a * (L : ℂ)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
    have hLpos : 0 < L := hL
    rw [norm_mul, norm_pow, norm_real, Complex.norm_exp, Real.norm_eq_abs,
      abs_of_pos hLpos]
    have hre : (-a * (L : ℂ)).re = -(a.re * L) := by
      simp [mul_re]
    rw [hre]

private theorem integral_sq_mul_cexp_neg
    {a : ℂ} (ha : 0 < a.re) :
    (∫ L : ℝ in Ioi 0,
      (L : ℂ) ^ 2 * Complex.exp (-a * (L : ℂ))) =
        2 / a ^ 3 := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_re] at ha
    linarith
  let P : ℝ → ℂ := fun L =>
    (L : ℂ) ^ 2 / a + 2 * (L : ℂ) / a ^ 2 + 2 / a ^ 3
  let A : ℝ → ℂ := fun L =>
    -(Complex.exp (-a * (L : ℂ)) * P L)
  have hderiv : ∀ L ∈ Ici (0 : ℝ),
      HasDerivAt A
        ((L : ℂ) ^ 2 * Complex.exp (-a * (L : ℂ))) L := by
    intro L hL
    have hcast : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 L :=
      (hasDerivAt_id L).ofReal_comp
    have harg : HasDerivAt (fun x : ℝ => -a * (x : ℂ)) (-a) L := by
      simpa using hcast.const_mul (-a)
    have hexp : HasDerivAt
        (fun x : ℝ => Complex.exp (-a * (x : ℂ)))
        (-a * Complex.exp (-a * (L : ℂ))) L := by
      simpa only [Function.comp_apply, mul_comm] using
        (Complex.hasDerivAt_exp _).comp L harg
    have hP : HasDerivAt P
        (2 * (L : ℂ) / a + 2 / a ^ 2) L := by
      dsimp only [P]
      have hsq := (hcast.pow 2).div_const a
      have hlin := (hcast.const_mul 2).div_const (a ^ 2)
      have hconst := hasDerivAt_const L (2 / a ^ 3)
      convert (hsq.add hlin).add hconst using 1 <;> ring
    dsimp only [A]
    convert (hexp.mul hP).neg using 1
    dsimp only [P]
    field_simp [ha0]
    ring
  have htendPow (k : ℕ) :
      Tendsto (fun L : ℝ =>
        (L : ℂ) ^ k * Complex.exp (-a * (L : ℂ)))
        atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hreal :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (k : ℝ) a.re ha
    refine hreal.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
    rw [norm_mul, norm_pow, norm_real, Complex.norm_exp, Real.norm_eq_abs,
      abs_of_pos hL, ← Real.rpow_natCast]
    have hre : (-a * (L : ℂ)).re = -(a.re * L) := by
      simp [mul_re]
    rw [hre]
    congr 2
    ring
  have htend : Tendsto A atTop (𝓝 0) := by
    have h2 := (htendPow 2).mul_const (1 / a)
    have h1 := (htendPow 1).mul_const (2 / a ^ 2)
    have h0 := (htendPow 0).mul_const (2 / a ^ 3)
    have hsum := (h2.add h1).add h0
    have hneg := hsum.neg
    convert hneg using 1
    funext L
    dsimp only [A, P]
    ring
    simp
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv (integrableOn_sq_mul_cexp_neg ha) htend
  rw [hmain]
  dsimp only [A, P]
  simp

private theorem integrableOn_sq_cexp_cos
    {s z : ℂ} {u : ℝ} (hs : |z.im| < s.re)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    IntegrableOn (fun L : ℝ =>
      Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        Complex.cos ((L : ℂ) * z * (u : ℂ))) (Ioi 0) := by
  let aMinus : ℂ := s - I * z * (u : ℂ)
  let aPlus : ℂ := s + I * z * (u : ℂ)
  have hMinus : 0 < aMinus.re := by
    dsimp only [aMinus]
    simp only [sub_re, mul_re, I_re, zero_mul, I_im, one_mul,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have hprod : |z.im * u| ≤ |z.im| := by
      rw [abs_mul]
      nlinarith [abs_nonneg z.im]
    linarith [neg_abs_le (z.im * u)]
  have hPlus : 0 < aPlus.re := by
    dsimp only [aPlus]
    simp only [add_re, mul_re, I_re, zero_mul, I_im, one_mul,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have hprod : |z.im * u| ≤ |z.im| := by
      rw [abs_mul]
      nlinarith [abs_nonneg z.im]
    linarith [le_abs_self (z.im * u)]
  have hM := integrableOn_sq_mul_cexp_neg hMinus
  have hP := integrableOn_sq_mul_cexp_neg hPlus
  have hsum : IntegrableOn (fun L : ℝ =>
      ((L : ℂ) ^ 2 * Complex.exp (-aMinus * (L : ℂ)) +
        (L : ℂ) ^ 2 * Complex.exp (-aPlus * (L : ℂ))) / 2) (Ioi 0) :=
    (hM.add hP).div_const 2
  apply hsum.congr_fun _ measurableSet_Ioi
  intro L hL
  dsimp only [aMinus, aPlus]
  rw [Complex.cos]
  have hleft :
      Complex.exp (-s * (L : ℂ)) *
          Complex.exp ((L : ℂ) * (z * (u : ℂ)) * I) =
        Complex.exp (-(s - I * z * (u : ℂ)) * (L : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright :
      Complex.exp (-s * (L : ℂ)) *
          Complex.exp (-((L : ℂ) * (z * (u : ℂ))) * I) =
        Complex.exp (-(s + I * z * (u : ℂ)) * (L : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  symm
  calc
    Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        ((Complex.exp ((L : ℂ) * z * (u : ℂ) * I) +
          Complex.exp (-((L : ℂ) * z * (u : ℂ)) * I)) / 2) =
      (((L : ℂ) ^ 2 *
          (Complex.exp (-s * (L : ℂ)) *
            Complex.exp ((L : ℂ) * (z * (u : ℂ)) * I))) +
        (L : ℂ) ^ 2 *
          (Complex.exp (-s * (L : ℂ)) *
            Complex.exp (-((L : ℂ) * (z * (u : ℂ))) * I))) / 2 := by
        ring
    _ = _ := by rw [hleft, hright]

private theorem integral_sq_cexp_cos
    {s z : ℂ} {u : ℝ} (hs : |z.im| < s.re)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        Complex.cos ((L : ℂ) * z * (u : ℂ))) =
      1 / (s - I * z * (u : ℂ)) ^ 3 +
        1 / (s + I * z * (u : ℂ)) ^ 3 := by
  let aMinus : ℂ := s - I * z * (u : ℂ)
  let aPlus : ℂ := s + I * z * (u : ℂ)
  have hMinus : 0 < aMinus.re := by
    dsimp only [aMinus]
    simp only [sub_re, mul_re, I_re, zero_mul, I_im, one_mul,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have hprod : |z.im * u| ≤ |z.im| := by
      rw [abs_mul]
      nlinarith [abs_nonneg z.im]
    linarith [neg_abs_le (z.im * u)]
  have hPlus : 0 < aPlus.re := by
    dsimp only [aPlus]
    simp only [add_re, mul_re, I_re, zero_mul, I_im, one_mul,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_sub]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    have hprod : |z.im * u| ≤ |z.im| := by
      rw [abs_mul]
      nlinarith [abs_nonneg z.im]
    linarith [le_abs_self (z.im * u)]
  have hM := integrableOn_sq_mul_cexp_neg hMinus
  have hP := integrableOn_sq_mul_cexp_neg hPlus
  have hfun :
      (fun L : ℝ =>
        Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
          Complex.cos ((L : ℂ) * z * (u : ℂ))) =
      fun L : ℝ =>
        ((L : ℂ) ^ 2 * Complex.exp (-aMinus * (L : ℂ)) +
          (L : ℂ) ^ 2 * Complex.exp (-aPlus * (L : ℂ))) / 2 := by
    funext L
    dsimp only [aMinus, aPlus]
    rw [Complex.cos]
    have hleft :
        Complex.exp (-s * (L : ℂ)) *
            Complex.exp ((L : ℂ) * (z * (u : ℂ)) * I) =
          Complex.exp (-(s - I * z * (u : ℂ)) * (L : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    have hright :
        Complex.exp (-s * (L : ℂ)) *
            Complex.exp (-((L : ℂ) * (z * (u : ℂ))) * I) =
          Complex.exp (-(s + I * z * (u : ℂ)) * (L : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    calc
      Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
          ((Complex.exp ((L : ℂ) * z * (u : ℂ) * I) +
            Complex.exp (-((L : ℂ) * z * (u : ℂ)) * I)) / 2) =
        (((L : ℂ) ^ 2 *
            (Complex.exp (-s * (L : ℂ)) *
              Complex.exp ((L : ℂ) * (z * (u : ℂ)) * I))) +
          (L : ℂ) ^ 2 *
            (Complex.exp (-s * (L : ℂ)) *
              Complex.exp (-((L : ℂ) * (z * (u : ℂ))) * I))) / 2 := by
          ring
      _ = _ := by rw [hleft, hright]
  rw [hfun, integral_div, integral_add hM hP,
    integral_sq_mul_cexp_neg hMinus, integral_sq_mul_cexp_neg hPlus]
  dsimp only [aMinus, aPlus]
  ring

/-- Uniform complex cosine bound along a real contraction of a spectral segment. -/
theorem norm_cos_real_mul_le_exp_abs_im
    (z : ℂ) {L u : ℝ} (hL : 0 < L)
    (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    ‖Complex.cos ((L : ℂ) * z * (u : ℂ))‖ ≤
      Real.exp (|z.im| * L) := by
  rw [Complex.cos, norm_div, norm_ofNat]
  have hprod : |z.im * u| ≤ |z.im| := by
    rw [abs_mul]
    have huabs : |u| ≤ 1 := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
    nlinarith [abs_nonneg z.im]
  have hrePlus :
      (((L : ℂ) * z * (u : ℂ)) * I).re =
        -(L * z.im * u) := by
    simp [mul_re]
  have hreMinus :
      ((-((L : ℂ) * z * (u : ℂ))) * I).re =
        L * z.im * u := by
    simp [mul_re]
  have hargPlus : -(L * z.im * u) ≤ |z.im| * L := by
    have hlow := neg_abs_le (z.im * u)
    nlinarith [mul_le_mul_of_nonneg_left hlow hL.le]
  have hargMinus : L * z.im * u ≤ |z.im| * L := by
    have hupp := le_abs_self (z.im * u)
    nlinarith [mul_le_mul_of_nonneg_left hupp hL.le]
  calc
    ‖Complex.exp (((L : ℂ) * z * (u : ℂ)) * I) +
        Complex.exp (-((L : ℂ) * z * (u : ℂ)) * I)‖ / 2 ≤
      (‖Complex.exp (((L : ℂ) * z * (u : ℂ)) * I)‖ +
        ‖Complex.exp (-((L : ℂ) * z * (u : ℂ)) * I)‖) / 2 := by
          gcongr
          exact norm_add_le _ _
    _ = (Real.exp (-(L * z.im * u)) +
        Real.exp (L * z.im * u)) / 2 := by
          rw [Complex.norm_exp, Complex.norm_exp, hrePlus, hreMinus]
    _ ≤ (Real.exp (|z.im| * L) + Real.exp (|z.im| * L)) / 2 := by
          gcongr <;> exact Real.exp_le_exp.mpr (by assumption)
    _ = Real.exp (|z.im| * L) := by ring

private theorem integral_exp_mul_compact_firstClock_eq_atom
    {s z : ℂ} (hs : |z.im| < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        (-(1 / (2 * (Real.pi : ℂ))) *
          ∫ u : ℝ in (0 : ℝ)..1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
              Complex.cos ((L : ℂ) * z * (u : ℂ)))) =
      ccmFirstClockLaplaceContinuationAtom s z := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let nu : Measure ℝ := volume.restrict (Ioc 0 1)
  let eta : ℝ := s.re - |z.im|
  let g : ℝ → ℝ := fun L => L ^ 2 * Real.exp (-(eta * L))
  let E : ℝ → ℝ → ℂ := fun L u =>
    Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
      (Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        Complex.cos ((L : ℂ) * z * (u : ℂ)))
  have heta : 0 < eta := by dsimp only [eta]; linarith
  have hg : Integrable g mu := by
    dsimp only [g, mu]
    simpa only [Real.rpow_two, Real.rpow_one, neg_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (2 : ℝ)) (b := eta)
        (by norm_num) (by norm_num) heta)
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) nu := by
    dsimp only [nu]
    exact integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  have hbase : Integrable
      (fun p : ℝ × ℝ => g p.1 * 1) (mu.prod nu) :=
    hg.mul_prod hone
  have hEmeas : AEStronglyMeasurable (Function.uncurry E) (mu.prod nu) := by
    exact (by fun_prop : Continuous (Function.uncurry E)).aestronglyMeasurable
  have hEbound : ∀ᵐ p : ℝ × ℝ ∂mu.prod nu,
      ‖Function.uncurry E p‖ ≤ g p.1 * 1 := by
    have hmem :
        ∀ᵐ p : ℝ × ℝ ∂mu.prod nu,
          p ∈ (Ioi (0 : ℝ) ×ˢ Ioc (0 : ℝ) 1) := by
      dsimp only [mu, nu]
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)
    filter_upwards [hmem] with p hp
    rcases p with ⟨L, u⟩
    have hLIoi : L ∈ Ioi (0 : ℝ) := by simpa using hp.1
    have huIoc : u ∈ Ioc (0 : ℝ) 1 := by simpa using hp.2
    have hL : 0 < L := hLIoi
    have hu : u ∈ Icc (0 : ℝ) 1 := ⟨huIoc.1.le, huIoc.2⟩
    have hsin :
        ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ ≤ 1 := by
      rw [show (2 * (Real.pi : ℂ)) * (u : ℂ) =
          ((2 * Real.pi * u : ℝ) : ℂ) by
        push_cast
        ring]
      rw [← Complex.ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hcos := norm_cos_real_mul_le_exp_abs_im z hL hu
    have hre : (-s * (L : ℂ)).re = -(s.re * L) := by
      simp [mul_re]
    dsimp only [E, g, Function.uncurry_apply_pair]
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_real,
      Complex.norm_exp, hre, Real.norm_eq_abs, abs_of_pos hL]
    calc
      ‖Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ))‖ *
          (Real.exp (-(s.re * L)) * L ^ 2 *
            ‖Complex.cos ((L : ℂ) * z * (u : ℂ))‖) ≤
        1 * (Real.exp (-(s.re * L)) * L ^ 2 *
          Real.exp (|z.im| * L)) := by gcongr
      _ = L ^ 2 * Real.exp (-(eta * L)) * 1 := by
        rw [show
          1 * (Real.exp (-(s.re * L)) * L ^ 2 *
            Real.exp (|z.im| * L)) =
          L ^ 2 * (Real.exp (-(s.re * L)) *
            Real.exp (|z.im| * L)) by ring]
        rw [← Real.exp_add]
        dsimp only [eta]
        ring_nf
  have hprod : Integrable (Function.uncurry E) (mu.prod nu) :=
    Integrable.mono' hbase hEmeas hEbound
  have hswap := integral_integral_swap hprod
  have hinnerL : ∀ u ∈ Ioc (0 : ℝ) 1,
      (∫ L : ℝ in Ioi 0, E L u) =
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          (1 / (s - I * z * (u : ℂ)) ^ 3 +
            1 / (s + I * z * (u : ℂ)) ^ 3) := by
    intro u hu
    rw [show (∫ L : ℝ in Ioi 0, E L u) =
        Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
          ∫ L : ℝ in Ioi 0,
            Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
              Complex.cos ((L : ℂ) * z * (u : ℂ)) by
      dsimp only [E]
      rw [integral_const_mul]]
    rw [integral_sq_cexp_cos hs ⟨hu.1.le, hu.2⟩]
  have hswap' :
      (∫ L : ℝ in Ioi 0, ∫ u : ℝ in Ioc 0 1, E L u) =
        ∫ u : ℝ in Ioc 0 1, ∫ L : ℝ in Ioi 0, E L u := by
    simpa only [mu, nu, Function.uncurry_apply_pair] using hswap
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  rw [ccmFirstClockLaplaceContinuationAtom]
  simp only [intervalIntegral.integral_of_le h01]
  calc
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
        (-(1 / (2 * (Real.pi : ℂ))) *
          ∫ u : ℝ in Ioc 0 1,
            Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
              Complex.cos ((L : ℂ) * z * (u : ℂ)))) =
      -(1 / (2 * (Real.pi : ℂ))) *
        ∫ L : ℝ in Ioi 0, ∫ u : ℝ in Ioc 0 1, E L u := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with L
          dsimp only [E]
          rw [show
              (∫ u : ℝ in Ioc 0 1,
                Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                  (Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2 *
                    Complex.cos ((L : ℂ) * z * (u : ℂ)))) =
                (Complex.exp (-s * (L : ℂ)) * (L : ℂ) ^ 2) *
                  ∫ u : ℝ in Ioc 0 1,
                    Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
                      Complex.cos ((L : ℂ) * z * (u : ℂ)) by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with u
            ring]
          ring
    _ = -(1 / (2 * (Real.pi : ℂ))) *
        ∫ u : ℝ in Ioc 0 1, ∫ L : ℝ in Ioi 0, E L u := by rw [hswap']
    _ = -(1 / (2 * (Real.pi : ℂ))) *
        ∫ u : ℝ in Ioc 0 1,
          Complex.sin ((2 * (Real.pi : ℂ)) * (u : ℂ)) *
            (1 / (s - I * z * (u : ℂ)) ^ 3 +
              1 / (s + I * z * (u : ℂ)) ^ 3) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact hinnerL u hu

private theorem firstClock_exceptional_set_finite
    {z : ℂ} (hz : z ≠ 0) :
    ({L : ℝ |
      ((L : ℂ) * z) ^ 2 = (2 * (Real.pi : ℂ)) ^ 2} : Set ℝ).Finite := by
  let roots : Set ℂ :=
    {(2 * (Real.pi : ℂ)), -(2 * (Real.pi : ℂ))}
  have hroots : roots.Finite := by
    dsimp only [roots]
    exact Set.finite_insert.mpr (Set.finite_singleton _)
  have hsubset :
      {w : ℂ | w ^ 2 = (2 * (Real.pi : ℂ)) ^ 2} ⊆ roots := by
    intro w hw
    rcases eq_or_eq_neg_of_sq_eq_sq w (2 * (Real.pi : ℂ)) hw with h | h
    · simp [roots, h]
    · simp [roots, h]
  have hfiniteRoots :
      ({w : ℂ | w ^ 2 = (2 * (Real.pi : ℂ)) ^ 2} : Set ℂ).Finite :=
    hroots.subset hsubset
  let f : ℝ → ℂ := fun L => (L : ℂ) * z
  have hinj : Function.Injective f := by
    intro a b hab
    dsimp only [f] at hab
    apply Complex.ofReal_injective
    exact mul_right_cancel₀ hz hab
  have hpre := hfiniteRoots.preimage hinj.injOn
  simpa only [f, Set.preimage_setOf_eq] using hpre

/-- The literal CCM first-clock rational kernel has the cubic compact-kernel transform.
The two apparent dilation singularities form a finite null set, so no regularization
hypothesis enters the identity. -/
theorem integral_exp_mul_ccmFirstClockRationalKernel_eq_atom
    {s z : ℂ} (hz : z ≠ 0) (hs : |z.im| < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) *
        ccmFirstClockRationalKernel L z) =
      ccmFirstClockLaplaceContinuationAtom s z := by
  rw [← integral_exp_mul_compact_firstClock_eq_atom hs]
  apply integral_congr_ae
  have hexc :
      ∀ᵐ L : ℝ ∂volume.restrict (Ioi 0),
        L ∉ {L : ℝ |
          ((L : ℂ) * z) ^ 2 = (2 * (Real.pi : ℂ)) ^ 2} :=
    ae_restrict_of_ae (s := Ioi 0)
      ((firstClock_exceptional_set_finite hz).countable.ae_notMem volume)
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hexc] with L hL hexcL
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hden :
      ((L : ℂ) * z) ^ 2 ≠ (2 * (Real.pi : ℂ)) ^ 2 := by
    exact fun h => hexcL h
  rw [ccmFirstClockRationalKernel_eq_dilation hL0,
    ccmFirstClockFixedCompactKernel_eq_cosineIntegral hden]
  ring

/-- Every multiplicity copy of the Xi divisor satisfies the exact first-clock transform
throughout the unconditional half-plane `Re s > 1/2`. -/
theorem integral_exp_mul_ccmFirstClockRationalKernel_xiSpectralPoint
    (q : XiZeroCopy) {s : ℂ} (hsHalf : 1 / 2 < s.re) :
    (∫ L : ℝ in Ioi 0,
      Complex.exp (-s * (L : ℂ)) *
        ccmFirstClockRationalKernel L (xiSpectralPoint q)) =
      ccmFirstClockLaplaceContinuationAtom s (xiSpectralPoint q) := by
  apply integral_exp_mul_ccmFirstClockRationalKernel_eq_atom
    (xiSpectralPoint_ne_zero q)
  have hstrip := xiSpectralPoint_im_mem_openHalf q
  rw [abs_lt]
  constructor <;> linarith

end

end RHTower
