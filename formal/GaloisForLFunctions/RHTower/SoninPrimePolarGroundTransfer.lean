import GaloisForLFunctions.RHTower.SoninDilationResolventEnergy
import GaloisForLFunctions.RHTower.SoninPrimePolarSignedEnergy
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# All Taylor columns from the native prime–polar ground source

The physical dilation resolvent sends the ground cutoff to every absolute
monomial after its affine transform. An isometric half-line parity multiplier
recovers each actual signed monomial. Both operators commute with the original
prime–polar source, giving an exact positive energy defect for every native
tail, simultaneously in all Taylor degrees. Arithmetic ground-tail decay is
not assumed or proved here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RHTower

private theorem integral_abs_pow_central (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (∫ x in Icc (-a) a, |x| ^ n) = 2 * a^(n+1) / (n+1) := by
  have hc : Continuous (fun x : ℝ => |x|^n) := continuous_abs.pow n
  have half : (∫ x in (0 : ℝ)..a, |x|^n) = a^(n+1)/(n+1) := by
    calc
      _ = ∫ x in (0 : ℝ)..a, x^n := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le ha] at hx
        change |x|^n = x^n
        rw [abs_of_nonneg hx.1]
      _ = _ := by rw [integral_pow]; simp
  have hreflect : (∫ x in -a..(0 : ℝ), |x|^n) = ∫ x in (0 : ℝ)..a, |x|^n := by
    have h := intervalIntegral.integral_comp_neg (fun x : ℝ => |x|^n) (a := (0 : ℝ)) (b := a)
    simpa only [abs_neg, neg_zero] using h.symm
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (neg_le_self ha),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-a) 0)
      (hc.intervalIntegrable 0 a), hreflect, half]
  ring

private theorem absMonomial_memLp (a : ℝ) (n : ℕ) :
    MemLp ((Icc (-a) a).indicator fun x : ℝ => ((|x|^n : ℝ) : ℂ)) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply MemLp.of_bound (by fun_prop) (a^n)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) n

private def absMonomial (a : ℝ) (n : ℕ) : SoninL2 := (absMonomial_memLp a n).toLp _

private theorem absMonomial_ae (a : ℝ) (n : ℕ) :
    (absMonomial a n : ℝ → ℂ) =ᵐ[volume]
      (Icc (-a) a).indicator (fun x : ℝ => ((|x|^n : ℝ) : ℂ)) :=
  (absMonomial_memLp a n).coeFn_toLp

private theorem inner_absMonomial (a : ℝ) (ha : 0 ≤ a) (m n : ℕ) :
    inner ℂ (absMonomial a m) (absMonomial a n) =
      ((2*a^(m+n+1)/(m+n+1) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x in Icc (-a) a, ((|x|^(m+n) : ℝ) : ℂ) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [absMonomial_ae a m, absMonomial_ae a n] with x hm hn
      rw [hm, hn]
      by_cases hx : x ∈ Icc (-a) a
      · simp only [indicator_of_mem hx, RCLike.inner_apply, Complex.conj_ofReal]
        push_cast
        rw [pow_add]
        ring
      · simp [indicator_of_notMem hx]
    _ = _ := by rw [integral_complex_ofReal, integral_abs_pow_central a ha (m+n)]; push_cast; rfl

private theorem inner_dilation_ground_abs (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (r : ℝ) (hr : 0 < r) (h1r : 1 ≤ r) :
    inner ℂ (dilation r hr (soninCutoffMonomial a 0)) (absMonomial a n) =
      ((Real.sqrt r * (2*(a/r)^(n+1)/(n+1)) : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hm := (soninCutoffMonomial_ae a 0).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  calc
    _ = ∫ x in Icc (-(a/r)) (a/r), ((Real.sqrt r * |x|^n : ℝ) : ℂ) := by
      rw [← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [dilation_ae r hr (soninCutoffMonomial a 0), hm,
        absMonomial_ae a n] with x hd hm hg
      change soninCutoffMonomial a 0 (r*x) = _ at hm
      simp only [Function.comp_apply] at hm
      rw [hd, hm, hg]
      have hs : x ∈ Icc (-(a/r)) (a/r) ↔ r*x ∈ centralInterval a := by
        change (-(a/r) ≤ x ∧ x ≤ a/r) ↔ (-a ≤ r*x ∧ r*x ≤ a)
        rw [← abs_le, ← abs_le, abs_mul, abs_of_pos hr, le_div_iff₀ hr]
        rw [mul_comm |x| r]
      by_cases hx : x ∈ Icc (-(a/r)) (a/r)
      · have hax : x ∈ Icc (-a) a := by
          apply abs_le.mp
          exact (abs_le.mpr hx).trans ((div_le_self ha h1r))
        rw [indicator_of_mem hx, indicator_of_mem (hs.mp hx), indicator_of_mem hax]
        simp only [pow_zero, mul_one, RCLike.inner_apply, Complex.conj_ofReal]
        push_cast
        ring
      · rw [indicator_of_notMem hx, indicator_of_notMem (mt hs.mpr hx), mul_zero]
        simp
    _ = _ := by
      rw [integral_complex_ofReal, integral_const_mul,
        integral_abs_pow_central (a/r) (div_nonneg ha hr.le)]

private theorem inner_log_ground_abs (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (t : ℝ) (ht : 0 ≤ t) :
    inner ℂ (dilationCLM (Real.exp t) (Real.exp_pos t) (soninCutoffMonomial a 0)) (absMonomial a n) =
      ((2*a^(n+1)/(n+1) * Real.exp (-((n:ℝ)+1/2)*t) : ℝ) : ℂ) := by
  rw [dilationCLM_apply,
    inner_dilation_ground_abs a ha n _ (Real.exp_pos _) (Real.one_le_exp_iff.mpr ht)]
  have hs : Real.sqrt (Real.exp t) = Real.exp (t/2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
    rw [Real.sq_sqrt (Real.exp_pos _).le, ← Real.exp_nat_mul]
    congr 1
    ring
  congr 1
  rw [hs, div_pow, ← Real.exp_nat_mul]
  have he : Real.exp (t/2) / Real.exp ((n+1 : ℕ)*t) =
      Real.exp (-((n:ℝ)+1/2)*t) := by
    rw [← Real.exp_sub]
    congr 1
    push_cast
    ring
  calc
    _ = (2*a^(n+1)/(n+1)) * (Real.exp (t/2) / Real.exp ((n+1 : ℕ)*t)) := by ring
    _ = _ := by rw [he]


/-- Parity on the negative half-line, with a modulus-one choice at zero. -/
def soninParityMultiplier (n : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (Ioi 0) measurableSet_Ioi +
    (-1 : ℂ)^n • (1 - indicatorCutoff (Ioi 0) measurableSet_Ioi)

private theorem soninParityMultiplier_ae (n : ℕ) (f : SoninL2) :
    (soninParityMultiplier n f : ℝ → ℂ) =ᵐ[volume]
      fun x => (if 0 < x then 1 else (-1 : ℂ)^n) * f x := by
  let P := indicatorCutoff (Ioi 0) measurableSet_Ioi
  change ((P f + (-1 : ℂ)^n • (f-P f) : SoninL2) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add (P f) ((-1 : ℂ)^n • (f-P f)),
    Lp.coeFn_smul ((-1 : ℂ)^n) (f-P f), Lp.coeFn_sub f (P f),
    indicatorCutoff_ae (Ioi 0) measurableSet_Ioi f] with x hadd hsmul hsub hcut
  change _ = (-1 : ℂ)^n * (f-P f) x at hsmul
  simp only [Pi.add_apply, Pi.sub_apply] at hadd hsub
  rw [hadd, hsmul, hsub, hcut]
  by_cases hx : 0 < x
  · simp [hx]
  · simp [hx]

/-- The parity switch preserves the full physical norm. -/
theorem norm_soninParityMultiplier (n : ℕ) (f : SoninL2) :
    ‖soninParityMultiplier n f‖ = ‖f‖ := by
  have h : ∀ᵐ x ∂volume, ‖soninParityMultiplier n f x‖ = ‖f x‖ := by
    filter_upwards [soninParityMultiplier_ae n f] with x hx
    rw [hx, norm_mul]
    split_ifs <;> simp
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.le))
    (Lp.norm_le_norm_of_ae_le (h.mono fun _ hx => hx.ge))

/-- Positive physical dilation preserves parity on each half-line. -/
theorem soninParityMultiplier_dilation (n : ℕ) (r : ℝ) (hr : 0 < r) (f : SoninL2) :
    soninParityMultiplier n (dilation r hr f) = dilation r hr (soninParityMultiplier n f) := by
  apply Lp.ext
  have hp := (soninParityMultiplier_ae n f).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  filter_upwards [soninParityMultiplier_ae n (dilation r hr f),
    dilation_ae r hr f, dilation_ae r hr (soninParityMultiplier n f), hp]
      with x hl hd hrhs hp
  change soninParityMultiplier n f (r*x) = _ at hp
  simp only [Function.comp_apply] at hp
  rw [hl, hd, hrhs, hp]
  have hx : 0 < r*x ↔ 0 < x := mul_pos_iff_of_pos_left hr
  simp only [hx]
  ring

private theorem parity_absMonomial (a : ℝ) (n : ℕ) :
    soninParityMultiplier n (absMonomial a n) = soninCutoffMonomial a n := by
  apply Lp.ext
  filter_upwards [soninParityMultiplier_ae n (absMonomial a n), absMonomial_ae a n,
    soninCutoffMonomial_ae a n] with x hp ha hm
  rw [hp, ha, hm]
  by_cases hx : x ∈ Icc (-a) a
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ centralInterval a from hx)]
    by_cases hx0 : 0 < x
    · simp [hx0, abs_of_pos hx0]
    · simp only [hx0, ite_false, abs_of_nonpos (le_of_not_gt hx0)]
      push_cast
      rw [← mul_pow]
      congr 1
      ring
  · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ centralInterval a from hx), mul_zero]


private theorem resolvent_orbit_integrable (lam : ℝ) (hlam : 0 < lam) (f : SoninL2) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam*t) • rayDilate (Real.exp t) f) (Ioi 0) volume := by
  apply Integrable.mono' ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hlam) 0).mul_const ‖f‖)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      (continuous_dilationOrbit f)).aestronglyMeasurable.restrict
  filter_upwards [] with t
  change ‖Real.exp (-lam*t) • rayDilate (Real.exp t) f‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_rayDilate (Real.exp_pos _)]

private theorem resolvent_inner_abs (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (lam : ℝ) (hlam : 0 < lam) :
    inner ℂ (soninDilationResolvent lam hlam (soninCutoffMonomial a 0))
      (absMonomial a n) =
      ((2*a^(n+1)/((n+1)*(lam+(n:ℝ)+1/2)) : ℝ) : ℂ) := by
  rw [soninDilationResolvent_apply]
  rw [← inner_conj_symm, ← integral_inner (resolvent_orbit_integrable lam hlam _), ← integral_conj]
  have hp : 0 < lam + (n:ℝ) + 1/2 := by positivity
  calc
    _ = ∫ t in Ioi (0:ℝ),
        ((2*a^(n+1)/(n+1) * Real.exp (-(lam+(n:ℝ)+1/2)*t) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [← inner_conj_symm]
      simp only [starRingEnd_apply, star_star]
      rw [rayDilate_of_pos (Real.exp_pos _)]
      change inner ℂ ((Real.exp (-lam*t) : ℂ) • dilationCLM (Real.exp t) (Real.exp_pos t) (soninCutoffMonomial a 0)) _ = _
      rw [inner_smul_left, inner_log_ground_abs a ha n t (le_of_lt ht), Complex.conj_ofReal]
      rw [← Complex.ofReal_mul]
      congr 1
      have he : Real.exp (-lam*t) * Real.exp (-((n:ℝ)+1/2)*t) =
          Real.exp (-(lam+(n:ℝ)+1/2)*t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2*a^(n+1)/(n+1)) * (Real.exp (-lam*t) * Real.exp (-((n:ℝ)+1/2)*t)) := by ring
        _ = _ := by rw [he]
    _ = _ := by
      rw [integral_complex_ofReal, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hp) 0]
      congr 1
      simp only [mul_zero, Real.exp_zero]
      field_simp


private theorem absMonomial_zero (a : ℝ) : absMonomial a 0 = soninCutoffMonomial a 0 := by
  apply Lp.ext
  filter_upwards [absMonomial_ae a 0, soninCutoffMonomial_ae a 0] with x ha hs
  rw [ha, hs]
  simp only [pow_zero, Complex.ofReal_one]
  rfl

private theorem norm_sq_absMonomial (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖absMonomial a n‖^2 = 2*a^(2*n+1)/(2*n+1) := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_absMonomial a ha n n]
  change 2*a^(n+n+1)/((n:ℝ)+n+1) = _
  simp only [← two_mul]

/-- Exact physical mass of every actual cutoff Taylor output. -/
theorem norm_sq_soninCutoffMonomial (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninCutoffMonomial a n‖^2 = 2*a^(2*n+1)/(2*n+1) := by
  rw [← parity_absMonomial, norm_soninParityMultiplier]
  exact norm_sq_absMonomial a ha n

private theorem norm_sq_ground (a : ℝ) (ha : 0 ≤ a) :
    ‖soninCutoffMonomial a 0‖^2 = 2*a := by
  simpa only [absMonomial_zero, mul_zero, zero_add, pow_one, Nat.cast_zero,
    Nat.cast_one, div_one] using norm_sq_absMonomial a ha 0

private theorem norm_sq_resolvent_ground (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (soninCutoffMonomial a 0)‖^2 =
      4*a/(((n:ℝ)+1)*(2*n+1)) := by
  have h := soninDilationResolvent_real_energy ((n:ℝ)+1/2) (by positivity)
    (soninCutoffMonomial a 0)
  have hi := resolvent_inner_abs a ha 0 ((n:ℝ)+1/2) (by positivity)
  rw [absMonomial_zero] at hi
  rw [hi, Complex.ofReal_re] at h
  simp only [Nat.cast_zero, zero_add, pow_one, one_mul] at h
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hn' : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith [h]

private theorem norm_sq_transfer_ground (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    ‖soninMonomialTransfer n (soninCutoffMonomial a 0)‖^2 = 2*a/(2*n+1) := by
  have h := soninMonomialTransfer_energy n (soninCutoffMonomial a 0)
  rw [norm_sq_resolvent_ground a ha n, norm_sq_ground a ha] at h
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hn' : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp at h ⊢
  nlinarith [h]

private theorem inner_transfer_ground_abs (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    inner ℂ (soninMonomialTransfer n (soninCutoffMonomial a 0)) (absMonomial a n) =
      ((2*a^(n+1)/(2*n+1) : ℝ) : ℂ) := by
  change inner ℂ (soninCutoffMonomial a 0 -
    (n:ℂ) • soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (soninCutoffMonomial a 0)) _ = _
  rw [inner_sub_left, inner_smul_left, resolvent_inner_abs a ha n]
  rw [← absMonomial_zero a, inner_absMonomial a ha 0 n]
  simp only [Nat.cast_zero, zero_add, map_natCast]
  norm_cast
  have hn : (n:ℝ)+1 ≠ 0 := by positivity
  have hn' : 2*(n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  push_cast
  ring

private theorem transfer_ground_abs (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (a^n : ℝ) • soninMonomialTransfer n (soninCutoffMonomial a 0) = absMonomial a n := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sq_transfer_ground a ha n, norm_sq_absMonomial a ha n]
  have hi : (inner ℂ ((a^n:ℝ) • soninMonomialTransfer n (soninCutoffMonomial a 0))
      (absMonomial a n)).re = a^n * (2*a^(n+1)/(2*n+1)) := by
    change (inner ℂ (((a^n:ℝ):ℂ) • soninMonomialTransfer n (soninCutoffMonomial a 0)) _).re = _
    rw [inner_smul_left, inner_transfer_ground_abs a ha n, Complex.conj_ofReal, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

  change _ - 2 * (inner ℂ ((a^n:ℝ) • soninMonomialTransfer n (soninCutoffMonomial a 0))
      (absMonomial a n)).re + _ = 0
  rw [hi]
  have hp : a^(2*n+1) = (a^n)^2*a := by rw [pow_add, pow_mul]; ring
  rw [hp, pow_succ]
  ring

/-- Every actual Taylor output is an isometric parity transform of the
same ground vector, through the explicitly constructed dilation resolvent. -/
theorem soninMonomialTransfer_cutoff (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    soninCutoffMonomial a n =
      (a^n : ℝ) • soninParityMultiplier n
        (soninMonomialTransfer n (soninCutoffMonomial a 0)) := by
  rw [← ContinuousLinearMap.map_smul_of_tower, transfer_ground_abs a ha n,
    parity_absMonomial]


/-- Every monomial transfer commutes with the original logarithmic dilation action. -/
theorem soninMonomialTransfer_dilation (n : ℕ) (t : ℝ) (f : SoninL2) :
    soninMonomialTransfer n (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp t) (soninMonomialTransfer n f) := by
  change rayDilate (Real.exp t) f - (n:ℝ) •
    soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (rayDilate (Real.exp t) f) = _
  rw [soninDilationResolvent_commutes]
  simp only [rayDilate_of_pos (Real.exp_pos _)]
  change _ = dilationCLM (Real.exp t) (Real.exp_pos t)
    (f - (n:ℝ) • soninDilationResolvent ((n:ℝ)+1/2) (by positivity) f)
  rw [map_sub, ContinuousLinearMap.map_smul_of_tower]
  rfl

private theorem polar_orbit_integrable (b R sign : ℝ) (hb : 0 < b) (f : SoninL2) :
    Integrable (fun u => soninLogPolarDensity u • rayDilate (Real.exp (sign*u)) f)
      (volume.restrict (Icc b R)) := by
  have hd : ContinuousOn soninLogPolarDensity (Icc b R) := by
    intro u hu
    apply ContinuousAt.continuousWithinAt
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le hb hu.1)
    unfold soninLogPolarDensity
    fun_prop
  exact (hd.smul ((continuous_dilationOrbit f).comp
    (continuous_const.mul continuous_id)).continuousOn).integrableOn_Icc


/-- A bounded dilation intertwiner preserves every original finite prime–polar source. -/
theorem soninPrimePolarSourceOperator_commutes (L : SoninL2 →L[ℂ] SoninL2)
    (hL : ∀ t f, L (rayDilate (Real.exp t) f) = rayDilate (Real.exp t) (L f))
    (P : Finset Nat.Primes) (b R sign : ℝ) (hb : 0 < b) (f : SoninL2) :
    L (soninPrimePolarSourceOperator P b R sign hb f) =
      soninPrimePolarSourceOperator P b R sign hb (L f) := by
  rw [soninPrimePolarSourceOperator_apply, soninPrimePolarSourceOperator_apply, map_sub, map_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    rw [map_smul, hL]
  · rw [← L.integral_comp_comm (polar_orbit_integrable b R sign hb f)]
    apply integral_congr_ae
    filter_upwards [] with u
    rw [map_smul, hL]

private theorem parity_log_dilation (n : ℕ) (t : ℝ) (f : SoninL2) :
    soninParityMultiplier n (rayDilate (Real.exp t) f) =
      rayDilate (Real.exp t) (soninParityMultiplier n f) := by
  simp only [rayDilate_of_pos (Real.exp_pos _)]
  exact soninParityMultiplier_dilation n _ (Real.exp_pos _) f

private theorem monomial_energy_of_commutes (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (K : SoninL2 →L[ℂ] SoninL2)
    (hT : ∀ f, K (soninMonomialTransfer n f) = soninMonomialTransfer n (K f))
    (hP : ∀ f, K (soninParityMultiplier n f) = soninParityMultiplier n (K f)) :
    ‖K (soninCutoffMonomial a n)‖^2 +
      a^(2*n) * (n:ℝ)*((n:ℝ)+1) *
        ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (K (soninCutoffMonomial a 0))‖^2 =
      a^(2*n) * ‖K (soninCutoffMonomial a 0)‖^2 := by
  rw [soninMonomialTransfer_cutoff a ha n, ContinuousLinearMap.map_smul_of_tower,
    hP, hT, norm_smul, norm_soninParityMultiplier, Real.norm_eq_abs, mul_pow, sq_abs]
  have h := soninMonomialTransfer_energy n (K (soninCutoffMonomial a 0))
  have hp : a^(2*n) = (a^n)^2 := by rw [mul_comm 2 n, pow_mul]
  rw [hp]
  linear_combination (a^n)^2 * h

/-- Every original signed prime–polar tail has an exact energy decomposition
through its ground column, simultaneously for all Taylor degrees. -/
theorem soninPrimePolar_tail_monomial_energy (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (P Q : Finset Nat.Primes) (b R S sign : ℝ) (hb : 0 < b) :
    let K := soninPrimePolarSourceOperator P b R sign hb -
      soninPrimePolarSourceOperator Q b S sign hb
    ‖K (soninCutoffMonomial a n)‖^2 +
      a^(2*n) * (n:ℝ)*((n:ℝ)+1) *
        ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (K (soninCutoffMonomial a 0))‖^2 =
      a^(2*n) * ‖K (soninCutoffMonomial a 0)‖^2 := by
  dsimp only
  apply monomial_energy_of_commutes a ha n
  · intro f
    simp only [sub_apply, map_sub]
    rw [← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n)]
  · intro f
    simp only [sub_apply, map_sub]
    rw [← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n)]

/-- The full two-direction source obeys the same ground-column law, including
arbitrary differences of finite prime cutoffs and continuum endpoints. -/
theorem soninPrimePolar_symmetric_tail_monomial_energy (a : ℝ) (ha : 0 ≤ a) (n : ℕ)
    (P Q : Finset Nat.Primes) (b R S : ℝ) (hb : 0 < b) :
    let K := (soninPrimePolarSourceOperator P b R 1 hb + soninPrimePolarSourceOperator P b R (-1) hb) -
      (soninPrimePolarSourceOperator Q b S 1 hb + soninPrimePolarSourceOperator Q b S (-1) hb)
    ‖K (soninCutoffMonomial a n)‖^2 +
      a^(2*n) * (n:ℝ)*((n:ℝ)+1) *
        ‖soninDilationResolvent ((n:ℝ)+1/2) (by positivity) (K (soninCutoffMonomial a 0))‖^2 =
      a^(2*n) * ‖K (soninCutoffMonomial a 0)‖^2 := by
  dsimp only
  apply monomial_energy_of_commutes a ha n
  · intro f
    simp only [sub_apply, add_apply, map_sub, map_add]
    rw [← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (soninMonomialTransfer_dilation n)]
  · intro f
    simp only [sub_apply, add_apply, map_sub, map_add]
    rw [← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n),
      ← soninPrimePolarSourceOperator_commutes _ (parity_log_dilation n)]


end RHTower
