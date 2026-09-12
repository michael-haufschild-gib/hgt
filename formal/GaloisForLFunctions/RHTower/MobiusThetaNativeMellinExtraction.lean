import GaloisForLFunctions.RHTower.MobiusThetaNativeFullJetBalance
import Mathlib.Analysis.MellinInversion

/-!
# Original native Mellin readings and their retained prime prefix

The original logarithmic coordinate transfers Fourier–Laplace integrability
and value to the literal Mellin integral, with its Jacobian `1/m`.
At each unchanged Xi divisor this gives cofinal admission and a nonzero
reading of the actual top jet. Absolute Dirichlet summation retains the
finite prime prefix. The same admitted source yields exact positive
moments through a finite window set by the native depth.

These are source comparisons. They do not identify the complete two-collar
boundary with the fixed degree-six Gamma/BV reader.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction Filter Topology Set
open scoped SchwartzMap Moebius LSeries.notation
noncomputable section
namespace RHTower
namespace NativeMellin

private theorem exp_kernel (f : ℝ → ℂ) (s : ℂ) (t : ℝ) :
    (Real.exp t : ℂ) * (((Real.exp t : ℝ) : ℂ) ^ (s - 1) * f (Real.exp t)) =
      Complex.exp (s * (t : ℂ)) * f (Real.exp t) := by
  have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),
    hlog, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  ring

private theorem hasMellin_of_log_integral {f : ℝ → ℂ} {s M : ℂ}
    (hi : Integrable (fun t : ℝ => Complex.exp (s * (t : ℂ)) * f (Real.exp t)))
    (he : (∫ t : ℝ, Complex.exp (s * (t : ℂ)) * f (Real.exp t)) = M) :
    HasMellin f s M := by
  have himage : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi 0 := by
    rw [Set.image_univ, Real.range_exp]
  have hd : ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt Real.exp (Real.exp t) Set.univ t :=
    fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt
  have hfun : (fun t : ℝ => |Real.exp t| •
      (((Real.exp t : ℝ) : ℂ) ^ (s - 1) • f (Real.exp t))) =
      fun t : ℝ => Complex.exp (s * (t : ℂ)) * f (Real.exp t) := by
    funext t
    rw [abs_of_pos (Real.exp_pos t)]
    exact exp_kernel f s t
  constructor
  · rw [MellinConvergent, ← himage,
      integrableOn_image_iff_integrableOn_abs_deriv_smul
        MeasurableSet.univ hd Real.exp_injective.injOn, integrableOn_univ, hfun]
    exact hi
  · rw [mellin, ← himage, integral_image_eq_integral_abs_deriv_smul
      MeasurableSet.univ hd Real.exp_injective.injOn, Measure.restrict_univ, hfun]
    exact he

private theorem log_integrand (k p : ℕ) (m : ℕ+) (v : ℂ) (t : ℝ) :
    Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        mobiusThetaNativeCollarTail k p m (Real.exp t) =
      Complex.exp (-I * v * ((-(m : ℝ) * t : ℝ) : ℂ)) *
        mobiusThetaInternalJetRawResidualSource k p m (-(m : ℝ) * t) := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hc : -(-(m : ℝ) * t) / (m : ℝ) = t := by field_simp
  have htail := mobiusThetaNativeCollarTail_at_log_coordinate k p m (-(m : ℝ) * t)
  rw [hc] at htail
  rw [htail, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  dsimp only [mobiusThetaCenteredParameter]
  push_cast
  ring

private theorem raw_data {p : ℕ} (hp : 0 < p) (k : ℕ) (m : ℕ+)
    {v : ℂ} (hv : |v.im| < 1)
    (hmv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    Integrable (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaInternalJetRawResidualSource k p m x) ∧
    (∫ x : ℝ, Complex.exp (-I * v * (x : ℂ)) *
      mobiusThetaInternalJetRawResidualSource k p m x) =
        mobiusThetaRawResidualMultiplier p m v * iteratedDeriv k XiC v := by
  have h := mobiusThetaRawLocalModulationSource_fourierLaplace_data hp m.ne_zero k
    (v := v) (delta := 0) (by simpa only [add_zero] using hv) hmv
  simpa only [mobiusThetaRawLocalModulationSource, mul_zero, zero_mul, Complex.exp_zero,
    one_mul, mobiusThetaInternalJetRawResidualSource, add_zero] using h

private theorem hasMellin_native {p : ℕ} (hp : 0 < p) (k : ℕ) (m : ℕ+)
    {v : ℂ} (hv : |v.im| < 1)
    (hmv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    HasMellin (mobiusThetaNativeCollarTail k p m)
      ((m : ℂ) * mobiusThetaCenteredParameter v)
      ((m : ℂ)⁻¹ * (mobiusThetaRawResidualMultiplier p m v * iteratedDeriv k XiC v)) := by
  obtain ⟨hi, he⟩ := raw_data hp k m hv hmv
  apply hasMellin_of_log_integral
  · simp_rw [log_integrand]
    exact hi.comp_mul_left' (neg_ne_zero.mpr (show (m : ℝ) ≠ 0 by exact_mod_cast m.ne_zero))
  · simp_rw [log_integrand]
    rw [MeasureTheory.Measure.integral_comp_mul_left
      (fun x : ℝ => Complex.exp (-I * v * (x : ℂ)) *
        mobiusThetaInternalJetRawResidualSource k p m x) (-(m : ℝ)), he]
    simp only [abs_inv, abs_neg, abs_of_pos (show (0 : ℝ) < m by exact_mod_cast m.pos),
      real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]

private theorem pnat_cofinal : Tendsto (fun m : ℕ+ => (m : ℕ)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (⟨b + 1, Nat.succ_pos b⟩ : ℕ+)] with m hm
  exact (Nat.le_succ b).trans (show b + 1 ≤ (m : ℕ) from hm)

private theorem multiplier_prefix {p : ℕ} (m : ℕ+) {v : ℂ}
    (hmv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    mobiusThetaRawResidualMultiplier p m v =
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter v))⁻¹ -
        ∑ n ∈ Finset.range p, LSeries.term (↗(μ : ArithmeticFunction ℤ))
          ((m : ℂ) * mobiusThetaCenteredParameter v) n := by
  have hs := one_lt_natCast_mul_re m.ne_zero hmv
  have hsum := (LSeriesSummable_moebius_iff.mpr hs).sum_add_tsum_nat_add p
  have hz := LSeries_moebius_eq_inv_riemannZeta hs
  change (∑' n : ℕ, LSeries.term (↗(μ : ArithmeticFunction ℤ))
    ((m : ℂ) * mobiusThetaCenteredParameter v) n) = _ at hz
  rw [hz] at hsum
  unfold mobiusThetaRawResidualMultiplier mobiusThetaPrimeRawAmplitude
  simpa only [Nat.add_comm] using eq_sub_of_add_eq' hsum

private theorem raw_ne_zero_of_normal {p m : ℕ} {v : ℂ}
    (hn : mobiusThetaPrimeNormalResidualMultiplier p m v ≠ 0) :
    mobiusThetaRawResidualMultiplier p m v ≠ 0 := by
  have hc : mobiusThetaPrimeNormalResidualMultiplier p m v =
      (p : ℂ) ^ ((m : ℂ) * mobiusThetaCenteredParameter v) *
        mobiusThetaRawResidualMultiplier p m v := by
    unfold mobiusThetaPrimeNormalResidualMultiplier mobiusThetaPrimeNormalResidualSpectralCoefficient
      mobiusThetaRawResidualMultiplier mobiusThetaPrimeRawAmplitude
    rw [tsum_mul_left]
  intro hr
  apply hn
  rw [hc, hr, mul_zero]

end NativeMellin
open NativeMellin

/-- The complete admitted native Mellin formula, with its original finite prefix.
This public form permits continuation arguments to start from an open integral domain. -/
theorem mobiusThetaNativeCollarTail_hasMellin_prefix
    {p : ℕ} (hp : 0 < p) (k : ℕ) (m : ℕ+)
    {v : ℂ} (hv : |v.im| < 1)
    (hmv : 1 / (m : ℝ) < (mobiusThetaCenteredParameter v).re) :
    HasMellin (mobiusThetaNativeCollarTail k p m)
      ((m : ℂ) * mobiusThetaCenteredParameter v)
      ((m : ℂ)⁻¹ *
        (((riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter v))⁻¹ -
          ∑ n ∈ Finset.range p, LSeries.term (↗(μ : ArithmeticFunction ℤ))
            ((m : ℂ) * mobiusThetaCenteredParameter v) n) * iteratedDeriv k XiC v)) := by
  have h := hasMellin_native hp k m hv hmv
  rwa [multiplier_prefix m hmv] at h

/-- Literal native Mellin admission at every original divisor, at all sufficiently large native depths. -/
theorem mobiusThetaNativeCollarTail_hasMellin_at_divisor_cofinal
    (p : Nat.Primes) (k : ℕ) (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      HasMellin (mobiusThetaNativeCollarTail k p m) ((m : ℂ) * (rho : ℂ))
        ((m : ℂ)⁻¹ * (mobiusThetaRawResidualMultiplier p m (xiSpectralPointSupport rho) *
          iteratedDeriv k XiC (xiSpectralPointSupport rho))) := by
  have hpos : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  filter_upwards [pnat_cofinal.eventually
    (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hpos)] with m hm
  have h := hasMellin_native p.property.pos k m (abs_im_xiSpectralPointSupport_lt_one rho) hm.2
  simpa only [mobiusThetaCenteredParameter_xiSpectralPointSupport] using h

/-- The original prime prefix is part of the admitted native Mellin reading. -/
theorem mobiusThetaNativeCollarTail_hasMellin_prefix_at_divisor_cofinal
    (p : Nat.Primes) (k : ℕ) (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      HasMellin (mobiusThetaNativeCollarTail k p m) ((m : ℂ) * (rho : ℂ))
        ((m : ℂ)⁻¹ * (((riemannZeta ((m : ℂ) * (rho : ℂ)))⁻¹ -
          ∑ n ∈ Finset.range p, LSeries.term (↗(μ : ArithmeticFunction ℤ))
            ((m : ℂ) * (rho : ℂ)) n) *
          iteratedDeriv k XiC (xiSpectralPointSupport rho))) := by
  have hpos : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  filter_upwards [mobiusThetaNativeCollarTail_hasMellin_at_divisor_cofinal p k rho,
    pnat_cofinal.eventually
      (eventually_mobiusThetaPrimeNormalResidual_convergenceDomain hpos)] with m hm hd
  have he := multiplier_prefix (p := (p : ℕ)) m hd.2
  rw [mobiusThetaCenteredParameter_xiSpectralPointSupport] at he
  rwa [he] at hm

/-- The literal Mellin read retains the nonzero top Xi jet at cofinal original depths. -/
theorem mobiusThetaNativeCollarTail_top_mellin_ne_zero_cofinal
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ∀ᶠ m : ℕ+ in atTop,
      MellinConvergent (mobiusThetaNativeCollarTail (xiSupportMultiplicity rho) p m)
          ((m : ℂ) * (rho : ℂ)) ∧
      mellin (mobiusThetaNativeCollarTail (xiSupportMultiplicity rho) p m)
          ((m : ℂ) * (rho : ℂ)) ≠ 0 := by
  have hpos : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  filter_upwards [mobiusThetaNativeCollarTail_hasMellin_at_divisor_cofinal p
      (xiSupportMultiplicity rho) rho,
    pnat_cofinal.eventually
      (eventually_mobiusThetaPrimeNormalResidualMultiplier_ne_zero_of_prime p.property hpos)]
    with m hm hn
  refine ⟨hm.1, ?_⟩
  rw [hm.2]
  exact mul_ne_zero (inv_ne_zero (show (m : ℂ) ≠ 0 by exact_mod_cast m.ne_zero))
    (mul_ne_zero (raw_ne_zero_of_normal hn)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))

/-- Source-derived positive moments through the native depth, with the prime prefix retained.
These are admitted integrals, supplying a finite window for Fourier endpoint subtraction. -/
theorem mobiusThetaNativeCollarTail_positive_moment_window
    (p : Nat.Primes) (k : ℕ) (m : ℕ+) (j : Fin (m : ℕ)) :
    let d : ℕ+ := ⟨(m : ℕ) + 1, Nat.succ_pos _⟩
    let r : ℝ := ((j : ℕ) + 2 : ℝ) / ((m : ℕ) + 1 : ℝ)
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ ((j : ℕ) + 1) *
        mobiusThetaNativeCollarTail k p d x) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ ((j : ℕ) + 1) *
        mobiusThetaNativeCollarTail k p d x) =
      (d : ℂ)⁻¹ * (((riemannZeta ((j : ℕ) + 2 : ℂ))⁻¹ -
        ∑ n ∈ Finset.range p, LSeries.term (↗(μ : ArithmeticFunction ℤ))
          ((j : ℕ) + 2 : ℂ) n) * iteratedDeriv k XiC (I * ((1 / 2 - r : ℝ) : ℂ))) := by
  dsimp only
  let d : ℕ+ := ⟨(m : ℕ) + 1, Nat.succ_pos _⟩
  let r : ℝ := ((j : ℕ) + 2 : ℝ) / ((m : ℕ) + 1 : ℝ)
  let v : ℂ := I * ((1 / 2 - r : ℝ) : ℂ)
  have hden : 0 < ((m : ℕ) + 1 : ℝ) := by positivity
  have hr0 : 0 < r := div_pos (by positivity) hden
  have hr1 : r ≤ 1 := by
    apply (div_le_one hden).2
    have hj : (j : ℕ) + 1 ≤ (m : ℕ) := Nat.succ_le_of_lt j.isLt
    have hjr : ((j : ℕ) : ℝ) + 1 ≤ ((m : ℕ) : ℝ) := by exact_mod_cast hj
    linarith
  have hv : |v.im| < 1 := by
    change |(I * ((1 / 2 - r : ℝ) : ℂ)).im| < 1
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, one_mul, zero_add]
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  have hcent : mobiusThetaCenteredParameter v = (r : ℂ) := by
    dsimp only [mobiusThetaCenteredParameter, v]
    push_cast
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  have hdR : (d : ℝ) = ((m : ℕ) : ℝ) + 1 := by
    change (((m : ℕ) + 1 : ℕ) : ℝ) = _
    push_cast
    rfl
  have hdC : (d : ℂ) = ((m : ℕ) : ℂ) + 1 := by
    change (((m : ℕ) + 1 : ℕ) : ℂ) = _
    push_cast
    rfl
  have hdom : 1 / (d : ℝ) < (mobiusThetaCenteredParameter v).re := by
    rw [hcent, Complex.ofReal_re, hdR]
    have hjpos : (1 : ℝ) < ((j : ℕ) : ℝ) + 2 := by
      have := Nat.cast_nonneg (α := ℝ) (j : ℕ)
      linarith
    exact div_lt_div_of_pos_right hjpos hden
  have hparam : (d : ℂ) * mobiusThetaCenteredParameter v = ((j : ℕ) + 2 : ℂ) := by
    rw [hcent, hdC]
    dsimp only [r]
    push_cast
    have hm : (((m : ℕ) : ℂ) + 1) ≠ 0 := by exact_mod_cast hden.ne'
    field_simp
  have h := hasMellin_native p.property.pos k d hv hdom
  rw [multiplier_prefix d hdom, hparam] at h
  have he : ((j : ℕ) + 2 : ℂ) - 1 = (((j : ℕ) + 1 : ℕ) : ℂ) := by push_cast; ring
  simpa only [HasMellin, MellinConvergent, mellin, he, Complex.cpow_natCast,
    smul_eq_mul, d, r, v] using h

end RHTower
