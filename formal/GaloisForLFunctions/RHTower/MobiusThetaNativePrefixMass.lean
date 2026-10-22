import GaloisForLFunctions.RHTower.MobiusThetaNativeMeyerAdmission
import GaloisForLFunctions.RHTower.Deninger.DeningerAdiabaticGreenStokes
import GaloisForLFunctions.RHTower.Deninger.DeningerEvenPreimageMassZero

/-!
# The original prime-prefix contribution to the native horizontal boundary

The actual even radial tail is absolutely integrable: it is the all-integer
Möbius preimage minus its unchanged finite prefix, away from the measure-zero
origin. The all-integer preimage has zero mass. Dilation and reflection give
the exact prefix mass, and the native Mellin identity identifies its theta
factor with the original Xi jet at `i(1/2-1/m)`, including the Jacobian `1/m`.
Consequently its Fourier value at zero is
`-(2/m) * (sum_{n<p} mu(n)/n) * Xi^(k)(i(1/2-1/m))`.

This retains the original prime anchor; it does not add a compensating source
or assert agreement of the fixed Gamma/BV readers.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction
open scoped SchwartzMap
noncomputable section
namespace RHTower

/-- The complete original prime-anchored tail in the physical radial coordinate. -/
def mobiusThetaNativeCollarTail (k p : ℕ) (m : ℕ+) (x : ℝ) : ℂ :=
  ∑' j : ℕ, ((moebius (p + j) : ℤ) : ℂ) *
    deningerLogPull (mobiusThetaNativeCollarSource k m) (((p + j : ℕ) : ℝ) * |x|)

theorem mobiusThetaNativeCollarTail_at_log_coordinate
    (k p : ℕ) (m : ℕ+) (x : ℝ) :
    mobiusThetaNativeCollarTail k p m (Real.exp (-x / (m : ℝ))) =
      (Real.exp (x / 2) : ℂ) * mobiusThetaInternalJetRawResidualSource k p m x := by
  rw [mobiusThetaNativeCollarTail, abs_of_pos (Real.exp_pos _)]
  exact mobiusThetaNativeCollarSource_tail_reconstruction k p m x

private theorem tail_eq_sub (k p : ℕ) (m : ℕ+) {x : ℝ} (hx : x ≠ 0) :
    mobiusThetaNativeCollarTail k p m x =
      deningerEvenPreimage (mobiusThetaNativeCollarSource k m) x -
        ∑ n ∈ Finset.range p, ((moebius n : ℤ) : ℂ) *
          deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeMeyerSource k m) n x := by
  have hs := deningerMobiusRay_summable
    (mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m) (abs_pos.mpr hx)
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm]
  simpa only [mobiusThetaNativeCollarTail, deningerEvenPreimage,
    deningerMobiusPreimage, deningerAdiabaticEvenLogPullDilation,
    mobiusThetaNativeMeyerSource_toSource, Nat.add_comm]
    using hs.sum_add_tsum_nat_add p

private theorem term_integrable (k : ℕ) (m : ℕ+) (n : ℕ) :
    Integrable (fun x : ℝ => ((moebius n : ℤ) : ℂ) *
      deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeMeyerSource k m) n x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (deningerAdiabaticEvenLogPullDilation_integrable
      (mobiusThetaNativeMeyerSource k m) hn).const_mul _

private theorem tail_eq_sub_ae (k p : ℕ) (m : ℕ+) :
    mobiusThetaNativeCollarTail k p m =ᵐ[volume]
      (fun x => deningerEvenPreimage (mobiusThetaNativeCollarSource k m) x -
        ∑ n ∈ Finset.range p, ((moebius n : ℤ) : ℂ) *
          deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeMeyerSource k m) n x) := by
  filter_upwards [deningerCompl_zero_ae_univ] with x hx
  have hxmem : x ∈ ({(0 : ℝ)}ᶜ : Set ℝ) := hx.mpr (Set.mem_univ x)
  have hx0 : x ≠ 0 := by simpa using hxmem
  exact tail_eq_sub k p m hx0

/-- Absolute integrability of the complete original radial tail. -/
theorem mobiusThetaNativeCollarTail_integrable (k p : ℕ) (m : ℕ+) :
    Integrable (mobiusThetaNativeCollarTail k p m) := by
  have hsum := integrable_finsetSum (Finset.range p)
    (fun n _ => term_integrable k m n)
  exact ((deningerEvenPreimage_integrable
    (mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m)).sub hsum).congr
      (tail_eq_sub_ae k p m).symm

private theorem integral_even_eq (g : ℝ → ℂ) (hg : Integrable g)
    (he : ∀ x, g (-x) = g x) :
    (∫ x : ℝ, g x) = 2 * ∫ x in Set.Ioi (0 : ℝ), g x := by
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (hg.integrableOn : IntegrableOn g (Set.Iic 0))
    (hg.integrableOn : IntegrableOn g (Set.Ioi 0))
  have href := integral_comp_neg_Ioi (0 : ℝ) g
  rw [neg_zero] at href
  have heq : (∫ x in Set.Ioi (0 : ℝ), g (-x)) = ∫ x in Set.Ioi (0 : ℝ), g x :=
    setIntegral_congr_fun measurableSet_Ioi fun x _ => he x
  rw [← hsplit, ← href, heq]
  ring

private theorem term_integral (k : ℕ) (m : ℕ+) (n : ℕ) :
    (∫ x : ℝ, ((moebius n : ℤ) : ℂ) *
      deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeMeyerSource k m) n x) =
        (2 * ((moebius n : ℤ) : ℂ) / (n : ℂ)) *
          deningerPullMass (mobiusThetaNativeCollarSource k m) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [integral_const_mul, integral_even_eq _
    (deningerAdiabaticEvenLogPullDilation_integrable (mobiusThetaNativeMeyerSource k m) hn)
    (deningerAdiabaticEvenLogPullDilation_even _ _)]
  have hpos : (∫ x in Set.Ioi (0 : ℝ),
      deningerAdiabaticEvenLogPullDilation (mobiusThetaNativeMeyerSource k m) n x) =
      (n : ℝ)⁻¹ • deningerPullMass (mobiusThetaNativeCollarSource k m) := by
    rw [← deningerLogPull_dilation_integral (mobiusThetaNativeCollarSource k m) hnR]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    change deningerLogPull _ ((n : ℝ) * |x|) = deningerLogPull _ ((n : ℝ) * x)
    rw [abs_of_pos hx]
    rfl
  rw [hpos, real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

/-- The original prime cutoff leaves exactly the negative mass of its finite prefix. -/
theorem mobiusThetaNativeCollarTail_integral_eq_prefix_mass
    (k p : ℕ) (m : ℕ+) :
    (∫ x : ℝ, mobiusThetaNativeCollarTail k p m x) =
      -2 * (∑ n ∈ Finset.range p, ((moebius n : ℤ) : ℂ) / (n : ℂ)) *
        deningerPullMass (mobiusThetaNativeCollarSource k m) := by
  have hsum := integrable_finsetSum (Finset.range p)
    (fun n _ => term_integrable k m n)
  rw [integral_congr_ae (tail_eq_sub_ae k p m),
    integral_sub (deningerEvenPreimage_integrable
      (mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m)) hsum,
    deningerEvenPreimage_integral_zero
      (mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m),
    integral_finsetSum _ (fun n _ => term_integrable k m n)]
  simp_rw [term_integral, mul_div_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

/-- The native point at which its radial mass reads the original Xi jet. -/
def mobiusThetaNativeMassParameter (m : ℕ+) : ℂ :=
  I * ((1 / 2 - (m : ℝ)⁻¹ : ℝ) : ℂ)

/-- The actual radial mass, with its native scale and change-of-variable factor. -/
theorem mobiusThetaNativeCollarSource_pullMass (k : ℕ) (m : ℕ+) :
    deningerPullMass (mobiusThetaNativeCollarSource k m) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast m.pos
  have hi0 : 0 < (m : ℝ)⁻¹ := inv_pos.mpr hmR
  have hi1 : (m : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hmR).mpr hm1
  have hv : |(mobiusThetaNativeMassParameter m).im| < 1 := by
    simp only [mobiusThetaNativeMassParameter, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
    rw [abs_lt]
    constructor <;> linarith
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast m.ne_zero
  have hparam : (m : ℂ) * mobiusThetaCenteredParameter (mobiusThetaNativeMassParameter m) = 1 := by
    have hiv : I * mobiusThetaNativeMassParameter m = (m : ℂ)⁻¹ - 1 / 2 := by
      dsimp [mobiusThetaNativeMassParameter]
      push_cast
      calc
        _ = I ^ (2 : ℕ) * (1 / 2 - (m : ℂ)⁻¹) := by ring
        _ = _ := by rw [I_sq]; ring
    rw [mobiusThetaCenteredParameter, hiv]
    field_simp
    ring
  have hdata := (mobiusThetaNativeCollarSource_mellin_data k m hv).2
  rw [hparam] at hdata
  rw [deningerPullMass, ← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  convert hdata using 1
  congr 1
  funext t
  simp only [deningerLogPull, Real.log_exp, abs_of_pos (Real.exp_pos _),
    one_mul, ← Complex.ofReal_exp, real_smul]

/-- Exact horizontal Fourier reading of the complete original prime-anchored source. -/
theorem mobiusThetaNativeCollarTail_fourier_zero (k p : ℕ) (m : ℕ+) :
    FourierTransform.fourier (mobiusThetaNativeCollarTail k p m) 0 =
      -2 * (∑ n ∈ Finset.range p, ((moebius n : ℤ) : ℂ) / (n : ℂ)) *
        (m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
  rw [mobiusThetaNativeCollarTail_integral_eq_prefix_mass,
    mobiusThetaNativeCollarSource_pullMass]
  ring

end RHTower
