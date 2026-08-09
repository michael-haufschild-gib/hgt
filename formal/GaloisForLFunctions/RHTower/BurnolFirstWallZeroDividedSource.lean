import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.BurnolPrimeTwoCollarSymbol
import GaloisForLFunctions.RHTower.BurnolFirstWallResiduePolarization

/-!
# The zero-divided Burnol source on the positive ray

The fixed prime-two Burnol atom is `f₀(t) = p(t)/t` with `p(t) = fract t - fract 2t`, a
one-periodic mean-zero profile.  Its raw Mellin transform is the Burnol symbol
`H(w) = (2^w - 1) ζ(w)/w`, so at a zero of `ξ` the whole positive-ray moment of the kernel
`p(y) y^{-w-1}` vanishes.

The forward divided shift is `g_ρ(t) = ∫_1^∞ u^{-ρ} f₀(ut) du`.  The substitution `y = ut` turns it
into the tail integral `t^{ρ-1} ∫_t^∞ p(y) y^{-ρ-1} dy`, and the vanishing total moment converts
that tail into a head integral over `(0,t]`.  Below the aperture the profile is `p(y) = -y`, so the
head integral is elementary and the divided shift is the constant `1/(1-ρ)`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The two-scale fractional coboundary -/

/-- The two-scale Haar coboundary of the fractional part. -/
def burnolFractPair (t : ℝ) : ℝ := Int.fract t - Int.fract (2 * t)

theorem burnolFractPair_periodic : Function.Periodic burnolFractPair 1 := by
  intro t
  rw [burnolFractPair, burnolFractPair, Int.fract_add_one,
    show 2 * (t + 1) = 2 * t + 2 by ring]
  congr 1
  have h2 : (2 : ℝ) * t + 2 = 2 * t + ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, Int.fract_add_natCast]

theorem abs_burnolFractPair_le_one (t : ℝ) : |burnolFractPair t| ≤ 1 := by
  rw [burnolFractPair, abs_sub_le_iff]
  constructor
  · linarith [Int.fract_lt_one t, Int.fract_nonneg (2 * t)]
  · linarith [Int.fract_lt_one (2 * t), Int.fract_nonneg t]

/-- Below the aperture `1/2` the coboundary is the identity with a sign. -/
theorem burnolFractPair_of_lt_half {t : ℝ} (ht0 : 0 ≤ t) (ht : t < 1 / 2) :
    burnolFractPair t = -t := by
  have h1 : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht0, by linarith⟩
  have h2 : Int.fract (2 * t) = 2 * t := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [burnolFractPair, h1, h2]
  ring

/-- The Mellin kernel of the coboundary. -/
def burnolFractPairKernel (ρ : ℂ) (y : ℝ) : ℂ :=
  ((burnolFractPair y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 1))

theorem burnolFractPairKernel_eq_sub (ρ : ℂ) (y : ℝ) :
    burnolFractPairKernel ρ y =
      ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 1)) -
        ((Int.fract (2 * y) : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 1)) := by
  rw [burnolFractPairKernel, burnolFractPair, Complex.ofReal_sub]
  ring

theorem integrableOn_burnolFractPairKernel {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    IntegrableOn (burnolFractPairKernel ρ) (Ioi (0 : ℝ)) := by
  have h1 := integrableOn_Ioi_zero_fract_cpow hρ0 hρ1
  have h2 := integrableOn_Ioi_zero_fract_dilate_cpow hρ0 hρ1 (c := (2 : ℝ)) (by norm_num)
  exact (h1.sub h2).congr_fun (fun y _ => (burnolFractPairKernel_eq_sub ρ y).symm)
    measurableSet_Ioi

/-- **The total moment is the Burnol symbol.**  The dyadic dilation contributes the factor `2^ρ`. -/
theorem integral_burnolFractPairKernel {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    (∫ y in Ioi (0 : ℝ), burnolFractPairKernel ρ y) = burnolFixedAtomRawMellin ρ := by
  have h1 := integrableOn_Ioi_zero_fract_cpow hρ0 hρ1
  have h2 := integrableOn_Ioi_zero_fract_dilate_cpow hρ0 hρ1 (c := (2 : ℝ)) (by norm_num)
  have hsplit : (∫ y in Ioi (0 : ℝ), burnolFractPairKernel ρ y) =
      (∫ y in Ioi (0 : ℝ), ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 1))) -
        ∫ y in Ioi (0 : ℝ), ((Int.fract (2 * y) : ℝ) : ℂ) * (y : ℂ) ^ (-(ρ + 1)) := by
    rw [← integral_sub h1 h2]
    exact setIntegral_congr_fun measurableSet_Ioi fun y _ => burnolFractPairKernel_eq_sub ρ y
  rw [hsplit, integral_Ioi_zero_fract_cpow hρ0 hρ1,
    integral_Ioi_zero_fract_dilate_cpow hρ0 hρ1 (c := (2 : ℝ)) (by norm_num),
    burnolFixedAtomRawMellin]
  push_cast
  ring

/-- **At a zero of `ξ` the total moment vanishes.** -/
theorem xiDivisor_integral_burnolFractPairKernel_eq_zero {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    (∫ y in Ioi (0 : ℝ), burnolFractPairKernel ρ y) = 0 := by
  rw [integral_burnolFractPairKernel hρ0 hρ1,
    burnolFixedAtomRawMellin_eq_zero_of_xi_eq_zero hρ0 hρ1 hxi]

/-! ## The forward divided shift -/

/-- Complex powers of a positive real quotient split. -/
theorem burnolPosCpow_div {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ w = ((a : ℝ) : ℂ) ^ w * (((b : ℝ) : ℂ) ^ w)⁻¹ := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hbne : ((b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have hdne : ((a / b : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_pos ha hb).ne'
  rw [Complex.cpow_def_of_ne_zero hdne, Complex.cpow_def_of_ne_zero hane,
    Complex.cpow_def_of_ne_zero hbne, ← Complex.exp_neg, ← Complex.exp_add,
    ← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le,
    ← Complex.ofReal_log (div_pos ha hb).le, Real.log_div ha.ne' hb.ne']
  push_cast
  ring_nf

/-- The forward Burnol divided shift of the fixed atom. -/
def burnolZeroDividedSource (ρ : ℂ) (t : ℝ) : ℂ :=
  ∫ u in Ioi (1 : ℝ), (u : ℂ) ^ (-ρ) * (((burnolFractPair (u * t) : ℝ) : ℂ) / ((u * t : ℝ) : ℂ))

/-- The integrand of the divided shift, written on the physical ray. -/
theorem burnolZeroDividedSource_integrand {ρ : ℂ} {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    (u : ℂ) ^ (-ρ) * (((burnolFractPair (u * t) : ℝ) : ℂ) / ((u * t : ℝ) : ℂ)) =
      ((t : ℝ) : ℂ) ^ (ρ - 1) * ((t : ℝ) : ℂ) * burnolFractPairKernel ρ (u * t) := by
  have hutpos : 0 < u * t := mul_pos hu ht
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hutne : ((u * t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hutpos.ne'
  have hu' : (u : ℝ) = (u * t) / t := by field_simp
  have hupow : (u : ℂ) ^ (-ρ) =
      ((u * t : ℝ) : ℂ) ^ (-ρ) * ((((t : ℝ)) : ℂ) ^ (-ρ))⁻¹ := by
    rw [show ((u : ℝ) : ℂ) = (((u * t) / t : ℝ) : ℂ) by rw [← hu'],
      burnolPosCpow_div hutpos ht]
  rw [hupow, burnolFractPairKernel]
  have hsplit : ((u * t : ℝ) : ℂ) ^ (-(ρ + 1)) =
      ((u * t : ℝ) : ℂ) ^ (-ρ) * (((u * t : ℝ) : ℂ))⁻¹ := by
    rw [show -(ρ + 1) = -ρ + (-1 : ℂ) by ring, Complex.cpow_add _ _ hutne,
      Complex.cpow_neg_one]
  rw [hsplit]
  have htpow : ((t : ℝ) : ℂ) ^ (ρ - 1) * ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) ^ ρ := by
    rw [show (ρ - 1 : ℂ) = ρ + (-1 : ℂ) by ring, Complex.cpow_add _ _ htne,
      Complex.cpow_neg_one]
    field_simp
  rw [htpow]
  have hinv : ((((t : ℝ)) : ℂ) ^ (-ρ))⁻¹ = ((t : ℝ) : ℂ) ^ ρ := by
    rw [Complex.cpow_neg, inv_inv]
  rw [hinv]
  field_simp

/-- **The tail representation.**  Substituting `y = ut` turns the divided shift into a tail
Mellin moment of the coboundary. -/
theorem burnolZeroDividedSource_eq_tail {ρ : ℂ} {t : ℝ} (ht : 0 < t) :
    burnolZeroDividedSource ρ t =
      ((t : ℝ) : ℂ) ^ (ρ - 1) * ∫ y in Ioi t, burnolFractPairKernel ρ y := by
  have hchange := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => ((t : ℝ) : ℂ) ^ (ρ - 1) * ((t : ℝ) : ℂ) * burnolFractPairKernel ρ y) 1 ht
  rw [mul_one] at hchange
  have hcongr : burnolZeroDividedSource ρ t =
      ∫ u in Ioi (1 : ℝ),
        ((t : ℝ) : ℂ) ^ (ρ - 1) * ((t : ℝ) : ℂ) * burnolFractPairKernel ρ (t * u) := by
    rw [burnolZeroDividedSource]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu1 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
    rw [burnolZeroDividedSource_integrand ht hu1, mul_comm t u]
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [hcongr, hchange, MeasureTheory.integral_const_mul, Complex.real_smul, Complex.ofReal_inv]
  field_simp

/-! ## The head value of the divided shift -/

theorem integrableOn_burnolFractPairKernel_Ioc {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (t : ℝ) : IntegrableOn (burnolFractPairKernel ρ) (Ioc (0 : ℝ) t) :=
  (integrableOn_burnolFractPairKernel hρ0 hρ1).mono_set
    (fun _ hy => mem_Ioi.mpr hy.1)

theorem integrableOn_burnolFractPairKernel_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    {t : ℝ} (ht : 0 < t) : IntegrableOn (burnolFractPairKernel ρ) (Ioi t) :=
  (integrableOn_burnolFractPairKernel hρ0 hρ1).mono_set
    (fun _ hy => mem_Ioi.mpr (lt_trans ht (mem_Ioi.mp hy)))

/-- **The tail is minus the head at a zero of `ξ`.** -/
theorem xiDivisor_integral_burnolFractPairKernel_Ioi {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) :
    (∫ y in Ioi t, burnolFractPairKernel ρ y) =
      -∫ y in Ioc (0 : ℝ) t, burnolFractPairKernel ρ y := by
  have hdisj : Disjoint (Ioc (0 : ℝ) t) (Ioi t) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ hx2
    exact absurd (mem_Ioi.mp hx2) (not_lt.mpr hx1)
  have hunion : Ioc (0 : ℝ) t ∪ Ioi t = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi ht.le
  have h := setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_burnolFractPairKernel_Ioc hρ0 hρ1 t)
    (integrableOn_burnolFractPairKernel_Ioi hρ0 hρ1 ht)
  rw [hunion, xiDivisor_integral_burnolFractPairKernel_eq_zero hρ0 hρ1 hxi] at h
  linear_combination -h

/-- Below the aperture the head integral is the elementary power moment. -/
theorem integral_burnolFractPairKernel_Ioc_of_le_half {ρ : ℂ} (hρ1 : ρ.re < 1) {t : ℝ}
    (ht : 0 < t) (hthalf : t ≤ 1 / 2) :
    (∫ y in Ioc (0 : ℝ) t, burnolFractPairKernel ρ y) =
      -(((t : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)) := by
  have hpow : ∀ y ∈ Ioo (0 : ℝ) t, burnolFractPairKernel ρ y = -((y : ℂ) ^ (-ρ)) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have hyhalf : y < 1 / 2 := lt_of_lt_of_le hy.2 hthalf
    have hyne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy0.ne'
    rw [burnolFractPairKernel, burnolFractPair_of_lt_half hy0.le hyhalf,
      show -(ρ + 1) = -ρ + (-1 : ℂ) by ring, Complex.cpow_add _ _ hyne, Complex.cpow_neg_one]
    push_cast
    field_simp
  rw [MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hpow,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le ht.le]
  have hr : (-1 : ℝ) < (-ρ).re := by
    rw [Complex.neg_re]
    linarith
  rw [intervalIntegral.integral_neg, integral_cpow (Or.inl hr)]
  have hsum : (-ρ + 1 : ℂ) = 1 - ρ := by ring
  rw [hsum]
  have hzero : ((0 : ℝ) : ℂ) ^ (1 - ρ) = 0 := by
    refine Complex.zero_cpow ?_
    intro hc
    have : (1 - ρ).re = 0 := by rw [hc]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  rw [hzero, sub_zero]

/-- **The head of the zero-divided source.**  On the aperture `(0, 1/2]` the forward divided shift
is the constant `a_ρ = 1/(1-ρ)`. -/
theorem xiDivisor_burnolZeroDividedSource_head {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) (hthalf : t ≤ 1 / 2) :
    burnolZeroDividedSource ρ t = 1 / (1 - ρ) := by
  have hrhone : (1 : ℂ) - ρ ≠ 0 := by
    intro hc
    have : (1 - ρ).re = 0 := by rw [hc]; simp
    rw [Complex.sub_re, Complex.one_re] at this
    linarith
  have htne : ((t : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [burnolZeroDividedSource_eq_tail ht,
    xiDivisor_integral_burnolFractPairKernel_Ioi hρ0 hρ1 hxi ht,
    integral_burnolFractPairKernel_Ioc_of_le_half hρ1 ht hthalf, neg_neg]
  rw [show ((t : ℝ) : ℂ) ^ (ρ - 1) * (((t : ℝ) : ℂ) ^ (1 - ρ) / (1 - ρ)) =
      (((t : ℝ) : ℂ) ^ (ρ - 1) * ((t : ℝ) : ℂ) ^ (1 - ρ)) / (1 - ρ) by ring,
    ← Complex.cpow_add _ _ htne, show (ρ - 1 + (1 - ρ) : ℂ) = 0 by ring, Complex.cpow_zero]

/-- The head value is the first-wall head constant of the residue polarization. -/
theorem xiDivisor_burnolZeroDividedSource_head_eq {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {t : ℝ} (ht : 0 < t) (hthalf : t ≤ 1 / 2) :
    burnolZeroDividedSource ρ t = burnolFirstWallHead ρ := by
  rw [xiDivisor_burnolZeroDividedSource_head hρ0 hρ1 hxi ht hthalf, burnolFirstWallHead, one_div]

end RHTower
