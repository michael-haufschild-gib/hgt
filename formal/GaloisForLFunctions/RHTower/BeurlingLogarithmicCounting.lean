import GaloisForLFunctions.RHTower.BeurlingRationalRealizability
import GaloisForLFunctions.RHTower.BeurlingRegularIntegersOffLineZeros
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# A continuous Euler pair with a quadratic logarithmic counting remainder

For each real `g`, two nonnegative densities have transforms equal to
`Z_g(s) = ((s-2/3)^(2 : ℕ)+g^(2 : ℕ))(s+1/3)/((s-1)s^(2 : ℕ))` on `Re s > 1`: the logarithmic-prime
density through the exponential of its Laplace integral, and the integer density through
its Laplace integral with a unit atom at zero. The latter's cumulative function is explicit.

One fixed pair, `g=1`, has counting remainder
`-13/27 - (40/27) log x - (13/54)(log x)^(2 : ℕ)`, hence error `o(x^e)` for every `e>0`,
and a genuine nonreal zero at `2/3+i`. The prime density is nonnegative by the exponential
factorization for poles `{1,0,0}` and zeros `{2/3,2/3,-1/3}`, followed by `cos <= 1`.
Frullani integrals and elementary exponential integrals give the two transforms.

The assertions concern continuous densities and their integral identities. They assert neither
a discrete prime sequence nor a functional equation. They do not identify the measures by a
formalized uniqueness theorem for convolution exponentials.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics
open GaloisForLFunctions.HTGeometry
namespace RHTower.BeurlingLogarithmicCounting

def quadraticCoefficient (g : ℝ) : ℝ := 4 / 27 + g ^ 2 / 3

def residue (g : ℝ) : ℝ := 4 / 27 + 4 * g ^ 2 / 3

def primeDensity (g t : ℝ) : ℝ :=
  (Real.exp t + 2 - 2 * Real.exp (2 * t / 3) * Real.cos (g * t) - Real.exp (-t / 3)) / t

def integerDensity (g t : ℝ) : ℝ :=
  residue g * (Real.exp t - 1) - quadraticCoefficient g * t

def logCounting (g t : ℝ) : ℝ :=
  residue g * Real.exp t + (1 - residue g) - residue g * t - quadraticCoefficient g * t ^ 2 / 2

def counting (g x : ℝ) : ℝ := logCounting g (Real.log x)

def zeta (g : ℝ) (s : ℂ) : ℂ :=
  ((s - 2 / 3) ^ 2 + (g : ℂ) ^ 2) * (s + 1 / 3) / ((s - 1) * s ^ 2)

theorem residue_pos (g : ℝ) : 0 < residue g := by
  unfold residue
  positivity

theorem residue_sub_quadraticCoefficient (g : ℝ) :
    residue g - quadraticCoefficient g = g ^ 2 := by
  unfold residue quadraticCoefficient
  ring

theorem primeDensity_nonneg (g : ℝ) {t : ℝ} (ht : 0 < t) : 0 ≤ primeDensity g t := by
  have h := RationalFactor.exp_difference_nonneg (t := t / 3) (by positivity)
  have hcos := Real.cos_le_one (g * t)
  have he := Real.exp_pos (2 * t / 3)
  rw [show 3 * (t / 3) = t by ring, show 2 * (t / 3) = 2 * t / 3 by ring,
    show -(t / 3) = -t / 3 by ring] at h
  apply div_nonneg _ ht.le
  nlinarith

theorem integerDensity_nonneg (g : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ integerDensity g t := by
  have h := mul_nonneg (residue_pos g).le (sub_nonneg.mpr (Real.add_one_le_exp t))
  have hsq := mul_nonneg (sq_nonneg g) ht
  have hr := residue_sub_quadraticCoefficient g
  unfold integerDensity
  nlinarith

theorem logCounting_zero (g : ℝ) : logCounting g 0 = 1 := by
  simp [logCounting]

theorem hasDerivAt_logCounting (g t : ℝ) :
    HasDerivAt (logCounting g) (integerDensity g t) t := by
  convert (((((Real.hasDerivAt_exp t).const_mul (residue g)).add_const (1 - residue g)).sub
    ((hasDerivAt_id t).const_mul (residue g))).sub
    ((((hasDerivAt_id t).pow 2).const_mul (quadraticCoefficient g)).div_const 2)) using 1 <;>
    first | rfl | (dsimp [logCounting, integerDensity]; ring)

theorem logCounting_eq_integral (g : ℝ) (t : ℝ) :
    logCounting g t = 1 + ∫ u in (0 : ℝ)..t, integerDensity g u := by
  have hc : Continuous (integerDensity g) := by
    unfold integerDensity
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_logCounting g u) (hc.intervalIntegrable 0 t)
  rw [logCounting_zero] at h
  linarith

theorem counting_exact (g : ℝ) {x : ℝ} (hx : 0 < x) :
    counting g x - residue g * x =
      1 - residue g - residue g * Real.log x - quadraticCoefficient g * (Real.log x) ^ 2 / 2 := by
  simp only [counting, logCounting, Real.exp_log hx]
  ring

theorem logCounting_remainder_littleO (g : ℝ) {e : ℝ} (he : 0 < e) :
    (fun t => logCounting g t - residue g * Real.exp t) =o[atTop]
      (fun t => Real.exp (e * t)) := by
  have h0 := (isLittleO_pow_exp_pos_mul_atTop 0 he).const_mul_left (1 - residue g)
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 1 he).const_mul_left (residue g)
  have h2 := (isLittleO_pow_exp_pos_mul_atTop 2 he).const_mul_left (quadraticCoefficient g / 2)
  convert (h0.sub h1).sub h2 using 1 <;> try rfl
  funext t
  dsimp [logCounting]
  ring

theorem counting_remainder_littleO (g : ℝ) {e : ℝ} (he : 0 < e) :
    (fun x => counting g x - residue g * x) =o[atTop] (fun x : ℝ => x ^ e) := by
  refine ((logCounting_remainder_littleO g he).comp_tendsto Real.tendsto_log_atTop).congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [counting, Real.exp_log hx]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    simp [Real.rpow_def_of_pos hx, mul_comm]

theorem zeta_partial_fractions (g : ℝ) {s : ℂ} (h0 : s ≠ 0) (h1 : s - 1 ≠ 0) :
    zeta g s = 1 + (residue g : ℂ) / (s - 1) - (residue g : ℂ) / s -
      (quadraticCoefficient g : ℂ) / s ^ 2 := by
  unfold zeta residue quadraticCoefficient
  push_cast
  field_simp
  ring

theorem zeta_zero (g : ℝ) : zeta g (2 / 3 + (g : ℂ) * Complex.I) = 0 := by
  unfold zeta
  rw [add_sub_cancel_left, mul_pow, Complex.I_sq]
  ring

theorem zeta_denominator_ne_zero (g : ℝ) :
    ((2 / 3 + (g : ℂ) * Complex.I) - 1) * (2 / 3 + (g : ℂ) * Complex.I) ^ 2 ≠ 0 := by
  apply mul_ne_zero _ (pow_ne_zero _ _)
  all_goals intro h; have h' := congrArg Complex.re h; norm_num at h'


private def frullaniKernel (a b : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(a * t)) - Complex.exp (-(b * t))) / t

private theorem positive_rates (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    0 < (s - 1).re ∧ 0 < s.re ∧ 0 < (s - 2 / 3 - (g : ℂ) * Complex.I).re ∧
    0 < (s - 2 / 3 + (g : ℂ) * Complex.I).re ∧ 0 < (s + 1 / 3).re := by
  simp only [Complex.add_re, Complex.sub_re, Complex.div_ofNat_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, zero_mul, sub_zero, add_zero]
  norm_num
  exact ⟨hs, by linarith, by linarith, by linarith⟩

private theorem weighted_primeDensity_split (g : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(s * t)) * (primeDensity g t : ℂ) =
      frullaniKernel (s - 1) (s - 2 / 3 - (g : ℂ) * Complex.I) t +
      frullaniKernel s (s - 2 / 3 + (g : ℂ) * Complex.I) t +
      frullaniKernel s (s + 1 / 3) t := by
  have hd : primeDensity g t = BeurlingRegularIntegers.regularDensity (2 / 3) g 0 1 t +
      (1 - Real.exp (-t / 3)) / t := by
    unfold primeDensity BeurlingRegularIntegers.regularDensity BeurlingRegularIntegers.regularNumerator
    simp only [zero_mul, Real.exp_zero, one_mul, sub_self, sub_zero]
    rw [show 2 / 3 * t = 2 * t / 3 by ring]
    ring
  have he : Complex.exp (-((s + 1 / 3) * (t : ℂ))) =
      Complex.exp (-(s * t)) * Complex.exp (-(t : ℂ) / 3) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hsplit := BeurlingRegularIntegers.cexp_mul_regularDensity (2 / 3) g 0 1 s ht
  simp only [Nat.cast_one, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_zero,
    sub_zero, sub_self, zero_mul, add_zero] at hsplit
  rw [hd, Complex.ofReal_add, mul_add, hsplit]
  unfold frullaniKernel
  push_cast
  rw [he]
  ring

theorem integrableOn_weighted_primeDensity (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (primeDensity g t : ℂ)) (Ioi 0) := by
  obtain ⟨h1, h0, hm, hp, ha⟩ := positive_rates g hs
  exact (((integrableOn_frullani h1 hm).add (integrableOn_frullani h0 hp)).add
    (integrableOn_frullani h0 ha)).congr_fun
      (fun t ht => (weighted_primeDensity_split g s ht).symm) measurableSet_Ioi

theorem integral_weighted_primeDensity (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity g t : ℂ)) =
      (Complex.log (s - 2 / 3 - (g : ℂ) * Complex.I) - Complex.log (s - 1)) +
      (Complex.log (s - 2 / 3 + (g : ℂ) * Complex.I) - Complex.log s) +
      (Complex.log (s + 1 / 3) - Complex.log s) := by
  obtain ⟨h1, h0, hm, hp, ha⟩ := positive_rates g hs
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => weighted_primeDensity_split g s ht)]
  unfold frullaniKernel
  have h12 : IntegrableOn (fun t : ℝ =>
      (Complex.exp (-((s - 1) * t)) - Complex.exp (-((s - 2 / 3 - (g : ℂ) * Complex.I) * t))) / t +
      (Complex.exp (-(s * t)) - Complex.exp (-((s - 2 / 3 + (g : ℂ) * Complex.I) * t))) / t)
      (Ioi 0) := (integrableOn_frullani h1 hm).add (integrableOn_frullani h0 hp)
  rw [integral_add h12 (integrableOn_frullani h0 ha), integral_add (integrableOn_frullani h1 hm)
    (integrableOn_frullani h0 hp), integral_frullani h1 hm, integral_frullani h0 hp,
    integral_frullani h0 ha]

theorem exp_integral_primeDensity (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity g t : ℂ)) =
      zeta g s := by
  obtain ⟨h1, h0, hm, hp, ha⟩ := positive_rates g hs
  have nz : ∀ z : ℂ, 0 < z.re → z ≠ 0 := by
    intro z hz h
    simp [h] at hz
  rw [integral_weighted_primeDensity g hs]
  simp only [Complex.exp_add, Complex.exp_sub, Complex.exp_log (nz _ h1),
    Complex.exp_log (nz _ h0), Complex.exp_log (nz _ hm), Complex.exp_log (nz _ hp),
    Complex.exp_log (nz _ ha)]
  unfold zeta
  have hf : (s - 2 / 3 - (g : ℂ) * Complex.I) * (s - 2 / 3 + (g : ℂ) * Complex.I) =
      (s - 2 / 3) ^ 2 + (g : ℂ) ^ 2 := by
    linear_combination -(g : ℂ)^(2 : ℕ) * Complex.I_sq
  rw [← hf]
  field_simp

private theorem weighted_integerDensity_split (g : ℝ) (s : ℂ) (t : ℝ) :
    Complex.exp (-(s * t)) * (integerDensity g t : ℂ) =
      (residue g : ℂ) * Complex.exp (-((s - 1) * t)) -
      (residue g : ℂ) * Complex.exp (-(s * t)) -
      (quadraticCoefficient g : ℂ) * ((t : ℂ) * Complex.exp (-(s * t))) := by
  have he : Complex.exp (-((s - 1) * (t : ℂ))) =
      Complex.exp (-(s * t)) * Complex.exp (t : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold integerDensity
  push_cast
  rw [he]
  ring

theorem integrableOn_weighted_integerDensity (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (integerDensity g t : ℂ)) (Ioi 0) := by
  obtain ⟨h1, h0, _⟩ := positive_rates g hs
  have hi1 := (integrableOn_cexp_neg_mul h1).const_mul (residue g : ℂ)
  have hi0 := (integrableOn_cexp_neg_mul h0).const_mul (residue g : ℂ)
  have hit := (integrableOn_natPow_mul_cexp h0 1).const_mul (quadraticCoefficient g : ℂ)
  simp only [pow_one] at hit
  exact IntegrableOn.congr_fun ((hi1.sub hi0).sub hit)
    (fun t _ => (weighted_integerDensity_split g s t).symm) measurableSet_Ioi

theorem integral_integerDensity (g : ℝ) {s : ℂ} (hs : 1 < s.re) :
    1 + (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (integerDensity g t : ℂ)) =
      zeta g s := by
  obtain ⟨h1, h0, _⟩ := positive_rates g hs
  have hi1 := (integrableOn_cexp_neg_mul h1).const_mul (residue g : ℂ)
  have hi0 := (integrableOn_cexp_neg_mul h0).const_mul (residue g : ℂ)
  have hit := (integrableOn_natPow_mul_cexp h0 1).const_mul (quadraticCoefficient g : ℂ)
  simp only [pow_one] at hit
  have hint := integral_Ioi_pow_mul_cexp h0 1
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, Nat.reduceAdd] at hint
  have hi10 : IntegrableOn (fun t : ℝ =>
      (residue g : ℂ) * Complex.exp (-((s - 1) * t)) -
      (residue g : ℂ) * Complex.exp (-(s * t))) (Ioi 0) := hi1.sub hi0
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => weighted_integerDensity_split g s t),
    integral_sub hi10 hit, integral_sub hi1 hi0,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_cexp_neg_mul h1, integral_cexp_neg_mul h0, hint]
  have n0 : s ≠ 0 := by intro h; simp [h] at h0
  have n1 : s - 1 ≠ 0 := by intro h; simp [h] at h1
  rw [zeta_partial_fractions g n0 n1]
  ring

/-- A single explicit continuous pair: both densities are positive, the transforms agree,
and the same counting function has subpower error for every positive exponent while its
rational transform vanishes at `2/3 + i`. No discrete realization or functional equation
is asserted. All parameters are instantiated; there are no unproved mathematical premises. -/
theorem explicit_continuous_countermodel :
    (∀ t : ℝ, 0 < t → 0 ≤ primeDensity 1 t) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ integerDensity 1 t) ∧
    (∀ t : ℝ, logCounting 1 t = 1 + ∫ u in (0 : ℝ)..t, integerDensity 1 u) ∧
    (∀ s : ℂ, 1 < s.re →
      IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (primeDensity 1 t : ℂ)) (Ioi 0) ∧
      IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) * (integerDensity 1 t : ℂ)) (Ioi 0) ∧
      Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity 1 t : ℂ)) =
        zeta 1 s ∧
      1 + (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (integerDensity 1 t : ℂ)) =
        zeta 1 s) ∧
    (∀ x : ℝ, 1 ≤ x → counting 1 x - (40 / 27) * x =
      -13 / 27 - (40 / 27) * Real.log x - (13 / 54) * (Real.log x) ^ 2) ∧
    (∀ e : ℝ, 0 < e →
      (fun x => counting 1 x - (40 / 27) * x) =o[atTop] (fun x : ℝ => x ^ e)) ∧
    zeta 1 (2 / 3 + Complex.I) = 0 ∧
    ((2 / 3 + Complex.I) - 1) * (2 / 3 + Complex.I) ^ 2 ≠ 0 ∧
    (2 / 3 + Complex.I).re = 2 / 3 ∧ (2 / 3 + Complex.I).im = 1 := by
  refine ⟨fun t ht => primeDensity_nonneg 1 ht,
    fun t ht => integerDensity_nonneg 1 ht, logCounting_eq_integral 1,
    fun s hs => ⟨integrableOn_weighted_primeDensity 1 hs,
      integrableOn_weighted_integerDensity 1 hs, exp_integral_primeDensity 1 hs,
      integral_integerDensity 1 hs⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have h := counting_exact 1 (lt_of_lt_of_le zero_lt_one hx)
    norm_num [residue, quadraticCoefficient] at h
    linarith
  · intro e he
    have h := counting_remainder_littleO 1 he
    norm_num [residue] at h
    exact h
  · simpa using zeta_zero 1
  · simpa using zeta_denominator_ne_zero 1
  · norm_num
  · norm_num

end RHTower.BeurlingLogarithmicCounting

