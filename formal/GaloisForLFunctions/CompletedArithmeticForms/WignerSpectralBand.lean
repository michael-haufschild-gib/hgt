import GaloisForLFunctions.CompletedArithmeticForms.BesselBarrierPayment
import GaloisForLFunctions.RHTower.PolyaBesselHeatKernel
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerProductFiberNormalForm

/-!
# A positive physical Wigner band and its arithmetic sign boundary

The literal radial transform is an exact Bessel value and argument-derivative
combination. Its nonoscillatory band has a positive reserve at every physical
nonnegative center. In each product fibre the remaining sign is precisely
the real divisor-character trace.
-/

noncomputable section

open Complex MeasureTheory Set

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry _root_.RHTower _root_.RHTower.DeBruijn

/-- The cosh-weighted Schläfli Fourier transform is the exact argument derivative. -/
theorem cosTransform_polyaKernel_cosh {a : ℝ} (ha : 0 < a) (w : ℂ) :
    cosTransform (fun t => polyaKernel a t * Real.cosh t) w =
      -2 * besselArgDeriv (I * w) a := by
  have hs := (superExpKernel_polyaKernel ha).cosTransform_add_shift 1 w
  simp only [Complex.ofReal_one, one_mul] at hs
  rw [cosTransform_polyaKernel ha, cosTransform_polyaKernel ha] at hs
  have hp : I * (w + I) = I * w - 1 := by
    rw [mul_add, Complex.I_mul_I]
    ring
  have hm : I * (w - I) = I * w + 1 := by
    rw [mul_sub, Complex.I_mul_I]
    ring
  rw [hp, hm] at hs
  have hd := (_root_.RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument ha (I * w)).unique
    (hasDerivAt_modifiedBesselKOrder_arg ha (I * w))
  change -(1 / 2 : ℂ) * (modifiedBesselKOrder a (I * w + 1) +
    modifiedBesselKOrder a (I * w - 1)) = besselArgDeriv (I * w) a at hd
  linear_combination (-1 / 2 : ℂ) * hs - 2 * hd

/-- The complete signed radial Fourier source, including its cosh term. -/
theorem thetaCuspWignerRadialTransform_eq_bessel {a : ℝ} (ha : 0 < a) (b : ℝ) :
    thetaCuspWignerRadialTransform a b = (a : ℂ) ^ 2 *
      (((a : ℂ) ^ 2 + 9) * modifiedBesselKOrder a ((b : ℂ) * I) +
        6 * a * besselArgDeriv ((b : ℂ) * I) a) := by
  let F : ℝ → ℂ := fun t => (polyaKernel a t : ℂ) *
    ((a : ℂ) ^ 2 + 9 - 6 * a * Complex.cosh (t : ℂ)) *
      Complex.exp (I * (b : ℂ) * t)
  have hpoint (v : ℝ) : (thetaCuspWignerRadialProfile a v : ℂ) *
      thetaWignerDifferencePhase b v = (a : ℂ) ^ 2 * F (2 * v) := by
    dsimp only [thetaCuspWignerRadialProfile, thetaWignerDifferencePhase, F, polyaKernel]
    have he : (((2 * b * v : ℝ) : ℂ) * I) = I * (b : ℂ) * ((2 * v : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, ← Complex.ofReal_cosh]
    push_cast
    ring
  have hscale := MeasureTheory.Measure.integral_comp_mul_left F 2
  have hscale' : (∫ v : ℝ, F (2 * v)) = (1 / 2 : ℂ) * ∫ t : ℝ, F t := by
    norm_num at hscale ⊢
    exact hscale
  have h0 := (superExpKernel_polyaKernel ha).integrable (b : ℂ)
  have h1 : Integrable (fun t : ℝ =>
      ((polyaKernel a t * Real.cosh t : ℝ) : ℂ) * Complex.exp (I * (b : ℂ) * t)) := by
    simpa only [pow_one, one_mul] using
      ((superExpKernel_polyaKernel ha).mul_cosh_pow 1 1).integrable (b : ℂ)
  have hF : (∫ t : ℝ, F t) =
      ((a : ℂ) ^ 2 + 9) * cosTransform (polyaKernel a) (b : ℂ) -
        6 * a * cosTransform (fun t => polyaKernel a t * Real.cosh t) (b : ℂ) := by
    have he : F = fun t =>
        ((a : ℂ) ^ 2 + 9) * ((polyaKernel a t : ℂ) * Complex.exp (I * (b : ℂ) * t)) -
          (6 * a : ℂ) * (((polyaKernel a t * Real.cosh t : ℝ) : ℂ) *
            Complex.exp (I * (b : ℂ) * t)) := by
      funext t
      dsimp only [F]
      rw [← Complex.ofReal_cosh]
      push_cast
      ring
    rw [he, integral_sub (h0.const_mul _) (h1.const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  unfold thetaCuspWignerRadialTransform
  simp_rw [hpoint]
  rw [integral_const_mul, hscale', hF, cosTransform_polyaKernel ha,
    cosTransform_polyaKernel_cosh ha, mul_comm I (b : ℂ)]
  ring

/-- The radial transform retains its full explicit positive Schläfli reserve on the band. -/
theorem thetaCuspWignerRadialTransform_band_lower {a b : ℝ}
    (ha : 0 < a) (hb : |b| ≤ a) :
    a ^ 2 * (a ^ 2 - 6 * a + 3) * (modifiedBesselKOrder a ((b : ℂ) * I)).re ≤
      (thetaCuspWignerRadialTransform a b).re := by
  rw [thetaCuspWignerRadialTransform_eq_bessel ha]
  have he : ((a : ℂ) ^ 2 * (((a : ℂ) ^ 2 + 9) *
      modifiedBesselKOrder a ((b : ℂ) * I) +
        6 * a * besselArgDeriv ((b : ℂ) * I) a)).re =
      a ^ 2 * ((a ^ 2 + 9) * (modifiedBesselKOrder a ((b : ℂ) * I)).re +
        6 * a * (besselArgDeriv ((b : ℂ) * I) a).re) := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, ← Complex.ofReal_pow,
      Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, mul_zero, sub_zero, add_zero]
  rw [he, mul_assoc]
  exact mul_le_mul_of_nonneg_left (besselSignedRadialCombination_lower ha hb) (sq_nonneg a)

/-- The actual signed radial source is positive on the full argument-sized band at scale six. -/
theorem thetaCuspWignerRadialTransform_re_pos_on_band {a b : ℝ}
    (ha : 6 ≤ a) (hb : |b| ≤ a) :
    0 < (thetaCuspWignerRadialTransform a b).re := by
  have ha0 : 0 < a := by linarith only [ha]
  have hpoly : 0 < a ^ 2 - 6 * a + 3 := by
    have h := mul_nonneg ha0.le (sub_nonneg.mpr ha)
    nlinarith only [h]
  exact (mul_pos (mul_pos (pow_pos ha0 2) hpoly)
    (modifiedBesselKOrder_re_pos_on_band ha0 hb)).trans_le
      (thetaCuspWignerRadialTransform_band_lower ha0 hb)

/-- In the physical band, the complete product fibre has exactly the divisor trace's sign. -/
theorem thetaCuspWignerProductFiber_re_nonneg_iff_on_band {k : ℕ} {u b : ℝ}
    (hc : 6 ≤ 2 * Real.pi * k * Real.exp (2 * u))
    (hb : |b| ≤ 2 * Real.pi * k * Real.exp (2 * u)) :
    0 ≤ (thetaCuspWignerProductFiber k u b).re ↔
      0 ≤ (thetaCuspWignerProductFiberDivisorTrace k b).re := by
  have hr := thetaCuspWignerRadialTransform_re_pos_on_band hc hb
  rw [thetaCuspWignerProductFiber_eq_divisorTrace_mul_radial]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    thetaCuspWignerProductFiberDivisorTrace_im_zero, thetaCuspWignerRadialTransform_im_zero,
    zero_mul, mul_zero, add_zero, sub_zero]
  rw [mul_nonneg_iff_of_pos_right hr, mul_nonneg_iff_of_pos_left (Real.exp_pos u)]

/-- Every positive product at a nonnegative physical center exceeds the radial threshold. -/
theorem six_le_physicalWignerScale {k : ℕ} (hk : 1 ≤ k) {u : ℝ} (hu : 0 ≤ u) :
    6 ≤ 2 * Real.pi * k * Real.exp (2 * u) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : 1 ≤ Real.exp (2 * u) := Real.one_le_exp_iff.mpr (by positivity)
  calc
    6 ≤ 2 * Real.pi := by linarith only [Real.pi_gt_three]
    _ = 2 * Real.pi * 1 := by ring
    _ ≤ 2 * Real.pi * k := mul_le_mul_of_nonneg_left hkR (by positivity)
    _ = (2 * Real.pi * k) * 1 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left he (by positivity)

/-- Actual physical product fibres have only the finite divisor-trace sign left inside their band. -/
theorem thetaCuspWignerProductFiber_physical_band_sign {k : ℕ} (hk : 1 ≤ k)
    {u b : ℝ} (hu : 0 ≤ u) (hb : |b| ≤ 2 * Real.pi * k * Real.exp (2 * u)) :
    0 ≤ (thetaCuspWignerProductFiber k u b).re ↔
      0 ≤ (thetaCuspWignerProductFiberDivisorTrace k b).re :=
  thetaCuspWignerProductFiber_re_nonneg_iff_on_band (six_le_physicalWignerScale hk hu) hb

/-- Each literal diagonal theta-atom pair has a positive band at every nonnegative center. -/
theorem thetaCuspSourcePairWigner_diagonal_re_pos {n : ℕ} (hn : 0 < n)
    {u b : ℝ} (hu : 0 ≤ u) (hb : |b| ≤ thetaCuspWignerAtomScale n n u) :
    0 < (thetaCuspSourcePairWigner n n u b).re := by
  have he : thetaCuspWignerAtomScale n n u =
      2 * Real.pi * (n * n : ℕ) * Real.exp (2 * u) := by
    unfold thetaCuspWignerAtomScale
    push_cast
    ring
  have hc : 6 ≤ thetaCuspWignerAtomScale n n u := by
    rw [he]
    exact six_le_physicalWignerScale (Nat.succ_le_iff.mpr (Nat.mul_pos hn hn)) hu
  have hr := thetaCuspWignerRadialTransform_re_pos_on_band hc hb
  rw [thetaCuspSourcePairWigner_eq_phase_mul_radial hn hn]
  simp only [thetaCuspWignerDivisorRatioPhase, sub_self, mul_zero, Complex.ofReal_zero,
    zero_mul, neg_zero, Complex.exp_zero, mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos (Real.exp_pos u) hr

#print axioms thetaCuspWignerRadialTransform_eq_bessel
#print axioms thetaCuspWignerRadialTransform_band_lower
#print axioms thetaCuspWignerRadialTransform_re_pos_on_band
#print axioms thetaCuspWignerProductFiber_re_nonneg_iff_on_band
#print axioms thetaCuspWignerProductFiber_physical_band_sign
#print axioms thetaCuspSourcePairWigner_diagonal_re_pos

end GaloisForLFunctions.CompletedArithmeticForms
