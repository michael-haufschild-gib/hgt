import GaloisForLFunctions.CompletedArithmeticForms.BesselHalfOrderSquare

/-!
# Positive weighted Bessel tails from radial squares

Polar coordinates identify the first weighted imaginary-order Bessel tail
with a strictly positive integral of half-order squares. Each radial slice
retains the exponential reserve of its base coordinate.
-/

open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology
namespace GaloisForLFunctions.CompletedArithmeticForms
open HTGeometry RHTower
noncomputable section

/-- Raising a radial coordinate above a fixed nonnegative base preserves its area element. -/
theorem integral_radial_lift {q : ℝ} (hq : 0 ≤ q) (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), r • f (Real.sqrt (q ^ 2 + r ^ 2))) =
      ∫ u in Ioi q, u • f u := by
  let S : ℝ → ℝ := fun r => Real.sqrt (q ^ 2 + r ^ 2)
  have hSpos {r : ℝ} (hr : 0 < r) : 0 < S r :=
    Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (sq_nonneg q) (sq_pos_of_pos hr))
  have hsq (r : ℝ) : (S r) ^ 2 = q ^ 2 + r ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg q) (sq_nonneg r))
  have hderiv {r : ℝ} (hr : 0 < r) : HasDerivAt S (r / S r) r := by
    have hp : q ^ 2 + r ^ 2 ≠ 0 :=
      (add_pos_of_nonneg_of_pos (sq_nonneg q) (sq_pos_of_pos hr)).ne'
    have h := ((hasDerivAt_const r (q ^ 2)).add ((hasDerivAt_id r).pow 2)).sqrt hp
    change HasDerivAt S _ r at h
    apply h.congr_deriv
    dsimp only [id_eq, Pi.add_apply, Pi.pow_apply, S]
    field_simp
    ring
  have hinj : InjOn S (Ioi 0) := by
    intro r hr s hs he
    have heq := congrArg (fun z : ℝ => z ^ 2) he
    rw [hsq, hsq] at heq
    nlinarith [show 0 < r from hr, show 0 < s from hs]
  have himage : S '' Ioi 0 = Ioi q := by
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      have hp := hSpos hr
      have hs := hsq r
      have hrp := sq_pos_of_pos (show 0 < r from hr)
      change q < S r
      nlinarith
    · intro hu
      have hp : 0 < u ^ 2 - q ^ 2 := by
        have hqu : q < u := hu
        nlinarith
      refine ⟨Real.sqrt (u ^ 2 - q ^ 2), Real.sqrt_pos.mpr hp, ?_⟩
      dsimp only [S]
      rw [Real.sq_sqrt hp.le]
      have he : q ^ 2 + (u ^ 2 - q ^ 2) = u ^ 2 := by ring
      rw [he, Real.sqrt_sq (hq.trans (le_of_lt hu))]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi 0)
    (f := S) (f' := fun r => r / S r) measurableSet_Ioi
    (fun r hr => (hderiv hr).hasDerivWithinAt) hinj (fun u => u • f u)
  rw [himage] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [abs_of_pos (div_pos hr (hSpos hr)), smul_smul,
    div_mul_cancel₀ _ (hSpos hr).ne']

/-- Polar reduction of a radial plane slice to its first weighted tail. -/
theorem integral_radial_plane {q : ℝ} (hq : 0 ≤ q) (f : ℝ → ℂ) :
    (∫ z : ℝ × ℝ, f (Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2))) =
      (2 * Real.pi) • ∫ u in Ioi q, u • f u := by
  rw [← integral_comp_polarCoord_symm]
  have he (z : ℝ × ℝ) :
      Real.sqrt (q ^ 2 + (polarCoord.symm z).1 ^ 2 + (polarCoord.symm z).2 ^ 2) =
        Real.sqrt (q ^ 2 + z.1 ^ 2) := by
    change Real.sqrt (q ^ 2 + (z.1 * Real.cos z.2) ^ 2 +
      (z.1 * Real.sin z.2) ^ 2) = _
    congr 1
    rw [add_assoc, mul_pow, mul_pow, ← mul_add, Real.cos_sq_add_sin_sq, mul_one]
  simp_rw [he]
  change (∫ z in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    z.1 • f (Real.sqrt (q ^ 2 + z.1 ^ 2))) = _
  change (∫ z in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    z.1 • f (Real.sqrt (q ^ 2 + z.1 ^ 2)) ∂((volume : Measure ℝ).prod volume)) = _
  rw [← Measure.prod_restrict]
  have hprod := integral_prod_mul
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioo (-Real.pi) Real.pi))
    (fun r : ℝ => r • f (Real.sqrt (q ^ 2 + r ^ 2))) (fun _ : ℝ => (1 : ℂ))
  simp only [mul_one] at hprod
  rw [hprod, integral_radial_lift hq]
  have hc : (∫ t in Ioo (-Real.pi) Real.pi, (1 : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
      (neg_le_self Real.pi_pos.le), intervalIntegral.integral_const]
    simp only [Complex.real_smul, mul_one]
    congr 1
    ring
  rw [hc, Complex.real_smul, mul_comm]

/-- The first radial weighted tail of the real imaginary-order Schläfli carrier. -/
def besselFirstWeightedTail (τ q : ℝ) : ℝ :=
  ∫ u in Ioi q, u * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re

private theorem integrable_exp_neg_abs :
    Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => by
      rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
  rw [← integrableOn_univ]
  simpa only [Ioi_union_Iic] using hpos.union hneg

private theorem base_le_plane_radius {q : ℝ} (hq : 0 ≤ q) (v w : ℝ) :
    q ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
  calc
    q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hq).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg v, sq_nonneg w])

private theorem plane_radius_coordinate_bound (q v w : ℝ) :
    |v| + |w| ≤ 2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
  have hv : |v| ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs v]
    apply Real.sqrt_le_sqrt
    nlinarith only [sq_nonneg q, sq_nonneg w]
  have hw : |w| ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs w]
    apply Real.sqrt_le_sqrt
    nlinarith only [sq_nonneg q, sq_nonneg v]
  linarith

/-- Absolute integrability of the imaginary-order carrier over every positive radial plane. -/
theorem integrable_bessel_plane_slice {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    Integrable (fun z : ℝ × ℝ => modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) (((2 * τ : ℝ) : ℂ) * I)) := by
  let ν : ℂ := ((2 * τ : ℝ) : ℂ) * I
  let C : ℝ := Real.exp 1 * besselOrderUnitMass ν
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hrad (v w : ℝ) : 1 ≤ 2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    linarith [base_le_plane_radius hq0 v w]
  have hc : Continuous (fun z : ℝ × ℝ => modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) ν) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_modifiedBesselKOrder_arg
      (lt_of_lt_of_le zero_lt_one (hrad z.1 z.2)) ν).continuousAt.comp'
        (f := fun z : ℝ × ℝ => 2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2))
        (x := z) (by fun_prop)
  have henv := (integrable_exp_neg_abs.mul_prod integrable_exp_neg_abs).const_mul C
  refine henv.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  calc
    _ ≤ Real.exp (1 - 2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) *
        besselOrderUnitMass ν := norm_modifiedBesselKOrder_le_exp (hrad z.1 z.2) ν
    _ ≤ Real.exp (1 - |z.1| - |z.2|) * besselOrderUnitMass ν := by
      apply mul_le_mul_of_nonneg_right _ (besselOrderUnitMass_nonneg ν)
      apply Real.exp_le_exp.mpr
      linarith [plane_radius_coordinate_bound q z.1 z.2]
    _ = _ := by
      dsimp only [C]
      rw [show 1 - |z.1| - |z.2| = 1 + (-|z.1|) + (-|z.2|) by ring,
        Real.exp_add, Real.exp_add]
      ring

private theorem imaginary_order_eq_ofReal_re (x τ : ℝ) :
    modifiedBesselKOrder x ((τ : ℂ) * I) =
      ((modifiedBesselKOrder x ((τ : ℂ) * I)).re : ℂ) := by
  have hn : conj ((τ : ℂ) * I) = -((τ : ℂ) * I) := by simp
  have h := modifiedBesselKOrder_conj x ((τ : ℂ) * I)
  rw [hn, modifiedBesselKOrder_neg] at h
  have hi := congrArg Complex.im h
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    linarith

private theorem square_slice_eq_inner_integral {q : ℝ} (hq : 0 < q) (τ v : ℝ) :
    (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ) =
      ∫ w : ℝ, modifiedBesselKOrder
        (2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2)) (((2 * τ : ℝ) : ℂ) * I) := by
  have hr : 0 < Real.sqrt (q ^ 2 + v ^ 2) :=
    Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq) (sq_nonneg v))
  rw [besselHalfOrderSquare_eq_radial_integral hr]
  simp_rw [Real.sq_sqrt (add_nonneg (sq_nonneg q) (sq_nonneg v))]

/-- The radial square slice is integrable on the entire real line. -/
theorem integrable_besselHalfOrderSquare_slice {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    Integrable (fun v : ℝ => besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2))) := by
  have h := (integrable_bessel_plane_slice hq τ).integral_prod_left
  have hc : Integrable (fun v : ℝ =>
      (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ)) := by
    refine h.congr (Filter.Eventually.of_forall fun v => ?_)
    exact (square_slice_eq_inner_integral (lt_of_lt_of_le zero_lt_one hq) τ v).symm
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.integrable_comp hc

/-- The first weighted Bessel tail is exactly a positive radial square integral. -/
theorem two_pi_mul_besselFirstWeightedTail_eq_square_integral
    {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    2 * Real.pi * besselFirstWeightedTail τ q =
      ∫ v : ℝ, besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) := by
  have hF := integrable_bessel_plane_slice hq τ
  have he : (∫ v : ℝ,
      (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ)) =
      ((2 * Real.pi * besselFirstWeightedTail τ q : ℝ) : ℂ) := by
    simp_rw [square_slice_eq_inner_integral (lt_of_lt_of_le zero_lt_one hq) τ]
    rw [← integral_prod _ hF]
    change (∫ z : ℝ × ℝ, modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) (((2 * τ : ℝ) : ℂ) * I)) = _
    rw [integral_radial_plane (zero_le_one.trans hq)
      (fun u => modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I))]
    have hw : (fun u : ℝ => u • modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)) =
        fun u : ℝ => ((u * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
      funext u
      rw [Complex.real_smul]
      conv_lhs => rw [imaginary_order_eq_ofReal_re]
      simp only [Complex.ofReal_mul]
    rw [hw, integral_complex_ofReal]
    simp only [Complex.real_smul, Complex.ofReal_mul, besselFirstWeightedTail]
  rw [integral_complex_ofReal] at he
  exact (Complex.ofReal_injective he).symm


/-- The first weighted imaginary-order Bessel tail is strictly positive at every frequency. -/
theorem besselFirstWeightedTail_pos {q : ℝ} (hq : 1 ≤ q) (τ : ℝ) :
    0 < besselFirstWeightedTail τ q := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp (v : ℝ) : 0 < besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) :=
    besselHalfOrderSquare_pos (Real.sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq0) (sq_nonneg v))) τ
  have hint := integrable_besselHalfOrderSquare_slice hq τ
  have hs : Function.support
      (fun v : ℝ => besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2))) = univ := by
    ext v
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp v).ne'
  have hpos : 0 < ∫ v : ℝ, besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) := by
    apply (MeasureTheory.integral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun v => (hp v).le) hint).mpr
    rw [hs]
    simp
  rw [← two_pi_mul_besselFirstWeightedTail_eq_square_integral hq τ] at hpos
  by_contra h
  have hn := mul_nonpos_of_nonneg_of_nonpos
    (show 0 ≤ 2 * Real.pi by positivity) (le_of_not_gt h)
  exact (not_lt_of_ge hn) hpos

private theorem radial_lift_sub_le {q u : ℝ} (hq : 0 ≤ q) (hqu : q ≤ u) (v : ℝ) :
    Real.sqrt (u ^ 2 + v ^ 2) - Real.sqrt (q ^ 2 + v ^ 2) ≤ u - q := by
  have hr : q ≤ Real.sqrt (q ^ 2 + v ^ 2) := by
    calc
      q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hq).symm
      _ ≤ _ := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg v))
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg q) (sq_nonneg v))
  have ht := Real.sq_sqrt (add_nonneg (sq_nonneg u) (sq_nonneg v))
  have hb : (Real.sqrt (u ^ 2 + v ^ 2)) ^ 2 ≤
      (Real.sqrt (q ^ 2 + v ^ 2) + (u - q)) ^ 2 := by
    nlinarith only [hs, ht, mul_nonneg (sub_nonneg.mpr hr) (sub_nonneg.mpr hqu)]
  have h := (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg
    (Real.sqrt_nonneg _) (sub_nonneg.mpr hqu))).mp hb
  linarith

/-- Every radial square slice retains the exponential reserve of its base coordinate. -/
theorem besselHalfOrderSquare_slice_exp_lower {q u : ℝ}
    (hq : 0 < q) (hqu : q ≤ u) (τ v : ℝ) :
    Real.exp (-2 * (u - q)) * besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) ≤
      besselHalfOrderSquare τ (Real.sqrt (u ^ 2 + v ^ 2)) := by
  have hr : 0 < Real.sqrt (q ^ 2 + v ^ 2) := Real.sqrt_pos.mpr
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq) (sq_nonneg v))
  have hru : Real.sqrt (q ^ 2 + v ^ 2) ≤ Real.sqrt (u ^ 2 + v ^ 2) := by
    apply Real.sqrt_le_sqrt
    nlinarith only [mul_nonneg (sub_nonneg.mpr hqu) (add_nonneg hq.le (hq.le.trans hqu))]
  have he : Real.exp (-2 * (u - q)) ≤
      Real.exp (-2 * (Real.sqrt (u ^ 2 + v ^ 2) - Real.sqrt (q ^ 2 + v ^ 2))) := by
    apply Real.exp_le_exp.mpr
    linarith [radial_lift_sub_le hq.le hqu v]
  exact (mul_le_mul_of_nonneg_right he (besselHalfOrderSquare_pos hr τ).le).trans
    (besselHalfOrderSquare_exp_lower hr hru τ)

/-- The first weighted tail retains an exponential reserve uniformly in frequency. -/
theorem besselFirstWeightedTail_exp_lower {q u : ℝ}
    (hq : 1 ≤ q) (hqu : q ≤ u) (τ : ℝ) :
    Real.exp (-2 * (u - q)) * besselFirstWeightedTail τ q ≤ besselFirstWeightedTail τ u := by
  have hi := integral_mono_ae
    ((integrable_besselHalfOrderSquare_slice hq τ).const_mul (Real.exp (-2 * (u - q))))
    (integrable_besselHalfOrderSquare_slice (hq.trans hqu) τ)
    (Filter.Eventually.of_forall fun v =>
      besselHalfOrderSquare_slice_exp_lower (lt_of_lt_of_le zero_lt_one hq) hqu τ v)
  rw [integral_const_mul,
    ← two_pi_mul_besselFirstWeightedTail_eq_square_integral hq τ,
    ← two_pi_mul_besselFirstWeightedTail_eq_square_integral (hq.trans hqu) τ] at hi
  apply (mul_le_mul_iff_left₀ (show 0 < 2 * Real.pi by positivity)).mp
  convert hi using 1 <;> ring


end
end GaloisForLFunctions.CompletedArithmeticForms
