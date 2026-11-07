import GaloisForLFunctions.CompletedArithmeticForms.BesselWeightedTail

/-!
# Positive Bessel tails at every positive cutoff

Schläfli comparison against any positive reference argument removes the
unit-cutoff restriction from radial square integrability. The first
weighted tail stays positive and retains its exponential reserve all
the way to the Mellin endpoint.
-/

open Complex Filter Set MeasureTheory
open scoped ComplexConjugate Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms
open GaloisForLFunctions.HTGeometry

private theorem norm_kernel_le_base {q x : ℝ} (hqx : q ≤ x) (ν : ℂ) (t : ℝ) :
    ‖besselOrderKernel x ν t‖ ≤ Real.exp (q - x) * ‖besselOrderKernel q ν t‖ := by
  simp only [besselOrderKernel, norm_mul]
  have he (a : ℝ) : ‖Complex.exp (-(a : ℂ) * Complex.cosh (t : ℂ))‖ =
      Real.exp (-a * Real.cosh t) := by
    rw [Complex.norm_exp, ← Complex.ofReal_cosh]
    congr 1
    simp
  rw [he, he, ← mul_assoc, ← Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hh := mul_nonneg (sub_nonneg.mpr hqx) (sub_nonneg.mpr (Real.one_le_cosh t))
  nlinarith only [hh]

/-- Every positive reference argument supplies an exponential Schläfli envelope. -/
theorem norm_modifiedBesselKOrder_le_positive_base {q x : ℝ}
    (hq : 0 < q) (hqx : q ≤ x) (ν : ℂ) :
    ‖modifiedBesselKOrder x ν‖ ≤
      Real.exp (q - x) * ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel q ν t‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  have hh := setIntegral_mono_on (integrableOn_besselOrderKernel (hq.trans_le hqx) ν).norm
    ((integrableOn_besselOrderKernel hq ν).norm.const_mul (Real.exp (q - x)))
    measurableSet_Ioi (fun t _ => norm_kernel_le_base hqx ν t)
  rwa [integral_const_mul] at hh

private theorem integrable_exp_abs : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
  have hpos : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have hneg : IntegrableOn (fun x : ℝ => Real.exp (-|x|)) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact (integrableOn_Ici_iff_integrableOn_Ioi).mpr hpos
  rw [← integrableOn_univ]
  simpa only [Ioi_union_Iic] using hpos.union hneg

/-- The complete radial plane is integrable at every positive base radius. -/
theorem integrable_bessel_plane_slice_of_pos {q : ℝ} (hq : 0 < q) (τ : ℝ) :
    Integrable (fun z : ℝ × ℝ => modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) (((2 * τ : ℝ) : ℂ) * I)) := by
  let ν : ℂ := ((2 * τ : ℝ) : ℂ) * I
  let B : ℝ := ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel q ν t‖
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hbase (v w : ℝ) : q ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    calc
      q = Real.sqrt (q ^ 2) := (Real.sqrt_sq hq.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg v, sq_nonneg w])
  have hrad (v w : ℝ) : q ≤ 2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    linarith only [hbase v w, Real.sqrt_nonneg (q ^ 2 + v ^ 2 + w ^ 2)]
  have hcoords (v w : ℝ) : |v| + |w| ≤ 2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
    have hv : |v| ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs v]
      exact Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg q, sq_nonneg w])
    have hw : |w| ≤ Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs w]
      exact Real.sqrt_le_sqrt (by nlinarith only [sq_nonneg q, sq_nonneg v])
    linarith only [hv, hw]
  have hc : Continuous (fun z : ℝ × ℝ => modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) ν) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_modifiedBesselKOrder_arg (hq.trans_le (hrad z.1 z.2)) ν).continuousAt.comp'
      (f := fun z : ℝ × ℝ => 2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2))
      (x := z) (by fun_prop)
  apply ((integrable_exp_abs.mul_prod integrable_exp_abs).const_mul (Real.exp q * B)).mono'
    hc.aestronglyMeasurable
  filter_upwards with z
  calc
    _ ≤ Real.exp (q - 2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) * B :=
      norm_modifiedBesselKOrder_le_positive_base hq (hrad z.1 z.2) ν
    _ ≤ Real.exp (q - |z.1| - |z.2|) * B := by
      apply mul_le_mul_of_nonneg_right _ hB
      apply Real.exp_le_exp.mpr
      linarith only [hcoords z.1 z.2]
    _ = _ := by
      rw [show q - |z.1| - |z.2| = q + (-|z.1|) + (-|z.2|) by ring,
        Real.exp_add, Real.exp_add]
      ring

private theorem square_slice_eq {q : ℝ} (hq : 0 < q) (τ v : ℝ) :
    (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ) =
      ∫ w : ℝ, modifiedBesselKOrder
        (2 * Real.sqrt (q ^ 2 + v ^ 2 + w ^ 2)) (((2 * τ : ℝ) : ℂ) * I) := by
  have hr : 0 < Real.sqrt (q ^ 2 + v ^ 2) := Real.sqrt_pos.mpr
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq) (sq_nonneg v))
  rw [besselHalfOrderSquare_eq_radial_integral hr]
  simp_rw [Real.sq_sqrt (add_nonneg (sq_nonneg q) (sq_nonneg v))]

/-- Every positive radial square slice has finite mass. -/
theorem integrable_besselHalfOrderSquare_slice_of_pos {q : ℝ} (hq : 0 < q) (τ : ℝ) :
    Integrable (fun v : ℝ => besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2))) := by
  have hi := (integrable_bessel_plane_slice_of_pos hq τ).integral_prod_left
  have hc : Integrable (fun v : ℝ =>
      (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ)) :=
    hi.congr (Eventually.of_forall fun v => (square_slice_eq hq τ v).symm)
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.ofReal_re] using
    Complex.reCLM.integrable_comp hc

private theorem imaginary_order_real (x τ : ℝ) :
    modifiedBesselKOrder x ((τ : ℂ) * I) =
      ((modifiedBesselKOrder x ((τ : ℂ) * I)).re : ℂ) := by
  have hn : conj ((τ : ℂ) * I) = -((τ : ℂ) * I) := by simp
  have hh := modifiedBesselKOrder_conj x ((τ : ℂ) * I)
  rw [hn, modifiedBesselKOrder_neg] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.conj_im] at hi
  apply Complex.ext
  · simp only [Complex.ofReal_re]
  · simp only [Complex.ofReal_im]
    linarith only [hi]

/-- The positive radial square representation holds down to every positive cutoff. -/
theorem two_pi_mul_firstTail_eq_square_integral_of_pos {q : ℝ} (hq : 0 < q) (τ : ℝ) :
    2 * Real.pi * besselFirstWeightedTail τ q =
      ∫ v : ℝ, besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) := by
  have hF := integrable_bessel_plane_slice_of_pos hq τ
  have he : (∫ v : ℝ,
      (besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) : ℂ)) =
      ((2 * Real.pi * besselFirstWeightedTail τ q : ℝ) : ℂ) := by
    simp_rw [square_slice_eq hq τ]
    rw [← integral_prod _ hF]
    change (∫ z : ℝ × ℝ, modifiedBesselKOrder
      (2 * Real.sqrt (q ^ 2 + z.1 ^ 2 + z.2 ^ 2)) (((2 * τ : ℝ) : ℂ) * I)) = _
    rw [integral_radial_plane hq.le
      (fun u => modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I))]
    have hw : (fun u : ℝ => u • modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)) =
        fun u : ℝ => ((u * (modifiedBesselKOrder (2 * u) (((2 * τ : ℝ) : ℂ) * I)).re : ℝ) : ℂ) := by
      funext u
      rw [Complex.real_smul]
      conv_lhs => rw [imaginary_order_real]
      simp only [Complex.ofReal_mul]
    rw [hw, integral_complex_ofReal]
    simp only [Complex.real_smul, Complex.ofReal_mul, besselFirstWeightedTail]
  rw [integral_complex_ofReal] at he
  exact (Complex.ofReal_injective he).symm

/-- The first weighted tail is strictly positive at every positive cutoff. -/
theorem besselFirstWeightedTail_pos_of_pos {q : ℝ} (hq : 0 < q) (τ : ℝ) :
    0 < besselFirstWeightedTail τ q := by
  have hp (v : ℝ) : 0 < besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) :=
    besselHalfOrderSquare_pos (Real.sqrt_pos.mpr
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hq) (sq_nonneg v))) τ
  have hi := integrable_besselHalfOrderSquare_slice_of_pos hq τ
  have hs : Function.support
      (fun v : ℝ => besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2))) = univ := by
    ext v
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hp v).ne'
  have hh : 0 < ∫ v : ℝ, besselHalfOrderSquare τ (Real.sqrt (q ^ 2 + v ^ 2)) := by
    apply (integral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun v => (hp v).le) hi).mpr
    rw [hs]
    simp
  rw [← two_pi_mul_firstTail_eq_square_integral_of_pos hq τ] at hh
  exact (mul_pos_iff_of_pos_left (by positivity : 0 < 2 * Real.pi)).mp hh

/-- The exponential reserve reaches every positive cutoff, uniformly in frequency. -/
theorem besselFirstWeightedTail_exp_lower_of_pos {q u : ℝ}
    (hq : 0 < q) (hqu : q ≤ u) (τ : ℝ) :
    Real.exp (-2 * (u - q)) * besselFirstWeightedTail τ q ≤ besselFirstWeightedTail τ u := by
  have hi := integral_mono_ae
    ((integrable_besselHalfOrderSquare_slice_of_pos hq τ).const_mul (Real.exp (-2 * (u - q))))
    (integrable_besselHalfOrderSquare_slice_of_pos (hq.trans_le hqu) τ)
    (Eventually.of_forall fun v => besselHalfOrderSquare_slice_exp_lower hq hqu τ v)
  rw [integral_const_mul, ← two_pi_mul_firstTail_eq_square_integral_of_pos hq τ,
    ← two_pi_mul_firstTail_eq_square_integral_of_pos (hq.trans_le hqu) τ] at hi
  apply (mul_le_mul_iff_right₀ (by positivity : 0 < 2 * Real.pi)).mp
  convert hi using 1 <;> ring

#print axioms besselFirstWeightedTail_pos_of_pos
#print axioms besselFirstWeightedTail_exp_lower_of_pos

end GaloisForLFunctions.CompletedArithmeticForms
