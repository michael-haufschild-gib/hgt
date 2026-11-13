/-
Comparison with the principal signal adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SignalsAndCommonProbes
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.PrincipalSlotEstimate
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LowPhysicalInverseBounds

/-!
# Comparison with the principal signal

Bare high summands and source coefficients; slot masses and source corrections of the principal
signal comparison; the normalized principal residue differs from the reciprocal Hecke signal by
a prime-scale saving; normalized probe Gauss sums.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter Asymptotics Complex
namespace PrincipalSignalComparison
open ProbePhysical HeckeFamily PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal

theorem raw_inverse_ae_reciprocal (χ : Character) (a : ℝ) :
    (fun t : ℝ => (LFunction χ ((a : ℂ)+t*I))⁻¹) =ᵐ[volume]
      (fun t => HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I)) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply (HeckeReciprocal.reciprocal_eq_inv χ ?_ ?_).symm
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem raw_quotient_integral_eq (χ : Character) (a : ℝ) (F : ℝ → ℂ) :
    (∫ t : ℝ, F t / LFunction χ ((a : ℂ)+t*I)) =
      ∫ t : ℝ, F t * HeckeReciprocal.reciprocal χ ((a : ℂ)+t*I) := by
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [div_eq_mul_inv, ht]

variable {κ ι : Type*}

def slotMass (T : κ → Finset ι) (w : κ → ι → ℝ) (j : κ) : ℝ := ∑ p ∈ T j, w j p

def slotProduct (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) : ℂ :=
  ∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s

def slotRatio (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) : ℂ :=
  slotProduct S T w Q A η s / PrincipalSlotEstimate.principalScalar S (slotMass T w)

structure SlotBounds (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(7/8 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

def slotErrorConstant (S : Finset κ) : ℝ := S.card * 2 ^ S.card * 1440

theorem slot_scalar_ne_zero (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P) :
    PrincipalSlotEstimate.principalScalar S (slotMass T w) ≠ 0 :=
  PrincipalSlotEstimate.principalScalar_ne_zero S _ h.mass_pos

theorem slotRatio_error (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 7/8 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(7/8 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem slotRatio_bound (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SlotBounds S T w Q A η P)
    {s : ℂ} (hs : 7/8 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(7/8 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [slotRatio_error S T w Q A η h hs]

theorem principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7/8 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hQslit : (Q : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hQ0
  have hg := principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1-coordR Q A s (1/6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1/6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1/6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ)^s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1/6) hR hV hD)
    (principal_correction_ne_zero hQ hA hη hs)

theorem slotRatio_continuous_line (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SlotBounds S T w Q A η P) {a : ℝ} (ha : 7/8 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

def slotResidue (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
      H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I)

theorem slotResidue_eq_reciprocal (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S T w Q A η = (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I) *
        slotRatio S T w Q A η ((a : ℂ)+t*I) := by
  unfold slotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def kernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-11/16) Z ((a : ℂ)+t*I)

def kernelEnvelope (a C Z : ℝ) : ℝ :=
  Z^(a-11/16) * Real.exp ((a-5/6)^2) * ((3/2)*C)

theorem kernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    {a Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (kernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.quotient_holomorphic χ H hH ha hβ) (-11/16) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem kernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (t : ℝ) : ‖kernel χ H a Z t‖ ≤ kernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := HeckeSignalShift.quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ)+t*I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold kernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z^(a+(-11/16))*Real.exp ((a-5/6)^2)) *
        (((3/2)*C)*(1+|t|^2))*Real.exp (-(t^2)) := by gcongr
    _ = _ := by unfold kernelEnvelope polynomialGaussian; ring_nf

theorem kernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C Z : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2)) :
    Integrable (kernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (kernelEnvelope a C Z)).mono'
    (kernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem slotResidue_bound_of_reciprocal_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a C : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C*(1+|s.im|^2))
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    {P Z : ℝ} (h : SlotBounds S T w Q A η P) (hZ : 1 ≤ Z) :
    Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
      ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
        (HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S) *
          Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  have hZ0 : 0 < Z := by linarith
  have hP0 : 0 < P := by linarith [h.lower]
  have hg := kernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
  have hc := slotRatio_continuous_line S T w Q A η h ha.le
  have hbound (t : ℝ) := slotRatio_bound S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
  refine ⟨hint, ?_⟩
  have herror (t : ℝ) := slotRatio_error S T w Q A η h
    (s := (a : ℂ)+t*I) (by simpa using ha.le)
  have heint := hg.mul_bdd (hc.sub continuous_const).aestronglyMeasurable (ae_of_all _ herror)
  have heq : slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z =
      (1/(2*Real.pi) : ℂ) * ∫ t : ℝ,
        kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I) - 1) := by
    rw [slotResidue_eq_reciprocal,
      HeckeSignalBounds.contour_shift_left χ H hH hb (-11/16) a ha ha2 hβ hZ,
      ← mul_sub]
    change (1/(2*Real.pi) : ℂ) *
      ((∫ t : ℝ, kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) -
        ∫ t : ℝ, kernel χ H a Z t) = _
    rw [← integral_sub hint hg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with t
    change kernel χ H a Z t * _ - kernel χ H a Z t = _
    ring_nf
  rw [heq, norm_mul]
  have he0 : 0 ≤ slotErrorConstant S * P^(-(7/8 : ℝ)) := by
    unfold slotErrorConstant
    positivity
  have hbnd (t : ℝ) :
      ‖kernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ)+t*I)-1)‖ ≤
        (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))) *
          polynomialGaussian 2 t := by
    rw [norm_mul]
    calc
      _ ≤ (kernelEnvelope a C Z * polynomialGaussian 2 t) *
          (slotErrorConstant S * P^(-(7/8 : ℝ))) :=
        mul_le_mul (kernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
          (norm_nonneg _) (mul_nonneg (by unfold kernelEnvelope; positivity)
            (polynomialGaussian_nonneg 2 t))
      _ = _ := by ring_nf
  have hn := norm_integral_le_of_norm_le
    ((polynomialGaussian_integrable 2).const_mul
      (kernelEnvelope a C Z * (slotErrorConstant S * P^(-(7/8 : ℝ)))))
    (ae_of_all _ hbnd)
  have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1/(2*Real.pi) : ℂ))
  rw [integral_const_mul] at hm
  convert hm using 1 <;> try rfl
  unfold kernelEnvelope HeckeSignalShift.infinityConstant
  ring_nf

theorem exists_slotResidue_bound (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I)) ∧
        ‖slotResidue χ H a Z S T w Q A η - signal χ H (-11/16) Z‖ ≤
          D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    exact slotResidue_bound_of_reciprocal_bound χ H hH hb ha ha2 hβ hC hR S T w Q A η h hZ

theorem raw_slot_integrable (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => kernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ)^(((a : ℂ)+t*I)-11/16) * Complex.exp ((((a : ℂ)+t*I)-5/6)^2) *
        H ((a : ℂ)+t*I) / LFunction χ ((a : ℂ)+t*I) *
          slotRatio S T w Q A η ((a : ℂ)+t*I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold kernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

open ProbePhysical Eisenstein CompletedGauss

theorem prime_coprime_of_norm_gt (η : Character) (P : PrimeIdeal)
    (hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val) : IsCoprime P.val η.modulus := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime P.property
  let : P.val.IsMaximal := Ideal.IsPrime.isMaximal inferInstance P.property.ne_zero
  rw [Ideal.isCoprime_iff_codisjoint,
    ← (Ideal.isMaximal_def.mp (inferInstance : P.val.IsMaximal)).not_le_iff_codisjoint]
  intro hle
  have hn : 0 < Ideal.absNorm η.modulus := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr η.modulus_ne_bot)
  exact (Nat.not_le_of_gt hN) (Nat.le_of_dvd hn (Ideal.absNorm_dvd_absNorm_of_le hle))

def annularPrimeWeight (W : ℝ → ℝ) (scale : ℝ) (P : PrimeIdeal) : ℝ :=
  W ((Ideal.absNorm P.val : ℝ)/scale) * (Ideal.absNorm P.val : ℝ)^(-(5/6 : ℝ))

theorem annularPrimeWeight_nonneg (W : ℝ → ℝ) (hW : ∀ x, 0 ≤ W x)
    (scale : ℝ) (P : PrimeIdeal) : 0 ≤ annularPrimeWeight W scale P :=
  mul_nonneg (hW _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem annularPrimeWeight_norm_lower (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : c*scale ≤ (Ideal.absNorm P.val : ℝ) :=
  (le_div_iff₀ hscale).mp (hW _ (left_ne_zero_of_mul hw))

theorem annularPrimeWeight_target_unit (W : ℝ → ℝ) (c scale : ℝ)
    (hscale : 0 < scale) (hW : ∀ x, W x ≠ 0 → c ≤ x) (η : Character)
    (hthreshold : (Ideal.absNorm η.modulus : ℝ) < c*scale) (P : PrimeIdeal)
    (hw : annularPrimeWeight W scale P ≠ 0) : ‖idealCoeff η P.val‖ = 1 := by
  have hN : Ideal.absNorm η.modulus < Ideal.absNorm P.val := by
    exact_mod_cast hthreshold.trans_le (annularPrimeWeight_norm_lower W c scale hscale hW P hw)
  exact idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero (prime_coprime_of_norm_gt η P hN)

def sourceCorrection (η : Character) (E : Finset (Ideal Eisenstein.O)) (s : ℂ) : ℂ :=
  globalClosedCorrection η E s 1 (1/6)

theorem sourceCorrection_eq_principal (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) : sourceCorrection η E = principalCorrection η E := by
  funext s
  exact source_globalCorrection_principal E hE η s

theorem sourceCorrection_differentiable (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | 7/8 < s.re} :=
  (globalClosedCorrection_analytic_x η E hE.tail 1 (1/6) (by norm_num) (by norm_num)).differentiableOn

theorem sourceCorrection_bound (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : 7/8 < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1/2 :=
  globalClosedCorrection_bound η E hE.tail s 1 (1/6) hs.le (by norm_num) (by norm_num)

def actualSlotResidue (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (a Z : ℝ) (S : Finset κ)
    (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ) : ℂ :=
  slotResidue (η.excludePrimes E hE.prime) (sourceCorrection η E) a Z S T w
    (fun _ P => Ideal.absNorm P.val)
    (fun _ P => actualAPhase η (primaryIdealGenerator P.val)) (fun _ P => idealCoeff η P.val)

theorem actual_principal_slot (η : Character) (P : PrimeIdeal) (s : ℂ) :
    compensatedReplacement (coordV (Ideal.absNorm P.val) (1/6))
      (coordW (Ideal.absNorm P.val) 1 1) (coordD (Ideal.absNorm P.val) (idealCoeff η P.val) 1 s)
      (idealMarkedClosed η P s 1 (1/6))
      (star (idealCoeff η P.val) * (Ideal.absNorm P.val : ℂ)^s)
      ((Ideal.absNorm P.val : ℂ)^(-1 : ℂ)) / idealClosedCorrection η P s 1 (1/6) =
      principalSlot (Ideal.absNorm P.val) (actualAPhase η (primaryIdealGenerator P.val))
        (idealCoeff η P.val) s := rfl

theorem exists_actualSlotResidue_bound (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset PrimeIdeal) (w : κ → PrimeIdeal → ℝ) (P Z : ℝ),
      480 ≤ P → 1440 * P^(-(7/8 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      ‖actualSlotResidue η E hE a Z S T w -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  obtain ⟨D, hD, hb⟩ := exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE)
    ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro T w P Z hP hsmall hw hnorm hcop hmass hZ
  exact (hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z
    ⟨hP, hsmall, hw, hnorm, fun j hj p hp => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp),
      hmass⟩ hZ).2

open PrincipalMellinResidues

theorem source_normalizer_cast (S : Finset κ) (T : κ → Finset ι) (w : κ → ι → ℝ)
    {Z ℓ : ℝ} (hZ : 0 < Z) :
    (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ) =
      (Z : ℂ)^(((-ℓ/6 : ℝ) : ℂ)) * PrincipalSlotEstimate.principalScalar S (slotMass T w) := by
  simp only [Probe.principalScalar, PrincipalSlotEstimate.principalScalar,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_cpow hZ.le]
  ring_nf

theorem source_normalizer_ne_zero (S : Finset κ) (T : κ → Finset ι)
    (w : κ → ι → ℝ) {Z ℓ : ℝ} (hZ : 0 < Z)
    (hm : ∀ j ∈ S, 0 < slotMass T w j) :
    (Probe.principalScalar S Z ℓ (slotMass T w) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Probe.principalScalar_ne_zero S hZ hm)

theorem source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z^(17/48 : ℝ) : ℝ) : ℂ)^(1/3 : ℂ) * (Z : ℂ)^(s-5/6) =
      (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) * (Z : ℂ)^(s-11/16) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (17/48) (1/3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

theorem normalized_source_double_residue (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1/6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z χ s H B 1 (1/6)) /
        (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)) =
      (Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) / LFunction χ s *
        slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := source_power_identity hZ s
  have hz : (Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)) *
          ((Z : ℂ)^(((-(1/6 : ℝ)/6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ)^(s-11/16) * Complex.exp ((s-5/6)^2) * H 1 (1/6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

def sourceResidueIntegral (W0 W1 : SchwartzMap ℝ ℂ) (M : Ideal Eisenstein.O) [NeZero M]
    (χ : Character) (a X Y Z : ℝ) (H B : ℂ → ℂ → ℂ → ℂ) : ℂ :=
  verticalIntegral a (fun s => fixedPrincipalResidue M ^ 2 / 6 *
    sourceMultiplier W0 W1 X Y Z χ s (H s) (B s) 1 (1/6))

theorem sourceResidueIntegral_normalized (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I)) :
    sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z^(17/48 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)) =
        slotResidue χ (fun s => H s 1 (1/6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral slotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem source_double_residue_integrable (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) =
      slotProduct S T w Q A η ((a : ℂ)+t*I))
    (hi : Integrable (fun t : ℝ => kernel χ (fun s => H s 1 (1/6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ)+t*I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z χ ((a : ℂ)+t*I)
        (H ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) := by
  have hiraw := raw_slot_integrable χ (fun s => H s 1 (1/6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 1/6))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M * (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

def activePools (T : κ → Finset ι) (w : κ → ι → ℝ) (j : κ) : Finset ι :=
  (T j).filter (fun p => w j p ≠ 0)

theorem slotMass_active (T : κ → Finset ι) (w : κ → ι → ℝ) :
    slotMass (activePools T w) w = slotMass T w := by
  funext j
  simp only [slotMass, activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem slotProduct_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotProduct S (activePools T w) w Q A η s = slotProduct S T w Q A η s := by
  apply Finset.prod_congr rfl
  intro j hj
  simp only [activePools, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hw : w j p = 0 <;> simp [hw]

theorem slotRatio_active (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (s : ℂ) :
    slotRatio S (activePools T w) w Q A η s = slotRatio S T w Q A η s := by
  rw [slotRatio, slotRatio, slotProduct_active, slotMass_active]

theorem slotResidue_active (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    slotResidue χ H a Z S (activePools T w) w Q A η = slotResidue χ H a Z S T w Q A η := by
  simp only [slotResidue, slotRatio_active]

theorem slotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (7/8)*ell)
    (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 7/8 < s.re})
    (hb : ∀ s : ℂ, 7/8 < s.re → ‖H s-1‖ ≤ 1/2)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset ι) (w Q : ℝ → κ → ι → ℝ) (A η : ℝ → κ → ι → ℂ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      SlotBounds S (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z) (c0*Z^ell)) :
    (fun Z : ℝ => slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
        signal χ H (-11/16) Z) =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) := by
  obtain ⟨D, hD, hd⟩ := exists_slotResidue_bound χ H hH hb ha ha2 hβ S
  apply IsBigO.of_bound (D*c0^(-(7/8 : ℝ)))
  filter_upwards [hdata, eventually_ge_atTop (1 : ℝ)] with Z hz hZ
  have hZ0 : 0 < Z := by linarith
  have he := (hd (activePools (T Z) (w Z)) (w Z) (Q Z) (A Z) (η Z)
    (c0*Z^ell) Z hz hZ).2
  rw [slotResidue_active] at he
  have hp : (c0*Z^ell)^(-(7/8 : ℝ)) = c0^(-(7/8 : ℝ))*Z^(ell*(-(7/8 : ℝ))) := by
    rw [Real.mul_rpow hc0.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
  rw [hp] at he
  have hpow : Z^(a-11/16+ell*(-(7/8 : ℝ))) ≤ Z^(a-11/16-saving) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have he' : ‖slotResidue χ H a Z S (T Z) (w Z) (Q Z) (A Z) (η Z) -
      signal χ H (-11/16) Z‖ ≤ (D*c0^(-(7/8 : ℝ)))*Z^(a-11/16-saving) := by
    calc
      _ ≤ D*Z^(a-11/16)*(c0^(-(7/8 : ℝ))*Z^(ell*(-(7/8 : ℝ)))) := he
      _ = (D*c0^(-(7/8 : ℝ)))*Z^(a-11/16+ell*(-(7/8 : ℝ))) := by
        rw [Real.rpow_add hZ0]
        ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hZ0 _)] using he'

theorem actualSlotResidue_isBigO (S : Finset κ) (c0 ell saving : ℝ)
    (hc0 : 0 < c0) (hsaving : saving ≤ (7/8)*ell)
    (E : Finset (Ideal Eisenstein.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (T : ℝ → κ → Finset PrimeIdeal) (w : ℝ → κ → PrimeIdeal → ℝ)
    (hdata : ∀ᶠ Z : ℝ in atTop,
      SlotBounds S (activePools (T Z) (w Z)) (w Z) (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val)
        (c0*Z^ell)) :
    (fun Z : ℝ => actualSlotResidue η E hE a Z S (T Z) (w Z) -
        signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z)
      =O[atTop] (fun Z : ℝ => Z^(a-11/16-saving)) :=
  slotResidue_isBigO S c0 ell saving hc0 hsaving (η.excludePrimes E hE.prime)
    (sourceCorrection η E) (sourceCorrection_differentiable η E hE)
    (sourceCorrection_bound η E hE) ha ha2 hβ T w
    (fun _ _ p => Ideal.absNorm p.val)
    (fun _ _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ _ p => idealCoeff η p.val) hdata

theorem fixedPrincipal_product_eq (E : Finset (Ideal Eisenstein.O)) (hE : SourceExclusions E) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    fixedPrincipal (∏ p ∈ E, p) = fixedSourcePrincipal E hE.prime := rfl

/-- The normalized principal residue differs from the reciprocal Hecke signal by a prime-scale saving. -/
theorem exists_normalized_actual_source_bound (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 7/8 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P^(-(7/8 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ)+t*I) 1 (1/6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ)+t*I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1/6) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z^(17/48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ)+t*I) (globalClosedCorrection η E ((a : ℂ)+t*I)) (B ((a : ℂ)+t*I)) 1 (1/6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z^(17/48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-11/16) Z‖ ≤
        D * Z^(a-11/16) * P^(-(7/8 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sourceCorrection_differentiable η E hE) (sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : SlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end PrincipalSignalComparison
end

end

noncomputable section
namespace ProbePrincipalResidueActual
def residueWeights {κ : Type*} (W : κ → ℝ → ℝ) (scale : κ → ℝ)
    (j : κ) (p : HeckeIdealSeries.PrimeIdeal) : ℝ :=
  W j ((Ideal.absNorm p.val : ℝ)/scale j) * (Ideal.absNorm p.val : ℝ)^(-(5/6 : ℝ))


end ProbePrincipalResidueActual
end

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePrincipalNormalizer
open HeckeFamily PrincipalMellinResidues PrincipalSignalComparison
local notation "O" => Eisenstein.O

/-- Both Mellin factors and the principal residue are nonzero. -/
theorem sourceResidueConstant_ne_zero (M : Ideal O) [NeZero M]
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0) :
    sourceResidueConstant W0 W1 M≠0 := by
  have hm0 := ProbeRadialMellin.radial_mellin_one_sixth_ne_zero W0 a0 b0 ha0 hW0
    hreal0 hpos0 hne0
  have hm1 : mellin W1 1 ≠ 0 := by
    intro hz
    have hp := (ProbeRadialMellin.positive_source_mellin W1 a1 b1 ha1 hW1
      hreal1 hpos1 hne1 1).1
    norm_num only [Complex.ofReal_one] at hp
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hm1 hm0)
    (pow_ne_zero 2 (fixedPrincipalResidue_ne_zero M))) (by norm_num)

theorem signed_source_normalizer_ne_zero {κ ι : Type*} [DecidableEq κ]
    (M : Ideal O) [NeZero M] (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hreal0 : ∀y,(W0 y).im=0) (hreal1 : ∀y,(W1 y).im=0)
    (hpos0 : ∀y,0≤(W0 y).re) (hpos1 : ∀y,0≤(W1 y).re) (hne0 : W0≠0) (hne1 : W1≠0)
    (S : Finset κ) (T : κ→Finset ι) (w : κ→ι→ℝ) (Z ℓ : ℝ) (hZ : 0< Z)
    (hm : ∀j∈S,0< slotMass T w j) :
    sourceResidueConstant W0 W1 M*(Probe.principalScalar S Z ℓ (slotMass T w):ℂ)≠0 :=
  mul_ne_zero (sourceResidueConstant_ne_zero M W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hreal0 hreal1 hpos0 hpos1 hne0 hne1) (source_normalizer_ne_zero S T w hZ hm)

end ProbePrincipalNormalizer
end

end

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace ProbeRaySlots
open ProbePrincipalResidueActual HeckeFamily ProbePhysical PrincipalSignalComparison
local notation "Id" => Ideal Eisenstein.O

theorem power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0< c) (hd : c≤ d) (hmin : 0< ellMin)
    (ell : ι→ℝ) (hell : ∀j,ellMin≤ ell j) :
    ∀ᶠZ : ℝ in atTop,
      1≤ Z ∧ 480≤ c*Z^ellMin ∧ 1440*(c*Z^ellMin)^(-(7/8:ℝ))≤1 ∧
      (∀j,480≤ c*Z^(ell j) ∧ (η.modulus.absNorm:ℝ)< c*Z^(ell j)) ∧
      (∀j,∀P∈pool C S c d (Z^(ell j)),
        c*Z^ellMin≤(P.val.absNorm:ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val∉S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ=>1440*(c*Z^ellMin)^(-(7/8:ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_def] using ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<7/8)).comp ht).const_mul (1440:ℝ)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop (480:ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0< Z := by linarith
  have hmono (j : ι) : c*Z^ellMin≤ c*Z^(ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ,h480,hsmall.le,fun j=>⟨h480.trans (hmono j),hmod.trans_le (hmono j)⟩,?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c*Z^ellMin<(P.val.absNorm:ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le,prime_coprime_of_norm_gt η P (hmod.trans hn),(mem_pool C S c d _ P).mp hP |>.2.2.2⟩

variable (M : Id) [NeZero M]
local instance : Finite (Eisenstein.O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (Eisenstein.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
include hH

theorem power_ray_mass_and_normalizer {ι : Type*} [Fintype ι]
    (S : Finset Id) (W : ι→ℝ→ℝ) (c d : ℝ) (hc : 0< c) (hd : c≤ d)
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hp : ∀j,tsupport (W j)⊆Set.Ioi 0) (hW0 : ∀j y,0≤ W j y) (hne : ∀j,W j≠0)
    (ell : ι→ℝ) (hell : ∀j,0< ell j) (eps : ℝ) (heps : 0< eps) :
    ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      (∀j,0< slotMass T (residueWeights W (fun j=> Z^(ell j))) j) ∧
      |(Probe.principalScalar Finset.univ Z (∑j,ell j)
        (slotMass T (residueWeights W (fun j=> Z^(ell j)))))⁻¹|≤ Z^eps := by
  have hm : ∀ᶠZ : ℝ in atTop,∀j,0< slotMass
      (fun j=> pool (RayQuotient.identityClass M H) S c d (Z^(ell j)))
      (residueWeights W (fun j=> Z^(ell j))) j := by
    apply Filter.eventually_all.mpr
    intro j
    exact (tendsto_rpow_atTop (hell j)).eventually
      (ray_pool_mass_eventually_positive M H hH S (W j) c d hc hd (hsupp j)
        (hW j) (hcompact j) (hp j) (hW0 j) (hne j))
  have hi := ProbeRayNormalization.ray_principalScalar_inverse_subpower M H hH Finset.univ S W
    (fun _=> c) (fun _=> d) ell (fun _ _=> hc) (fun _ _=> hd) (fun j _=> hsupp j)
    (fun j _=> hW j) (fun j _=> hcompact j) (fun j _=> hp j) (fun j _=> hW0 j) (fun j _=> hne j)
    (fun j _=> hell j) eps heps
  filter_upwards [hm,hi] with Z hmass hinv
  exact ⟨hmass,hinv⟩
end ProbeRaySlots
end

end

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace ProbeHighRowFamily
open ProbePrincipalResidueActual HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues
local notation "O" => Eisenstein.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0< c) (hcb : c≤ b)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤ W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤ C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=> Z^(ell j))) Z (1/6) hZ (fun j _=> hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6)
        (slotMass (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=> Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end ProbeHighRowFamily

end

end

noncomputable section
open HeckeIdealSeries Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical ContDiff
open Filter
namespace ProbePhysical
open ProbePrincipalResidueActual ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
local notation "O" => Eisenstein.O

/-- The low-frequency detector retains the three-sixteenths bound after normalization. -/
theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer‖≤
        C*Z^(3/16+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(3/16+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(3/16+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbePhysical
open Eisenstein  CubicEisenstein CanonicalRowCompletion GaussianShiftedPartition
open CanonicalQuadraticSieve CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentFourier CenteredMomentFirstPoisson CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

/-- The scaled Chinese remainder coordinates separate the two Fourier sums. -/
theorem coprime_function_fourier (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime a b)
    [Fintype (Residue a)] [Fintype (Residue b)] [Fintype (Residue (a * b))]
    (Fa : Residue a → ℂ) (F : Residue b → ℂ)
    (h : Residue (a * b)) :
    (∑ x : Residue (a * b),
      Fa (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
        F (frequencyReduction b (a * b) (dvd_mul_left b a) x) *
          primitiveTrace (a * b) (mul_ne_zero ha hb) (h * x)) =
      (∑ x : Residue a, Fa (Ideal.Quotient.mk _ b*x) *
        primitiveTrace a ha (frequencyReduction a (a*b) (dvd_mul_right a b) h*x)) *
      (∑ y : Residue b, F (Ideal.Quotient.mk _ a*y) *
        primitiveTrace b hb (frequencyReduction b (a*b) (dvd_mul_left b a) h*y)) := by
  let ua := residueUnit a b hcop
  let ub := residueUnit b a hcop.symm
  let e : Residue a × Residue b ≃ Residue (a * b) :=
    (ua.mulLeft.prodCongr ub.mulLeft).trans (principalCRT a b hcop).toEquiv.symm
  have heproj (x : Residue a × Residue b) : principalCRT a b hcop (e x) =
      ((ua : Residue a) * x.1, (ub : Residue b) * x.2) := by
    change (principalCRT a b hcop).toEquiv
      ((principalCRT a b hcop).toEquiv.symm ((ua : Residue a) * x.1, (ub : Residue b) * x.2)) = _
    exact (principalCRT a b hcop).toEquiv.apply_symm_apply _
  have he (x : Residue a × Residue b) : e x =
      scaledResidue a b (a * b) rfl x.1 + scaledResidue b a (a * b) (mul_comm a b) x.2 := by
    apply (principalCRT a b hcop).injective
    rw [heproj, map_add, principalCRT_scaled_left, principalCRT_scaled_right]
    simp only [Prod.mk_add_mk, add_zero, zero_add, ua, ub, residueUnit_coe]
  have hproj (x : Residue (a * b)) :
      (frequencyReduction a (a * b) (dvd_mul_right a b) x,
        frequencyReduction b (a * b) (dvd_mul_left b a) x) = principalCRT a b hcop x := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [frequencyReduction_mk, principalCRT_mk]
  have hprojA (x : Residue a × Residue b) :
      frequencyReduction a (a * b) (dvd_mul_right a b) (e x) = Ideal.Quotient.mk _ b * x.1 := by
    have ht := congrArg Prod.fst (hproj (e x))
    rw [heproj] at ht
    simpa only [ua, residueUnit_coe] using ht
  have hprojB (x : Residue a × Residue b) :
      frequencyReduction b (a * b) (dvd_mul_left b a) (e x) = Ideal.Quotient.mk _ a * x.2 := by
    have ht := congrArg Prod.snd (hproj (e x))
    rw [heproj] at ht
    simpa only [ub, residueUnit_coe] using ht
  rw [← e.sum_comp]
  simp_rw [hprojA, hprojB]
  simp only [ he, mul_add, AddChar.map_add_eq_mul,
    primitiveTrace_scaled a b (a * b) rfl ha hb (mul_ne_zero ha hb),
    primitiveTrace_scaled b a (a * b) (mul_comm a b) hb ha (mul_ne_zero ha hb)]
  simp only [Fintype.sum_prod_type, ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

lemma elementFourier_const_mul (c : O) (hc : c≠0) (F : O → ℂ) (H : O) (B : ℂ) :
    elementFourier c hc (fun m => B*F m) H = B*elementFourier c hc F H := by
  simp only [elementFourier, mul_assoc, tsum_mul_left]

lemma bareMoving_product (A B s r : O) (hs : Supported (Ideal.span {s}))
    (hr : Supported (Ideal.span {r})) (hcop : IsCoprime s r) (m : O) :
    idealRowHom m (Ideal.span {A*B}) *
      sexticGauss (s*r) (mul_ne_zero (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)) (-m) =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      ((idealRowHom m (Ideal.span {A}) * sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr) (-m))) := by
  rw [sexticGauss_coprime_product s r hs hr hcop]
  rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  ring

theorem barePhysicalFourier_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    barePhysicalFourier (A*B) (s*r) (mul_ne_zero hA hB)
      (mul_ne_zero (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H *
      barePhysicalFourier B r hB (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr) H := by
  have hsc : IsCoprime s r := hcop.of_mul_left_right.of_mul_right_right
  have hc1 : IsCoprime (B*r) s := hcop.of_mul_left_right.symm
  have hc2 : IsCoprime (A*s) r := hcop.of_mul_right_right
  have hAs := mul_ne_zero hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs)
  have hBr := mul_ne_zero hB (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)
  let := finiteEisensteinQuotientOfNonzero hAs
  let := finiteEisensteinQuotientOfNonzero hBr
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero hAs hBr)
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let : Fintype (Residue (B*r)) := Fintype.ofFinite _
  let : Fintype (Residue ((A*s)*(B*r))) := Fintype.ofFinite _
  have he := coprime_function_fourier (A*s) (B*r) hAs hBr hcop
    (movingQuotient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
    (movingQuotient B r (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr)) (Ideal.Quotient.mk _ H)
  simp only [frequencyReduction_mk] at he
  simp_rw [movingQuotient_unit_scale A s hs (B*r) hc1,
    movingQuotient_unit_scale B r hr (A*s) hc2, mul_assoc] at he
  simp only [← Finset.mul_sum] at he
  have hexpand : elementFourier ((A*s)*(B*r)) (mul_ne_zero hAs hBr)
      (fun m => (idealRowHom m (Ideal.span {A}) * sexticGauss s (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) (-m)) *
        (idealRowHom m (Ideal.span {B}) * sexticGauss r (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr) (-m))) H =
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      barePhysicalFourier A s hA (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H *
      barePhysicalFourier B r hB (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr) H := by
    unfold elementFourier
    rw [tsum_fintype]
    calc
      _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        have hmk := representative_spec ((A*s)*(B*r)) x
        have hred1 : frequencyReduction (A*s) ((A*s)*(B*r)) (dvd_mul_right _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        have hred2 : frequencyReduction (B*r) ((A*s)*(B*r)) (dvd_mul_left _ _) x =
            Ideal.Quotient.mk _ (representative ((A*s)*(B*r)) x) := by
          conv_lhs => rw [← hmk]
          rfl
        rw [hred1, hred2, movingQuotient_mk, movingQuotient_mk]
        ring
      _ = _ := he
      _ = _ := by
        simp only [barePhysicalFourier, elementFourier, movingQuotient, tsum_fintype]
        ring
  simp only [barePhysicalFourier] at hexpand
  unfold barePhysicalFourier
  rw [elementFourier_congr ((A*B)*(s*r)) ((A*s)*(B*r)) _ (mul_ne_zero hAs hBr) _ H (by ring)]
  simp_rw [bareMoving_product A B s r hs hr hsc]
  rw [elementFourier_const_mul, hexpand]
  ring

theorem bareCongruenceCoefficient_product (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
    (idealRowHom r (Ideal.span {s}) * idealRowHom s (Ideal.span {r})) *
      (idealRowHom (B*r) (Ideal.span {A}) * (idealRowHom (B*r) (Ideal.span {s}))⁻¹) *
      (idealRowHom (A*s) (Ideal.span {B}) * (idealRowHom (A*s) (Ideal.span {r}))⁻¹) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  have he := barePhysicalFourier_product A B s r hA hB hs hr hcop H
  simp only [barePhysicalFourier_eq] at he
  have hnorm : Ideal.absNorm (Ideal.span {s*r}) =
      Ideal.absNorm (Ideal.span {s}) * Ideal.absNorm (Ideal.span {r}) := by
    rw [← Ideal.span_singleton_mul_span_singleton, map_mul]
  rw [hnorm, Nat.cast_mul] at he
  have hns : (Ideal.absNorm (Ideal.span {s}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs))
  have hnr : (Ideal.absNorm (Ideal.span {r}):ℂ)≠0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (CenteredMomentSupportedCorrelation.supported_element_ne_zero r hr))
  apply mul_left_cancel₀ (mul_ne_zero hns hnr)
  rw [he]
  ring

lemma idealRowHom_ne_zero_of_coprime (s a : O)
    (hs : Supported (Ideal.span {s})) (hc : IsCoprime s a) :
    idealRowHom a (Ideal.span {s})≠0 := by
  rw [← supportedModulusCharacter_mk s hs a]
  exact (supportedModulusCharacter s hs).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff s a).mpr hc)

/-- Coprime factorization leaves only the two cross-character quotients. -/
theorem bareCongruenceCoefficient_product_reduced (A B s r : O) (hA : A≠0) (hB : B≠0)
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    bareCongruenceCoefficient (A*B) (s*r) (mul_ne_zero hA hB) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) *
      bareCongruenceCoefficient A s hA H * bareCongruenceCoefficient B r hB H := by
  rw [bareCongruenceCoefficient_product A B s r hA hB hs hr hcop H]
  have hsr := idealRowHom_ne_zero_of_coprime s r hs
    hcop.of_mul_left_right.of_mul_right_right
  have hrs := idealRowHom_ne_zero_of_coprime r s hr
    hcop.of_mul_left_right.of_mul_right_right.symm
  have hsB := idealRowHom_ne_zero_of_coprime s B hs
    hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr
    hcop.of_mul_left_left.of_mul_right_right.symm
  simp only [idealRowHom_argument_mul]
  field_simp

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

namespace ProbePhase
open CanonicalQuadraticSieve
local notation "O" => Eisenstein.O

abbrev reciprocitySign (a b : O) : ℂ := sexticReciprocityPhase a b

/-- Odd elements are exactly those not divisible by the prime above two. -/
def Odd (a : O) : Prop := ¬(2 : O) ∣ a

lemma odd_of_supported (a : O) (ha : Supported (Ideal.span {a})) : Odd a :=
  ((CanonicalQuadraticSieve.supported_span_iff a).mp ha).2

lemma odd_one : Odd (1 : O) := by
  intro h
  exact negative_two_prime.not_unit (isUnit_of_dvd_one (by simpa only [neg_dvd] using h))

lemma odd_mul (a b : O) (ha : Odd a) (hb : Odd b) : Odd (a*b) := by
  intro h
  exact (two_dvd_mul_iff a b).mp h |>.elim ha hb

lemma odd_pow (a : O) (ha : Odd a) (n : ℕ) : Odd (a^n) := by
  induction n with
  | zero => simpa only [pow_zero] using odd_one
  | succ n ih => simpa only [pow_succ] using odd_mul (a^n) a ih ha

lemma reciprocitySign_symm (a b : O) : reciprocitySign a b = reciprocitySign b a :=
  sexticReciprocityPhase_comm a b

lemma reciprocitySign_mul_left (a b c : O) :
    reciprocitySign (a*b) c = reciprocitySign a c * reciprocitySign b c :=
  sexticReciprocityPhase_mul_left a b c

lemma reciprocitySign_mul_right (a b c : O) :
    reciprocitySign a (b*c) = reciprocitySign a b * reciprocitySign a c :=
  sexticReciprocityPhase_mul_right a b c

lemma reciprocitySign_one_left (a : O) (ha : Odd a) : reciprocitySign 1 a = 1 := by
  rw [reciprocitySign, sexticReciprocityPhase_good 1 a odd_one ha,
    FixedRayArithmetic.quadraticPhase_comm,
    FixedRayArithmetic.quadraticPhase_one a (fun h => ha (Ideal.mem_span_singleton.mp h))]

lemma reciprocitySign_sq (a b : O) (ha : Odd a) (hb : Odd b) :
    reciprocitySign a b ^ 2 = 1 := by
  rw [reciprocitySign, sexticReciprocityPhase_good a b ha hb]
  exact FixedRayArithmetic.quadraticPhase_sq
    (fun h => ha (Ideal.mem_span_singleton.mp h))
    (fun h => hb (Ideal.mem_span_singleton.mp h))

lemma reciprocitySign_pow_left (a b : O) (hb : Odd b) (n : ℕ) :
    reciprocitySign (a^n) b = reciprocitySign a b ^ n := by
  induction n with
  | zero => simp only [pow_zero, reciprocitySign_one_left b hb]
  | succ n ih => rw [pow_succ, reciprocitySign_mul_left, ih, pow_succ]

lemma reciprocitySign_pow_right (a b : O) (ha : Odd a) (n : ℕ) :
    reciprocitySign a (b^n) = reciprocitySign a b ^ n := by
  rw [reciprocitySign_symm, reciprocitySign_pow_left b a ha n, reciprocitySign_symm b a]

lemma reciprocitySign_cube_right (a b : O) (ha : Odd a) (hb : Odd b) :
    reciprocitySign a (b^3) = reciprocitySign a b := by
  rw [reciprocitySign_pow_right a b ha 3, pow_succ, reciprocitySign_sq a b ha hb, one_mul]

end ProbePhase

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhase
open Eisenstein Eisenstein.Coordinates CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve 
local notation "O" => Eisenstein.O

def sexticPair (p q : O) : ℂ :=
  idealRowHom q (Ideal.span {p}) * idealRowHom p (Ideal.span {q})

theorem sexticPair_cube (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda ^ 2 ∣ p - 1) (hprimaryQ : lambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) :
    sexticPair p q ^ 3 = reciprocitySign p q := by
  have hr : idealRowHom q (Ideal.span {p}) =
      reciprocitySign p q * idealRowHom p (Ideal.span {q}) :=
    idealRowHom_prime_reciprocity p q hp hq hprimaryP hprimaryQ ((supported_iff_native _).mp hsP) ((supported_iff_native _).mp hsQ)
  have h6 := idealRowHom_sixth_mask p (Ideal.span {q}) ((supported_iff_native _).mp hsQ)
  rw [idealRowHom_argument_pow _ _ _ ((supported_iff_native _).mp hsQ).1, if_pos hcop.symm] at h6
  have h2 := reciprocitySign_sq p q (odd_of_supported p hsP) (odd_of_supported q hsQ)
  calc
    sexticPair p q ^ 3 = reciprocitySign p q ^ 3 * idealRowHom p (Ideal.span {q}) ^ 6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = reciprocitySign p q := by rw [h6, mul_one, pow_succ, h2, one_mul]

theorem completed_pair_phase (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda ^ 2 ∣ p - 1) (hprimaryQ : lambda ^ 2 ∣ q - 1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q})) (e f l k : ℕ) :
    sexticPair p q ^ ((e + 3 * l) * (f + 3 * k)) / sexticPair p q ^ (e * f) =
      reciprocitySign p q ^ (e * k + f * l + l * k) := by
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q (odd_of_supported p hsP) (odd_of_supported q hsQ)
  have hr : reciprocitySign p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h2; norm_num at h2
  have hz : sexticPair p q ≠ 0 := by intro h; rw [h, zero_pow (by decide)] at h3; exact hr h3.symm
  have hexp : (e + 3 * l) * (f + 3 * k) = e * f + 3 * (e * k + f * l + 3 * l * k) := by ring
  rw [hexp, pow_add, pow_mul (sexticPair p q) 3 (e * k + f * l + 3 * l * k),
    h3, mul_div_cancel_left₀ _ (pow_ne_zero _ hz)]
  have htail : e * k + f * l + 3 * l * k = (e * k + f * l + l * k) + 2 * (l * k) := by ring
  rw [htail, pow_add, pow_mul (reciprocitySign p q) 2 (l * k), h2, one_pow, mul_one]

end ProbePhase
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhase
open Eisenstein Eisenstein.Coordinates CompletedGauss CubicEisenstein
open CanonicalRowCompletion CanonicalQuadraticSieve 
local notation "O" => Eisenstein.O

lemma reciprocitySign_star (a b : O) : star (reciprocitySign a b)=reciprocitySign a b := by
  exact CenteredMomentSupportedCorrelation.star_sexticReciprocityPhase a b

theorem completed_cubic_pair_cancel (p q : O) (hp : Prime p) (hq : Prime q)
    (hprimaryP : lambda^2∣p-1) (hprimaryQ : lambda^2∣q-1)
    (hsP : Supported (Ideal.span {p})) (hsQ : Supported (Ideal.span {q}))
    (hcop : IsCoprime (Ideal.span {p} : Ideal O) (Ideal.span {q}))
    (e f l k : ℕ) :
    sexticPair p q ^ ((e+3*l)*(f+3*k)) * sexticPair p q ^ (2*e*f) *
      star (reciprocitySign (p^(e+3*l)) (q^(f+3*k))) = 1 := by
  have hpodd := odd_of_supported p hsP
  have hqodd := odd_of_supported q hsQ
  have h3 := sexticPair_cube p q hp hq hprimaryP hprimaryQ hsP hsQ hcop
  have h2 := reciprocitySign_sq p q hpodd hqodd
  rw [reciprocitySign_star, reciprocitySign_pow_left p _ (odd_pow q hqodd _) _,
    reciprocitySign_pow_right p q hpodd, ← pow_mul, ← pow_add]
  have hexp : (e+3*l)*(f+3*k)+2*e*f = 3*(e*f+e*k+f*l+3*l*k) := by ring
  rw [hexp, pow_mul, h3, ← pow_add]
  have hsum : e*f+e*k+f*l+3*l*k+(f+3*k)*(e+3*l) =
      2*(e*f+2*e*k+2*f*l+6*l*k) := by ring
  rw [hsum, pow_mul, h2, one_pow]

lemma sexticPair_mul_left (a b c : O) :
    sexticPair (a*b) c = sexticPair a c * sexticPair b c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_mul_right (a b c : O) :
    sexticPair a (b*c) = sexticPair a b * sexticPair a c := by
  simp only [sexticPair, ← Ideal.span_singleton_mul_span_singleton, map_mul,
    idealRowHom_argument_mul]
  ring

lemma sexticPair_cube_left (a b : O) : sexticPair (a^3) b=sexticPair a b^3 := by
  rw [show a^3=a*a*a by ring, sexticPair_mul_left, sexticPair_mul_left]
  ring

lemma sexticPair_cube_right (a b : O) : sexticPair a (b^3)=sexticPair a b^3 := by
  rw [show b^3=b*b*b by ring, sexticPair_mul_right, sexticPair_mul_right]
  ring

theorem sexticPair_cube_supported (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hpa : lambda^2∣a-1) (hpb : lambda^2∣b-1) (hcop : IsCoprime a b) :
    sexticPair a b^3 = reciprocitySign a b := by
  have hr : idealRowHom b (Ideal.span {a}) =
      reciprocitySign a b * idealRowHom a (Ideal.span {b}) :=
    idealRowHom_primary_reciprocity a b hpa hpb ((supported_iff_native _).mp ha) ((supported_iff_native _).mp hb)
  have hc : IsCoprime (Ideal.span {b}:Ideal O) (Ideal.span {a}) := by
    exact (Ideal.isCoprime_span_singleton_iff b a).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask a (Ideal.span {b}) ((supported_iff_native _).mp hb)
  rw [idealRowHom_argument_pow _ _ _ ((supported_iff_native _).mp hb).1, if_pos hc] at h6
  have h2 := reciprocitySign_sq a b (odd_of_supported a ha) (odd_of_supported b hb)
  calc
    _ = reciprocitySign a b^3 * idealRowHom a (Ideal.span {b})^6 := by
      unfold sexticPair
      rw [hr]
      ring
    _ = _ := by rw [h6,mul_one,pow_succ,h2,one_mul]

/-- Cubic completion cancels the sextic cross terms against the quadratic sign. -/
theorem completed_cubic_cross_cancel (c n d m : O)
    (hc : Supported (Ideal.span {c})) (hn : Supported (Ideal.span {n}))
    (hd : Supported (Ideal.span {d})) (hm : Supported (Ideal.span {m}))
    (hpc : lambda^2∣c-1) (hpn : lambda^2∣n-1)
    (hpd : lambda^2∣d-1) (hpm : lambda^2∣m-1)
    (hcd : IsCoprime c d) (hcm : IsCoprime c m)
    (hnd : IsCoprime n d) (hnm : IsCoprime n m) :
    sexticPair (c*n^3) (d*m^3) * sexticPair c d^2 *
      star (reciprocitySign (c*n^3) (d*m^3)) = 1 := by
  have hcd3 := sexticPair_cube_supported c d hc hd hpc hpd hcd
  have hcm3 := sexticPair_cube_supported c m hc hm hpc hpm hcm
  have hnd3 := sexticPair_cube_supported n d hn hd hpn hpd hnd
  have hnm3 := sexticPair_cube_supported n m hn hm hpn hpm hnm
  have hRnm := reciprocitySign_sq n m (odd_of_supported n hn) (odd_of_supported m hm)
  have he : sexticPair (c*n^3) (d*m^3)*sexticPair c d^2 =
      reciprocitySign (c*n^3) (d*m^3) := by
    calc
      _ = sexticPair c d^3 * sexticPair c m^3 * sexticPair n d^3 *
          (sexticPair n m^3)^3 := by
        rw [sexticPair_mul_left, sexticPair_mul_right, sexticPair_mul_right,
          sexticPair_cube_left, sexticPair_cube_left, sexticPair_cube_right,
          sexticPair_cube_right]
        ring
      _ = reciprocitySign c d * reciprocitySign c m * reciprocitySign n d * reciprocitySign n m := by
        rw [hcd3,hcm3,hnd3,hnm3,pow_succ,hRnm,one_mul]
      _ = _ := by
        rw [reciprocitySign_mul_left, reciprocitySign_mul_right, reciprocitySign_mul_right,
          reciprocitySign_cube_right c m (odd_of_supported c hc) (odd_of_supported m hm),
          reciprocitySign_symm (n^3) d,
          reciprocitySign_cube_right d n (odd_of_supported d hd) (odd_of_supported n hn),
          reciprocitySign_symm d n,
          reciprocitySign_cube_right (n^3) m (odd_pow n (odd_of_supported n hn) 3)
            (odd_of_supported m hm), reciprocitySign_symm (n^3) m,
          reciprocitySign_cube_right m n (odd_of_supported m hm) (odd_of_supported n hn),
          reciprocitySign_symm m n]
        ring
  rw [he,reciprocitySign_star,←pow_two]
  exact reciprocitySign_sq _ _
    (odd_mul c (n^3) (odd_of_supported c hc) (odd_pow n (odd_of_supported n hn) 3))
    (odd_mul d (m^3) (odd_of_supported d hd) (odd_pow m (odd_of_supported m hm) 3))

end ProbePhase
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein ProbePhase
local notation "O" => Eisenstein.O

def reciprocityCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  reciprocitySign A s * bareCongruenceCoefficient A s hA H

theorem reciprocityCoefficient_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : lambda^2∣A-1) (hpB : lambda^2∣B-1)
    (hps : lambda^2∣s-1) (hpr : lambda^2∣r-1)
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    reciprocityCoefficient (A*B) (s*r)
      (mul_ne_zero (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (CenteredMomentSupportedCorrelation.supported_element_ne_zero B hB)) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocityCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H *
        reciprocityCoefficient B r (CenteredMomentSupportedCorrelation.supported_element_ne_zero B hB) H := by
  have hsB := idealRowHom_ne_zero_of_coprime s B hs hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr hcop.of_mul_left_left.of_mul_right_right.symm
  have hAr : idealRowHom r (Ideal.span {A}) = reciprocitySign A r * idealRowHom A (Ideal.span {r}) :=
    idealRowHom_primary_reciprocity A r hpA hpr ((supported_iff_native _).mp hA) ((supported_iff_native _).mp hr)
  have hBs : idealRowHom s (Ideal.span {B}) = reciprocitySign B s * idealRowHom B (Ideal.span {s}) :=
    idealRowHom_primary_reciprocity B s hpB hps ((supported_iff_native _).mp hB) ((supported_iff_native _).mp hs)
  have hratio :
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocitySign A r * reciprocitySign B s := by
    rw [hAr, hBs]
    field_simp
  have hsign : reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s =
      reciprocitySign A s * reciprocitySign B r := by
    calc
      _ = reciprocitySign A s * reciprocitySign B r *
          reciprocitySign A r ^ 2 * reciprocitySign B s ^ 2 := by
        simp only [reciprocitySign_mul_left, reciprocitySign_mul_right]
        ring
      _ = _ := by
        rw [reciprocitySign_sq A r (odd_of_supported A hA) (odd_of_supported r hr),
          reciprocitySign_sq B s (odd_of_supported B hB) (odd_of_supported s hs),
          mul_one, mul_one]
  unfold reciprocityCoefficient
  rw [bareCongruenceCoefficient_product_reduced A B s r (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA)
    (CenteredMomentSupportedCorrelation.supported_element_ne_zero B hB) hs hr hcop H, hratio]
  calc
    _ = (reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s) *
        (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H *
        bareCongruenceCoefficient B r (CenteredMomentSupportedCorrelation.supported_element_ne_zero B hB) H := by ring
    _ = _ := by rw [hsign]; ring

end ProbePhysical
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

namespace ProbePhysical
open CubicSieve
local notation "O" => Eisenstein.O

/-- Periodic-row CRT gives the cubic Gauss product. -/
theorem gaussTwo_coprime_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      (CubicSieve.cubicRow I (primaryIdealGenerator J) * CubicSieve.cubicRow J (primaryIdealGenerator I)) *
      gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  have hc : IsCoprime (primaryIdealGenerator I) (primaryIdealGenerator J) := by
    rw [← Ideal.isCoprime_span_singleton_iff,
      (primaryIdealGenerator_spec I hI.2).1, (primaryIdealGenerator_spec J hJ.2).1]
    exact hcop
  have he := residueRowGauss_mul (primaryIdealGenerator I) (primaryIdealGenerator J)
    hI.2 hJ.2 hc (elementCharacter I hI.2) (elementCharacter J hJ.2)
    (cubicRow_congr I hI.2) (cubicRow_congr J hJ.2)
  have hci : (elementCharacter I hI.2 : O → ℂ) = CubicSieve.cubicRow I := by
    funext x
    rfl
  have hcj : (elementCharacter J hJ.2 : O → ℂ) = CubicSieve.cubicRow J := by
    funext x
    rfl
  have hrow : CubicSieve.cubicRow (I*J) =
      (CubicSieve.cubicRow I * CubicSieve.cubicRow J : O → ℂ) := by
    funext x
    exact cubicRow_mul I J x
  have hgauss : residueRowGauss (primaryIdealGenerator (I*J)) hIJ.2
      (CubicSieve.cubicRow (I*J)) =
      (CubicSieve.cubicRow I (primaryIdealGenerator J) * CubicSieve.cubicRow J (primaryIdealGenerator I)) *
      residueRowGauss (primaryIdealGenerator I) hI.2 (CubicSieve.cubicRow I) *
      residueRowGauss (primaryIdealGenerator J) hJ.2 (CubicSieve.cubicRow J) := by
    simpa only [primaryIdealGenerator_mul, hrow, hci, hcj] using he
  unfold gaussTwo
  rw [hgauss, primaryIdealGenerator_mul, map_mul, norm_mul, Complex.ofReal_mul]
  ring

theorem gaussTwo_coprime_product_sextic (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hcop : IsCoprime I J) :
    gaussTwo (I*J) hIJ.2 =
      ProbePhase.sexticPair (primaryIdealGenerator I) (primaryIdealGenerator J)^2 *
        gaussTwo I hI.2 * gaussTwo J hJ.2 := by
  rw [gaussTwo_coprime_product I J hI hJ hIJ hcop]
  simp only [CubicSieve.cubicRow, ← idealRowHom_square, ProbePhase.sexticPair,
    (primaryIdealGenerator_spec I hI.2).1, (primaryIdealGenerator_spec J hJ.2).1, mul_pow]


end ProbePhysical

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson

namespace ProbePhase
open QuadraticPhase.Eisenstein
local notation "O" => Eisenstein.O

lemma cubicTwo_isUnit_of_odd (a : O) (ha : Odd a) :
    IsUnit (Ideal.Quotient.mk cubicTwoIdeal a) := by
  let : Field (O ⧸ cubicTwoIdeal) := Ideal.Quotient.field _
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply ha
  simpa only [cubicTwoIdeal, Ideal.mem_span_singleton, neg_dvd] using
    Ideal.Quotient.eq_zero_iff_mem.mp hz

lemma cubicTwoSupplement_cube (a : O) (ha : Odd a) : cubicTwoSupplement a ^ 3 = 1 := by
  change complexCubicChar cubicTwoIdeal cubicTwoIdeal_good (Ideal.Quotient.mk cubicTwoIdeal a)^3 = 1
  have h := congrArg (fun χ : MulChar (O ⧸ cubicTwoIdeal) ℂ =>
    χ (Ideal.Quotient.mk cubicTwoIdeal a))
    (complexCubicChar_pow_three cubicTwoIdeal cubicTwoIdeal_good)
  simpa only [MulChar.pow_apply' _ (by decide : (3 : ℕ) ≠ 0),
    MulChar.one_apply (cubicTwo_isUnit_of_odd a ha)] using h

lemma G_one : G (1 : O) = 1 := by
  rw [G_eq, map_one, star_one, fixedDualAverage_one, one_mul]

lemma G_mul (a b : O) (ha : Odd a) (hb : Odd b) :
    G (a*b) = G a * G b * reciprocitySign a b := by
  have hga := FixedRayArithmetic.gamma_ne_zero
    (fun h => ha (Ideal.mem_span_singleton.mp h))
  have hgb := FixedRayArithmetic.gamma_ne_zero
    (fun h => hb (Ideal.mem_span_singleton.mp h))
  rw [G_eq, G_eq, G_eq, map_mul, star_mul, reciprocitySign,
    sexticReciprocityPhase_good a b ha hb, FixedRayArithmetic.quadraticPhase]
  field_simp [hga, hgb]

lemma G_norm_one_of_odd (a : O) (ha : Odd a) : ‖G a‖ = 1 := by
  have hc := Complex.norm_eq_one_of_pow_eq_one (cubicTwoSupplement_cube a ha)
    (by decide : (3 : ℕ) ≠ 0)
  have hg := Complex.norm_eq_one_of_pow_eq_one
    (FixedRayArithmetic.gamma_pow_four (fun h => ha (Ideal.mem_span_singleton.mp h)))
    (by decide : (4 : ℕ) ≠ 0)
  rw [G_eq, norm_mul, norm_star, hc, hg, mul_one]

lemma G_cube (a : O) (ha : Odd a) : G (a^3) = fixedDualAverage a := by
  rw [G_eq, map_pow, cubicTwoSupplement_cube a ha, star_one, one_mul]
  have hg := FixedRayArithmetic.gamma_mul_sq
    (fun h => ha (Ideal.mem_span_singleton.mp h))
    (fun h => ha (Ideal.mem_span_singleton.mp h))
  simpa only [show a*a^2=a^3 by ring] using hg

lemma G_conjugate_cancel (a : O) (ha : Odd a) : star (G a) * G a = 1 := by
  have hn := G_norm_one_of_odd a ha
  rw [Complex.star_def, (Complex.inv_eq_conj hn).symm]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero))

lemma G_completed_index (c n : O) (hc : Odd c) (hn : Odd n) :
    G (c*n^3) = G c * reciprocitySign c n * G (n^3) := by
  rw [G_mul c (n^3) hc (odd_pow n hn 3), reciprocitySign_cube_right c n hc hn]
  ring

lemma completed_phase_cancel (c n : O) (hc : Odd c) (hn : Odd n) :
    star (G (c*n^3)) * (G c * reciprocitySign c n * G (n^3)) = 1 := by
  rw [← G_completed_index c n hc hn]
  exact G_conjugate_cancel _ (odd_mul c (n^3) hc (odd_pow n hn 3))

theorem G_pow (a : O) (ha : Odd a) (n : ℕ) :
    G (a ^ n) = G a ^ n * reciprocitySign a a ^ (n.choose 2) := by
  induction n with
  | zero => simp [G_one]
  | succ n ih =>
    rw [pow_succ, G_mul (a ^ n) a (odd_pow a ha n) ha, ih,
      reciprocitySign_pow_left a a ha n, Nat.choose_succ_succ, Nat.choose_one_right,
      pow_add, pow_succ]
    ring

theorem reciprocitySign_cube_self (a : O) (ha : Odd a) :
    reciprocitySign (a ^ 3) (a ^ 3) = reciprocitySign a a := by
  rw [reciprocitySign_cube_right (a ^ 3) a (odd_pow a ha 3) ha,
    reciprocitySign_symm, reciprocitySign_cube_right a a ha ha]

theorem G_cube_power (a : O) (ha : Odd a) (l : ℕ) :
    G (a ^ (3 * l)) = G (a ^ 3) ^ l * reciprocitySign a a ^ (l.choose 2) := by
  rw [pow_mul, G_pow (a ^ 3) (odd_pow a ha 3), reciprocitySign_cube_self a ha]

theorem G_completed_prime_power (a : O) (ha : Odd a)
    (e l : ℕ) (he : e ≤ 1) :
    G (a ^ (e + 3 * l)) =
      G a ^ e * G (a ^ 3) ^ l * reciprocitySign a a ^ (e * l + l.choose 2) := by
  have hc : e = 0 ∨ e = 1 := by omega
  rcases hc with rfl | rfl
  · simpa only [zero_add, zero_mul, pow_zero, one_mul] using G_cube_power a ha l
  · rw [pow_add, pow_one, G_mul a (a ^ (3 * l)) ha (odd_pow a ha _),
      G_cube_power a ha l, pow_mul, reciprocitySign_pow_right a (a ^ 3) ha l,
      reciprocitySign_cube_right a a ha ha]
    simp only [pow_one, one_mul, pow_add]
    ring


end ProbePhase

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein ProbePhase
local notation "O" => Eisenstein.O

lemma supported_completed (c n : O) (hc : Supported (Ideal.span {c}))
    (hn : Supported (Ideal.span {n})) : Supported (Ideal.span {c*n^3}) := by
  rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow]
  apply (supported_mul_iff _ _).mpr
  refine ⟨hc,?_⟩
  have hn2 := (supported_mul_iff _ _).mpr ⟨hn,hn⟩
  have hn3 := (supported_mul_iff _ _).mpr ⟨hn2,hn⟩
  simpa only [pow_succ, pow_zero, one_mul] using hn3

lemma primary_completed (c n : O) (hc : lambda^2∣c-1)
    (hn : lambda^2∣n-1) : lambda^2∣c*n^3-1 := by
  have h := dvd_add (dvd_mul_of_dvd_left hc (n^3))
    (dvd_mul_of_dvd_left hn (n^2+n+1))
  convert h using 1 <;> first | rfl | ring

def correctedFiniteCoefficient (I : Ideal O) (hI : primaryIdealGenerator I≠0)
    (A s : O) (hA : A≠0) (H : O) : ℂ :=
  gaussTwo I hI * star (G A) * reciprocityCoefficient A s hA H

/-- The cubic Gauss factor and fixed phase cancel the CRT cross terms. -/
theorem correctedFiniteCoefficient_product (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryIdealGenerator I})) (hd : Supported (Ideal.span {primaryIdealGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : lambda^2∣primaryIdealGenerator I-1) (hpd : lambda^2∣primaryIdealGenerator J-1)
    (hpn : lambda^2∣n-1) (hpm : lambda^2∣m-1)
    (hps : lambda^2∣s-1) (hpr : lambda^2∣r-1)
    (hcop : IsCoprime ((primaryIdealGenerator I*n^3)*s) ((primaryIdealGenerator J*m^3)*r)) (H : O) :
    let A := primaryIdealGenerator I*n^3
    let B := primaryIdealGenerator J*m^3
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _ hc hn)
    let hB := CenteredMomentSupportedCorrelation.supported_element_ne_zero B (supported_completed _ _ hd hm)
    correctedFiniteCoefficient (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      correctedFiniteCoefficient I hI.2 A s hA H * correctedFiniteCoefficient J hJ.2 B r hB H := by
  dsimp only
  let c := primaryIdealGenerator I
  let d := primaryIdealGenerator J
  let A := c*n^3
  let B := d*m^3
  have hAs := supported_completed c n hc hn
  have hBs := supported_completed d m hd hm
  have hAB : IsCoprime A B := hcop.of_mul_left_left.of_mul_right_left
  have hnA : n∣A := by refine ⟨c*n^2,?_⟩; dsimp only [A]; ring
  have hmB : m∣B := by refine ⟨d*m^2,?_⟩; dsimp only [B]; ring
  have hcA : c∣A := dvd_mul_right c (n^3)
  have hdB : d∣B := dvd_mul_right d (m^3)
  have hcd : IsCoprime c d := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hdB
  have hcm : IsCoprime c m := (hAB.of_isCoprime_of_dvd_left hcA).of_isCoprime_of_dvd_right hmB
  have hnd : IsCoprime n d := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hdB
  have hnm : IsCoprime n m := (hAB.of_isCoprime_of_dvd_left hnA).of_isCoprime_of_dvd_right hmB
  have hphase := completed_cubic_cross_cancel c n d m hc hn hd hm hpc hpn hpd hpm hcd hcm hnd hnm
  change sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)=1 at hphase
  change gaussTwo (I*J) hIJ.2 * star (G (A*B)) *
      reciprocityCoefficient (A*B) (s*r) _ H =
    (gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
    (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)
  rw [gaussTwo_coprime_product_sextic I J hI hJ hIJ hIJcop,
    G_mul A B (odd_of_supported A hAs) (odd_of_supported B hBs),
    reciprocityCoefficient_product A B s r hAs hBs hs hr
      (primary_completed c n hpc hpn) (primary_completed d m hpd hpm) hps hpr hcop H]
  simp only [star_mul]
  change (sexticPair c d^2 * gaussTwo I hI.2 * gaussTwo J hJ.2) *
    (star (reciprocitySign A B)*(star (G B)*star (G A))) *
    (sexticPair A B * reciprocityCoefficient A s _ H * reciprocityCoefficient B r _ H) = _
  calc
    _ = (sexticPair A B * sexticPair c d^2 * star (reciprocitySign A B)) *
      ((gaussTwo I hI.2 * star (G A) * reciprocityCoefficient A s _ H) *
       (gaussTwo J hJ.2 * star (G B) * reciprocityCoefficient B r _ H)) := by ring
    _ = _ := by rw [hphase,one_mul]

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbePhase ProbeRow 
local notation "O" => Eisenstein.O

def sourceHighCoefficient (C : CalibrationData) (η : HeckeFamily.Character)
    (I : Ideal O) (hI : primaryIdealGenerator I≠0) (A s : O) (hA : A≠0) (u a : O) : ℂ :=
  actualCongruenceCoefficient C A s hA (u*a^6) * idealRowHom C.generator (Ideal.span {s}) /
    ((Real.sqrt (elementNorm C.generator):ℂ)*C.tau*C.residueMonoid s*star (C.residueMonoid u)) *
    gaussTwo I hI * star (CompletedGauss.angularFactor A * G A) *
    targetMonoid η A * (C.Xi A)⁻¹ * reciprocitySign A s

def bareSourceCoefficient (η : HeckeFamily.Character) (I : Ideal O)
    (hI : primaryIdealGenerator I≠0) (A s : O) (hA : A≠0) (H : O) : ℂ :=
  targetMonoid η A * star (CompletedGauss.angularFactor A) *
    correctedFiniteCoefficient I hI A s hA H

theorem sourceHighCoefficient_eq_bare (S : Finset (Ideal O)) (hS : ∀ P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (I : Ideal O) (hI : primaryIdealGenerator I≠0)
    (A s : O) (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (hcop : IsCoprime (calibrationForSet S hS).generator (A*s)) (u a : O)
    (hH : IsCoprime (calibrationForSet S hS).generator (u*a^6)) :
    sourceHighCoefficient (calibrationForSet S hS) η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) u a =
      bareSourceCoefficient η I hI A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (u*a^6) := by
  let C := calibrationForSet S hS
  have ha : IsCoprime C.generator a :=
    hH.of_isCoprime_of_dvd_right (by refine ⟨u*a^5,?_⟩; ring)
  have hval : C.residueMonoid (u*a^6)=C.residueMonoid u := by
    rw [map_mul,map_pow,calibrationForSet_residue_sixth S hS a ha,mul_one]
  have he := calibration_coefficient_cancel S hS A s hA hs hcop (u*a^6) hH
  dsimp only at he
  dsimp only [C] at hval
  rw [hval] at he
  unfold sourceHighCoefficient bareSourceCoefficient correctedFiniteCoefficient reciprocityCoefficient
  simp only [star_mul]
  calc
    _ = (actualCongruenceCoefficient (calibrationForSet S hS) A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) (u*a^6) *
      idealRowHom (calibrationForSet S hS).generator (Ideal.span {s}) /
      ((Real.sqrt (elementNorm (calibrationForSet S hS).generator):ℂ)*(calibrationForSet S hS).tau*
       (calibrationForSet S hS).residueMonoid s*star ((calibrationForSet S hS).residueMonoid u)) *
      ((calibrationForSet S hS).Xi A)⁻¹) *
      (gaussTwo I hI * star (G A) * star (CompletedGauss.angularFactor A) *
        targetMonoid η A * reciprocitySign A s) := by ring
    _ = _ := by rw [he]; ring

theorem bareSourceCoefficient_product (η : HeckeFamily.Character) (I J : Ideal O)
    (hI : CubicSieve.Admissible I) (hJ : CubicSieve.Admissible J)
    (hIJ : CubicSieve.Admissible (I*J)) (hIJcop : IsCoprime I J)
    (n m s r : O)
    (hc : Supported (Ideal.span {primaryIdealGenerator I})) (hd : Supported (Ideal.span {primaryIdealGenerator J}))
    (hn : Supported (Ideal.span {n})) (hm : Supported (Ideal.span {m}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpc : lambda^2∣primaryIdealGenerator I-1) (hpd : lambda^2∣primaryIdealGenerator J-1)
    (hpn : lambda^2∣n-1) (hpm : lambda^2∣m-1)
    (hps : lambda^2∣s-1) (hpr : lambda^2∣r-1)
    (hcop : IsCoprime ((primaryIdealGenerator I*n^3)*s) ((primaryIdealGenerator J*m^3)*r)) (H : O) :
    let A := primaryIdealGenerator I*n^3
    let B := primaryIdealGenerator J*m^3
    let hA := CenteredMomentSupportedCorrelation.supported_element_ne_zero A (supported_completed _ _ hc hn)
    let hB := CenteredMomentSupportedCorrelation.supported_element_ne_zero B (supported_completed _ _ hd hm)
    bareSourceCoefficient η (I*J) hIJ.2 (A*B) (s*r) (mul_ne_zero hA hB) H =
      bareSourceCoefficient η I hI.2 A s hA H * bareSourceCoefficient η J hJ.2 B r hB H := by
  have he := correctedFiniteCoefficient_product I J hI hJ hIJ hIJcop n m s r
    hc hd hn hm hs hr hpc hpd hpn hpm hps hpr hcop H
  dsimp only at he ⊢
  unfold bareSourceCoefficient
  rw [he,map_mul,angularFactor_mul,star_mul]
  ring

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein ProbePhase ProbeRow
local notation "O" => Eisenstein.O

theorem bareCongruenceCoefficient_norm_le (A s : O) (hA : A≠0) (hs : s≠0) (H : O) :
    ‖bareCongruenceCoefficient A s hA H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  apply congruenceCoefficient_norm_le A s hA hs
  · intro m
    exact idealRowHom_norm _ _
  · intro m
    exact idealRowHom_norm _ _

theorem bareSourceCoefficient_norm_le (η : HeckeFamily.Character)
    (I : Ideal O) (hI : CubicSieve.Admissible I) (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s})) (H : O) :
    ‖bareSourceCoefficient η I hI.2 A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H‖ ≤
      (Ideal.absNorm (Ideal.span {s}):ℝ)*(Ideal.absNorm (Ideal.span {A}):ℝ) := by
  have hR : ‖reciprocitySign A s‖≤1 := sexticReciprocityPhase_norm A s
  have ht := targetMonoid_norm_le_one η A
  have hfac : ‖targetMonoid η A‖*‖reciprocitySign A s‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) ht).trans hR
  calc
    _ = (‖targetMonoid η A‖*‖reciprocitySign A s‖)*
        ‖bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H‖ := by
      simp only [bareSourceCoefficient, correctedFiniteCoefficient, reciprocityCoefficient,
        norm_mul,norm_star,CubicSieve.gaussTwo_norm_one I hI,
        CompletedGauss.norm_angularFactor A (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA),
        G_norm_one_of_odd A (odd_of_supported A hA),one_mul,mul_one]
      ring
    _ ≤ ‖bareCongruenceCoefficient A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA) H‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hfac
    _ ≤ _ := bareCongruenceCoefficient_norm_le A s (CenteredMomentSupportedCorrelation.supported_element_ne_zero A hA)
      (CenteredMomentSupportedCorrelation.supported_element_ne_zero s hs) H

end ProbePhysical
end

end

noncomputable section
open CubicSieve Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical
namespace ProbePhysical
open Eisenstein CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open CubicEisenstein
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def bareIdealHighCoefficient (η : HeckeFamily.Character) (u : O) (I J K L : Id) : ℂ :=
  if h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L then
    bareSourceCoefficient η I (supported_primaryIdealGenerator_ne_zero I h.2.1)
      (primaryIdealGenerator I * primaryIdealGenerator J^3) (primaryIdealGenerator K)
      (mul_ne_zero (supported_primaryIdealGenerator_ne_zero I h.2.1)
        (pow_ne_zero _ (supported_primaryIdealGenerator_ne_zero J h.2.2.1)))
      (u*primaryIdealGenerator L^6)
  else 0

theorem bareIdealHighCoefficient_norm_le (η : HeckeFamily.Character) (u : O) (I J K L : Id) :
    ‖bareIdealHighCoefficient η u I J K L‖ ≤ (K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3 := by
  unfold bareIdealHighCoefficient
  split_ifs with h
  · have hi := (supported_span_primaryIdealGenerator_iff I).mpr h.2.1
    have hj := (supported_span_primaryIdealGenerator_iff J).mpr h.2.2.1
    have hk := (supported_span_primaryIdealGenerator_iff K).mpr h.2.2.2.1
    have hb := bareSourceCoefficient_norm_le η I ⟨h.1,supported_primaryIdealGenerator_ne_zero I h.2.1⟩
      (primaryIdealGenerator I*primaryIdealGenerator J^3) (primaryIdealGenerator K)
      (supported_completed _ _ hi hj) hk (u*primaryIdealGenerator L^6)
    rw [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
      (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I h.2.1)).1,
      (primaryIdealGenerator_spec J (supported_primaryIdealGenerator_ne_zero J h.2.2.1)).1,
      (primaryIdealGenerator_spec K (supported_primaryIdealGenerator_ne_zero K h.2.2.2.1)).1,
      map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] at hb
    convert hb using 1 <;> first | rfl | ring
  · simp only [norm_zero]
    positivity

def bareIdealHighSummand (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) : ℂ :=
  bareIdealHighCoefficient η u I J K L * fullIdealWeight (x+1/2) I *
    fullIdealWeight (1+3*x) J * fullIdealWeight w K * fullIdealWeight (6*z) L

lemma fullIdealWeight_nat_scale (s : ℂ) (I : Id) (hI : I≠0) (k : ℕ) :
    (I.absNorm:ℝ)^k * ‖fullIdealWeight s I‖ = ‖fullIdealWeight (s-k) I‖ := by
  have hN : 0<(I.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  simp only [fullIdealWeight,if_neg hI]
  simp only [← Complex.ofReal_natCast]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [Complex.neg_re,Complex.sub_re,Complex.ofReal_re]
  rw [← Real.rpow_natCast,← Real.rpow_add hN]
  congr 1
  ring

theorem bareIdealHighSummand_norm_le (η : HeckeFamily.Character) (u : O) (x w z : ℂ) (I J K L : Id) :
    ‖bareIdealHighSummand η u x w z I J K L‖ ≤
      ‖fullIdealWeight (x-1/2) I‖ * ‖fullIdealWeight (3*x-2) J‖ *
      ‖fullIdealWeight (w-1) K‖ * ‖fullIdealWeight (6*z) L‖ := by
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported L
  · have hb := bareIdealHighCoefficient_norm_le η u I J K L
    calc
      _ ≤ ((K.absNorm:ℝ)*(I.absNorm:ℝ)*(J.absNorm:ℝ)^3) *
          ‖fullIdealWeight (x+1/2) I‖ * ‖fullIdealWeight (1+3*x) J‖ *
          ‖fullIdealWeight w K‖ * ‖fullIdealWeight (6*z) L‖ := by
        simp only [bareIdealHighSummand,norm_mul]
        gcongr
      _ = ((I.absNorm:ℝ)^1*‖fullIdealWeight (x+1/2) I‖) *
          ((J.absNorm:ℝ)^3*‖fullIdealWeight (1+3*x) J‖) *
          ((K.absNorm:ℝ)^1*‖fullIdealWeight w K‖) * ‖fullIdealWeight (6*z) L‖ := by ring
      _ = _ := by
        rw [fullIdealWeight_nat_scale _ I h.2.1.1 1,
          fullIdealWeight_nat_scale _ J h.2.2.1.1 3,
          fullIdealWeight_nat_scale _ K h.2.2.2.1.1 1]
        norm_num only [Nat.cast_one, Nat.cast_ofNat]
        rw [show x+(1/2:ℂ)-1=x-1/2 by ring,show (1:ℂ)+3*x-3=3*x-2 by ring]
  · simp only [bareIdealHighSummand,bareIdealHighCoefficient,dif_neg h,zero_mul,norm_zero]
    positivity

/-- Absolute convergence follows from four independent ideal-norm series. -/
theorem bareIdealHighSummand_summable (η : HeckeFamily.Character) (u : O) (x w z : ℂ)
    (hx : 3/2< x.re) (hw : 2< w.re) (hz : 1/6< z.re) :
    Summable (fun p : (Id×Id)×(Id×Id) =>
      bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2) := by
  have h1 := fullIdealWeight_summable_norm (x-1/2) (by
    simp only [Complex.sub_re,Complex.div_re,Complex.one_re,Complex.one_im,
      show (2:ℂ).re=2 by rfl,show (2:ℂ).im=0 by rfl]
    norm_num
    linarith)
  have h2 := fullIdealWeight_summable_norm (3*x-2) (by
    norm_num [Complex.sub_re,Complex.mul_re]
    linarith)
  have h3 := fullIdealWeight_summable_norm (w-1) (by
    simp only [Complex.sub_re,Complex.one_re]
    linarith)
  have h4 := fullIdealWeight_summable_norm (6*z) (by
    norm_num [Complex.mul_re]
    linarith)
  have h12 := h1.mul_of_nonneg h2 (fun _=> norm_nonneg _) (fun _=> norm_nonneg _)
  have h34 := h3.mul_of_nonneg h4 (fun _=> norm_nonneg _) (fun _=> norm_nonneg _)
  have hall := h12.mul_of_nonneg h34
    (fun _=> mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (fun _=> mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ hall
  intro p
  simpa only [mul_assoc] using bareIdealHighSummand_norm_le η u x w z p.1.1 p.1.2 p.2.1 p.2.2

def bareIdealHighSeries (η : HeckeFamily.Character) (u : O) (x w z : ℂ) : ℂ :=
  ∑' p : (Id×Id)×(Id×Id), bareIdealHighSummand η u x w z p.1.1 p.1.2 p.2.1 p.2.2

end ProbePhysical
end

end

noncomputable section
open CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


namespace ProbeGauss
open scoped BigOperators Classical
noncomputable section

theorem gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

/-- A nonprincipal Gauss sum has unit norm after division by the square root of the field size. -/
theorem normalizedGauss_norm {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖normalizedGauss χ ψ‖ = 1 := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq] at h
  have hn : (‖gaussSum χ ψ‖ : ℂ)^2 = (Fintype.card F : ℂ) := by
    rw [← Complex.conj_mul', mul_comm]
    exact h
  have hr : ‖gaussSum χ ψ‖^2 = (Fintype.card F : ℝ) := by exact_mod_cast hn
  have hnorm : ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
    rw [← hr, Real.sqrt_sq (norm_nonneg _)]
  have hpos : 0 < Real.sqrt (Fintype.card F : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  unfold normalizedGauss
  rw [norm_div, hnorm, Complex.norm_real, Real.norm_of_nonneg hpos.le, div_self hpos.ne']

theorem normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq

theorem finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring

end
end ProbeGauss

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
