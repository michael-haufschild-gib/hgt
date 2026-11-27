import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsPrincipalComparison

/-!
# Principal-row comparison at the `(17/48, 2299/4800, 801/4800)` sub-Farkas geometry

Specializes the `Re s > 43/50` contour-shift and residue bounds of
`SubSevenEighthsPrincipalComparison` to the edge geometry
`X = Z^{17/48}`, `Y = Z^{2299/4800}`, `∑ j, ell j = 801/4800`, where the normalized principal
signal shift is `-19799/28800 = 17/144 + 801/28800 - 5/6`.
-/

noncomputable section
open MeasureTheory Set Filter Asymptotics Complex
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

open Eisenstein CubicJacobi CubicKubota CubicRamified CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve SchwartzPlanePoisson
open HeckeFamily

section SubFarkasPrincipalContours

namespace ProbePrincipalRemainderBounds
open ProbePhysical ProbeFiniteProductBounds PrincipalMellinResidues
open PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

lemma subFarkas_source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 801 / 4800) (Z a ξ υ : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z a ξ υ *
      (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) =
    Z ^ (a - 19799 / 28800 + (3901 / 4800) * (ξ - 1 / 6) + (2299 / 4800) * (υ - 1)) := by
  have hp : (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) = Z ^ ((801 / 4800) * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hell]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma subFarkas_source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 801 / 4800) (Z a e : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (1 / 6 + e)) =
    Z ^ (a - 19799 / 28800 + (3901 / 4800) * e - 2299 / 96000) := by
  rw [subFarkas_source_scale_identity J ell hell Z a (1 / 6 + e) (19 / 20) hZ]
  congr 1; ring

lemma subFarkas_source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 801 / 4800) (Z a : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (33 / 200 : ℝ)) =
    Z ^ (a - 19799 / 28800 - 3901 / 2880000) := by
  rw [subFarkas_source_scale_identity J ell hell Z a (33 / 200) 1 hZ]
  congr 1; ring

lemma subFarkas_source_w_strict_exponent (β e : ℝ) (he : e ≤ 1 / 2000) :
    (β + e) - 19799 / 28800 + (3901 / 4800) * e - 2299 / 96000 ≤ β - 19799 / 28800 - 1 / 1200 := by
  linarith

lemma subFarkas_source_z_strict_exponent (β e : ℝ) (he : e ≤ 1 / 2000) :
    (β + e) - 19799 / 28800 - 3901 / 2880000 ≤ β - 19799 / 28800 - 1 / 1200 := by
  linarith

theorem subFarkas_source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000)
    (ha : HeckeZeroSupremum.beta + e ∈ Icc (43 / 50 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : ι → ℝ), (∑ j ∈ J, ell j = 801 / 4800) → ∀ (W : ι → ℝ → ℝ),
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ Z : ℝ, 1 ≤ Z →
    (∀ j ∈ J, 480 ≤ c * Z ^ (ell j)) → (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * Z ^ (ell j)) →
    let K0 := fun s => sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x => (W j x : ℂ)) (fun j => Z ^ (ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta + e) (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral (19 / 20) (fun w => K0 s w z * LFunction π (6 * z) * LFunction π w)))‖ ≤
      C / e * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta + e)
      (fun s => verticalIntegral (33 / 200) (fun z => K0 s 1 z * LFunction π (6 * z)))‖ ≤
      C * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200)) := by
  obtain ⟨C, hC, hbound⟩ := sub_ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta + e) e ha (by linarith) he (by linarith)
  refine ⟨C, hC, ?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hZ0 : 0 < Z := by linarith
  have hh := hbound W hW hsupp (fun j => Z ^ (ell j)) (fun _ _ => Real.rpow_pos_of_pos hZ0 _)
    hthreshold hmod T hT (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  dsimp only at hh
  rw [subFarkas_source_w_scale_identity J ell hell Z (HeckeZeroSupremum.beta + e) e hZ0,
    subFarkas_source_z_scale_identity J ell hell Z (HeckeZeroSupremum.beta + e) hZ0] at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (subFarkas_source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (subFarkas_source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end ProbePrincipalRemainderBounds

namespace ProbePrincipalPhysical

open ProbePhysical ProbeFiniteProductBounds PrincipalMellinResidues
open PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

theorem subFarkas_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K → Finset PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
    (hdis : ∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val))
    (b : Fin K → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑ P : (∀ i, T i), (∏ i, b i (P i).val) *
      principalRowIntegral η S (fun i => primaryIdealGenerator (P i).val.val) W0 W1 X Y Z) =
      verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
        (fun w => F s w z * LFunction π (6 * z) * LFunction π w))) +
      R * verticalIntegral a (fun s => verticalIntegral (33 / 200) (fun z => F s 1 z * LFunction π (6 * z))) +
      R ^ 2 / 6 * verticalIntegral a (fun s => F s 1 (1 / 6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ProbePrincipalTransport.sub_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp => hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

/-- Physical principal-pool contour remainder along `(Z^(17/48), Z^(2299/4800), Z)` with
`∑ j, ell j = 801/4800` and `43/50 < β + e ≤ 2`. -/
theorem subFarkas_physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000)
    (ha : 43 / 50 < HeckeZeroSupremum.beta + e) (ha2 : HeckeZeroSupremum.beta + e ≤ 2) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Fin K → ℝ, (∑ j, ell j) = 801 / 4800 → ∀ W : Fin K → ℝ → ℝ,
    (∀ j x, 0 ≤ W j x ∧ W j x ≤ B) → (∀ j, Function.support (W j) ⊆ Set.Icc c d) →
    ∀ T : Fin K → Finset PrimeIdeal, (∀ j p, p ∈ T j → p.val ∉ S) →
    (∀ P : (∀ j, T j), Function.Injective (fun j => (P j).val)) →
    ∀ Z : ℝ, 1 ≤ Z → (∀ j, 480 ≤ c * Z ^ (ell j)) →
    (∀ j, (Ideal.absNorm η.modulus : ℝ) < c * Z ^ (ell j)) →
    ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val : ℝ) / Z ^ (ell j)) : ℂ)) *
        principalRowIntegral η S (fun j => primaryIdealGenerator (P j).val.val)
          W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z) -
      sourceResidueIntegral W0 W1 (∏ p ∈ S, p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta + e) (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x => (W j x : ℂ)) (fun j => Z ^ (ell j)))‖ ≤
      C / e * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := ProbePrincipalRemainderBounds.subFarkas_source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le, ha2⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0 < Z := by linarith
  have hb := hbound ell hell W (fun j _ => hW j) (fun j _ => hsupp j) T (fun j _ p hp => hT j p hp)
    Z hZ (fun j _ => hthreshold j) (fun j _ => hmod j)
  dsimp only at hb
  have heq := subFarkas_principal_physical_pool_ordered η S hS T hT hdis
    (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / Z ^ (ell j)) : ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z (HeckeZeroSupremum.beta + e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ → ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1) ^ 2 / 6 *
        verticalIntegral (HeckeZeroSupremum.beta + e) F =
      verticalIntegral (HeckeZeroSupremum.beta + e)
        (fun s => fixedPrincipalResidue (∏ p ∈ S, p) ^ 2 / 6 * F s) := by
    rw [verticalIntegral, verticalIntegral, integral_const_mul]
    dsimp only [fixedPrincipalResidue, fixedPrincipal, fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres, add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2 * C) / e * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200)
  apply hn.trans
  have hCe : C ≤ C / e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200) := Real.rpow_nonneg hZ0.le _
  have htwo : (2 * C) / e = 2 * (C / e) := by ring
  rw [htwo]
  nlinarith

end ProbePrincipalPhysical

end SubFarkasPrincipalContours

section SubFarkasSignalComparison

namespace PrincipalSignalComparison
open ProbePhysical PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open PrincipalMellinResidues

def subFarkasSlotResidue {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ) ^ (((a : ℂ) + t * I) - 19799 / 28800) * Complex.exp ((((a : ℂ) + t * I) - 5 / 6) ^ 2) *
      H ((a : ℂ) + t * I) / LFunction χ ((a : ℂ) + t * I) *
        slotRatio S T w Q A η ((a : ℂ) + t * I)

theorem subFarkasSlotResidue_eq_reciprocal {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    subFarkasSlotResidue χ H a Z S T w Q A η = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-19799 / 28800) Z ((a : ℂ) + t * I) *
        slotRatio S T w Q A η ((a : ℂ) + t * I) := by
  unfold subFarkasSlotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def subFarkasKernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-19799 / 28800) Z ((a : ℂ) + t * I)

def subFarkasKernelEnvelope (a C Z : ℝ) : ℝ :=
  Z ^ (a - 19799 / 28800) * Real.exp ((a - 5 / 6) ^ 2) * ((3 / 2) * C)

theorem subFarkasKernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    {a Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (subFarkasKernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.sub_quotient_holomorphic χ H hH ha hβ) (-19799 / 28800) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem subFarkasKernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a C Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ 2))
    (t : ℝ) : ‖subFarkasKernel χ H a Z t‖ ≤ subFarkasKernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := HeckeSignalShift.sub_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ) + t * I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold subFarkasKernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z ^ (a + (-19799 / 28800)) * Real.exp ((a - 5 / 6) ^ 2)) *
        (((3 / 2) * C) * (1 + |t| ^ 2)) * Real.exp (-(t ^ 2)) := by gcongr
    _ = _ := by unfold subFarkasKernelEnvelope polynomialGaussian; ring_nf

theorem subFarkasKernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a C Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ 2)) :
    Integrable (subFarkasKernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (subFarkasKernelEnvelope a C Z)).mono'
    (subFarkasKernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (subFarkasKernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem subFarkas_exists_slotResidue_bound {κ ι : Type*} (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SubSlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => subFarkasKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I)) ∧
        ‖subFarkasSlotResidue χ H a Z S T w Q A η - signal χ H (-19799 / 28800) Z‖ ≤
          D * Z ^ (a - 19799 / 28800) * P ^ (-(43 / 50 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    have hZ0 : 0 < Z := by linarith
    have hg := subFarkasKernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
    have hc := sub_slotRatio_continuous_line S T w Q A η h ha.le
    have hbound (t : ℝ) := sub_slotRatio_bound S T w Q A η h
      (s := (a : ℂ) + t * I) (by simpa using ha.le)
    have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
    refine ⟨hint, ?_⟩
    have herror (t : ℝ) := sub_slotRatio_error S T w Q A η h
      (s := (a : ℂ) + t * I) (by simpa using ha.le)
    have heq : subFarkasSlotResidue χ H a Z S T w Q A η - signal χ H (-19799 / 28800) Z =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          subFarkasKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ) + t * I) - 1) := by
      rw [subFarkasSlotResidue_eq_reciprocal,
        HeckeSignalShift.sub_contour_shift_left χ H hH hb (-19799 / 28800) a ha ha2 hβ hZ,
        ← mul_sub]
      change (1 / (2 * Real.pi) : ℂ) *
        ((∫ t : ℝ, subFarkasKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I)) -
          ∫ t : ℝ, subFarkasKernel χ H a Z t) = _
      rw [← integral_sub hint hg]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      change subFarkasKernel χ H a Z t * _ - subFarkasKernel χ H a Z t = _
      ring_nf
    rw [heq, norm_mul]
    have hbnd (t : ℝ) :
        ‖subFarkasKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ) + t * I) - 1)‖ ≤
          (subFarkasKernelEnvelope a C Z * (slotErrorConstant S * P ^ (-(43 / 50 : ℝ)))) *
            polynomialGaussian 2 t := by
      rw [norm_mul]
      calc
        _ ≤ (subFarkasKernelEnvelope a C Z * polynomialGaussian 2 t) *
            (slotErrorConstant S * P ^ (-(43 / 50 : ℝ))) :=
          mul_le_mul (subFarkasKernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
            (norm_nonneg _) (mul_nonneg (by unfold subFarkasKernelEnvelope; positivity)
              (polynomialGaussian_nonneg 2 t))
        _ = _ := by ring_nf
    have hn := norm_integral_le_of_norm_le
      ((polynomialGaussian_integrable 2).const_mul
        (subFarkasKernelEnvelope a C Z * (slotErrorConstant S * P ^ (-(43 / 50 : ℝ)))))
      (ae_of_all _ hbnd)
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1 / (2 * Real.pi) : ℂ))
    rw [integral_const_mul] at hm
    convert hm using 1 <;> try rfl
    unfold subFarkasKernelEnvelope HeckeSignalShift.infinityConstant
    ring_nf

theorem subFarkas_raw_slot_integrable {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => subFarkasKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ) ^ (((a : ℂ) + t * I) - 19799 / 28800) * Complex.exp ((((a : ℂ) + t * I) - 5 / 6) ^ 2) *
        H ((a : ℂ) + t * I) / LFunction χ ((a : ℂ) + t * I) *
          slotRatio S T w Q A η ((a : ℂ) + t * I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold subFarkasKernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

theorem subFarkas_source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 3 : ℂ) * (Z : ℂ) ^ (s - 5 / 6) =
      (Z : ℂ) ^ (((-(801 / 4800 : ℝ) / 6 : ℝ) : ℂ)) * (Z : ℂ) ^ (s - 19799 / 28800) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (17 / 48) (1 / 3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

theorem subFarkas_normalized_source_double_residue {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1 / 6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z χ s H B 1 (1 / 6)) /
        (sourceResidueConstant W0 W1 M *
          (Probe.principalScalar S Z (801 / 4800) (slotMass T w) : ℂ)) =
      (Z : ℂ) ^ (s - 19799 / 28800) * Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) /
        LFunction χ s * slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := subFarkas_source_power_identity hZ s
  have hz : (Z : ℂ) ^ (((-(801 / 4800 : ℝ) / 6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ) ^ (((-(801 / 4800 : ℝ) / 6 : ℝ) : ℂ)) *
          ((Z : ℂ) ^ (((-(801 / 4800 : ℝ) / 6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ) ^ (s - 19799 / 28800) * Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem subFarkas_sourceResidueIntegral_normalized {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A η ((a : ℂ) + t * I)) :
    sourceResidueConstant W0 W1 M *
      (Probe.principalScalar S Z (801 / 4800) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z ^ (17 / 48 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M *
        (Probe.principalScalar S Z (801 / 4800) (slotMass T w) : ℂ)) =
        subFarkasSlotResidue χ (fun s => H s 1 (1 / 6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral subFarkasSlotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [show (267 / 1600 : ℝ) = 801 / 4800 by norm_num]
  exact subFarkas_normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem subFarkas_source_double_residue_integrable {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A η ((a : ℂ) + t * I))
    (hi : Integrable (fun t : ℝ => subFarkasKernel χ (fun s => H s 1 (1 / 6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ) + t * I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z χ ((a : ℂ) + t * I)
        (H ((a : ℂ) + t * I)) (B ((a : ℂ) + t * I)) 1 (1 / 6)) := by
  have hiraw := subFarkas_raw_slot_integrable χ (fun s => H s 1 (1 / 6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 801 / 4800))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M *
      (Probe.principalScalar S Z (801 / 4800) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (subFarkas_normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

theorem subFarkas_exists_normalized_actual_source_bound {κ : Type*} (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ) + t * I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (801 / 4800) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ) + t * I) (globalClosedCorrection η E ((a : ℂ) + t * I)) (B ((a : ℂ) + t * I)) 1 (1 / 6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z ^ (17 / 48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-19799 / 28800) Z‖ ≤
        D * Z ^ (a - 19799 / 28800) * P ^ (-(43 / 50 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := subFarkas_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sub_sourceCorrection_differentiable η E hE) (sub_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := subFarkas_sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : SubSlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact subFarkas_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end PrincipalSignalComparison

namespace ProbePrincipalResidueActual

open PrincipalMellinResidues PrincipalSignalComparison ProbeFiniteProductBounds
open ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation

theorem subFarkas_normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal Eisenstein.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0 < a0 → 0 < a1 → Function.support W0 ⊆ Set.Icc a0 b0 →
      Function.support W1 ⊆ Set.Icc a1 b1 →
      (∀ y, (W0 y).im = 0) → (∀ y, (W1 y).im = 0) →
      (∀ y, 0 ≤ (W0 y).re) → (∀ y, 0 ≤ (W1 y).re) → W0 ≠ 0 → W1 ≠ 0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480 ≤ P → 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ W j ((Ideal.absNorm p.val : ℝ) / scale j)) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T (residueWeights W scale) j) → 1 ≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (801 / 4800) (slotMass T (residueWeights W scale)) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ) + t * I) (globalClosedCorrection η E ((a : ℂ) + t * I))
          (B ((a : ℂ) + t * I)) 1 (1 / 6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z ^ (17 / 48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-19799 / 28800) Z‖ ≤
        D * Z ^ (a - 19799 / 28800) * P ^ (-(43 / 50 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hbound⟩ := subFarkas_exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏ p ∈ E, p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end ProbePrincipalResidueActual
namespace ProbePrincipalNormalized

open ProbePhysical ProbeFiniteProductBounds PrincipalMellinResidues
open PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal Eisenstein.O

/-- Normalized principal-row comparison along the sub-`7/8` ray `(Z^(17/48), Z^(2299/4800), Z)`
with `∑ j, ell j = 801/4800` and `43/50 < β + e ≤ 2`: the normalized principal pool converges to
`HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-19799/28800) Z` with
strict polynomial saving below `Z^(β - 19799/28800)`. -/
theorem subFarkas_actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (Eisenstein.O ⧸ M)]
    (H : Subgroup (Eisenstein.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hmin : 0 < ellMin)
    (ell : Fin K → ℝ) (hell : ∀ j, ellMin ≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑ j, ell j) = 801 / 4800)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo c d)
    (hWbounds : ∀ j y, 0 ≤ W j y ∧ W j y ≤ B) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re) (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (e nu : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000) (hnu : 0 < nu)
    (ha : 43 / 50 < HeckeZeroSupremum.beta + e) (ha2 : HeckeZeroSupremum.beta + e ≤ 2) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ S, p) *
        (Probe.principalScalar Finset.univ Z (801 / 4800)
          (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
      normer ≠ 0 ∧
      ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val : ℝ) / Z ^ (ell j)) : ℂ)) *
        principalRowIntegral η S (fun j => primaryIdealGenerator (P j).val.val)
          W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (2299 / 4800 : ℝ)) Z) / normer -
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-19799 / 28800) Z‖ ≤
      C * (Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200 + nu) +
        Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 + e - (43 / 50) * ellMin)) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0, hC0, hrem⟩ := ProbePrincipalPhysical.subFarkas_physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K := K)
  obtain ⟨D, hD, hres⟩ := subFarkas_normalized_actual_window_residue S hS η ha ha2 (by linarith)
    (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏ p ∈ S, p)
  let C := C0 / e * ‖cs⁻¹‖ + D * c ^ (-(43 / 50 : ℝ)) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hpos (j : Fin K) : tsupport (W j) ⊆ Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [sub_power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y => (hWbounds j y).1) hne ell (fun j => hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ => c) (fun _ => d) ell (fun _ => hc) (fun _ => hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ, h480, hsmall, hslot, hpool⟩
  have hZ0 : 0 < Z := by linarith
  let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
  let normer := cs * (Probe.principalScalar Finset.univ Z (801 / 4800)
    (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j => Z ^ (ell j)) (c * Z ^ ellMin) (Z ^ (2299 / 4800 : ℝ)) Z h480 hsmall
    (fun j _ p _ => (hWbounds j _).1) (fun j _ p hp => (hpool j p hp).1)
    (fun j _ p hp => (hpool j p hp).2.1) (fun j _ => hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1, ?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j => Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp => (hpool j p hp).2.2) htuple Z hZ (fun j => (hslot j).1) (fun j => (hslot j).2)
  have hinv : ‖normer⁻¹‖ ≤ ‖cs⁻¹‖ * Z ^ nu := by
    dsimp only [normer]
    rw [mul_inv_rev, norm_mul, ← Complex.ofReal_inv, norm_real]
    simpa only [hsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ)) = c ^ (-(43 / 50 : ℝ)) * Z ^ (-(43 / 50 : ℝ) * ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
    congr 2; ring
  have heq1 : (C0 / e * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200)) * (‖cs⁻¹‖ * Z ^ nu) =
      (C0 / e * ‖cs⁻¹‖) * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200 + nu) := by
    rw [Real.rpow_add hZ0]; ring
  have heq2 : D * Z ^ (HeckeZeroSupremum.beta + e - 19799 / 28800) * (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ)) =
      (D * c ^ (-(43 / 50 : ℝ))) * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 + e - (43 / 50) * ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta - 19799 / 28800 + e - (43 / 50) * ellMin =
      (HeckeZeroSupremum.beta + e - 19799 / 28800) + (-(43 / 50 : ℝ) * ellMin) by ring, Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1, heq2]
  have h1 : C0 / e * ‖cs⁻¹‖ ≤ C := by
    dsimp [C]
    have : 0 ≤ D * c ^ (-(43 / 50 : ℝ)) := by positivity
    linarith
  have h2 : D * c ^ (-(43 / 50 : ℝ)) ≤ C := by
    dsimp [C]
    have : 0 ≤ C0 / e * ‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 - 1 / 1200 + nu) +
        C * Z ^ (HeckeZeroSupremum.beta - 19799 / 28800 + e - (43 / 50) * ellMin) := by gcongr
    _ = _ := by ring

end ProbePrincipalNormalized
end SubFarkasSignalComparison

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

end
