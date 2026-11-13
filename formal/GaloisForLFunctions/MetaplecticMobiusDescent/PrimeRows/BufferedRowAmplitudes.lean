/-
Buffered row amplitudes adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.PrimeRows.DyadicRowBands

/-!
# Buffered row amplitudes

Row amplitudes on lines and contour arithmetic costs; buffered integrability and polynomial
bounds of row amplitudes; uniform slice and horizontal join decay.
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
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

def rowAmplitudeOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  (∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1))*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u
        ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I))

lemma continuedRowOnLines_eq_amplitude {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0< elementNorm (primaryIdealGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  have hN : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  · exact hphys.const_mul _

lemma rowAmplitudeOnLines_first_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (υ r : ℝ)
    (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤ C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (primaryIdealGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤ B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro t
  have hn (i : Fin K) : ‖(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (primaryIdealGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem continuedPhysicalRowKernel_first_integrable {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_first_bound S hS hmax hfirst P hPS η u hu υ r hυ hr
  have hm := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤ C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hbound t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC _ hm.norm.aestronglyMeasurable (fun _=> norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ 2 r υ (by linarith)
  have hk : AEStronglyMeasurable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
    have heq : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun t=> sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
          rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t) := by funext t;exact continuedRowOnLines_eq_amplitude ..
    rw [heq]
    exact hs.aestronglyMeasurable.mul hm.aestronglyMeasurable
  exact hi.mono' hk (Filter.Eventually.of_forall fun t=> by rw [continuedRowOnLines_eq_amplitude,norm_mul])

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma physicalRow_first_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0< eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+l) :
    ∃C : ℝ,0< C ∧ ∀v : ℝ,l≤ v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z l hx hl hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by unfold height;nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_first_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr hx hl hz hxw
    (fun v hv t=> hbound v hv.1 t)

lemma nonprincipal_first_w_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+l) :
    Integrable (fun t : ℝ=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW X Y Z hY x z l l C 2 hC.le
    (fun v hv t=> hbound v hv.1 t)
  have hc : Continuous (fun t : ℝ=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x ((l:ℂ)+t*I) z hx (by simpa using hl) hz
      (by simpa using hxw)).continuousAt.comp (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=> hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0< eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character)
    (F : Finset FreeRow) (hF : ∀u∈F,u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0< a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0< Y) (x z : ℂ) (l r : ℝ) (hlr : l≤ r)
    (hx : (51/100:ℝ)≤ x.re) (hl : -(1/100:ℝ)≤ l) (hz : (17/50:ℝ)≤ z.re)
    (hxw : 1+eps≤ x.re+l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  rw [integral_finsetSum F (fun u hu=> nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l hx hl hz hxw),
    integral_finsetSum F (fun u hu=> nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
      W0 W1 a b ha hW X Y Z hY x z r hx (hl.trans hlr) hz (by linarith))]
  exact Finset.sum_congr rfl (fun u hu=> nonprincipal_first_w_integral_eq eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l r hlr hx hl hz hxw)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤ eps') : FirstTail eps' S := by
  have hp : 0< eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤ P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

theorem continuedRowOnLines_first_w_transport {K : ℕ}
    (l r ξ : ℝ) (hl : -(1/100:ℝ)≤ l) (hlr : l≤ r) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 l ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 r ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : -(1/100:ℝ)≤ q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 q ξ) heightMeasure :=
    continuedPhysicalRowKernel_first_integrable q ξ hq hξ S hS hmax hfirst P hPS η u hu W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [integral_prod _ (hi l hl),integral_prod _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  exact nonprincipal_first_w_integral_eq (1/2) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY ((2:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) l r hlr
    (by norm_num) hl (by simpa using hξ) (by norm_num;linarith)

theorem rowIntegral_first_w_lines {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤ r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤2 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨_,hphysical⟩ := rowIntegral_source_lines (1/2000) 2 3 r (by norm_num) (by norm_num)
    (by norm_num) hβ (by norm_num) (by norm_num) le_rfl hr S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hw := continuedRowOnLines_first_w_transport υ 3 r hυ hυ3 hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨continuedPhysicalRowKernel_first_integrable υ r hυ hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ,hphysical.trans (by rw [hw])⟩

theorem rowIntegral_central_start {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50)) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=> primaryIdealGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure :=
  rowIntegral_first_w_lines (1-a-6*e) (17/50) (by linarith) (by linarith) le_rfl
    S hS hmax (hfirst.mono_parameter (by linarith)) P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_joint_growth
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (ha1 : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e) :
    ∃C : ℝ,0≤ C ∧ ∀x w z : ℂ,a+16*e≤ x.re → x.re≤2 → |x.im|≤ H → w.re=1-a-6*e → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤ R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤ w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤ R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀t : HeightSpace, |t.1.1|≤ H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤ C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (primaryIdealGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤ A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro t ht
  have hn (i : Fin K) : ‖(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (primaryIdealGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤ r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤ H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤ C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤ C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=> norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=> by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃K : ℝ,0< K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀A : ℝ,0≤ A → ∀X Y Z : ℝ,0< X → 0< Y → 0< Z →
      ∀G : HeightSpace→ℂ,AEStronglyMeasurable G heightMeasure →
      (∀q,‖G q‖≤ A*jointHeight q.1.1 q.1.2 q.2^J) →
      let F := fun q : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q
      Integrable F heightMeasure ∧ ∀T : ℝ,0≤ T →
        (∫q : HeightSpace in outsideBox T,‖F q‖ ∂heightMeasure)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/(1+T)^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤ E := by dsimp [E];positivity
  let S := fun q : HeightSpace=> sourceScale X Y Z ((σ:ℂ)+q.1.1*I)
    ((υ:ℂ)+q.2*I) ((ξ:ℂ)+q.1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp hc
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : HeightSpace) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : HeightSpace) : ‖S q*G q‖≤(E*A)*jointHeight
      q.1.1 q.1.2 q.2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ (E*A) (mul_nonneg hE hA)
    (fun q=> S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : HeightSpace=> sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ q) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  intro T hT
  have hnorm := congrArg (fun f : HeightSpace→ℂ => ∫q : HeightSpace in outsideBox T,‖f q‖ ∂heightMeasure) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/(1+T)^N := hb T hT
    _ = _ := by dsimp [E];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma rowAmplitudeOnLines_first_uniform {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤ C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (primaryIdealGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤ B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro υ hυ t
  have hn (i : Fin K) : ‖(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (primaryIdealGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem original_x_height_tail {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0< X → 0< Y → 0< Z →
      ∀H : ℝ,0≤ H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_first_uniform S hS hmax hfirst P hPS η u hu r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A*D,by positivity,?_⟩
  intro υ hυ X Y Z hX hY hZ H hH
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤ T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=> sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ (ht'.2 H hH)
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=> norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := lt_of_not_ge hp
  exact Or.inl hx

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma height_slab_integral_wzx (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤ H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤ H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H},f p ∂heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with w hw
  rw [integral_prod_symm _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=> f ((x,z),w)) := by
    funext x
    simp only [Set.indicator_apply,E,Set.mem_setOf_eq,Set.mem_Icc,abs_le]
  dsimp only
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_buffered_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH0 : 0≤ H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let F := fun x w z=> continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    let E : Set HeightSpace := {t | |t.1.1|≤ H}
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫tw : ℝ,∫tz : ℝ,
          (∫tx : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+tx*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))+
          I*((∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+(-H)*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))-
            (∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+H*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))))+
          ∫p : HeightSpace in Eᶜ,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure) := by
  dsimp only
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_wzx _ H hH0 hi.integrableOn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  have hHT : H≤3*(i+1:ℕ)*B := by
    apply hH.trans
    have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
    ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_height_growth
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    : ∃C : ℝ,0≤ C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀x w z : ℂ,a+16*e≤ x.re → x.re≤2 → |x.im|≤ H → w.re=1-a-6*e → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) 0)/9
  have hR : 0≤ R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=> selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤ A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=> hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤ w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤ R*(3+|H|)^2 := by
    have hr := hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
    have hscale : Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)=R*(3+|H|)^2 := by
      dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
      rw [Real.rpow_one]
      ring
    simpa only [sourceDetectorFamily_denominator,hscale] using hr
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(R*(3+|H|)^2))*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0< a0) (ha1 : 0< a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0< zlo) (J N : ℕ) :
    ∃K : ℝ,0< K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤ A → ∀X Y Z : ℝ,0< X → 0< Y → 0< Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤ A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=> sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤ E := by dsimp [E];positivity
  let S := fun q : ℝ×ℝ=> sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=> S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=> sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ (sliceMap axis T q)) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by dsimp [E];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_uniform {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤ H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤ C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (primaryIdealGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤ A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (primaryIdealGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_slices {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|≤ H →
      let F := fun q : ℝ×ℝ=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_uniform e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (a+16*e) 2 r r (1-a-6*e) (1-a-6*e) (by linarith) 2 N
  refine ⟨(9*A)*D,by positivity,?_⟩
  intro σ hσ tx htx
  let G := fun q : ℝ×ℝ=> rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ ((tx,q.1),q.2) htx).trans
    calc
      _ ≤ A*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile σ hσ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩ .s tx
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_height_uniform {K : ℕ}
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤ H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤ C*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_height_growth e he he' S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ
  let A : ℝ := (∏i,(elementNorm (primaryIdealGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤ A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=> Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro a B H i ha haTop hB hH hbin σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (primaryIdealGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound a B H i ha haTop hB hH hbin ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem buffered_x_slice_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_height_uniform e he he' S hS hmax hfirst P hPS η u hu ψ r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A*D,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let G := fun q : ℝ×ℝ=> rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow a B H i ha haTop hB hH hbin σ hσ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤ H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0< height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by rw [pow_add];field_simp;ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma continuedRow_horizontal_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) (tx υ r : ℝ) (hr : 0< r) :
    Measurable (fun p : ℝ × (ℝ × ℝ)=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      p.1 υ r ((tx,p.2.1),p.2.2)) := by
  have hR : Continuous (fun t : ℝ=> mellin (SchwartzPlanePoisson.paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  have hW := (compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)).continuous
  have hcoords : Continuous (fun p : ℝ × (ℝ × ℝ)=>(((p.1:ℂ)+tx*I,(υ:ℂ)+p.2.2*I),(r:ℂ)+p.2.1*I)) := by fun_prop
  have hscale := (sourceScale_continuous X Y Z hX hY hZ).comp hcoords
  have hprof : Measurable (fun p : ℝ × (ℝ × ℝ)=> profile W0 W1
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    unfold profile
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hR.measurable.comp (by fun_prop)
    · exact hW.measurable.comp (by fun_prop)
  have hsource : Measurable (fun p : ℝ × (ℝ × ℝ)=> sourceMellinWeight W0 W1 X Y Z
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    simp_rw [sourceMellinWeight_eq_scale]
    exact hscale.measurable.mul hprof
  have hphysical := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun p : ℝ × (ℝ × ℝ)=>(p.1:ℂ)+tx*I) (fun p : ℝ × (ℝ × ℝ)=>(υ:ℂ)+p.2.2*I)
    (fun p : ℝ × (ℝ × ℝ)=>(r:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold continuedRowOnLines continuedPhysicalRowKernel
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul hsource
      apply Finset.measurable_prod
      intro i hi
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _
          (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero).ne'
      · fun_prop
    · unfold frequencyWeight
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
      · fun_prop
  · exact hphysical.const_mul _

lemma horizontal_integral_bound (F : ℝ→(ℝ×ℝ)→ℂ) (l r C : ℝ) (hlr : l≤ r) (_hC : 0≤ C)
    (hm : Measurable (Function.uncurry F))
    (hi : ∀v∈Ioc l r,Integrable (F v) (volume.prod volume))
    (hb : ∀v∈Ioc l r,(∫q : ℝ×ℝ,‖F v q‖ ∂volume.prod volume)≤ C) :
    Integrable (fun q : ℝ×ℝ=>∫v : ℝ in l..r,F v q) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖∫v : ℝ in l..r,F v q‖ ∂volume.prod volume)≤(r-l)*C := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let ν : Measure (ℝ×ℝ) := volume.prod volume
  have hm' : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := hm.aestronglyMeasurable
  have hnorm : Integrable (fun v=>∫q,‖F v q‖ ∂ν) μ := by
    apply (integrable_const C).mono' hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=> norm_nonneg _))]
    exact hb v hv
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hm').mpr
    refine ⟨?_,hnorm⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hi v hv
  have hj : Integrable (fun q=>∫v,F v q ∂μ) ν := hprod.integral_prod_right
  simp only [intervalIntegral.integral_of_le hlr]
  refine ⟨hj,?_⟩
  calc
    _ ≤ ∫q,∫v,‖F v q‖ ∂μ ∂ν := integral_mono hj.norm hprod.integral_norm_prod_right
      (fun q=> norm_integral_le_integral_norm _)
    _ = ∫v,∫q,‖F v q‖ ∂ν ∂μ := integral_integral_swap hprod.norm.swap
    _ ≤ ∫v,C ∂μ := integral_mono_ae hnorm (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hb v hv)
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hlr,smul_eq_mul]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem buffered_horizontal_join_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) :
    ∃C : ℝ,0≤ C ∧ ∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := buffered_x_slice_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr
  refine ⟨2*C,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  let A : ℝ := C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤ A := by dsimp [A];exact div_nonneg (mul_nonneg hC (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤ A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O

lemma height_slab_partial_integrable (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤ H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤ H} heightMeasure) :
    Integrable (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) (volume.prod volume) := by
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  have hp := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)).symm MeasurableEquiv.prodAssoc
  have hr : Integrable (fun p : ℝ × (ℝ × ℝ)=>(E.indicator f) ((p.1,p.2.1),p.2.2))
      (volume.prod (volume.prod volume)) := hp.integrable_comp_of_integrable hi
  have hj := hr.integral_prod_right
  have heq : (fun q : ℝ×ℝ=>∫x : ℝ,(E.indicator f) ((x,q.1),q.2))=
      (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) := by
    funext q
    have hfun : (fun x : ℝ=>(E.indicator f) ((x,q.1),q.2))=
        (Icc (-H) H).indicator (fun x=> f ((x,q.1),q.2)) := by
      funext x
      simp only [Set.indicator_apply,E,Set.mem_setOf_eq,Set.mem_Icc,abs_le]
    rw [hfun,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith)]
  exact heq ▸ hj

lemma height_slab_integral_pair (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤ H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤ H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H},f p ∂heightMeasure)=
      ∫q : ℝ×ℝ,(∫x : ℝ in -H..H,f ((x,q.1),q.2)) ∂volume.prod volume := by
  rw [height_slab_integral_wzx f H hH hf]
  exact (integral_prod_symm _ (height_slab_partial_integrable f H hH hf)).symm

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0< e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤ a) (haTop : a≤1) (hB : 2< B) (hH0 : 0≤ H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let k := fun σ p=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤ H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  dsimp only
  let k := fun σ p=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hleft := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  obtain ⟨C,hC,hjoins⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 0 (17/50) le_rfl
  have hJ (tx : ℝ) (htx : |tx|=H) :
      Integrable (fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) (volume.prod volume) :=
    (hjoins X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx).1
  have hm := hJ (-H) (by rw [abs_neg,abs_of_nonneg hH0])
  have hp := hJ H (abs_of_nonneg hH0)
  have hc := height_slab_partial_integrable _ H hH0 hleft
  refine ⟨hleft,?_⟩
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_pair _ H hH0 hi.integrableOn,
    height_slab_integral_pair _ H hH0 hleft]
  have heq : (fun q : ℝ×ℝ=>∫tx : ℝ in -H..H,k 2 ((tx,q.1),q.2))=
      (fun q : ℝ×ℝ=>(∫tx : ℝ in -H..H,k (a+16*e) ((tx,q.1),q.2))+
        I*((∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2))-(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)))) := by
    funext q
    have hHT : H≤3*(i+1:ℕ)*B := by
      apply hH.trans
      have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
    simpa only [k,continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
        ((((1-a-6*e):ℝ):ℂ)+q.2*I) ((17/50:ℂ)+q.1*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT
  rw [heq]
  dsimp only [k] at hm hp ⊢
  have hsplit := integral_add hc ((hm.sub hp).const_mul I)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_const_mul]
  congr 1
  exact congrArg (fun z : ℂ=> I*z) (integral_sub hm hp)

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

/-- The shifted row integral truncated in the first height coordinate. -/
def centralRowIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤ H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

lemma scaleBound_eq_rpow_of_one_le {q lo hi : ℝ} (hq : 1≤ q) (hl : lo≤ hi) :
    scaleBound q lo hi=q^hi := by
  unfold scaleBound
  rw [max_eq_right (mul_le_mul_of_nonneg_left hl (Real.log_nonneg hq)),
    Real.rpow_def_of_pos (by linarith)]

theorem original_row_central_error {K : ℕ}
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→ Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤ C ∧ ∀X Y Z : ℝ,0< X → 0< Y → 1≤ Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → 0≤ H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  obtain ⟨Ct,hCt,htail⟩ := original_x_height_tail S hS hmax (hfirst.mono_parameter (by linarith)) P hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hZ0 : 0< Z := by linarith
  let k := fun σ p=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤ H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1)/height H^N
  have hA : 0≤ A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤ Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    exact hb.trans_eq (by dsimp only [A]; ring)
  have ht : ‖tail‖≤ Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    exact hb.trans_eq (by dsimp only [A,height]; rw [abs_of_nonneg hH0]; ring)
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=> primaryIdealGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O

lemma selectedFirstBound_polynomial {Q : ℝ} (hQ : 1≤ Q) : selectedFirstBound Q 2≤8192*Q^3 := by
  have hQ0 : 0≤ Q := by linarith
  have hsmall : Q^(1/100:ℝ)≤ Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1/100:ℝ)≤1)
  have hsmall0 : 0≤ Q^(1/100:ℝ) := Real.rpow_nonneg hQ0 _
  have hQQ : Q≤ Q^2 := by nlinarith
  have hQ2 : 0≤ Q^2 := sq_nonneg Q
  have hQ3 : Q^2≤ Q^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  unfold selectedFirstBound
  rw [Real.rpow_two]
  calc
    _ ≤ 2*((2*Q^2)*2*(2*Q)*388+Q*(2*Q)) := by gcongr <;> nlinarith
    _ ≤ _ := by nlinarith

theorem nonprincipal_first_uniform_growth :
    ∃C : ℝ,0< C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖HeckeOrigin.continued χ s‖≤ C*(χ.modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let U := HeckeLogarithmicInput.uniformConstant
  have hU : 0≤ U := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨1+U*Cd,by positivity,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=> hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hN : (1:ℝ)≤χ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one χ
  have hψN : (1:ℝ)≤ψ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one ψ
  have hQ' : (ψ.modulus.absNorm:ℝ)≤χ.modulus.absNorm := by exact_mod_cast hQ
  have hpow : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤χ.modulus.absNorm := by
    apply le_trans _ hQ'
    simpa using Real.rpow_le_rpow_of_exponent_le hψN (by norm_num : (3/5:ℝ)≤1)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤ s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hl : ‖LFunction ψ s‖≤ U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2 := by
    exact hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hU) (sq_nonneg _))
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤ Cd*(χ.modulus.absNorm:ℝ)^2 := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    calc
      _ ≤ (χ.modulus.absNorm:ℝ)^(max (-s.re) 0+1) := Real.rpow_le_rpow (by positivity)
        (HeckeDyadic.radical_norm_le_modulus χ) (by positivity)
      _ ≤ (χ.modulus.absNorm:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num);linarith)
      _ = _ := Real.rpow_two _
  rw [HeckeOrigin.continued,if_neg hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2)*(Cd*(χ.modulus.absNorm:ℝ)^2) :=
      mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤χ.modulus.absNorm) 3) (sq_nonneg (3+|s.im|))]

theorem calibrated_numerator_first_uniform_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0< C ∧ ∀u : FreeRow,u.val≠1 → ∀s : ℂ,-(1/100:ℝ)≤ s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_first_uniform_growth
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤ A := by dsimp [A];positivity
  refine ⟨C*(1+A^3),by positivity,?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^3*(3+|s.im|)^2 := by gcongr
      _ ≤ _ := by
        rw [mul_pow]
        nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm) 3)
          (sq_nonneg (3+|s.im|))]

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem buffered_denominator_polynomial_growth (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0< C ∧ ∀(η : Character) (u : FreeRow) (ψ : ι→ Character)
      (a B H : ℝ) (i : ℕ),(51/100:ℝ)≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀x : ℂ,a+16*e≤ x.re → x.re≤2 → |x.im|≤ H →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^2*(3+|H|)^2 := by
  obtain ⟨C,hC,hbound⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤ A := by dsimp [A];positivity
  refine ⟨2*C*(1+A^2),by positivity,?_⟩
  intro η u ψ a B H i ha haTop hB hH hbin x hxl hxr hxi
  let χ := (targetRow η u).excludePrimes S hS
  have hb := hbound (sourceDetectorFamily S hS η u ψ) B a H i hB ha haTop hH hbin (Sum.inl false) x hxl hxr hxi
  simp only [sourceDetectorFamily_denominator,Real.rpow_one] at hb
  have hQ : (χ.modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [χ,A]
    exact_mod_cast (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh)
  apply hb.trans
  unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity
  have hrad := HeckeDyadic.radical_norm_le_modulus χ
  calc
    _ ≤ C*((χ.modulus.absNorm:ℝ)*(2*(χ.modulus.absNorm:ℝ)*(3+|H|)^2)) := by gcongr
    _ ≤ C*(((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*
        (2*((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*(3+|H|)^2)) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((η.modulus.absNorm:ℝ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)*(3+|H|))]

def coarsePrimeCost (T : Finset HeckeIdealSeries.PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3

lemma coarsePrimeCost_nonneg (T : Finset HeckeIdealSeries.PrimeIdeal) : 0≤ coarsePrimeCost T := by
  unfold coarsePrimeCost
  positivity

theorem calibrated_physicalRow_buffered_polynomial_growth
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (ψ : ι→ Character),
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀x w z : ℂ,a+16*e≤ x.re → x.re≤2 → |x.im|≤ H → w.re=1-a-6*e → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*
          coarsePrimeCost T*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_denominator_polynomial_growth (ι:=ι) e he he' S hS.prime
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*Cr*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT ψ a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hwlow : -(1/100:ℝ)≤ w.re := by rw [hw];linarith
  have hn' := hn u hu w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec := hreciprocal η u ψ a B H i ha ha1 hB hH hbin x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤ coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    have hQ : (4:ℝ)≤ P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    exact (continuedCompensatedLocal_first_bound η u P.val _ hQ 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)).trans (selectedFirstBound_polynomial (by linarith))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(Cr*(η.modulus.absNorm:ℝ)^2*N^2*(3+|H|)^2))*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

theorem calibrated_physicalRow_first_joint_polynomial_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀P∈T,P.val∉S),∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤ w.re → (17/50:ℝ)≤ z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤ C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*coarsePrimeCost T*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤ L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*L*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hn' := hn u hu w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤ Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤ L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤ L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤ coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod (fun _ _=> norm_nonneg _)
    intro P hP
    apply (continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)).trans
    exact selectedFirstBound_polynomial (by have hn:=hS.tail.norm_four P.val (hT P.val P.property);exact_mod_cast (by omega : 1≤ P.val.val.absNorm))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

lemma coarsePrimeCost_image {K : ℕ} (P : Fin K→ HeckeIdealSeries.PrimeIdeal) (hP : Function.Injective P) :
    coarsePrimeCost (Finset.univ.image P)=(8192:ℝ)^K*(∏i,(P i).val.absNorm:ℝ)^3 := by
  unfold coarsePrimeCost
  rw [Finset.prod_image (by intro a ha b hb hab;exact hP hab)]
  rw [Finset.prod_mul_distrib,←Finset.prod_pow]
  simp

lemma prime_frequency_amplitude_le_one {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (P : Fin K→ HeckeIdealSeries.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) (u : FreeRow) (r : ℝ) (hr : 0≤ r) (hr1 : r≤1) (t : ℝ) :
    ‖(∏i,(elementNorm (primaryIdealGenerator (P i).val):ℂ)^(((r:ℂ)+t*I)-1))*
      frequencyWeight ((r:ℂ)+t*I) ⟨u.val,u.property.1⟩‖≤1 := by
  have hp (i : Fin K) : 1≤ elementNorm (primaryIdealGenerator (P i).val) := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using
        (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero))
  have hu : 1≤ elementNorm u.val := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  rw [norm_mul,norm_prod]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
  · apply Finset.prod_le_one (fun _ _=> norm_nonneg _)
    intro i hi
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hp i])]
    simp only [sub_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,one_re]
    simpa using Real.rpow_le_rpow_of_exponent_le (hp i) (by linarith : r-1≤0)
  · unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0< elementNorm u.val)]
    simp only [neg_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    simpa using Real.rpow_le_rpow_of_exponent_le hu (by linarith : -r≤0)

/-- Polynomial conductor and prime-norm cost of the contour estimates. -/
def contourArithmeticCost {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) : ℝ :=
  (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*(∏i,(P i).val.absNorm:ℝ)^3

lemma contourArithmeticCost_nonneg {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→ HeckeIdealSeries.PrimeIdeal) :
    0≤ contourArithmeticCost η u P := by unfold contourArithmeticCost;positivity

theorem rowAmplitudeOnLines_buffered_polynomial (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,|t.1.1|≤ H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤
        C*contourArithmeticCost η u P*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_polynomial_growth (ι:=ι) e he he' S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r hr t ht
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS) ψ a B H i ha haTop hB hH hbin
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans_eq
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  ring

theorem rowAmplitudeOnLines_first_polynomial (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤
        C*contourArithmeticCost η u P*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_polynomial_growth S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ r hr t
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS)
    ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  have hN : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  have hη := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hN46 : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    pow_le_pow_right₀ hN (by norm_num)
  have hη2 : (1:ℝ)≤(η.modulus.absNorm:ℝ)^2 := by nlinarith
  have hlarge : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤
      (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    hN46.trans (le_mul_of_one_le_left (by positivity) hη2)
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  calc
    _ = (C*(8192:ℝ)^K)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*(∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 := by ring
    _ ≤ (C*(8192:ℝ)^K)*((η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6)*
        (∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlarge (mul_nonneg hC (pow_nonneg (by norm_num) _)))
        (pow_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (P i).val.absNorm)) _)) (sq_nonneg _)
    _ = _ := by ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_x_slice_decay (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤ a → a≤1 → 2< B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤ A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin
  let G := fun q : ℝ×ℝ=> rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ r ⟨hr,hr1⟩ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤ H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0< height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end ProbeHighRowFamily

end

end

noncomputable section
open CubicSieve CenteredMomentFourier Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_horizontal_join_decay (K : ℕ)
    (e : ℝ) (he : 0< e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤ r) (hr1 : r≤1) :
    ∃C : ℝ,0≤ C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→ HeckeIdealSeries.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→ Character,∀X Y Z : ℝ,0< X → 0< Y → 0< Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤ a → a≤1 → 2< B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)< a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound0⟩ := uniform_buffered_x_slice_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr hr1
  refine ⟨2*C,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  have hbound := hbound0 η u hu P hP hPS ψ
  have hcost := contourArithmeticCost_nonneg η u P
  let A : ℝ := C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤ A := by dsimp [A];exact div_nonneg (mul_nonneg (mul_nonneg hC hcost) (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤ A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=> continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end ProbeHighRowFamily

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
