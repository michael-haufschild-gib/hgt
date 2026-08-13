import GaloisForLFunctions.HTGeometry.NevanlinnaPositiveCarrierCapstone
import GaloisForLFunctions.HTGeometry.NevanlinnaClassicalInterface
import GaloisForLFunctions.HTGeometry.CauchyJetFrame
import GaloisForLFunctions.HTGeometry.LocalNevanlinnaJetTriangular

/-!
# Analytic Nevanlinna carrier bridge

The projective boundary kernel records the classical extremal measures and their support labels,
but it deliberately does not postulate their analytic Cauchy-transform formula.  This file adds a
source-faithful interface for precisely that classical formula and proves the project-specific
consequence: a positive bounded reweighting has Cauchy transform equal to the full affine
Nevanlinna family `m₀ + a/(τ-q)` averaged against the density.  No part of the affine reduction or
the barycentric integration argument is left as an external assumption.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint Filter Measure Metric Complex
open scoped ENNReal OnePoint Topology ComplexOrder

noncomputable section

/-- Classical analytic data in the carrier convention.  The base family is the source-faithful
classical N-extremal family.  The four entire functions extend its determinant-one real carrier
matrix, and the two transform fields are exactly the finite and infinite parts of the classical
Nevanlinna parametrization. -/
structure ClassicalAnalyticNevanlinnaCarrierFamily (s : ℕ → ℝ) where
  base : ClassicalNevanlinnaExtremalFamily s
  a : ℂ → ℂ
  b : ℂ → ℂ
  c : ℂ → ℂ
  d : ℂ → ℂ
  differentiable_a : Differentiable ℂ a
  differentiable_b : Differentiable ℂ b
  differentiable_c : Differentiable ℂ c
  differentiable_d : Differentiable ℂ d
  det_one : ∀ z, a z * d z - b z * c z = 1
  a_real : ∀ x : ℝ, a x = base.toBoundaryFamily.matrix.a x
  b_real : ∀ x : ℝ, b x = base.toBoundaryFamily.matrix.b x
  c_real : ∀ x : ℝ, c x = base.toBoundaryFamily.matrix.c x
  d_real : ∀ x : ℝ, d x = base.toBoundaryFamily.matrix.d x
  finite_cauchy : ∀ (tau : ℝ) (z : ℂ), 0 < z.im →
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(base.leaf tau : Measure ℝ)) =
      (a z * tau + b z) / (c z * tau + d z)
  infinity_cauchy : ∀ z : ℂ, 0 < z.im → c z ≠ 0 →
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(base.leaf ∞ : Measure ℝ)) = a z / c z

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The background, amplitude, and projective pole of the analytic carrier chart. -/
def background (z : ℂ) : ℂ := F.a z / F.c z

def amplitude (z : ℂ) : ℂ := -1 / F.c z ^ 2

def quotient (z : ℂ) : ℂ := -F.d z / F.c z

/-- Every derivative of the meromorphic background is smooth on its literal denominator-regular
locus.  Thus the compact-patch background regularity hypothesis is automatic for the classical
analytic carrier family. -/
theorem contDiffOn_iteratedDeriv_background (k : ℕ) :
    ContDiffOn ℂ ⊤ (iteratedDeriv k F.background) (projectiveRegularLocus F.c) := by
  let U := projectiveRegularLocus F.c
  have hU : IsOpen U := projectiveRegularLocus_isOpen F.differentiable_c
  have hbackground : DifferentiableOn ℂ F.background U := by
    exact F.differentiable_a.differentiableOn.div F.differentiable_c.differentiableOn
      (fun z hz => by simpa [U, projectiveRegularLocus] using hz)
  have hiter : DifferentiableOn ℂ (iteratedDeriv k F.background) U := by
    induction k with
    | zero => simpa [iteratedDeriv_zero] using hbackground
    | succ k ih =>
        rw [iteratedDeriv_succ]
        exact ih.deriv hU
  exact hiter.contDiffOn hU

/-- In a one-node packet, the finite projective expansion coordinate is literally the scalar
Nevanlinna jet expansion. -/
theorem projectiveNevanlinnaJetExpansionColumn_singleton_coe
    (a q : ℂ → ℂ) (tau : ℝ) (z : ℂ) (n : ℕ) :
    projectiveNevanlinnaJetExpansionColumn
        a q (fun _ : Unit => z) (fun _ : Unit => n + 1) (tau : OnePoint ℝ)
        ⟨(), ⟨n, Nat.lt_succ_self n⟩⟩ =
      nevanlinnaJetExpansion a q tau n z := by
  rw [projectiveNevanlinnaJetExpansionColumn, nevanlinnaJetExpansion]
  rw [Fin.sum_univ_eq_sum_range
    (fun k => nevanlinnaJetCoeff a q n k z *
      projectiveCauchyPower (q z) k (tau : OnePoint ℝ)) (n + 1)]
  simp only [projectiveCauchyPower_coe]

/-- A selected jet coordinate only uses projective powers through its own derivative order.
Hence a coordinate in a longer packet is exactly the last coordinate of the corresponding
minimal one-node packet. -/
theorem projectiveNevanlinnaJetExpansionColumn_coordinate_eq_singleton_last
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (nodes : ι → ℂ) (orders : ι → ℕ)
    (t : OnePoint ℝ) (i : ι) (j : Fin (orders i)) :
    projectiveNevanlinnaJetExpansionColumn a q nodes orders t ⟨i, j⟩ =
      projectiveNevanlinnaJetExpansionColumn
        a q (fun _ : Unit => nodes i) (fun _ : Unit => j.1 + 1) t
        ⟨(), Fin.last j.1⟩ := by
  simp only [projectiveNevanlinnaJetExpansionColumn]
  rw [Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        nevanlinnaJetCoeff a q j k (nodes i) *
          projectiveCauchyPower (q (nodes i)) k t),
    Fin.sum_univ_eq_sum_range
      (fun k : ℕ =>
        nevanlinnaJetCoeff a q (Fin.last j.1) k (nodes i) *
          projectiveCauchyPower (q (nodes i)) k t)]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hkn
    simp only [Finset.mem_range, not_lt] at hk hkn
    have hjk : j.1 < k := by omega
    have hzero : nevanlinnaJetCoeff a q (Fin.last j.1) k = 0 := by
      simpa using (nevanlinnaJetCoeff_eq_zero_of_lt a q hjk)
    rw [hzero]
    simp

/-- Selecting one coordinate of a finite smooth projective control is independent of the other
nodes in the packet.  This is the exact compatibility needed to compare the simultaneous
transversality packet with the one-node analytic carrier identity. -/
theorem projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (orders : ι → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (η : ℝ) (hη : 0 < η) (nodes : ι → ℂ)
    (hupper : ∀ i, η ≤ (q (nodes i)).im)
    (w : Lp ℝ (⊤ : ENNReal) eta) (i : ι) (j : Fin (orders i)) :
    (projectiveNevanlinnaJetExpansionSmoothControl
        a q orders eta nodes w) ⟨i, j⟩ =
      (projectiveNevanlinnaJetExpansionSmoothControl
        a q (fun _ : Unit => orders i) eta (fun _ : Unit => nodes i) w) ⟨(), j⟩ := by
  let z : ι → NevanlinnaUpperNodeAtLeast q η := fun k => ⟨nodes k, hupper k⟩
  let zi : Unit → NevanlinnaUpperNodeAtLeast q η := fun _ => ⟨nodes i, hupper i⟩
  rw [projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q orders eta η hη z,
    projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun _ : Unit => orders i) eta η hη zi,
    linftyBochnerControl_apply_pi, linftyBochnerControl_apply_pi]
  apply integral_congr_ae
  filter_upwards [] with t
  rfl

/-- The same coordinate compatibility with the one-node packet truncated at the selected order.
This is the form matched by the analytic all-order carrier identity. -/
theorem projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton_last
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (orders : ι → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (η : ℝ) (hη : 0 < η) (nodes : ι → ℂ)
    (hupper : ∀ i, η ≤ (q (nodes i)).im)
    (w : Lp ℝ (⊤ : ENNReal) eta) (i : ι) (j : Fin (orders i)) :
    (projectiveNevanlinnaJetExpansionSmoothControl
        a q orders eta nodes w) ⟨i, j⟩ =
      (projectiveNevanlinnaJetExpansionSmoothControl
        a q (fun _ : Unit => j.1 + 1) eta (fun _ : Unit => nodes i) w)
          ⟨(), Fin.last j.1⟩ := by
  let z : ι → NevanlinnaUpperNodeAtLeast q η := fun k => ⟨nodes k, hupper k⟩
  let zi : Unit → NevanlinnaUpperNodeAtLeast q η := fun _ => ⟨nodes i, hupper i⟩
  rw [projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q orders eta η hη z,
    projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
      a q (fun _ : Unit => j.1 + 1) eta η hη zi,
    linftyBochnerControl_apply_pi, linftyBochnerControl_apply_pi]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  simpa [z, zi] using
    (projectiveNevanlinnaJetExpansionColumn_coordinate_eq_singleton_last
      a q nodes orders t i j)

/-- Complex determinant-one Mobius subtraction. -/
theorem complex_mobius_difference
    {A B C D tau : ℂ} (hdet : A * D - B * C = 1)
    (hC : C ≠ 0) (hden : C * tau + D ≠ 0) :
    (A * tau + B) / (C * tau + D) =
      A / C + (-1 / C ^ 2) / (tau - (-D / C)) := by
  have hden' : tau * C + D ≠ 0 := by simpa [mul_comm] using hden
  field_simp [hC, hden, hden']
  linear_combination -(C * tau + D) * hdet

/-- A real parameter cannot meet an upper-half-plane projective pole, so the finite Mobius
denominator is nonzero on the analytic chart. -/
theorem finite_denominator_ne_zero_of_quotient_upper
    (z : ℂ) (hc : F.c z ≠ 0) (hq : 0 < (F.quotient z).im) (tau : ℝ) :
    F.c z * (tau : ℂ) + F.d z ≠ 0 := by
  have htauq : (tau : ℂ) ≠ F.quotient z := by
    intro h
    have him := congrArg Complex.im h
    simp only [ofReal_im] at him
    linarith
  have hfactor : F.c z * (tau : ℂ) + F.d z =
      F.c z * ((tau : ℂ) - F.quotient z) := by
    simp only [quotient]
    field_simp [hc]
    ring
  rw [hfactor]
  exact mul_ne_zero hc (sub_ne_zero.mpr htauq)

/-- The two classical transform clauses combine into one continuous projective affine formula.
The value at the point at infinity is exactly the background because the projective Cauchy term
vanishes there. -/
theorem leaf_cauchy_eq_background_add_projective
    (t : OnePoint ℝ) (z : ℂ) (hz : 0 < z.im)
    (hc : F.c z ≠ 0) (hq : 0 < (F.quotient z).im) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) =
      F.background z + F.amplitude z * projectiveCauchyPower (F.quotient z) 0 t := by
  induction t using OnePoint.rec with
  | coe tau =>
      rw [F.finite_cauchy tau z hz]
      rw [complex_mobius_difference (F.det_one z) hc
        (F.finite_denominator_ne_zero_of_quotient_upper z hc hq tau)]
      simp [background, amplitude, quotient, projectiveCauchyPower, div_eq_mul_inv]
  | infty =>
      rw [F.infinity_cauchy z hz hc]
      simp [background, amplitude, quotient, projectiveCauchyPower]

/-- The projective affine leaf transform is continuous in the compactified real parameter. -/
theorem continuous_leaf_cauchy
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) :
    Continuous (fun t : OnePoint ℝ =>
      ∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) := by
  have hproj : Continuous (projectiveCauchyPower (F.quotient z) 0) :=
    continuous_projectiveCauchyPower (F.quotient z) hq.ne' 0
  apply (continuous_const.add (continuous_const.mul hproj)).congr
  intro t
  exact (F.leaf_cauchy_eq_background_add_projective t z hz hc hq).symm

/-- Every classical leaf jet is the background jet plus the literal forward projective
Nevanlinna expansion used by the transversality family.  This is local on the meromorphic regular
locus, so no fictitious global smooth extension of `-1/c²` or `-d/c` is assumed. -/
theorem iteratedDeriv_leafCauchy_eq_background_add_expansion
    (t : OnePoint ℝ) (z : ℂ) (hz : 0 < z.im)
    (hc : F.c z ≠ 0) (hq : 0 < (F.quotient z).im) (n : ℕ) :
    iteratedDeriv n
        (fun w => ∫ x, ((x : ℂ) - w)⁻¹ ∂(F.base.leaf t : Measure ℝ)) z =
      iteratedDeriv n F.background z +
        projectiveNevanlinnaJetExpansionColumn
          F.amplitude F.quotient (fun _ : Unit => z) (fun _ : Unit => n + 1) t
          ⟨(), ⟨n, Nat.lt_succ_self n⟩⟩ := by
  let U : Set ℂ := projectiveRegularLocus F.c
  have hU : IsOpen U := projectiveRegularLocus_isOpen F.differentiable_c
  have hzU : z ∈ U := hc
  have hcoords := contDiffOn_projectiveNevanlinna_coordinates
    F.differentiable_c F.differentiable_d
  have hamp : ContDiffOn ℂ ⊤ F.amplitude U := by
    simpa [amplitude, U] using! hcoords.1
  have hquot : ContDiffOn ℂ ⊤ F.quotient U := by
    simpa [quotient, U] using! hcoords.2
  have hbackground : ContDiffOn ℂ ⊤ F.background U := by
    have ha : ContDiff ℂ ⊤ F.a := F.differentiable_a.contDiff
    have hcDiff : ContDiff ℂ ⊤ F.c := F.differentiable_c.contDiff
    exact ha.contDiffOn.div hcDiff.contDiffOn
      (fun w hw => by simpa [U, projectiveRegularLocus] using hw)
  have hbackgroundAt : ContDiffAt ℂ ⊤ F.background z :=
    hbackground.contDiffAt (hU.mem_nhds hzU)
  have hampAt : ContDiffAt ℂ ⊤ F.amplitude z :=
    hamp.contDiffAt (hU.mem_nhds hzU)
  have hquotAt : ContDiffAt ℂ ⊤ F.quotient z :=
    hquot.contDiffAt (hU.mem_nhds hzU)
  have hzEv : ∀ᶠ w in 𝓝 z, 0 < w.im :=
    continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hz
  have hcEv : ∀ᶠ w in 𝓝 z, F.c w ≠ 0 :=
    F.differentiable_c.continuous.continuousAt.eventually_ne hc
  have hqEv : ∀ᶠ w in 𝓝 z, 0 < (F.quotient w).im :=
    continuousAt_const.eventually_lt
      (Complex.continuous_im.continuousAt.comp hquotAt.continuousAt) hq
  induction t using OnePoint.rec with
  | coe tau =>
      have hden : (tau : ℂ) - F.quotient z ≠ 0 := by
        intro heq
        have him := congrArg Complex.im heq
        simp only [sub_im, ofReal_im, zero_sub, zero_im] at him
        linarith
      have hcenteredAt : ContDiffAt ℂ ⊤
          (fun w => F.amplitude w * ((tau : ℂ) - F.quotient w)⁻¹) z :=
        hampAt.mul ((contDiffAt_const.sub hquotAt).inv hden)
      have heq :
          (fun w => ∫ x, ((x : ℂ) - w)⁻¹
            ∂(F.base.leaf (tau : OnePoint ℝ) : Measure ℝ)) =ᶠ[𝓝 z]
          (fun w => F.background w +
            F.amplitude w * ((tau : ℂ) - F.quotient w)⁻¹) := by
        filter_upwards [hzEv, hcEv, hqEv] with w hwUpper hwc hwq
        simpa [projectiveCauchyPower, div_eq_mul_inv] using
          F.leaf_cauchy_eq_background_add_projective
            (tau : OnePoint ℝ) w hwUpper hwc hwq
      calc
        iteratedDeriv n
            (fun w => ∫ x, ((x : ℂ) - w)⁻¹
              ∂(F.base.leaf (tau : OnePoint ℝ) : Measure ℝ)) z =
            iteratedDeriv n
              (fun w => F.background w +
                F.amplitude w * ((tau : ℂ) - F.quotient w)⁻¹) z :=
          heq.iteratedDeriv_eq n
        _ = iteratedDeriv n F.background z +
            iteratedDeriv n
              (fun w => F.amplitude w * ((tau : ℂ) - F.quotient w)⁻¹) z := by
          exact iteratedDeriv_add
            (hbackgroundAt.of_le (by simp)) (hcenteredAt.of_le (by simp))
        _ = iteratedDeriv n F.background z +
            nevanlinnaJetExpansion F.amplitude F.quotient tau n z := by
          rw [iteratedDeriv_nevanlinnaKernel_eq_expansion_of_contDiffOn
            hU hamp hquot tau z hzU hden n]
        _ = _ := by
          rw [projectiveNevanlinnaJetExpansionColumn_singleton_coe]
  | infty =>
      have heq :
          (fun w => ∫ x, ((x : ℂ) - w)⁻¹
            ∂(F.base.leaf ∞ : Measure ℝ)) =ᶠ[𝓝 z] F.background := by
        filter_upwards [hzEv, hcEv] with w hwUpper hwc
        exact F.infinity_cauchy w hwUpper hwc
      rw [heq.iteratedDeriv_eq n]
      simp [projectiveNevanlinnaJetExpansionColumn]

/-- The Cauchy kernel at an upper-half-plane point is integrable against every finite real
measure. -/
theorem integrable_cauchyKernel_of_im_pos
    (mu : Measure ℝ) [IsFiniteMeasure mu] (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) mu := by
  have hzsupport : z ∉ algebraMap ℝ ℂ '' mu.support := by
    rintro ⟨x, _hx, hzx⟩
    have him := congrArg Complex.im hzx
    change ((x : ℂ)).im = z.im at him
    simp only [ofReal_im] at him
    linarith
  simpa [resolvent, pow_one] using
    (integrable_resolvent_pow (μ := mu) hzsupport 1)

/-- Every positive power of the upper-half-plane Cauchy kernel is integrable against a finite
real measure. -/
theorem integrable_cauchyKernel_pow_of_im_pos
    (mu : Measure ℝ) [IsFiniteMeasure mu] (z : ℂ) (hz : 0 < z.im) (r : ℕ) :
    Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹) ^ r) mu := by
  have hzsupport : z ∉ algebraMap ℝ ℂ '' mu.support := by
    rintro ⟨x, _hx, hzx⟩
    have him := congrArg Complex.im hzx
    change ((x : ℂ)).im = z.im at him
    simp only [ofReal_im] at him
    linarith
  simpa [resolvent] using (integrable_resolvent_pow (μ := mu) hzsupport r)

/-- Complex Fubini for a bounded-density reweighting of the Nevanlinna boundary kernel.  The
inner-integral continuity hypothesis is automatic for the Cauchy jet functions used below. -/
theorem weightedBoundaryCarrier_integral_eq_parameterIntegral
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (f : ℝ → ℂ) (hf : Continuous f)
    (hcarrier : Integrable f
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w))
    (hleaf : ∀ t, Integrable f (F.base.leaf t : Measure ℝ))
    (hinner : Continuous (fun t : OnePoint ℝ =>
      ∫ x, f x ∂(F.base.leaf t : Measure ℝ))) :
    (∫ x, f x ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
      ∫ t, (w t) • (∫ x, f x ∂(F.base.leaf t : Measure ℝ)) ∂eta := by
  letI (t : OnePoint ℝ) : IsProbabilityMeasure
      (F.base.leaf t : Measure ℝ) := (F.base.leaf t).prop
  let inner : OnePoint ℝ → ℂ := fun t =>
    ∫ x, f x ∂(F.base.leaf t : Measure ℝ)
  have hinnerLp : MemLp inner 1 eta :=
    hinner.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hparam : Integrable (fun t => (w t) • inner t) eta :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).integrable_of_bilin_of_bdd_left
      ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm eta w)
      (hinnerLp.integrable (by norm_num))
  apply Complex.ext
  · have hrecarrier := integral_re hcarrier
    change (∫ x, (f x).re
      ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
        (∫ x, f x ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w).re at hrecarrier
    have hreparam := integral_re hparam
    change (∫ t, (((w t) • inner t)).re ∂eta) =
      (∫ t, (w t) • inner t ∂eta).re at hreparam
    rw [← hrecarrier, ← hreparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (f x).re) F.base.toBoundaryFamily.measurable_leaf
      (Complex.continuous_re.comp hf).measurable hcarrier.re]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have hreleaf := integral_re (hleaf t)
    change (∫ x, (f x).re ∂(F.base.leaf t : Measure ℝ)) =
      (∫ x, f x ∂(F.base.leaf t : Measure ℝ)).re at hreleaf
    change (w t) * (∫ x, (f x).re ∂(F.base.leaf t : Measure ℝ)) =
      ((w t) • inner t).re
    rw [hreleaf]
    simp [inner, Complex.real_smul]
  · have himcarrier := integral_im hcarrier
    change (∫ x, (f x).im
      ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
        (∫ x, f x ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w).im at himcarrier
    have himparam := integral_im hparam
    change (∫ t, (((w t) • inner t)).im ∂eta) =
      (∫ t, (w t) • inner t ∂eta).im at himparam
    rw [← himcarrier, ← himparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (f x).im) F.base.toBoundaryFamily.measurable_leaf
      (Complex.continuous_im.comp hf).measurable hcarrier.im]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have himleaf := integral_im (hleaf t)
    change (∫ x, (f x).im ∂(F.base.leaf t : Measure ℝ)) =
      (∫ x, f x ∂(F.base.leaf t : Measure ℝ)).im at himleaf
    change (w t) * (∫ x, (f x).im ∂(F.base.leaf t : Measure ℝ)) =
      ((w t) • inner t).im
    rw [himleaf]
    simp [inner, Complex.real_smul]

/-- Integrating the Cauchy kernel through a positive bounded boundary reweighting is exactly
integration of the leaf Cauchy transforms against that density.  This is the complex-valued
Fubini step underlying the carrier bridge. -/
theorem weightedBoundaryCarrier_cauchy_eq_parameterIntegral
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1)
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) :
    (∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
      ∫ t, (w t) •
        (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) ∂eta := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure
      (F.base.leaf t : Measure ℝ) := (F.base.leaf t).prop
  letI : IsProbabilityMeasure
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      F.base.toBoundaryFamily.measurable_leaf
      (fun t => (F.base.toBoundaryFamily.leaf t).prop)
  let inner : OnePoint ℝ → ℂ := fun t =>
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)
  have hinner : Continuous inner := F.continuous_leaf_cauchy z hz hc hq
  have hinnerLp : MemLp inner 1 eta :=
    hinner.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hparam : Integrable (fun t => (w t) • inner t) eta :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).integrable_of_bilin_of_bdd_left
      ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm eta w)
      (hinnerLp.integrable (by norm_num))
  have hcarrier : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹)
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) :=
    integrable_cauchyKernel_of_im_pos
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) z hz
  have hkernelContinuous : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) := by
    exact (continuous_ofReal.sub continuous_const).inv₀ (fun x hzero => by
      change (x : ℂ) - z = 0 at hzero
      have him := congrArg Complex.im hzero
      simp only [sub_im, ofReal_im, zero_im] at him
      linarith)
  apply Complex.ext
  · have hrecarrier := integral_re hcarrier
    change (∫ x, (((x : ℂ) - z)⁻¹).re
      ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
        (∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w).re at hrecarrier
    have hreparam := integral_re hparam
    change (∫ t, (((w t) • inner t)).re ∂eta) =
      (∫ t, (w t) • inner t ∂eta).re at hreparam
    rw [← hrecarrier, ← hreparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (((x : ℂ) - z)⁻¹).re)
      F.base.toBoundaryFamily.measurable_leaf
      (Complex.continuous_re.comp hkernelContinuous).measurable hcarrier.re]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have hleaf := integrable_cauchyKernel_of_im_pos
      (F.base.leaf t : Measure ℝ) z hz
    have hreleaf := integral_re hleaf
    change (∫ x, (((x : ℂ) - z)⁻¹).re ∂(F.base.leaf t : Measure ℝ)) =
      (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)).re at hreleaf
    change (w t) * (∫ x, (((x : ℂ) - z)⁻¹).re
      ∂(F.base.leaf t : Measure ℝ)) = ((w t) • inner t).re
    rw [hreleaf]
    simp [inner, Complex.real_smul]
  · have himcarrier := integral_im hcarrier
    change (∫ x, (((x : ℂ) - z)⁻¹).im
      ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
        (∫ x, ((x : ℂ) - z)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w).im at himcarrier
    have himparam := integral_im hparam
    change (∫ t, (((w t) • inner t)).im ∂eta) =
      (∫ t, (w t) • inner t ∂eta).im at himparam
    rw [← himcarrier, ← himparam]
    rw [weightedBoundaryCarrier, boundaryBarycenter, integral_bind_real
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      (fun x : ℝ => (((x : ℂ) - z)⁻¹).im)
      F.base.toBoundaryFamily.measurable_leaf
      (Complex.continuous_im.comp hkernelContinuous).measurable hcarrier.im]
    rw [linftyDensityMeasure]
    have hmeas : AEMeasurable (fun t => ENNReal.ofReal (w t)) eta :=
      (Lp.memLp w).1.aemeasurable.ennreal_ofReal
    rw [integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [hw] with t ht
    rw [ENNReal.toReal_ofReal ht.le]
    have hleaf := integrable_cauchyKernel_of_im_pos
      (F.base.leaf t : Measure ℝ) z hz
    have himleaf := integral_im hleaf
    change (∫ x, (((x : ℂ) - z)⁻¹).im ∂(F.base.leaf t : Measure ℝ)) =
      (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)).im at himleaf
    change (w t) * (∫ x, (((x : ℂ) - z)⁻¹).im
      ∂(F.base.leaf t : Measure ℝ)) = ((w t) • inner t).im
    rw [himleaf]
    simp [inner, Complex.real_smul]

/-- **All-order actual-carrier jet identity.**  Every derivative of the Cauchy transform of a
positive normalized weighted carrier is the background derivative plus the exact smooth forward
projective control coordinate used by the compact-patch transversality theorem. -/
theorem iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_background_add_control
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1)
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) (n : ℕ) :
    iteratedDeriv n
        (fun u => ∫ x, ((x : ℂ) - u)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) z =
      iteratedDeriv n F.background z +
        (projectiveNevanlinnaJetExpansionSmoothControl
          F.amplitude F.quotient (fun _ : Unit => n + 1) eta (fun _ : Unit => z) w)
          ⟨(), ⟨n, Nat.lt_succ_self n⟩⟩ := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta w) :=
    linftyDensityMeasure_isProbabilityMeasure eta w hw hint
  letI (t : OnePoint ℝ) : IsProbabilityMeasure
      (F.base.leaf t : Measure ℝ) := (F.base.leaf t).prop
  letI : IsProbabilityMeasure
      (weightedBoundaryCarrier F.base.toBoundaryFamily eta w) := by
    dsimp only [weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure eta w)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      F.base.toBoundaryFamily.measurable_leaf
      (fun t => (F.base.toBoundaryFamily.leaf t).prop)
  let muw : Measure ℝ := weightedBoundaryCarrier F.base.toBoundaryFamily eta w
  have hzsupport : z ∉ algebraMap ℝ ℂ '' muw.support := by
    rintro ⟨x, _hx, hzx⟩
    have him := congrArg Complex.im hzx
    change ((x : ℂ)).im = z.im at him
    simp only [ofReal_im] at him
    linarith
  have hactual := iteratedDeriv_resolventTransform n z hzsupport
  rw [resolventTransform_def] at hactual
  have hactual' : iteratedDeriv n
      (fun u => ∫ x, ((x : ℂ) - u)⁻¹ ∂muw) z =
      cauchyJetFunction muw n z := by
    simpa [resolvent] using hactual
  change iteratedDeriv n
      (fun u => ∫ x, ((x : ℂ) - u)⁻¹ ∂muw) z = _
  rw [hactual']
  let f : ℝ → ℂ := fun x => (n.factorial : ℂ) * (((x : ℂ) - z)⁻¹) ^ (n + 1)
  have hf : Continuous f := by
    apply Continuous.const_mul
    exact ((continuous_ofReal.sub continuous_const).inv₀ (fun x hzero => by
      change (x : ℂ) - z = 0 at hzero
      have him := congrArg Complex.im hzero
      simp only [sub_im, ofReal_im, zero_im] at him
      linarith)).pow (n + 1)
  have hfcarrier : Integrable f muw :=
    (integrable_cauchyKernel_pow_of_im_pos muw z hz (n + 1)).const_mul
      (n.factorial : ℂ)
  have hfleaves : ∀ t, Integrable f (F.base.leaf t : Measure ℝ) := by
    intro t
    exact (integrable_cauchyKernel_pow_of_im_pos
      (F.base.leaf t : Measure ℝ) z hz (n + 1)).const_mul (n.factorial : ℂ)
  let eta0 : ℝ := (F.quotient z).im / 2
  have heta0 : 0 < eta0 := by dsimp [eta0]; linarith
  let zu : Unit → NevanlinnaUpperNodeAtLeast F.quotient eta0 := fun _ =>
    ⟨z, by dsimp [eta0]; linarith⟩
  let coord : (Σ _ : Unit, Fin (n + 1)) :=
    ⟨(), ⟨n, Nat.lt_succ_self n⟩⟩
  let column : OnePoint ℝ → ℂ := fun t =>
    projectiveNevanlinnaJetExpansionColumn
      F.amplitude F.quotient (fun _ : Unit => z) (fun _ : Unit => n + 1) t coord
  have hcolumn : Continuous column := by
    exact (continuous_apply coord).comp
      (continuous_projectiveNevanlinnaJetExpansionColumn
        (a := F.amplitude) (q := F.quotient) eta0 heta0
        (fun _ : Unit => n + 1) zu)
  have hleafIntegral (t : OnePoint ℝ) :
      (∫ x, f x ∂(F.base.leaf t : Measure ℝ)) =
        iteratedDeriv n F.background z + column t := by
    calc
      (∫ x, f x ∂(F.base.leaf t : Measure ℝ)) =
          cauchyJetFunction (F.base.leaf t : Measure ℝ) n z := by
        rw [cauchyJetFunction, resolventPowerTransform, integral_const_mul]
        simp only [resolvent, Ring.inverse_eq_inv, Complex.coe_algebraMap]
      _ = iteratedDeriv n
          (fun u => ∫ x, ((x : ℂ) - u)⁻¹
            ∂(F.base.leaf t : Measure ℝ)) z := by
        symm
        have hleafActual := iteratedDeriv_resolventTransform
          (μ := (F.base.leaf t : Measure ℝ)) n z (by
            rintro ⟨x, _hx, hzx⟩
            have him := congrArg Complex.im hzx
            change ((x : ℂ)).im = z.im at him
            simp only [ofReal_im] at him
            linarith)
        rw [resolventTransform_def] at hleafActual
        simpa [resolvent] using hleafActual
      _ = iteratedDeriv n F.background z + column t := by
        exact F.iteratedDeriv_leafCauchy_eq_background_add_expansion
          t z hz hc hq n
  have hinner : Continuous (fun t : OnePoint ℝ =>
      ∫ x, f x ∂(F.base.leaf t : Measure ℝ)) := by
    apply (continuous_const.add hcolumn).congr
    intro t
    exact (hleafIntegral t).symm
  have hFubini := F.weightedBoundaryCarrier_integral_eq_parameterIntegral
    eta w hw f hf hfcarrier hfleaves hinner
  change (n.factorial : ℂ) * resolventPowerTransform muw (n + 1) z = _
  rw [resolventPowerTransform, ← integral_const_mul]
  simp only [resolvent, Ring.inverse_eq_inv, Complex.coe_algebraMap]
  change (∫ x, f x ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) = _
  rw [hFubini]
  have hwInt : Integrable (fun t => w t) eta :=
    (Lp.memLp w).integrable (by simp)
  have hbgInt : Integrable (fun t => (w t) • iteratedDeriv n F.background z) eta :=
    hwInt.smul_const (iteratedDeriv n F.background z)
  have hcolumnLp : MemLp column 1 eta :=
    hcolumn.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcolumnInt : Integrable (fun t => (w t) • column t) eta :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).integrable_of_bilin_of_bdd_left
      ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm eta w)
      (hcolumnLp.integrable (by norm_num))
  calc
    (∫ t, (w t) • (∫ x, f x ∂(F.base.leaf t : Measure ℝ)) ∂eta) =
        ∫ t, (w t) • (iteratedDeriv n F.background z + column t) ∂eta := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [hleafIntegral]
    _ = ∫ t, ((w t) • iteratedDeriv n F.background z) +
        ((w t) • column t) ∂eta := by
      congr 1
      funext t
      exact smul_add (w t) (iteratedDeriv n F.background z) (column t)
    _ = (∫ t, (w t) • iteratedDeriv n F.background z ∂eta) +
        ∫ t, (w t) • column t ∂eta := integral_add hbgInt hcolumnInt
    _ = iteratedDeriv n F.background z + ∫ t, (w t) • column t ∂eta := by
      rw [integral_smul_const, hint, one_smul]
    _ = _ := by
      have hcontrol := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
        F.amplitude F.quotient (fun _ : Unit => n + 1) eta eta0 heta0 zu
      rw [hcontrol, linftyBochnerControl_apply_pi]

/-- **Cauchy-frozen packets kill the forward Nevanlinna variation.**  If a perturbation fixes
total mass and a finite packet of projective Cauchy powers, then its complete forward genuine
Nevanlinna jet packet vanishes.  This holds even when the Nevanlinna coordinate is critical at a
frozen source node. -/
theorem projectiveNevanlinnaJetExpansionSmoothControl_eq_zero_of_cauchyFrozenTangent
    {ι : Type} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (hupper : ∀ i, 0 < (q (z i)).im)
    (w : LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        (fun i => q (z i)) n eta hupper).toLinearMap) :
    projectiveNevanlinnaJetExpansionSmoothControl a q n eta z w.1 = 0 := by
  obtain ⟨η0, hη0, hη0all⟩ := compact_finite_strictPositive_uniformLowerBound
    ({()} : Set Unit) isCompact_singleton
    (fun (_ : Unit) i => (q (z i)).im)
    (fun _ => continuousOn_const) (by
      intro _ _ i
      exact hupper i)
  let zu : ι → NevanlinnaUpperNodeAtLeast q η0 := fun i =>
    ⟨z i, hη0all () (Set.mem_singleton ()) i⟩
  have hsmooth := projectiveNevanlinnaJetExpansionSmoothControl_eq_existing
    a q n eta η0 hη0 zu
  have hfactor :=
    projectiveNevanlinnaJetExpansionLinftyControl_eq_forwardCLM_comp_cauchyControl
      a q η0 hη0 n eta zu
  have hwzero : normalizedProjectiveCauchyJetLinftyContinuousControl
      (fun i => q (z i)) n eta hupper w.1 = 0 :=
    LinearMap.mem_ker.mp w.2
  have hcauchy : linftyBochnerControl eta
      (projectiveCauchyJetColumn (fun i => q (z i)) n)
      (memLp_projectiveCauchyJetColumn (fun i => q (z i))
        (fun i => (hupper i).ne') n eta) w.1 = 0 := by
    exact congrArg Prod.snd hwzero
  rw [hsmooth, hfactor, ContinuousLinearMap.comp_apply, hcauchy, map_zero]

/-- **Finite-frame preservation without frozen noncriticality.**  Translating a positive
probability density by a Cauchy-frozen tangent leaves every actual carrier derivative in the
frozen packet unchanged.  The conclusion concerns the literal Cauchy transform of the weighted
carrier, while the hypotheses impose no amplitude or `q'` condition at the frozen nodes. -/
theorem iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_base_of_cauchyFrozenTangent
    {ι : Type} [Fintype ι]
    (zf : ι → ℂ) (nf : ι → ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (hupperf : ∀ i, 0 < (F.quotient (zf i)).im)
    (baseDensity : Lp ℝ (⊤ : ENNReal) eta)
    (hbasePositive : LinftyStrictlyPositive eta baseDensity)
    (hbaseIntegral : ∫ t, baseDensity t ∂eta = 1)
    (w : LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        (fun i => F.quotient (zf i)) nf eta hupperf).toLinearMap)
    (hpositive : LinftyStrictlyPositive eta (baseDensity + w.1))
    (hintegral : ∫ t, (baseDensity + w.1) t ∂eta = 1)
    (i : ι) (j : Fin (nf i))
    (hz : 0 < (zf i).im) (hc : F.c (zf i) ≠ 0) :
    iteratedDeriv j.1
        (fun u => ∫ x, ((x : ℂ) - u)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta
            (baseDensity + w.1)) (zf i) =
      iteratedDeriv j.1
        (fun u => ∫ x, ((x : ℂ) - u)⁻¹
          ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta baseDensity) (zf i) := by
  obtain ⟨η0, hη0, hη0all⟩ := compact_finite_strictPositive_uniformLowerBound
    ({()} : Set Unit) isCompact_singleton
    (fun (_ : Unit) k => (F.quotient (zf k)).im)
    (fun _ => continuousOn_const) (by
      intro _ _ k
      exact hupperf k)
  have hpacketZero :=
    projectiveNevanlinnaJetExpansionSmoothControl_eq_zero_of_cauchyFrozenTangent
      F.amplitude F.quotient zf nf eta hupperf w
  have hsingletonZero :
      (projectiveNevanlinnaJetExpansionSmoothControl
        F.amplitude F.quotient (fun _ : Unit => j.1 + 1)
        eta (fun _ : Unit => zf i) w.1) ⟨(), Fin.last j.1⟩ = 0 := by
    rw [← projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton_last
      F.amplitude F.quotient nf eta η0 hη0 zf
      (fun k => hη0all () (Set.mem_singleton ()) k) w.1 i j]
    exact congrFun hpacketZero ⟨i, j⟩
  have hpert := F.iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_background_add_control
    eta (baseDensity + w.1) hpositive hintegral (zf i) hz hc (hupperf i) j.1
  have hbase := F.iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_background_add_control
    eta baseDensity hbasePositive hbaseIntegral (zf i) hz hc (hupperf i) j.1
  have hcontrolAdd :
      (projectiveNevanlinnaJetExpansionSmoothControl
        F.amplitude F.quotient (fun _ : Unit => j.1 + 1)
        eta (fun _ : Unit => zf i) (baseDensity + w.1))
          ⟨(), ⟨j.1, Nat.lt_succ_self j.1⟩⟩ =
      (projectiveNevanlinnaJetExpansionSmoothControl
        F.amplitude F.quotient (fun _ : Unit => j.1 + 1)
        eta (fun _ : Unit => zf i) baseDensity)
          ⟨(), ⟨j.1, Nat.lt_succ_self j.1⟩⟩ := by
    rw [map_add]
    change _ +
      (projectiveNevanlinnaJetExpansionSmoothControl
        F.amplitude F.quotient (fun _ : Unit => j.1 + 1)
        eta (fun _ : Unit => zf i) w.1) ⟨(), Fin.last j.1⟩ = _
    rw [hsingletonZero, add_zero]
  rw [hcontrolAdd] at hpert
  exact hpert.trans hbase.symm

/-- **Exact upper-node frozen-frame law.**  Freezing the first `N` projective Cauchy powers at
the upper source node `i` preserves the Cayley moments through level `N`, hence the complete
finite Toeplitz/Cholesky frame through that level.  Conjugation of real-measure Cauchy jets is what
connects the upper controllability chart to the conventional frame node `-i`. -/
theorem cayleyMoment_prefix_weightedBoundaryCarrier_eq_base_of_cauchyFrozenTangent_at_I
    (N : ℕ)
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (hupperI : 0 < (F.quotient I).im)
    (baseDensity : Lp ℝ (⊤ : ENNReal) eta)
    (hbasePositive : LinftyStrictlyPositive eta baseDensity)
    (hbaseIntegral : ∫ t, baseDensity t ∂eta = 1)
    (w : LinearMap.ker
      (normalizedProjectiveCauchyJetLinftyContinuousControl
        (fun _ : Unit => F.quotient I) (fun _ : Unit => N)
        eta (fun _ => hupperI)).toLinearMap)
    (hpositive : LinftyStrictlyPositive eta (baseDensity + w.1))
    (hintegral : ∫ t, (baseDensity + w.1) t ∂eta = 1) :
    ∀ k ≤ N,
      cayleyMoment
          (weightedBoundaryCarrier F.base.toBoundaryFamily eta
            (baseDensity + w.1)) k =
        cayleyMoment
          (weightedBoundaryCarrier F.base.toBoundaryFamily eta baseDensity) k := by
  letI : IsProbabilityMeasure (linftyDensityMeasure eta (baseDensity + w.1)) :=
    linftyDensityMeasure_isProbabilityMeasure eta (baseDensity + w.1) hpositive hintegral
  letI : IsProbabilityMeasure (linftyDensityMeasure eta baseDensity) :=
    linftyDensityMeasure_isProbabilityMeasure eta baseDensity hbasePositive hbaseIntegral
  let muPert : Measure ℝ :=
    weightedBoundaryCarrier F.base.toBoundaryFamily eta (baseDensity + w.1)
  let muBase : Measure ℝ :=
    weightedBoundaryCarrier F.base.toBoundaryFamily eta baseDensity
  letI : IsProbabilityMeasure muPert := by
    dsimp only [muPert, weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure eta (baseDensity + w.1))
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      F.base.toBoundaryFamily.measurable_leaf
      (fun t => (F.base.toBoundaryFamily.leaf t).prop)
  letI : IsProbabilityMeasure muBase := by
    dsimp only [muBase, weightedBoundaryCarrier]
    exact boundaryBarycenter_isProbabilityMeasure
      (linftyDensityMeasure eta baseDensity)
      (fun t => (F.base.toBoundaryFamily.leaf t : Measure ℝ))
      F.base.toBoundaryFamily.measurable_leaf
      (fun t => (F.base.toBoundaryFamily.leaf t).prop)
  rw [cayleyMoment_prefix_iff_cauchyJet_pos_I_prefix]
  intro n hn
  let j : Fin N := ⟨n, hn⟩
  have hcI : F.c I ≠ 0 := by
    intro hc
    have hqzero : F.quotient I = 0 := by simp [quotient, hc]
    rw [hqzero] at hupperI
    simp at hupperI
  have hjet :=
    F.iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_base_of_cauchyFrozenTangent
      (fun _ : Unit => I) (fun _ : Unit => N) eta (fun _ => hupperI)
      baseDensity hbasePositive hbaseIntegral w hpositive hintegral () j
      (by simp) hcI
  simpa [muPert, muBase, resolventTransform_def, resolvent] using hjet

/-- The simultaneous finite packet of actual Cauchy-transform derivatives of one weighted
Nevanlinna carrier. -/
def weightedBoundaryCarrierExpandedPacketValue
    {row ι : Type} [Fintype ι]
    (eta : Measure (OnePoint ℝ))
    (density : Lp ℝ (⊤ : ENNReal) eta) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι) :
    row × Fin (Fintype.card (Σ i, Fin (orders i))) → ℂ :=
  fun p =>
    let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
    iteratedDeriv s.2
      (fun u => ∫ x, ((x : ℂ) - u)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta density)
      (packet.1 p.1 + shift.1 s.1)

/-- **Literal analytic/transversality packet identity.**  In the positive normalized chart, the
abstract packet used by compact-patch transversality is exactly the packet of derivatives of the
Cauchy transform of the weighted singular-continuous carrier.  The proof is simultaneous over all
rows, shifts, and derivative orders. -/
theorem weightedBoundaryCarrierExpandedPacketValue_eq_actualNevanlinnaExpandedPacketValue
    {row ι : Type} [Fintype row] [Fintype ι]
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (baseDensity : Lp ℝ (⊤ : ENNReal) eta)
    (S : Submodule ℝ (Lp ℝ (⊤ : ENNReal) eta)) (w : S)
    (hw : LinftyStrictlyPositive eta (baseDensity + w.1))
    (hint : ∫ t, (baseDensity + w.1) t ∂eta = 1)
    (orders : ι → ℕ) (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι)
    (hupperMap : ∀ z, z.im < 0 → 0 < (F.quotient z).im)
    (hupper : ∀ x, 0 < (combinedProjectiveRowShiftPacket packet shift x).im) :
    F.weightedBoundaryCarrierExpandedPacketValue
        eta (baseDensity + w.1) orders packet shift =
      actualNevanlinnaExpandedPacketValue
        F.background F.amplitude F.quotient orders eta baseDensity S packet w shift := by
  classical
  let nodes : row × ι → ℂ := ambientCombinedProjectiveNodes packet shift.1
  have hnodeUpper : ∀ x, 0 < (nodes x).im := by
    intro x
    simpa [nodes, ambientCombinedProjectiveNodes, combinedProjectiveRowShiftPacket] using hupper x
  have hquotientUpper : ∀ x, 0 < (F.quotient (nodes x)).im := fun x =>
    hupperMap (nodes x) (hnodeUpper x)
  obtain ⟨η0, hη0, hη0nodes⟩ := compact_finite_strictPositive_uniformLowerBound
    ({()} : Set Unit) isCompact_singleton
    (fun (_ : Unit) (x : row × ι) => (F.quotient (nodes x)).im)
    (fun _ => continuousOn_const) (by
      intro _ _ x
      exact hquotientUpper x)
  have hη0all : ∀ x, η0 ≤ (F.quotient (nodes x)).im := fun x =>
    hη0nodes () (Set.mem_singleton ()) x
  funext p
  let s := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2
  let z : ℂ := nodes (p.1, s.1)
  have hz : 0 < z.im := hnodeUpper (p.1, s.1)
  have hq : 0 < (F.quotient z).im := hquotientUpper (p.1, s.1)
  have hc : F.c z ≠ 0 := by
    intro hcz
    have hqzero : F.quotient z = 0 := by simp [quotient, hcz]
    rw [hqzero] at hq
    simp at hq
  have hjet := F.iteratedDeriv_weightedBoundaryCarrier_cauchy_eq_background_add_control
    eta (baseDensity + w.1) hw hint z hz hc hq s.2
  have hcoord :=
    projectiveNevanlinnaJetExpansionSmoothControl_coordinate_eq_singleton_last
      F.amplitude F.quotient (fun x : row × ι => orders x.2)
      eta η0 hη0 nodes hη0all (baseDensity + w.1) (p.1, s.1) s.2
  change iteratedDeriv s.2
      (fun u => ∫ x, ((x : ℂ) - u)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta (baseDensity + w.1)) z =
    iteratedDeriv s.2 F.background z +
      (reshapeCombinedJetsFinCLM row ι orders
        (projectiveNevanlinnaJetExpansionSmoothControl
          F.amplitude F.quotient (fun x : row × ι => orders x.2)
          eta nodes (baseDensity + w.1))) p
  rw [hjet]
  congr 1
  symm
  simpa [reshapeCombinedJetsFinCLM, s, z] using! hcoord

/-- The centered order-zero projective Nevanlinna control at one analytic node. -/
def projectiveNevanlinnaValueLinftyControl
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (z : ℂ) (hq : (F.quotient z).im ≠ 0) :
    Lp ℝ (⊤ : ENNReal) eta →L[ℝ] ℂ :=
  let K : OnePoint ℝ → ℂ := fun t =>
    F.amplitude z * projectiveCauchyPower (F.quotient z) 0 t
  let hK : Continuous K :=
    continuous_const.mul (continuous_projectiveCauchyPower (F.quotient z) hq 0)
  linftyBochnerControl eta K
    (hK.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

@[simp]
theorem projectiveNevanlinnaValueLinftyControl_apply
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    (z : ℂ) (hq : (F.quotient z).im ≠ 0)
    (w : Lp ℝ (⊤ : ENNReal) eta) :
    F.projectiveNevanlinnaValueLinftyControl eta z hq w =
      ∫ t, (w t) •
        (F.amplitude z * projectiveCauchyPower (F.quotient z) 0 t) ∂eta := by
  rw [projectiveNevanlinnaValueLinftyControl, linftyBochnerControl_apply]

/-- **Actual weighted-carrier affine identity.**  On the upper projective chart, the Cauchy
transform of a positive normalized reweighted Nevanlinna carrier is the full background plus the
centered bounded-density control used by the transversality theorem. -/
theorem weightedBoundaryCarrier_cauchy_eq_background_add_control
    (eta : Measure (OnePoint ℝ)) [IsProbabilityMeasure eta]
    (w : Lp ℝ (⊤ : ENNReal) eta) (hw : LinftyStrictlyPositive eta w)
    (hint : ∫ t, w t ∂eta = 1)
    (z : ℂ) (hz : 0 < z.im) (hc : F.c z ≠ 0)
    (hq : 0 < (F.quotient z).im) :
    (∫ x, ((x : ℂ) - z)⁻¹
        ∂weightedBoundaryCarrier F.base.toBoundaryFamily eta w) =
      F.background z + F.projectiveNevanlinnaValueLinftyControl eta z hq.ne' w := by
  rw [F.weightedBoundaryCarrier_cauchy_eq_parameterIntegral eta w hw hint z hz hc hq]
  let K : OnePoint ℝ → ℂ := fun t =>
    F.amplitude z * projectiveCauchyPower (F.quotient z) 0 t
  have hK : Continuous K :=
    continuous_const.mul (continuous_projectiveCauchyPower (F.quotient z) hq.ne' 0)
  have hKlp : MemLp K 1 eta :=
    hK.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hwInt : Integrable (fun t => w t) eta :=
    (Lp.memLp w).integrable (by simp)
  have hbackgroundInt : Integrable (fun t => (w t) • F.background z) eta :=
    hwInt.smul_const (F.background z)
  have hcenteredInt : Integrable (fun t => (w t) • K t) eta :=
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).integrable_of_bilin_of_bdd_left
      ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm eta w)
      (hKlp.integrable (by norm_num))
  calc
    (∫ t, (w t) •
        (∫ x, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)) ∂eta) =
        ∫ t, (w t) • (F.background z + K t) ∂eta := by
          apply integral_congr_ae
          filter_upwards [] with t
          rw [F.leaf_cauchy_eq_background_add_projective t z hz hc hq]
    _ = ∫ t, ((w t) • F.background z) + ((w t) • K t) ∂eta := by
          congr 1
          funext t
          exact smul_add (w t) (F.background z) (K t)
    _ = (∫ t, (w t) • F.background z ∂eta) +
        ∫ t, (w t) • K t ∂eta := integral_add hbackgroundInt hcenteredInt
    _ = F.background z + ∫ t, (w t) • K t ∂eta := by
          rw [integral_smul_const, hint, one_smul]
    _ = F.background z + F.projectiveNevanlinnaValueLinftyControl eta z hq.ne' w := by
          rw [F.projectiveNevanlinnaValueLinftyControl_apply eta z hq.ne' w]

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
