import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniFourierTruncation
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniRapidMuntz
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniZetaCycles
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# The rough `L²` carrier for Connes--Consani `scalingact(iii)`

This file puts the literal bounded-variation periodization from `fouriertruncated1` in the same
circle `L²` space as the Meyer source.  It also proves strong continuity of circle translation on
every `L²` vector.  These are the two analytic closure inputs of `scalingact(iii)`; the remaining
source-specific theorem is the literal Meyer landing of multiplicative mollification.
-/

open Complex Filter MeasureTheory Set Topology
open scoped ENNReal FourierTransform
open GaloisForLFunctions GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Complex-valued rough quotient function, on the exact circle used by the zeta-cycle source. -/
def ccmFourierTruncatedQuotientComplex
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    AddCircle (L : ℝ) → ℂ :=
  fun x => (ccmFourierTruncatedQuotient f (L : ℝ) L.property x : ℂ)

theorem measurable_ccmFourierTruncatedQuotientComplex
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    Measurable (ccmFourierTruncatedQuotientComplex f L) :=
  Complex.measurable_ofReal.comp
    (measurable_ccmFourierTruncatedQuotient f L.property)

theorem memLp_ccmFourierTruncatedQuotientComplex
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    MemLp (ccmFourierTruncatedQuotientComplex f L) 2 AddCircle.haarAddCircle := by
  obtain ⟨D, hD, -, hbound⟩ := connesConsani_fouriertruncated1 f L.property |>.2.2
  apply MemLp.of_bound
    (measurable_ccmFourierTruncatedQuotientComplex f L).aestronglyMeasurable D
  exact Eventually.of_forall fun x => by
    rw [ccmFourierTruncatedQuotientComplex, Complex.norm_real, Real.norm_eq_abs]
    exact hbound x

/-- Literal rough periodization as an `L²` vector. -/
def ccmFourierTruncatedQuotientL2
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) :=
  (memLp_ccmFourierTruncatedQuotientComplex f L).toLp
    (ccmFourierTruncatedQuotientComplex f L)

theorem ccmFourierTruncatedQuotientL2_coeFn
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    (ccmFourierTruncatedQuotientL2 f L : AddCircle (L : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle]
        ccmFourierTruncatedQuotientComplex f L :=
  MemLp.coeFn_toLp (memLp_ccmFourierTruncatedQuotientComplex f L)

/-- The complex rough quotient is exactly the `Ioc` lift of the complexified real-line
periodization. -/
theorem ccmFourierTruncatedQuotientComplex_eq_liftIoc
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    ccmFourierTruncatedQuotientComplex f L =
      AddCircle.liftIoc (L : ℝ) 0
        (fun t => (ccmFourierTruncatedPeriodization f (L : ℝ) t : ℂ)) := by
  funext x
  rfl

/-- Exact Fourier coordinates of the rough `L²` quotient. -/
theorem fourierBasis_repr_ccmFourierTruncatedQuotientL2
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) (m : ℤ) :
    fourierBasis.repr (ccmFourierTruncatedQuotientL2 f L) m =
      (1 / (L : ℝ)) •
        𝓕 (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ))
          ((1 / (L : ℝ)) * (m : ℝ)) := by
  rw [fourierBasis_repr]
  rw [congrFun (fourierCoeff_congr_ae
    (ccmFourierTruncatedQuotientL2_coeFn f L)) m]
  rw [ccmFourierTruncatedQuotientComplex_eq_liftIoc, fourierCoeff_liftIoc_eq]
  simpa using fourierCoeffOn_ccmFourierTruncatedPeriodization f L.property m

/-- Translation by a varying circle parameter as a continuous map of the circle. -/
def ccmZetaCircleTranslateCM (L : CCMZetaCircleLength)
    (a : AddCircle (L : ℝ)) : C(AddCircle (L : ℝ), AddCircle (L : ℝ)) :=
  ⟨fun x => x + a, continuous_id.add continuous_const⟩

theorem continuous_ccmZetaCircleTranslateCM (L : CCMZetaCircleLength) :
    Continuous (ccmZetaCircleTranslateCM L) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_snd.add continuous_fst

theorem measurePreserving_ccmZetaCircleTranslateCM
    (L : CCMZetaCircleLength) (a : AddCircle (L : ℝ)) :
    MeasurePreserving (ccmZetaCircleTranslateCM L a)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  ccmZetaCircleMeasurePreservingTranslate L a

/-- Strong continuity of the exact translation representation on every circle `L²` vector. -/
theorem continuous_ccmZetaCircleTransOp_orbit
    (L : CCMZetaCircleLength)
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    Continuous fun a : AddCircle (L : ℝ) => ccmZetaCircleTransOp L a u := by
  let F : AddCircle (L : ℝ) →
      Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)) := fun _ => u
  have hF : Continuous F := continuous_const
  have h := hF.compMeasurePreservingLp
    (continuous_ccmZetaCircleTranslateCM L)
    (measurePreserving_ccmZetaCircleTranslateCM L)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have heq : (fun a : AddCircle (L : ℝ) => ccmZetaCircleTransOp L a u) =
      fun a => Lp.compMeasurePreserving (ccmZetaCircleTranslateCM L a)
        (measurePreserving_ccmZetaCircleTranslateCM L a) u := by
    funext a
    rfl
  rw [heq]
  exact h

/-- In particular, translations of the rough CCM quotient converge strongly back to it. -/
theorem tendsto_ccmFourierTruncatedQuotientL2_translate_zero
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    Tendsto
      (fun a : AddCircle (L : ℝ) =>
        ccmZetaCircleTransOp L a (ccmFourierTruncatedQuotientL2 f L))
      (𝓝 0) (𝓝 (ccmFourierTruncatedQuotientL2 f L)) := by
  have hzero : Tendsto
      (fun a : AddCircle (L : ℝ) =>
        ccmZetaCircleTransOp L a (ccmFourierTruncatedQuotientL2 f L))
      (𝓝 (0 : AddCircle (L : ℝ)))
      (𝓝 (ccmZetaCircleTransOp L 0 (ccmFourierTruncatedQuotientL2 f L))) :=
    (continuous_ccmZetaCircleTransOp_orbit L
      (ccmFourierTruncatedQuotientL2 f L)).continuousAt
  have hopzero : ccmZetaCircleTransOp L 0
      (ccmFourierTruncatedQuotientL2 f L) =
        ccmFourierTruncatedQuotientL2 f L := by
    refine Lp.ext ?_
    have hcomp := ccmZetaCircleTransOp_coeFn L 0
      (ccmFourierTruncatedQuotientL2 f L)
    have hbase : (fun x => (ccmFourierTruncatedQuotientL2 f L) x)
        =ᵐ[AddCircle.haarAddCircle]
          fun x => (ccmFourierTruncatedQuotientL2 f L) x := EventuallyEq.rfl
    filter_upwards [hcomp, hbase] with x hx _
    simpa using hx
  rwa [hopzero] at hzero

/-! ## Exact Fourier classification of the closed CCM source -/

/-- The closed Connes--Consani source consists exactly of the circle vectors whose Fourier
coefficients vanish at every sampled critical-line zero of zeta.  This is a simultaneous,
whole-space strengthening of the paper's character-by-character `spectralreal` statement. -/
theorem mem_ccmZetaCycleSourceSubmodule_iff
    (L : CCMZetaCircleLength)
    (u : Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance))) :
    u ∈ ccmZetaCycleSourceSubmodule L ↔
      ∀ m : ℤ, riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 →
        fourierBasis.repr u m = 0 := by
  constructor
  · intro hu m hz
    have hm : fourierLp 2 m ∈ ccmZetaCycleCohomology L :=
      (fourierLp_mem_ccmZetaCycleCohomology_iff_zeta_zero L m).2 hz
    have hinner : inner ℂ u (fourierLp 2 m) = 0 := hm u hu
    have hswap : inner ℂ (fourierLp 2 m) u = 0 := by
      rw [← inner_conj_symm, hinner]
      simp
    calc
      fourierBasis.repr u m = inner ℂ (fourierBasis m) u :=
        HilbertBasis.repr_apply_apply fourierBasis u m
      _ = inner ℂ (fourierLp 2 m) u := by rw [coe_fourierBasis]
      _ = 0 := hswap
  · intro hcoeff
    let S := ccmZetaCycleSourceSubmodule L
    have hdouble : u ∈ Sᗮᗮ := by
      rw [Submodule.mem_orthogonal]
      intro v hv
      rw [← fourierBasis.tsum_inner_mul_inner v u]
      calc
        (∑' m : ℤ, inner ℂ v (fourierBasis m) * inner ℂ (fourierBasis m) u) =
            ∑' _m : ℤ, (0 : ℂ) := by
          apply tsum_congr
          intro m
          by_cases hz : riemannZeta (ccmZetaCircleCriticalPoint L m) = 0
          · have hu0 : inner ℂ (fourierBasis m) u = 0 := by
              rw [← HilbertBasis.repr_apply_apply]
              exact hcoeff m hz
            rw [hu0, mul_zero]
          · have hb : fourierLp 2 m ∈ S :=
              fourierLp_mem_ccmZetaCycleSourceSubmodule_of_zeta_ne_zero L m hz
            have hv0 : inner ℂ (fourierLp 2 m) v = 0 :=
              hv (fourierLp 2 m) hb
            have hv0' : inner ℂ v (fourierBasis m) = 0 := by
              rw [coe_fourierBasis]
              calc
                inner ℂ v (fourierLp 2 m) =
                    starRingEnd ℂ (inner ℂ (fourierLp 2 m) v) :=
                  (inner_conj_symm (𝕜 := ℂ) v (fourierLp 2 m)).symm
                _ = 0 := by rw [hv0]; simp
            rw [hv0', zero_mul]
        _ = 0 := by simp
    have hclosed : IsClosed (S : Set
        (Lp ℂ 2 (@AddCircle.haarAddCircle (L : ℝ) (inferInstance)))) :=
      (Submodule.span ℂ (Set.range (ccmZetaCycleTraceL2 L))).isClosed_topologicalClosure
    have hclosure : S.topologicalClosure = S :=
      hclosed.submodule_topologicalClosure_eq
    have hmemClosure : u ∈ S.topologicalClosure := by
      rw [← Submodule.orthogonal_orthogonal_eq_closure]
      exact hdouble
    rw [hclosure] at hmemClosure
    exact hmemClosure

/-- **Exact spectral form of the `scalingact(iii)` gate.**  The literal BV periodization belongs
to the closed Meyer source exactly when the Fourier transform of its logarithmic boundary
vanishes at every lattice frequency whose associated critical-line zeta sample vanishes.  Thus
the source-landing problem has no residual quotient-space ambiguity. -/
theorem ccmFourierTruncatedQuotientL2_mem_source_iff_fourier_zero
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    ccmFourierTruncatedQuotientL2 f L ∈ ccmZetaCycleSourceSubmodule L ↔
      ∀ m : ℤ, riemannZeta (ccmZetaCircleCriticalPoint L m) = 0 →
        𝓕 (fun t => (ccmFourierTruncatedLogBoundary f t : ℂ))
          ((1 / (L : ℝ)) * (m : ℝ)) = 0 := by
  rw [mem_ccmZetaCycleSourceSubmodule_iff]
  constructor
  · intro h m hz
    have hm := h m hz
    rw [fourierBasis_repr_ccmFourierTruncatedQuotientL2] at hm
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt L.property
    have hscalar : (1 / (L : ℝ)) ≠ 0 := one_div_ne_zero hLne
    exact (smul_eq_zero.mp hm).resolve_left hscalar
  · intro h m hz
    rw [fourierBasis_repr_ccmFourierTruncatedQuotientL2, h m hz, smul_zero]

/-- **Connes--Consani `scalingact(iii)`, strengthened.**  Every literal bounded-variation input
from `fouriertruncated1` lands in the closed Meyer source.  The paper's additional hypothesis that
the input coincide near zero with a smooth even function is unnecessary for the closure
conclusion: rapid BV Muntz continuation annihilates exactly the Fourier coordinates selected by
the source classifier. -/
theorem connesConsani_scalingact_iii
    (f : CCMFourierTruncatedInput) (L : CCMZetaCircleLength) :
    ccmFourierTruncatedQuotientL2 f L ∈ ccmZetaCycleSourceSubmodule L := by
  rw [ccmFourierTruncatedQuotientL2_mem_source_iff_fourier_zero]
  intro m hz
  apply fourier_ccmFourierTruncatedLogBoundary_eq_zero_of_zeta_zero
  have hp :
      ((1 / 2 : ℂ) -
          ((2 * Real.pi * ((1 / (L : ℝ)) * (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
        ccmZetaCircleCriticalPoint L m := by
    rw [ccmZetaCircleCriticalPoint]
    push_cast
    congr 2
    field_simp
  rw [hp]
  exact hz

end

end RHTower
