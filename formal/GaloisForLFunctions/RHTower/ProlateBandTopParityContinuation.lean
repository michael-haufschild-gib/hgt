import GaloisForLFunctions.RHTower.ProlateSmallApertureRankOne
import GaloisForLFunctions.RHTower.ProlateFourierBandEigen
import GaloisForLFunctions.RHTower.ConstrainedProlateSpectralIdentification
import GaloisForLFunctions.RHTower.BandEvenTrialCarrier
import GaloisForLFunctions.RHTower.BandOperatorContraction
import GaloisForLFunctions.RHTower.BandStrictGap
import GaloisForLFunctions.RHTower.ProlateBandOperatorInjective
import GaloisForLFunctions.HTGeometry.ContinuousSquareIntegralPositive
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Global prolate top-line parity and signed-mode-zero identification

Propagates the small-aperture even/odd spectral separation to every positive band parameter,
constructs a smooth even joint eigenprofile on the global leading line, and identifies that line
with signed physical Fourier mode zero through an exact reverse scaling bridge.
-/

noncomputable section

open MeasureTheory Set
attribute [local instance] Measure.Subtype.measureSpace

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A nonzero compact symmetric positive operator on a real Hilbert space attains its operator
norm as a positive eigenvalue. -/
theorem exists_unit_eigenvector_norm_real {S : H →L[ℝ] H} (hcpt : IsCompactOperator S)
    (hsym : S.IsSymmetric) (hpos : ∀ x : H, 0 ≤ (inner ℝ x (S x) : ℝ)) (hS : S ≠ 0) :
    ∃ x : H, ‖x‖ = 1 ∧ S x = ‖S‖ • x := by
  haveI : Nontrivial (H →L[ℝ] H) := ⟨S, 0, hS⟩
  have hspectrum : (spectrum ℝ S).Nonempty := by
    have hex : ∃ k : ℝ, Module.End.HasEigenvalue (↑S : Module.End ℝ H) k ∧ k ≠ 0 := by
      by_contra h
      push Not at h
      have hall : ∀ k : ℝ, Module.End.HasEigenvalue (↑S : Module.End ℝ H) k → k = 0 := by
        intro k hk
        exact h k hk
      exact hS ((ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero hcpt hsym).mp hall)
    obtain ⟨k, hk, hk0⟩ := hex
    exact ⟨k, (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hk0).mp hk⟩
  obtain ⟨k, hk_mem, hk_norm⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty hspectrum
  rw [S.spectralRadius_eq_nnnorm hsym.isSelfAdjoint] at hk_norm
  have hk_norm' : ‖k‖ = ‖S‖ := by
    have h2 : ‖k‖₊ = ‖S‖₊ := ENNReal.coe_inj.mp hk_norm
    exact congrArg NNReal.toReal h2
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, norm_zero] at hk_norm'
    exact hS (by rwa [eq_comm, norm_eq_zero] at hk_norm')
  have heig : Module.End.HasEigenvalue (↑S : Module.End ℝ H) k :=
    (IsCompactOperator.hasEigenvalue_iff_mem_spectrum hcpt hk0).mpr hk_mem
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have happ : S v = k • v := hv.apply_eq_smul
  have hk_nonneg : 0 ≤ k := by
    have hp := hpos v
    rw [happ, inner_smul_right] at hp
    have hi : (inner ℝ v v : ℝ) = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    rw [hi] at hp
    have hvp : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv0)
    nlinarith
  have hk : k = ‖S‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg hk_nonneg] at hk_norm'
    exact hk_norm'
  refine ⟨‖v‖⁻¹ • v, norm_smul_inv_norm hv0, ?_⟩
  rw [map_smul, happ, hk, smul_comm]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- At greedy stage zero there is no orthogonality constraint, so the constrained operator norm
is the ordinary operator norm. -/
theorem orthSup_zero_eq_opNorm_complex (S : K →L[ℂ] K) (v : ℕ → K) :
    orthSup S v 0 = ‖S‖ := by
  apply le_antisymm (orthSup_le_opNorm S v 0)
  apply ContinuousLinearMap.opNorm_le_bound S (orthSup_nonneg S v 0)
  intro x
  by_cases hx : x = 0
  · subst x
    simp
  · have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let y : K := ((‖x‖⁻¹ : ℝ) : ℂ) • x
    have hynorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ hxpos.ne']
    have hy := le_orthSup S v 0 hynorm.le (fun _ hm => by omega)
    dsimp only [y] at hy
    rw [map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos), inv_mul_eq_div] at hy
    exact (div_le_iff₀ hxpos).mp hy

theorem svVal_zero_eq_opNorm_complex (S : K →L[ℂ] K) :
    svVal S 0 = ‖S‖ :=
  orthSup_zero_eq_opNorm_complex S (svVec S)

theorem abs_sgVal_zero_eq_opNorm_complex [CompleteSpace K]
    {S : K →L[ℂ] K} (hcpt : IsCompactOperator S) (hsym : S.IsSymmetric) :
    |sgVal S 0| = ‖S‖ := by
  rw [abs_sgVal hcpt hsym]
  exact orthSup_zero_eq_opNorm_complex S (sgVec S)

end ContinuousLinearMap

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

def unitIntervalNeg : ClosedInterval (-1 : ℝ) 1 → ClosedInterval (-1 : ℝ) 1 :=
  fun x => ⟨-(x : ℝ), by constructor <;> linarith [x.2.1, x.2.2]⟩

theorem unitIntervalNeg_continuous : Continuous unitIntervalNeg := by
  exact continuous_subtype_val.neg.subtype_mk _

theorem unitIntervalNeg_involutive (x : ClosedInterval (-1 : ℝ) 1) :
    unitIntervalNeg (unitIntervalNeg x) = x := by
  apply Subtype.ext
  simp [unitIntervalNeg]

def unitIntervalNegMeasurableEquiv :
    ClosedInterval (-1 : ℝ) 1 ≃ᵐ ClosedInterval (-1 : ℝ) 1 where
  toEquiv :=
    { toFun := unitIntervalNeg
      invFun := unitIntervalNeg
      left_inv := unitIntervalNeg_involutive
      right_inv := unitIntervalNeg_involutive }
  measurable_toFun := unitIntervalNeg_continuous.measurable
  measurable_invFun := unitIntervalNeg_continuous.measurable

@[simp] theorem unitIntervalNegMeasurableEquiv_apply
    (x : ClosedInterval (-1 : ℝ) 1) :
    unitIntervalNegMeasurableEquiv x = unitIntervalNeg x := rfl

theorem unitIntervalNeg_preimage_Icc :
    (fun x : ℝ => -x) ⁻¹' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem measurePreserving_unitIntervalNeg :
    MeasurePreserving unitIntervalNeg
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) volume := by
  refine ⟨unitIntervalNeg_continuous.measurable, ?_⟩
  apply (MeasurableEmbedding.subtype_coe measurableSet_Icc).map_injective
  rw [Measure.map_map measurable_subtype_coe unitIntervalNeg_continuous.measurable]
  have hfun : (Subtype.val ∘ unitIntervalNeg) =
      (fun x : ℝ => -x) ∘ (Subtype.val : ClosedInterval (-1 : ℝ) 1 → ℝ) := by
    funext x
    rfl
  rw [hfun, ← Measure.map_map (Measure.measurePreserving_neg
    (volume : Measure ℝ)).measurable measurable_subtype_coe]
  rw [MeasurableSet.map_coe_volume measurableSet_Icc]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (s := Icc (-1 : ℝ) 1) measurableSet_Icc
  rw [unitIntervalNeg_preimage_Icc] at h
  exact h.map_eq

theorem measurePreserving_unitIntervalNegMeasurableEquiv :
    MeasurePreserving unitIntervalNegMeasurableEquiv
      (volume : Measure (ClosedInterval (-1 : ℝ) 1)) volume :=
  measurePreserving_unitIntervalNeg

def unitBandReflectionIsometry :
    RealIntervalL2 (-1 : ℝ) 1 →ₗᵢ[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  Lp.compMeasurePreservingₗᵢ ℝ unitIntervalNeg measurePreserving_unitIntervalNeg

def unitBandReflection :
    RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  unitBandReflectionIsometry.toContinuousLinearMap

theorem unitBandReflection_ae (f : RealIntervalL2 (-1 : ℝ) 1) :
    (unitBandReflection f : ClosedInterval (-1 : ℝ) 1 → ℝ) =ᵐ[volume]
      fun x => f (unitIntervalNeg x) :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_unitIntervalNeg

@[simp] theorem unitBandReflection_involutive (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandReflection (unitBandReflection f) = f := by
  apply Lp.ext
  have hinner := (unitBandReflection_ae f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [unitBandReflection_ae (unitBandReflection f), hinner] with x hout hin
  rw [hout]
  simpa [Function.comp_apply, unitIntervalNeg_involutive] using hin

@[simp] theorem norm_unitBandReflection (f : RealIntervalL2 (-1 : ℝ) 1) :
    ‖unitBandReflection f‖ = ‖f‖ :=
  unitBandReflectionIsometry.norm_map f

theorem sincKernelSmooth_neg_left_eq_neg_right (c x y : ℝ) :
    sincKernelSmooth c (-x) y = sincKernelSmooth c x (-y) := by
  unfold sincKernelSmooth
  rw [show -x - y = -(x - -y) by ring, RHTower.sincSmooth_even]

theorem bandOperatorL2_unitBandReflection (c : ℝ)
    (f : RealIntervalL2 (-1 : ℝ) 1) :
    bandOperatorL2 c (unitBandReflection f) = unitBandReflection (bandOperatorL2 c f) := by
  apply Lp.ext
  have hBneg := (bandOperatorL2_coeFn c f).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [bandOperatorL2_coeFn c (unitBandReflection f),
    unitBandReflection_ae (bandOperatorL2 c f), hBneg] with x hleft hright hBnegx
  have hBnegx' : (bandOperatorL2 c f : ClosedInterval (-1 : ℝ) 1 → ℝ)
      (unitIntervalNeg x) = ∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c (unitIntervalNeg x : ℝ) (y : ℝ) * f y ∂volume := by
    simpa only [Function.comp_apply] using hBnegx
  rw [hleft, hright, hBnegx']
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c (x : ℝ) (y : ℝ) * (unitBandReflection f) y ∂volume)
        = ∫ y : ClosedInterval (-1 : ℝ) 1,
            sincKernelSmooth c (x : ℝ) (y : ℝ) * f (unitIntervalNeg y) ∂volume := by
              apply integral_congr_ae
              filter_upwards [unitBandReflection_ae f] with y hy
              rw [hy]
    _ = ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c (x : ℝ) (unitIntervalNeg y : ℝ) * f y ∂volume := by
            have hchange := measurePreserving_unitIntervalNegMeasurableEquiv.integral_comp'
              (fun y : ClosedInterval (-1 : ℝ) 1 =>
                sincKernelSmooth c (x : ℝ) (unitIntervalNeg y : ℝ) * f y)
            simpa only [Function.comp_apply, unitIntervalNegMeasurableEquiv_apply,
              unitIntervalNeg_involutive] using hchange
    _ = ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c (unitIntervalNeg x : ℝ) (y : ℝ) * f y ∂volume := by
            apply integral_congr_ae
            filter_upwards [] with y
            exact congrArg (fun z : ℝ => z * f y)
              (sincKernelSmooth_neg_left_eq_neg_right c (x : ℝ) (y : ℝ)).symm

theorem unitBandReflection_symmetric : unitBandReflection.toLinearMap.IsSymmetric := by
  intro f g
  calc
    inner ℝ (unitBandReflection f) g =
        inner ℝ (unitBandReflection (unitBandReflection f)) (unitBandReflection g) :=
      (unitBandReflectionIsometry.inner_map_map (unitBandReflection f) g).symm
    _ = inner ℝ f (unitBandReflection g) := by rw [unitBandReflection_involutive]

def unitBandEvenProjection :
    RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  (2 : ℝ)⁻¹ • ((1 : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
    RealIntervalL2 (-1 : ℝ) 1) + unitBandReflection)

def unitBandOddProjection :
    RealIntervalL2 (-1 : ℝ) 1 →L[ℝ] RealIntervalL2 (-1 : ℝ) 1 :=
  (2 : ℝ)⁻¹ • ((1 : RealIntervalL2 (-1 : ℝ) 1 →L[ℝ]
    RealIntervalL2 (-1 : ℝ) 1) - unitBandReflection)

@[simp] theorem unitBandEvenProjection_apply (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandEvenProjection f = (2 : ℝ)⁻¹ • (f + unitBandReflection f) := rfl

@[simp] theorem unitBandOddProjection_apply (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandOddProjection f = (2 : ℝ)⁻¹ • (f - unitBandReflection f) := rfl

@[simp] theorem unitBandReflection_evenProjection (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandReflection (unitBandEvenProjection f) = unitBandEvenProjection f := by
  simp [unitBandEvenProjection_apply, map_add, map_smul, add_comm]

@[simp] theorem unitBandReflection_oddProjection (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandReflection (unitBandOddProjection f) = -unitBandOddProjection f := by
  simp [unitBandOddProjection_apply, map_sub, map_smul]
  module

theorem unitBandEvenProjection_idempotent : IsIdempotentElem unitBandEvenProjection := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change unitBandEvenProjection (unitBandEvenProjection f) = unitBandEvenProjection f
  rw [unitBandEvenProjection_apply (unitBandEvenProjection f),
    unitBandReflection_evenProjection]
  module

theorem unitBandOddProjection_idempotent : IsIdempotentElem unitBandOddProjection := by
  rw [isIdempotentElem_iff]
  apply ContinuousLinearMap.ext
  intro f
  change unitBandOddProjection (unitBandOddProjection f) = unitBandOddProjection f
  rw [unitBandOddProjection_apply (unitBandOddProjection f),
    unitBandReflection_oddProjection]
  module

theorem unitBandEvenProjection_add_oddProjection (f : RealIntervalL2 (-1 : ℝ) 1) :
    unitBandEvenProjection f + unitBandOddProjection f = f := by
  rw [unitBandEvenProjection_apply, unitBandOddProjection_apply]
  module

def unitBandEvenSubspace : Submodule ℝ (RealIntervalL2 (-1 : ℝ) 1) :=
  LinearMap.range unitBandEvenProjection.toLinearMap

def unitBandOddSubspace : Submodule ℝ (RealIntervalL2 (-1 : ℝ) 1) :=
  LinearMap.range unitBandOddProjection.toLinearMap

instance unitBandEvenSubspace_completeSpace : CompleteSpace unitBandEvenSubspace :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    unitBandEvenProjection_idempotent).completeSpace_coe

instance unitBandOddSubspace_completeSpace : CompleteSpace unitBandOddSubspace :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    unitBandOddProjection_idempotent).completeSpace_coe

theorem mem_unitBandEvenSubspace_iff (f : RealIntervalL2 (-1 : ℝ) 1) :
    f ∈ unitBandEvenSubspace ↔ unitBandReflection f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact unitBandReflection_evenProjection g
  · intro hf
    refine ⟨f, ?_⟩
    change unitBandEvenProjection f = f
    rw [unitBandEvenProjection_apply, hf]
    module

theorem mem_unitBandOddSubspace_iff (f : RealIntervalL2 (-1 : ℝ) 1) :
    f ∈ unitBandOddSubspace ↔ unitBandReflection f = -f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact unitBandReflection_oddProjection g
  · intro hf
    refine ⟨f, ?_⟩
    change unitBandOddProjection f = f
    rw [unitBandOddProjection_apply, hf]
    module

theorem inner_even_odd_eq_zero
    {f g : RealIntervalL2 (-1 : ℝ) 1}
    (hf : f ∈ unitBandEvenSubspace) (hg : g ∈ unitBandOddSubspace) :
    (inner ℝ f g : ℝ) = 0 := by
  have hmap := unitBandReflectionIsometry.inner_map_map f g
  change (inner ℝ (unitBandReflection f) (unitBandReflection g) : ℝ) = inner ℝ f g at hmap
  rw [(mem_unitBandEvenSubspace_iff f).mp hf,
    (mem_unitBandOddSubspace_iff g).mp hg, inner_neg_right] at hmap
  linarith

theorem bandOperatorL2_mem_unitBandEvenSubspace (c : ℝ)
    {f : RealIntervalL2 (-1 : ℝ) 1} (hf : f ∈ unitBandEvenSubspace) :
    bandOperatorL2 c f ∈ unitBandEvenSubspace := by
  rw [mem_unitBandEvenSubspace_iff, ← bandOperatorL2_unitBandReflection,
    (mem_unitBandEvenSubspace_iff f).mp hf]

theorem bandOperatorL2_mem_unitBandOddSubspace (c : ℝ)
    {f : RealIntervalL2 (-1 : ℝ) 1} (hf : f ∈ unitBandOddSubspace) :
    bandOperatorL2 c f ∈ unitBandOddSubspace := by
  rw [mem_unitBandOddSubspace_iff, ← bandOperatorL2_unitBandReflection,
    (mem_unitBandOddSubspace_iff f).mp hf, map_neg]

def unitBandEvenBlock (c : ℝ) : unitBandEvenSubspace →L[ℝ] unitBandEvenSubspace :=
  (bandOperatorL2 c).restrict (fun _ hf => bandOperatorL2_mem_unitBandEvenSubspace c hf)

def unitBandOddBlock (c : ℝ) : unitBandOddSubspace →L[ℝ] unitBandOddSubspace :=
  (bandOperatorL2 c).restrict (fun _ hf => bandOperatorL2_mem_unitBandOddSubspace c hf)

@[simp] theorem coe_unitBandEvenBlock_apply (c : ℝ) (f : unitBandEvenSubspace) :
    ((unitBandEvenBlock c f : unitBandEvenSubspace) : RealIntervalL2 (-1 : ℝ) 1) =
      bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1) := rfl

@[simp] theorem coe_unitBandOddBlock_apply (c : ℝ) (f : unitBandOddSubspace) :
    ((unitBandOddBlock c f : unitBandOddSubspace) : RealIntervalL2 (-1 : ℝ) 1) =
      bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1) := rfl

theorem isCompactOperator_unitBandEvenBlock (c : ℝ) :
    IsCompactOperator (unitBandEvenBlock c) :=
  (isCompactOperator_bandOperatorL2 c).restrict'
    (fun _ hf => bandOperatorL2_mem_unitBandEvenSubspace c hf)

theorem isCompactOperator_unitBandOddBlock (c : ℝ) :
    IsCompactOperator (unitBandOddBlock c) :=
  (isCompactOperator_bandOperatorL2 c).restrict'
    (fun _ hf => bandOperatorL2_mem_unitBandOddSubspace c hf)

theorem unitBandEvenBlock_symmetric (c : ℝ) : (unitBandEvenBlock c).IsSymmetric := by
  have hsym : (bandOperatorL2 c).IsSymmetric := bandOperatorL2_symmetric c
  exact hsym.restrict_invariant
    (fun f hf => bandOperatorL2_mem_unitBandEvenSubspace c hf)

theorem unitBandOddBlock_symmetric (c : ℝ) : (unitBandOddBlock c).IsSymmetric := by
  have hsym : (bandOperatorL2 c).IsSymmetric := bandOperatorL2_symmetric c
  exact hsym.restrict_invariant
    (fun f hf => bandOperatorL2_mem_unitBandOddSubspace c hf)

theorem unitBandEvenBlock_positive {c : ℝ} (hc : 0 < c) (f : unitBandEvenSubspace) :
    0 ≤ (inner ℝ f (unitBandEvenBlock c f) : ℝ) := by
  change 0 ≤ (inner ℝ (f : RealIntervalL2 (-1 : ℝ) 1)
    (bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1)) : ℝ)
  rw [real_inner_comm]
  exact inner_bandOperatorL2_nonneg hc f

theorem unitBandOddBlock_positive {c : ℝ} (hc : 0 < c) (f : unitBandOddSubspace) :
    0 ≤ (inner ℝ f (unitBandOddBlock c f) : ℝ) := by
  change 0 ≤ (inner ℝ (f : RealIntervalL2 (-1 : ℝ) 1)
    (bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1)) : ℝ)
  rw [real_inner_comm]
  exact inner_bandOperatorL2_nonneg hc f

theorem unitBandReflection_bandClass (Φ : ℝ → ℝ) (hΦ : Continuous Φ) :
    unitBandReflection (bandClass Φ hΦ) =
      bandClass (fun x => Φ (-x)) (hΦ.comp continuous_neg) := by
  apply Lp.ext
  have hneg := (coeFn_bandClass Φ hΦ).comp_tendsto
    measurePreserving_unitIntervalNeg.quasiMeasurePreserving.tendsto_ae
  filter_upwards [unitBandReflection_ae (bandClass Φ hΦ), hneg,
    coeFn_bandClass (fun x => Φ (-x)) (hΦ.comp continuous_neg)] with x href hsource htarget
  rw [href, htarget]
  simpa only [Function.comp_apply, unitIntervalNeg] using hsource

theorem constantBandClass_mem_unitBandEvenSubspace :
    constantBandClass ∈ unitBandEvenSubspace := by
  rw [mem_unitBandEvenSubspace_iff]
  change unitBandReflection (bandClass (fun _ : ℝ => 1) continuous_const) = _
  rw [unitBandReflection_bandClass]
  rfl

noncomputable def oddCoordinateBandClass : RealIntervalL2 (-1 : ℝ) 1 :=
  bandClass (fun x : ℝ => x) continuous_id

theorem oddCoordinateBandClass_mem_unitBandOddSubspace :
    oddCoordinateBandClass ∈ unitBandOddSubspace := by
  rw [mem_unitBandOddSubspace_iff]
  rw [oddCoordinateBandClass, unitBandReflection_bandClass]
  have hsmul := bandClass_smul continuous_id (-1)
    (continuous_const.mul continuous_id)
  change bandClass (fun x : ℝ => -x) _ =
    -(bandClass (fun x : ℝ => x) continuous_id)
  change bandClass (fun x : ℝ => (-1 : ℝ) * x) _ =
    (-1 : ℝ) • bandClass (fun x : ℝ => x) continuous_id at hsmul
  simpa only [neg_one_mul, neg_one_smul] using hsmul

theorem oddCoordinateBandClass_ne_zero : oddCoordinateBandClass ≠ 0 := by
  intro hzero
  have hclass : bandClass (fun x : ℝ => x) continuous_id =
      bandClass (fun _ : ℝ => 0) continuous_const := by
    rw [← oddCoordinateBandClass, hzero]
    exact (bandClass_zero continuous_const).symm
  have hpoint := eqOn_of_bandClass_eq continuous_id continuous_const hclass 1
    (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
  norm_num at hpoint

theorem unitBandEvenBlock_ne_zero {c : ℝ} (hc : 0 < c) : unitBandEvenBlock c ≠ 0 := by
  intro hzero
  have happ := DFunLike.congr_fun hzero
    (⟨constantBandClass, constantBandClass_mem_unitBandEvenSubspace⟩ : unitBandEvenSubspace)
  have hBzero : bandOperatorL2 c constantBandClass = 0 := by
    have hcoe := congrArg (fun z : unitBandEvenSubspace =>
      (z : RealIntervalL2 (-1 : ℝ) 1)) happ
    simpa using hcoe
  exact bandClass_one_ne_zero (eq_zero_of_bandOperatorL2_eq_zero hc hBzero)

theorem unitBandOddBlock_ne_zero {c : ℝ} (hc : 0 < c) : unitBandOddBlock c ≠ 0 := by
  intro hzero
  have happ := DFunLike.congr_fun hzero
    (⟨oddCoordinateBandClass, oddCoordinateBandClass_mem_unitBandOddSubspace⟩ :
      unitBandOddSubspace)
  have hBzero : bandOperatorL2 c oddCoordinateBandClass = 0 := by
    have hcoe := congrArg (fun z : unitBandOddSubspace =>
      (z : RealIntervalL2 (-1 : ℝ) 1)) happ
    simpa using hcoe
  exact oddCoordinateBandClass_ne_zero (eq_zero_of_bandOperatorL2_eq_zero hc hBzero)

theorem exists_unitBandEvenBlock_norm_eigenvector {c : ℝ} (hc : 0 < c) :
    ∃ f : unitBandEvenSubspace, ‖f‖ = 1 ∧
      unitBandEvenBlock c f = ‖unitBandEvenBlock c‖ • f :=
  ContinuousLinearMap.exists_unit_eigenvector_norm_real
    (isCompactOperator_unitBandEvenBlock c) (unitBandEvenBlock_symmetric c)
    (unitBandEvenBlock_positive hc) (unitBandEvenBlock_ne_zero hc)

theorem exists_unitBandOddBlock_norm_eigenvector {c : ℝ} (hc : 0 < c) :
    ∃ f : unitBandOddSubspace, ‖f‖ = 1 ∧
      unitBandOddBlock c f = ‖unitBandOddBlock c‖ • f :=
  ContinuousLinearMap.exists_unit_eigenvector_norm_real
    (isCompactOperator_unitBandOddBlock c) (unitBandOddBlock_symmetric c)
    (unitBandOddBlock_positive hc) (unitBandOddBlock_ne_zero hc)

theorem norm_unitBandEvenBlock_pos {c : ℝ} (hc : 0 < c) :
    0 < ‖unitBandEvenBlock c‖ := by
  refine lt_of_le_of_ne (ContinuousLinearMap.opNorm_nonneg _) ?_
  intro hzero
  exact unitBandEvenBlock_ne_zero hc
    ((ContinuousLinearMap.opNorm_zero_iff (unitBandEvenBlock c)).mp hzero.symm)

theorem norm_unitBandOddBlock_pos {c : ℝ} (hc : 0 < c) :
    0 < ‖unitBandOddBlock c‖ := by
  refine lt_of_le_of_ne (ContinuousLinearMap.opNorm_nonneg _) ?_
  intro hzero
  exact unitBandOddBlock_ne_zero hc
    ((ContinuousLinearMap.opNorm_zero_iff (unitBandOddBlock c)).mp hzero.symm)

/-- The two parity-sector top eigenvalues cannot collide at positive aperture.  A collision would
give two orthogonal eigenvectors for one nonzero eigenvalue, contradicting full simplicity. -/
theorem norm_unitBandEvenBlock_ne_norm_unitBandOddBlock {c : ℝ} (hc : 0 < c) :
    ‖unitBandEvenBlock c‖ ≠ ‖unitBandOddBlock c‖ := by
  intro hnorm
  obtain ⟨e, heunit, heig⟩ := exists_unitBandEvenBlock_norm_eigenvector hc
  obtain ⟨o, hounit, hoig⟩ := exists_unitBandOddBlock_norm_eigenvector hc
  have he0 : (e : RealIntervalL2 (-1 : ℝ) 1) ≠ 0 := by
    intro hzero
    have : e = 0 := Subtype.ext hzero
    rw [this, norm_zero] at heunit
    norm_num at heunit
  have hlambda0 : ‖unitBandEvenBlock c‖ ≠ 0 :=
    ne_of_gt (norm_unitBandEvenBlock_pos hc)
  have heigFull : bandOperatorL2 c (e : RealIntervalL2 (-1 : ℝ) 1) =
      ‖unitBandEvenBlock c‖ • (e : RealIntervalL2 (-1 : ℝ) 1) := by
    exact congrArg Subtype.val heig
  have hoigFull : bandOperatorL2 c (o : RealIntervalL2 (-1 : ℝ) 1) =
      ‖unitBandEvenBlock c‖ • (o : RealIntervalL2 (-1 : ℝ) 1) := by
    have hcoe := congrArg Subtype.val hoig
    rw [hnorm]
    exact hcoe
  obtain ⟨s, hs⟩ := bandOperatorL2_eigenvectors_proportional
    hc hlambda0 heigFull he0 hoigFull
  have horth : (inner ℝ (e : RealIntervalL2 (-1 : ℝ) 1)
      (o : RealIntervalL2 (-1 : ℝ) 1) : ℝ) = 0 :=
    inner_even_odd_eq_zero e.property o.property
  have heunitFull : ‖(e : RealIntervalL2 (-1 : ℝ) 1)‖ = 1 := heunit
  rw [hs, inner_smul_right, real_inner_self_eq_norm_sq, heunitFull, one_pow, mul_one] at horth
  have hs0 : s = 0 := horth
  have ho0 : o = 0 := by
    apply Subtype.ext
    change (o : RealIntervalL2 (-1 : ℝ) 1) = 0
    simpa [hs0] using hs
  rw [ho0, norm_zero] at hounit
  norm_num at hounit

theorem norm_unitBandEvenBlock_sub_le (c d : ℝ) :
    ‖unitBandEvenBlock c - unitBandEvenBlock d‖ ≤
      ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
  intro f
  change ‖bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1) -
      bandOperatorL2 d (f : RealIntervalL2 (-1 : ℝ) 1)‖ ≤
    ‖bandOperatorL2 c - bandOperatorL2 d‖ * ‖f‖
  exact (bandOperatorL2 c - bandOperatorL2 d).le_opNorm
    (f : RealIntervalL2 (-1 : ℝ) 1)

theorem norm_unitBandOddBlock_sub_le (c d : ℝ) :
    ‖unitBandOddBlock c - unitBandOddBlock d‖ ≤
      ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
  intro f
  change ‖bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1) -
      bandOperatorL2 d (f : RealIntervalL2 (-1 : ℝ) 1)‖ ≤
    ‖bandOperatorL2 c - bandOperatorL2 d‖ * ‖f‖
  exact (bandOperatorL2 c - bandOperatorL2 d).le_opNorm
    (f : RealIntervalL2 (-1 : ℝ) 1)

theorem dist_norm_unitBandEvenBlock_le (c d : ℝ) :
    dist ‖unitBandEvenBlock c‖ ‖unitBandEvenBlock d‖ ≤
      dist (bandOperatorL2 c) (bandOperatorL2 d) := by
  rw [Real.dist_eq, dist_eq_norm]
  rw [abs_le]
  constructor
  · have htri : ‖unitBandEvenBlock d‖ ≤
        ‖unitBandEvenBlock d - unitBandEvenBlock c‖ + ‖unitBandEvenBlock c‖ := by
      calc
        ‖unitBandEvenBlock d‖ =
            ‖(unitBandEvenBlock d - unitBandEvenBlock c) + unitBandEvenBlock c‖ := by
              congr 1
              module
        _ ≤ _ := ContinuousLinearMap.opNorm_add_le _ _
    have hsector : ‖unitBandEvenBlock d - unitBandEvenBlock c‖ ≤
        ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
      calc
        ‖unitBandEvenBlock d - unitBandEvenBlock c‖ ≤
            ‖bandOperatorL2 d - bandOperatorL2 c‖ :=
          norm_unitBandEvenBlock_sub_le d c
        _ = ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
          rw [show bandOperatorL2 d - bandOperatorL2 c =
            -(bandOperatorL2 c - bandOperatorL2 d) by module,
            ContinuousLinearMap.opNorm_neg]
    linarith
  · have htri : ‖unitBandEvenBlock c‖ ≤
        ‖unitBandEvenBlock c - unitBandEvenBlock d‖ + ‖unitBandEvenBlock d‖ := by
      calc
        ‖unitBandEvenBlock c‖ =
            ‖(unitBandEvenBlock c - unitBandEvenBlock d) + unitBandEvenBlock d‖ := by
              congr 1
              module
        _ ≤ _ := ContinuousLinearMap.opNorm_add_le _ _
    linarith [norm_unitBandEvenBlock_sub_le c d]

theorem dist_norm_unitBandOddBlock_le (c d : ℝ) :
    dist ‖unitBandOddBlock c‖ ‖unitBandOddBlock d‖ ≤
      dist (bandOperatorL2 c) (bandOperatorL2 d) := by
  rw [Real.dist_eq, dist_eq_norm]
  rw [abs_le]
  constructor
  · have htri : ‖unitBandOddBlock d‖ ≤
        ‖unitBandOddBlock d - unitBandOddBlock c‖ + ‖unitBandOddBlock c‖ := by
      calc
        ‖unitBandOddBlock d‖ =
            ‖(unitBandOddBlock d - unitBandOddBlock c) + unitBandOddBlock c‖ := by
              congr 1
              module
        _ ≤ _ := ContinuousLinearMap.opNorm_add_le _ _
    have hsector : ‖unitBandOddBlock d - unitBandOddBlock c‖ ≤
        ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
      calc
        ‖unitBandOddBlock d - unitBandOddBlock c‖ ≤
            ‖bandOperatorL2 d - bandOperatorL2 c‖ :=
          norm_unitBandOddBlock_sub_le d c
        _ = ‖bandOperatorL2 c - bandOperatorL2 d‖ := by
          rw [show bandOperatorL2 d - bandOperatorL2 c =
            -(bandOperatorL2 c - bandOperatorL2 d) by module,
            ContinuousLinearMap.opNorm_neg]
    linarith
  · have htri : ‖unitBandOddBlock c‖ ≤
        ‖unitBandOddBlock c - unitBandOddBlock d‖ + ‖unitBandOddBlock d‖ := by
      calc
        ‖unitBandOddBlock c‖ =
            ‖(unitBandOddBlock c - unitBandOddBlock d) + unitBandOddBlock d‖ := by
              congr 1
              module
        _ ≤ _ := ContinuousLinearMap.opNorm_add_le _ _
    linarith [norm_unitBandOddBlock_sub_le c d]

theorem continuous_norm_unitBandEvenBlock :
    Continuous fun c : ℝ => ‖unitBandEvenBlock c‖ := by
  rw [Metric.continuous_iff]
  intro c ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuous_iff.mp contDiff_bandOperatorL2.continuous) c ε hε
  exact ⟨δ, hδpos, fun d hd =>
    lt_of_le_of_lt (dist_norm_unitBandEvenBlock_le d c) (hδ d hd)⟩

theorem continuous_norm_unitBandOddBlock :
    Continuous fun c : ℝ => ‖unitBandOddBlock c‖ := by
  rw [Metric.continuous_iff]
  intro c ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    (Metric.continuous_iff.mp contDiff_bandOperatorL2.continuous) c ε hε
  exact ⟨δ, hδpos, fun d hd =>
    lt_of_le_of_lt (dist_norm_unitBandOddBlock_le d c) (hδ d hd)⟩

theorem norm_unitBandEvenBlock_le_norm_bandOperatorL2 (c : ℝ) :
    ‖unitBandEvenBlock c‖ ≤ ‖bandOperatorL2 c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
  intro f
  change ‖bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1)‖ ≤
    ‖bandOperatorL2 c‖ * ‖f‖
  exact (bandOperatorL2 c).le_opNorm (f : RealIntervalL2 (-1 : ℝ) 1)

theorem norm_unitBandOddBlock_le_norm_bandOperatorL2 (c : ℝ) :
    ‖unitBandOddBlock c‖ ≤ ‖bandOperatorL2 c‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
  intro f
  change ‖bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1)‖ ≤
    ‖bandOperatorL2 c‖ * ‖f‖
  exact (bandOperatorL2 c).le_opNorm (f : RealIntervalL2 (-1 : ℝ) 1)

theorem bandClass_mem_unitBandEvenSubspace_of_even
    {Phi : ℝ → ℝ} (hPhi : Continuous Phi) (heven : Function.Even Phi) :
    bandClass Phi hPhi ∈ unitBandEvenSubspace := by
  rw [mem_unitBandEvenSubspace_iff, unitBandReflection_bandClass]
  have hfun : (fun x : ℝ => Phi (-x)) = Phi := funext heven
  exact bandClass_congr (hPhi.comp continuous_neg) hPhi hfun

/-- Small-aperture anchor expressed as a strict ordering of the actual parity-sector operator
norms.  This is the sign input for global continuation. -/
theorem norm_unitBandOddBlock_lt_norm_unitBandEvenBlock_of_smallAperture
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 8) :
    ‖unitBandOddBlock c‖ < ‖unitBandEvenBlock c‖ := by
  obtain ⟨lam, _eta, Phi, hlamLower, hlamNorm, hPhiSmooth, hPhiNe, hPhiEven,
    hPhiBand, _hPhiProlate, _hetaLower⟩ :=
    exists_smallAperture_leading_joint_separation_anchor hc hcsmall
  have hlam0 : lam ≠ 0 := by
    have hnonneg : 0 ≤ 4 * c ^ 2 / Real.pi := by positivity
    linarith
  let f := bandClass Phi hPhiSmooth.continuous
  have hfne : f ≠ 0 :=
    bandClass_ne_zero_of_global_band_eigen hPhiSmooth.continuous hlam0 hPhiNe hPhiBand
  have hfmem : f ∈ unitBandEvenSubspace :=
    bandClass_mem_unitBandEvenSubspace_of_even hPhiSmooth.continuous hPhiEven
  let e : unitBandEvenSubspace := ⟨f, hfmem⟩
  have heigFull : bandOperatorL2 c (e : RealIntervalL2 (-1 : ℝ) 1) =
      ‖bandOperatorL2 c‖ • (e : RealIntervalL2 (-1 : ℝ) 1) := by
    change bandOperatorL2 c f = ‖bandOperatorL2 c‖ • f
    rw [← hlamNorm]
    exact bandOperatorL2_bandClass_eq_smul_of_global_band_eigen
      hPhiSmooth.continuous hPhiBand
  have heigBlock : unitBandEvenBlock c e = ‖bandOperatorL2 c‖ • e := by
    apply Subtype.ext
    exact heigFull
  have henormpos : 0 < ‖e‖ := by
    rw [norm_pos_iff]
    intro hezero
    apply hfne
    exact congrArg Subtype.val hezero
  have hop := (unitBandEvenBlock c).le_opNorm e
  rw [heigBlock, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _)] at hop
  have hfullLeEven : ‖bandOperatorL2 c‖ ≤ ‖unitBandEvenBlock c‖ := by
    nlinarith
  have hevenEq : ‖unitBandEvenBlock c‖ = ‖bandOperatorL2 c‖ :=
    le_antisymm (norm_unitBandEvenBlock_le_norm_bandOperatorL2 c) hfullLeEven
  have hoddLe : ‖unitBandOddBlock c‖ ≤ ‖unitBandEvenBlock c‖ := by
    rw [hevenEq]
    exact norm_unitBandOddBlock_le_norm_bandOperatorL2 c
  exact lt_of_le_of_ne hoddLe
    (norm_unitBandEvenBlock_ne_norm_unitBandOddBlock hc).symm

def unitBandParityNormGap (c : ℝ) : ℝ :=
  ‖unitBandEvenBlock c‖ - ‖unitBandOddBlock c‖

theorem continuous_unitBandParityNormGap : Continuous unitBandParityNormGap :=
  continuous_norm_unitBandEvenBlock.sub continuous_norm_unitBandOddBlock

theorem unitBandParityNormGap_ne_zero {c : ℝ} (hc : 0 < c) :
    unitBandParityNormGap c ≠ 0 := by
  rw [unitBandParityNormGap, sub_ne_zero]
  exact norm_unitBandEvenBlock_ne_norm_unitBandOddBlock hc

theorem unitBandParityNormGap_pos_of_smallAperture
    {c : ℝ} (hc : 0 < c) (hcsmall : c < 1 / 8) :
    0 < unitBandParityNormGap c := by
  rw [unitBandParityNormGap, sub_pos]
  exact norm_unitBandOddBlock_lt_norm_unitBandEvenBlock_of_smallAperture hc hcsmall

/-- **Global parity-sector ordering.** At every positive aperture, the top even concentration
eigenvalue is strictly larger than the top odd concentration eigenvalue.  Proof is continuation
from the small-aperture rank-one anchor; a sign change would force a forbidden parity collision. -/
theorem norm_unitBandOddBlock_lt_norm_unitBandEvenBlock
    {c : ℝ} (hc : 0 < c) :
    ‖unitBandOddBlock c‖ < ‖unitBandEvenBlock c‖ := by
  let c0 : ℝ := 1 / 16
  have hc0 : 0 < c0 := by norm_num [c0]
  have hc0small : c0 < 1 / 8 := by norm_num [c0]
  have hanchor : 0 < unitBandParityNormGap c0 :=
    unitBandParityNormGap_pos_of_smallAperture hc0 hc0small
  have hgap : 0 < unitBandParityNormGap c := by
    by_contra hnot
    have hneg : unitBandParityNormGap c < 0 :=
      lt_of_le_of_ne (le_of_not_gt hnot) (unitBandParityNormGap_ne_zero hc)
    have hzmem : (0 : ℝ) ∈ Icc (unitBandParityNormGap c) (unitBandParityNormGap c0) :=
      ⟨hneg.le, hanchor.le⟩
    by_cases horder : c ≤ c0
    · obtain ⟨t, ht, htzero⟩ :=
        (intermediate_value_Icc horder continuous_unitBandParityNormGap.continuousOn) hzmem
      exact unitBandParityNormGap_ne_zero (lt_of_lt_of_le hc ht.1) htzero
    · have horder' : c0 ≤ c := le_of_not_ge horder
      obtain ⟨t, ht, htzero⟩ :=
        (intermediate_value_Icc' horder'
          continuous_unitBandParityNormGap.continuousOn) hzmem
      exact unitBandParityNormGap_ne_zero (lt_of_lt_of_le hc0 ht.1) htzero
  rwa [unitBandParityNormGap, sub_pos] at hgap

theorem bandOperatorL2_ne_zero {c : ℝ} (hc : 0 < c) : bandOperatorL2 c ≠ 0 := by
  intro hzero
  apply unitBandEvenBlock_ne_zero hc
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  change bandOperatorL2 c (f : RealIntervalL2 (-1 : ℝ) 1) = 0
  rw [hzero]
  rfl

theorem exists_unit_bandOperatorL2_norm_eigenvector {c : ℝ} (hc : 0 < c) :
    ∃ f : RealIntervalL2 (-1 : ℝ) 1, ‖f‖ = 1 ∧
      bandOperatorL2 c f = ‖bandOperatorL2 c‖ • f :=
  ContinuousLinearMap.exists_unit_eigenvector_norm_real
    (isCompactOperator_bandOperatorL2 c) (bandOperatorL2_symmetric c)
    (fun f => by
      rw [real_inner_comm]
      exact inner_bandOperatorL2_nonneg hc f)
    (bandOperatorL2_ne_zero hc)

/-- Every normalized eigenvector at the full band-operator norm is even.  Simplicity first forces
reflection parity; global sector ordering then excludes the odd alternative. -/
theorem bandOperatorL2_norm_eigenvector_mem_unitBandEvenSubspace
    {c : ℝ} (hc : 0 < c) {f : RealIntervalL2 (-1 : ℝ) 1}
    (hfnorm : ‖f‖ = 1)
    (hf : bandOperatorL2 c f = ‖bandOperatorL2 c‖ • f) :
    f ∈ unitBandEvenSubspace := by
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hfnorm
    norm_num at hfnorm
  have hlambda0 : ‖bandOperatorL2 c‖ ≠ 0 := by
    intro hzero
    exact bandOperatorL2_ne_zero hc
      ((ContinuousLinearMap.opNorm_zero_iff (bandOperatorL2 c)).mp hzero)
  have hrefEig : bandOperatorL2 c (unitBandReflection f) =
      ‖bandOperatorL2 c‖ • unitBandReflection f := by
    rw [bandOperatorL2_unitBandReflection, hf, map_smul]
  obtain ⟨s, hs⟩ := bandOperatorL2_eigenvectors_proportional
    hc hlambda0 hf hfne hrefEig
  have htwice : f = (s * s) • f := by
    calc
      f = unitBandReflection (unitBandReflection f) :=
        (unitBandReflection_involutive f).symm
      _ = unitBandReflection (s • f) := congrArg unitBandReflection hs
      _ = (s * s) • f := by rw [map_smul, hs, smul_smul]
  have hinner := congrArg (fun g : RealIntervalL2 (-1 : ℝ) 1 =>
    (inner ℝ f g : ℝ)) htwice
  rw [inner_smul_right, real_inner_self_eq_norm_sq, hfnorm, one_pow, mul_one] at hinner
  have hsquare : s ^ 2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hsquare with hsone | hsneg
  · rw [mem_unitBandEvenSubspace_iff]
    simpa [hsone] using hs
  · have hfodd : f ∈ unitBandOddSubspace := by
      rw [mem_unitBandOddSubspace_iff]
      simpa [hsneg] using hs
    let o : unitBandOddSubspace := ⟨f, hfodd⟩
    have hoEig : unitBandOddBlock c o = ‖bandOperatorL2 c‖ • o := by
      apply Subtype.ext
      exact hf
    have hop := (unitBandOddBlock c).le_opNorm o
    have honorm : ‖o‖ = 1 := hfnorm
    rw [hoEig, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _), honorm, mul_one] at hop
    have hevenLe := norm_unitBandEvenBlock_le_norm_bandOperatorL2 c
    have hstrict := norm_unitBandOddBlock_lt_norm_unitBandEvenBlock hc
    linarith

theorem norm_unitBandEvenBlock_eq_norm_bandOperatorL2
    {c : ℝ} (hc : 0 < c) :
    ‖unitBandEvenBlock c‖ = ‖bandOperatorL2 c‖ := by
  obtain ⟨f, hfnorm, hf⟩ := exists_unit_bandOperatorL2_norm_eigenvector hc
  have hfeven := bandOperatorL2_norm_eigenvector_mem_unitBandEvenSubspace hc hfnorm hf
  let e : unitBandEvenSubspace := ⟨f, hfeven⟩
  have heEig : unitBandEvenBlock c e = ‖bandOperatorL2 c‖ • e := by
    apply Subtype.ext
    exact hf
  have henorm : ‖e‖ = 1 := hfnorm
  have hop := (unitBandEvenBlock c).le_opNorm e
  rw [heEig, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ContinuousLinearMap.opNorm_nonneg _), henorm, mul_one] at hop
  exact le_antisymm (norm_unitBandEvenBlock_le_norm_bandOperatorL2 c)
    (by simpa only [mul_one] using hop)

theorem eigenExtension_even_of_mem_unitBandEvenSubspace
    (c nu : ℝ) {f : RealIntervalL2 (-1 : ℝ) 1}
    (hf : f ∈ unitBandEvenSubspace) :
    Function.Even (eigenExtension c nu f) := by
  have href := unitBandReflection_ae f
  rw [(mem_unitBandEvenSubspace_iff f).mp hf] at href
  intro x
  unfold eigenExtension
  congr 1
  have hchange := measurePreserving_unitIntervalNegMeasurableEquiv.integral_comp'
    (fun y : ClosedInterval (-1 : ℝ) 1 =>
      sincKernelSmooth c (-x) (unitIntervalNeg y : ℝ) * f (unitIntervalNeg y))
  calc
    (∫ y : ClosedInterval (-1 : ℝ) 1,
        sincKernelSmooth c (-x) (y : ℝ) * f y ∂volume) =
        ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c (-x) (unitIntervalNeg y : ℝ) *
            f (unitIntervalNeg y) ∂volume := by
              simpa only [Function.comp_apply, unitIntervalNegMeasurableEquiv_apply,
                unitIntervalNeg_involutive] using hchange
    _ = ∫ y : ClosedInterval (-1 : ℝ) 1,
          sincKernelSmooth c x (y : ℝ) * f y ∂volume := by
            apply integral_congr_ae
            filter_upwards [href] with y hy
            rw [← hy]
            exact congrArg (fun z : ℝ => z * f y)
              (by simpa [unitIntervalNeg] using
                sincKernelSmooth_neg_left_eq_neg_right c x (-(y : ℝ)))

/-- **Global leading joint mode.** For every positive aperture, the full concentration norm is
carried by a smooth nonzero even joint Slepian/prolate eigenfunction. -/
theorem exists_leading_joint_even_prolate_band_eigen
    {c : ℝ} (hc : 0 < c) :
    ∃ (Phi : ℝ → ℝ) (eta : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi ∧
      Phi ≠ 0 ∧ Function.Even Phi ∧
      (∀ x : ℝ, bandTransform c Phi x = ‖bandOperatorL2 c‖ * Phi x) ∧
      (∀ x : ℝ, prolateSLAction c Phi x = eta * Phi x) := by
  obtain ⟨f, hfnorm, hf⟩ := exists_unit_bandOperatorL2_norm_eigenvector hc
  have hfne : f ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hfnorm
    norm_num at hfnorm
  have hlam0 : ‖bandOperatorL2 c‖ ≠ 0 := by
    intro hzero
    exact bandOperatorL2_ne_zero hc
      ((ContinuousLinearMap.opNorm_zero_iff (bandOperatorL2 c)).mp hzero)
  have hfmem := bandOperatorL2_norm_eigenvector_mem_unitBandEvenSubspace hc hfnorm hf
  exact exists_joint_even_prolate_band_eigen hc hlam0 hf hfne
    (eigenExtension_even_of_mem_unitBandEvenSubspace c ‖bandOperatorL2 c‖ hfmem)

theorem fourier_bandTrunc_mul_eq_of_realFourierBandTransform_eigen
    {a mu : ℝ} (ha : 0 < a) {Phi : ℝ → ℝ}
    (hPhi : Continuous Phi) (hPhiEven : Function.Even Phi)
    (hmu : ∀ x : ℝ,
      realFourierBandTransform (2 * Real.pi * a ^ 2) Phi x = mu * Phi x)
    (x : ℝ) :
    FourierTransform.fourier (bandTrunc Phi) (a * x) =
      (mu : ℂ) * (Phi (x / a) : ℂ) := by
  have hfreq := bandFourier_eq_fourier (-(2 * Real.pi * a * x)) Phi
  have harg : -( -(2 * Real.pi * a * x) / (2 * Real.pi)) = a * x := by
    field_simp [Real.pi_ne_zero]
  rw [harg] at hfreq
  have hfinite : bandFourier (-(2 * Real.pi * a * x)) Phi =
      fourierBandTransform (2 * Real.pi * a ^ 2)
        (fun t => ((Phi t : ℝ) : ℂ)) (-x / a) := by
    rw [bandFourier, fourierBandTransform]
    apply intervalIntegral.integral_congr
    intro t _
    unfold RHTower.bandKernel
    change
      (Phi t : ℂ) *
          Complex.exp (Complex.I * (((-(2 * Real.pi * a * x) : ℝ) : ℂ) * (t : ℂ))) =
        Complex.exp
            (Complex.I * ((((2 * Real.pi * a ^ 2) * (-x / a) * t : ℝ)) : ℂ)) *
          (Phi t : ℂ)
    have hexp :
        Complex.I * (((-(2 * Real.pi * a * x) : ℝ) : ℂ) * (t : ℂ)) =
          Complex.I * ((((2 * Real.pi * a ^ 2) * (-x / a) * t : ℝ)) : ℂ) := by
      push_cast
      congr 1
      field_simp [ha.ne']
    rw [hexp]
    ring
  have hPhiArg : Phi (-x / a) = Phi (x / a) := by
    simpa only [neg_div] using hPhiEven (x / a)
  rw [← hfreq, hfinite,
    fourierBandTransform_ofReal_even hPhi hPhiEven,
    hmu, hPhiArg]
  push_cast
  rfl

/-- Reverse scaling bridge: a real even finite-Fourier eigenprofile on the unit aperture gives an
eigenvector of the actual physical compressed Fourier block. -/
theorem evenTimeBandFourier_continuousEvenPhysicalTrial_eigen
    {a mu : ℝ} (ha : 0 < a) {Phi : ℝ → ℝ}
    (hPhi : Continuous Phi) (hPhiEven : Function.Even Phi)
    (hmu : ∀ x : ℝ,
      realFourierBandTransform (2 * Real.pi * a ^ 2) Phi x = mu * Phi x) :
    evenTimeBandFourier a
        (continuousEvenPhysicalTrial a ha Phi hPhi hPhiEven) =
      ((a * mu : ℝ) : ℂ) • continuousEvenPhysicalTrial a ha Phi hPhi hPhiEven := by
  rw [evenTimeBandFourier_continuousEvenPhysicalTrial ha Phi hPhi hPhiEven]
  apply Subtype.ext
  apply Lp.ext
  let q : evenSubspace := evenIndicatorCutoff (a ^ 2)
    (evenFourierTransform (continuousEvenBandTrial Phi hPhi hPhiEven))
  have hqae : ((q : evenSubspace) : SoninL2) =ᵐ[volume]
      (Icc (-(a ^ 2)) (a ^ 2)).indicator
        (fun xi => FourierTransform.fourier (bandTrunc Phi) xi) := by
    filter_upwards [indicatorCutoff_ae (centralInterval (a ^ 2))
        (measurableSet_centralInterval (a ^ 2))
        (fourierUnitary (continuousEvenBandL2 Phi hPhi)),
      fourierUnitary_continuousEvenBandL2_coeFn Phi hPhi] with xi hcut hfourier
    rw [show ((q : evenSubspace) : SoninL2) =
      indicatorCutoff (centralInterval (a ^ 2))
        (measurableSet_centralInterval (a ^ 2))
        (fourierUnitary (continuousEvenBandL2 Phi hPhi)) from rfl,
      hcut]
    by_cases hxi : xi ∈ Icc (-(a ^ 2)) (a ^ 2)
    · rw [Set.indicator_of_mem hxi, Set.indicator_of_mem, hfourier]
      simpa [centralInterval] using hxi
    · rw [Set.indicator_of_notMem hxi, Set.indicator_of_notMem]
      simpa [centralInterval] using hxi
  have hqcomp := hqae.comp_tendsto
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) ha.ne').tendsto_ae
  have hleft := dilation_ae a ha (q : SoninL2)
  have hsource := continuousEvenBandL2_coeFn Phi hPhi
  have hsourceComp := hsource.comp_tendsto
    (Measure.quasiMeasurePreserving_smul (volume : Measure ℝ)
      (inv_ne_zero ha.ne')).tendsto_ae
  have hrightDil := dilation_ae a⁻¹ (inv_pos.mpr ha) (continuousEvenBandL2 Phi hPhi)
  have hrightSmul := Lp.coeFn_smul (((a * mu : ℝ) : ℂ))
    (dilation a⁻¹ (inv_pos.mpr ha) (continuousEvenBandL2 Phi hPhi))
  filter_upwards [hleft, hqcomp, hrightSmul, hrightDil, hsourceComp] with
      x hxleft hxq hxsmul hxdil hxsource
  change
    ((dilation a ha (q : SoninL2) : SoninL2) : ℝ → ℂ) x =
      (((((a * mu : ℝ) : ℂ) •
        dilation a⁻¹ (inv_pos.mpr ha) (continuousEvenBandL2 Phi hPhi)) : SoninL2) :
          ℝ → ℂ) x
  rw [hxleft, hxsmul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hxdil]
  have hxq' : ((q : evenSubspace) : SoninL2) (a * x) =
      (Icc (-(a ^ 2)) (a ^ 2)).indicator
        (fun xi => FourierTransform.fourier (bandTrunc Phi) xi) (a * x) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hxq
  rw [hxq']
  have hxsource' : (continuousEvenBandL2 Phi hPhi : ℝ → ℂ) (a⁻¹ * x) =
      bandTrunc Phi (a⁻¹ * x) := by
    simpa only [Function.comp_apply, smul_eq_mul] using hxsource
  rw [hxsource']
  by_cases hxin : x ∈ Icc (-a) a
  · have haxin : a * x ∈ Icc (-(a ^ 2)) (a ^ 2) := by
      constructor <;> nlinarith [hxin.1, hxin.2]
    have hxunit : a⁻¹ * x ∈ Icc (-1 : ℝ) 1 := by
      rw [inv_mul_eq_div]
      constructor
      · exact (le_div_iff₀ ha).mpr (by simpa using hxin.1)
      · exact (div_le_iff₀ ha).mpr (by simpa using hxin.2)
    rw [Set.indicator_of_mem haxin,
      fourier_bandTrunc_mul_eq_of_realFourierBandTransform_eigen
        ha hPhi hPhiEven hmu,
      bandTrunc, Set.indicator_of_mem hxunit]
    push_cast
    have hsqrt : a * Real.sqrt a⁻¹ = Real.sqrt a := by
      rw [Real.sqrt_inv, ← div_eq_mul_inv]
      field_simp [Real.sqrt_ne_zero'.mpr ha]
      rw [Real.sq_sqrt ha.le]
    rw [show x / a = a⁻¹ * x by field_simp [ha.ne']]
    have hsqrtC : (a : ℂ) * (Real.sqrt a⁻¹ : ℂ) = (Real.sqrt a : ℂ) := by
      exact_mod_cast hsqrt
    rw [← hsqrtC]
    ring
  · have haxout : a * x ∉ Icc (-(a ^ 2)) (a ^ 2) := by
      intro h
      apply hxin
      constructor <;> nlinarith [h.1, h.2]
    have hxunitOut : a⁻¹ * x ∉ Icc (-1 : ℝ) 1 := by
      intro h
      apply hxin
      rw [inv_mul_eq_div] at h
      constructor
      · simpa using (le_div_iff₀ ha).mp h.1
      · simpa using (div_le_iff₀ ha).mp h.2
    rw [Set.indicator_of_notMem haxout, bandTrunc, Set.indicator_of_notMem hxunitOut]
    simp

/-- A continuous profile nonzero at the symmetry center gives a nonzero physical trial. -/
theorem continuousEvenPhysicalTrial_ne_zero_of_value_zero_ne
    {a : ℝ} (ha : 0 < a) {Phi : ℝ → ℝ}
    (hPhi : Continuous Phi) (hPhiEven : Function.Even Phi) (hPhi0 : Phi 0 ≠ 0) :
    continuousEvenPhysicalTrial a ha Phi hPhi hPhiEven ≠ 0 := by
  intro hzero
  have hmass : 0 < ∫ x in (-1 : ℝ)..1, Phi x ^ 2 :=
    GaloisForLFunctions.HTGeometry.integral_sq_pos_of_ne_zero hPhi
      (show (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 by norm_num) hPhi0
  have hnorm := norm_sq_continuousEvenPhysicalTrial ha Phi hPhi hPhiEven
  rw [hzero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hnorm
  linarith

/-- The leading signed physical Fourier mode is exactly the global top Slepian concentration
line.  This identifies greedy index zero without assuming any prior mode normalization. -/
theorem evenProlateSignedValue_zero_sq_eq_norm_bandOperatorL2
    {a : ℝ} (ha : 0 < a) :
    evenProlateSignedValue a 0 ^ 2 =
      ‖bandOperatorL2 (2 * Real.pi * a ^ 2)‖ := by
  let c : ℝ := 2 * Real.pi * a ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hlam : ‖bandOperatorL2 c‖ ≠ 0 := by
    intro hzero
    exact bandOperatorL2_ne_zero hc
      ((ContinuousLinearMap.opNorm_zero_iff (bandOperatorL2 c)).mp hzero)
  obtain ⟨Phi, eta, hPhiSmooth, hPhiNe, hPhiEven, hBand, hProlate⟩ :=
    exists_leading_joint_even_prolate_band_eigen hc
  have hPhi0 : Phi 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen
      hPhiSmooth hPhiNe hPhiEven hlam hBand hProlate
  have hκ : 0 < a ^ 2 := sq_pos_of_pos ha
  obtain ⟨mu, hmu, hmuSq, hmuEig⟩ :=
    exists_realFourierBandTransform_eigen hκ hPhiSmooth hPhiNe hPhiEven
      (by simpa only [c] using hlam)
      (by simpa only [c] using hBand)
      (by simpa only [c] using hProlate)
  let v : evenSubspace :=
    continuousEvenPhysicalTrial a ha Phi hPhiSmooth.continuous hPhiEven
  have hv : v ≠ 0 := by
    dsimp only [v]
    exact continuousEvenPhysicalTrial_ne_zero_of_value_zero_ne
      ha hPhiSmooth.continuous hPhiEven hPhi0
  have hvEig : evenTimeBandFourier a v = ((a * mu : ℝ) : ℂ) • v := by
    dsimp only [v]
    exact evenTimeBandFourier_continuousEvenPhysicalTrial_eigen
      ha hPhiSmooth.continuous hPhiEven hmuEig
  have hphysNorm : |a * mu| ≤ ‖evenTimeBandFourier a‖ := by
    have hop := (evenTimeBandFourier a).le_opNorm v
    rw [hvEig, norm_smul, Complex.norm_real, Real.norm_eq_abs] at hop
    exact le_of_mul_le_mul_right hop (norm_pos_iff.mpr hv)
  have hsignedAbs : |evenProlateSignedValue a 0| = ‖evenTimeBandFourier a‖ := by
    simpa only [evenProlateSignedValue] using
      (ContinuousLinearMap.abs_sgVal_zero_eq_opNorm_complex
        (isCompactOperator_evenTimeBandFourier a ha)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (adjoint_evenTimeBandFourier a)))
  have hphysNe : a * mu ≠ 0 := mul_ne_zero ha.ne' hmu
  have hnormPos : 0 < ‖evenTimeBandFourier a‖ :=
    lt_of_lt_of_le (abs_pos.mpr hphysNe) hphysNorm
  have hsignedNe : evenProlateSignedValue a 0 ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hsignedAbs
    linarith
  have hlower : ‖bandOperatorL2 c‖ ≤ evenProlateSignedValue a 0 ^ 2 := by
    calc
      ‖bandOperatorL2 c‖ = a ^ 2 * mu ^ 2 := by
        simpa only [c] using hmuSq.symm
      _ = (a * mu) ^ 2 := by ring
      _ = |a * mu| ^ 2 := by rw [sq_abs]
      _ ≤ ‖evenTimeBandFourier a‖ ^ 2 :=
        (sq_le_sq₀ (abs_nonneg (a * mu))
          (norm_nonneg (evenTimeBandFourier a))).2 hphysNorm
      _ = |evenProlateSignedValue a 0| ^ 2 := by rw [hsignedAbs]
      _ = evenProlateSignedValue a 0 ^ 2 := sq_abs _
  obtain ⟨psi, hpsi, hpsiEig, _⟩ :=
    exists_realIntervalL2_bandEigen_of_signedMode ha 0 hsignedNe
  have hupper : evenProlateSignedValue a 0 ^ 2 ≤ ‖bandOperatorL2 c‖ := by
    have hop := (bandOperatorL2 c).le_opNorm psi
    rw [hpsiEig, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (evenProlateSignedValue a 0))] at hop
    exact le_of_mul_le_mul_right hop (norm_pos_iff.mpr hpsi)
  exact le_antisymm hupper hlower

end GaloisForLFunctions.RHTower
