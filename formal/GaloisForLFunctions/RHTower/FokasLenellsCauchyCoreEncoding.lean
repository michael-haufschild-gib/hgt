import GaloisForLFunctions.RHTower.FokasLenellsCauchyCoreFaithfulness
import GaloisForLFunctions.RHTower.FokasLenellsCutoffComplexHardy

/-!
# Exact but unstable Cauchy encoding of the entire core

Cauchy projection is a continuous linear encoding onto its actual core range.
Its algebraic inverse exists, but no uniform recovery bound or continuous
inverse exists in the inherited L² norms. Core cutoffs of a concrete nonzero
Hardy pole vector prove the obstruction. The exact complex-time group still
transports algebraically to the encoded data, whose range is dense in lower Hardy.
-/

open MeasureTheory Complex Filter Topology Metric Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- The literal bounded Cauchy encoding map on the common entire core. -/
def rawComplexCauchyCoreEncodingMap : rawComplexEntireCore →L[ℂ] SoninL2 :=
  negativeCauchy.comp rawComplexEntireCore.subtypeL

/-- The actual encoded core data, with the inherited original L² norm. -/
def rawComplexCauchyCoreRange : Submodule ℂ SoninL2 := rawComplexCauchyCoreEncodingMap.toLinearMap.range

/-- Exact linear encoding onto the actual range; no continuous inverse is built into this carrier. -/
def rawComplexCauchyCoreEncoding : rawComplexEntireCore ≃ₗ[ℂ] rawComplexCauchyCoreRange :=
  LinearEquiv.ofInjective rawComplexCauchyCoreEncodingMap.toLinearMap negativeCauchy_core_injective

/-- The exact encoding retains the actual Cauchy boundary value. -/
theorem rawComplexCauchyCoreEncoding_apply (u : rawComplexEntireCore) :
    (rawComplexCauchyCoreEncoding u).val = negativeCauchy u.val := rfl

/-- The actual encoding is continuous for the inherited L² norms. -/
theorem rawComplexCauchyCoreEncoding_continuous : Continuous rawComplexCauchyCoreEncoding := by
  exact (rawComplexCauchyCoreEncoding.toLinearMap.mkContinuous 1 (fun u => by
    change ‖negativeCauchy u.val‖ ≤ 1 * ‖u.val‖
    rw [one_mul]
    exact negativeCauchy_bound u.val)).continuous

/-- A concrete Hardy-kernel approximation forces arbitrarily poor Cauchy recovery on the core. -/
theorem rawComplexCauchyCoreEncoding_unbounded_recovery :
    ∀ B : ℝ, ∃ u : rawComplexEntireCore, B * ‖negativeCauchy u.val‖ < ‖u‖ := by
  intro B
  by_contra h
  push Not at h
  let p : SoninL2 := lowerPoleProbe 0 0
  have hp : p ≠ 0 := lowerPoleProbe_ne_zero 0 0
  have ht := (rawComplexGraphCutoff_tendsto p).norm
  have hc : Tendsto (fun a => ‖negativeCauchy (rawComplexGraphCutoff a p)‖) atBot (𝓝 (0 : ℝ)) := by
    have hc := (negativeCauchy.continuous.continuousAt.tendsto.comp (rawComplexGraphCutoff_tendsto p)).norm
    simpa only [Function.comp_apply,p,negativeCauchy_lowerPoleProbe,norm_zero] using hc
  have hb : ‖p‖ ≤ B * 0 := le_of_tendsto_of_tendsto ht (tendsto_const_nhds.mul hc)
    (Eventually.of_forall (fun a => h ⟨rawComplexGraphCutoff a p,⟨(a,p),rfl⟩⟩))
  have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp
  linarith

/-- The exact linear decoder is discontinuous in the inherited L² data norm. -/
theorem rawComplexCauchyCoreEncoding_symm_not_continuous :
    ¬ Continuous rawComplexCauchyCoreEncoding.symm := by
  intro hc
  let T : rawComplexCauchyCoreRange →L[ℂ] rawComplexEntireCore :=
    ⟨rawComplexCauchyCoreEncoding.symm.toLinearMap,hc⟩
  obtain ⟨u,hu⟩ := rawComplexCauchyCoreEncoding_unbounded_recovery ‖T‖
  have hb := T.le_opNorm (rawComplexCauchyCoreEncoding u)
  change ‖rawComplexCauchyCoreEncoding.symm (rawComplexCauchyCoreEncoding u)‖ ≤
    ‖T‖ * ‖rawComplexCauchyCoreEncoding u‖ at hb
  rw [rawComplexCauchyCoreEncoding.symm_apply_apply] at hb
  change ‖u‖ ≤ ‖T‖ * ‖negativeCauchy u.val‖ at hb
  exact not_lt_of_ge hb hu

/-- All zeroth-order complex times have exactly the same actual encoded core range. -/
theorem rawComplexCauchyCoreHierarchy_range (τ : ℂ) :
    (rawComplexCauchyCoreHierarchy 0 τ).range = rawComplexCauchyCoreRange := by
  ext y
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨rawComplexCoreHierarchy 0 τ u,hu⟩
  · rintro ⟨u,hu⟩
    refine ⟨(rawComplexCoreGroup τ).symm u,?_⟩
    calc
      rawComplexCauchyCoreHierarchy 0 τ ((rawComplexCoreGroup τ).symm u) = negativeCauchy u.val := by
        change negativeCauchy ((rawComplexCoreGroup τ) ((rawComplexCoreGroup τ).symm u)).val = _
        rw [(rawComplexCoreGroup τ).apply_symm_apply]
      _ = y := hu

/-- The encoded core data are dense in precisely the full lower Hardy subspace. -/
theorem closure_rawComplexCauchyCoreRange :
    closure (rawComplexCauchyCoreRange : Set SoninL2) = hardyL2ᗮ := by
  apply Set.Subset.antisymm
  · apply closure_minimal ?_ hardyL2.isClosed_orthogonal
    rintro y ⟨u,rfl⟩
    exact (negativeCauchy_eq_neg_iff (negativeCauchy u.val)).1 (negativeCauchy_square u.val)
  · intro y hy
    have he : negativeCauchy (-y) = y := by
      rw [map_neg,(negativeCauchy_eq_neg_iff y).2 hy,neg_neg]
    have ht := negativeCauchy.continuous.continuousAt.tendsto.comp (rawComplexGraphCutoff_tendsto (-y))
    rw [he] at ht
    apply mem_closure_of_tendsto ht
    exact Eventually.of_forall (fun a => ⟨⟨rawComplexGraphCutoff a (-y),⟨(a,-y),rfl⟩⟩,rfl⟩)

/-- The actual complex-time group transported to encoded Cauchy data. -/
def rawComplexCauchyCoreGroup (τ : ℂ) : rawComplexCauchyCoreRange ≃ₗ[ℂ] rawComplexCauchyCoreRange :=
  rawComplexCauchyCoreEncoding.symm.trans ((rawComplexCoreGroup τ).trans rawComplexCauchyCoreEncoding)

private theorem encoded_group_apply (τ : ℂ) (u : rawComplexEntireCore) :
    rawComplexCauchyCoreGroup τ (rawComplexCauchyCoreEncoding u) =
      rawComplexCauchyCoreEncoding (rawComplexCoreGroup τ u) := by
  change rawComplexCauchyCoreEncoding ((rawComplexCoreGroup τ)
    (rawComplexCauchyCoreEncoding.symm (rawComplexCauchyCoreEncoding u))) = _
  rw [rawComplexCauchyCoreEncoding.symm_apply_apply]

/-- Transported data evolution is literally the original Cauchy-compressed raw orbit. -/
theorem rawComplexCauchyCoreGroup_transport (τ : ℂ) (u : rawComplexEntireCore) :
    (rawComplexCauchyCoreGroup τ (rawComplexCauchyCoreEncoding u)).val =
      rawComplexCauchyCoreHierarchy 0 τ u := by
  rw [encoded_group_apply,rawComplexCauchyCoreEncoding_apply]
  rfl

/-- Opposite complex time reverses the exact encoded-data evolution algebraically. -/
theorem rawComplexCauchyCoreGroup_symm (τ : ℂ) :
    (rawComplexCauchyCoreGroup τ).symm = rawComplexCauchyCoreGroup (-τ) := by
  apply LinearEquiv.ext
  intro y
  obtain ⟨u,rfl⟩ := rawComplexCauchyCoreEncoding.surjective y
  change rawComplexCauchyCoreEncoding ((rawComplexCoreGroup τ).symm
    (rawComplexCauchyCoreEncoding.symm (rawComplexCauchyCoreEncoding u))) = _
  rw [rawComplexCauchyCoreEncoding.symm_apply_apply,rawComplexCoreGroup_symm,encoded_group_apply]

/-- The encoded data carry a genuine representation of the complex additive group. -/
def rawComplexCauchyCoreGroupHom : Multiplicative ℂ →*
    (rawComplexCauchyCoreRange ≃ₗ[ℂ] rawComplexCauchyCoreRange) where
  toFun τ := rawComplexCauchyCoreGroup τ.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro y
    obtain ⟨u,rfl⟩ := rawComplexCauchyCoreEncoding.surjective y
    change rawComplexCauchyCoreGroup 0 (rawComplexCauchyCoreEncoding u) = rawComplexCauchyCoreEncoding u
    rw [encoded_group_apply]
    exact congrArg rawComplexCauchyCoreEncoding (rawComplexCoreHierarchy_initial u)
  map_mul' τ σ := by
    apply LinearEquiv.ext
    intro y
    obtain ⟨u,rfl⟩ := rawComplexCauchyCoreEncoding.surjective y
    change rawComplexCauchyCoreGroup (τ.toAdd+σ.toAdd) (rawComplexCauchyCoreEncoding u) =
      rawComplexCauchyCoreGroup τ.toAdd (rawComplexCauchyCoreGroup σ.toAdd (rawComplexCauchyCoreEncoding u))
    rw [encoded_group_apply,encoded_group_apply,encoded_group_apply]
    apply congrArg rawComplexCauchyCoreEncoding
    change rawComplexCoreHierarchy 0 (τ.toAdd+σ.toAdd) u =
      rawComplexCoreHierarchy 0 τ.toAdd (rawComplexCoreHierarchy 0 σ.toAdd u)
    simpa only [zero_add] using (rawComplexCoreHierarchy_comp 0 0 τ.toAdd σ.toAdd u).symm

end
end RHTower.FokasLenells
