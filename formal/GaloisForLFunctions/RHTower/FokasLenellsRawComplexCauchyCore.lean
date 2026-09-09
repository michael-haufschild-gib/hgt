import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexCoreContinuity
import GaloisForLFunctions.RHTower.FokasLenellsCauchyModulation

/-!
# Cauchy compression on the common raw entire core

Modulation preserves the one common core and commutes with every actual raw
multiplier. Sending that modulation into the selected Hardy direction recovers
the full raw output norm. Thus Cauchy compression preserves every uniform norm
bound on the core, including the exact boundedness and continuous-extension gate.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

private theorem core_cutoff_ae (a : ℝ) (u : SoninL2) :
    (rawComplexGraphCutoff a u : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexGraphCutoffSymbol a z * u z := by
  unfold rawComplexGraphCutoff
  exact lpBoundedMulCLM_coeFn _ _ _ _

private theorem core_cutoff_modulation (a b : ℝ) (u : SoninL2) :
    rawComplexGraphCutoff a (modulationMul b u) = modulationMul b (rawComplexGraphCutoff a u) := by
  apply Lp.ext
  filter_upwards [core_cutoff_ae a (modulationMul b u),coeFn_modulationMul b u,
    coeFn_modulationMul b (rawComplexGraphCutoff a u),core_cutoff_ae a u] with z h0 h1 h2 h3
  rw [h0,h1,h2,h3]
  ring

private theorem core_modulation_mem (a : ℝ) (u : rawComplexEntireCore) :
    modulationMul a u.val ∈ rawComplexEntireCore := by
  obtain ⟨⟨b,w⟩,hw⟩ := u.property
  change rawComplexGraphCutoff b w = u.val at hw
  refine ⟨(b,modulationMul a w),?_⟩
  change rawComplexGraphCutoff b (modulationMul a w) = modulationMul a u.val
  rw [core_cutoff_modulation,hw]

/-- The Fourier modulation probe is an actual linear isometry of the common entire core. -/
def rawComplexCoreModulation (a : ℝ) : rawComplexEntireCore →ₗᵢ[ℂ] rawComplexEntireCore where
  toFun u := ⟨modulationMul a u.val,core_modulation_mem a u⟩
  map_add' u v := by apply Subtype.ext; exact (modulationMul a).map_add _ _
  map_smul' c u := by apply Subtype.ext; exact (modulationMul a).map_smul _ _
  norm_map' u := norm_modulationMul_eq a u.val

/-- Every actual raw core multiplier commutes with the norm-preserving modulation probe. -/
theorem rawComplexCoreHierarchy_commutes_modulation (n : ℕ) (τ : ℂ) (a : ℝ) (u : rawComplexEntireCore) :
    (rawComplexCoreHierarchy n τ (rawComplexCoreModulation a u)).val =
      modulationMul a (rawComplexCoreHierarchy n τ u).val := by
  apply Lp.ext
  filter_upwards [rawComplexCoreHierarchy_ae n τ (rawComplexCoreModulation a u),
    coeFn_modulationMul a u.val,coeFn_modulationMul a (rawComplexCoreHierarchy n τ u).val,
    rawComplexCoreHierarchy_ae n τ u] with z h0 h1 h2 h3
  rw [h0,h2,h3]
  change rawComplexSymbol n τ z * modulationMul a u.val z = _
  rw [h1]
  ring

/-- The actual Cauchy-compressed raw hierarchy on the common core, with its original L² output. -/
def rawComplexCauchyCoreHierarchy (n : ℕ) (τ : ℂ) : rawComplexEntireCore →ₗ[ℂ] SoninL2 :=
  negativeCauchy.toLinearMap.comp (rawComplexEntireCore.subtype.comp (rawComplexCoreHierarchy n τ))

/-- Real zeroth Cauchy core evolution is the original Cauchy evolution on the unchanged input. -/
theorem rawComplexCauchyCoreHierarchy_zero_ofReal (t : ℝ) (u : rawComplexEntireCore) :
    rawComplexCauchyCoreHierarchy 0 (t : ℂ) u = cauchyEvolution t u.val := by
  change negativeCauchy (rawComplexCoreHierarchy 0 (t : ℂ) u).val = _
  rw [rawComplexCoreHierarchy_zero_ofReal]
  rfl

/-- Actual L² differentiation of the Cauchy core orbit advances its raw order. -/
theorem rawComplexCauchyCoreHierarchy_hasDerivAt (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    HasDerivAt (fun σ => rawComplexCauchyCoreHierarchy n σ u)
      (rawComplexCauchyCoreHierarchy (n+1) τ u) τ :=
  negativeCauchy.hasFDerivAt.comp_hasDerivAt τ (rawComplexCoreHierarchy_hasDerivAt n τ u)

/-- Every Cauchy-compressed actual core orbit remains entire as an L²-valued function. -/
theorem rawComplexCauchyCoreHierarchy_analyticAt (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    AnalyticAt ℂ (fun σ => rawComplexCauchyCoreHierarchy n σ u) τ :=
  (negativeCauchy.analyticAt _).comp (rawComplexCoreHierarchy_analyticAt n τ u)

/-- All Cauchy core orders are literal iterated derivatives of the same entire orbit. -/
theorem iteratedDeriv_rawComplexCauchyCoreHierarchy (n : ℕ) (u : rawComplexEntireCore) :
    iteratedDeriv n (fun σ => rawComplexCauchyCoreHierarchy 0 σ u) =
      (fun σ => rawComplexCauchyCoreHierarchy n σ u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext τ
    exact (rawComplexCauchyCoreHierarchy_hasDerivAt n τ u).deriv

/-- Core-preserving modulation recovers the full uncompressed raw output norm. -/
theorem rawComplexCauchyCoreHierarchy_modulation_norm_tendsto (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    Tendsto (fun a : ℝ => ‖rawComplexCauchyCoreHierarchy n τ (rawComplexCoreModulation a u)‖)
      atBot (𝓝 ‖rawComplexCoreHierarchy n τ u‖) := by
  change Tendsto (fun a : ℝ => ‖rawComplexCauchyCoreHierarchy n τ (rawComplexCoreModulation a u)‖)
    atBot (𝓝 ‖(rawComplexCoreHierarchy n τ u).val‖)
  have he (a : ℝ) : rawComplexCauchyCoreHierarchy n τ (rawComplexCoreModulation a u) =
      negativeCauchy (modulationMul a (rawComplexCoreHierarchy n τ u).val) := by
    change negativeCauchy (rawComplexCoreHierarchy n τ (rawComplexCoreModulation a u)).val = _
    rw [rawComplexCoreHierarchy_commutes_modulation]
  simpa only [he] using negativeCauchy_modulation_norm_tendsto (rawComplexCoreHierarchy n τ u).val

/-- Cauchy compression preserves every proposed uniform core norm bound, with the exact same constant. -/
theorem rawComplexCauchyCoreHierarchy_bound_iff (n : ℕ) (τ : ℂ) (B : ℝ) :
    (∀ u : rawComplexEntireCore, ‖rawComplexCauchyCoreHierarchy n τ u‖ ≤ B * ‖u‖) ↔
      (∀ u : rawComplexEntireCore, ‖rawComplexCoreHierarchy n τ u‖ ≤ B * ‖u‖) := by
  constructor
  · intro h u
    apply le_of_tendsto (rawComplexCauchyCoreHierarchy_modulation_norm_tendsto n τ u)
    apply Eventually.of_forall
    intro a
    simpa only [(rawComplexCoreModulation a).norm_map] using h (rawComplexCoreModulation a u)
  · intro h u
    exact (negativeCauchy_bound (rawComplexCoreHierarchy n τ u).val).trans (h u)

/-- Cauchy compression leaves the exact raw core boundedness gate unchanged. -/
theorem rawComplexCauchyCoreHierarchy_bounded_iff (n : ℕ) (τ : ℂ) :
    (∃ B : ℝ, ∀ u : rawComplexEntireCore, ‖rawComplexCauchyCoreHierarchy n τ u‖ ≤ B * ‖u‖) ↔
      n = 0 ∧ τ.im = 0 := by
  simp only [rawComplexCauchyCoreHierarchy_bound_iff,rawComplexCoreHierarchy_bounded_iff]

/-- Outside the same sharp gate, Cauchy core outputs exceed every proposed norm bound. -/
theorem rawComplexCauchyCoreHierarchy_unbounded_growth_iff (n : ℕ) (τ : ℂ) :
    (∀ B : ℝ, ∃ u : rawComplexEntireCore, B * ‖u‖ < ‖rawComplexCauchyCoreHierarchy n τ u‖) ↔
      n ≠ 0 ∨ τ.im ≠ 0 := by
  simpa only [not_exists,not_forall,not_le,not_and_or] using
    not_congr (rawComplexCauchyCoreHierarchy_bounded_iff n τ)

/-- Actual Cauchy core continuity in the inherited L² norm holds exactly at real zeroth order. -/
theorem rawComplexCauchyCoreHierarchy_continuous_iff (n : ℕ) (τ : ℂ) :
    Continuous (rawComplexCauchyCoreHierarchy n τ) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · intro hc
    let T : rawComplexEntireCore →L[ℂ] SoninL2 := ⟨rawComplexCauchyCoreHierarchy n τ,hc⟩
    exact (rawComplexCauchyCoreHierarchy_bounded_iff n τ).1 ⟨‖T‖,fun u => T.le_opNorm u⟩
  · intro h
    exact ((rawComplexCauchyCoreHierarchy n τ).mkContinuousOfExistsBound
      ((rawComplexCauchyCoreHierarchy_bounded_iff n τ).2 h)).continuous

private theorem good_cauchy_core_value (n : ℕ) (τ : ℂ) (hn : n = 0) (hi : τ.im = 0)
    (u : rawComplexEntireCore) : rawComplexCauchyCoreHierarchy n τ u = cauchyEvolution τ.re u.val := by
  have he : τ = (τ.re : ℂ) := by apply Complex.ext <;> simp [hi]
  rw [hn,he,rawComplexCauchyCoreHierarchy_zero_ofReal,Complex.ofReal_re]

/-- Every continuous Cauchy extension is uniquely the original real-time Cauchy evolution. -/
theorem rawComplexCauchyCoreHierarchy_extension_iff (n : ℕ) (τ : ℂ) (T : SoninL2 →L[ℂ] SoninL2) :
    (∀ u : rawComplexEntireCore, T u.val = rawComplexCauchyCoreHierarchy n τ u) ↔
      n = 0 ∧ τ.im = 0 ∧ T = cauchyEvolution τ.re := by
  constructor
  · intro h
    have hg : n = 0 ∧ τ.im = 0 := (rawComplexCauchyCoreHierarchy_bounded_iff n τ).1
      ⟨‖T‖,fun u => by rw [← h u]; exact T.le_opNorm _⟩
    refine ⟨hg.1,hg.2,?_⟩
    apply ContinuousLinearMap.ext
    intro u
    have hsub : (rawComplexEntireCore : Set SoninL2) ⊆ {u | T u = cauchyEvolution τ.re u} := by
      intro u hu
      exact (h ⟨u,hu⟩).trans (good_cauchy_core_value n τ hg.1 hg.2 ⟨u,hu⟩)
    exact closure_minimal hsub (isClosed_eq T.continuous (cauchyEvolution τ.re).continuous)
      (dense_rawComplexEntireCore u)
  · rintro ⟨hn,hi,rfl⟩ u
    exact (good_cauchy_core_value n τ hn hi u).symm

/-- Cauchy compression permits a bounded full-Hilbert extension exactly at real zeroth order. -/
theorem rawComplexCauchyCoreHierarchy_has_continuous_extension_iff (n : ℕ) (τ : ℂ) :
    (∃ T : SoninL2 →L[ℂ] SoninL2, ∀ u : rawComplexEntireCore,
      T u.val = rawComplexCauchyCoreHierarchy n τ u) ↔ n = 0 ∧ τ.im = 0 := by
  constructor
  · rintro ⟨T,hT⟩
    have h := (rawComplexCauchyCoreHierarchy_extension_iff n τ T).1 hT
    exact ⟨h.1,h.2.1⟩
  · intro h
    refine ⟨cauchyEvolution τ.re,?_⟩
    exact (rawComplexCauchyCoreHierarchy_extension_iff n τ _).2 ⟨h.1,h.2,rfl⟩

end
end RHTower.FokasLenells
