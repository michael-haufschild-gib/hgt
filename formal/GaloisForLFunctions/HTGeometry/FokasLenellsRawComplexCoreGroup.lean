import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexCore
import GaloisForLFunctions.HTGeometry.FokasLenellsRawComplexInversion

/-!
# Genuine raw complex-time evolution on the common entire core

The canonical cutoff witnesses provide concrete values, while almost-everywhere
raw multiplier identities prove that these values define linear maps independent
of the witness. Zeroth-order evolution is an actual complex additive-group
action by linear automorphisms; every vector has its genuine entire L² orbit.
-/

open MeasureTheory Complex Filter Topology Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private def coreWitness (u : rawComplexEntireCore) : ℝ × Lp ℂ 2 (volume : Measure ℝ) :=
  Classical.choose u.property

private theorem coreWitness_spec (u : rawComplexEntireCore) :
    rawComplexGraphCutoff (coreWitness u).1 (coreWitness u).2 = u.val :=
  Classical.choose_spec u.property

private def coreValue (u : rawComplexEntireCore) (n : ℕ) (τ : ℂ) : Lp ℂ 2 (volume : Measure ℝ) :=
  rawComplexCoreOrbit (coreWitness u).1 (coreWitness u).2 n τ

private theorem coreValue_ae (u : rawComplexEntireCore) (n : ℕ) (τ : ℂ) :
    (coreValue u n τ : ℝ → ℂ) =ᵐ[volume] fun z => rawComplexSymbol n τ z * u.val z := by
  have h := rawComplexCoreOrbit_ae (coreWitness u).1 (coreWitness u).2 n τ
  rw [coreWitness_spec] at h
  exact h

/-- The actual raw complex derivative hierarchy acting linearly on its common invariant core. -/
def rawComplexCoreHierarchy (n : ℕ) (τ : ℂ) : rawComplexEntireCore →ₗ[ℂ] rawComplexEntireCore where
  toFun u := ⟨coreValue u n τ,rawComplexCoreOrbit_mem_core (coreWitness u).1 (coreWitness u).2 n τ⟩
  map_add' u v := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coreValue_ae (u+v) n τ,coreValue_ae u n τ,coreValue_ae v n τ,
      Lp.coeFn_add u.val v.val,Lp.coeFn_add (coreValue u n τ) (coreValue v n τ)] with z h0 h1 h2 hi ho
    change coreValue (u+v) n τ z = (coreValue u n τ + coreValue v n τ) z
    rw [h0,ho,Pi.add_apply,h1,h2]
    change rawComplexSymbol n τ z * (u.val + v.val) z = _
    rw [hi,Pi.add_apply,mul_add]
  map_smul' c u := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coreValue_ae (c • u) n τ,coreValue_ae u n τ,
      Lp.coeFn_smul c u.val,Lp.coeFn_smul c (coreValue u n τ)] with z h0 h1 hi ho
    change coreValue (c • u) n τ z = (c • coreValue u n τ) z
    rw [h0,ho,Pi.smul_apply,h1]
    change rawComplexSymbol n τ z * (c • u.val) z = _
    rw [hi,Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

/-- The linear hierarchy is the literal raw multiplier on the original L² representatives. -/
theorem rawComplexCoreHierarchy_ae (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    ((rawComplexCoreHierarchy n τ u).val : ℝ → ℂ) =ᵐ[volume]
      fun z => rawComplexSymbol n τ z * u.val z := coreValue_ae u n τ

/-- Every core action value lies in the actual maximal raw graph with the unchanged input. -/
theorem rawComplexCoreHierarchy_mem_graph (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    (u.val,(rawComplexCoreHierarchy n τ u).val) ∈ rawComplexGraph n τ :=
  rawComplexCoreHierarchy_ae n τ u

/-- The actual zeroth core action at time zero is the identity. -/
theorem rawComplexCoreHierarchy_initial (u : rawComplexEntireCore) : rawComplexCoreHierarchy 0 0 u = u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [rawComplexCoreHierarchy_ae 0 0 u] with z hz
  simpa only [rawComplexSymbol_zero_zero,one_mul] using hz

/-- Literal raw core composition adds derivative orders and complex times. -/
theorem rawComplexCoreHierarchy_comp (n k : ℕ) (τ σ : ℂ) (u : rawComplexEntireCore) :
    rawComplexCoreHierarchy n τ (rawComplexCoreHierarchy k σ u) =
      rawComplexCoreHierarchy (n+k) (τ+σ) u := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [rawComplexCoreHierarchy_ae n τ (rawComplexCoreHierarchy k σ u),
    rawComplexCoreHierarchy_ae k σ u,rawComplexCoreHierarchy_ae (n+k) (τ+σ) u] with z h0 h1 h2
  rw [h0,h1,h2,← mul_assoc,rawComplexSymbol_mul]

/-- Real zeroth core evolution is exactly the original raw unitary evolution on L². -/
theorem rawComplexCoreHierarchy_zero_ofReal (t : ℝ) (u : rawComplexEntireCore) :
    (rawComplexCoreHierarchy 0 (t : ℂ) u).val = evolution t u.val := by
  apply Lp.ext
  filter_upwards [rawComplexCoreHierarchy_ae 0 (t : ℂ) u,evolution_ae t u.val] with z h0 h1
  rw [h0,h1,rawComplexSymbol_zero_ofReal]

/-- Real core evolution preserves the actual inherited Hilbert norm. -/
theorem norm_rawComplexCoreHierarchy_zero_ofReal (t : ℝ) (u : rawComplexEntireCore) :
    ‖rawComplexCoreHierarchy 0 (t : ℂ) u‖ = ‖u‖ := by
  change ‖(rawComplexCoreHierarchy 0 (t : ℂ) u).val‖ = ‖u.val‖
  rw [rawComplexCoreHierarchy_zero_ofReal]
  exact (evolution t).norm_map _

/-- Every actual core vector has a genuine L² derivative equal to the next raw action. -/
theorem rawComplexCoreHierarchy_hasDerivAt (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    HasDerivAt (fun σ => (rawComplexCoreHierarchy n σ u).val)
      (rawComplexCoreHierarchy (n+1) τ u).val τ :=
  rawComplexCoreOrbit_hasDerivAt (coreWitness u).1 (coreWitness u).2 n τ

/-- Every actual core vector has an entire L²-valued raw orbit at every order. -/
theorem rawComplexCoreHierarchy_analyticAt (n : ℕ) (τ : ℂ) (u : rawComplexEntireCore) :
    AnalyticAt ℂ (fun σ => (rawComplexCoreHierarchy n σ u).val) τ :=
  rawComplexCoreOrbit_analyticAt (coreWitness u).1 (coreWitness u).2 n τ

/-- The full hierarchy is the literal iterated L² derivative of the same actual raw orbit. -/
theorem iteratedDeriv_rawComplexCoreHierarchy (n : ℕ) (u : rawComplexEntireCore) :
    iteratedDeriv n (fun σ => (rawComplexCoreHierarchy 0 σ u).val) =
      (fun σ => (rawComplexCoreHierarchy n σ u).val) :=
  iteratedDeriv_rawComplexCoreOrbit (coreWitness u).1 (coreWitness u).2 n

/-- Actual raw complex-time evolution is a linear automorphism of the one common entire core. -/
def rawComplexCoreGroup (τ : ℂ) : rawComplexEntireCore ≃ₗ[ℂ] rawComplexEntireCore where
  toLinearMap := rawComplexCoreHierarchy 0 τ
  invFun := rawComplexCoreHierarchy 0 (-τ)
  left_inv u := by
    change rawComplexCoreHierarchy 0 (-τ) (rawComplexCoreHierarchy 0 τ u) = u
    rw [rawComplexCoreHierarchy_comp,zero_add,neg_add_cancel,rawComplexCoreHierarchy_initial]
  right_inv u := by
    change rawComplexCoreHierarchy 0 τ (rawComplexCoreHierarchy 0 (-τ) u) = u
    rw [rawComplexCoreHierarchy_comp,zero_add,add_neg_cancel,rawComplexCoreHierarchy_initial]

/-- Opposite complex time is the exact algebraic inverse on the common core. -/
theorem rawComplexCoreGroup_symm (τ : ℂ) :
    (rawComplexCoreGroup τ).symm = rawComplexCoreGroup (-τ) := by
  apply LinearEquiv.ext
  intro u
  rfl

/-- The core automorphisms form a genuine representation of the complex additive group. -/
def rawComplexCoreGroupHom : Multiplicative ℂ →* (rawComplexEntireCore ≃ₗ[ℂ] rawComplexEntireCore) where
  toFun τ := rawComplexCoreGroup τ.toAdd
  map_one' := by
    apply LinearEquiv.ext
    intro u
    exact rawComplexCoreHierarchy_initial u
  map_mul' τ σ := by
    apply LinearEquiv.ext
    intro u
    change rawComplexCoreHierarchy 0 (τ.toAdd + σ.toAdd) u =
      rawComplexCoreHierarchy 0 τ.toAdd (rawComplexCoreHierarchy 0 σ.toAdd u)
    simpa only [zero_add] using (rawComplexCoreHierarchy_comp 0 0 τ.toAdd σ.toAdd u).symm

end
end GaloisForLFunctions.HTGeometry.FokasLenells
