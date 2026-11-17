import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeWalkFiniteness
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Spectral transport between the probe signal and its reflection walk

The doubled probe span covers the reflection hull and carries a companion
operator for the compressed signal. Away from the two reflection endpoints,
the lift `v ↦ ζ Rv - v` identifies signal and walk eigenspaces.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- The compressed reflection as an endomorphism of the original probe span. -/
def probeSignal : Module.End ℂ (probeSpace p) where
  toFun v := ⟨probeProjection p (zeroReflection v),
    (probeSpace p).starProjection_apply_mem _⟩
  map_add' v w := Subtype.ext (by simp only [Submodule.coe_add, map_add])
  map_smul' c v := Subtype.ext (by simp only [Submodule.coe_smul, map_smul, RingHom.id_apply])

@[simp] theorem probeSignal_apply (v : probeSpace p) :
    (probeSignal p v : ZeroSpace) = probeProjection p (zeroReflection v) := rfl

/-- Two copies of the probe span generate the full active state space. -/
def doubledProbeCover : ((probeSpace p) × (probeSpace p)) →ₗ[ℂ] reflectionHull p where
  toFun v := ⟨(v.1 : ZeroSpace) + zeroReflection v.2,
    (reflectionHull p).add_mem (probeSpace_le_reflectionHull p v.1.property)
      (zeroReflection_mem_reflectionHull p (probeSpace_le_reflectionHull p v.2.property))⟩
  map_add' v w := Subtype.ext (by
    change ((v.1 : ZeroSpace) + w.1) + zeroReflection ((v.2 : ZeroSpace) + w.2) =
      ((v.1 : ZeroSpace) + zeroReflection v.2) + ((w.1 : ZeroSpace) + zeroReflection w.2)
    rw [map_add]
    abel)
  map_smul' c v := Subtype.ext (by simp only [Prod.smul_fst, Prod.smul_snd,
    Submodule.coe_smul, map_smul, smul_add, RingHom.id_apply])

theorem doubledProbeCover_surjective : Function.Surjective (doubledProbeCover p) := by
  intro x
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp x.property
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv
  exact ⟨(⟨u, hu⟩, ⟨w, hw⟩), Subtype.ext huv⟩

/-- The signal's companion operator on the doubled probe span. -/
def doubledProbeWalk : Module.End ℂ ((probeSpace p) × (probeSpace p)) where
  toFun v := (-v.2, v.1 + (2 : ℂ) • probeSignal p v.2)
  map_add' v w := by
    apply Prod.ext
    · exact neg_add v.2 w.2
    · change v.1 + w.1 + (2 : ℂ) • probeSignal p (v.2 + w.2) =
        (v.1 + (2 : ℂ) • probeSignal p v.2) + (w.1 + (2 : ℂ) • probeSignal p w.2)
      rw [map_add, smul_add]
      abel
  map_smul' c v := by
    apply Prod.ext
    · exact (smul_neg c v.2).symm
    · change c • v.1 + (2 : ℂ) • probeSignal p (c • v.2) =
        c • (v.1 + (2 : ℂ) • probeSignal p v.2)
      rw [map_smul, smul_add, smul_comm (2 : ℂ) c]

/-- The doubled signal model descends to the actual reflection walk. -/
theorem doubledProbeCover_intertwines (v : (probeSpace p) × (probeSpace p)) :
    doubledProbeCover p (doubledProbeWalk p v) = hullWalk p (doubledProbeCover p v) := by
  apply Subtype.ext
  have hq : probeProjection p (v.1 : ZeroSpace) = v.1 :=
    Submodule.starProjection_eq_self_iff.mpr v.1.property
  change -(v.2 : ZeroSpace) + zeroReflection ((v.1 : ZeroSpace) +
    (2 : ℂ) • probeProjection p (zeroReflection v.2)) =
    zeroReflection (probeProjection p ((v.1 : ZeroSpace) + zeroReflection v.2) +
      probeProjection p ((v.1 : ZeroSpace) + zeroReflection v.2) -
      ((v.1 : ZeroSpace) + zeroReflection v.2))
  rw [map_add, map_smul, map_add, hq, map_sub, map_add, map_add,
    map_add, zeroReflection_involutive]
  module

/-- The Joukowski parameter of a nonzero walk eigenvalue. -/
def signalParameter (ζ : ℂ) : ℂ := (ζ + ζ⁻¹) / 2

/-- Lift from the signal space to the reflection hull at a spectral parameter. -/
def signalEigenLift (ζ : ℂ) : (probeSpace p) →ₗ[ℂ] reflectionHull p :=
  ζ • (hullReflection p).comp (Submodule.inclusion (probeSpace_le_reflectionHull p)) -
    Submodule.inclusion (probeSpace_le_reflectionHull p)

private theorem lift_projection {ζ : ℂ} (hζ : ζ ≠ 0) (v : probeSpace p)
    (hv : probeSignal p v = signalParameter ζ • v) :
    probeProjection p ((signalEigenLift p ζ v : reflectionHull p) : ZeroSpace) =
      ((ζ ^ 2 - 1) / 2) • (v : ZeroSpace) := by
  have he := congrArg (fun w : probeSpace p => (w : ZeroSpace)) hv
  change probeProjection p (zeroReflection v) = signalParameter ζ • (v : ZeroSpace) at he
  have hq : probeProjection p (v : ZeroSpace) = v :=
    Submodule.starProjection_eq_self_iff.mpr v.property
  change probeProjection p (ζ • zeroReflection v - (v : ZeroSpace)) = _
  rw [map_sub, map_smul, he, hq, smul_smul]
  have hs : ζ * signalParameter ζ - 1 = (ζ ^ 2 - 1) / 2 := by
    unfold signalParameter
    field_simp [hζ]
    ring
  calc
    _ = (ζ * signalParameter ζ - 1) • (v : ZeroSpace) := by rw [sub_smul, one_smul]
    _ = _ := by rw [hs]

/-- Signal eigenvectors lift to genuine walk eigenvectors. -/
theorem signalEigenLift_eigen {ζ : ℂ} (hζ : ζ ≠ 0) (v : probeSpace p)
    (hv : probeSignal p v = signalParameter ζ • v) :
    hullWalk p (signalEigenLift p ζ v) = ζ • signalEigenLift p ζ v := by
  apply Subtype.ext
  change zeroReflection (probeProjection p (ζ • zeroReflection v - (v : ZeroSpace)) +
    probeProjection p (ζ • zeroReflection v - (v : ZeroSpace)) -
      (ζ • zeroReflection v - (v : ZeroSpace))) =
    ζ • (ζ • zeroReflection v - (v : ZeroSpace))
  rw [show probeProjection p (ζ • zeroReflection v - (v : ZeroSpace)) =
      ((ζ ^ 2 - 1) / 2) • (v : ZeroSpace) from lift_projection p hζ v hv]
  simp only [map_sub, map_add, map_smul, zeroReflection_involutive]
  module

private theorem walk_eigen_reconstruction {ζ : ℂ} (x : reflectionHull p)
    (hx : hullWalk p x = ζ • x) :
    ζ • zeroReflection (probeProjection p (x : ZeroSpace)) -
      probeProjection p (x : ZeroSpace) = ((ζ ^ 2 - 1) / 2) • (x : ZeroSpace) := by
  have hw := congrArg (fun y : reflectionHull p => (y : ZeroSpace)) hx
  change zeroReflection (probeProjection p (x : ZeroSpace) +
    probeProjection p (x : ZeroSpace) - (x : ZeroSpace)) = ζ • (x : ZeroSpace) at hw
  have hr := congrArg zeroReflection hw
  rw [zeroReflection_involutive, map_smul] at hr
  rw [map_sub, map_add] at hw
  have h := congrArg (fun y : ZeroSpace => ζ • y) hw
  have hr' : ζ • zeroReflection x = probeProjection p (x : ZeroSpace) +
      probeProjection p (x : ZeroSpace) - (x : ZeroSpace) := hr.symm
  rw [smul_sub, smul_add, hr'] at h
  calc
    _ = (1 / 2 : ℂ) • ((ζ • zeroReflection (probeProjection p (x : ZeroSpace)) +
        ζ • zeroReflection (probeProjection p (x : ZeroSpace)) -
        (probeProjection p (x : ZeroSpace) + probeProjection p (x : ZeroSpace) -
          (x : ZeroSpace))) - (x : ZeroSpace)) := by module
    _ = (1 / 2 : ℂ) • (ζ • (ζ • (x : ZeroSpace)) - (x : ZeroSpace)) := by rw [h]
    _ = _ := by module

/-- Projection sends walk eigenvectors to the matching signal eigenspace. -/
theorem walkEigen_projection {ζ : ℂ} (hζ : ζ ≠ 0) (x : reflectionHull p)
    (hx : hullWalk p x = ζ • x) :
    probeSignal p ⟨probeProjection p (x : ZeroSpace),
      (probeSpace p).starProjection_apply_mem _⟩ =
        signalParameter ζ • ⟨probeProjection p (x : ZeroSpace),
          (probeSpace p).starProjection_apply_mem _⟩ := by
  apply Subtype.ext
  have h := congrArg (probeProjection p) (walk_eigen_reconstruction p x hx)
  have hq : probeProjection p (probeProjection p (x : ZeroSpace)) = probeProjection p x :=
    Submodule.starProjection_eq_self_iff.mpr ((probeSpace p).starProjection_apply_mem _)
  rw [map_sub, map_smul, map_smul, hq] at h
  change probeProjection p (zeroReflection (probeProjection p (x : ZeroSpace))) =
    signalParameter ζ • probeProjection p (x : ZeroSpace)
  have hs : ζ * signalParameter ζ = ((ζ ^ 2 - 1) / 2) + 1 := by
    unfold signalParameter
    field_simp [hζ]
    ring
  have he : ζ • probeProjection p (zeroReflection (probeProjection p (x : ZeroSpace))) =
      ζ • (signalParameter ζ • probeProjection p (x : ZeroSpace)) := by
    rw [smul_smul, hs, add_smul, one_smul]
    exact sub_eq_iff_eq_add.mp h
  have hi := congrArg (fun y : ZeroSpace => ζ⁻¹ • y) he
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hζ, one_mul, one_smul] using hi

/-- Away from the reflection endpoints, signal and walk eigenspaces are explicitly isomorphic. -/
def walkSignalEigenspaceEquiv {ζ : ℂ} (hζ : ζ ≠ 0) (hζ₂ : ζ ^ 2 ≠ 1) :
    (probeSignal p).eigenspace (signalParameter ζ) ≃ₗ[ℂ] (hullWalk p).eigenspace ζ where
  toFun v := ⟨signalEigenLift p ζ v.val,
    Module.End.mem_eigenspace_iff.mpr (signalEigenLift_eigen p hζ v.val
      (Module.End.mem_eigenspace_iff.mp v.property))⟩
  invFun x := ⟨(((ζ ^ 2 - 1) / 2)⁻¹ : ℂ) •
      (⟨probeProjection p (x.val : ZeroSpace),
        (probeSpace p).starProjection_apply_mem _⟩ : probeSpace p),
    ((probeSignal p).eigenspace (signalParameter ζ)).smul_mem _
      (Module.End.mem_eigenspace_iff.mpr (walkEigen_projection p hζ x.val
        (Module.End.mem_eigenspace_iff.mp x.property)))⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    change (((ζ ^ 2 - 1) / 2)⁻¹ : ℂ) •
      probeProjection p ((signalEigenLift p ζ v.val : reflectionHull p) : ZeroSpace) =
        (v.val : ZeroSpace)
    rw [lift_projection p hζ v.val (Module.End.mem_eigenspace_iff.mp v.property), smul_smul,
      inv_mul_cancel₀ (div_ne_zero (sub_ne_zero.mpr hζ₂) (by norm_num)), one_smul]
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change ζ • zeroReflection ((((ζ ^ 2 - 1) / 2)⁻¹ : ℂ) •
      probeProjection p (x.val : ZeroSpace)) -
        (((ζ ^ 2 - 1) / 2)⁻¹ : ℂ) • probeProjection p (x.val : ZeroSpace) =
          (x.val : ZeroSpace)
    rw [map_smul, smul_comm ζ, ← smul_sub,
      walk_eigen_reconstruction p x.val (Module.End.mem_eigenspace_iff.mp x.property),
      smul_smul, inv_mul_cancel₀ (div_ne_zero (sub_ne_zero.mpr hζ₂) (by norm_num)), one_smul]
  map_add' v w := Subtype.ext (map_add (signalEigenLift p ζ) v.val w.val)
  map_smul' c v := Subtype.ext (map_smul (signalEigenLift p ζ) c v.val)

/-- The spectral lift preserves every non-endpoint geometric multiplicity. -/
theorem walk_signal_eigen_multiplicity {ζ : ℂ} (hζ : ζ ≠ 0) (hζ₂ : ζ ^ 2 ≠ 1) :
    Module.finrank ℂ ((hullWalk p).eigenspace ζ) =
      Module.finrank ℂ ((probeSignal p).eigenspace (signalParameter ζ)) :=
  (walkSignalEigenspaceEquiv p hζ hζ₂).finrank_eq.symm

#print axioms doubledProbeCover_intertwines
#print axioms signalEigenLift_eigen
#print axioms walkEigen_projection
#print axioms walkSignalEigenspaceEquiv
#print axioms walk_signal_eigen_multiplicity
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
