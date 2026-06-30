/-
# Fundamental group via a simply-connected (universal) cover

For a covering map `p : E → X` whose total space `E` is simply connected (the universal cover), the
**monodromy orbit map** `π₁(X, x₀) → p⁻¹{x₀}`, `[γ] ↦` (endpoint of the lift of `γ` from `e₀`), is a
bijection. Injectivity uses that two lifts with the same endpoints are homotopic in the simply-connected
`E`; surjectivity uses path-connectedness of `E`.

This abstracts the `π₁(ℂ*) ≅ ℤ` computation (`Pi1CMinusZero`) so it can be reused for the exterior
`escapeOpen` and the escape levels, each of which has an explicit universal cover by `exp` from a convex
half-plane preimage.
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

open Topology unitInterval

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [SimplyConnectedSpace E] {p : E → X} (cov : IsCoveringMap p)

/-- The monodromy orbit map `π₁(X, x₀) → p⁻¹{x₀}` of a covering with simply-connected total space. -/
noncomputable def orbit (x₀ : X) (e₀ : p ⁻¹' {x₀})
    (γ : Path.Homotopic.Quotient x₀ x₀) : p ⁻¹' {x₀} :=
  cov.monodromy γ e₀

/-- **Surjectivity** of the orbit map (uses `E` path-connected). -/
theorem orbit_surjective (x₀ : X) (e₀ : p ⁻¹' {x₀}) :
    Function.Surjective (cov.orbit x₀ e₀) := by
  intro e
  have hp1 : p (e : E) = x₀ := (Set.mem_singleton_iff).mp e.2
  have hp0 : p (e₀ : E) = x₀ := (Set.mem_singleton_iff).mp e₀.2
  set Γ : Path (e₀ : E) (e : E) := PathConnectedSpace.somePath (e₀ : E) (e : E) with hΓ
  set q : Path x₀ x₀ := (Γ.map cov.continuous).cast hp0.symm hp1.symm with hq
  refine ⟨⟦q⟧, ?_⟩
  apply Subtype.ext
  have hlift : p ∘ (Γ.toContinuousMap) = q := by
    funext t; show p (Γ t) = q t; rw [hq, Path.cast_coe, Path.map_coe]; rfl
  have h0 : (Γ.toContinuousMap) 0 = (e₀ : E) := Γ.source
  have heq : (Γ.toContinuousMap) = cov.liftPath q (e₀ : E) ((q.source).trans e₀.2.symm) :=
    (cov.eq_liftPath_iff' _).mpr ⟨hlift, h0⟩
  show (cov.monodromy ⟦q⟧ e₀ : E) = (e : E)
  have hcomp : (cov.monodromy ⟦q⟧ e₀ : E)
      = (cov.liftPath q (e₀ : E) ((q.source).trans e₀.2.symm)) 1 := rfl
  rw [hcomp, ← heq]
  exact Γ.target

/-- **Injectivity** of the orbit map (uses `E` simply connected). -/
theorem orbit_injective (x₀ : X) (e₀ : p ⁻¹' {x₀}) :
    Function.Injective (cov.orbit x₀ e₀) := by
  intro a b hab
  induction a using Quotient.inductionOn with
  | _ pa =>
  induction b using Quotient.inductionOn with
  | _ pb =>
  apply Quotient.sound
  set Γa : C(I, E) := cov.liftPath pa (e₀ : E) ((pa.source).trans e₀.2.symm)
  set Γb : C(I, E) := cov.liftPath pb (e₀ : E) ((pb.source).trans e₀.2.symm)
  have hla : p ∘ Γa = pa := cov.liftPath_lifts pa (e₀ : E) _
  have hlb : p ∘ Γb = pb := cov.liftPath_lifts pb (e₀ : E) _
  have h0a : Γa 0 = (e₀ : E) := cov.liftPath_zero pa (e₀ : E) _
  have h0b : Γb 0 = (e₀ : E) := cov.liftPath_zero pb (e₀ : E) _
  have hend : Γa 1 = Γb 1 := congrArg Subtype.val hab
  set Pa : Path (e₀ : E) (Γa 1) := ⟨Γa, h0a, rfl⟩
  set Pb : Path (e₀ : E) (Γa 1) := ⟨Γb, h0b, hend.symm⟩
  have hHom : Pa.Homotopic Pb := SimplyConnectedSpace.paths_homotopic Pa Pb
  have hmap := hHom.map ⟨p, cov.continuous⟩
  have h1 : x₀ = p (e₀ : E) := ((Set.mem_singleton_iff).mp e₀.2).symm
  have h2 : x₀ = p (Γa 1) := ((congr_fun hla 1).trans pa.target).symm
  have hcastA : (Pa.map (ContinuousMap.continuous ⟨p, cov.continuous⟩)).cast h1 h2 = pa := by
    apply Path.ext; funext t; exact congr_fun hla t
  have hcastB : (Pb.map (ContinuousMap.continuous ⟨p, cov.continuous⟩)).cast h1 h2 = pb := by
    apply Path.ext; funext t; exact congr_fun hlb t
  have hcast := Path.Homotopic.pathCast hmap h1 h2
  rwa [hcastA, hcastB] at hcast

/-- **The monodromy orbit map `π₁(X, x₀) ≃ p⁻¹{x₀}`** of a covering with simply-connected total
space. -/
noncomputable def pi1FiberEquiv (x₀ : X) (e₀ : p ⁻¹' {x₀}) :
    Path.Homotopic.Quotient x₀ x₀ ≃ p ⁻¹' {x₀} :=
  Equiv.ofBijective (cov.orbit x₀ e₀) ⟨cov.orbit_injective x₀ e₀, cov.orbit_surjective x₀ e₀⟩

end IsCoveringMap
