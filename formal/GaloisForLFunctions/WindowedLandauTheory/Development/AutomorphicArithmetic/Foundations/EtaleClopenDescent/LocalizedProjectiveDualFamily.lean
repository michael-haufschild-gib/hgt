import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Finiteness.Projective

/-! A finite projective lattice gives a finite dual family on its
generic fibre. -/

noncomputable section

namespace GlobalTheory.PD

variable {A F M W : Type*} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
  [IsFractionRing A F] [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
  [AddCommGroup W] [Module A W] [Module F W] [IsScalarTower A F W]

/-- Extend a finite projective splitting to the fraction field. Its
coordinate functions are integral on the original lattice. -/
theorem exists_localized_projective_dual_family (u : M →ₗ[A] W)
    [IsLocalizedModule (nonZeroDivisors A) u] :
    ∃ (n : ℕ) (v : Fin n → M) (φ : Fin n → W →ₗ[F] F),
      (∀ i m, φ i (u m) ∈ (algebraMap A F).range) ∧
      ∀ w : W, w = ∑ i, φ i w • u (v i) := by
  classical
  let S := nonZeroDivisors A
  obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective A M
  let ψ (i : Fin n) : M →ₗ[A] F := (Algebra.linearMap A F).comp ((LinearMap.proj i).comp g)
  have hunit (s : S) : IsUnit (algebraMap A (Module.End A F) (s : A)) :=
    IsLocalizedModule.map_units (S := S) (f := Algebra.linearMap A F) s
  let φ (i : Fin n) : W →ₗ[F] F :=
    (IsLocalizedModule.lift S u (ψ i) hunit).extendScalarsOfIsLocalization S F
  have hφ (i : Fin n) (m : M) : φ i (u m) = algebraMap A F (g m i) :=
    IsLocalizedModule.lift_apply S u (ψ i) hunit m
  let v (i : Fin n) := f (Pi.single i 1)
  let T : W →ₗ[F] W := ∑ i, (φ i).smulRight (u (v i))
  have he : (LinearMap.id : W →ₗ[F] W).restrictScalars A = T.restrictScalars A := by
    apply IsLocalizedModule.ext S u (fun s => IsLocalizedModule.map_units (S := S) (f := u) s)
    ext m
    change u m = T (u m)
    have hm : f (g m) = m := LinearMap.congr_fun hfg m
    have hg : g m = ∑ i, (g m i) • (Pi.single i (1 : A) : Fin n → A) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    calc
      u m = u (f (g m)) := congrArg u hm.symm
      _ = u (f (∑ i, (g m i) • (Pi.single i (1 : A) : Fin n → A))) :=
        congrArg (fun b => u (f b)) hg
      _ = ∑ i, (g m i) • u (v i) := by rw [map_sum, map_sum]; simp only [map_smul, v]
      _ = T (u m) := by
        simp only [T, LinearMap.sum_apply, LinearMap.smulRight_apply, hφ, IsScalarTower.algebraMap_smul F]
  refine ⟨n, v, φ, fun i m => ⟨g m i, (hφ i m).symm⟩, fun w => ?_⟩
  have hw : w = T w := LinearMap.congr_fun he w
  simpa only [T, LinearMap.sum_apply, LinearMap.smulRight_apply] using hw

end GlobalTheory.PD
