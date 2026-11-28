import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteTypeRetraction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothSubrepresentation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.InflatedCuspidalTypeMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.FiniteCuspidalTypeDual
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The dual of a finite inflated type maps injectively to the
smooth contragredient. The type retraction makes the map nonzero,
and the open congruence kernel fixes its image. -/

noncomputable section

open Module

namespace Representation

variable {G K Γ V W : Type*} [Group G] [Group K] [Group Γ] [Fintype Γ]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ G V) (ρ : Representation ℂ Γ W)
  (ι : K →* G) (q : K →* Γ)

theorem exists_finite_type_dual_map (hπ : ∀ v : V, IsOpen {g : G | π g v = v})
    (hq : Function.Surjective q) (hKc : IsCompact ((q.ker.map ι : Subgroup G) : Set G))
    (hKo : IsOpen ((q.ker.map ι : Subgroup G) : Set G))
    (j : W →ₗ[ℂ] V) (hj : Function.Injective j)
    (h : ∀ k w, j (ρ (q k) w) = π (ι k) (j w)) :
    ∃ J : Dual ℂ W →ₗ[ℂ] π.dual.smoothVectors, Function.Injective J ∧
      ∀ k l, J (ρ.dual (q k) l) = π.smoothDual (ι k) (J l) := by
  obtain ⟨P, hPj, hP⟩ := exists_finite_type_retraction π ρ ι q hπ hq hKc j hj h
  have hmem (l : Dual ℂ W) : P.dualMap l ∈ π.dual.smoothVectors := by
    rw [mem_smoothVectors]
    apply π.dual.isOpen_vectorStabilizer_of_open_subgroup (H := q.ker.map ι) hKo
    intro g hg
    obtain ⟨k, hk, rfl⟩ := hg
    apply LinearMap.ext
    intro x
    change l (P (π (ι k)⁻¹ x)) = l (P x)
    rw [← map_inv ι, hP k⁻¹ x, map_inv q, show q k = 1 from hk, inv_one, map_one, Module.End.one_apply]
  let J := P.dualMap.codRestrict π.dual.smoothVectors hmem
  refine ⟨J, ?_, fun k l => ?_⟩
  · intro l l' he
    apply LinearMap.ext
    intro w
    have e := congrArg (fun f : π.dual.smoothVectors => f.val (j w)) he
    have hw : P (j w) = w := LinearMap.congr_fun hPj w
    change l (P (j w)) = l' (P (j w)) at e
    rwa [hw] at e
  · apply Subtype.ext
    apply LinearMap.ext
    intro v
    change l (ρ (q k)⁻¹ (P v)) = l (P (π (ι k)⁻¹ v))
    rw [← map_inv ι, hP k⁻¹ v, map_inv q]

end Representation

open Matrix Representation GlobalTheory.GLq

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ G V) (τ : FDRep ℂ (Gn p n))

theorem hasInflatedType_smoothDual_comp (f : GL (Fin n) ℚ_[p] →* G)
    (hf : Continuous f) (hfo : IsOpenMap f)
    (hπ : ∀ v : V, IsOpen {g : G | π g v = v})
    (hτ : IsCusp τ.character) (ht : HasInflatedType (π.comp f) τ) :
    HasInflatedType (π.smoothDual.comp f) (finiteTypeDual τ) := by
  obtain ⟨j, hj₀, hj⟩ := ht
  let ι := f.comp (integralInclusion p (Fin n))
  let q := integralReduction p (Fin n)
  have he : ((q.ker.map ι : Subgroup G) : Set G) =
      f '' (principalCongruenceOne p (Fin n) : Set (GL (Fin n) ℚ_[p])) := by
    change ((q.ker.map (f.comp (integralInclusion p (Fin n))) : Subgroup G) : Set G) = _
    rw [← Subgroup.map_map]
    rfl
  have hKc : IsCompact ((q.ker.map ι : Subgroup G) : Set G) := by
    rw [he]
    exact (isCompact_principalCongruenceOne p (Fin n)).image hf
  have hKo : IsOpen ((q.ker.map ι : Subgroup G) : Set G) := by
    rw [he]
    exact hfo _ (isOpen_principalCongruenceOne p (Fin n))
  obtain ⟨J, hJ, hJint⟩ := exists_finite_type_dual_map π τ.ρ ι q hπ
    (integralReduction_surjective p (Fin n)) hKc hKo j
    (injective_of_cuspidal_type_map (π.comp f) τ hτ j hj₀ hj) hj
  refine ⟨J, ?_, hJint⟩
  have hw : ∃ w : τ, w ≠ 0 := by
    by_contra! h
    exact hj₀ (LinearMap.ext fun w => by rw [h w, map_zero, LinearMap.zero_apply])
  obtain ⟨w, hw⟩ := hw
  obtain ⟨l, hl⟩ := Module.Projective.exists_dual_ne_zero ℂ hw
  intro hz
  have hz' : J l = 0 := LinearMap.congr_fun hz l
  have he : l = 0 := hJ (hz'.trans (map_zero J).symm)
  exact hl (congrArg (fun m : Dual ℂ τ => m w) he)

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.hasInflatedType_smoothDual_comp
