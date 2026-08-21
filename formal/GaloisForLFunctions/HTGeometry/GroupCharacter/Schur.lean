import GaloisForLFunctions.HTGeometry.GroupCharacter.Character
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Schur's lemma and the trivial summand

* `schur` — a `ℂ`-linear endomorphism of a minimal `G`-stable subspace of `ℂ[G]` that commutes with
  the `G`-action is a scalar.
* `sumRho_dichotomy` — on a minimal `G`-stable subspace, `∑_{g} rho g` is either `#G` times the
  identity (exactly when the action is trivial) or zero.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

/-- `N` is a minimal nonzero `G`-stable subspace of the group algebra. -/
structure IsMinimalGStable (N : Submodule ℂ (MonoidAlgebra ℂ G)) : Prop where
  stable : IsGStable G N
  ne_bot : N ≠ ⊥
  minimal : ∀ W : Submodule ℂ (MonoidAlgebra ℂ G), IsGStable G W → W ≤ N → W = ⊥ ∨ W = N

/-- **Schur's lemma.** -/
theorem schur {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N)
    (T : ↥N →ₗ[ℂ] ↥N) (hT : ∀ g : G, (rho hN.stable g) ∘ₗ T = T ∘ₗ (rho hN.stable g)) :
    ∃ c : ℂ, ∀ v : ↥N, T v = c • v := by
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hN.ne_bot
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := ↥N) T
  refine ⟨c, ?_⟩
  have hEbot : (Module.End.eigenspace T c) ≠ ⊥ := hc
  have hWle : (Module.End.eigenspace T c).map N.subtype ≤ N := by
    rintro x ⟨v, _, rfl⟩
    exact v.2
  have hWstable : IsGStable G ((Module.End.eigenspace T c).map N.subtype) := by
    rintro g x ⟨v, hv, rfl⟩
    refine ⟨rho hN.stable g v, ?_, rfl⟩
    simp only [SetLike.mem_coe] at hv ⊢
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have hcomm := congrArg (fun (f : ↥N →ₗ[ℂ] ↥N) => f v) (hT g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hcomm
    rw [← hcomm, hv, map_smul]
  have hWbot : (Module.End.eigenspace T c).map N.subtype ≠ ⊥ := by
    intro h
    exact hEbot (Submodule.map_injective_of_injective (N.subtype_injective)
      (by rw [h, Submodule.map_bot]))
  rcases hN.minimal _ hWstable hWle with h | h
  · exact absurd h hWbot
  · have htop : (Module.End.eigenspace T c) = ⊤ := by
      refine Submodule.map_injective_of_injective (N.subtype_injective) ?_
      rw [h, Submodule.map_subtype_top]
    intro v
    exact Module.End.mem_eigenspace_iff.mp (htop ▸ Submodule.mem_top)

/-- The sum of the group action over all of `G`, acting on a `G`-stable subspace. -/
noncomputable def sumRho {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) :
    ↥N →ₗ[ℂ] ↥N := ∑ g : G, rho hN g

theorem sumRho_apply {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (v : ↥N) :
    sumRho hN v = ∑ g : G, rho hN g v := by
  rw [sumRho, LinearMap.sum_apply]

theorem rho_comp_sumRho {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (h : G) :
    (rho hN h) ∘ₗ (sumRho hN) = sumRho hN := by
  refine LinearMap.ext fun v => ?_
  show (rho hN h) ((sumRho hN) v) = (sumRho hN) v
  rw [sumRho_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  show (rho hN h) ((rho hN g) v) = (rho hN (h * g)) v
  rw [rho_mul]
  rfl

theorem sumRho_comp_rho {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (h : G) :
    (sumRho hN) ∘ₗ (rho hN h) = sumRho hN := by
  refine LinearMap.ext fun v => ?_
  show (sumRho hN) ((rho hN h) v) = (sumRho hN) v
  rw [sumRho_apply, sumRho_apply]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ fun g => ?_
  show (rho hN g) ((rho hN h) v) = (rho hN (g * h)) v
  rw [rho_mul]
  rfl

/-- The action of `G` on `N` is trivial. -/
def IsTrivialOn {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) : Prop :=
  ∀ g : G, rho hN g = LinearMap.id

theorem sumRho_of_isTrivialOn {N : Submodule ℂ (MonoidAlgebra ℂ G)} {hN : IsGStable G N}
    (h : IsTrivialOn hN) (v : ↥N) : sumRho hN v = (Fintype.card G : ℂ) • v := by
  have h' : ∀ g : G, rho hN g = LinearMap.id := h
  rw [sumRho_apply]
  simp only [h', LinearMap.id_apply, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ]

/-- On a minimal `G`-stable subspace, `∑_g rho g` is `#G` times the identity when the action is
trivial and zero otherwise. -/
theorem sumRho_dichotomy {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsMinimalGStable N) :
    (IsTrivialOn hN.stable ∧ sumRho hN.stable = (Fintype.card G : ℂ) • LinearMap.id) ∨
      (¬ IsTrivialOn hN.stable ∧ sumRho hN.stable = 0) := by
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hN.ne_bot
  obtain ⟨c, hc⟩ := schur hN (sumRho hN.stable)
    (fun g => by rw [rho_comp_sumRho, sumRho_comp_rho])
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  obtain ⟨v, hv⟩ := exists_ne (0 : ↥N)
  have hstep : (sumRho hN.stable) ((sumRho hN.stable) v)
      = (Fintype.card G : ℂ) • ((sumRho hN.stable) v) := by
    rw [sumRho_apply]
    have heach : ∀ g : G, (rho hN.stable g) ((sumRho hN.stable) v) = (sumRho hN.stable) v :=
      fun g => congrArg (fun f : ↥N →ₗ[ℂ] ↥N => f v) (rho_comp_sumRho hN.stable g)
    rw [Finset.sum_congr rfl (fun g _ => heach g), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
  have hsq : c * c = (Fintype.card G : ℂ) * c := by
    have h1 : (sumRho hN.stable) ((sumRho hN.stable) v) = (c * c) • v := by
      rw [hc, hc, smul_smul]
    have h2 : (sumRho hN.stable) ((sumRho hN.stable) v) = ((Fintype.card G : ℂ) * c) • v := by
      rw [hstep, hc, smul_smul]
    exact smul_left_injective ℂ hv (h1.symm.trans h2)
  have hccase : c = 0 ∨ c = (Fintype.card G : ℂ) := by
    have hz : c * (c - (Fintype.card G : ℂ)) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hccase with h0 | hG
  · right
    refine ⟨?_, LinearMap.ext fun w => ?_⟩
    · intro htriv
      have h1 : sumRho hN.stable v = (Fintype.card G : ℂ) • v := sumRho_of_isTrivialOn htriv v
      rw [hc v, h0, zero_smul] at h1
      exact hv (by
        rcases smul_eq_zero.mp h1.symm with h | h
        · exact absurd h hcard
        · exact h)
    · rw [hc w, h0, zero_smul]
      rfl
  · left
    have hsum : sumRho hN.stable = (Fintype.card G : ℂ) • LinearMap.id :=
      LinearMap.ext fun w => by rw [hc w, hG]; rfl
    refine ⟨fun g => LinearMap.ext fun w => ?_, hsum⟩
    have hcomm := congrArg (fun (f : ↥N →ₗ[ℂ] ↥N) => f w) (rho_comp_sumRho hN.stable g)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hcomm
    rw [hsum] at hcomm
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hcomm
    rw [map_smul] at hcomm
    exact smul_right_injective ↥N hcard hcomm

end GaloisForLFunctions.HTGeometry.GroupCharacter
