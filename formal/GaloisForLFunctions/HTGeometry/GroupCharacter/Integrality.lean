import GaloisForLFunctions.HTGeometry.GroupCharacter.Eigenvalues
import GaloisForLFunctions.HTGeometry.GroupCharacter.Schur
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Integrality of characters and of the central character

* `chi_isIntegral` — character values are algebraic integers.
* `exists_classSum_scalar` — the sum of the action over a conjugation-stable finite set acts on a
  minimal `G`-stable subspace as multiplication by an algebraic integer `lam`, and
  `lam * finrank = ∑ chi`.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type u} [Group G] [Fintype G]

theorem isIntegral_of_pow_eq_one {μ : ℂ} {m : ℕ} (hm : m ≠ 0) (h : μ ^ m = 1) :
    IsIntegral ℤ μ := by
  refine ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm, ?_⟩
  simp [h]

/-- Character values are algebraic integers. -/
theorem chi_isIntegral {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g : G) :
    IsIntegral ℤ (chi hN g) := by
  obtain ⟨E, _, hroots, hsum⟩ := exists_eigen_multiset hN g
  have hcard : (Fintype.card G) ≠ 0 := Fintype.card_ne_zero
  have hmem : ∀ μ ∈ E, μ ∈ integralClosure ℤ ℂ := fun μ hμ =>
    isIntegral_of_pow_eq_one hcard (hroots μ hμ)
  have : E.sum ∈ integralClosure ℤ ℂ := Subalgebra.multiset_sum_mem _ hmem
  rw [hsum] at this
  exact this

omit [Fintype G] in
theorem rho_mul' {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (g h : G) :
    rho hN (g * h) = rho hN g * rho hN h := rho_mul hN g h

omit [Fintype G] in
/-- Characters are class functions. -/
theorem chi_conj {N : Submodule ℂ (MonoidAlgebra ℂ G)} (hN : IsGStable G N) (h y : G) :
    chi hN (h * y * h⁻¹) = chi hN y := by
  have hmul : ∀ a b : G, rho hN (a * b) = rho hN a * rho hN b := fun a b => rho_mul' hN a b
  have hinv : rho hN h⁻¹ * rho hN h = 1 := by
    rw [← hmul, inv_mul_cancel, rho_one]; rfl
  calc chi hN (h * y * h⁻¹)
      = LinearMap.trace ℂ ↥N (rho hN h * (rho hN y * rho hN h⁻¹)) := by
        rw [chi, hmul, hmul, mul_assoc]
    _ = LinearMap.trace ℂ ↥N ((rho hN y * rho hN h⁻¹) * rho hN h) := LinearMap.trace_mul_comm _ _ _
    _ = LinearMap.trace ℂ ↥N (rho hN y) := by rw [mul_assoc, hinv, mul_one]
    _ = chi hN y := rfl

variable {N : Submodule ℂ (MonoidAlgebra ℂ G)}

/-- The monoid of operators coming from the group. -/
def rhoSubmonoid (hN : IsGStable G N) : Submonoid (Module.End ℂ ↥N) where
  carrier := Set.range (rho hN)
  one_mem' := ⟨1, rho_one hN⟩
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, rho_mul' hN a b⟩

theorem isIntegral_of_mem_rhoAdjoin (hN : IsGStable G N)
    {T : Module.End ℂ ↥N} (hT : T ∈ Algebra.adjoin ℤ (Set.range (rho hN))) :
    IsIntegral ℤ T := by
  refine IsIntegral.of_mem_of_fg (Algebra.adjoin ℤ (Set.range (rho hN))) ?_ T hT
  rw [Algebra.adjoin_eq_span]
  refine Submodule.fg_span ?_
  have : (Submonoid.closure (Set.range (rho hN)) : Set (Module.End ℂ ↥N))
      = Set.range (rho hN) := by
    have h1 : Submonoid.closure (Set.range (rho hN)) = rhoSubmonoid hN :=
      Submonoid.closure_eq (rhoSubmonoid hN)
    rw [h1]
    rfl
  rw [this]
  exact Set.finite_range _

omit [Fintype G] in
theorem algebraMap_end_injective (hNbot : N ≠ ⊥) :
    Function.Injective (algebraMap ℂ (Module.End ℂ ↥N)) := by
  haveI : Nontrivial ↥N := Submodule.nontrivial_iff_ne_bot.mpr hNbot
  intro a b hab
  obtain ⟨v, hv⟩ := exists_ne (0 : ↥N)
  have h1 : a • v = b • v := by
    have := congrArg (fun (f : Module.End ℂ ↥N) => f v) hab
    simpa [Algebra.algebraMap_eq_smul_one] using this
  exact smul_left_injective ℂ hv h1

/-- The class sum acts as an algebraic integer scalar on a minimal `G`-stable subspace. -/
theorem exists_classSum_scalar (hN : IsMinimalGStable N) (K : Finset G)
    (hK : ∀ h : G, ∀ y ∈ K, h * y * h⁻¹ ∈ K) :
    ∃ lam : ℂ, IsIntegral ℤ lam ∧
      lam * (Module.finrank ℂ ↥N : ℂ) = ∑ y ∈ K, chi hN.stable y := by
  classical
  set T : Module.End ℂ ↥N := ∑ y ∈ K, rho hN.stable y with hTdef
  have hcomm : ∀ h : G, (rho hN.stable h) ∘ₗ T = T ∘ₗ (rho hN.stable h) := by
    intro h
    show (rho hN.stable h) * T = T * (rho hN.stable h)
    have hbij : ∑ y ∈ K, rho hN.stable (h * y * h⁻¹) = T := by
      rw [hTdef]
      refine Finset.sum_nbij' (fun y => h * y * h⁻¹) (fun y => h⁻¹ * y * h) ?_ ?_ ?_ ?_ ?_
      · intro y hy; exact hK h y hy
      · intro y hy; simpa using hK h⁻¹ y hy
      · intro y _; group
      · intro y _; group
      · intro y _; rfl
    have hstep : ∀ y : G, (rho hN.stable h) * rho hN.stable y
        = rho hN.stable (h * y * h⁻¹) * (rho hN.stable h) := by
      intro y
      rw [← rho_mul', ← rho_mul']
      congr 1
      group
    calc (rho hN.stable h) * T = ∑ y ∈ K, (rho hN.stable h) * rho hN.stable y := by
          rw [hTdef, Finset.mul_sum]
      _ = ∑ y ∈ K, rho hN.stable (h * y * h⁻¹) * (rho hN.stable h) :=
          Finset.sum_congr rfl (fun y _ => hstep y)
      _ = (∑ y ∈ K, rho hN.stable (h * y * h⁻¹)) * (rho hN.stable h) := (Finset.sum_mul _ _ _).symm
      _ = T * (rho hN.stable h) := by rw [hbij]
  obtain ⟨lam, hlam⟩ := schur hN T hcomm
  have hTeq : T = algebraMap ℂ (Module.End ℂ ↥N) lam := by
    refine LinearMap.ext fun v => ?_
    rw [hlam v, Algebra.algebraMap_eq_smul_one]
    rfl
  refine ⟨lam, ?_, ?_⟩
  · refine IsIntegral.tower_bot (R := ℤ) (A := ℂ) (B := Module.End ℂ ↥N) ?_ ?_
    · exact algebraMap_end_injective hN.ne_bot
    · rw [← hTeq]
      refine isIntegral_of_mem_rhoAdjoin hN.stable ?_
      exact Subalgebra.sum_mem _ (fun y _ => Algebra.subset_adjoin ⟨y, rfl⟩)
  · have h1 : LinearMap.trace ℂ ↥N T = ∑ y ∈ K, chi hN.stable y := by
      rw [hTdef, map_sum]
      rfl
    have h2 : LinearMap.trace ℂ ↥N T = lam * (Module.finrank ℂ ↥N : ℂ) := by
      have hT' : T = lam • (LinearMap.id : Module.End ℂ ↥N) := LinearMap.ext fun v => hlam v
      rw [hT', map_smul, LinearMap.trace_id, smul_eq_mul]
    rw [← h2, h1]

end GaloisForLFunctions.HTGeometry.GroupCharacter
