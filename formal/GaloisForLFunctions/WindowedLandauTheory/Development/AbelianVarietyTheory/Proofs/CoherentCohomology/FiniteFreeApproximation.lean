import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Projective

/-! A bounded cochain complex with finite cohomology admits a finite free approximation. -/

universe u v

namespace GlobalTheory

section Construction

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Combine lifts of finite generators for the projected cycles and the cohomology. -/
private theorem exists_free_step {C₀ C₁ K₁ K₂ : Type*} [AddCommGroup C₀] [AddCommGroup C₁]
    [AddCommGroup K₁] [AddCommGroup K₂] [Module R C₀] [Module R C₁] [Module R K₁] [Module R K₂]
    [Module.Finite R K₁] (d : C₀ →ₗ[R] C₁) (φ : K₁ →ₗ[R] C₁) (δ : K₁ →ₗ[R] K₂) (B : Submodule R C₀)
    [Module.Finite R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)] :
    ∃ (m : ℕ) (φ₀ : (Fin m → R) →ₗ[R] C₀) (δ₀ : (Fin m → R) →ₗ[R] K₁),
      (∀ x, d (φ₀ x) = φ (δ₀ x)) ∧ (∀ x, δ (δ₀ x) = 0) ∧
      ∀ c k, d c = φ k → δ k = 0 → ∃ x, c - φ₀ x ∈ B ∧ δ₀ x = k := by
  let N : Submodule R (C₀ × K₁) :=
    LinearMap.ker (d.coprod (-φ)) ⊓ LinearMap.ker (δ ∘ₗ LinearMap.snd R _ _)
  have hN : ∀ x, x ∈ N ↔ d x.1 = φ x.2 ∧ δ x.2 = 0 := by
    intro x
    simp [N, add_neg_eq_zero]
  let s : N →ₗ[R] K₁ := LinearMap.snd R _ _ ∘ₗ N.subtype
  obtain ⟨a, π₁, hπ₁⟩ := Module.Finite.exists_fin' R (LinearMap.range s)
  obtain ⟨g₁, hg₁⟩ := Module.projective_lifting_property s.rangeRestrict π₁
    s.surjective_rangeRestrict
  obtain ⟨b, π₂, hπ₂⟩ :=
    Module.Finite.exists_fin' R (LinearMap.ker d ⧸ B.comap (LinearMap.ker d).subtype)
  obtain ⟨g₂, hg₂⟩ := Module.projective_lifting_property
    (B.comap (LinearMap.ker d).subtype).mkQ π₂ (Submodule.mkQ_surjective _)
  let e : (Fin (a + b) → R) ≃ₗ[R] (Fin a → R) × (Fin b → R) :=
    (LinearEquiv.funCongrLeft R R finSumFinEquiv).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)
  refine ⟨a + b, ((LinearMap.fst R _ _ ∘ₗ N.subtype ∘ₗ g₁).coprod
    ((LinearMap.ker d).subtype ∘ₗ g₂)) ∘ₗ e.toLinearMap,
    (s ∘ₗ g₁ ∘ₗ LinearMap.fst R _ _) ∘ₗ e.toLinearMap, fun x => ?_, fun x => ?_,
    fun c k h h' => ?_⟩
  · have h1 := ((hN _).1 (g₁ (e x).1).2).1
    have h2 : d (g₂ (e x).2) = 0 := (g₂ (e x).2).2
    simp [s, h1, h2]
  · exact ((hN _).1 (g₁ (e x).1).2).2
  · obtain ⟨x, hx⟩ := hπ₁ (s.rangeRestrict ⟨(c, k), (hN _).2 ⟨h, h'⟩⟩)
    have hx' : ((g₁ x : N) : C₀ × K₁).2 = k := by
      rw [← hg₁] at hx
      exact congrArg Subtype.val hx
    have h1 := ((hN _).1 (g₁ x).2).1
    have h3 : c - ((g₁ x : N) : C₀ × K₁).1 ∈ LinearMap.ker d := by
      simp [h, h1, hx']
    obtain ⟨y, hy⟩ := hπ₂ ((B.comap (LinearMap.ker d).subtype).mkQ ⟨_, h3⟩)
    rw [← hg₂] at hy
    have h4 := (Submodule.Quotient.eq _).1 hy.symm
    refine ⟨e.symm (x, y), ?_, ?_⟩
    · simpa [sub_sub] using h4
    · simpa [s] using hx'

/-- Construct the approximation from the highest degree downward. -/
theorem exists_free_complex (n : ℕ) : ∀ (C : ℕ → ModuleCat.{v} R)
    (d : ∀ p, C p →ₗ[R] C (p + 1)) (B : Submodule R (C 0))
    (_ : ∀ p, n ≤ p → Subsingleton (C p))
    (_ : Module.Finite R (LinearMap.ker (d 0) ⧸ B.comap (LinearMap.ker (d 0)).subtype))
    (_ : ∀ p, Module.Finite R (LinearMap.ker (d (p + 1)) ⧸
      (LinearMap.range (d p)).comap (LinearMap.ker (d (p + 1))).subtype)),
    ∃ (m : ℕ → ℕ) (δ : ∀ p, (Fin (m p) → R) →ₗ[R] (Fin (m (p + 1)) → R))
      (φ : ∀ p, (Fin (m p) → R) →ₗ[R] C p),
      (∀ p, n ≤ p → m p = 0) ∧ (∀ p x, δ (p + 1) (δ p x) = 0) ∧
      (∀ p x, d p (φ p x) = φ (p + 1) (δ p x)) ∧
      (∀ c k, d 0 c = φ 1 k → δ 1 k = 0 → ∃ x, c - φ 0 x ∈ B ∧ δ 0 x = k) ∧
      ∀ p c k, d (p + 1) c = φ (p + 2) k → δ (p + 2) k = 0 →
        ∃ c' k', d p c' + φ (p + 1) k' = c ∧ δ (p + 1) k' = k := by
  induction n with
  | zero =>
    intro C d B hC _ _
    have hC' : ∀ p, Subsingleton (C p) := fun p => hC p p.zero_le
    refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => Subsingleton.elim _ _, fun c k _ _ => ⟨0, ?_, Subsingleton.elim _ _⟩,
      fun p c k _ _ => ⟨0, 0, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
    rw [Subsingleton.elim (c - _) 0]
    exact B.zero_mem
  | succ n ih =>
    intro C d B hC hB hH
    obtain ⟨m, δ, φ, hm, hδ, hφ, h0, h1⟩ := ih (fun p => C (p + 1)) (fun p => d (p + 1))
      (LinearMap.range (d 0)) (fun p hp => hC _ (by omega)) (hH 0) (fun p => hH (p + 1))
    obtain ⟨a, φ₀, δ₀, e1, e2, e3⟩ := exists_free_step (d 0) (φ 0) (δ 0) B
    refine ⟨fun p => Nat.casesOn p a m,
      fun p => match p with | 0 => δ₀ | p + 1 => δ p,
      fun p => match p with | 0 => φ₀ | p + 1 => φ p, ?_, ?_, ?_, e3, ?_⟩
    · rintro (_ | p) hp
      · omega
      · exact hm p (by omega)
    · rintro (_ | p)
      · exact e2
      · exact hδ p
    · rintro (_ | p)
      · exact e1
      · exact hφ p
    · rintro (_ | p)
      · intro c k h h'
        obtain ⟨x, ⟨c', hc'⟩, hx⟩ := h0 c k h h'
        exact ⟨c', x, eq_sub_iff_add_eq.1 hc', hx⟩
      · exact h1 p

end Construction

end GlobalTheory
