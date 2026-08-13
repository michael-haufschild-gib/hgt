import Mathlib

/-!
# Rank-two commutator parity-multiplicity balance

For a reflection-invariant symmetric operator whose commutator with the reflection-odd frequency
operator has the Connes--van Suijlekom rank-two form `[D,Q] = |β⟩⟨η| - |η⟩⟨β|` with even `η` and
odd `β`, the even and odd multiplicities of every real eigenvalue differ by at most one.  The
frequency map sends an even eigenvector annihilated by the single functional `⟨η,·⟩` to an odd
eigenvector of the same eigenvalue and conversely, and each restriction is injective under the
literal kernel conditions of the truncated model; a one-functional kernel loses at most one
dimension.  Consequently an eigenvalue lying strictly below the opposite-parity Rayleigh floor is
automatically simple, and a zero-mode/odd-level pair carries the exact reciprocal gap current
`⟨Df,g⟩ = -1/λ`.
-/

open scoped RealInnerProductSpace
open Submodule

noncomputable section

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- The rank-two commutator relation `[D,Q] = |β⟩⟨η| - |η⟩⟨β|`. -/
def RankTwoCommutator (D Q : H →ₗ[ℝ] H) (η β : H) : Prop :=
  ∀ f : H, D (Q f) - Q (D f) = ⟪η, f⟫ • β - ⟪β, f⟫ • η

/-- Even eigenspace of `Q` at `λ` for the reflection `Γ`. -/
def evenEigenspace (Q Γ : H →ₗ[ℝ] H) (lam : ℝ) : Submodule ℝ H where
  carrier := {f | Q f = lam • f ∧ Γ f = f}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨by rw [map_add, hf1, hg1, smul_add], by rw [map_add, hf2, hg2]⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨by rw [map_smul, hf1, smul_comm], by rw [map_smul, hf2]⟩

/-- Odd eigenspace of `Q` at `λ` for the reflection `Γ`. -/
def oddEigenspace (Q Γ : H →ₗ[ℝ] H) (lam : ℝ) : Submodule ℝ H where
  carrier := {f | Q f = lam • f ∧ Γ f = -f}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨by rw [map_add, hf1, hg1, smul_add], by rw [map_add, hf2, hg2]; abel⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨by rw [map_smul, hf1, smul_comm], by rw [map_smul, hf2, smul_neg]⟩

omit [FiniteDimensional ℝ H] in
@[simp] theorem mem_evenEigenspace {Q Γ : H →ₗ[ℝ] H} {lam : ℝ} {f : H} :
    f ∈ evenEigenspace Q Γ lam ↔ Q f = lam • f ∧ Γ f = f := Iff.rfl

omit [FiniteDimensional ℝ H] in
@[simp] theorem mem_oddEigenspace {Q Γ : H →ₗ[ℝ] H} {lam : ℝ} {f : H} :
    f ∈ oddEigenspace Q Γ lam ↔ Q f = lam • f ∧ Γ f = -f := Iff.rfl

section Parity

variable {Γ : H →ₗ[ℝ] H}
variable (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)

omit [FiniteDimensional ℝ H] in
/-- An even and an odd vector are orthogonal for a symmetric involution. -/
theorem inner_eq_zero_of_even_odd (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    {u v : H} (hu : Γ u = u) (hv : Γ v = -v) : ⟪v, u⟫ = 0 := by
  have h := hΓsym v u
  rw [hv, hu] at h
  have : -⟪v, u⟫ = ⟪v, u⟫ := by
    rw [← inner_neg_left]
    exact h
  linarith

end Parity

section Balance

variable {D Q Γ : H →ₗ[ℝ] H} {η β : H} {lam : ℝ}

omit [FiniteDimensional ℝ H] in
/-- The frequency image of an even eigenvector killed by the source functional is an odd
eigenvector. -/
theorem frequency_maps_even_to_odd
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hβ : Γ β = -β)
    {f : H} (hf : f ∈ evenEigenspace Q Γ lam) (hηf : ⟪η, f⟫ = 0) :
    D f ∈ oddEigenspace Q Γ lam := by
  obtain ⟨hQf, hΓf⟩ := hf
  have hβf : ⟪β, f⟫ = 0 := inner_eq_zero_of_even_odd hΓsym hΓf hβ
  have hDQ := hcomm f
  rw [hηf, hβf, zero_smul, zero_smul, sub_zero, sub_eq_zero] at hDQ
  constructor
  · rw [← hDQ, hQf, map_smul]
  · have hDf := hanti f
    rw [hΓf] at hDf
    have hneg := congrArg (fun x : H => -x) hDf
    simpa using hneg.symm

omit [FiniteDimensional ℝ H] in
/-- The frequency image of an odd eigenvector killed by the odd source functional is an even
eigenvector. -/
theorem frequency_maps_odd_to_even
    (hΓsym : ∀ f g : H, ⟪Γ f, g⟫ = ⟪f, Γ g⟫)
    (hanti : ∀ f, D (Γ f) = -Γ (D f))
    (hcomm : RankTwoCommutator D Q η β)
    (hη : Γ η = η)
    {g : H} (hg : g ∈ oddEigenspace Q Γ lam) (hβg : ⟪β, g⟫ = 0) :
    D g ∈ evenEigenspace Q Γ lam := by
  obtain ⟨hQg, hΓg⟩ := hg
  have hηg : ⟪η, g⟫ = 0 := by
    have h := hΓsym η g
    rw [hη, hΓg] at h
    have h2 : ⟪η, g⟫ = -⟪η, g⟫ := by
      rw [← inner_neg_right]
      exact h
    linarith
  have hDQ := hcomm g
  rw [hηg, hβg, zero_smul, zero_smul, sub_zero, sub_eq_zero] at hDQ
  constructor
  · rw [← hDQ, hQg, map_smul]
  · have := hanti g
    rw [hΓg, map_neg] at this
    rw [← neg_neg (Γ (D g)), ← this, neg_neg]

/-- One-functional codimension bound: intersecting with the kernel of a single inner-product
functional loses at most one dimension. -/
theorem finrank_inf_ker_functional_ge (E : Submodule ℝ H) (w : H) :
    Module.finrank ℝ E ≤
      Module.finrank ℝ ↥(E ⊓ (LinearMap.ker (innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap :
        Submodule ℝ H)) + 1 := by
  classical
  set L : Submodule ℝ H := LinearMap.ker (innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap with hLdef
  set φ : E →ₗ[ℝ] ℝ := ((innerSL ℝ w : H →L[ℝ] ℝ).toLinearMap).comp E.subtype with hφdef
  have hmem : ∀ y : E, y ∈ LinearMap.ker φ ↔ (y : H) ∈ L := by
    intro y
    simp [hφdef, hLdef, LinearMap.mem_ker]
  have hmap : Submodule.map E.subtype (LinearMap.ker φ) = E ⊓ L := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hmem y).1 hy⟩
    · rintro ⟨hxE, hxL⟩
      exact ⟨⟨x, hxE⟩, (hmem ⟨x, hxE⟩).2 hxL, rfl⟩
  have hkereq : Module.finrank ℝ ↥(LinearMap.ker φ) = Module.finrank ℝ ↥(E ⊓ L) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective E.subtype E.injective_subtype
      (LinearMap.ker φ)).finrank_eq
  have hrank := LinearMap.finrank_range_add_finrank_ker φ
  have hrange : Module.finrank ℝ ↥(LinearMap.range φ) ≤ 1 := by
    have hle := Submodule.finrank_le (LinearMap.range φ)
    simpa using hle
  omega

end Balance

end RHTower

end
