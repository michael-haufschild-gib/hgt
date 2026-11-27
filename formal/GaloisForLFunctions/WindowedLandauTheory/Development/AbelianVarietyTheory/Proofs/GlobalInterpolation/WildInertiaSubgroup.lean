import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global

/-! The multiplicative valuation test defines wild inertia. It is normal in
the decomposition group, so its fixed subspace is stable under Weil actions. -/

noncomputable section

open NumberField Module WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory.TameKummer

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

/-- Automorphisms inducing the identity on every nonzero element's leading residue. -/
def wildInertia (A : ValuationSubring Ω) : Subgroup (G E Ω) where
  carrier := {σ | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}
  one_mem' := fun y hy => by simp [div_self hy]
  mul_mem' := by
    intro σ τ hσ hτ y hy
    have hy' : τ y ≠ 0 := (_root_.map_ne_zero τ).mpr hy
    have h₁ := hσ _ hy'
    have h₂ := hτ _ hy
    have he : (σ * τ) y / y - 1 =
        (σ (τ y) / τ y - 1) * (τ y / y - 1) + ((σ (τ y) / τ y - 1) + (τ y / y - 1)) := by
      rw [AlgEquiv.mul_apply]
      field_simp
      ring
    rw [he]
    refine Valuation.map_add_lt _ ?_ (Valuation.map_add_lt _ h₁ h₂)
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' h₂.le) h₁
  inv_mem' := by
    intro σ hσ y hy
    let z := (σ⁻¹ : G E Ω) y
    have hz : z ≠ 0 := (_root_.map_ne_zero _).mpr hy
    have h := hσ z hz
    change A.valuation (σ ((σ⁻¹ : G E Ω) y) / z - 1) < 1 at h
    rw [mul_inv_apply] at h
    have hu : A.valuation (y / z) = 1 := by
      have he := A.valuation.map_eq_of_sub_lt (x := 1) (y := y / z)
        (by rwa [map_one])
      rwa [map_one] at he
    change A.valuation (z / y - 1) < 1
    rw [show z / y - 1 = -((y / z - 1) / (y / z)) by field_simp; ring,
      Valuation.map_neg, map_div₀, hu, div_one]
    exact h

theorem mem_wildInertia_iff (A : ValuationSubring Ω) (s : G E Ω) :
    s ∈ wildInertia A ↔ ∀ y : Ω, y ≠ 0 → A.valuation (s y / y - 1) < 1 :=
  Iff.rfl

theorem wildInertia_le_inertia (A : ValuationSubring Ω) : wildInertia A ≤ Ine (F := E) A := by
  intro σ hs
  have hlt (x : Ω) (hx : x ≠ 0) : A.valuation (σ x - x) < A.valuation x := by
    have he : σ x - x = (σ x / x - 1) * x := by field_simp
    rw [he, map_mul]
    exact mul_lt_of_lt_one_left (zero_lt_iff.mpr (by simpa using hx)) (hs x hx)
  have hval (x : Ω) : A.valuation (σ x) = A.valuation x := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · exact A.valuation.map_eq_of_sub_lt (hlt x hx)
  refine ⟨?_, fun x hx => ?_⟩
  · change σ • A = A
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← A.valuation_le_one_iff,
      ← A.valuation_le_one_iff, ← hval, AlgEquiv.smul_def, mul_inv_apply]
  · rcases eq_or_ne x 0 with rfl | hx₀
    · simp
    · exact (hlt x hx₀).trans_le hx

theorem conj_mem_wildInertia (A : ValuationSubring Ω) {φ s : G E Ω}
    (hφ : φ ∈ Dec (F := E) A) (hs : s ∈ wildInertia A) :
    φ * s * φ⁻¹ ∈ wildInertia A := by
  intro y hy
  have h := hs ((φ⁻¹ : G E Ω) y) ((_root_.map_ne_zero _).mpr hy)
  rw [← valuation_apply_lt_one_iff hφ, map_sub, map_div₀, mul_inv_apply, map_one] at h
  exact h

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]

/-- The subspace on which wild inertia acts trivially. -/
def wildInvariants (A : ValuationSubring Ω) {W : Subgroup (G E Ω)} (ρ : Representation k W V) :
    Submodule k V := Representation.invariants (ρ.comp ((wildInertia A).subgroupOf W).subtype)

theorem mem_wildInvariants (A : ValuationSubring Ω) {W : Subgroup (G E Ω)} (ρ : Representation k W V)
    (v : V) : v ∈ wildInvariants A ρ ↔ ∀ s : W, (s : G E Ω) ∈ wildInertia A → ρ s v = v :=
  ⟨fun hv s hs => hv ⟨s, hs⟩, fun hv s => hv s.1 s.2⟩

/-- Wild inertia invariants are stable under the decomposition action. -/
theorem map_mem_wildInvariants (A : ValuationSubring Ω) {W : Subgroup (G E Ω)}
    (hWD : W ≤ Dec (F := E) A) (ρ : Representation k W V) (g : W)
    {v : V} (hv : v ∈ wildInvariants A ρ) : ρ g v ∈ wildInvariants A ρ := by
  rw [mem_wildInvariants] at hv ⊢
  intro s hs
  have h := hv (g⁻¹ * s * (g⁻¹)⁻¹) (conj_mem_wildInertia A (hWD (g⁻¹).2) hs)
  calc
    ρ s (ρ g v) = ρ g (ρ (g⁻¹ * s * (g⁻¹)⁻¹) v) := by
      rw [← End.mul_apply, ← End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    _ = ρ g v := by rw [h]

/-- If the wild inertia invariant subspace has full dimension, wild inertia
acts trivially on the original representation. -/
theorem wild_apply_eq_of_finrank_invariants [FiniteDimensional k V] (A : ValuationSubring Ω)
    {W : Subgroup (G E Ω)} (ρ : Representation k W V)
    (hd : Module.finrank k (wildInvariants A ρ) = Module.finrank k V)
    (s : W) (hs : (s : G E Ω) ∈ wildInertia A) (v : V) : ρ s v = v := by
  have h := Submodule.eq_top_of_finrank_eq hd
  have hv : v ∈ wildInvariants A ρ := h.symm ▸ Submodule.mem_top
  exact (mem_wildInvariants A ρ v).mp hv s hs

end GlobalTheory.TameKummer
