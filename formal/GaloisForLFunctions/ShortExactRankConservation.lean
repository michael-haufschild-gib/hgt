import Mathlib

/-!
# Rank conservation across a short exact sequence

For a short exact sequence `0 → A → B → C → 0` of vector spaces, the ranks add:
`rank A + rank C = rank B` (and the finite-dimensional `finrank` version).  This is the frequency
conservation law underlying the frequency-budget cards: Pontryagin duality turns a surjection of
compact groups into such a short exact sequence of character groups, and tensoring with `ℚ` gives the
exact rational-rank split `rank Γ(X) = rank Γ(B) + rank Γ(K)`.
-/

open Module

namespace HTGeometry

/-- **Rank additivity across a short exact sequence.**  If `f` is injective, `g` surjective, and
`range f = ker g`, then `rank A + rank C = rank B`. -/
theorem rank_add_of_shortExact {K : Type*} {A B C : Type u} [DivisionRing K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : LinearMap.range f = LinearMap.ker g) :
    Module.rank K A + Module.rank K C = Module.rank K B := by
  have h1 := LinearMap.rank_range_add_rank_ker g
  rw [LinearMap.range_eq_top.mpr hg, rank_top, ← hfg,
    ← (LinearEquiv.ofInjective f hf).rank_eq] at h1
  rw [add_comm]; exact h1

/-- Finite-dimensional form of rank additivity across a short exact sequence. -/
theorem finrank_add_of_shortExact {K : Type*} {A B C : Type u} [DivisionRing K]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]
    [FiniteDimensional K B]
    (f : A →ₗ[K] B) (g : B →ₗ[K] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : LinearMap.range f = LinearMap.ker g) :
    Module.finrank K A + Module.finrank K C = Module.finrank K B := by
  have hAfin : FiniteDimensional K A :=
    (LinearEquiv.ofInjective f hf).symm.finiteDimensional
  have hCfin : FiniteDimensional K C :=
    (LinearMap.quotKerEquivOfSurjective g hg).finiteDimensional
  have hr := rank_add_of_shortExact f g hf hg hfg
  show (Module.rank K A).toNat + (Module.rank K C).toNat = (Module.rank K B).toNat
  rw [← Cardinal.toNat_add (Module.rank_lt_aleph0 K A) (Module.rank_lt_aleph0 K C), hr]

end HTGeometry
