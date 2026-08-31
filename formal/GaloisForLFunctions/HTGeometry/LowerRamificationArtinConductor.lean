import GaloisForLFunctions.HTGeometry.LowerRamificationGroup
import Mathlib.RepresentationTheory.Invariants

/-!
# Artin conductor from a finite lower ramification filtration

This file formalizes the classical lower-numbering summand

`(|Gᵢ| / |G₀|) * codim(V ^ Gᵢ)`

and its finite partial sum.  A lower filtration is eventually trivial, so the partial sum is the
actual local Artin conductor after any cutoff beyond the final ramification break.  The elementary
tail lemmas below make that stabilization explicit without postulating a conductor value.
-/

namespace GaloisForLFunctions.HTGeometry

variable {k G V : Type*} [Field k] [Group G] [Finite G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Codimension of the fixed subspace for a subgroup of the local Galois group. -/
noncomputable def Representation.lowerArtinCodimension
    (rho : Representation k G V) (H : Subgroup G) : ℕ :=
  Module.finrank k V -
    Module.finrank k (Representation.invariants (rho.comp H.subtype))

/-- Classical lower-numbering Artin-conductor summand. -/
noncomputable def Representation.lowerArtinTerm
    (rho : Representation k G V) (Gzero H : Subgroup G) : ℚ :=
  (Nat.card H : ℚ) / Nat.card Gzero *
    Representation.lowerArtinCodimension rho H

/-- Finite lower-numbering Artin conductor through levels `0, ..., N - 1`. -/
noncomputable def Representation.lowerArtinConductorUpTo
    (rho : Representation k G V) (filtration : ℕ → Subgroup G) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N,
    Representation.lowerArtinTerm rho (filtration 0) (filtration i)

omit [Finite G] [FiniteDimensional k V] in
/-- The trivial subgroup fixes the entire representation carrier. -/
theorem Representation.invariants_comp_bot_eq_top
    (rho : Representation k G V) :
    Representation.invariants (rho.comp (⊥ : Subgroup G).subtype) = ⊤ := by
  apply top_unique
  intro v _
  rw [Representation.mem_invariants]
  intro g
  have hg : (g : G) = 1 := by
    simpa only [Subgroup.mem_bot] using g.property
  change rho (g : G) v = v
  rw [hg]
  simp

omit [Finite G] [FiniteDimensional k V] in
@[simp] theorem Representation.lowerArtinCodimension_bot
    (rho : Representation k G V) :
    Representation.lowerArtinCodimension rho (⊥ : Subgroup G) = 0 := by
  unfold Representation.lowerArtinCodimension
  rw [Representation.invariants_comp_bot_eq_top rho]
  simp

omit [Finite G] [FiniteDimensional k V] in
@[simp] theorem Representation.lowerArtinTerm_bot
    (rho : Representation k G V) (Gzero : Subgroup G) :
    Representation.lowerArtinTerm rho Gzero ⊥ = 0 := by
  simp [Representation.lowerArtinTerm]

omit [Finite G] [FiniteDimensional k V] in
theorem Representation.lowerArtinConductorUpTo_succ
    (rho : Representation k G V) (filtration : ℕ → Subgroup G) (N : ℕ) :
    Representation.lowerArtinConductorUpTo rho filtration (N + 1) =
      Representation.lowerArtinConductorUpTo rho filtration N +
        Representation.lowerArtinTerm rho (filtration 0) (filtration N) := by
  simp [Representation.lowerArtinConductorUpTo, Finset.sum_range_succ]

omit [Finite G] [FiniteDimensional k V] in
/-- Once the next lower group is trivial, extending the conductor cutoff does not change it. -/
theorem Representation.lowerArtinConductorUpTo_succ_of_eq_bot
    (rho : Representation k G V) (filtration : ℕ → Subgroup G) (N : ℕ)
    (hN : filtration N = ⊥) :
    Representation.lowerArtinConductorUpTo rho filtration (N + 1) =
      Representation.lowerArtinConductorUpTo rho filtration N := by
  rw [Representation.lowerArtinConductorUpTo_succ, hN,
    Representation.lowerArtinTerm_bot, add_zero]

end GaloisForLFunctions.HTGeometry
