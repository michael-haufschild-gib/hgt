import GaloisForLFunctions.RHTower.ConnesSelbergPeriodization

/-!
# §VII (31)-(32): only finitely many lattice terms are nonzero

§VII (31)-(32) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  "Since `f` has compact support in `A_S^*`, the intersection of `O_S^*` with the support of `f`
  is finite", and "there are only finitely many `q ∈ O_S^*` such that `k_v^*` meets the support of
  `f_q`", so "all the sums in `q` will have only finitely many non zero terms".

The mechanism is purely topological: a *discrete* subset that is *closed* meets every compact set
in a finite set, because the intersection is then compact and discrete.  This module proves that,
its consequence for the support of a test function along the lattice, and the summability that
follows - so every `∑_q` appearing in Theorem 4 is a finite sum.
-/

open Set

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {X : Type*} [TopologicalSpace X]

/-- **A discrete closed set meets a compact set in a finite set.** -/
theorem connes_discrete_inter_compact_finite {Γ K : Set X}
    (hΓd : IsDiscrete Γ) (hΓc : IsClosed Γ) (hK : IsCompact K) : (Γ ∩ K).Finite :=
  (hK.inter_left hΓc).finite (hΓd.mono Set.inter_subset_left)

/-- **§VII (31), finiteness.**  Only finitely many lattice points lie in the compact support of
the test function. -/
theorem connes_lattice_support_finite {Γ K : Set X} (hΓd : IsDiscrete Γ) (hΓc : IsClosed Γ)
    (hK : IsCompact K) {f : X → ℂ} (hsupp : ∀ x : X, f x ≠ 0 → x ∈ K) :
    {x : X | x ∈ Γ ∧ f x ≠ 0}.Finite := by
  refine Set.Finite.subset (connes_discrete_inter_compact_finite hΓd hΓc hK) ?_
  rintro x ⟨hxΓ, hxf⟩
  exact ⟨hxΓ, hsupp x hxf⟩

/-- The same statement as finiteness of the support of the restriction to the lattice. -/
theorem connes_lattice_restrict_support_finite {Γ K : Set X} (hΓd : IsDiscrete Γ)
    (hΓc : IsClosed Γ) (hK : IsCompact K) {f : X → ℂ} (hsupp : ∀ x : X, f x ≠ 0 → x ∈ K) :
    (Function.support fun q : Γ => f (q : X)).Finite := by
  have hfin := connes_lattice_support_finite hΓd hΓc hK hsupp
  have hinj : Function.Injective (fun q : Γ => (q : X)) := Subtype.val_injective
  refine Set.Finite.of_finite_image (f := fun q : Γ => (q : X)) ?_ hinj.injOn
  refine Set.Finite.subset hfin ?_
  rintro x ⟨q, hq, rfl⟩
  exact ⟨q.2, hq⟩

/-- **§VII (31)-(32).**  Every sum over the lattice in Theorem 4 has finitely many nonzero terms,
hence is summable. -/
theorem connes_lattice_summable {Γ K : Set X} (hΓd : IsDiscrete Γ) (hΓc : IsClosed Γ)
    (hK : IsCompact K) {f : X → ℂ} (hsupp : ∀ x : X, f x ≠ 0 → x ∈ K) :
    Summable fun q : Γ => f (q : X) :=
  summable_of_hasFiniteSupport
    (connes_lattice_restrict_support_finite hΓd hΓc hK hsupp)

end

end GaloisForLFunctions.RHTower
