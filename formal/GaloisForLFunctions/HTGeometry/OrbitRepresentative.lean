import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# A set of orbit representatives maps bijectively onto the orbit space

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), the set-theoretic core
of Theorem 7.10: each `Q`-orbit of the suspension contains exactly one point of the subspace of
injective characters, so that subspace maps bijectively onto the orbit space.
-/

namespace HTGeometry


variable {Q S : Type*} [Group Q] [MulAction Q S] (A : Set S)

/-- The map from a set of orbit representatives to the orbit space. -/
def orbitRepMap (a : A) : MulAction.orbitRel.Quotient Q S :=
  Quotient.mk (MulAction.orbitRel Q S) (a : S)

/-- **Deninger, Theorem 7.10, the set-theoretic core.**  If every orbit contains exactly one
element of `A`, then `A` maps bijectively onto the orbit space. -/
theorem orbitRepMap_bijective
    (h : ∀ s : S, ∃! a : A, ∃ q : Q, q • (a : S) = s) :
    Function.Bijective (orbitRepMap (Q := Q) A) := by
  constructor
  · intro a b hab
    have hmem : ∃ q : Q, q • (a : S) = (b : S) := by
      obtain ⟨q, hq⟩ := Quotient.exact hab
      have hq' : q • (b : S) = (a : S) := hq
      exact ⟨q⁻¹, by rw [← hq', inv_smul_smul]⟩
    obtain ⟨c, -, huniq⟩ := h (b : S)
    have ha : a = c := huniq a hmem
    have hb : b = c := huniq b ⟨1, one_smul Q (b : S)⟩
    rw [ha, hb]
  · intro y
    obtain ⟨s, rfl⟩ := Quotient.exists_rep y
    obtain ⟨a, ⟨q, hq⟩, -⟩ := h s
    refine ⟨a, ?_⟩
    refine Quotient.sound ?_
    refine ⟨q⁻¹, ?_⟩
    show q⁻¹ • s = (a : S)
    rw [← hq, inv_smul_smul]


end HTGeometry
