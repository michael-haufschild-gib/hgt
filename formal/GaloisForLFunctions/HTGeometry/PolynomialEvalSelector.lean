import Mathlib

/-!
# A nonzero polynomial is nonzero along an injective sequence infinitely often

A nonzero polynomial has finitely many roots, so along an injective sequence `b` its value
`Q(b M)` vanishes for only finitely many `M`.  Hence on any infinite index set there is an `M`
at which `Q(b M) ≠ 0` (`exists_mem_eval_ne_zero`).

For the leading symbol of a homogeneous differential polynomial evaluated at the exponent
sequence, this selects a scale at which the leading-symbol combination does not vanish — while
staying inside the infinite set of scales where the series coefficient is nonzero.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **Eval selector.**  A nonzero polynomial, composed with an injective sequence, is nonzero
at some index of any infinite index set. -/
theorem exists_mem_eval_ne_zero {b : ℕ → ℂ} (hb : Function.Injective b) {Q : Polynomial ℂ}
    (hQ : Q ≠ 0) {s : Set ℕ} (hs : s.Infinite) : ∃ M ∈ s, Q.eval (b M) ≠ 0 := by
  have h1 : {x : ℂ | Q.eval x = 0}.Finite := by
    apply Set.Finite.subset Q.roots.toFinset.finite_toSet
    intro x hx
    exact Multiset.mem_toFinset.mpr (Polynomial.mem_roots'.mpr ⟨hQ, hx⟩)
  have hfin : {M | Q.eval (b M) = 0}.Finite :=
    (h1.preimage hb.injOn).subset (fun M hM => hM)
  obtain ⟨M, hMs, hM0⟩ := (hs.diff hfin).nonempty
  exact ⟨M, hMs, hM0⟩

end GaloisForLFunctions
