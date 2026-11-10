# Frobenius order at an integer point

- **Stage:** 3-formalized
- **Source:** review-0911 §11.5, construction A.

For a ring with Frobenius lift `ψ_p`, a `p`-derivation `δ_p`, and an
integer point `f`, the exact defect is

`p (f(δ_p a) − δ_p^ℤ(f(a))) = f(ψ_p a) − f(a)`.

Thus the derivative descends at `a` exactly when the point takes the same
value on `ψ_p a` and `a`. Compatibility on all iterated derivatives
transfers the integer valuation law and its sharp product-formula cost.

Without this compatibility, vanishing of the evaluated derivative jets
does not measure the valuation of the evaluated element. On the cofree
arithmetic square take `a=[p]` and the diagonal point `f=x↦x₁`.
Then `f(a)=p`, `δ_p a=0`, and all positive derivative jets vanish, but
`p²∤f(a)`. This is an unconditional counterexample to that interpretation
of the whole-class cost claim.

The ideal-power restriction theorem remains valid:
`map_ghostComponent_ker_pow_prime_pow` gives exactly `(p^m)` on a
prime-power graph. It concerns order along the diagonal ideal, not
evaluated `δ_p` jets. Construction A must distinguish these notions.

Lean: `AbsoluteGeometryOfSpecZ/DeltaOrderDoesNotDescendAtEveryIntegerPoint.lean`:
`delta_descends_iff`, `delta_order_iff_of_compatible`, and
`exists_delta_jets_without_integer_order`. Direct audit passed without
warnings; all three transitive axiom lists contain only `propext`,
`Classical.choice`, `Quot.sound`.
