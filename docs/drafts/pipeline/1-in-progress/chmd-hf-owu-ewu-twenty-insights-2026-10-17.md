# Twenty cross-route contributions: CHMD, HF, OWU, EWU

- **ID:** cross-route-twenty-2026-10-17
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** user attachment `6f6034ae-cd9a-40e9-9fb2-e9d49ef0b291/pasted-text-1.txt`
- **Statement:** Find and verify twenty substantive mathematical contributions from combinations of current Lean frontier theorems, advancing CHMD, HF, OWU, or EWU directly or indirectly.

## Contract and completion evidence

The task remains active until twenty independent significant results are proved and audited. Helpers, renamed facts, routine bridges, conditional sign receivers, and unverified conjectures do not count. Existing results from other tasks do not count again.

Use current Lean sources and documented corpus research search. No web, numerical experiments, external novelty claims, added axioms, hidden sign premises, heartbeat increases, full builds, or commits. The frontier map is read-only. Preserve concurrent work. One owned foreground Lean process at a time; final checks use `lake --old env lean` on needed leaves; wire new modules into umbrellas. Run formal lint and inspect axiom dependencies in `/tmp`.

## Plan

1. Inspect current route interfaces and search whole corpus for mechanisms that address their actual open cores.
2. State and attack exact conjectures; complete paper proofs before Lean. Record failed conjectures and strongest positive survivors.
3. Formalize each surviving independent contribution, audit signatures/dependencies/build output, and count only after significance review.
4. Repeat until twenty qualifying contributions; retain an explicit ledger and unresolved next conjecture.

`update_plan` is unavailable in the current tool inventory; this card carries task state.

## Verified contribution ledger

Count: **0 / 20**. No mathematical result yet claimed for this task.

## Current cycle

The current source interfaces distinguish shifted positivity from absolute Weil positivity. OWU already has canonical odd ground generators, simple nonzero transform zeros, and exact finite cardinal interpolation with positive norming constants. CHMD already has actual source graph spectral and nodal decompositions. HF and EWU require absolute sign, not merely shifted ground geometry.

Candidate under investigation: a complete odd spectral expansion modulo the actual arithmetic ground space, including all missing origin coordinates, rather than another finite interpolation identity. Need establish completeness and identify any residual signed information. This is not yet a theorem or counted contribution.

### Exact completeness conjecture and proof strategy

Write `H` for the odd complete CCM form domain, `q` for `arithmeticShiftedForm`, `N` for its actual finite-dimensional radical, and `G` for the canonical odd generator. The conjecture is that the positive cardinal representatives at **all** distinct nonzero squared zeros of `G`, together with one origin derivative representative if `G'(0)=0`, span `H/N` in the `q` norm. Equivalently, a source invisible to every such coordinate lies in `N`. This is stronger than the existing finite interpolation theorem, which selects only an infinite subsequence and supplies no completeness.

Attack: omission of the origin is unjustified. Oddness forces `G(0)=0`, but does not force `G'(0)≠0`. The nonzero-node theorem excludes this point explicitly. Do not claim completeness from its sequence alone.

Dependency-closed paper proof of the origin repair: if `G'(0)=0`, divide successively at zero using the existing compact Fourier division theorem. Differentiating `G(w)=w F_1(w)` gives `F_1(0)=G'(0)=0`, so the second quotient `V` exists and is odd, with `G(w)=w²V(w)`. Its corrected energy is strictly positive: otherwise it is ground and the polynomial representation would give `X P=1`. If `V'(0)=0`, divide it twice again to obtain odd `W`. The exact real-quadratic transfer gives `q(V,V)=q(G,W)=0`, contradiction. For any odd `U` with `U'(0)=0`, the same division and transfer give `q(V,U)=0`. Normalize `E=V/V'(0)`. Subtracting `U'(0)E` from arbitrary `U` therefore gives `q(E,U)=q(E,E)U'(0)`, with positive real `q(E,E)`. Thus the origin contributes precisely one positive derivative coordinate when the derivative of `G` vanishes, and no higher odd order than three is possible. This repair is part of the completeness contribution, not a separate count.

Remaining completeness mechanism: choose an imaginary nonzero point `z` with `G(z)≠0`, set real `c=z²<0`, and define `D_c U=(U-U(z)G/G(z))/(w²-c)`. It preserves `N` by polynomial division. Fourier weight is logarithmic, so division gains enough decay to factor continuously through the compact physical embedding; evaluation is bounded on the fixed physical aperture. On `N`'s orthogonal complement, `q` is an equivalent Hilbert norm because it is a nonnegative identity-minus-compact form. Quadratic transfer makes the compressed `D_c` self-adjoint in that norm. Its kernel is zero: a quotient in `N` forces `U` to be a polynomial multiple of `G`; smooth odd core density and quadratic transfer show every admissible such multiple is ground. Compact spectral theory then gives a basis. Its nonzero eigenvalue equation forces each eigenvector to be a ground-zero quotient modulo `N`; the origin repair supplies the sole exceptional node. Formal proofs of these analytic and operator steps remain required before claiming the completeness theorem.

## Log

- 2026-10-17: Read task, initialized Serena, inspected read-only route entries and current OWU Lean interfaces. Existing unrelated worktree modifications preserved. Corpus searches underway.
