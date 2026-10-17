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

### Formalization checkpoint

`OddSectorGroundOriginInterpolation.lean` passed its leaf build. The origin repair is not counted separately. `OddSectorGroundDivisionOperator.lean` is under compiler repair; `OddSectorGroundDivisionCalculus.lean` and `HTGeometry/CompactPositiveFormGap.lean` are drafted but not yet checked. No umbrella or frontier-map edits made.

Completeness proof simplification: let `V` be the closed odd subspace invisible at every ground-zero coordinate, including the origin derivative when needed. It contains `N` and is invariant under `D_c`. On `L=V∩Nᗮ`, subtracting the ground projection gives a compact `q`-symmetric operator. Every nonzero eigenvalue `r` determines real `λ=c+1/r`. Quadratic transfer shows its eigenvector annihilates every odd source divisible by `w²−λ`. If `G` vanishes at `λ`, invisibility makes the eigenvector itself divisible. Otherwise subtract a ground multiple to make it divisible. At `λ=0`, use the first derivative instead of evaluation and the origin division lemma. Either way its `q` norm vanishes, contradiction. The compact spectral theorem then forces the compressed operator to be zero; injectivity forces `L=0`. This proves completeness without first classifying an entire eigenbasis.

The final closed-space definition uses `q`-orthogonality to all actual paired divisors of `G`; closure follows directly from form continuity. Every divisor `v=G/(w²−λ)` is an exact eigenvector of normalized division, with coefficient `−Fv(z)/FG(z)`. This proves invariance without separately constructing derivative-evaluation continuity. The eigenvector argument subtracts either a ground multiple or a divisor multiple to kill the relevant coordinate, using nonzero quotient evaluation (or its nonzero first derivative at zero). The final target is `exists_complete_oddGround_zero_coordinates`: an unconditional canonical `G` for which odd sources vanishing at all nonzero zeros and the required origin derivative are exactly the ground radical.

Checked intermediate leaves: `OddSectorGroundDivisionOperator`, `HTGeometry/CompactPositiveFormGap`, `HTGeometry/CoerciveCompactSpectralVanishing`. Origin and division are being rebuilt after exporting four proof helpers. Drafted but not fully checked: `OddSectorGroundDivisionCalculus`, `OddSectorGroundSpectralQuotient`, `OddSectorGroundDivisionEigenvectors`, `OddSectorGroundCompleteDivisors`. Count remains **0/20**. Concurrent edits/commits have touched the worktree, including the frontier map; this task has not modified that map.

## Log

### Next candidate: finite imaginary-zero obstruction in the opposite parity

Whole-corpus lexical searches `ground imaginary finite` and the odd-sector negative/paired/parity search found no corresponding result. Source inspection found the existing CCM finite negative-block theorem and finite Schur reduction; these are ingredients, not new contributions. Strict aperture decay already exists for the polar route and is excluded from the novelty ledger.

Paper mechanism: for each distinct imaginary squared zero `λ=-b²<0` of canonical odd `G`, choose the odd divisor `v=G/(w²−λ)`. Its shifted energy is strictly positive. Single Fourier division constructs an actual same-aperture even vector `h` with `Fh=w Fv`. The polarized-product identity gives `q(h_i,h_j)=q(v_i,(w²)v_j)=λ_j q(v_i,v_j)`. Distinct ground divisors are `q`-orthogonal, so the even vectors form a strictly negative diagonal block. The actual corrected form is identity-minus-compact on the full form domain. Its finite Schur exterior is positive, hence every negative block projects injectively into one fixed finite-dimensional complement. Therefore the number of distinct imaginary zero pairs is finite, bounded by an actual even negative-direction capacity. This would strengthen the existing cross-axis zero statement to “all but finitely many zeros are real” and connect OWU zero geometry to the opposite-parity Morse obstruction. Not yet formalized or counted.

- 2026-10-17: Read task, initialized Serena, inspected read-only route entries and current OWU Lean interfaces. Existing unrelated worktree modifications preserved. Corpus searches underway.
