# Twenty cross-route contributions: CHMD, HF, OWU, EWU

- **ID:** cross-route-twenty-2026-10-17
- **Stage:** 1-in-progress
- **Type:** THEOREM (two completed contributions; original twenty-result goal cleared)
- **Completion status:** Resumed proof-completion scope finished; original twenty-result programme discontinued by the user.
- **Source:** user attachment `6f6034ae-cd9a-40e9-9fb2-e9d49ef0b291/pasted-text-1.txt`
- **Statement:** Find and verify twenty substantive mathematical contributions from combinations of current Lean frontier theorems, advancing CHMD, HF, OWU, or EWU directly or indirectly.

## Contract and completion evidence

The original twenty-result goal was cleared by the user. The follow-up request, “finish unfinished work,” resumes completion and audit of the two existing proof drafts and this checkpoint. It does not restart the twenty-result research loop. Helpers, renamed facts, routine bridges, conditional sign receivers, and unverified conjectures do not count. Existing results from other tasks do not count again.

Use current Lean sources and documented corpus research search. No web, numerical experiments, external novelty claims, added axioms, hidden sign premises, heartbeat increases, full builds, or commits. The frontier map is read-only. Preserve concurrent work. One owned foreground Lean process at a time; final checks use `lake --old env lean` on needed leaves; wire new modules into umbrellas. Run formal lint and inspect axiom dependencies in `/tmp`.

## Completion plan after goal cancellation

1. Preserve and record the completed, audited ground-coordinate completeness result.
2. Finish the existing compact-capacity and imaginary-zero proof drafts.
3. Audit every new public declaration, wire both modules, refresh generated indexes, and run lint.
4. Record exact completion and repository-wide blockers; remove owned scratch artifacts.

`update_plan` is unavailable in the current tool inventory; this card carries task state.

## Verified contribution ledger

Count: **2 / 20** against the original, now-cleared goal. Both proof drafts in the resumed completion scope are finished; the original twenty-result goal is not claimed complete.

1. **Complete odd ground-zero coordinates.** `exists_complete_oddGround_zero_coordinates` and `exists_complete_oddGround_divisors` in `OddSectorGroundCompleteDivisors.lean` construct an actual canonical generator at every positive aperture. All its nonzero zero coordinates, plus the origin derivative coordinate when the generator derivative vanishes, detect exactly the odd ground radical. All eight supporting leaves passed individual `lake --old env lean -j 1` checks. Every public declaration was audited using a temporary scratch file; dependencies are only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired. This is one contribution, not one per helper. No infinite Parseval identity or absolute Weil positivity is claimed.

2. **Finite nonreal ground-zero obstruction.** `exists_oddGround_generator_finite_nonreal_zeros` in `OddSectorImaginaryZeroMorseBound.lean` constructs an actual canonical generator at every positive aperture with only finitely many nonreal zeros. Distinct imaginary zero pairs yield an actual form-orthogonal negative family in the even sector; `CompactFormNegativeCapacity.lean` supplies a common finite bound. Both leaves passed warning-free `lake --old env lean -j 1` builds. All ten public declarations passed the axiom audit with only the same three standard axioms. The final signature has only the positive aperture as an outer input. Both umbrella imports are wired. The generic helper and intermediate transfer laws are parts of this one contribution.

The resumed source work is complete. No added sign hypothesis, axiom, heartbeat increase, full build, or commit was used. Repository-wide lint is a separate gate and is not claimed to pass; final diagnostics are recorded below.

## Current cycle

The current source interfaces distinguish shifted positivity from absolute Weil positivity. OWU already has canonical odd ground generators, simple nonzero transform zeros, and exact finite cardinal interpolation with positive norming constants. CHMD already has actual source graph spectral and nodal decompositions. HF and EWU require absolute sign, not merely shifted ground geometry.

Completed first contribution: completeness modulo the actual arithmetic ground space, including the missing origin coordinate. The ledger above supersedes the historical compiler checkpoints below.

### Exact completeness conjecture and proof strategy

Write `H` for the odd complete CCM form domain, `q` for `arithmeticShiftedForm`, `N` for its actual finite-dimensional radical, and `G` for the canonical odd generator. The conjecture is that the positive cardinal representatives at **all** distinct nonzero squared zeros of `G`, together with one origin derivative representative if `G'(0)=0`, span `H/N` in the `q` norm. Equivalently, a source invisible to every such coordinate lies in `N`. This is stronger than the existing finite interpolation theorem, which selects only an infinite subsequence and supplies no completeness.

Attack: omission of the origin is unjustified. Oddness forces `G(0)=0`, but does not force `G'(0)≠0`. The nonzero-node theorem excludes this point explicitly. Do not claim completeness from its sequence alone.

Dependency-closed paper proof of the origin repair: if `G'(0)=0`, divide successively at zero using the existing compact Fourier division theorem. Differentiating `G(w)=w F_1(w)` gives `F_1(0)=G'(0)=0`, so the second quotient `V` exists and is odd, with `G(w)=w²V(w)`. Its corrected energy is strictly positive: otherwise it is ground and the polynomial representation would give `X P=1`. If `V'(0)=0`, divide it twice again to obtain odd `W`. The exact real-quadratic transfer gives `q(V,V)=q(G,W)=0`, contradiction. For any odd `U` with `U'(0)=0`, the same division and transfer give `q(V,U)=0`. Normalize `E=V/V'(0)`. Subtracting `U'(0)E` from arbitrary `U` therefore gives `q(E,U)=q(E,E)U'(0)`, with positive real `q(E,E)`. Thus the origin contributes precisely one positive derivative coordinate when the derivative of `G` vanishes, and no higher odd order than three is possible. This repair is part of the completeness contribution, not a separate count.

Completeness mechanism: choose an imaginary nonzero point `z` with `G(z)≠0`, set real `c=z²<0`, and define `D_c U=(U-U(z)G/G(z))/(w²-c)`. It preserves `N` by polynomial division. Fourier weight is logarithmic, so division gains enough decay to factor continuously through the compact physical embedding; evaluation is bounded on the fixed physical aperture. On `N`'s orthogonal complement, `q` is an equivalent Hilbert norm because it is a nonnegative identity-minus-compact form. Quadratic transfer makes the compressed `D_c` self-adjoint in that norm. Its kernel is zero: a quotient in `N` forces `U` to be a polynomial multiple of `G`; smooth odd core density and quadratic transfer show every admissible such multiple is ground. The formal proof uses the invariant invisible subspace below, avoiding construction of an infinite expansion.

### Formalization checkpoint

The eight completed leaves are `OddSectorGroundOriginInterpolation`, `OddSectorGroundDivisionOperator`, `OddSectorGroundDivisionCalculus`, `HTGeometry/CompactPositiveFormGap`, `HTGeometry/CoerciveCompactSpectralVanishing`, `OddSectorGroundSpectralQuotient`, `OddSectorGroundDivisionEigenvectors`, and `OddSectorGroundCompleteDivisors`. All passed individual leaf builds and all 54 public declarations have only the three standard axioms. Umbrellas are wired. The origin repair and operator lemmas are parts of one contribution, not separate contributions.

Completeness proof simplification: let `V` be the closed odd subspace invisible at every ground-zero coordinate, including the origin derivative when needed. It contains `N` and is invariant under `D_c`. On `L=V∩Nᗮ`, subtracting the ground projection gives a compact `q`-symmetric operator. Every nonzero eigenvalue `r` determines real `λ=c+1/r`. Quadratic transfer shows its eigenvector annihilates every odd source divisible by `w²−λ`. If `G` vanishes at `λ`, invisibility makes the eigenvector itself divisible. Otherwise subtract a ground multiple to make it divisible. At `λ=0`, use the first derivative instead of evaluation and the origin division lemma. Either way its `q` norm vanishes, contradiction. The compact spectral theorem then forces the compressed operator to be zero; injectivity forces `L=0`. This proves completeness without first classifying an entire eigenbasis.

The final closed-space definition uses `q`-orthogonality to all actual paired divisors of `G`; closure follows directly from form continuity. Every divisor `v=G/(w²−λ)` is an exact eigenvector of normalized division, with coefficient `−Fv(z)/FG(z)`. This proves invariance without separately constructing derivative-evaluation continuity. The eigenvector argument subtracts either a ground multiple or a divisor multiple to kill the relevant coordinate, using nonzero quotient evaluation (or its nonzero first derivative at zero). The final target is `exists_complete_oddGround_zero_coordinates`: an unconditional canonical `G` for which odd sources vanishing at all nonzero zeros and the required origin derivative are exactly the ground radical.

The quotient proof uses named compression, positivity, kernel, and generic metric lemmas, with explicit `Submodule.normedAddCommGroup` and `Submodule.innerProductSpace` arguments. This resolved elaborator exhaustion without changing heartbeat limits. Concurrent edits/commits touched the worktree, including the frontier map; this task has neither edited that map nor made commits.

## Log

### Second contribution: finite imaginary-zero obstruction in the opposite parity

Whole-corpus lexical searches `ground imaginary finite` and the odd-sector negative/paired/parity search found no corresponding result. Source inspection found the existing CCM finite negative-block theorem and finite Schur reduction; these are ingredients, not new contributions. Strict aperture decay already exists for the polar route and is excluded from the novelty ledger.

Paper mechanism: for each distinct imaginary squared zero `λ=-b²<0` of canonical odd `G`, choose the odd divisor `v=G/(w²−λ)`. Its shifted energy is strictly positive. Single Fourier division constructs an actual same-aperture even vector `h` with `Fh=w Fv`. The polarized-product identity gives `q(h_i,h_j)=q(v_i,(w²)v_j)=λ_j q(v_i,v_j)`. Distinct ground divisors are `q`-orthogonal, so the even vectors form a strictly negative diagonal block. The actual corrected form is identity-minus-compact on the full form domain. Its finite Schur exterior is positive, hence every negative block projects injectively into one fixed finite-dimensional complement. Therefore the number of distinct imaginary zero pairs is finite, bounded by a common finite capacity for negative directions. This strengthens the existing cross-axis zero statement to “all but finitely many zeros are real” and connects OWU zero geometry to the opposite-parity Morse obstruction. It does not show that the finite exception set is empty.

Verified generic helper `HTGeometry/CompactFormNegativeCapacity.lean`: all algebraic nonpositive subspaces of an identity-minus-compact form have one uniform finite dimension bound, using projection into the finite Schur complement. Closedness is not assumed. This helper is not separately counted.

Verified source leaf `OddSectorImaginaryZeroMorseBound.lean`: actual even frequency lifts of paired divisors, exact full-form transfer `q(h_i,h_j)=z_j² q(v_i,v_j)`, finite negative families, a uniform imaginary-zero capacity, positive-imaginary-zero finiteness, and an unconditional existence theorem for a canonical generator with finitely many nonreal zeros.

The final paper and Lean proof chooses the existing canonical generator with cross-axis zero geometry. Every nonreal zero is `ib` or `-ib` for some positive imaginary zero `ib`; oddness pairs the two. The positive imaginary zero set is finite by the negative-capacity argument, so its two images cover all nonreal zeros. This discharges the generator premise through the existing existence theorem; only the positive aperture remains as input.

Significance audit: the first contribution closes the infinite completeness gap left by finite interpolation; the second bounds the imaginary exceptions using the actual opposite-parity form. These are two substantive corpus advances, not 64 independent results. Neither supplies absolute Weil positivity or proves RH. External novelty was not assessed, per the user's corpus-only restriction.

## Final verification

- All ten owned Lean leaves passed targeted `lake --old env lean -j 1` checks. The two resumed leaves emitted no warnings. No full or umbrella builds ran.
- All 64 public declarations (54 completeness, 10 capacity/imaginary-zero) were checked with `#print axioms` in temporary files. Every dependency set is exactly `propext`, `Classical.choice`, `Quot.sound`. Final actual-source signatures were inspected; there is no additional sign or RH premise.
- All ten modules are reachable through their area umbrellas. Generated API, gap, overview, and search indexes were refreshed. Scoped `git diff --check` and new-file whitespace checks passed.
- Final `scripts/formal_tools.py lint --check-generated` exited 1 with 17 unrelated integration errors: 16 unreachable modules and `research leaf module at package root: BiScaleUncertainty.lean; move it into an owned theorem area`. There were no stale-generated-file or proof-debt errors in this final run. Existing large-file warnings remain unrelated to these leaves.
- The unreachable modules were `RHTower.EvenSectorSmoothBlindInterpolationObstruction` and `HTGeometry.{FiniteRankTraceDeterminant, HolomorphicRieszFamily, OuterSpectralContinuation, QuasiCompactSpectralCircle, RieszProjectionPowerCalculus, SymbolicHolderSpace, SymbolicLevelSpaces, SymbolicQuasiCompactness, SymbolicRuellePollicott, SymbolicRuellePollicottBounds, SymbolicShiftSpace, SymbolicTraceSplitting, SymbolicTransferBounds, SymbolicTransferHolomorphy, SymbolicTransferOperator}`. These concurrent files were not modified by this task.
- No owned compiler or guarded job remains active. Temporary scratch files and logs were removed after recording this evidence. No frontier-map edits, commits, or pushes were made by this task.

- 2026-10-17: Read task, initialized Serena, inspected read-only route entries and current OWU Lean interfaces. Existing unrelated worktree modifications preserved. Corpus searches underway.
