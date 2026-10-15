# HCF structural research after first-contact rigidity

Status: formalized and directly audited; one unrelated repository lint failure recorded below.

Objective: a further unconditional structural advance for HCF, beyond the
completed single-window transition and finite first-contact rigidity. An
estimate, RH equivalence, conditional source receiver, or repackaging of those
results does not satisfy this task.

Plan:
1. Search the current Lean corpus for unresolved structural obstacles and
   mechanisms that can remove them. Use completed prior proofs as input.
2. Conjecture, attack, and record what each failure rules out or exposes.
3. Formalize a successful dependency-closed structural theorem with no added
   source or RH premises; continue the loop until this is achieved.
4. Focused foreground builds only; direct final `lake env lean` audits, standard
   axiom checks, umbrella imports, index/lint, and cleanup of owned scratch.

Constraints: no web, novelty search, old research markdown, numerical
experiments, heartbeat changes, full/umbrella builds, commits, or pushes.
Preserve concurrent work, including the in-progress even-sector source work.

Starting mathematical facts: actual even ground energy strictly decreases with
aperture; a unique possible heat-window transition is proved. Every actual
finite heat-Hankel first contact has a strictly positive preceding head, a
single normalized null direction, positive quadrature with simple real nodes,
and a strictly earlier first contact at the next rank. Neither result orients
the completed prime--Gamma source. Ground-generator classification allows
derivative chains, so generator existence alone does not prove simplicity.

Search/conjecture ledger follows as the work progresses.

## Conjecture loop

1. Ground-generator existence might force simplicity. Rejected: the actual
   polynomial-generator theorem allows derivative chains. Boundary-source
   nonvanishing on the whole constrained sector does not imply nonvanishing
   or injectivity on the ground space. No valid source argument closes this.
2. At every heat time, regular Hankel heads should be cofinal, and every gap
   should have an exact polynomial-kernel classification. Paper mechanism:
   after a regular head of size n, take its canonical monic admission P.
   Nondegeneracy gives a first j with L(X^j P) nonzero; orthogonality gives
   j >= n. Set d = j - n + 1. Then the block X^r P, 0 <= r < d,
   is orthogonal to the old head and has a nonzero constant anti-diagonal,
   with zero entries before it. For 0 <= k <= d, the kernel at size n+k
   consists exactly of Pq with deg q < min(k,d-k). Polynomial division and
   the highest coefficient of q prove both directions. Thus n+d is the
   next regular head, every intervening head is singular, and recursion
   produces a cofinal regular ladder without a generic-time assumption.
   This is an exact classification, not a positivity receiver or estimate.
   Core classification, cofinality, covering existence and uniqueness now
   pass Lean. The exact kernel parametrization is a linear isomorphism from
   `Fin (min k (d-k)) -> R`; its nullity formula and the constant
   anti-diagonal Gram block also pass focused Lean builds. Full inertia and
   source orientation are not claimed by this argument.
3. Every genuine gap should produce an explicit hyperbolic plane orthogonal
   to its old head. Let Q = X^(d-1) P, delta = L(P Q) != 0 and
   R = Q - L(Q^2)/(2 delta) P. Then L(P^2) = L(R^2) = 0 and
   L(P R) = delta. Hence U = P + R/delta and V = P - R/delta have
   Gram matrix diag(2,-2). This is a constructive resolution of the zero
   pivot, not a sign assumption. Paper proof and focused Lean build complete.

## Actual source and result

`heatHankel_mapReal_eq_momentRows` expresses the actual complex heat pairing
of a real polynomial with an arbitrary complex polynomial in its real moment
rows. Consequently the existing actual heat-form nondegeneracy theorem proves
`nondegenerate_heatRealMoments` without any new source premise.

`hcf_normal_block_resolution` produces the unique covering block at every
positive heat time and every rank, its next invertible head, its complete
matrix kernel, and its exact nullity. `hcf_regular_heads_cofinal` excludes a
terminal singular tail. `hcf_singular_section_resolution` produces, for any
singular section, the explicit orthogonal hyperbolic plane before the next
regular head. Each capstone takes only the positive heat time and rank.

Files:
- HTGeometry/MomentHankelNormalBlocks.lean
- HTGeometry/MomentHankelNormalKernel.lean
- HTGeometry/MomentHankelHyperbolicResolution.lean
- RHTower/XiGaussianHeatNormalBlockResolution.lean

All four focused `lake --old build +Module:olean` targets pass. The final
actual-source build and warning cleanup pass. Umbrellas are wired without
building them. All four final direct `lake env lean` audits of the actual tree
files pass without warnings, sequentially in one foreground job. Eight
`#print axioms` checks in `/tmp` return only `propext`, `Classical.choice`,
and `Quot.sound`. No added axioms, hypotheses in the actual capstones,
heartbeat changes, numerical experiments, or full/umbrella builds were used.

Final corpus search finds both actual capstones in their source module.
`git diff --check` passes for the touched scope. `scripts/formal_tools.py lint`
completed with one unrelated error: concurrent module
`RHTower.EvenSectorDetunedReflection` is unreachable from its umbrella. All
four new modules here are wired; the unrelated work was preserved.
Owned `/tmp/hcf3*` proof probes, search results and audit logs were removed
after their results were recorded. No owned build or search process remains.

Scope: this closes the singular-pivot obstruction in finite-section geometry,
including arbitrary singular heat times and multiple-dimensional kernels.
It does not prove full block-inertia counting or select the RH/source-positive
branch. No such source claim is hidden in a hypothesis of the capstones.

Corpus searches used the documented research command in deep mode, followed
by exhaustive focused Lean-source searches. The normal-block search was
partial but its file inventory complete; no existing normal-index/kernel-gap
classification was found. Ground search completed. Source declarations are
checked directly rather than trusting stale compiler-index metadata.
