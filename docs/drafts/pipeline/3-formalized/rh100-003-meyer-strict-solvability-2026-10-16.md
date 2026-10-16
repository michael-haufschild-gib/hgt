# Contribution 003: strict solvability on literal Meyer cohomology

Status: formalized, directly audited, wired, and axiom-audited. One contribution.
Goal progress: 3 / 100. Previous turn classified as verified progress (002).

## Obstacle and result

The corpus already classified the algebraic range of every finite generator
word with arbitrary coupling among its resonant Xi jets. Algebraic solvability
did not supply closed range, a separated complete natural quotient, or
continuous dependence of solution classes. A discontinuous finite obstruction
map would invalidate passage from approximate solutions to exact solutions.

For every finite word L and every endomorphism B of its full resonant Xi jet
packet, let Q be literal strong-log Poisson cohomology and
T = W_L(A) + J_S B E_S, with S = WordXiSupport(L). The new unconditional result is

    range(T) is closed, and Q / ker(T) ≃L[ℂ] range(T).

The topology is the natural all-weight, all-derivative source topology and its
actual quotient topology. It is not a substituted separation or divisor model.
Every convergent family of outputs T(u_i) has an exactly solvable limit, even
when the chosen u_i do not converge. The finite-rank repaired words are open
surjections: each source neighbourhood solves an entire data neighbourhood.

This enables limit constructions and stable solution classes for the whole
finitely coupled family on the original source. The contribution is the
analytic upgrade as a whole, not its supporting gauge estimates or helper count.

## Corpus inputs across routes

- Route E: `deningerExpSchwartzOfStrongLogDecay` identifies strong-decay
  functions with actual exponential Schwartz sources.
- Meyer source: `deningerPoissonMeyer_range_isClosed` and source completeness
  establish the genuine Poisson embedding in the original seminorm topology.
- Finite causal Xi synthesis: `deningerMeyerCoupledSourceOperator_range`,
  full-multiplicity packet evaluations, causal sections, and repaired-word
  surjectivity supply the exact algebraic obstruction and actual preimages.
- HTGeometry: `GaloisForLFunctions.isOpenMap_of_surjective` supplies the
  formalized Fréchet open mapping theorem.

## Dependency-closed paper proof

1. Reverse Route E's source realization using exponential Schwartz derivative
   bounds. The resulting linear equivalence preserves the underlying function
   and sends the actual strong Poisson boundary to the original Meyer boundary.
2. For Meyer seminorm p(m,n) and integral weighted derivative gauge G(n,k),
   prove p(m,n) ≤ ||G(n,m)|| + ||G(n,-m)|| and
   ||G(n,k)|| ≤ p(|k|,n). Hence the source equivalence and its inverse are
   continuous for their existing, independently defined topologies.
3. Transfer actual boundary closedness through that equivalence. The strong
   source is complete and separated; its literal quotient Q is Hausdorff,
   complete, and first countable. Scoped instances expose precisely this
   natural topology without replacing ambient instances globally.
4. Realize every Mellin jet by exponential weighting, polynomial
   multiplication in Schwartz space, Fourier transform, and point evaluation.
   All operations are continuous. Boundary annihilation descends these
   functionals to Q. The gauge identity G(n,k)(Ag) = -G(n+1,k)(g) proves
   continuity of the actual generator. Finite-dimensional causal sections and
   finite packet operators are continuous, so T is continuous.
5. The existing exact range formula is
   range(T) = E_S^{-1}(range(W_L(A_S)+B)). The finite packet range is closed;
   continuity of E_S proves that the actual source range is closed.
6. That closed range is Fréchet. Apply open mapping to the continuous
   surjection T: Q → range(T). Its quotient property makes the inverse of
   the canonical algebraic first-isomorphism map continuous. This produces
   the displayed continuous linear equivalence with the actual kernel.
7. Closedness gives exact solvability of output limits. Existing surjectivity
   of the repaired word plus continuity and open mapping gives the stated
   neighbourhood solvability on all of Q.

## Conjecture loop and retained limitations

Initial question: can generator invariance be promoted to original dilation
invariance of finite causal chains or a global arithmetic complement? Current
Lean searches did not supply that covariance. No such result is claimed.

The topology bridge succeeded and exposed the stronger strict-solvability
target. One attempted inference failed: the invisible sector's injectivity as
a polynomial module is Baer injectivity, not injectivity of multiplication by
a polynomial. Thus it cannot prove a zero homogeneous kernel. The successful
theorem retains ker(T) explicitly and needs no continuous global complement.

Kernel finiteness, a continuous linear choice of representatives, positivity,
and original-flow covariance remain unproved here. No Fredholm index or RH
conclusion is asserted. Finite cofinal interpolation singularity and off-line
half-density graph obstructions were also checked in the current Lean corpus;
this result does not erase either obstruction.

## Formal audit

Four new leaves, each directly checked in the foreground with
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/<name>.olean GaloisForLFunctions/RHTower/<name>.lean`:

- `DeningerMeyerStrongLogSourceEquivalence`
- `DeningerMeyerStrongLogFrechet`
- `DeningerMeyerStrongLogOperatorContinuity`
- `DeningerMeyerStrictCoupledSolvability`

All four exited 0 and are imported individually by `RHTower.lean`.
Twenty `#print axioms` checks in a temporary file exited 0; every audited
declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`.
`scripts/formal_tools.py lint` exited 0: `formal lint passed`, with existing
large-file warnings. The prior turn's concurrent missing imports are resolved
in the authoritative worktree at this audit. `git diff --check` passed.

No web, external novelty search, numerical experiment, added axiom, proof hole,
heartbeat increase, full build, umbrella build, commit, or push. Owned temporary
search and Lean scratch files were removed; concurrent edits were preserved.

Search provenance: documented deep corpus searches for source topology, finite
packet/original flow, strong-log equivalence, and Euler-Schwartz division.
The topology-bridge search reported partial coverage; all used declarations
were verified directly in current Lean source and by the compiler. Search
outputs were evidence for leads, never proof certificates.
