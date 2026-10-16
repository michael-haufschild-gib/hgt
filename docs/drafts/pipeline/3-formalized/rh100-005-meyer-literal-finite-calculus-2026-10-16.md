# Contribution 005: complete finite-order calculus on literal Meyer cohomology

Status: formalized and audited. Ledger 5 / 100. One contribution, comprising
six supporting leaves. Contribution 004's finite-flow covariance is baseline.

Hard obstacle removed: invisible homogeneous ambiguity on the full literal
Poisson quotient. The existing arithmetic-complement calculus and literal
closed-range theorem did not control the full homogeneous kernel. Cyclic Xi
boundary generation and closed source division now eliminate all invisible
finite-word torsion. Every finitely coupled word has exactly its finite Xi
packet kernel, and the fixed finite-rank repair has a continuous two-sided
inverse on the whole literal quotient.

Plan: search current Lean corpus across source division, Schwartz synthesis,
and global topology; attack competing exact conjectures; complete a paper
proof of a distinct structural advance; formalize, audit each leaf directly,
check axioms and formal lint, wire umbrellas, and clean owned scratch.

Initial questions: can source Euler division control polynomial torsion of the
invisible kernel? Can the natural topology produce infinite causal synthesis
or obstruct a continuous global arithmetic complement? Finite covariance
alone settles neither. Baer injectivity is not multiplication injectivity.

Use the hgtl7 research loop with the user's explicit overrides: local Lean
corpus only; no external literature/novelty search, old reports, numerical
experiments, full builds, heartbeat increases, or added premises. Preserve
concurrent research files. Count only a distinct audited structural theorem.

## Proven mechanism

Result: polynomial torsion is eliminated from the invisible sector on the
literal quotient. All finite-word homogeneous solutions are finite Xi Jordan
packets. Finite-order spectral calculus no longer requires passage to a
chosen algebraic complement.

Direct Euler integration on the cap leaves a nontrivial origin-regularity
proof. A stronger structural route uses Gaussian–Hermite approximation:

1. Hermite expansions converge in every oscillator seminorm; those seminorms
   control the full Schwartz topology. Thus polynomial Gaussians are dense.
2. On the even Gaussian monomials, negative Euler differentiation obeys
   A(x^(2n)g) = 2 pi x^(2n+2)g - 2n x^(2n)g. Consequently the polynomial
   Euler orbit of g is dense in the even Schwartz subspace.
3. Evaluation at zero and Fourier evaluation at zero read P(A)g as P(0)
   and P(1). A continuous finite-rank correction of Gaussian polynomials
   therefore approximates every cap source inside the ideal X(X-1).
4. The exact Xi cap is A(A-1)g. Hence its polynomial Euler orbit is dense
   in the original cap, and its Poisson image has closure equal to the full
   actual boundary range in the natural strong topology.
5. On the strong source, A-lambda is injective by faithful entire Mellin
   transform. Its range is the closed Mellin-evaluation hyperplane by causal
   division. The Frechet open mapping theorem gives a continuous inverse on
   that range.
6. Suppose u is invisible and (A-lambda)u=0. For a representative g,
   (A-lambda)g is an actual boundary. Approximate it by p_i(A)b, where b is
   the fixed Xi boundary source. Let d be the zero order of Xi at lambda.
   The d-th Mellin jet of (A-lambda)g is zero: for d=0 this is the factor
   s-lambda; for d>0 invisibility annihilates the required jet of g.
7. The same jet of p_i(A)b is p_i(lambda) times the nonzero d-th Xi jet.
   Subtract p_i(lambda)b. This correction tends to zero, and each corrected
   polynomial is divisible by X-lambda. Its source preimage is again an
   actual boundary. Continuity of the strong-source inverse and closedness
   of the boundary range imply g is a boundary, so u=0.
8. Iterate injectivity on the invariant invisible sector. For a finite-word
   homogeneous class subtract its finite causal projection. Existing packet
   algebra makes the remainder invisible, so it vanishes. Full kernels now
   equal their finite Xi packets; the existing solvability and topology then
   yield actual finite-order Fredholm structure.

The Gaussian cyclic-density identification and topological saturation are
both formally audited, completing this dependency-closed proof.
It does not assert that the entire invisible sector vanishes. A nonzero
torsion-free divisible invisible sector remains logically possible.

## Formal results

Direct leaf audits passed, and umbrella imports added:

- `DeningerMeyerGaussianEulerDensity`: full Schwartz Hermite convergence and
  density of the Gaussian polynomial Euler orbit in even Schwartz space.
- `DeningerMeyerCyclicCap`: endpoint evaluations are polynomial values at 0
  and 1; exact Xi cap is the X(X-1) Gaussian source; its orbit is dense.
- `DeningerMeyerCyclicBoundary`: forward Poisson continuity follows from the
  existing strict inverse and Frechet open mapping; its closed cyclic orbit
  equals the entire actual boundary range.
- `DeningerMeyerSourceShiftTopology`: every source shift is injective, has
  exactly the closed Mellin hyperplane as range, and is a closed map with
  continuous inverse onto that range.

- `DeningerMeyerInvisibleTorsionFree`: the core saturation argument passed;
  every complex shift and every finite word is bijective on the invisible
  sector of the literal quotient. This eliminates finite-order homogeneous
  modes without asserting the sector itself vanishes.

- `DeningerMeyerLiteralFiniteCalculus`: direct audit passed. The kernel of
  every finitely coupled word is exactly the causal section of its finite
  packet kernel, hence finite dimensional. Every fixed finite-rank repair is
  a continuous automorphism of literal cohomology, with a unique solution
  class for every forcing.

All six leaves are wired. Formal lint passed with preexisting large-file
warnings. All 39 public declarations passed the separate axiom audit, with
exactly `propext`, `Classical.choice`, and `Quot.sound` as dependencies.

Proof simplification: no approximation sequence or choice of polynomial
preimages is needed. The shift image of the closed boundary is closed.
Subtracting the normalized leading Xi jet is a continuous rank-one map that
sends every cyclic polynomial into this closed shift image. Closure then
gives exact source boundary division.

## Exact new solution class

Let Q be literal cohomology, A its actual generator, W_L a finite word,
S its full resonant Xi support, E_S the full jet map, and J_S its causal
section. For every finite packet operator B, without extra premises,

    ker(W_L(A) + J_S B E_S) = J_S ker(W_L(T_S) + B).

The right side is finite dimensional. Taking B = I - W_L(T_S) gives a
continuous automorphism of Q and a unique solution class for every forcing.
Together with the previously established exact range and cokernel, this
completes the finite obstruction model on the actual source quotient.

Key declarations: `deningerMeyerInvisibleGeneratorWord_bijective`,
`deningerMeyerLiteralCoupled_kernel`, and
`deningerMeyerRegularizedSourceWordContinuousEquiv`.

Corpus ingredients: nuclear Hermite synthesis (`DeningerSchwartzNuclear`,
`HermiteCoordinateMoments`); the exact Connes–Consani theta/Poisson Xi cap
(`CCMConnesConsaniZetaCycles`, `DeningerMeyerExactXiCapSource`); Hedenmalm
multiplicity chains and actual causal division (`DeningerMeyerXiCausalChains`);
strict original-source embedding and natural Frechet exactness
(`DeningerMeyerStrictEmbedding`, `DeningerMeyerStrongLogSourceEquivalence`);
finite packet solvability (`DeningerMeyerFiniteRankSourceSolvability`).

## Audit and scope

Each leaf passed a foreground `lake --old env lean -o <leaf.olean> <leaf.lean>`
audit from `formal/`. Only one owned Lean process ran at a time. No full or
umbrella builds, numerical experiments, extra axioms, proof holes, or
heartbeat increases. A separate `/tmp` file audited all 39 public declarations.
`scripts/formal_tools.py lint` passed. All six umbrella imports were checked.
Owned scratch inputs, search outputs, and audit logs were removed after review.

The invisible sector itself may remain nonzero and torsion free. No positive
Hodge form, infinite-packet synthesis, or RH conclusion is supplied. Routine
finite resolvent consequences should not be counted as another contribution.
