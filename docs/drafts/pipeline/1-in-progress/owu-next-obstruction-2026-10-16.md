# OWU: next obstruction after canonical ground factorization

Status: PAPER PROOF CLOSED; Lean implementation pending (2026-10-17).

## Scope and plan

Produce one further unconditional structural advance for OWU. The existing
canonical factorization is the starting point, not the requested contribution.
Use the Lean corpus and documented research search, without external search,
numerical experiments, novelty checks, or old research notes. Preserve
concurrent edits. Build only needed leaf modules, sequentially and in the
foreground; audit with `lake --old env lean`, no heartbeat increases.

1. Search the current corpus across route boundaries for missing mechanisms.
2. Conjecture, attack, record failure precisely, and continue.
3. Complete a dependency-closed paper proof before adding Lean code.
4. Formalize, audit axioms, wire the umbrella, lint, and clean owned scratch.

`update_plan` and `multi_tool_use.parallel` are unavailable. This file tracks
progress; independent tool reads use awaited parallel calls. Serena's Lean
symbol lookup was already found unavailable in this session.

## Starting point

At every positive aperture the actual corrected odd ground eigenspace is
`{P(w²)F_G(w): deg P<dim S}`, with a common generator unique up to scalar and
zeros on the two axes. Every blind minimizer belongs to this space. The blind
minimum's sign, an odd-positive arithmetic weight, and all-scale dilation
positivity remain open.

## Conjecture loop

1. Derivative closure might force a simple ground eigenspace. Failed: the
   corpus criterion needs an actual derivative in the form domain. Neither
   regularity nor a simple eigenspace can be assumed.
2. Further scalar purification might eliminate the optimizer obstruction.
   Rejected as duplicate: exact smooth odd scalarization and completion are
   already in the corpus.
3. Uniqueness of optimal arithmetic multipliers might make the generator
   intrinsic. Failed: independence of the compressed arithmetic operators is
   not established; their kernels cannot be ignored.
4. Averaging all feasible dual corrections should realize their common
   kernel. The finite-dimensional argument works, but is a generic convex
   fact and does not remove the requested hard analytic obstruction.
5. A single axis-zero division should retain the ground. Failed: the
   off-axis splitting coefficient is Im(z²), which vanishes on both axes.
   Positive survivor: real squared-zero multiplication transfers between
   the arguments of the full corrected Hermitian form. Combined with a
   *second* division, this rules out a repeated nonzero generator zero.
6. Stronger survivor: the same transfer gives positive Riesz representatives
   for evaluation at every nonzero generator zero, orthogonal for distinct
   squared zeros. This closes the exact finite interpolation problem and
   classifies all minimizers, without a nonvanishing or simplicity premise.

## Corpus evidence

Documented research searches covered ground multiplicity, division, spectral
factorization, purification, and interpolation; source searches checked the
actual relevant declarations. Search metadata reported an older coverage
snapshot and unavailable semantic coverage. Results are leads, not proofs of
absence. The polar-ground quadrature module supplies only a polar-constrained
frequency form and assumes nonzero quotient evaluations in its quadrature
statement. OWU needs the full signed pole term and exact arithmetic correction.
The new argument uses the actual canonical OWU generator and discharges the
nonvanishing obstruction rather than adding it as a hypothesis.

## Dependency-closed paper proof

Fix any positive aperture. Write F_u for the entire Fourier–Laplace transform,
q for `arithmeticShiftedForm`, S for `oddArithmeticGroundSpace`, and G for the
existing canonical generator. Already proved: q is Hermitian, nonnegative on
odd vectors; q(G,u)=0 for every form vector u; an odd vector has q(u,u)=0 iff
it belongs to S; every member of S is P(w²)F_G for a polynomial P; F_G is
nonzero and all its zeros lie on the two axes.

**Paired division.** If u is odd, z≠0, and F_u(z)=0, ordinary same-aperture
division at z and -z produces v with F_u(w)=(w²-z²)F_v(w) everywhere. The
quotient is odd: cancel the even polynomial off its finite zero set and
extend by continuity. This needs no derivative-domain assumption.

**Full-form transfer.** Suppose c is real and form vectors u,v,k,h satisfy
F_u(w)=(w²-c)F_k(w) and F_v(w)=(w²-c)F_h(w). Then q(u,h)=q(k,v).
On the real frequency line the multiplier is real. At the two polar points
it is conjugation-compatible, so the polarized pole products obey the same
identity. The frequency density, every arithmetic cosine correction, and
the mass term therefore transfer exactly. Polarization recovers both real
and imaginary parts; no positive pole replacement is made.

**Positive norming and simplicity.** Take any nonzero zero z of F_G and put
c=z², which is real by the established two-axis theorem. Paired division
gives v_z. If q(v_z,v_z)=0, v_z belongs to S, hence F_v=P(w²)F_G. Cancellation
would give (X-c)P=1, impossible on evaluating at c. Nonnegativity therefore
gives q(v_z,v_z)>0. If F_v(z)=0, divide again: F_v=(w²-c)F_k. Transfer gives
q(v,v)=q(k,G)=0, contradiction. Thus F_v(z)≠0 and differentiating the entire
factorization yields F_G'(z)=2zF_v(z)≠0. This proves simplicity, including
imaginary-axis and polar-point zeros, without excluding any nonzero node.

**Evaluation representatives.** For any odd u vanishing at z, paired division
and transfer give q(u,v_z)=0. Set e_z=v_z/F_v(z), so F_e(z)=1, and set
rho_z=q(e_z,e_z)>0. Subtracting F_u(z)e_z from arbitrary odd u gives
q(e_z,u)=rho_z F_u(z). This is an exact Riesz identity for the actual corrected
form, not a bound or a conditional positivity receiver.

**Exact finite interpolation.** Choose any finite list z_i of nonzero zeros
with pairwise distinct squares. Factorization gives F_{e_j}(z_i)=delta_ij.
Consequently q(e_i,e_j)=rho_i delta_ij. For arbitrary complex data b_i define
I(b)=sum_i b_i e_i. It is an odd form vector, F_I(z_i)=b_i, and
q(I(b),I(b))=sum_i rho_i |b_i|². Every odd u with the same data satisfies the
exact decomposition

    q(u,u) = sum_i rho_i |b_i|² + q(u-I(b),u-I(b)).

The final term is nonnegative. Equality with the explicit minimum occurs
exactly when u-I(b) belongs to S. Thus the interpolant exists in the actual
same-aperture form domain, its positive norming data are nondegenerate, and
all minimizers form the affine space I(b)+S. No external premise is needed.

**Nonvacuity at every finite size.** The corpus theorem
`zeroSet_infinite_of_subquadratic_twoRayDecay` applies to every same-aperture
Fourier–Laplace transform: compact support supplies an exponential envelope,
and the Riemann–Lebesgue lemma gives decay on both real rays. Therefore its
zero set is infinite. Removing zero preserves infinitude; squaring has finite
fibers because X²-c is a nonzero polynomial. The squared nonzero zero set is
infinite and admits a sequence of distinct values with actual zero lifts.
Consequently the exact interpolation construction is available at every
finite dimension, without an external existence-of-nodes premise.

## Scope of advance and remaining obstruction

This removes repeated nonzero generator zeros and degenerate zero-quotient
coordinates, then solves the resulting finite spectral interpolation problem
exactly for OWU's signed, arithmetic-corrected form. It does not establish
the sign of the unshifted blind minimum, exclude imaginary-axis zeros, claim
completeness of an infinite interpolation expansion, or claim RH.

`docs/reports/rh-current-frontier-map.md` is read-only and will not be edited.
