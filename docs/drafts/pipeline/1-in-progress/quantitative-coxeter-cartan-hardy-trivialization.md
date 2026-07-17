# The `O(N)` exchange cocycle admits a uniformly conditioned Coxeter--Cartan frame

- **ID:** `quantitative-coxeter-cartan-hardy-trivialization`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / QUANTITATIVE COMPLEX ANALYSIS / COMPACT-LOCAL QFT GATE
- **Scientific status:** `[CONJECTURE] [PUBLISHED OPEN PROBLEM SHARPENED]`
  `[NOT A NEW CONJECTURE] [NEW ATTACK UNVERIFIED]`
- **Scope:** the standard regular `O(N)` identity-zero adjacent-braid scattering family,
  `N>=3`; no RH and no distinguished scalar special-function input
- **Parent:**
  `../2-fully-proven/not_new_scientific_knowledge/fixed-particle-holomorphic-acyclicity-identity-zero-yang-baxter.md`
- **Statement:** On the Alazzawi--Lechner particle tubes, the standard `O(N)` braid cocycle has
  exact holomorphic frames `J_n` satisfying

  ```text
  J_n(z) B_k(z_(k+1)-z_k)=-J_n(z^tau_k)                    (1)
  ```

  and constants `gamma,gamma_tilde` independent of `n` such that

  ```text
  sup_(z in Omega_n) ||J_n(z)|| <= gamma^n,
  sup_(theta in R^n) ||J_n(theta+i lambda_(pi/2))^(-1)||
    <= gamma_tilde^n.                                       (2)
  ```

## Why this is the exact open theorem

The fixed-particle parent theorem proves `(1)` abstractly by sign-corrected equivariant descent
and Oka--Grauert.  It kills ordinary holomorphic and topological obstruction classes.  The
identity-zero componentwise-Pauli theorem proves that `(2)`, combined with the already established
Hardy continuation, gives the factorial improvement needed for modular nuclearity and compact
locality.

Thus the `O(N)` problem is neither existence of some holomorphic frame nor permutation-cocycle
coherence.  It is the uniform condition number `(2)` on a noncompact family of shrinking tubes.
This is Alazzawi--Lechner's published open intertwiner problem, now stripped of its qualitative
cohomology shell.

## SOTA and parent-theory audit

1. Alazzawi--Lechner Definition 5.2 is exactly `(1)`--`(2)` plus the central subspace mapping.
   Their diagonal construction has the bounds; the `O(N)` construction reaches only particle
   number two.
2. Ordinary and equivariant Oka principles give holomorphic triviality and compact-open
   approximation, not a global supremum bound on the unbounded tube.
3. Berndtsson--Rosay obtain bounded factorization in one complex variable.  Several-variable
   quantitative Cartan lemmas require a cocycle uniformly close to the identity.  The `O(N)`
   cocycle is unitary on the central real slice but is not uniformly close to `I` for arbitrary
   real rapidity differences.
4. Coordinatewise strip-to-disc maps identify the tube with `D^n` and its quotient with the
   symmetrized polydisc.  Generic matrix-corona or bounded-bundle results do not provide the
   required equivariance, square completion, and constants uniform in both rank and particle
   number.  Treil--Wick's polydisc theorem is an `H^p`, `p<infinity`, matrix-corona result; the
   `H-infinity` completion theorems found in the audit are one-variable.
5. Finite-group/additive bounded-cohomology averaging proves a bounded linear projection onto
   equivariant sections.  It does not produce an invertible section with a lower singular-value
   bound.

No SOTA theorem found in the audit implies `(2)`, and no counterexample specific to the regular
`O(N)` cocycle was found.  Generic claims about the status of the multidimensional corona problem
are not used as evidence either way.

## Upper exponential scale `[PROVED REDUCTION]`

On

```text
Omega_n=R^n+i(lambda_(pi/2)+(-kappa/(2n),kappa/(2n))^n),    (3)
```

every rapidity difference lies at imaginary distance at most `kappa/n` from the real axis.
Real-axis unitarity and the three-lines theorem therefore give a loss `M^(O(1/n))` for each
adjacent scattering factor.  A longest permutation word has `n(n-1)/2` factors, so the complete
permutation cocycle satisfies

```text
sup_(pi,z) ||A_n^pi(z)|| <= exp(C n),
sup_(pi,z) ||A_n^pi(z)^(-1)|| <= exp(C_tilde n).             (4)
```

Hence the upper scale in `(2)` is dimensionally compatible with the full noncommuting cocycle.
The `O(n^2)` pair count is not the obstruction.

## Canonical rectangular regular frame `[PROVED REDUCTION]`

Let `G=S_n`, `m=|G|=n!`, and define the stacked holomorphic operator

```text
T_n(z):V -> l2(G) tensor V,
(T_n(z)v)_pi=m^(-1/2) A_n^pi(z)^(-1)v.                     (5)
```

If `P_sigma` is left translation of the `G` block index, the cocycle identity gives

```text
T_n(z_sigma)=P_sigma T_n(z) A_n^sigma(z).                  (6)
```

On the central real slice every `A_n^pi` is unitary, so the factorial number of blocks cancels
the normalization exactly:

```text
T_n(theta)^* T_n(theta)=I.                                 (7)
```

Thus `T_n` has central lower singular value one, with no `n!` loss.  On the full tube, `(4)` gives

```text
exp(-C n)||v|| <= ||T_n(z)v|| <=exp(C_tilde n)||v||.        (8)
```

The lower bound follows because every block obeys
`||A_n^pi(z)^(-1)v||>=||A_n^pi(z)||^(-1)||v||`, and the normalized sum of the `n!` squared block
norms cancels the factorial exactly.  Hence equations `(5)`--`(8)` solve the full exponential
condition-number problem after stabilization to the regular block representation.  The remaining
step is **square compression**: find a holomorphic family

```text
L_n(z):l2(G) tensor V -> V                                 (9)
```

with the matching block equivariance and `exp(O(n))` bounds such that `L_n(z)T_n(z)` is invertible
and uniformly well-conditioned on the central slice.  The constant invariant coisometry
`m^(-1/2) sum_pi` turns `L_n T_n` into the normalized Reynolds average.  Hence the determinant and
least-singular-value failure below is precisely failure of the obvious square compression, not
failure of a controlled rectangular frame.

The exact covariance required of the compressor is

```text
L_n(z_sigma) P_sigma=L_n(z).                               (9a)
```

Then `J_n=L_n T_n` satisfies `(1)` automatically.  The square-compression formulation is therefore
equivalent to the remaining construction problem once the bounds and invertibility are included;
it is not merely an analogy with matrix completion.  Conversely, any frame `J_n` satisfying
`(1)` gives such a compressor by the block formula

```text
(L_n(z))_pi=m^(-1/2) J_n(z) A_n^pi(z),                    (9b)
```

and `(4)` preserves the exponential upper scale.

## Controlled continuous square frame `[PROVED REDUCTION]`

The square-compression obstruction is purely holomorphic, not topological or metric.  Define the
Hermitian metric on the sign-corrected exchange bundle by

```text
H_n(z)=m^(-1) sum_(pi in G)
  A_n^pi(z)^(-*) A_n^pi(z)^(-1).                           (9c)
```

The cocycle identity gives

```text
H_n(z_sigma)=A_n^sigma(z)^* H_n(z) A_n^sigma(z),           (9d)
```

which is exactly the descent law for the right action `(z,v).sigma=(z_sigma,A_sigma^(-1)v)`.
By `(4)`, this metric is uniformly comparable with the standard fiber metric:

```text
exp(-2 C n) I <= H_n(z) <= exp(2 C_tilde n) I.             (9e)
```

On the central real slice every cocycle matrix is unitary, hence `H_n=I`.

The quotient is contractible, so its descended Hermitian bundle has a global continuous
orthonormal frame.  Pulling that frame back and taking its inverse gives a continuous exact
intertwiner `J_n^cont` satisfying `(1)` and

```text
sup ||J_n^cont|| <=exp(C_tilde n),
sup ||(J_n^cont)^(-1)|| <=exp(C n),                         (9f)
```

with `J_n^cont` unitary on the central real slice.  Thus all topology, square selection, and
condition-number control are already solved in the continuous category.  The remaining theorem
is precisely a bounded holomorphization of this frame that retains `(9f)` up to `exp(O(n))` loss.
Ordinary equivariant Oka holomorphizes it only in the compact-open topology.

## Reynolds attempt and exact failure

Twisted Reynolds averaging sends a bounded holomorphic seed to an exact equivariant section.  By
`(4)`, a normalized average can retain an `exp(O(n))` upper norm.  At the total collision it is the
identity after normalization, so it is invertible near that point.

The attempt fails globally for a precise reason:

```text
unitary matrices can cancel in their average;
determinant zeros can appear away from the collision locus;
even without zeros, the least singular value can tend to zero
along unbounded real rapidity directions.                             (10)
```

Oka theory can remove the zeros pointwise by changing the section, but supplies no bound on the
condition number of the repaired section.  Additive bounded-cohomology vanishing does not control
this nonlinear `GL` selection problem.

## Radial Oka homotopy and exact uniform failure

The equivariant contraction used in the qualitative theorem suggests scaling every rapidity
difference to zero and integrating the infinitesimal cocycle.  For a two-body factor this
differentiates

```text
t |-> B(t u),
d/dt B(t u)=u B'(t u).                                     (11)
```

This route cannot supply a rapidity-uniform estimate.  If `B` is nonconstant, choose a real
`x_0 != 0` with `B'(x_0) != 0`.  Since `u` ranges over the complete real line,

```text
sup_(u in R) ||u B'(t u)||
  =(1/t) sup_(x in R) ||x B'(x)||
  >=||x_0 B'(x_0)||/t.                                    (12)
```

The resulting `dt/t` majorant is non-integrable at `t=0`.  Finite-group averaging can cancel
parts of the infinitesimal cocycle, so `(12)` is not a no-go for every homotopy construction; it is
an exact kill of the naive uniform contraction estimate.  A successful proof must localize in
rapidity differences or glue at finite scale instead of transporting the complete unbounded real
axis through the total collision.

## Coxeter--Cartan attack `[CONJECTURAL]`

Edge-colour the complete graph on `n` particle labels into `n-1` perfect matchings when `n` is
even, and `n` near-perfect matchings when `n` is odd.  Pair collision hyperplanes within one
matching involve disjoint tensor legs and commute.  This suggests a gluing scheme with only
`O(n)` noncommuting layers:

```text
collision-normalized local frames
  -> simultaneous Cartan split on each commuting matching
  -> Coxeter braid correction between consecutive matchings
  -> uniformly conditioned global frame.                           (13)
```

The desired per-layer estimate is constant, so `O(n)` layers would yield `(2)`.  The load-bearing
missing lemma is a near-identity matrix Cartan split on one matching that:

1. is holomorphic on the complete `1/n` tube;
2. preserves the already repaired collision hyperplanes;
3. has a condition number bounded independently of `n` and the internal rank `N^n`;
4. is compatible with the Brauer contraction terms and the next Coxeter layer.

The pure pair-word theorem shows that `(13)` cannot simply multiply one copy of the published
two-body half-phase along the edge colouring.  Each layer must include a genuine multiparticle
correction or a nonlinear selection from the descended frame bundle.

## Hypertranscendental physics payoff

Proving `(2)` constructs the missing compact-local `O(N)` net in the identity-zero convention.
Regular scalar HT CDD dressing is neutral for `(2)`, so the theorem would immediately admit
nonabelian local QFTs with a physically measurable HT scattering delay and relative modular
carrier.  It would not yet create projective HT mixing, because the undressed `O(N)` projective
ratios are DA.  Its larger value is to supply the locality mechanism that any future intrinsically
mixing projective-HT Yang--Baxter family must clear.

## Anti-theatre and novelty gates

1. **The conjecture called new.**  Rejected.  It is the published `O(N)` intertwiner conjecture in
   a controlled-descent formulation.
2. **The Oka theorem cited as evidence for `(2)`.**  Rejected.  It proves only fixed-`n`
   qualitative existence.
3. **The controlled continuous frame `(9f)` called the solution.**  Rejected.  Hardy
   multiplication requires a bounded holomorphic frame; compact-open Oka approximation is not a
   global supremum estimate.
4. **Generic corona language called a reduction theorem.**  Rejected.  The exact equivariant
   matrix-completion equivalence and constants must be proved.
5. **The radial contraction called quantitative Oka.**  Rejected by the exact `1/t` loss `(12)`.
6. **The edge-colouring schedule called a proof.**  Rejected.  The matching-layer Cartan lemma is
   open and explicitly named.

The possible new contribution is the `O(n)`-layer Coxeter--Cartan construction, not the conjecture
or its physical significance.  It clears neither novelty nor significance until the missing
matching-layer lemma is proved and compared with factorizing `F`-matrix constructions.  Focused
searches for edge-coloured or matching-layer Yang--Baxter twists found parallel sorting networks,
Yang--Baxter bases, and ordinary complete-graph factorization, but no analytic Hardy-frame
construction of the form `(13)`.  This is negative search evidence only.

## Primary literature

- S. Alazzawi and G. Lechner, *Inverse Scattering and Locality in Integrable Quantum Field
  Theories*, <https://arxiv.org/abs/1608.02359>.
- P. Heinzner and F. Kutzschebauch, *An equivariant version of Grauert's Oka principle*,
  <https://eudml.org/doc/144259>.
- B. Berndtsson and J.-P. Rosay, *Quasi-isometric vector bundles and bounded factorization of
  holomorphic matrices*, <https://doi.org/10.5802/aif.1964>.
- J. Leiterer, *A quantitative Oka principle*,
  <https://doi.org/10.1090/conm/550/10869>.
- S. Treil and B. D. Wick, *Analytic projections, corona problem and geometry of holomorphic
  vector bundles*, <https://arxiv.org/abs/math/0702756>.
- S. Treil and B. D. Wick, *The Matrix-Valued `H^p` Corona Problem in the Disk and Polydisk*,
  <https://arxiv.org/abs/math/0409494>.

## Lean boundary

No Lean edit or build is justified.  The missing theorem is a several-variable bounded
holomorphic factorization with uniform operator estimates.  The existing `HTGeometry` bounded
gauge API records the correct conceptual distinction but cannot express the analytic tube,
Cartan splitting, or Hardy multiplier norm.  Formalizing edge colouring or the estimate `(4)`
alone would not formalize the load-bearing theorem.

## Gates

- [x] corpus-first audit
- [x] SOTA parent-theory audit
- [x] fixed-particle ordinary holomorphic obstruction killed
- [x] upper cocycle scale reduced to `exp(O(n))`
- [x] canonical regular-representation frame is globally `exp(O(n))`-conditioned and
  central-isometric
- [x] continuous exact square frame is globally `exp(O(n))`-conditioned and central-unitary
- [x] Reynolds averaging failure isolated to invertibility/conditioning
- [x] naive radial contraction killed by non-integrable `1/t` loss
- [x] pure pair-word lift killed at three particles
- [ ] matching-layer near-identity Cartan lemma
- [ ] `O(n)` Coxeter-layer assembly
- [ ] uniform lower singular-value bound
- [ ] Alazzawi--Lechner intertwiner property for `O(N)`
- [ ] modular nuclearity and compact-local `O(N)` net
