# Prime--theta Young graph, Edrei--Thoma, and RH

- **ID:** `prime-theta-young-thoma-schur-rh`
- **Stage:** 1-in-progress
- **Type:** `[LARGE OUTLANDISH DETOUR] [CONJECTURE] [TWO-ENDED RH CLOSURE]`
- **Lean inputs:** `formal/GaloisForLFunctions/RHTower/PrimeWordEnsembleBoundaryTomography.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeSupportMultivariateLiftMarker.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeWordYoungShapeNoGo.lean`,
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaCumulantMinor.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailTelescope.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailCompletedSource.lean`,
  `formal/GaloisForLFunctions/RHTower/XiCTaylorThetaTailMomentLogConvex.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiHadamardFactorization.lean`
- **Statement:** `[CONJECTURE]` The normalized positive theta-cusp Taylor coefficients define a
  Schur-positive specialization because they are the coherent boundary weights of a completed
  prime-word Young graph.  Edrei--Thoma factorization then forces the square-coordinate centered
  Xi function to have only negative real zeros, hence proves RH.

## Why this detour is different

This route does not build a self-adjoint operator, a positive moment measure, a flow, or a finite
Taylor hyperbolicity test.  It changes the state space from prime supports to multiplicity
partitions and asks for projective coherence under deletion of one prime letter.  The consumer is
the boundary classification of the Young graph, equivalently the character theory of the infinite
symmetric group.

The route is source-pure only if the coherent partition weights are constructed from prime words,
the Gamma/theta completion, and deletion branching.  Reading the Thoma column parameters from Xi
zeros is forbidden.

## The square-coordinate entire function

Put

```text
m_n = thetaCuspRawEvenMoment(n),
a_n = m_n / ((2n)! m_0),
A(u) = sum_(n>=0) a_n u^n.
```

The existing Lean corpus proves `m_n>0`, identifies `m_n/(2n)!` with the even Taylor magnitude of
`XiC`, and proves the odd Taylor coefficients vanish.  Thus `A` is the unique normalized entire
function satisfying

```text
XiC(z) / XiC(0) = A(-z^2).                                (SQ)
```

Equivalently, for either square-root branch at a point,

```text
A(u) = XiC(i sqrt(u)) / XiC(0).
```

The branch-free identity `(SQ)`, not a global square-root choice, is the definition used in a
proof.

The zero geometry closes both ways:

```text
every zero of A is negative real
  <-> every zero z of XiC has -z^2 negative real
  <-> every zero z of XiC is real
  <-> RH.
```

The origin is harmless because `XiC(0) != 0` is already formalized.

## The closed Young--Thoma chain

Geometrically normalize the coefficient sequence by

```text
b_n = a_n / a_1^n.
```

Then `b_0=b_1=1`.  Geometric normalization multiplies every Toeplitz minor by a positive row/column
factor, so it does not change total nonnegativity.  Define a specialization `rho` of the symmetric
functions by

```text
rho(h_n) = b_n.
```

Jacobi--Trudi gives

```text
rho(s_lambda) = det[b_(lambda_i-i+j)].                    (JT)
```

The proposed source construction must close the following chain:

```text
completed finite prime words with full exponent multiplicities
  -> sort exponent multiplicities into Young shapes lambda
  -> nonnegative completed weight M_N(lambda) at every size N
  -> deletion coherence
       M_(N-1)(mu) = sum_(lambda covers mu)
         M_N(lambda) dim(mu)/dim(lambda)                  (YG)
     and sum_(lambda partitions N) M_N(lambda)=1
  -> one Schur-positive specialization rho with
       M_N(lambda)=dim(lambda) rho(s_lambda)
     and rho(h_n)=b_n                                     [OPEN CORE]
  -> every Jacobi--Trudi/Toeplitz minor is nonnegative
  -> (b_n), hence (a_n), is PF-infinity
  -> Edrei--Thoma factorization
       A(u)=exp(gamma u) product_i(1+beta_i u)/(1-alpha_i u),
       alpha_i,beta_i,gamma>=0,
       sum_i(alpha_i+beta_i)<infinity
  -> A entire forces every alpha_i=0
  -> the order-at-most-one bound for XiC and `(SQ)` give order(A)<=1/2,
     so gamma=0
  -> A(u)=product_i(1+beta_i u)
  -> every zero of A is negative real
  -> RH.
```

Conversely, RH and the paired Hadamard product give

```text
A(u)=product_gamma (1+u/gamma^2),
```

with multiplicities and a convergent sum of reciprocal squared ordinates.  Hence RH implies the
same PF-infinity and coherent-Young conclusions.  The final positivity statement is therefore
RH-equivalent; the new scientific content must be the source derivation of `(YG)` and `(JT)`.

## The source producer

A prime word retains more information than its support.  If its prime exponents are
`e_1,...,e_r>0`, sorting them gives a partition

```text
lambda(w)=sort(e_1,...,e_r),     |lambda(w)|=word length.
```

Deleting one letter removes one box.  This is exactly the edge relation in the Young graph after
forgetting which prime carried the affected row.  The required completed weight has the form

```text
M_N(lambda) = sum_(prime words w of shape lambda and length N)
  EulerWeight(w) * ArchWeight_N(w) * Renorm_N,
```

where the Gamma/theta weld and `Renorm_N` must make all weights nonnegative, normalized, and
deletion-coherent.  The one-row value must reproduce `b_N` through `(JT)`; it may not be declared
equal by definition.

The required first map is now formalized with mathlib's finite partition type.  Lean also proves
that the words `[0,0,0,1]` and `[0,0,1,1]` have the same support and complete scalar boundary germ
but distinct multiplicity partitions `[3,1]` and `[2,2]`.  This closes the scalar-germ shortcut and
positively certifies that the full-word packet contains the missing Young-shape datum.
Both one-box branches are now formalized.  Adjoining a fresh prime label inserts a new row of
length one.  If the label already has multiplicity `k`, adjoining it replaces that part by `k+1`.
Consequently the complete labelled-word insertion map descends exactly to Young-graph adjacency.
The remaining difficulty is entirely in the completed positive weight balance across all labelled
preimages of an unlabelled shape; it is no longer hidden in the shape combinatorics.

There is also now an exact interface to the finite Möbius channel.  Lean proves that a prime word
has pure-column shape `[1^N]` if and only if it is squarefree.  Hence the normalized positive
Bernoulli law underlying `MobiusFiniteSchurTransfer.lean` is already a canonical column-positive
Young boundary, but it has no rows of length at least two.  The positive completion problem is to
add a second archimedean alphabet whose binary incidences repeat prime rows while preserving the
existing column law.  The dual-Cauchy/RSK version of that producer is separated in
`prime-arch-dual-cauchy-rsk-fredholm-rh.md`.

The first decisive source equation is the one-box balance.  For every shape `mu` of size `N-1`,
group completed words by which prime letter was deleted and prove `(YG)` before summing over
shapes.  Failure of shape-resolved balance cannot be repaired by the scalar theta moments.

## Direct Euler no-go and its positive statement

The raw bosonic Euler product has the symmetric-function form

```text
product_p (1-x_p u)^(-1),
```

which is a pure Thoma row (`alpha`) sector.  It is meromorphic and therefore cannot equal the
entire function `A`.  This kills the direct raw-Euler specialization.

The positive replacement is canonical: the symmetric-function involution `omega`, equivalently
Young-diagram transposition or tensoring symmetric-group representations by the sign character,
sends

```text
h_n <-> e_n,
product_p (1-x_p u)^(-1) <-> product_p (1+x_p u).
```

Thus completion must implement a row-to-column transmutation, not merely damp the same row sector.
The corpus already contains a graded parity/half-shift sector exchange in the completed KMS model;
the exact open bridge is to prove that its finite prime-word action descends to `omega` on
multiplicity partitions and supplies the missing coherent column weights.

## Numerical falsification gate

High-precision quadrature/Taylor evaluation gives

```text
a_0 = 1
a_1 = 2.3104993115418970788933810430339e-2
a_2 = 2.4833405378914417572385644520882e-4
a_3 = 1.6743526279849498609886294424108e-6
a_4 = 8.0306974210437117112465899077501e-9
a_5 = 2.9401357580298666131092626347178e-11
a_6 = 8.5985946133951541783130432203363e-14
a_7 = 2.0738674758657183863978595176379e-16
a_8 = 4.2238624903224540850942924365865e-19.
```

All minors of order at most four in the tested `7 x 7` upper Toeplitz truncation are nonnegative.
Sample nontrivial Jacobi--Trudi values for the unscaled `a_n` are

```text
lambda=(2,1)       4.0634039751373107e-6
lambda=(3,1)       3.0655208521332216e-8
lambda=(2,2)       2.2983896328973628e-8
lambda=(3,2,1)     3.1957761009550925e-12
lambda=(4,2)       1.3149774808450385e-12
lambda=(4,3,1)     9.883810898904162e-17
lambda=(5,3,2,1)   3.837400452617553e-23.
```

This only fails to falsify the route.  It is not evidence for the all-order sign.

## Attacks and positive successors

1. **Target-equivalence attack.**  PF-infinity of `(a_n)` is RH-equivalent.
   **Positive successor:** prove it from the shape-resolved source branching `(YG)`, never from Xi
   zeros or a total-positivity hypothesis on `A`.
2. **Support-blindness attack.**  Scalar support cardinality forgets exponent multiplicities and
   Young shape.
   **Positive successor:** retain full prime words until after `lambda(w)` and deletion edges are
   formed.
3. **Raw-Euler pole attack.**  A pure row specialization has positive-axis poles.
   **Positive successor:** construct the completion-induced `omega` transposition to the column
   sector.
4. **Inverse-character attack.**  Every Schur-positive specialization already has coherent Young
   measures.
   **Positive successor:** construct `M_N` directly from completed words and prove `(YG)` before
   invoking Edrei--Thoma.
5. **Finite-minor attack.**  Any bounded list of positive minors is compatible with a later
   negative minor.
   **Positive successor:** obtain every minor at once as a nonnegative tableau/nonintersecting-path
   sum under the same source weight.
6. **Plancherel-factor attack.**  A surviving `exp(gamma u)` factor has no zeros and would not hurt
   root location, but it shows the producer has not matched the order of `A`.
   **Positive successor:** use the square-coordinate order bound to prove `gamma=0`; record any
   source Plancherel mass as a defect of exact identification.
7. **Cancellation attack.**  Signed Gamma counterterms can fake scalar coefficients while
   destroying Schur positivity.
   **Positive successor:** realize completion as a positive graded/sign representation whose
   ordinary character is the required transposition, not as coefficientwise subtraction.

## Primary parent results

- A. Edrei, *On the generating functions of totally positive sequences II* (1952), and E. Thoma,
  *Die unzerlegbaren, positiv-definiten Klassenfunktionen der abzählbar unendlichen,
  symmetrischen Gruppe* (1964), in the factorization formulation summarized in
  <https://arxiv.org/abs/1907.06985>;
- Aissen--Schoenberg--Whitney, the finite PF/negative-root theorem, as summarized in the same
  source.

## Kill conditions

Retire this producer if the completed finite word weights are negative in every canonical grading,
if deletion fails shape-resolved coherence at a finite aperture, if the KMS parity exchange does
not descend to Young transposition, or if `rho(h_n)=b_n` is obtained only by reading Xi coefficients
back into an abstract specialization.  Preserve as positive output any coherent subgraph,
restricted family of Schur-positive shapes, or exact signed transposition defect.

## Gates

- [x] branch-free square-coordinate Xi function and positive coefficients isolated
- [x] both directions between negative zeros of `A` and RH closed
- [x] Edrei--Thoma entire/order reduction closed
- [x] coherent Young system and exact source branching equation stated
- [x] full prime word to multiplicity partition map and scalar-germ blindness formalized
- [x] fresh-letter Young one-box branching formalized
- [x] repeated-letter Young row-lengthening branching formalized
- [x] squarefree Möbius sector identified exactly with the pure-column Young boundary
- [x] direct raw-Euler row sector retired positively into the `omega` transposition target
- [x] low-order Toeplitz and Jacobi--Trudi signs numerically pre-certified
- [ ] completed prime-word weights on multiplicity partitions constructed
- [ ] one-box deletion coherence proved at the first nontrivial shapes
- [ ] completion/KMS sector exchange identified with Young transposition
- [ ] all-order Schur positivity proved source-first
- [ ] RH capstone formalized
