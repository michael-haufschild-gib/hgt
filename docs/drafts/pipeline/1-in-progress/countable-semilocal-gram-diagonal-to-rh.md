# Countable semilocal Gram diagonal to RH

- **ID:** `countable-semilocal-gram-diagonal-to-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[RH-SUFFICIENT SOURCE ROUTE]`
- **Source:** `XiTraceHankelCountableCriterion.lean`, `XiRelativeResolventFlux.lean`, and the
  principal-relative Sonin trace stack
- **Statement:** It is enough to realize, separately for each `P in Int[X]`, the source-defined Xi
  trace-Hankel value as a limit of nonnegative compact-support semilocal Gram energies. No universal
  positive operator, all-moment equality, or uniformity in the polynomial degree is required.

## Goal

Let

```text
Q(P) = Re(xiCentralTraceHankel(P mapped to Real)).
```

For every `P : Polynomial Int`, construct source-defined Hilbert--Schmidt kernels `K(P,j)` from
finite prime--archimedean semilocal test data such that

```text
hsNormSq(K(P,j)) -> Q(P).                                      (1)
```

Each term on the left is nonnegative. Therefore `Q(P)>=0` for every integer polynomial, and the
formal theorem

```text
xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis
```

proves RH.

The kernels must be constructed before reading the Xi divisor. Equality `(1)` may use the already
proved source identity between the continued prime--archimedean relative trace and the Xi relative
resolvent, but positivity may not be imported from an RH-equivalent divisor or Weil criterion.

## Gates

- [x] 0 -> 1 in-progress: exact countable endpoint and source-pure sufficient statement isolated
- [ ] 1 -> 2 fully-proven: construct the per-test kernels and prove `(1)` for every integer polynomial
- [ ] 2 -> 3 formalized: source construction, convergence, and composition with the countable Lean
  criterion
- [ ] 3 -> 4 publication-ready: standalone semilocal source proof and Lean certificate

## Why this is strictly weaker than the previous Sonin weld

The previous target asked for one positive trace-class operator `T` satisfying

```text
Tr(T^(n+1)) = xiCentralReciprocalMoment(n)   for every n.       (2)
```

That forces one coherent Stieltjes moment sequence, all mixed polynomial identities, and one
operator valid at every degree. The countable criterion needs none of this. For a polynomial of
degree `d`, `Q(P)` uses only the finite block of moments with indices at most `2d`; the aperture,
finite prime support, renormalization, and Gram carrier may all depend on `P`. Only the scalar limit
`(1)` must be correct.

Thus the new chain is

```text
per-integer-test compact-support source Gram convergence
  -> Q(P)>=0 for every P in Int[X]
  -> countable trace-Hankel criterion
  -> RH.
```

It does not follow formally from the universal-moment route: `(1)` permits incompatible Gram
realizations for different tests and requires no operator whose powers generate them all.

## Source-side attack

For fixed `P` of degree `d`:

1. use the continued source trace
   `continuedPrimeArchSourceRelativeTrace`, which contains only `-zeta'/zeta` and the fixed
   archimedean/boundary factor;
2. extract only the finite local jet needed for the moments `0,...,2d`;
3. approximate that jet by a compact-support prime-power test whose cutoff is allowed to depend on
   `P`;
4. realize the resulting scalar quadratic combination as the squared Hilbert--Schmidt norm of a
   principal-relative log-coordinate test operator;
5. pass to the scalar limit.

The countable reduction removes every uniform-in-degree and simultaneous-moment requirement. A
diagonal enumeration of `Int[X]` can be used after the individual tests are constructed, but no
diagonalization is needed for the logical implication to RH.

## Positive exclusions inherited from the Sonin audit

The residual-only block-diagonal operator cannot supply `(1)`: its powers square the regularized
Euler coefficients and delete mixed prime words. The fixed projection-correction scalarization
also cannot supply `(1)`: its geometric response is uniformly bounded, whereas the required local
von-Mangoldt response contains the unbounded scale `m log p`.

Consequently a successful per-test kernel must positively retain the principal shell and the
logarithmic scale length. The appropriate object is a genuine log-coordinate convolution or
semilocal trace-formula test operator, allowed to vary with `P`.

## Open core

`[OPEN RH CORE]` For one arbitrary integer polynomial `P`, construct a source-defined
principal-relative compact-support kernel and prove `(1)`. The first decisive case is not a
monomial but a two-term polynomial `P=X^r+cX^s`, because it tests whether the construction carries
the mixed anti-diagonal moment rather than only positive diagonal energies.

## Log

- 2026-07-11 -- Countable integer-polynomial RH criterion formalized; universal all-moment Sonin
  weld weakened to independent per-test Gram convergence.

## 2026-07-11 corpus and Lean audit

The unrestricted formulation has now been separated from the source theorem.

`[PROVED IN LEAN]` Define `XiCentralTraceHankelIntNonnegativeLimit` by asking, separately for every
integer polynomial `P`, for an arbitrary sequence of nonnegative real numbers converging to `Q(P)`.
Then

```text
XiCentralTraceHankelIntNonnegativeLimit
  <-> XiCentralTraceHankelIntNonnegative
  <-> RiemannHypothesis.
```

The declarations are
`xiCentralTraceHankelIntNonnegativeLimit_iff_nonnegative` and
`xiCentralTraceHankelIntNonnegativeLimit_iff_riemannHypothesis` in
`XiTraceHankelCountableCriterion.lean`. The companion formalized card is
`../3-formalized/not_new_scientific_knowledge/per-test-nonnegative-limit-rh-equivalence.md`.

The proof is the closedness of the nonnegative half-line, with the constant sequence for the
converse. Consequently, arbitrary polynomial-dependent Gram kernels have exactly the RH sign
content unless their source construction carries additional coherence before `Q(P)` is evaluated.

### What the existing corpus already supplies

The project already contains the following unconditional pieces.

1. `xiCentralTraceHankel_ofFn` identifies the degree-`d` target with the finite Hankel block
   `[xiCentralReciprocalMoment (m+n)]`.
2. `continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace` supplies the exact
   prime--archimedean source identity away from its natural poles.
3. `SoninAllPrimeResidualKernel.lean` constructs a positive Hilbert--Schmidt polynomial probe, and
   `SoninAllPrimeHankelCollapse.lean` proves its Gram entries depend only on `m+n`.
4. That residual Gram has the wrong arithmetic law: block orthogonalization deletes mixed prime
   words and its positive energy squares the residual coefficients. The remaining equality with
   the Xi reciprocal moments is not formal plumbing; it is the missing RH-bearing theorem.
5. `SoninRelativeGramDefect.lean` restores the unsquared Euler coefficient in the
   principal/residual cross. The cross is Hilbert--Schmidt, while the quadratic residual is positive
   trace class.
6. A Hilbert--Schmidt cross has no automatic trace. `SoninSemilocalRelativeTrace.lean` constructs
   one legitimate compact-support scalarization, but `not_soninSemilocalFluxNormalization` proves
   that its geometric response is uniformly bounded and cannot equal the required unbounded
   orbital length `m log p`.
7. `critical-euler-position-commutator-carrier-law.md` already identifies the correct replacement
   on paper: logarithmic position `X_A` and the skew Euler logarithm `Z_A` satisfy
   `[X_A,T_(A,h)]=hT_(A,h)`, so the missing orbital length is produced intrinsically. After
   compression, the degree-one source splits into an internal trace-defect cocycle and the
   polarized position/Euler leakage cross.
8. `SoninLogCoordinateScattering.lean` now proves the exact coordinate compatibility: the original
   Sonin Fourier transform becomes an involutive translation-reversing scattering operator `J_log`
   after logarithmic transport. The ordinary Fourier two-edge commutator is not the Euler carrier.
9. `ccm-sonin-three-grade-relative-carrier-law.md` synthesizes the forced carrier: principal Calkin
   shell, degree-one Hilbert--Schmidt relative cross with the exact logarithmic response, positive
   trace-class residual energy, and the archimedean/Gamma channel. The closed carrier and its
   positive contraction are not yet constructed.
10. The formal tree already contains the principal Calkin faithfulness, relative ideal tower,
   positive residual energy, exact unsquared coefficient exposure, finite Hankel expansion, and RH
   endpoint. It does not yet contain the closed commutator `[M_t,J_log]`, the genuine semilocal
   relative trace on that pair, or the completed lower-floor estimate.

## Corrected finite-degree Gram target

The phrase “the two-term test carries the mixed anti-diagonal” is false without coherence. If
`K(X^r+cX^s,j)` is unrelated to the kernels chosen for the two monomials, it realizes only one
scalar and contains no recoverable mixed inner product.

The minimal source-pure target is therefore:

For every degree `d`, construct source-defined Hilbert spaces `H_(d,j)` and coefficient-linear maps

```text
G_(d,j) : R^(d+1) -> HS(H_(d,j))
```

from finite prime--archimedean log-coordinate test data such that

```text
< G_(d,j)e_m, G_(d,j)e_n >_HS
  -> xiCentralReciprocalMoment(m+n)                       (2)
```

for every `0<=m,n<=d`. Equivalently, the positive finite Gram forms

```text
q_(d,j)(a)=||G_(d,j)a||_HS^2
```

converge to `xiCentralTraceHankelVector(d+1,a)` on coefficient vectors. The carrier and cutoff may
depend on `d`, so this remains strictly weaker than one universal all-degree trace-class moment
operator. The map may not depend on the sign of the target quadratic value or on the Xi divisor.

Polarization makes the mixed obligation explicit:

```text
2 Re <G e_m,G e_n>
  = ||G(e_m+e_n)||^2-||Ge_m||^2-||Ge_n||^2.
```

Thus the first decisive construction is one common source carrier for the three tests
`X^r`, `X^s`, and `X^r+X^s`, not three unrelated kernels.

## Candidate moves after the corpus audit

1. `[RETIRED]` Residual-only all-prime Gram. It is positive and Hankel, but its moment sequence is
   not the Xi sequence and its coefficient law is wrong.
2. `[RETIRED]` Fixed projection-correction scalarization. Its response cannot carry `m log p`.
3. `[RETIRED]` Arbitrary per-polynomial nonlinear factorization. The new Lean equivalence proves it
   is the target sign condition with no independent source content.
4. `[BRIDGE, INSUFFICIENT]` Bare semilocal prolate/self-adjoint extension. Existing pipeline work
   shows extension existence but rank-at-most-two boundary ambiguity; a chosen extension is not
   canonical source data.
5. `[CONJECTURE]` Finite-degree coherent log-position/Sonin leakage Gram. Transport the existing
   `X_A,Z_A` commutator carrier through the exact Sonin principal--relative extension, include the
   Gamma conductor, and construct a source-canonical contraction whose defect tends to zero on the
   finite rational-resolvent block generated by degrees `0,...,d`.

## Attack on the surviving candidate

- Compactness of a Weil--Sonin defect is not enough; one also needs a bounded family of test vectors
  converging weakly to zero, or a trace-norm error tending to zero.
- A selected self-adjoint boundary condition can encode the scalar sign. Source symmetry must select
  it, or the final Gram limit must be invariant under the rank-two extension ambiguity.
- Positive Euler coefficients are not enough. Existing point-source Hankel cards show the local
  FE-even kernels are indefinite; the proof must use the exact prime--Gamma coupling.
- The internal compressed commutator cannot be discarded by formal cyclicity. For the boundary
  relative trace it may contribute a nonzero trace-defect cocycle.
- A scalar convergence proof for each `P` is insufficient unless it comes by polarization from the
  common degree-`d` map `G_(d,j)`.

## Revised open core

`[OPEN RH CORE]` Construct, on the existing three-grade Sonin carrier, the closed transport of the
finite-aperture logarithmic-position/Euler commutator and the archimedean conductor. Prove that its
compressed degree-one pair (trace-defect cocycle plus polarized leakage cross) and the positive
grade-two residual assemble into coefficient-linear maps `G_(d,j)` satisfying `(2)` for every fixed
degree `d`.

A sufficient quantitative endpoint is an entirely source-side estimate

```text
|xiCentralTraceHankelVector(d+1,a)-||G_(d,j)a||_HS^2|
  <= epsilon_(d,j) ||a||^2,
epsilon_(d,j) -> 0,                                       (3)
```

first on integer vectors and then on all real vectors. Equation `(3)` must be proved through the
continued prime--archimedean trace and the semilocal carrier, not by evaluating the Xi divisor.

The next mathematical object is therefore not another Gram wrapper. It is the common closed
log-position/Sonin graph and its source-selected relative trace.

## Prime-log Herglotz source refinement

The prime-log pole carrier constructed in `PrimeLogHerglotz.lean` supplies a canonical static
source coordinate, but the dyadic gauge used by the facet-sewn HT construction is not the
arithmetic zeta weight. The later theorem
`not_summable_primeLogHerglotzTransportMassOrder_of_pos` is a distinct statement: it proves that
every finite logarithmic cancellation order fails after positive transport.

`[PROVED ON PAPER]` The exact Euler-logarithm measure on prime-power log support is

```text
mu_E=sum_(p prime,k>=1) 1/(k p^k) delta_(k log p).
```

Its Herglotz-normalized Cauchy transform

```text
H_E(z)=sum_(p,k) 1/(k p^k)
  (1/(k log p-z)-(k log p)/(1+(k log p)^2))
```

converges locally uniformly off its locally finite pole set and has positive imaginary part in the
upper half-plane. Multiplication by log position changes the residue weight by

```text
(k log p)/(k p^k)=log p/p^k,
```

and its Laplace transform is exactly `-zeta'(1+s)/zeta(1+s)` on `Re s>0`. The complete proof is in
`../2-fully-proven/not_new_scientific_knowledge/euler-log-prime-power-herglotz-half-weight-law.md`.

`[PROVED IN LEAN]` The positive carrier cannot be transported toward the critical line by an
exponential weight. For every `b>0`,

```text
sum_p p^(2b-1)/(1+(log p)^2)=infinity.
```

This is
`GaloisForLFunctions.HTGeometry.not_summable_primeLogHerglotzTransportMass_of_pos`, with formalized
card
`../3-formalized/not_new_scientific_knowledge/prime-log-herglotz-positive-transport-wall.md`.
The stronger declaration
`not_summable_primeLogHerglotzTransportMassOrder_of_pos` proves the same divergence after every
finite log-position cancellation order. `PrimeLogCauchySeamRank.lean` then proves exact finite
independence: every nonzero packet of distinct upper-half-plane Cauchy sections remains outside the
transported prime `ell^2` space. The critical half-weight is therefore not a domain issue that
finite polynomial degree or finite-rank additive renormalization removes.

`[PROVED IN LEAN, POSITIVE COUNTERPART]` The canonical Gamma diagonal repairs the complete finite
Cauchy core, not only one normalized section:

```text
sum_p phi(2log p)
  |sum_j c_j/(z_j-log p)|^2<infinity.                    (3a)
```

For distinct upper-half-plane nodes, the paired capstone says that `(3a)` always holds while the
undamped critical packet is summable exactly when `c=0`. This is formalized in
`GammaDampedPrimeLogCauchyDomain.lean`. Hence a successful carrier is forced to supply a genuine
inverse-prime archimedean order before completion; the Gamma diagonal supplies exactly that domain
resource.

### Consequence

The prime-log Herglotz measure solves channel resolution and produces the orbital length
intrinsically, but it does not transport positivity to the Xi reciprocal moments. The next live
object must sew this marked prime measure to the Gamma conductor before the half-weight is applied.
The sewing must retain the exact residues and functional-equation polarization; the facet-sewn
universality theorem proves that an unpointed Herglotz/HT relation complex has no source-selection
content.

`[OPEN RH CORE, SHARPENED]` Derive the Gamma-damped finite-Cauchy domain from the actual
Hardy--Titchmarsh/Gauss-paired/Sonin source operator, then prove that its source-selected relative
covariance equals the completed prime--archimedean trace and satisfies the Gram error estimate `(3)`.
The analytic domain crossing is complete; source selection, covariance subtraction, and
divisor-sensitive positivity remain open. Any construction that first transports the positive
prime Herglotz space and adds Gamma afterward is formally excluded.

## Hardy--Titchmarsh/Sonin sewing audit after the prime-log pointer

The project already contains an exact prime--Gamma sewing, but it is not yet the positive compact
carrier required by `(3)`.

`[PROVED IN LEAN]` `HardyTitchmarshSemilocalSquare.lean` constructs, for every prime scale `p>1`,
the weighted semilocal line and the place-adjoining map `iota'_p`.  Its exact Gram law is

```text
(iota'_p)^* iota'_p = M_(|1-p^(-1/2-is)|^2),
```

and the Hardy--Titchmarsh square commutes exactly with the physical local factor.  Thus the Gamma
and prime pieces are already on one source-defined carrier; no arbitrary facet sewing is needed.

The same file and `HardyTitchmarshEulerConcrete.lean` prove the decisive ideal obstruction:

```text
M_(w_p) M_(w_q) is noncompact,
[Pi_(a,infinity),M_(w_p)] is noncompact,
```

and the one-prime cross-boundary Euler corner is noncompact.  Therefore the raw semilocal Gram and
its finite-prime products cannot themselves be the Hilbert--Schmidt feature maps `G_(d,j)`.  The
principal-shell relative subtraction is not optional.

`[PROVED IN LEAN]` `SoninPrincipalShellResidual.lean` supplies that canonical subtraction at one
scale, and `SoninRelativeGramDefect.lean` proves that the resulting degree-one cross is
Hilbert--Schmidt while retaining the unsquared Euler coefficient.  However, the subtraction gives
an indefinite relative Gram defect, not a positive square.  The missing theorem is exactly a
completed prime--Gamma contraction dominating this relative cross while preserving its
log-position response.

### Gamma-decay attack

The archimedean cyclic characteristic

```text
phi(t)=(cosh t)^(-1/2)
```

has asymptotic decay of critical size `exp(-|t|/2)`, so a tempting construction is the damped
sum-Hankel kernel `K(u,v)=phi(u+v)` on the prime-log semigroup.

`[FALSIFIED IN LEAN]` For every `t!=0`,

```text
phi(2t)<phi(t)^2,
phi(0)phi(2t)-phi(t)^2<0.
```

Hence the `2 x 2` Gram matrix on `{0,t}` is indefinite.  The declarations are
`semilocalArchimedeanCharacteristic_two_mul_lt_sq` and
`semilocalArchimedeanCharacteristic_hankelDet_neg`; the formalized card is
`../3-formalized/not_new_scientific_knowledge/gamma-characteristic-sum-hankel-no-go.md`.
Difference-frequency use of `phi` is positive definite, but its diagonal is `1` and gives no
half-weight damping.  Thus the Gamma factor has the right decay only inside a nontrivial relative
covariance; it cannot be attached as a scalar positive Hankel weight.

### Current-literature check

The semilocal prolate literature still presents positivity comparison as the program rather than a
proved theorem.  The 2026 screw-function formulation likewise leaves the limiting nonlocal
self-adjoint realization conjectural.  The 2026 finite Guinand--Weil dictionary sharpens the warning:
each truncated Galerkin quadratic value is already an exact zero sum, while only the omitted
archimedean tail is an automatically positive Cauchy--Stieltjes increment.  Finite truncation does
not manufacture the missing full positivity.

### Surviving construction

`[CONJECTURE, NARROWED]` Use the channel-resolved finite-place multipliers from the semilocal
Hardy--Titchmarsh square, subtract their common noncompact principal shell before squaring, and sew
the resulting Hilbert--Schmidt degree-one channels to the archimedean conductor through a
source-defined block contraction.  For a block Gram

```text
[ A  C  ]
[ C* B  ],
```

positivity requires a factorization `C=A^(1/2) K B^(1/2)` with `||K||<=1`.  Here `C` is forced by
the log-position/Euler leakage cross, `A` by the channel-resolved prime residuals, and `B` by the
Gamma conductor.  The Hardy--Titchmarsh unitary identifies the common carrier but does not prove
this contraction; its noncompact-corner theorem shows why principal subtraction must occur first.

`[OPEN RH CORE, CURRENT]` Construct this explicit source contraction on the principal-relative
Sonin graph and prove its finite-degree compression error tends to zero as in `(3)`.  The following
three shortcuts are now formally excluded: positive prime transport followed by Gamma addition,
scalar Gamma Hankel damping, and the raw Hardy--Titchmarsh semilocal Gram without principal-shell
subtraction.
## A positive sewing that really crosses the half-weight

The negative sum-Hankel determinant does not exclude every positive Gamma sewing.  There is one
canonical positive covariance that crosses the wall.

Let `phi(t)=(cosh t)^(-1/2)` and define

```text
d(t)=sqrt(phi(2t)),
K_Gamma(t,u)=d(t)d(u)phi(t-u).                              (4)
```

`[PROVED ON PAPER]` Since `phi(t-u)` is the characteristic kernel of the normalized Gamma cyclic
measure, `(4)` is positive semidefinite by diagonal congruence.  Its diagonal is

```text
K_Gamma(t,t)=phi(2t) asymp exp(-t).
```

At `t=log p`, this changes the critical transported Cauchy mass from
`1/(1+(log p)^2)` to at most

```text
sqrt(2)/(p(1+(log p)^2)),
```

which is summable.  Thus sewing Gamma before transport really does repair the analytic half-weight
domain.  The proof and exact bounds are in
`../2-fully-proven/not_new_scientific_knowledge/gamma-damped-stationary-prime-log-covariance-law.md`.

### Why this is not yet the Xi Gram

Every entry `K_Gamma(t,u)` is strictly positive.  A coherent square of two positive prime-power
channels therefore contains a strictly positive cross term.  The Euler logarithm and its
log-position derivative are additive over prime powers and contain no such pair terms.  Hence this
positive covariance cannot equal the continued source trace directly.

This leaves one precise, nonempty construction problem rather than a generic half-weight wall.
The correct positive organization is now known: retain the prime channels as the columns of one
Gamma-damped synthesis operator `T`. The formal finite-Cauchy summability theorem makes `T`
Hilbert--Schmidt; `T^*T` retains every off-diagonal covariance, while `Tr(T^*T)` is automatically the
additive sum of its diagonal column energies. This is proved on paper in
`../2-fully-proven/not_new_scientific_knowledge/ccm-gamma-damped-cauchy-frame-trace-law.md`.
The remaining construction problem is to realize this synthesis inside the actual semilocal
operator. Its Euler-region prime-power diagonal is exact: the uniquely forced correction

```text
r_(p,k)=1/(k p^k phi(2klog p))
       =sqrt(1+p^(-4k))/(sqrt(2)k)
```

is a positive contraction, and the corrected Gram trace is precisely the Euler-log Cauchy
polarization. But the centered von-Mangoldt source forces instead

```text
q_(p,k)=((log p)/sqrt(2))p^(k/2)sqrt(1+p^(-4k)),
```

which is cofinally unbounded. This is proved in
`../2-fully-proven/not_new_scientific_knowledge/ccm-euler-gamma-radon-nikodym-frame-law.md`.
The remaining source problem is therefore to realize that recession as a closable relative
operator and implement the exponential Loewner atom
`(exp(-i conjugate(w)t)-exp(-i zt))/(z-conjugate(w))`, which is not the Euler Cauchy product. The
archimedean/boundary divided-difference channel must live on the same domain before the complete
frame can be identified with the actual semilocal operator. The canonical closed two-channel graph
and the exact bilateral factorization of this atom are already proved in
`../2-fully-proven/not_new_scientific_knowledge/ccm-logderivative-closed-two-channel-graph-law.md`;
the open input is the distinguished Sonin compression and its quantitative relative trace bound.

`[LEADING CONJECTURE]` The conjugated local-channel family in the Gauss-paired quantized
differential identity is the resolved synthesis map, and the Sonin principal-shell relative defect
is its compact/Hilbert--Schmidt compression. Prove that their common Hardy--Titchmarsh realization
has the channel Gram described above, sends its diagonal trace to the completed degree-one relative
trace, and retains the grade-two covariance as its positive off-diagonal operator. The bounded
correction is exact only in the Euler region; no existing project theorem realizes the unbounded
critical correction and archimedean/boundary channel in the same Sonin operator.

`[SOURCE-SELECTION CAVEAT]` The damping `d(t)=sqrt(phi(2t))` is natural but is not yet selected by
the exact Hardy--Titchmarsh forward map.  That map selects the local symbol and its noncompact Euler
Gram.  The next proof must derive `(4)` (or a replacement with the same diagonal decay) from the
Gauss-paired ratio/Sonin/conductor operator itself.  Treating `d` as an admissible external gauge
would merely move the missing theorem into the choice of covariance.
## Exact half-unit seam and finite-degree audit

The completed Hardy/CCM pipeline already identifies the global version of the same obstruction.
For `omega>0`, the completed causal quotient

```text
Phi_omega(z)=xi(1+z)/xi(1+2omega+z)
```

is unconditionally Schur, and exponential conjugation remains contractive through widths
`0<=a<=omega`.  The shifted-Xi/RH boundary requires width

```text
a_omega=1/2+omega.
```

Thus the unproved width is exactly `1/2` at every prelimit, not only as `omega->0`.  The card
`ccm-completed-quotient-weighted-schur-seam-law.md` proves that contractivity at the target width is
equivalent to vanishing of the denominator model space carrying the off-line zero Cauchy jets.
Consequently a generic completed contraction is not a lemma waiting to be connected: at the target
width it is already an RH-equivalent statement.

The countable finite-degree criterion does not shorten this seam.  For any prescribed degree,
sufficiently high off-line reciprocal pairs perturb the finite Hankel block by an arbitrarily small
amount while preserving its positivity.  This is the theorem in
`finite-degree-reciprocal-tests-height-limited.md`.  Therefore no fixed-degree estimate can force a
smaller exponential domain.  The route must construct one source operator/form whose all-degree
compressions exhaust the target, or prove estimates with genuine degree-to-height control.

`[ROUTE DISCIPLINE]` The Gamma-damped covariance `(4)` is useful only if its channel synthesis is
derived inside that completed source operator and its diagonal trace is identified arithmetically.
The off-diagonal covariance should remain in the Gram operator rather than be canceled. Proving
positivity only after identifying the whole Gram with the target form would merely restate the
target-width contraction/RH criterion.

`[LEAN PROGRESS]` The damped covariance itself, strict positivity of its entries, its diagonal law,
and the exact bound

```text
phi(2t)<=sqrt(2)exp(-t)
```

are now formalized in `SoninSemilocalTwoPlaceAssociation.lean`.  The finite-matrix PSD theorem still
uses the Gamma Fourier integral on paper; it does not yet supply the missing additive source
identity.
## Gauss-paired covariance depth attack

The leading Gauss-paired interpretation does not by itself supply the required Hilbert--Schmidt
feature map.  Connes--Consani prove that for `m` finite primes the completed local-ratio product is
quasi-inner, but quasi-inner means only that its Hardy off-diagonal is compact.  Their Gauss
factorization gives paired channel defects of infinitesimal order `1/(2m)`; the existing
`gauss-paired-quasi-inner-channel-schatten-depth-law.md` records the sharper project audit that the
channel direct sum has critical weak-Schatten exponent `2m` (the exact endpoint residue remains in
`needs-audit`).  Thus no fixed Schatten class contains the unsmoothed cofinal channel system.

`[ATTACK RESULT]` The Gauss-paired quantized differential performs the correct finite trace
additivity, but its raw channel carrier cannot be `G_(d,j)`: as the prime cutoff grows it moves
farther from `S_2`, not closer.  A successful use must prove one of two genuinely new analytic
statements:

1. a source-defined cancellation in the full multiplicative product defect that improves the
   channel direct sum to a uniform Hilbert--Schmidt/trace-class relative object; or
2. a test/resolvent smoothing, uniform in the growing prime set and compatible with the Gamma
   half-weight, that reaches the same ideal before taking the finite-degree Gram.

This leaves the Gamma-damped covariance `(4)` as a model for the required decay, not as an
identified suboperator of the present Gauss-paired construction.  The exact open core is now a
uniform covariance-cancellation/Schatten theorem, followed by the finite-degree Xi moment identity.

## Diagonal residue-bundle reduction

`[PROVED BRIDGE]` The infinitesimal safe completed kernel now has a canonical diagonal Fock
relation

```text
T_0 k_x=k_x tensor (t |-> exp(-xt)),
```

whose contractivity is equivalent to RH.  This target is source-selected: under the reflected
Paley--Wiener transform, `exp(-xt)` is the anti-causal residue coordinate of the upper-half-plane
Cauchy pole `(u-i x)^(-1)` in the canonical closed completed-logarithmic-source graph.

The universal Laplace coordinate also has the exact polar--prime incidence

```text
1/(x+y)
 =-zeta'(1+x+y)/zeta(1+x+y)-1/(x+y+1)
  +integral_0^infinity exp(-(x+y+1/2)h)dR(h).
```

Thus the required contraction is precisely a four-channel passivity law coupling the safe
completed input, the shifted polar Laplace channel, the resolved von-Mangoldt prime-power channel,
and the signed critical Mellin-defect channel.  The complete proof is in
`../2-fully-proven/not_new_scientific_knowledge/ccm-diagonal-fock-polar-prime-mellin-incidence-law.md`.

The formal line-211 transport theorem fixes the topology of any approximation.  Sampling the same
Cauchy residue coordinates at `log p` remains outside the prime Hilbert domain after every fixed
finite rational cancellation order, while the formal Gamma-damped carrier transition places every
finite Cauchy packet in the domain.  Therefore the genuine Gauss/Sonin construction must sew Gamma
before completion and converge in a relative graph topology; ordinary prime `ell^2` convergence is
not the relevant limit.

`[OPEN RH CORE, RESIDUE FORM]` Prove that the distinguished Sonin compression of the closed Xi
source graph is contractive on the complete diagonal residue bundle and that its cofinal defect
index is preserved.  This is the common operator statement behind the finite-degree Gram target,
the four-unit boundary relative-trace bound, and the square restricted-Weil Evans line.

`[PROVED SOURCE DICTIONARY]` For each off-line quartet, the Euler-ray defect and the boundary trace
are not merely equivalent counters.  Writing the causal and anti-causal resolvents as
`f_lambda(x)=(x-lambda)^(-1)` and
`g_lambda(x)=(x+conjugate(lambda))^(-1)`, their Hermitian packet is

```text
|u_lambda><u_lambda|-|v_lambda><v_lambda|,
u_lambda=(f_lambda+g_lambda)/sqrt(2),
v_lambda=(f_lambda-g_lambda)/sqrt(2).
```

The negative coordinate has Laplace density `exp(i gamma t)sinh(a t)`; the decaying half
`exp(-a t)exp(i gamma t)` is exactly the residue mode whose norm gives the boundary trace slope.
Thus cofinal index preservation and the four-unit metric budget are two required readings of the
same bilateral source channel.  The proof is in
`../2-fully-proven/not_new_scientific_knowledge/ccm-quartet-resolvent-bilateral-polarization-law.md`.

## Sharp Sonin position-domain reduction

`[PROVED IN LEAN; COORDINATE CORRECTION]` The ordinary-position commutator with the sharp Fourier
cutoff is a two-edge Sobolev trace, but it is not the Euler orbital-length carrier. If
`Q_0=I-P_a-B_a`, then on a Schwartz core

```text
-i <[X,Q_0]f,g>
 =1/(2pi)
   [hat(f)(a)conjugate(hat(g)(a))
    -hat(f)(-a)conjugate(hat(g)(-a))].
```

Here `X=x`. Lean proves that `[x,U_p]=(1-p)xU_p` is not a scalar multiple of the dilation, whereas
the required identity is `[log|x|,U_p]=-log(p)U_p`.

After the exact even logarithmic unitary sends dilations to translations, the original Sonin
Fourier transform becomes an involutive translation-reversing scattering operator `J_log`, not the
ordinary Fourier transform used in the edge formula. Therefore the current source-side open theorem
is

The current source-side open theorem is therefore concrete:

```text
closed Mellin-scattering commutator [M_t,J_log]
  + Euler translation leakage
  + Gamma/Burnol conductor
  -> a source-defined relative trace with a uniform finite lower floor.
```

The corrected Lean theorem is in
`../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`.
The ordinary edge formula remains valid but is retired as an Euler source carrier.

## Full-divisor Lean reduction

`[PROVED IN LEAN]` The non-q62 formal corpus already contains more of the global target/source
incidence than the finite-section formulation exposes.  `XiWeilResolventSource.lean` proves that
on every separated finite Cauchy packet the multiplicity-exact Xi--Weil polarization is exactly the
continued prime-plus-archimedean relative-resolvent source form.  `XiWeilHilbertCore.lean` supplies
the algebraic Cauchy span and its closed Hilbert completion.

The missing converse positivity statement is now formalized in
`XiWeilPositivityCriterion.lean`.  For every nonreal centered divisor point `alpha`, the finite
sign test which is `1` at `alpha`, `-1` at `conjugate(alpha)`, and zero elsewhere has exact Weil
square

```text
-card { divisor copies over alpha or conjugate(alpha) } < 0.
```

Consequently Lean proves

```text
RH
  iff
xiWeilPolarization is nonnegative on every square-summable divisor test.
```

The finite diagonal-Fock layer is also formalized: the Gram matrix of diagonal tensor features is
the Hadamard product of the factor Gram matrices; defect nonnegativity, diagonal-lift passivity,
and the four-channel source inequality are exactly equivalent, both sectionwise and cofinally.

## Rank-two Cauchy exhaustion

`[PROVED IN LEAN]` Full Cauchy-core density is not required. For every centered point `alpha`,
analytic isolation of the Xi divisor gives a positive gap from the complete `alpha` multiplicity
fiber. There are regular points `z_n -> alpha` for which

```text
(alpha-z_n) * (lambda_q-z_n)^(-1)
  -> 1_{lambda_q=alpha}
```

in the multiplicity-exact divisor `ell^2` norm. The proof uses the uniform majorant

```text
|(alpha-z_n)/(lambda_q-z_n)|^2
  <= 4 |lambda_q-alpha|^(-2)
```

and the formal Cauchy square-summability theorem.

Subtracting the corresponding conjugate-fiber limit shows that regular two-pole Cauchy packets
exhaust every off-line negative sign direction. Boundedness of the line-conjugation Hilbert form
then gives the exact Lean criterion

```text
RH iff every regular two-pole Cauchy packet has nonnegative Xi--Weil square.
```

The formal proof is in `XiWeilCauchyPoleExhaustion.lean`; its pipeline card is
`../3-formalized/not_new_scientific_knowledge/ccm-normalized-cauchy-pole-fiber-exhaustion.md`.

## Exact continued source criterion

`[PROVED IN LEAN]` The rank-two target criterion has now been pulled completely to the explicit
prime-plus-archimedean source side. For the continued relative trace `T`, define

```text
K(z,w) = (T(conjugate(w))-T(z))/(z-conjugate(w))
```

and let `E(z,w;a,b)` be its four-term Hermitian two-pole energy. On the natural continued domain,
with both poles separated from both reflected poles, Lean proves

```text
E(z,w;a,b)
  = xiWeilPolarization(twoCauchy(z,w;a,b), twoCauchy(z,w;a,b)).
```

The normalized pole approaches can be chosen with arbitrarily small unequal positive speeds. They
stay inside the open-strip source domain and avoid every reflected collision. Hence Lean proves the
source-side equivalence

```text
RH iff CCMContinuedTwoPoleSourcePassivity.
```

The proof is in `CCMTwoPoleSourceCriterion.lean`; its pipeline card is
`../3-formalized/not_new_scientific_knowledge/ccm-continued-two-pole-source-criterion.md`.

## Minimal rank-one source criterion

`[PROVED IN LEAN]` The general non-q62 formal audit reduces the RH-bearing sign further. The
diagonal of one regular Cauchy kernel is exactly

```text
(T(conjugate(z))-T(z))/(z-conjugate(z)) = -Im(T(z))/Im(z).
```

Under `s=1/2+zI`, its nonnegativity is precisely

```text
0 <= Re(infinitePrimeFlux(s) - logDeriv(archFactor)(s))
```

on the pole-free left half-strip. Lean proves

```text
RH iff CompletedPrimeGammaLeftHalfAccretive
   iff CompletedPrimeGammaGaussianRatLeftHalfAccretive.
```

The corpus proves a weaker exact criterion as well:

```text
RH iff CompletedPrimeGammaGaussianRatLeftHalfBoundedBelow.
```

This asks only for one finite uniform lower floor on the completed flux over the regular
Gaussian-rational points; the floor may be negative and need not be explicit. Failure of RH forces
the flux below every floor near a reflected off-line pole. The formal proofs are in
`CCMCompletedPrimeGammaAccretivityCriterion.lean` and `PrimeArchSourceUpperBoundGate.lean`; their
pipeline cards are
`../3-formalized/not_new_scientific_knowledge/ccm-completed-prime-gamma-accretivity-criterion.md`
and `../3-formalized/not_new_scientific_knowledge/prime-arch-source-upper-bound-rh-gate.md`.

`[OPEN RH CORE, DISTINGUISHED SONIN FORM]` The non-q62 corpus already constructs the finite-support
semilocal Sonin relative trace, proves its Hilbert--Schmidt pairing and reality, and isolates
`SoninSemilocalFluxNormalization` as the exact one-mode geometric source-identity gate. The
surviving construction theorem must positively derive a uniform finite lower floor for the
completed prime--Gamma flux from the distinguished Sonin principal/residual graph. Accretivity or
rank-two source passivity are stronger sufficient producers, but the smallest currently formalized
resource is countable rank-one boundedness. No divisor-density, target/source, pole-admissibility,
determinant-limit, or finite-section transfer theorem remains outside Lean.
