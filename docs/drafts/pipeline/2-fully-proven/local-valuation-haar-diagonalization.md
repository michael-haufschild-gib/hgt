# The matched finite-prime operator has the torsion-adjunction spectrum

- **ID:** local-valuation-haar-diagonalization
- **Stage:** 2-fully-proven
- **Type:** THEOREM
- **Source:** AIT transverse towers and torsion adjunction; RAPT finite-sieve finite part; Hardy Blaschke model space
- **Count:** uncounted until exact Lean realization and final audits

## Precise contribution

For a finite set Q of primes let S_Q be its supported positive integers,
H_Q=ell-two(S_Q;Complex), and

`gamma_Q=gamma+sum_(p in Q) log(p)/(p-1)`.

The actual Weil prime kernel restricted to S_Q has a bounded self-adjoint
extension P_Q. Define

`A_Q=diag(log n)-P_Q+gamma_Q I`

on the maximal domain `sum_n |log(n) x(n)|^2 < infinity`.

There is an explicit complete orthonormal basis `(Phi_m)_(m in S_Q)` such that

`A_Q Phi_m = E(m) Phi_m`,
`E(m)=gamma+log(m)+tameDifferent(m)`
`    =gamma+2log(m)-selfIntersection(m)`.

In this basis the actual maximal domain is exactly the set of x for which
`(E(m) <Phi_m,x>)_m` is in ell-two, and A_Q acts by multiplication by E(m).
All eigenvalues are simple. The shifted operator `A_Q+(1-gamma)I` has a bounded
compact inverse, with eigenvalues `1/(1+log(m)+tameDifferent(m))` in this basis.

This operator is an actual horizon defect. For a finitely supported real class
vector b, let `x_b=sum_d b_d w_d/sqrt(delta_d)` using the class poles and densities
from the formalized finite-prime horizon theorem. Then

`(B_M(x_b,x_b)-log(M)||x_b||_M^2)/log(M)`
` -> -Re <b,A_Q b>`.

The finite square identity, basis construction, and generic operator helpers
are supporting work within this single proposed contribution. First-gap bounds,
Hodge index on one-prime class spans, and top bounds are already corpus results.

## Dependency-closed paper proof

### 1. The actual one-prime kernel

Work first on H=ell-two(N;Complex). Let S be the unilateral shift, D the maximal
number operator `(Dx)_n=n*x_n`, and 0<q<1. The shift has norm one, so the
Neumann series

`R=sum_(k>=0) q^k S^k=(I-q S)^(-1)`

converges in operator norm. Define `K=R+R*-I`. It is bounded and self-adjoint.
Its matrix is exactly `K(n,m)=q^|n-m|`: R is the lower triangular geometric
matrix, its adjoint is the upper triangular one, and subtracting I removes
the duplicated diagonal. Thus `H_q=D-K+I` is the actual number-minus-KMS
operator on the domain of D, not an operator defined by desired eigenvalues.

D is closed and self-adjoint on its maximal square-summability domain, as in
the existing maximal-real-diagonal construction. Subtracting bounded K-I
preserves closedness: the graph is the inverse image of D's closed graph under
`(x,y) -> (x,y+(K-I)x)`. It preserves symmetry as well.

### 2. Complete modes from the Blaschke range

Put `U=(S-q I)R`, multiplication by `b_q(z)=(z-q)/(1-q z)` in coefficient Hardy
space. Existing Hardy results prove U is an isometry and its range is the
orthogonal complement of the geometric kernel `g(n)=q^n`. Its squared norm is
`1/(1-q^2)`. Therefore

`phi_0(n)=sqrt(1-q^2)*q^n`,
`phi_k=U e_(k-1)` for k>=1

form a complete orthonormal basis. Orthogonality follows from the isometry and
its one-dimensional complement. A vector orthogonal to all modes is orthogonal
to g, hence Uy for some y, and orthogonality to all Ue_j forces every coefficient
of y to vanish. Explicitly, for j=k-1,

`phi_k(n)=0` if n<j,
`phi_k(j)=-q`,
`phi_k(n)=(1-q^2)*q^(n-j-1)` if n>j.

These geometric sequences lie in the domain of D. Besides polynomial-geometric
summability, there is a direct bounded-image proof: `Dg=Rg-g`, and the pointwise
identity below gives `D phi_k=K phi_k+(k-1)phi_k`. Each right-hand side is already
an element of the actual Hardy space.

### 3. Eigenvector equations and the entire domain

For n>=0, splitting the geometric row at n gives

`(K g)(n)=(n+1+q^2/(1-q^2))*g(n)`.

For the shifted Blaschke mode with j=k-1, its two geometric tails cancel when
n<=j. When n>j, the terms between j and n leave exactly n-j equal summands.
Thus

`(K phi_k)(n)=0` for n<=j,
`(K phi_k)(n)=(n-j)*phi_k(n)` for n>j.

It follows pointwise that

`H_q phi_0=-q^2/(1-q^2)*phi_0`,
`H_q phi_k=k*phi_k` for k>=1.

An equivalent operator calculation is available for the same equations.
The identity `R*(S-q I)=S`, obtained from `S*S=I`, gives
`K U=(1-q^2) S R^2`. On the domain of D,
`[D,U]=(1-q^2) S R^2`, hence `H_q U=U(D+I)`.
Domain preservation by R follows from the finite Neumann sums: their D-images
are the sums of `q^j S^j Dx + j q^j S^j x`, which converge because
`sum_j j q^j` is finite. Closedness of D passes the identity to R; the same
then holds for U. No domain-preservation assumption is introduced.

The eigenvectors determine the full domain, not merely a core action. If x is
in the domain of H_q, symmetry gives

`<phi_k,H_q x>=lambda_k <phi_k,x>`.

The right-hand coordinate sequence is square-summable by Parseval. Conversely,
if these weighted coordinates are square-summable, the finite eigenvector
expansions converge both to x and, after applying H_q, to the vector with those
weighted coordinates. Closedness of H_q puts x in its actual domain and gives
that image. The coordinate unitary therefore identifies H_q with the existing
maximal real diagonal operator; self-adjointness follows on the full domain.

For finitely supported real x this also gives the exact finite square law.
With `T_j=sum_(j<=n<N)q^(n-j)x_n` and `h_j=q*T_j-T_(j+1)`,

`sum_(n<N)n*x_n^2 - sum_(m,n<N,m!=n)q^|m-n|x_m*x_n`
` = -q^2*T_0^2 + sum_(j<N)(j+1)*h_j^2`.

It can alternatively be proved without a limit: `x_j=T_j-q*T_(j+1)` and
`x_j^2-h_j^2=(1-q^2)(T_j^2-T_(j+1)^2)`. Telescoping with weights 1 and j+1,
then using AIT's `kmsForm_eq_tail`, gives the displayed identity.
This finite algebraic identity holds for every real q.

### 4. Finite-prime assembly identifies the actual arithmetic operator

Unique prime factorization identifies S_Q with the exponent vectors Q->N.
On these coordinates, AIT's `ladderKernel_eq_tensor` and its exact transverse
tower decomposition identify the actual prime kernel with

`P_Q=sum_(p in Q) log(p) (K_(p^(-1/2))-I)_p`.

Each summand is bounded and self-adjoint, so the finite sum gives the claimed
bounded extension of the actual matrix. Multiplication by log(n) is exactly
`sum_p log(p) D_p`. Thus A_Q is the stated sum of local operators plus gamma_Q.
Its domain remains the maximal log-weighted domain; bounded perturbation gives
closedness and symmetry there.

Take finite tensor products of the local bases. Their inner products factor,
and they are complete: finite coordinate tensors span a dense subspace, each
factor can be approximated by finite local eigenvector sums, and the pure-tensor
norm is the product of the factor norms. This proves completeness on the actual
ell-two exponent-vector carrier, transported by the factorization equivalence.
The local coefficient equations also prove that each product mode belongs to
the log-weighted domain: its log-weighted sequence equals a finite sum of
bounded local KMS images plus a scalar multiple of the mode. This proves
square-summability directly. The same equations give its eigenvalue.

Index the local ground by exponent 0 and local mode k>=1 by exponent k. For
`m=product_p p^(e_p)`, the energy is

`gamma_Q+sum_p log(p)*(if e_p=0 then -1/(p-1) else e_p)`
` =gamma+sum_p e_p*log(p)+sum_(p divides m)log(p)/(p-1)`.

This is the actual `gamma+log(m)+tameDifferent(m)`. AIT's torsion adjunction
`selfIntersection(m)=log(m)-tameDifferent(m)` proves the second arithmetic
expression. The same closed-graph/basis argument from step 3 proves the exact
maximal-domain identification for A_Q and its self-adjointness.

### 5. Simplicity and compact inverse

If two energies agree, multiply their logarithmic identity by
`L=product_(p in Q)(p-1)>0`. Exponentiating gives equality of integer prime-power
products. Unique factorization equates each exponent

`L*e_p+(L/(p-1))*1_(e_p>0)`.

This is strictly increasing as a function of e_p, so all exponents coincide.
The labels and eigenvalues are therefore simple, including the empty-prime
case, which has only the label 1.

The positive shifted energies are
`r(m)=1+log(m)+tameDifferent(m)>=1+log(m)>=1`.
For every bound C, only finitely many positive integers have r(m)<=C, since
m<=exp(C-1). Define the inverse in the complete eigenbasis by multiplying the
m-th coefficient by 1/r(m). These multipliers are bounded by one and tend to
zero off finite sets. Finite-coordinate truncations converge in operator norm,
so this bounded inverse is compact. Multiplication by E(m)/r(m) is bounded,
which puts its output in the proved maximal domain. Coefficientwise identities
prove both inverse equations for `A_Q+(1-gamma)I`.

### 6. The horizon bridge

For a fixed finite real class vector b, write `D_d(M)=H_d(M)/delta_d`. The
formalized finite-sieve harmonic law gives

`D_d(M)-log(M)->gamma_Q-log(d)`, `D_d(M)/log(M)->1`.

The actual ordinary norm is `sum_d b_d^2 D_d(M)` and the actual polar counterterm
is `sum_d b_d^2 D_d(M)^2`. Therefore

`(C_M-log(M)||x_b||_M^2)/log(M)`
` -> sum_d b_d^2*(gamma_Q-log(d))`.

Add the proved finite-part limit
`(B_M-C_M)/log(M)->-2gamma_Q sum_d b_d^2+sum_(d,e)b_d b_e P(d,e)`.
The result is exactly `-Re<b,A_Q b>`, using the actual matrix of P_Q from
step 4. This establishes the connection to the horizon form without assuming
an archimedean payment or an all-primes limit.

## Novelty and scope

The existing one-prime Hodge module proves the first excitation gap and one
positive square. `TheValuationTowerIsExactlySolvable` also proves every
pointwise pole-gauge eigenvector (`towerOp_pole`, `towerOp_step`) and the sharp
depth-uniform gap. Those local eigenvalues and eigenvectors are baseline.
Its operator is a pointwise formula on real sequences; it does not construct
the complete Hilbert basis, maximal operator domain, or finite-prime arithmetic
spectrum. Its formalized card `rapt-valuation-tower-exactly-solvable.md` also
anticipates the Kronecker-sum list `gamma+sum_p log(p)(k_p+1/(p-1))` over excited
primes. That energy list alone, and its relabelling by integers, are not novelty.
The new assertion identifies the literal bounded prime kernel and original
maximal domain, proves the basis complete there, proves simplicity and the
compact actual inverse, and identifies the actual horizon defect with its form.
`covariantCounterterm_sharp` already proves the sharp top bound
for every atomic profile. None of those conclusions is counted again.
The new target is the complete explicit basis, actual operator domain, simple
arithmetic spectrum, compact inverse, and exact horizon-defect identification.
Corpus searches for geometric Haar, Blaschke number, valuation/KMS spectra, and
closed eigenbasis domains found the listed building blocks but no such operator
identification. The algebraic geometric spectrum in
`GomesFormalSeriesOperatorSpectrum` concerns formal differentiation on
polynomials and is unrelated.

The final novelty recheck also inspected the valuation-energy section of
`RHTower/ChiRamanujanFinsuppTrace.lean`: its energy is a squared coefficient
times an Euler weight, used for summability of a different dilation trace.
`RHTower/KrejcirikTransverseValuationPseudospectrum.lean` through its spectrum
theorem treats a finite Gaussian similarity of a prescribed label diagonal.
Neither constructs the present number-minus-Weil-kernel operator.

Q is finite throughout. No all-prime Weil sign, RH conclusion, or comparison
with the full Weil-test carrier is claimed. Compatible completion through prime
ground states is a separate backlog conjecture:
`docs/drafts/pipeline/0-backlog/coherent-prime-ground-state-completion.md`.

## Lean implementation checkpoint

- `HTGeometry/HardyBlaschkeMonomialBasis.lean` passed its scratch check and
  first dependency olean build. It uses `HardyLeakageRankOne` and
  `HilbertSchmidtMatrix` for the complete geometric-complement/Blaschke basis.
- `HTGeometry/HardyGeometricResolvent.lean` passed its scratch check and its
  first dependency build. It constructs
  `R=(I+q U)/(1-q^2)` from the actual Blaschke multiplier, proves the inverse
  equations and coefficient recurrences, and identifies the bounded
  self-adjoint `R+R*-I` with the geometric KMS matrix. This equivalent
  construction avoids an unnecessary second inverse operator.
- `HTGeometry/HardyBlaschkeNumberModes.lean` passed its scratch check and first
  dependency olean build. It contains the squared-resolvent
  recurrence, adjoint kernel identity, exact Blaschke/KMS coefficients, and
  number-domain proofs through bounded images.
- `HTGeometry/ClosedEigenbasisDomain.lean` passed its scratch check and first
  dependency olean build. It gives the full graph/domain and
  self-adjointness argument for a complete real eigenbasis. The existing
  `LinearPMapBoundedUnitaryTransport` already supplies bounded-perturbation
  closedness and unitary transport, so those helpers will be reused.
- `HTGeometry/HardyNumberMinusKMS.lean` defines the actual maximal-number-domain
  bounded perturbation and assembles local eigenmodes, domain equivalence, and
  self-adjointness. Scratch check and first dependency olean build passed.
- `HTGeometry/LpProductUnitary.lean` proves tensor unitaries, product Hilbert bases,
  and bounded fibre operators on actual product coordinates. It reuses
  `LpTwoCurry`, `LpFamilyIsometry`, `WoldThermofieldStandardForm`, and Mathlib's
  `lp.mapCLM` (located after corpus search). Scratch and first dependency
  olean build passed.
- `HTGeometry/LpFiniteProductUnitary.lean` proves finite product-basis assembly by
  empty/option induction. Scratch and first dependency olean build passed.
  `RAPT/TheAdjunctionEnergySeparatesValuations.lean` proves strict local rational
  weights, injectivity of their prime-log sum, and nonnegativity/logarithmic bounds
  for the tame different. Scratch check and first required dependency build passed.
- `RAPT/TheSieveClassesAreValuationCoordinates.lean` proves the exact
  `SieveSupported`/exponent-function equivalence, its logarithmic degree, and
  off-prime coordinate agreement. Scratch and first dependency build passed.
  `HTGeometry/ClosedEigenbasisPositiveInverse.lean` proves actual graph inverse
  equations and compactness from proper positive eigenvalues. Scratch check
  and first required dependency build passed.
- `HTGeometry/HardyNumberSpectrum.lean` reindexes the local basis by natural labels.
  Scratch and first dependency build passed.
- `HTGeometry/LpFiniteCoordinateOperator.lean` proves exact coordinate-fibre matrix
  and product-basis actions. Scratch and first dependency build passed.
  `HTGeometry/FiniteBlaschkeNumberOperator.lean` assembles finite weighted local
  operators on their actual maximal domain. Scratch check and first required
  dependency build passed, including complete spectral-domain equivalence and
  self-adjointness.
- `RAPT/TheSieveExcitationsHaveAdjunctionEnergy.lean` proves exact prime-ground
  cancellation, the tame-different label, simple arithmetic energies, and properness.
  Scratch check and first required dependency build passed.
  `/tmp/TheTowerNumberFormIsAWeightedSquareSum.lean` drafts the finite square identity.
  `RAPT/TheFiniteSieveHorizonDefectHasTheClassEnergy.lean` proves the actual matched
  horizon limit in original class coordinates. Scratch check passed; its first
  required dependency build is active. The finite-square draft awaits checking.
- `RAPT/TheSievePrimeKernelIsABoundedOperator.lean` proves the exact bounded,
  self-adjoint extension of the literal prime kernel on all supported integers.
  Its matrix identification uses the full off-prime valuation equivalence;
  that equivalence has been added to the valuation-coordinate scratch draft.
  Fibre matrix evaluation is isolated in `HTGeometry/LpGeometricCoordinateKernel.lean`
  to keep Hardy-space coercions out of the arithmetic comparison. An explicit
  equality identifies singleton vectors formed with different equality instances.
  Scratch check and first required dependency build passed; the refactored
  arithmetic kernel comparison passed after the same singleton normalization
  was supplied for the finite exponent-function index. Its first dependency
  olean build passed.
- `RAPT/TheSieveOperatorHasTheAdjunctionEigenbasis.lean` proves the actual
  transported operator, original maximal log domain, explicit product coefficients,
  literal kernel action, simple arithmetic energies, and full spectral domain.
  Scratch check and first required dependency build passed. It also proves
  every actual eigenvector lies on its one-dimensional basis line, and every
  nonzero eigenvector has an energy from the arithmetic list.
- `RAPT/TheAdjunctionResolventIsCompact.lean` proves the positive shifted operator,
  reciprocal basis inverse, both actual-domain inverse equations, and compactness.
  Scratch check passed. Sixteen transitive endpoint reports use only `propext`,
  `Classical.choice`, and `Quot.sound`; saved in
  `logs/local-valuation-adjunction-axioms-2026-10-28.log`. No olean is needed for this leaf.
- `RAPT/TheSieveHorizonDefectIsTheAdjunctionOperator.lean` proves the exact finite
  Hilbert quadratic form and its actual horizon limit, with final statement
  quantified over a finite set of supported classes and arbitrary real coefficients.
  Scratch check passed. Both endpoint axiom reports use only `propext`,
  `Classical.choice`, and `Quot.sound`; appended to the persistent audit log.
  No olean is needed for this leaf. The finite weighted-square identity is checking.
- `HTGeometry/HardyBlaschkeCoefficients.lean` proves the closed normalized ground
  and excitation coefficient formulas from the existing Szego-kernel norm identity.
  Scratch check and first required dependency build passed.
  This exposes the precise coefficients of the product basis stated above.
- Inspected: `HardyDiskModelSpace`, `HardyBeurlingInvariantSubspace`,
  `BoundedResolventNeumann`, `MaximalRealDiagonalSelfAdjoint`,
  `DiagonalCompactOperator`, `HistoryTensorOperators`,
  `TheTowerFormOfAPrime`, `ThePrimeKernelIsASumOfTransverseTowers`,
  `TheDifferentOfATorsionOrbit`, and the formalized finite-sieve package.
- `HilbertBasis.mkOfOrthogonalEqBot` and `IsSelfAdjoint.isClosed` were located
  in Mathlib after corpus search. New uses must pass scratch checks before
  repository insertion. The dependency oleans listed above exist.
- Generic helpers and the local finite identity are not separate contributions.
  The main actual operator and complete spectral-domain theorem are checked in
  scratch. Compact inverse and horizon bridge have passed scratch and their
  endpoint axiom audits. The finite-square check, final actual-source checks,
  and umbrella wiring remain; the contribution is uncounted.

- [x] 0 -> 1: explicit operator, actual horizon bridge, corpus novelty audit.
- [x] Paper proof above closes the local and finite-prime domains and inputs.
- [ ] Exact Lean formalization and final audit.
