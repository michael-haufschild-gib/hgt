# Bures incidence minimax coarea law

- **ID:** `bures-incidence-minimax-coarea-law`
- **Stage:** 3-formalized
- **Type:** theorem / source--target incidence minimax law
- **Parents:** `../3-formalized/replica-hilbert-coarea-incidence-law.md`,
  `../3-formalized/return-excised-optimal-design-coarea-law.md`,
  `radial-krylov-projected-complete-incidence-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [KERNEL-AUDITED] [EXTERNAL PRIORITY NOT ESTABLISHED]`
- **Date:** 2026-08-08

## Public sentence

**The complete shortcut union is governed not by target count or occupied rank, but by the largest
Bures fidelity between the quenched replica covariance and a convex mixture of the actually
occupied target rays.**

This is the sharp source-aware quadratic replacement for the projected incidence moment.  It keeps
every source fibre sheet, forgets duplicate target labels, allows an arbitrary compact target
family, and removes a target-independent return set once.

## The universal minimax law

Let `H` be a finite-dimensional complex Hilbert space, let `(X,mu)` be a finite measure space, and
let `u:X->H` be square-integrable.  Let `V` be a nonempty arbitrary subset of the closed unit ball
of `H`.
Assume the complete capture event

```text
E_b = {x : there exists v in V with |<u(x),v>|^2 >= b},   b>0,
```

is measurable.  Define the unnormalized quenched covariance and occupied-ray convex body

```text
C = integral_X |u(x)><u(x)| dmu(x),
K(V) = closed convex hull { |v><v| : v in V }.
```

For positive operators `C,M`, use root-fidelity convention

```text
F(C,M) = Tr sqrt(C^(1/2) M C^(1/2)).
```

Then

```text
                                      2
b mu(E_b) <= max { F(C,M) : M in K(V) }

            = inf     Tr(C A) sup <v,A^(-1)v>.              (BIM)
              A>0             v in V
```

Here `A>0` means positive definite.  The infimum need not be attained when the source or occupied
image is singular.  Since the rank-one image of the unit ball is compact in finite dimension,
`K(V)` may equivalently be formed after closing `V`; the maximum exists.  Thus `(BIM)` covers finite,
countably infinite, and continuous target families without target enumeration.

The second line is an equality, not a comparison.  It says the Bures quantity is exactly the best
ellipsoidal Cauchy--Schwarz reporter available after source covariance and occupied target image are
both known.

## Return-excised law

For any independently fixed measurable return set `R`, put

```text
C_R = integral_(R^c) |u(x)><u(x)| dmu(x).
```

Then

```text
mu(E_b)
 <= mu(R)
  + b^(-1) max {F(C_R,M)^2 : M in K(V)}.                    (BIM-R)
```

No source quotient occurs.  If several source points have the same endpoint, every point remains
in `C_R` with its original weight.  Duplicate target labels do not change `K(V)`.  Adding the zero
target also changes neither maximum nor capture event at positive threshold.

## Conditional/bundle law

The theorem also covers source-dependent target geometry after honest disintegration.  Let `Y` be
a standard Borel context space, disintegrate the finite source law as

```text
mu(dy,dx) = nu(dy) mu_y(dx),
```

and suppose `V_y` is a nonempty compact target family which is fixed inside the conditional source
fibre `mu_y`.  Put

```text
C_y = integral |u(y,x)><u(y,x)| dmu_y(x),
Gamma_y = max {F(C_y,M)^2 : M in K(V_y)}.
```

Whenever the resulting functions and capture event are measurable,

```text
b mu{(y,x): exists v in V_y,
                  |<u(y,x),v>|^2 >= b}
 <= integral_Y Gamma_y dnu(y).                               (BIM-C)
```

The return-excised form replaces `C_y` by its integral on the conditional complement and pays the
global return mass once.  This is immediate from `(BIM)` on almost every conditional fibre and
Tonelli integration.  It is the correct way to handle random occupied images: the target family
may vary with the context `y`, but it may not vary with the residual variable `x` left inside the
same covariance without a further disintegration.

## Fixed-carrier Krylov-projected complete-incidence corollary

Use the notation of `radial-krylov-projected-complete-incidence-law.md`.  For a measurable time map
`tau:X->[-T,T]`, set

```text
u_(K,r)(x) = phi_K(tau(x))^(tensor r),
v_(K,r)(z) = (P_K z)^(tensor r),

C_(K,r,R) = integral_(R^c)
  |u_(K,r)(x)><u_(K,r)(x)| dmu(x),

K_(K,r)(Z) = closed convex hull
  {|v_(K,r)(z)><v_(K,r)(z)| : z in Z}.
```

If the original orbit is captured at squared fidelity `a`, `0<a<=1`, and

```text
eta_K(T) < sqrt(a),
```

then the projected amplitude has modulus at least `sqrt(a)-eta_K(T)`.  Consequently

```text
mu(E_a)
 <= mu(R)
  + (sqrt(a)-eta_K(T))^(-2r)
      max {F(C_(K,r,R),M)^2 : M in K_(K,r)(Z)}.              (K-BIM)
```

This strictly weakens the projected occupied-span obligation on every source fibre on which `P_K`
is fixed, for example a fixed Hamiltonian with time as source variable, or a genuine conditional
law after disintegration by a carrier context.  One no longer needs decay of the entire projected
occupied-span moment on that fibre.  It is enough to prove Bures separation of the conditional
projected-orbit covariance from every convex mixture of actual projected shallow-circuit rays.

It is invalid to average the displayed `C_(K,r,R)` over Hamiltonians while silently treating
`P_K(H)Z` as one fixed target body.  Either keep the Hamiltonian fixed, disintegrate by enough
context to make `P_K(H)Z` fixed, or use the unprojected ensemble corollary below.

## Ordinary static-local ensemble corollary

For the ordinary one-draw ensemble, disintegrate only by the independently chosen seed `chi`.  The
depth-`s` occupied circuit image `Z_s(chi)` is then fixed, while all Hamiltonian randomness remains
inside the conditional covariance.  Put

```text
C_(r,t,R)^chi
 = E_H[1_(R^c)(H,chi)
       |psi_(H,chi)(t)^(tensor r)>
       <psi_(H,chi)(t)^(tensor r)|],

K_(r,s)^chi
 = closed convex hull
   {|z^(tensor r)><z^(tensor r)| : z in Z_s(chi)}.
```

For squared-fidelity threshold `a`, `(BIM-C)` gives the exact complete-circuit estimate

```text
Pr_(H,chi)(E_a)
 <= Pr_(H,chi)(R)
  + a^(-r) E_chi max {
      F(C_(r,t,R)^chi,M)^2 : M in K_(r,s)^chi}.             (SL-BIM)
```

This is a valid strict weakening of the ensemble projected-moment conjecture: fidelity
Cauchy--Schwarz bounds each conditional Bures maximum by the corresponding occupied-span trace.
No random Krylov flag is conditioned on, and no target is allowed to depend on the still-random
Hamiltonian.

## Dependency-closed proof

### Step 1 -- every positive reporter controls the complete union

Fix `A>0`.  Matrix Cauchy--Schwarz gives, for every source vector `u` and occupied target `v`,

```text
|<u,v>|^2
 = |<A^(1/2)u,A^(-1/2)v>|^2
 <= <u,A u> <v,A^(-1)v>.                                  (1)
```

Put

```text
L_V(A) = sup_(v in V) <v,A^(-1)v>.
```

If `x in E_b`, some occupied target witnesses capture, so `(1)` gives

```text
b <= L_V(A) <u(x),A u(x)>.                                (2)
```

Integrating `(2)` over `E_b`, enlarging the nonnegative integral to `X`, and using the covariance
definition yields

```text
b mu(E_b) <= L_V(A) Tr(C A).                              (3)
```

Taking the infimum over `A>0` proves the inequality in `(BIM)`.  This operation handles the complete
target union before integration; there is no targetwise union bound.

### Step 2 -- scale turns the product into the Alberti fidelity functional

For each fixed positive-definite shape `A`, scalar rescaling gives

```text
inf_(c>0) 1/2 [Tr(C cA) + L_V(cA)]
 = sqrt(Tr(C A) L_V(A)).                                  (4)
```

Therefore

```text
sqrt(inf_(A>0) Tr(CA)L_V(A))
 = inf_(A>0) 1/2 [Tr(CA)+L_V(A)].                         (5)
```

Every linear functional reaches the same supremum on a set and on its closed convex hull.  Hence

```text
L_V(A) = max_(M in K(V)) Tr(M A^(-1)).                    (6)
```

The function

```text
(M,A) |-> 1/2 [Tr(CA)+Tr(MA^(-1))]
```

is affine in `M` and convex and continuous in `A`; inversion is operator convex on the positive
cone.  The compact-convex form of the minimax theorem, with the compact variable `M in K(V)`, gives

```text
inf_(A>0) max_(M in K(V)) 1/2[Tr(CA)+Tr(MA^(-1))]
 = max_(M in K(V)) inf_(A>0) 1/2[Tr(CA)+Tr(MA^(-1))].     (7)
```

For arbitrary positive semidefinite `C,M`, the variational formula for root fidelity is

```text
inf_(A>0) 1/2[Tr(CA)+Tr(MA^(-1))]
 = Tr sqrt(C^(1/2) M C^(1/2))
 = F(C,M).                                                 (8)
```

For positive-definite `C,M`, `(8)` follows from the polar decomposition and matrix arithmetic--
geometric mean inequality, with equality at the geometric-mean reporter.  Adding `epsilon I` and
letting `epsilon` decrease to zero proves the singular case; the infimum may then move to the
boundary.  Substituting `(8)` into `(7)`, then squaring `(5)`, proves the equality in `(BIM)`.

### Step 3 -- return removal and Krylov approximation

Apply `(BIM)` to the restricted measure `mu|_(R^c)` and use

```text
E_b subset R union (E_b intersect R^c)
```

to prove `(BIM-R)`.

For `(K-BIM)`, original capture supplies a target `z` with

```text
|<psi(tau(x)),z>| >= sqrt(a).
```

The factorial Krylov estimate and `||z||<=1` give

```text
|<phi_K(tau(x)),P_K z>|
 = |<phi_K(tau(x)),z>|
 >= sqrt(a)-eta_K(T).                                     (9)
```

Tensor inner products factor, so `(9)` raised to replica order yields squared replica overlap at
least `(sqrt(a)-eta_K(T))^(2r)`.  Apply `(BIM-R)` to the displayed projected source and target
vectors to prove `(K-BIM)`.

## Exact comparison with previous incidence laws

Let `S=span V`, let `P_S` be its orthogonal projector, and suppose `||v||<=1`.  Every
`M in K(V)` has trace at most one and is supported on `S`.  Fidelity Cauchy--Schwarz gives

```text
F(C,M)^2 <= Tr(P_S C) Tr(M) <= Tr(P_S C).                 (10)
```

Thus `(BIM)` is never weaker than the replica target-span projection law

```text
b mu(E_b) <= Tr(P_S C).
```

It can be strictly stronger.  If the source is deterministic, `C=|u><u|`, then

```text
max_(M in K(V)) F(C,M)^2
 = sup_(v in V) |<u,v>|^2.                                (11)
```

The span projector can equal the identity while `(11)` is arbitrarily small.  Conversely, for
uniform source mass on an orthonormal target basis, the Bures maximum equals `Tr(P_S C)`; no
universal strict improvement is possible.

The target-only D/G-optimal-design theorem is recovered by the rank bound

```text
F(C,M)^2 <= rank(M) Tr(CM).
```

The new law is sharper because it optimizes the full singular-value profile of `C^(1/2)M^(1/2)`,
not only target rank or a uniform fixed-target moment ceiling.

## Opposite-tilt observer certificate

Every positive-definite reporter has the form `A=exp(W)` for a Hermitian observable `W`.  Thus
`(BIM)` immediately gives

```text
b mu(E_b)
 <= Tr(C exp(W)) sup_(v in V) <v,exp(-W)v>.                 (TILT)
```

The two factors are opposite half-density observation channels.  This is the noncommutative
source--target version of the classical Hellinger/Bhattacharyya exponential-tilt inequality already
present in the read-only corpus.

For physical one-copy states `psi(x)` and unit targets `z`, use replica vectors
`u(x)=psi(x)^(tensor r)`, `v(z)=z^(tensor r)` and choose the additive reporter

```text
W_[r] = W tensor I tensor ... + ... + I tensor ... tensor W.
```

Since `exp(W_[r])=exp(W)^(tensor r)`, `(TILT)` becomes

```text
a^r mu(E_a)
 <= [sup_(z in Z) <z,exp(-W)z>]^r
      integral_X <psi(x),exp(W)psi(x)>^r dmu(x).           (TILT-r)
```

The return-excised version restricts the source integral to `R^c` and adds `mu(R)` once.  Hence an
explicit observer `W` satisfying, off one target-independent exceptional set,

```text
<psi(x),exp(W)psi(x)>
  sup_(z in Z)<z,exp(-W)z> <= a exp(-gamma)
```

proves complete-union decay `exp(-gamma r)` with no circuit-label union.  Allowing a genuinely
collective replica observable `W_r` recovers the full Bures optimum; restricting to additive
`W_[r]` is a deliberate proof strategy, not an assumption hidden in `(BIM)`.

### Bures equilibrium reporter

In the nondegenerate case, let `M_* in K(V)` maximize fidelity and let `A_*` minimize the saddle
functional in `(7)`.  First variation in `A` gives the exact transport equation

```text
A_* C A_* = M_*.                                            (EQ1)
```

Equivalently,

```text
A_* = C^(-1/2)
      [C^(1/2) M_* C^(1/2)]^(1/2)
      C^(-1/2),

Tr(C A_*) = Tr(M_* A_*^(-1)) = F(C,M_*).                   (EQ2)
```

If `M_*` is represented by an occupied-endpoint probability design, every endpoint with positive
design weight obeys

```text
<v,A_*^(-1)v> = sup_(w in V)<w,A_*^(-1)w>.                 (EQ3)
```

Indeed, at the saddle `M_*` maximizes the affine functional `M |-> Tr(MA_*^(-1))`; a convex
mixture can be maximal only when every positively weighted extreme point is maximal.  Singular
cases follow on their joint support or by positive regularization, with possible nonattainment at
the boundary.

Thus the optimal observer `W_*=log A_*` is geometric transport from quenched source covariance to
the hardest convex mixture of occupied targets.  Local-Hamiltonian analysis need not guess an
arbitrary normalization: it must bound, approximate, or separate this source--target transport.

## Exact sheet--target incidence operator

The Bures quantity has an equivalent operator form which makes fibre sheets explicit.  For a
probability design `lambda` on the occupied target family, define synthesis maps

```text
U : L^2(X,mu) -> H,
U f = integral_X f(x) u(x) dmu(x),

V_lambda : L^2(V,lambda) -> H,
V_lambda g = integral_V g(v) v dlambda(v).
```

For a finite target family, the second integral is the sum with target column `sqrt(lambda_v)v`
after identifying `L^2(V,lambda)` with weighted coordinates.  These maps satisfy

```text
U U^* = C,
V_lambda V_lambda^* = M_lambda
  = integral_V |v><v| dlambda(v).
```

Define the sheet--target incidence operator

```text
K_lambda = U^* V_lambda : L^2(V,lambda) -> L^2(X,mu).
```

Its kernel is exactly

```text
K_lambda(x,v) = <u(x),v>.                                  (INC1)
```

Polar decomposition of `U` and `V_lambda` shows that partial isometries do not change the nonzero
singular values, and therefore

```text
||K_lambda||_(Schatten 1)
 = ||C^(1/2) M_lambda^(1/2)||_(Schatten 1)
 = F(C,M_lambda).                                          (INC2)
```

Consequently the universal law is equivalently

```text
b mu(E_b)
 <= sup_(probability designs lambda on V)
      ||K_lambda||_(Schatten 1)^2.                         (INC3)
```

For replica source and target vectors, `(INC1)` becomes

```text
K_(r,lambda)(x,z) = <psi(x),z>^r.                          (INC4)
```

Thus replica order acts on the physical incidence kernel before any norm is taken.  Source sheets
remain distinct `L^2(X,mu)` coordinates; occupied target labels enter only through their convex
mixture and synthesis range.

This identifies why the earlier norm choices lost the frontier:

```text
||K||_1^2 <= rank(K) ||K||_2^2.                            (INC5)
```

The Hilbert--Schmidt norm is only the weighted average of fixed-target replica moments, and `(INC5)`
reintroduces occupied incidence rank.  Operator norm can ignore how many source sheets carry the
incidence.  Schatten-1 is the exact complete-union norm selected by Bures minimax geometry.  The
ordinary-static-local problem is therefore a uniform nuclear-norm contraction theorem for the
physical replica incidence kernels, not an operator-norm, Hilbert--Schmidt, determinant, or raw
coarea estimate.

## Separable trace-class extension

The law is not intrinsically finite-dimensional.  Let `H` be a separable Hilbert space, let `u` be
Bochner square-integrable, and let `V` be a nonempty norm-compact subset of its closed unit ball.
Then:

1. `C=integral |u><u|` is positive trace class;
2. the rank-one map is continuous from the norm topology of `H` to trace norm, so `K(V)` is a
   trace-norm compact convex set;
3. every target probability design has a Hilbert--Schmidt synthesis map `V_lambda`, while the
   source synthesis map `U` is Hilbert--Schmidt;
4. `K_lambda=U^*V_lambda` is trace class and `(INC2)` remains exact;
5. the von Neumann-algebraic Alberti formula gives `(8)` with `A` ranging over bounded strictly
   positive invertible operators;
6. compact-convex minimax then proves `(BIM)`, `(BIM-R)`, and `(INC3)` verbatim.

Thus arbitrary finite systems, countably infinite carriers, continuous compact target images, and
trace-class source laws obey the same incidence law.  This does not by itself establish a
thermodynamic limit for local Hamiltonians: one must still prove uniform trace-class tightness and
the physical nuclear-norm contraction before passing to that limit.

## Distance, saturation, and observer laws

Assume now that source vectors and occupied targets are unit vectors, and let

```text
tau = Tr(C) > 0,     rho = C/tau.
```

Every member of `K(V)` is then a density operator.  Define distance from the quenched source state
to the occupied target body by

```text
d_B(rho,K(V))
 = min_(M in K(V)) sqrt(2[1-F(rho,M)]).
```

Homogeneity of fidelity turns `(BIM)` into the exact distance identity

```text
max_(M in K(V)) F(C,M)^2
 = tau [1 - d_B(rho,K(V))^2/2]^2.                       (12)
```

Consequently:

```text
max_(M in K(V)) F(C,M)^2 = tau
  iff rho belongs to K(V),                                (13)

max_(M in K(V)) F(C,M)^2 = 0
  iff supp(C) is orthogonal to every occupied target.     (14)
```

Equation `(13)` is the exact quadratic no-go.  If the normalized quenched covariance is already a
randomized shallow-circuit state in replica space, no positive quadratic reporter can distinguish
it.  Exponential shortcut suppression requires the source covariance to approach maximal Bures
distance from the complete shallow-target convex body, not merely to have large ambient rank.

Let `Phi` be any trace-preserving completely positive map.  Fidelity data processing gives

```text
max_(M in K(V)) F(C,M)^2
 <= max_(N in Phi(K(V))) F(Phi(C),N)^2.                    (15)
```

Thus lossy observation can only increase apparent source--target incidence.  Conversely, to prove
small full incidence it is enough to find one coarse observer which still separates the source
from every occupied-target mixture.

For a POVM `(E_j)`, put

```text
p_j = Tr(rho E_j),
q_j(v) = <v,E_j v>,
Q(V) = closed convex hull {q(v) : v in V}.
```

The measurement channel and `(15)` give the classical Hellinger certificate

```text
max_(M in K(V)) F(C,M)^2
 <= tau max_(q in Q(V)) (sum_j sqrt(p_j q_j))^2.           (16)
```

This is the direct interface with local Pauli-word, Krylov-innovation, and history-orientation
measurements.  A classical Hellinger separation theorem for one such observer is sufficient for
the full quantum complete-union bound; no reconstruction of the entire replica covariance is
needed.

## Conjecturing and falsification ledger

### C0 -- raw coarea mass is the missing invariant

**Failed / circular.**  Coarea disintegration reproduces source event mass, including fibre sheets,
but supplies no independent upper bound.

### C1 -- projected occupied-span covariance is the final invariant

**True but lossy.**  `Tr(P_S C)` solves target enumeration, yet forgets how quenched source
covariance is oriented inside the occupied span.  A deterministic source and many nearly
orthogonal occupied targets make the loss arbitrarily large.

### C2 -- target-only optimal design is universally sharp

**False once source covariance is known.**  The dimension factor is sharp under a uniform
fixed-target moment ceiling, but it is not sharp for anisotropic source covariance.

### C3 -- source-aware ellipsoidal reporter

**Proved.**  Equations `(1)--(8)` identify its exact optimum with maximum Bures fidelity against the
occupied-ray convex body.

### C4 -- the minimizing reporter itself is the new physical assumption

**Rejected.**  Reporter optimization is unconditional finite-dimensional convex geometry.  Local
physics enters only when bounding the resulting Bures incidence.  Hiding that bound in a chosen
reporter would be circular.

### C5 -- a coarse observer loses the required separation

**False as a proof obstruction.**  Data processing does make source and targets closer, but this
has the useful contrapositive `(16)`: exponential separation which survives one chosen coarse
observer certifies exponential separation in the full carrier.

### C6 -- a simple conserved or return-projector tilt closes local growth

**Failed.**  Energy tilts are constant along the orbit and can be reproduced by shallow targets.
A return-projector tilt controls the seed direction but the complete shallow target convex body
contains directions which evade the same sign of tilt.  Neither supplies a product below the
capture threshold.

**Positive survivor:** construct an oriented history/Pauli-word observable, generally collective
at replica order `r`, whose opposite exponential channels separate quenched orbit covariance from
every shallow-target mixture.

### Positive survivor

The exact ordinary-static-local core is now

```text
Pr(R) + a^(-r) E_chi max {
  F(C_(r,t,R)^chi,M)^2 : M in K_(r,s)^chi}
 <= o_n(1) + exp(-gamma r),                                (17)
```

at scale-matched `r,t,s`.  This is weaker than decay of the full projected carrier action.  On each
fixed conditional geometry it is the strongest bound obtainable from a positive quadratic
reporter without discarding source multiplicity or occupied-target geometry.  By `(16)`, a
sufficient next theorem is exponential classical Hellinger separation under one explicitly
constructed local/history observer.

## Hostile audit

1. **No local-Hamiltonian decay is claimed.**  `(BIM)` proves the exact universal reduction and a
   strictly smaller physical invariant.  It does not prove `(17)` for the ordinary static-local
   shell.
2. **Fidelity ingredients are prior mathematics.**  Variational fidelity, Bures geometry, convex
   state approximation, and minimax theory are established subjects.  Candidate novelty is their
   exact composition with complete return-excised replica incidence, source-sheet retention,
   occupied circuit image, and Krylov projection.  Priority remains unverified.
3. **The Bures maximum can still be one.**  If normalized source covariance belongs to the occupied
   target convex body, no source-aware quadratic argument can prove decay; this is a genuine
   obstruction, not a defect of the theorem.
4. **Infinite carrier has explicit hypotheses.**  The separable extension requires trace-class
   source covariance and norm-compact target image.  It does not cover arbitrary noncompact target
   families, continuous spectrum with infinite source mass, or a thermodynamic limit without
   uniform tightness.
5. **Random-carrier conditioning may be useless.**  A sufficiently resolved Krylov flag can encode
   most or all of the coefficient direction, leaving an atomic conditional source law.  The theorem
   never assumes that conditioning on the full flag creates anti-concentration.
6. **Measurability is explicit.**  For a nonmeasurable arbitrary target union, use outer measure or
   impose a compact target parameterization with measurable overlap supremum.  No silent selector
   measurability is assumed.
7. **No computability claim.**  The maximum and infimum are exact mathematical objects.  Device
   estimation or scalable numerical optimization is outside this theorem.
8. **Publication boundary.**  The law can strengthen the master paper's universal mathematical
   spine after formal verification.  It cannot by itself authorize Brown--Susskind growth or a
   Nature-level physical claim.

## External separation audit

- Alberti's variational fidelity theory supplies `(8)` in much greater operator-algebraic
  generality: <https://arxiv.org/abs/math-ph/0202032>.
- Fidelity optimization over convex mixtures of available states is known; for example:
  <https://arxiv.org/abs/2105.07336>.
- Composite quantum hypothesis testing already treats convex state alternatives and regularized
  asymptotic exponents: <https://arxiv.org/abs/1709.07268>.  Any publication claim must distinguish
  `(BIM-R)` as a single-shot complete-incidence/return law, not present convex alternatives as new.
- Kiefer--Wolfowitz D/G equivalence supplies the target-only optimal-design predecessor.
- The audited recurrence, circuit-complexity, quantum-fidelity, and optimal-design sources did not
  state `(BIM-R)` or `(K-BIM)`.  This is separation evidence, not a priority proof.

## Lean status

Formalization closes the full dependency-closed theorem family. Existing finite-dimensional,
return-excised, conditional, Krylov-projected, data-processing, observer-tilt, probability-design,
and sheet--target incidence modules cover the corresponding card statements. The remaining
separable positive-reporter gap is closed by:

- `GaloisForLFunctions/HTGeometry/FiniteDimensionalOperatorAlbertiLaw.lean`: exact operator--matrix
  bridge and finite-dimensional strictly-positive reporter approximation;
- `GaloisForLFunctions/HTGeometry/SeparableBuresPositiveReporterLaw.lean`: bounded-operator
  trace pairing, positivity, continuity, reporter-cone convexity, and lower Alberti bound;
- `GaloisForLFunctions/HTGeometry/SeparableBuresAlbertiApproximationLaw.lean`: finite-subspace block
  reporters, Hilbert--Schmidt tail control, and the singular separable Alberti equality;
- `GaloisForLFunctions/HTGeometry/SeparableBuresCompactTargetMinimaxLaw.lean`: compact-target Sion
  equality, exact reporter scaling, AM--GM infimum, and product-capacity square law.

Capstones `separableReporter_sInf_eq_operatorBuresRootFidelity`,
`separableBuresPrimalCapacity_eq_dualCapacity`, and
`separableBuresProductCapacity_eq_dualCapacity_sq` are unconditional theorems over their stated
mathematical objects. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
No card-specific axiom, `sorry`, `admit`, `opaque`, or `unsafe` declaration is used.

## Gates

- [x] Exact conjecture frozen
- [x] Counterexamples to raw-coarea, projector-finality, and target-only sharpness
- [x] Dependency-closed finite-dimensional proof
- [x] Return-excised, conditional, fixed-carrier Krylov, and ordinary-ensemble corollaries
- [x] Hostile internal audit
- [ ] External theorem-level priority established
- [x] Finite-dimensional minimax and physical corollaries formalized
- [x] Separable compact-body probability-design capacity and attained return law formalized
- [x] Infinite-dimensional positive-reporter/Alberti/Sion equality formalized

## Pipeline

- [x] Stage 1 -> 2: dependency-closed proof
- [x] Stage 2 -> 3: complete theorem family kernel-checked and umbrella-wired
- [ ] Stage 3 -> 4: only after external theorem-level priority is established

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/SeparableBuresAlbertiApproximationLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/SeparableBuresCompactTargetMinimaxLaw.lean
lake build GaloisForLFunctions.HTGeometry.SeparableBuresCompactTargetMinimaxLaw
#print axioms capstones: [propext, Classical.choice, Quot.sound]
```
