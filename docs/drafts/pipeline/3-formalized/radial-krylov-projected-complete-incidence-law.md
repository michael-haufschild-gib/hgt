# Radial--Krylov projected complete-incidence law

- **ID:** `radial-krylov-projected-complete-incidence-law`
- **Stage:** 3-formalized
- **Type:** theorem / exact frontier reduction
- **Parents:** `../3-formalized/krylov-carrier-load-shortcut-dichotomy-law.md`,
  `../3-formalized/replica-hilbert-coarea-incidence-law.md`,
  `return-excised-optimal-design-coarea-law.md`,
  `../1-in-progress/scale-matched-signed-action-packet-law.md`
- **Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [EXTERNAL PRIORITY NOT ESTABLISHED]`
- **Date:** 2026-08-08

## Public sentence

**Before the Krylov horizon, every complete quantum shortcut event is already visible inside one
causal projection of the occupied circuit image; everything outside that image contributes only a
factorial boundary error, while radial Hamiltonian scale changes time but not the image.**

## Theorem A -- causal projection before replicas

Let `H` be self-adjoint on a finite-dimensional complex Hilbert space `mathcal H`, let
`||H||<=B`, and let `psi_0` be a unit vector.  Put

```text
psi(t) = exp(-i t H) psi_0,
K_K = span_C { H^j psi_0 : 0 <= j <= K },
P_K = orthogonal projection onto K_K,
phi_K(t) = P_K psi(t),
eta_K(T) = (B T)^(K+1)/(K+1)!.
```

Let `Z` be any finite subset of the closed unit ball of `mathcal H`; repetitions and zero targets
are allowed.  For `r>=1`, define the original and causally projected occupied-image spaces

```text
S_r(Z)       = span_C { z^(tensor r) : z in Z },
S_(K,r)(Z)   = span_C { (P_K z)^(tensor r) : z in Z },
q_r(t)       = || Proj_(S_r(Z)) psi(t)^(tensor r) ||^2,
q_(K,r)(t)   = || Proj_(S_(K,r)(Z)) phi_K(t)^(tensor r) ||^2.
```

Then, for every `|t|<=T`,

```text
0 <= q_r(t) <= q_(K,r)(t) + 2 r eta_K(T).                  (1)
```

The projected occupied-image rank obeys the exact image identity and the two simultaneous caps

```text
S_(K,r)(Z) = P_K^(tensor r) S_r(Z),                         (2)

h_(K,Z)(r) := dim S_(K,r)(Z)
 <= min { dim S_r(Z), binom(dim K_K + r - 1,r) }.           (3)
```

Thus causal projection commutes with the Veronese replica lift exactly.  Distinct endpoints may
merge only when the causal carrier itself cannot distinguish them.

There is also a threshold form.  If `0<a<=1`, `eta_K(T)<sqrt(a)`, and

```text
E_a = { x : exists z in Z,
              |<psi(tau(x)),z>|^2 >= a },
```

for an arbitrary finite measure space `(X,mu)` and measurable `tau:X->[-T,T]`, then every
target-independent measurable return set `R subset X` satisfies

```text
mu(E_a)
 <= mu(R)
  + (sqrt(a)-eta_K(T))^(-2r)
      integral_(R^c) q_(K,r)(tau(x)) dmu(x).                (4)
```

Equivalently, the additive form obtained directly from `(1)` is

```text
mu(E_a)
 <= mu(R) + a^(-r)
      (integral_(R^c) q_(K,r)(tau(x)) dmu(x)
       + 2 r eta_K(T) mu(R^c)).                             (5)
```

Both bounds retain every source fibre sheet: integration is over the original `X`, not over its
endpoint quotient.  They depend on the target family only through the actual projected occupied
image.  Duplicate circuit labels do not change `(2)--(5)`, zero residual targets disappear, and
the return set is paid once before any replica or target operation.

## Theorem B -- radial scale changes time, not causal incidence geometry

Let

```text
H(x) = sum_(j=1)^m x_j A_j,       x in R^m,
```

for fixed self-adjoint operators `A_j`, and use the same seed, target image, `K`, and `r` as above.
For every nonzero real `c`,

```text
K_K(H(c x),psi_0) = K_K(H(x),psi_0),
P_K(c x) = P_K(x),
S_(K,r)(c x;Z) = S_(K,r)(x;Z),                              (6)

psi_(c x)(t) = psi_x(c t),
phi_(K,c x)(t) = phi_(K,x)(c t),
q_(K,r,c x)(t) = q_(K,r,x)(c t).                            (7)
```

In particular, if a standard Gaussian coefficient vector is written as `G=R Omega`, where `Omega`
is uniform on the unit sphere and independent of the chi radius `R`, then

```text
E_G q_(K,r,G)(t)
  = E_Omega E_R q_(K,r,Omega)(t R).                         (8)
```

The same identity holds after any return removal whose radial section is transported by
`s=tR`.  Equation `(8)` is an exact bridge from a Gaussian ordinary local-Hamiltonian ensemble to
a positive radial mixture of fixed-shell temporal incidence actions.  No random-matrix, spectral
gap, independence of eigenvalues, or late-time limit is used.

## Dependency-closed proof

### Factorial causal boundary

The degree-`K` exponential Taylor vector

```text
tau_K(t) = sum_(j=0)^K (-i t)^j H^j psi_0 / j!
```

lies in `K_K`.  Taylor's integral remainder on the real segment and `||H||<=B` give

```text
||psi(t)-tau_K(t)|| <= (B|t|)^(K+1)/(K+1)!.
```

Orthogonal projection is the best approximation, hence

```text
||psi(t)-phi_K(t)|| <= eta_K(T).                            (9)
```

Since both vectors have norm at most one, tensor telescoping gives

```text
||psi(t)^(tensor r)-phi_K(t)^(tensor r)||
 <= r eta_K(T).                                            (10)
```

For any orthogonal projector `Q` and unit-bounded `u,v`, the reverse triangle inequality gives

```text
| ||Q u||^2-||Q v||^2 |
 = | ||Q u||-||Q v|| | (||Q u||+||Q v||)
 <= 2 ||u-v||.                                             (11)
```

Applying `(11)` to `Q=Proj_(S_r(Z))` and `(10)` changes the original incidence action by at most
`2r eta_K(T)`.

### Projection before the complete target union

Let `C=K_K^(tensor r)` and `P_C=P_K^(tensor r)`.  Because

```text
P_C z^(tensor r) = (P_K z)^(tensor r),
```

we have `P_C S_r(Z)=S_(K,r)(Z)`, proving `(2)`.  If `y=phi_K(t)^(tensor r)`, then `y in C`.
For every `s in S_r(Z)`,

```text
||y-P_C s|| = ||P_C(y-s)|| <= ||y-s||.
```

Taking infima shows

```text
dist(y,S_(K,r)(Z)) <= dist(y,S_r(Z)),
```

and hence

```text
||Proj_(S_r(Z)) y||^2 <= ||Proj_(S_(K,r)(Z)) y||^2.        (12)
```

Combining `(10)--(12)` proves `(1)`.  The first cap in `(3)` is rank contraction under the linear
map `P_C`.  The second follows because `S_(K,r)(Z)` lies in `Sym^r(K_K)`, whose dimension is the
displayed binomial coefficient.

### Complete capture, return removal, and fibre sheets

Suppose `x in E_a` and choose its witnessing target `z`.  By `(9)`,

```text
|<phi_K(tau(x)),P_K z>|
 = |<phi_K(tau(x)),z>|
 >= sqrt(a)-eta_K(T).                                      (13)
```

The vector `(P_K z)^(tensor r)` belongs to `S_(K,r)(Z)` and has norm at most one.  Cauchy--Schwarz
against the orthogonal projection therefore turns `(13)` into

```text
1_(E_a)(x) (sqrt(a)-eta_K(T))^(2r)
 <= q_(K,r)(tau(x)).                                       (14)
```

Integrate `(14)` on `R^c` and use `E_a subset R union (E_a intersect R^c)` to obtain `(4)`.
Alternatively, combine the already proved pointwise complete-incidence inequality
`1_(E_a)a^r<=q_r` with `(1)` to obtain `(5)`.  No source point is identified with another, so all
coarea fibre sheets remain in the integrals.  Return mass has coefficient one.

### Radial factorization

Linearity gives `H(c x)^j=c^j H(x)^j`.  For `c ne 0`, multiplication of each spanning vector by
the nonzero scalar `c^j` leaves its span unchanged, proving `(6)`.  Functional calculus gives
`exp(-itH(c x))=exp(-i(ct)H(x))`; the remaining identities in `(7)` follow.  Standard Gaussian
polar decomposition and Tonelli's theorem applied to the nonnegative action give `(8)`.

## Conjecturing protocol and route audit

### C0 -- contract the full signed occupied-incidence packet

**Verdict:** `[REJECTED AS UNDERDEFINED / POTENTIALLY CIRCULAR]`.

Before a quotient norm and selector are fixed, “packet contraction” can rename the desired
shortcut bound.  Stepwise return killing is also false because return projection does not commute
with replica convolution.

**Positive survivor:** first isolate a canonical causal subspace without touching return or target
selection.

### C1 -- compare every target moment after Krylov projection

**Verdict:** `[TRUE BUT INSUFFICIENT]`.

For one target, power Lipschitz continuity gives a factorial `O(r eta_K)` error.  Summing this error
over a circuit dictionary reintroduces target entropy and destroys the Brown-scale estimate.

**Positive survivor:** project the orbit before the Veronese lift and apply one occupied-image
projector to the complete union.

### C2 -- causal projection commutes with complete replica incidence

**Verdict:** `[PAPER-PROVED]` by `(1)--(5)`.

The factorial error is paid once, independent of target count, occupied-image rank, and source
fibre multiplicity.  This is stronger than targetwise carrier-load bounds and gives an intrinsic,
positive replacement for the unresolved signed packet norm outside the carrier.

### C3 -- small causal rank alone forces anti-concentration

**Verdict:** `[FALSIFIED; EXACT LIMIT IDENTIFIED]`.

Take one target parallel to `phi_K(t_0)` at a nonreturn time.  Then `h_(K,Z)(r)=1` but
`q_(K,r)(t_0)=||phi_K(t_0)||^(2r)`, which is near one when the factorial error is small.  Neither
Krylov dimension nor projected Hilbert rank alone can prove complexity.

**Positive survivor:** the missing variable is the quenched angle/action between the actual
Krylov orbit vector and the projected occupied shallow-circuit image.

### C4 -- radial disorder changes the causal image

**Verdict:** `[FALSIFIED BY EXACT RIGIDITY]`.

Equations `(6)--(8)` show that radial scaling changes only the clock along a fixed causal incidence
geometry.  Radial randomness cannot manufacture new carrier directions.

**Positive survivor:** disintegrate Gaussian disorder into one fixed-shell angular incidence law
and one radial time mixture.

### C5 -- radial Fourier decay alone closes Brown growth

**Verdict:** `[FALSIFIED AS A COMPLETE MECHANISM]`.

The action in `(8)` is nonnegative, exact returns survive, and growing-replica spectral actions
crowd near zero.  A worst-gap or one-dimensional Riemann--Lebesgue estimate cannot survive through
`r=Theta(dim mathcal H)`.

**Positive survivor / former sufficient core:** prove a quenched growing-replica upper bound for

```text
integral_(R^c) q_(K,r)(t) dmu(t)                            (15)
```

for the ordinary fixed-strength local shell, with `K` scale-matched to `BT`, after the complete
shallow-circuit image has been projected into the same random Krylov flag.  This one positive
quantity retains occupied endpoint image and every source sheet, charges recurrence once, and has
no exterior Taylor, targetwise-union, raw-pseudodeterminant, or minimum-gap defect.

### C6 -- full projected-span action is the minimal source-aware invariant

**Verdict:** `[FALSIFIED AS MINIMAL; STRICTLY SHARPENED]`.

The paper-proved `bures-incidence-minimax-coarea-law.md` replaces `(15)` on every fixed-carrier
source fibre by

```text
max {F(C_(K,r,R),M)^2 :
     M in closedConv{|v_(K,r)(z)><v_(K,r)(z)| : z in Z}},   (15')
```

where `C_(K,r,R)` is the return-restricted covariance of
`phi_K(t)^(tensor r)`.  The complete capture mass is bounded by `(15')` divided by the projected
replica threshold.  Fidelity Cauchy--Schwarz proves `(15') <= integral_(R^c)q_(K,r)(t)dmu(t)`, and
deterministic anisotropic examples make the inequality arbitrarily strict.

**New exact open core:** prove Bures separation of conditional quenched orbit covariance from every
convex mixture of actual occupied projected circuit rays.  For an ensemble in which `P_K(H)`
varies with `H`, first disintegrate by a context that makes the carrier fixed; it is invalid to
average variable projected target bodies as though they were one set.  The ordinary ensemble may
instead use the unprojected seed-conditional covariance, as frozen in
`../1-in-progress/quenched-krylov-circuit-incidence-front-law.md`.

## Quantitative consequence for the remaining core

The factorial boundary is no longer part of the hard problem.  The elementary factorial estimate

```text
eta_K(T) <= (e B T/(K+1))^(K+1)
```

shows that if `K+1 >= exp(1+delta) B T`, then

```text
2 r eta_K(T) <= 2 r exp(-delta(K+1)).                       (16)
```

Thus any desired exponentially small replica error can be obtained by a linear enlargement of the
causal order.  What remains in `(15)` is the true finite-time local-Hamiltonian geometry, not a
Taylor remainder.

## External-priority and hostile audit

- Krylov approximation, tensor telescoping, Gaussian polar decomposition, and optimal-design/
  Hilbert-span incidence are individually classical or already present in the corpus.  Novelty is
  claimed only for their exact composition in `(1)--(8)` and the resulting identification of
  `(15)` as the sole carrier core.  A focused external priority audit is still required before
  publication use.
- Ippoliti's 2026 theorem proves a connected spectral-form-factor ramp in an engineered static
  local Hamiltonian sector; it does not control a complete state-circuit incidence action.
- Current temporal-design results use three Hamiltonian quenches, or two Hamiltonians plus a random
  Pauli operation.  They do not prove `(15)` for one fixed generator.
- Existing fresh-random-circuit complexity lower bounds do not transfer to powers of one static
  Hamiltonian.
- Lv--Zhang--Zhou (2023) derive a notion of Krylov complexity from circuit-complexity geometry in
  symmetry-restricted operator dynamics.  They do not give a return-excised complete target-union
  bound, a projected occupied-image Hilbert law, or the radial rigidity `(6)--(8)`.
- The theorem does **not** prove Brown--Susskind growth.  It proves that exterior replica packets,
  target enumeration, return overcounting, fibre-sheet loss, and radial/Krylov mixing are no longer
  legitimate explanations for the gap.
- Causal projection can increase the projection action by collapsing endpoints that differ only
  outside the carrier.  Inequality `(1)` is safe but not automatically small; quantitative progress
  requires controlling the projected action itself.
- A hostile reviewer can still reject any master-paper growth claim until `(15)` is bounded at
  growing `K,r` for an ordinary local ensemble strongly enough to beat projected circuit-image
  entropy.

## References used only to delimit the frontier

- M. Ippoliti, *Provable random-matrix spectral ramp in a static, geometrically local
  Hamiltonian*, arXiv:2606.30635 (2026).
- Y.-N. Zhou, T.-G. Zhou, J. Sonner, *Three Hamiltonians are Sufficient for Unitary k-Design in
  Temporal Ensemble*, arXiv:2604.04205 (2026).
- N. Sun, P. Zhang, *Unitary Designs from Two Chaotic Hamiltonians and a Random Pauli Operation*,
  arXiv:2604.10122 (2026).
- C. Lv, R. Zhang, Q. Zhou, *Building Krylov complexity from circuit complexity*,
  arXiv:2303.07343 (2023).

## Pipeline

- [x] Stage 1 -> 2: dependency-closed proof
- [x] Stage 2 -> 3: exact theorem family is kernel-checked in
  `GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw`
- [ ] Stage 2 -> 4: only after `(15)` is closed and external priority is established

## Lean formalization audit (2026-08-09)

The module proves the card's complete dependency-closed theorem set, without card-specific axioms
or hypotheses beyond the mathematical objects quantified in the paper statement:

- exact factorial Taylor and Krylov projection bounds:
  `norm_boundedHamiltonianOrbit_sub_krylovProjection_le_boundary`;
- projection-before-replica incidence inequality:
  `replicaTargetProjectionMass_boundedHamiltonianOrbit_le_krylov`;
- exact projected target span identity (imported from `ReplicaProjectionIncidenceLaw`) and the sharp
  minimum rank cap: `finrank_projectedReplicaTargetSpan_le_krylov_min`;
- return-excised additive and explicit-error laws:
  `measureReal_boundedHamiltonian_capture_le_return_add_krylovMoment` and
  `measureReal_boundedHamiltonian_capture_le_return_add_krylovMoment_error`;
- radial invariance of Krylov carrier, projected targets, and incidence action:
  `boundedHamiltonianKrylovSubspace_smul`,
  `projectedReplicaTarget_krylov_real_smul`, and
  `realLinearHamiltonianKrylovIncidenceAction_smul`;
- Gaussian polar-product and radial-mixture identities:
  `integral_stdGaussian_realLinearHamiltonianKrylovIncidenceAction_product` and
  `integral_stdGaussian_realLinearHamiltonianKrylovIncidenceAction`.

Verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/KrylovProjectedCompleteIncidenceLaw.lean  # pass
lake build GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw          # pass
#print axioms capstones: [propext, Classical.choice, Quot.sound]
```
