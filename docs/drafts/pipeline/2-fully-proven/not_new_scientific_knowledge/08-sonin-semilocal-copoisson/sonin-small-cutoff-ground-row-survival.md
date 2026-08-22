# Small-cutoff survival of the smoothed semilocal ground row

- **ID:** sonin-small-cutoff-ground-row-survival
- **Stage:** 2-fully-proven
- **Type:** THEOREM / BRIDGE (paper)
- **Scientific status:** NOT NEW SCIENTIFIC KNOWLEDGE
- **Source inputs:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2; `semilocal-all-even-jacobi-prolate-residue-tower.md`

## Statement

Let `H_infinity,H_P` be the normalized archimedean and finite semilocal cyclic spectral spaces,
`J_P:H_infinity->H_P` the bounded identity on polynomial functions, and `N_infinity,N_P` their number
operators. Let `P_0^P` be the rank-one orthogonal projection onto the semilocal ground state `p_0^P=1`.
Define on the polynomial core

`T_P=P_0^P(N_PJ_P-J_PN_infinity)(N_infinity+1)^(-1)`.       (1)

Then (1) has a canonical bounded extension

`T_P=-P_0^P J_P N_infinity(N_infinity+1)^(-1)`.             (2)

It is rank one, trace class, and nonzero for every finite nonempty prime set `P`.

Let `Q_(lambda,infinity)` and `Q_(lambda,P)` be the orthogonal projections onto the exact
archimedean and semilocal Sonin spaces. There exists `lambda_0(P)>0` such that for every
`0<lambda<lambda_0(P)`,

`(1-Q_(lambda,P))T_PQ_(lambda,infinity)`                    (3)

is a nonzero rank-one trace-class operator. Thus a canonical number-resolvent smoothing of the
source grading defect genuinely crosses the exact Sonin sector at every sufficiently small cutoff.

## Proof of boundedness and nonvanishing

Since `N_Pp_0^P=0` and `N_P` is self-adjoint,

`P_0^P N_P=0`

on its domain. Hence the first term in (1) vanishes after left projection, giving (2). The operator

`F_infinity=N_infinity(N_infinity+1)^(-1)`

is bounded with norm at most one. Since `J_P` and `P_0^P` are bounded, (2) is a bounded rank-one
operator and therefore trace class.

For the degree-two archimedean polynomial,

`T_Pp_2^infinity=-(2/3)<p_0^P,J_Pp_2^infinity>_P p_0^P`.

The all-even residue theorem gives

`<p_0^P,J_Pp_2^infinity>_P<0`,

so `T_P` is nonzero.

Equivalently, if

`v_P=F_infinity J_P^*p_0^P`,

then `v_P!=0` and

`T_Pf=-<v_P,f>_infinity p_0^P`.                            (4)

## Strong small-cutoff Sonin limit

On the even archimedean physical space let `A_lambda` be multiplication by the indicator of
`[-lambda,lambda]`, let `R_lambda=Fourier^*A_lambda Fourier`, and let

`K_lambda=ker A_lambda intersect ker R_lambda`.

Its orthogonal projection is `Q_(lambda,infinity)`. As `lambda` decreases to zero,

`Q_(lambda,infinity)->1` strongly.                          (5)

Indeed `A_lambda->0` and `R_lambda->0` strongly. Moreover the time--band block
`A_lambda Fourier^* A_lambda` is Hilbert--Schmidt with norm tending to zero, so the angle between
`range A_lambda` and `range R_lambda` stays uniformly away from zero for all sufficiently small
`lambda`. The orthogonal projection onto their sum therefore tends strongly to zero. Its complement
is `Q_(lambda,infinity)`, proving (5).

Applying (5) to the nonzero vector `v_P` gives

`Q_(lambda,infinity)v_P->v_P`.

Thus `Q_(lambda,infinity)v_P!=0` for all sufficiently small positive `lambda`.

The semilocal ground state is the positive semilocal amplification of the Gaussian cyclic vector. It
does not vanish on a neighborhood of the physical origin and hence does not belong to any positive
cutoff Sonin space. Therefore

`(1-Q_(lambda,P))p_0^P!=0`                                 (6)

for every `lambda>0`.

Using (4), the corner (3) is the rank-one operator with output vector
`(1-Q_(lambda,P))p_0^P` and input vector `Q_(lambda,infinity)v_P`. Both are nonzero by (5)--(6),
which proves the claim.

## Cofinal decay

As `lambda` tends to infinity,

`Q_(lambda,infinity)->0` strongly.                          (7)

Indeed the archimedean Sonin space is contained in `ker A_lambda`, so

`0<=Q_(lambda,infinity)<=1-A_lambda`

as orthogonal projections. Since `A_lambda->1` strongly, equation (7) follows. In particular

`Q_(lambda,infinity)v_P->0`.

The trace norm of a rank-one operator is the product of the norms of its output and input vectors.
Using (4),

`||(1-Q_(lambda,P))T_PQ_(lambda,infinity)||_1
 <= ||p_0^P|| ||Q_(lambda,infinity)v_P|| ->0`.              (8)

Thus the same canonical corner that survives every sufficiently small cutoff decays to zero in trace
norm along the cofinal large-cutoff direction.

## Attack and route boundary

- `[PROVED]` Exact Sonin compression does not automatically erase every normalized Jacobi defect:
  the canonical smoothed ground row survives for all sufficiently small cutoffs.
- `[PROVED]` The surviving corner is trace class for the strongest possible reason: it has rank one.
- `[PROVED]` No self-adjoint realization of the formal prolate operator is required for this bridge.
- `[LIMIT]` The smoothing uses the number-operator resolvent, not the prolate resolvent. It does not
  solve the source prolate domain problem.
- `[LIMIT]` The theorem is local at small cutoff. Weil cofinality requires control through arbitrarily
  large support windows.
- `[PROVED LIMIT]` Its trace norm tends to zero as the cutoff tends to infinity. It cannot provide a
  uniform cofinal gap or obstruction by itself.
- `[LIMIT]` After pullback to one Hilbert space the rank-one ground row is strictly filtration-lowering,
  so its ordinary Fredholm determinant remains one. The result supplies survival and trace class, not
  a determinant boundary or RH positivity.

## Novelty audit

The source-specific assembly is useful, but the mechanism is an elementary rank-one projection plus
strong convergence of shrinking-cutoff Sonin projections. It fails the significance half of the
new-knowledge gate and is classified as BRIDGE.
