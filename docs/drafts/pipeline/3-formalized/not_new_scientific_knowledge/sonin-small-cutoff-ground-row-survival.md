# Small-cutoff survival of the smoothed semilocal ground row

- **ID:** sonin-small-cutoff-ground-row-survival
- **Stage:** 3-formalized / needs independent audit
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

## Lean formalization

All statements are unconditional and closed.  The two archimedean strong limits `(5)` and `(7)` are
proved on the concrete model `SoninL2 = L^2(R)` with the actual cutoff and Fourier-cutoff
projections; the rank-one algebra of `(1)`-`(4)`, `(6)` and `(8)` is proved for arbitrary Hilbert
spaces, so it applies verbatim to any unitary copy of the archimedean space, in particular to the
Jacobi coefficient model in which the semilocal moments live.

The one place where the card *assumes* rather than proves is the boundedness of `J_P`, which it
takes from the source construction.  In the Jacobi model that datum is exactly the
square-summability of the ground-row coefficients `(2k/(2k+1)) <p_0^P, J_P p_{2k}^inf>`.  For a
single prime it is **discharged** from the corpus's sharp order `k^{-3/4}`; for a general finite
prime family it is carried as the explicit summability hypothesis, and the nonvanishing conclusion
is proved for every finite nonempty family.

| Paper item | Lean declaration | Module |
|---|---|---|
| the Sonin carrier is the orthogonal complement of the two forbidden spans | `centralSoninCarrier_eq_sup_orthogonal`, `centralSoninProjection_eq_supOrthogonal` | `RHTower.SoninSmallCutoffGroundRow` |
| the time-band angle: `norm of the forbidden block <= 2a` | `norm_centralForbidden_block_le` | `RHTower.SoninSmallCutoffGroundRow` |
| Friedrichs deficiency of the intersection projection | `norm_sub_intersectionProjection_sq_le`, `angle_of_norm_starProjection_mul_le` | `HTGeometry.TwoProjectionDeficiency` |
| deficiency of the Sonin projection at small aperture | `norm_sub_centralSoninProjection_sq_le` | `RHTower.SoninSmallCutoffGroundRow` |
| shrinking-window `L^2` mass vanishes, physical and Fourier | `tendsto_norm_indicatorCutoff_of_tendsto_zero`, `tendsto_norm_fourierCutoff_of_tendsto_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| `(5)` `Q_{lambda,inf} -> 1` strongly as `lambda` decreases to zero | `tendsto_norm_sub_centralSoninProjection_of_tendsto_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| `(7)` `Q_{lambda,inf} -> 0` strongly as `lambda` tends to infinity | `norm_centralSoninProjection_le`, `tendsto_norm_centralSoninProjection_atTop` | `RHTower.SoninSmallCutoffGroundRow` |
| `(4)` the smoothed ground row `T f = -<v,f> p_0` | `groundRow`, `groundRow_apply`, `groundRow_eq_rankOne` | `RHTower.SoninSmallCutoffGroundRow` |
| `(1) => (2)`: `P_0^P N_P = 0` | `groundProjection_numberOperator_eq_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| `T_P` is rank one with norm the product of the two vector norms | `norm_groundRow`, `groundRow_ne_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| `(3)` the exact Sonin corner is again a ground row | `corner_eq`, `norm_corner`, `corner_ne_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| `T_P` and its Sonin corners are trace class | `onePrimeGroundRow_isTraceClass`, `groundRow_corner_isTraceClass` | `RHTower.SoninSmallCutoffGroundRow` |
| one-prime `v_P` and its nonvanishing | `onePrimeGroundRowVector`, `semilocalOnePrimeGroundCommutatorRow_one_ne_zero`, `onePrimeGroundRowVector_ne_zero`, `onePrimeGroundRow_ne_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| finite-prime `v_P` and its nonvanishing for every nonempty family | `finitePrimeGroundRowCoefficient`, `finitePrimeGroundRowVector`, `finitePrimeGroundRowVector_ne_zero`, `finitePrimeGroundRow_ne_zero` | `RHTower.SoninSmallCutoffGroundRow` |
| the all-even ground residue that makes `T_P` nonzero | `semilocalFinitePrimeEvenJacobiMoment_signed_pos` | `RHTower.SoninSemilocalAllEvenJacobiResidue` |
| `(3)` + `(8)` the card's theorem | `smallCutoff_groundRow_survival` | `RHTower.SoninSmallCutoffGroundRow` |

Axiom audit: every declaration above depends only on `propext`, `Classical.choice`, `Quot.sound`.
