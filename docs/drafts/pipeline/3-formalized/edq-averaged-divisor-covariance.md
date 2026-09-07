# EDQ averaged divisor source and cumulative covariance

Stage: 3-formalized. Derived [BRIDGE]; RH remains the primary objective.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.
Objective: connect the averaged source to the corpus's arithmetic mean-square estimates without losing its compensator or cumulative cross terms.

## Corpus evidence

`EulerDeletionCutoffAverage` identifies the tapered source and supplies an
adaptive outer-cutoff current criterion in the preserved inner scale.
`Sieve.BarbanVehovWeight` identifies the divisor coefficient with von Mangoldt
on its full support, except for its explicit unit coefficient.
`Sieve.GrahamMeanSquare` bounds the sum of coefficient squares by
`C*N*(1+log M)+(M*log M)^2`; `BarbanVehovSharpSummatory` retains the exact
lcm main term and floor-removal error. `MollifiedDeviationHeadVariance` already
identifies the head of a single normalized linear mollifier. None of these
inspected statements is an estimate for the complete averaged primitive.

## Closed exact statements

Write L=log M-log X, w_Y(d)=mu(d)*log(Y/d) for d<=Y and zero otherwise,
and b_Y(k)=sum_(d divides k) w_Y(d). For 1<=X<M, the averaged coefficient is
`a(d)=(w_M(d)-w_X(d))/L` at every positive d, with zero beyond M.
Thus its divisor coefficient is `g(k)=(b_M(k)-b_X(k))/L`.
For 1<k<=M this is `(Lambda(k)-b_X(k))/L`; at k=1 it is one.
For 1<k<=X it is zero.

The literal modular vector has the exact global formula
`F(n)=sum_(1<=k<=n) g(k)-n*H`, where H is the same averaged harmonic
compensation already fixed by the source. No term is removed for n>M.
Its error is the cumulative sum of `c(k)=[k=1]-g(k)+H`.

For any real sequence c and finite T, exact summation reversal gives
`sum_(n=1..T) (sum_(j=1..n)c(j))^2/[n(n+1)]`
`=sum_(j,k=1..T)c(j)c(k)*(1/max(j,k)-1/(T+1))`.
The diagonal is explicit; every temporal cross term remains. This positive
cumulative form is the actual finite primitive/error energy, whereas an
ordinary coefficient mean-square controls its diagonal input only.
The identity alone does not supply a subpower upper bound or justify dropping
the complementary infinite tail.

## Scientific controls and status

These statements follow by finite algebra from inspected corpus identities;
their numerical outcomes are predictable, so no computation is warranted.
No route is retired. The intended positive result is an exact source and
covariance representation suitable for assessing arithmetic estimates.
`EulerDeletionAveragedDivisorCovariance.lean`, namespace
`RHTower.DeletionAveragedDivisor`, proves all of these source identities.
The full floor/divisor identity holds at every coordinate, not only below M.
The modular/cumulative identities require only X<=M, whereas the normalized
Barban–Vehov difference uses 1<=X<M.

`sum_sq_divisorSource_le` applies the actual corpus Graham bound to both
endpoints. With `B(Y,N)=N*4*C^2*(1+log Y)+(Y*log Y)^2`, it proves
`sum_(k<=N)g(k)^2<=2*(B(M,N)+B(X,N))/L^2` for N>=M.
This retains the explicit floor-removal costs. It is an input coefficient
estimate; no subpower bound on cumulative covariance follows here.

The entire averaged modular sequence is bounded by M. Its full error is
therefore genuinely square summable at every fixed pair of cutoffs.
`fullErrorEnergy_eq_covariance_add_tail` identifies that complete energy with
the finite covariance above plus the literal error tail on coordinates >T.
No infinite double-sum exchange or discarded tail is used.

## Validation

The complete scratch passed `lake env lean` without diagnostics. The module
contains fourteen public theorems, six definitions, and five private helpers.
The targeted `lake build --old GaloisForLFunctions.RHTower.EulerDeletionAveragedDivisorCovariance`
built only this leaf in 7.3 seconds; all dependencies were cached. The module
is wired once into `RHTower.lean`; no full or umbrella build was run.
All twenty new public declarations passed one temporary `lake env lean`
axiom audit; each depends exactly on `propext`, `Classical.choice`, and
`Quot.sound`. No added axiom, admission, or numerical certificate is used.
The search index was refreshed once. Scoped source, axiom coverage, unique
umbrella import, whitespace, documentation-link and stage checks passed.
All owned Lean processes exited and temporary Lean sources were removed;
logs remain under `/tmp/edq_covariance.*.log`.

Repository lint was run once and reported three concurrent unrelated modules
unreachable from their umbrella: `ProductAFEContour`, `ProductAFEIntegrand`,
and `RectangleThreePoleResidue`. They remained untracked and unwired at the
subsequent inspection. This EDQ module was correctly wired and produced no
lint error. No global lint pass is claimed and those concurrent files were
not modified.

## Remaining mathematical producer

Prove a full compensated covariance bound that controls the averaged current
in the preserved inner scale. The source now has an exact prime/divisor
representation and a verified coefficient-square donor. A transfer retaining
temporal cross terms and the complete tail is still needed. Neither the
finite representation nor the donor proves the required subpower bound.
No route is retired and RH remains open.
