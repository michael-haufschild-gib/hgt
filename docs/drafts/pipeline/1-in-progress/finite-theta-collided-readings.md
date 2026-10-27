# Finite theta-source readings of the collided metric

- **ID:** CDG-FINITE-THETA-READINGS
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Conjugate-Diagonal Geometry question 2; common moving theta trace.
- **Count:** Unaccepted; no theorem claimed.

## Proposed construction

Use the actual polynomial-Gaussian summands `thetaCuspSourceTerm` on the
nonnegative half-line. For a finite integer cutoff define

```
g_N(x) = sum_(1<=m<=N) thetaCuspSourceTerm |x| m,
A_N(s) = integral g_N(x) exp((1/2-s)x) dx,
B_N(s) = integral x g_N(x) exp((1/2-s)x) dx.
```

Reflection of the half-line is essential: the unscreened finite-prime
source is not automatically an entire bilateral transform. Its already
proved compact-local convergence does not justify that assertion.

Conjecture: a prescribed cofinal integer cutoff `N_n` and a source-only
regulator `eta_n`, chosen without zero coordinates or an error-minimization
oracle, make

```
pi^-1 integral chi_n(s) |F_f(s-i tau)|^2 k_L(Re(s)-1/2)^j
  eta_n |B_(N_n)(s)|^2 / (|A_(N_n)(s)|^2 + eta_n)^2
```

converge to the full multiplicity-weighted collided moment uniformly in
`|tau|<=n/2`, `j|L|<=2log(n+1)`, for every compact C² test and finite order.
This would replace the infinite theta amplitude in the current formula by
finitely many literal integer summands. It would still not be a selective
positivity theorem or an RH claim.

## Inputs and obligations

The actual definitions and compact-local finite-prime convergence in
`ThetaCusp/ThetaCuspFinitePrimeSource.lean` have been read. That source is a
sum over all smooth integers; it is not the finite integer cutoff above.
The full amplitude and first moment already equal xi and minus its derivative.

Required new work:

1. Verify the exact half-line reflection identity and normalization.
2. Prove uniform complex-disc bounds for both finite-integer amplitude
   errors, including the first moment. Control the unbounded physical
   integral before interchanging limits.
3. Prove a denominator-stable curvature perturbation estimate with its
   explicit powers of `eta`. Multiple zeros must be allowed.
4. Choose a closed cofinal cutoff making the amplitude error smaller than
   the regulator sensitivity throughout the expanding disc.
5. Combine with a checked regulator formula and the moving-tail theorem;
   audit the final transitive dependencies.

## Novelty gate

Finite entire approximants and Poincaré–Lelong regularization are already
known mechanisms. Acceptance requires the complete arithmetic construction
and a demonstrated advance over existing theta/Taylor divisor recovery.
No claim is made that the finite amplitudes have only critical-line zeros.
Positive source kernels and positive curvature alone do not prove that.

## Candidate cutoff mechanism

If the prescribed regulator conjecture succeeds with `eta_n=exp(-K_n)`,
a finite-integer tail of size `exp(-c N^2)` on the relevant complex disc
would dominate the curvature denominator sensitivity `eta_n^-q` for every
fixed q by taking a closed cutoff of order `ceil(K_n)+n+constant`.
The half-line theta summands have Gaussian integer tails; their integrated
amplitude and first-moment tails still need a proved uniform estimate with
all dependence on the disc radius exposed. No such bound is assumed here.

The finite reflected source may have a cusp at zero; analyticity of its
bilateral amplitude follows from integrable exponential moments, not from
smoothness of the reflected physical source. Its zeros need no critical-line
or simplicity property. The proposed value is a full positive trace formula
from finite literal arithmetic input without zero-free contour admission;
novelty must still be checked against existing finite-source divisor recovery.

## Relative tail mechanism from the actual corpus

The existing `thetaCuspSourceTerm_le_first` in
`RHTower/PrimeArchThetaSourceAtomDomination.lean` gives, for `x>=0` and `m>=1`,

```
0 <= thetaCuspSourceTerm x m
  <= 2 m^4 exp(-pi(m^2-1)) thetaCuspSourceTerm x 1.
```

Its exact proof and the summable domination weights have been read. Use the
existing `thetaCuspFiniteShellPrefix N` for the finite sum; reflect it by
`x -> |x|`. The exact evenness of the completed source follows from
`thetaCuspFullSource_neg`. The finite prefix itself is not even: the existing
`thetaCuspFiniteShellPrefix_boundary_derivative_pos` proves its positive seam
slope. Reflection is therefore an actual change to the finite construction.

Put `C_tail = 2 exp(pi) sum_m m^4 exp(-(pi-1)m^2)`, a finite positive constant.
For `m>N`, extracting `exp(-N^2)` from the domination weight gives

```
0 <= thetaCuspFullSource x - thetaCuspFiniteShellPrefix N x
  <= C_tail exp(-N^2) thetaCuspSourceTerm x 1
  <= C_tail exp(-N^2) thetaCuspFullSource x  (x>=0).
```

Evenness then gives the same relative estimate for the reflected finite
source on the whole real line. This avoids any exchange of an uncontrolled
infinite physical tail. The full source already has exponential moments of
all orders. For `|s|<=R`, the amplitude error is bounded by the relative
factor times `integral k(x) exp((R+1/2)|x|) dx`; the first-moment error uses
`|x|<=exp(|x|)` and the same integral with exponent `R+3/2`.
Their radius dependence can be bounded through the actual xi growth theorem
and the bilateral theta transform. Those exact quantitative bounds are still
proof obligations, not inputs.

For positive eta, an elementary denominator comparison gives the tentative
curvature stability estimate

```
|eta |B|^2/(|A|^2+eta)^2 - eta |B'|^2/(|A'|^2+eta)^2|
 <= | |B|^2-|B'|^2 |/eta
    + 2 |B'|^2 | |A|^2-|A'|^2 |/eta^2.
```

A prescribed integer cutoff at least `ceil(K_n)+n+10` makes the Gaussian
integer tail dominate the factor `exp(2K_n)`. The complete uniform integral
estimate and its Lean proof remain open. No part of this mechanism is counted
separately as a contribution.


A second route may simplify curvature stability: compare the two regularized
logarithmic potentials and apply the existing compact Green identity. The
scalar bound `|log u-log v| <= |u-v|/eta` for `u,v>=eta>0` needs only amplitude
approximation; derivative approximation is then needed only to identify the
finite amplitude's curvature with its literal first source moment. The
existing `ThetaSource` bilateral-Laplace theorem in `ThetaTiltFluxCarrier.lean`
already proves that derivative identity from positive, continuous, even,
superexponentially decaying sources. Each nonempty reflected finite prefix
should satisfy those conditions by the actual completed-source domination.
Every field must be proved for that prefix; none will be assumed at the endpoint.


The source envelope is stronger than the initially proposed xi-growth bridge.
`ThetaCuspTiltFluxSourceWeld.lean` proves the literal global inequality

```
k(x) <= U exp((|M|+5)^2/24) exp(-M|x|)
```

with fixed explicit `U=thetaEnvelopeUpper>0`, for every real M. Taking
`M=R+5/2` controls both amplitude and first-moment integrands on `|s|<=R`
by a fixed multiple of `exp((R+15/2)^2/24) exp(-|x|)`. Together with the
relative integer-tail bound this gives a direct arithmetic target
`delta_(N,R) <= C exp(-N^2+(R+15/2)^2/24)` without a canonical zero radius.
The exact envelope and its actual `ThetaSource` instance were read. The
relative-tail and finite-carrier proofs are written in scratch, unchecked.


## Closed finite cutoff and potential comparison

A dependency-closed paper route now uses the source envelope directly. Write
`J=integral exp(-|x|) dx`, `H_R=J U exp((R+15/2)^2/24)` for `R>=0`.
The same envelope, with `|x|<=exp(|x|)`, bounds amplitude and first moment by
`H_R`; the finite prefix is pointwise between zero and the full source.
The relative tail gives amplitude error at most `C_tail H_R exp(-N^2)`
for a prefix through N. All integrations are dominated by the integrable
function `exp(-|x|)`.

For any complex a,b and eta>0,

```
|0.5 log(|a|^2+eta)-0.5 log(|b|^2+eta)|
 <= (|a|+|b|)|a-b|/(2eta).
```

This follows from `|log u-log v|<=|u-v|/eta` for `u,v>=eta` and the reverse
triangle inequality. Thus the potential difference between finite and full
amplitudes is at most `C_tail H_R^2 exp(K_n-N^2)` at eta=exp(-K_n).

Choose the literal prefix cutoff `N_n=ceil(K_n)+n+10`; using an index N+1
for the nonempty `ThetaSource` constructor only strengthens this estimate.
For `R=n+2`, `(R+15/2)^2/12 <= (n+10)^2`, while
`N_n^2 >= K_n^2+(n+10)^2`. Also `M_n<=K_n<=exp(K_n)`, so

```
M_n C_tail H_(n+2)^2 exp(K_n-N_n^2)
 <= C_tail (J U)^2 exp(2K_n-K_n^2)
 <= C_tail (J U)^2 exp(-(n+1)^4),   n>=1.
```

The last step follows from `K_n>=exp((n+1)^4)>=(n+1)^4+1` and
`(n+1)^4>=16`. No bound on cutoff derivative growth is assumed.
Multiplication by the disc area and addition of the checked full-xi
regularization error preserves a polynomial-times-quartic-exponential local
error. Since `(n+2)^2<=4(n+1)^6`, this can be absorbed by increasing the
constant in the existing local-error shape. Compact Green testing then
provides the finite-source current error; the existing moving-square and
arithmetic-tail bounds supply the full moving collided trace.

The generic scalar comparison, exact finite source transform estimates,
positive curvature identity, and final assembly have not yet passed Lean.
The potential comparison route is preferred to a direct ratio perturbation
because it preserves the existing Laplacian estimate and needs no derivative
error estimate. The first moment remains explicit through the proved entire
bilateral-transform derivative theorem.
