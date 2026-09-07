# EDQ uniform period averaging: growth obstruction and positive projection

Stage: 1-in-progress. [BRIDGE] dependency-closed paper deduction; Lean validation pending.
Full chain: Euler deletion → exact complex zero balance → signed arithmetic separation → off-line exclusion → RH.

## Claim under attack

Replacing the actual residue-dependent progression weights by uniform averaging
does not produce the polynomial-log upper ceiling required by EDQ. The complete
uniform period variance itself grows faster than every fixed logarithmic power.
This retires only that averaging shortcut, not the weighted EDQ architecture.

## Positive survivor and paper proof

Let V_N be the exact centered period covariance from
EulerDeletionMobiusPeriodCovariance, and U_N the primes p with N/2<p<=N.
Such a prime is coprime to every other positive modulus m<=N: a distinct positive
multiple of p would exceed N. The complete covariance formula therefore makes
each of these channels orthogonal to every other channel. Removing them leaves
the covariance of the remaining actual coefficient vector, which is nonnegative.
The exact decomposition is

    V_N = sum_(p in U_N) (1-1/p^2)/12 + covariance(remaining coefficients).

Since p>=2, each retained diagonal is at least 1/16. Thus V_N>=card(U_N)/16,
at every cutoff, without an asymptotic or zero hypothesis.

The corpus's every-window theta lower bound at exponent 3/4, applied to
y=N/2 and L=N/2, gives theta(N)-theta(N/2)>=N/32768 eventually.
Its prime-shell counting comparison then gives card(U_N)>=N/(32768*log N).
Consequently V_N>=N/(524288*log N) eventually. This exceeds every fixed
logarithmic power and forbids even cofinal polynomial-log upper returns.

The already proved actual weighted carrier energy is o(N/(log N)^q) for every
fixed q. Combining q=1 with this variance lower bound gives

    norm(rawVec_N)^2 / V_N -> 0.

This is a quantitative failure of uniform period averaging as an asymptotically
comparable replacement for the actual carrier energy. The exact signed prime
projection and its nonnegative remainder survive; all progression weights in
the actual carrier remain necessary.

## Scientific-method and closure audit

This statement is a [BRIDGE] forced by a visible source calculation, not a new
primary conjecture. No numerical experiment is warranted: the paper proof
predicts the outcome. Formalize the exact projection and growth statements before
retiring the shortcut. No RH proof, off-line zero, or weighted energy ceiling is
claimed. The original RH objective and its remaining weighted comparison are
unchanged.
