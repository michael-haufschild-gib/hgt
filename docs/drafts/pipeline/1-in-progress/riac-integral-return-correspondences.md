# Integral return correspondences

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [RIAC](renormalized-intersection-arithmetic-counts.md)

## Arithmetic construction to test

For a finite set `P` of rational primes, construct the actual integral order

`R_P = ⊗_(p∈P) ℤ[x_p]/(x_p²−p)`.

Its squarefree monomial basis gives ordinary multiplication by `x_p` the
return law `T_p²=p·id`. The real embeddings should give the trace pairing
`Tr(x_S x_T)=2^|P| [S=T] ∏_(p∈S)p`. This supplies the return term missing
from the nilpotent conductor quotient, but the metric identity alone is
not an arithmetic count or the missing height estimate.

Required output: actual finite quotient counts, their prime-local
multiplicities and archimedean product formula, plus an exact comparison
with the original signed gluing functional. Any proposed height must
explain whether its scaling is quadratic under the relevant addition law.

## Source comparison

The [formalized conductor quotient](../3-formalized/riac-hecke-stable-arithmetic-sections.md)
has `T_p²=0`. The proposed return operator is therefore a different action;
its arithmetic comparison cannot identify all conductor moments unchanged.

The local calculation to formalize uses `C(a+b x_p)=a−b`:

`C(x_p^(2k))=p^k`, `C(x_p^(2k+1))=−p^k`.

Its formal generating factor is `(1−t)/(1−p t²)`. Recovering the Möbius
factor requires the counterterm `1−p t²`. Globally the predicted return
coefficients are `μ*w`, with `w(d²)=d` and `w(n)=0` off squares; the
counterterm is supported on squares with coefficient `d μ(d)` at `d²`.
These are candidate comparison identities, not accepted Lean results.
An estimate for the compensated original gluing class remains necessary.

## Decisive test

Does this independently constructed arithmetic height control
`C(b_N)=1−M(N)` at `N^(1/2+ε)`? The square-root matrix identity and a
positive trace form alone do not answer this. Without such a comparison,
the construction is not a solution of signed local-index cancellation.
