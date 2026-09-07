# CCM-FU: positive harmonic boundary of the actual divisor source

- **Stage:** 3-formalized
- **Type:** unconditional analytic source construction and nonvanishing
- **Source:** [PE5 investigation](../5-failed/ccm-fu-bernoulli-prime-energy.md)
- **Boundary:** the deformed-mean no-go, PE4, SD1 and RH remain open in Lean.

## Exact theorem

For positive integers n, let `b(n)=log(n)-tau(n)+2 gamma` and `D(N)=sum_(n<=N)b(n)`, the literal `primeFreeDivisorIncrement` and `primeFreeDivisorDefect` already in the corpus. The series

`B_1=sum_(n>=1)D(n)/(n(n+1))`

converges absolutely, and `sum_(n<=N)b(n)/n -> B_1`. Its quantitative value satisfies `B_1>=1/30>0`.

The ordinary Dirichlet sum `B(s)=sum_(n>=1)b(n)n^(-s)` converges and is holomorphic on `Re(s)>1/2`. It satisfies `B(1)=B_1`. On `Re(s)>3/2`, it is absolutely convergent and equals mathlib's `LSeries` of the same literal coefficient function. This is a proved source identity, not an identification with an unrelated continuation.

## Source proof

The existing bound `|D(n)|<=24 sqrt(n)` controls the absolute harmonic series by a convergent power series. Set `A(n)=sum_(k<=n)D(k)` and `w(n)=1/(n(n+1))`. The existing all-cutoff theorem gives `A(n)>=0`. A second exact Abel summation gives

`sum_(n<=N)D(n)w(n)=sum_(n<=N)A(n)(w(n)-w(n+1))+A(N)w(N+1)`.

Every displayed contribution is nonnegative. The term at n=1 is `D(1)/3`; a symbolic harmonic estimate for Euler's constant gives `D(1)>=1/10`. Passing to the limit proves the stated floor. The exact first Abel identity is

`sum_(n<=N)b(n)/n=sum_(n<=N)D(n)w(n)+D(N)/(N+1)`.

Its terminal term tends to zero by the square-root bound. Thus the positive boundary belongs to the original source.

The corpus's polynomial Abel theorem applies directly to the exact partial sums of `b(n+1)`. Choosing a convergence point between `1/2` and any given real part proves holomorphy on the whole strict half-plane. The existing width-one absolute-convergence theorem and indexing bridge identify the continuation with `LSeries` on `Re(s)>3/2`.

## Lean certificate

`DivisorSourceHarmonicBoundary.lean` contains eight public theorems. Principal results: `summable_divisorHarmonicBoundaryTerm`, `one_thirtieth_le_divisorHarmonicBoundary`, `sum_primeFreeDivisorIncrement_div_eq`, and `tendsto_sum_primeFreeDivisorIncrement_div`.

`DivisorSourceDirichlet.lean` contains twelve public theorems. Principal results: `divisorSourceDirichlet_converges`, `analyticOnNhd_divisorSourceDirichlet`, `divisorSourceDirichlet_one`, `divisorSourceDirichlet_one_ne_zero`, `LSeriesSummable_primeFreeDivisorIncrement`, and `divisorSourceDirichlet_eq_LSeries`.

Both leaves passed scratch checks and `lake env lean <file> -o <exact olean>`. All twenty new public theorems were axiom-audited once, using only `propext`, `Classical.choice`, and `Quot.sound`. No added axiom, numerical certificate or unproved source premise enters them. Both imports are wired once into `RHTower.lean`; no umbrella or dependency build was run.

Global formal lint was run once. Its eighteen errors concern concurrent, unwired `HTGeometry.PolynomialODEOddCompact*` modules; neither new source leaf is flagged. The [deformed Euler correction and actual-source simple-zero obstruction](ccm-fu-half-selection-euler-pole-obstruction.md) have a separate formal certificate. The remaining mean-bound-to-continuation transfer can use discrete Abel summation. This certificate itself closes the actual nonvanishing divisor-source factor only.
