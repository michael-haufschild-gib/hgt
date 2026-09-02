# Dyadic subunit quadratic-index rigidity

- **ID:** `ULF-DQIR-1`
- **Stage:** 2-fully-proven
- **Type:** unconditional analytic-arithmetic rigidity law
- **Status:** dependency-closed paper proof; Lean-certified in
  `GaloisForLFunctions.RHTower.DyadicQuadraticGhostIndexRigidity`

## Statement

For `a in R` with `|a|<1`, set

`Q_2(a)=(2^a-1)(2^-a-1)=-2(cosh(a log 2)-1)`.

Then

`-1<Q_2(a)<=0`,

and

`Q_2(a) in Z  <->  a=0`.

For an actual Xi divisor copy `rho`, the one-copy dyadic quadratic Gamma ghost is integral iff
`Re(rho)=1/2`.

## Proof

Since `log 2>0` and `|a|<1`,

`|a log 2|<log 2`.

Strict monotonicity of `cosh` in absolute value gives

`cosh(a log 2)<cosh(log 2)=(2+1/2)/2=5/4`.

Also `cosh x>=1`. Therefore

`-1/2<Q_2(a)<=0`,

which implies the stated weaker lower bound `-1<Q_2(a)`. If `Q_2(a)` is an integer, no integer
lies in `(-1,0)`; hence `Q_2(a)=0`. Thus `cosh(a log 2)=1`, so `a log 2=0`, and `a=0`. The converse
is immediate.

For Xi, put `a=2 Re(rho)-1`. The standard open critical strip gives `|a|<1`, and `a=0` is exactly
`Re(rho)=1/2`.

## Sharp boundary

1. The interval is open. At `|a|=1`, `Q_2(a)=-1/2`.
2. Total multiplicity cannot replace one-copy integrality. For any integer `m>=3`, continuity and
   strict monotonicity of `-Q_2(a)` on `[0,1)` produce nonzero `a` with
   `m Q_2(a)=-1`. Hence a total divisor index can be integral off line.
3. Dyadic aperture is canonical for this integer-gap argument. For `p>=3`,
   `Q_p(a)` approaches `2-p-p^-1<=-4/3` as `a` approaches `1`; its strip image crosses negative
   integers, so one-copy integrality alone need not force zero.

## Corpus consequence

The existing full integral Laurent producer already supplies the analytic value. Remaining burden
is not to discover another scalar or prove positivity. It is to produce an ordinary integral index
for one canonical local-length layer whose analytic fixed-point formula equals this value. If that
source-native index transgression exists, one prime and one quadratic ghost close RH.

## Dependency audit

- `cosh` monotonicity in absolute value and `cosh(log 2)=5/4`.
- Exact corpus identity between the Laurent Hermitian square evaluation and
  `-2(cosh(a)-1)`.
- Standard Xi open-strip theorem for the pointwise corollary.
- No RH, numerical approximation, added axiom, positivity hypothesis, or index-existence premise.
