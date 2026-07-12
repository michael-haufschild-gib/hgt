# Von Mangoldt normalized Hankel far-right negativity

- **ID:** `von-mangoldt-normalized-hankel-far-right-negativity`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE]` / source-orientation guardrail
- **Scientific status:** `[NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean file:** `formal/GaloisForLFunctions/RHTower/EulerNormalizedTraceHankelFarRight.lean`

## Statement

Let

\[
A_m(x)=\operatorname{Re}\sum_{n\ge 1}
  \frac{\Lambda(n)(\log n)^m}{n^x}
\]

and form the first factorial-normalized trace-Hankel determinant

\[
D_E(x)=A_1(x)\frac{A_5(x)}{120}
       -\left(\frac{A_3(x)}6\right)^2.
\]

Then

\[
2^{2x}D_E(x)\longrightarrow
-\frac{7(\log 2)^8}{360}<0
\qquad (x\to+\infty).
\]

Consequently, `D_E(x)<0` for every sufficiently large real `x`.

## Formal declarations

- `vonMangoldtLogCoeff`;
- `tendsto_vonMangoldtLogCoeff_firstPrime`;
- `vonMangoldtLogMoment`;
- `tendsto_scaled_vonMangoldtLogMoment`;
- `vonMangoldtNormalizedFirstHankelDet`;
- `tendsto_scaled_vonMangoldtNormalizedFirstHankelDet`;
- `vonMangoldtNormalizedFirstHankelDet_eventually_neg`.

## Proof

The first nonzero coefficient of every logarithmically weighted von Mangoldt
Dirichlet series occurs at `n=2`.  The general first-coefficient asymptotic for
Dirichlet series therefore gives

\[
2^x A_m(x)\longrightarrow(\log 2)^{m+1}.
\]

Substitution for `m=1,3,5` gives

\[
2^{2x}D_E(x)\longrightarrow
(\log 2)^2\frac{(\log 2)^6}{120}
-\left(\frac{(\log 2)^4}{6}\right)^2
=-\frac{7(\log 2)^8}{360}.
\]

The limit is strictly negative because `log 2>0`; eventual negativity follows
because the scaling factor `2^(2x)` is strictly positive.

## Positive top-down consequence

`PrimeLaplaceGramStrict.lean` proves that the unnormalized resolved Euler
Laplace matrices are strictly positive definite.  The present theorem shows
that factorial trace normalization changes the orientation: the actual
infinite Euler source, not merely a finite model, is forced into the negative
first-Hankel chamber far to the right.

Therefore a completed-source route cannot preserve a positive Euler
trace-Hankel orientation all the way to the central Xi cone.  The positive
research target is an arithmetic crossing theorem:

```text
far-right negative Euler factorial-Hankel chamber                         [Lean]
  + completed prime--Gamma incidence producing a forced oriented crossing [OPEN]
  + positive central leading determinants                                 [OPEN RH CORE]
  -> RH.                                                                   [Lean]
```

The missing source theorem must explain how the Gamma, polar, and weighted
all-prime-tail channels change the factorial Hankel geometry.  Parity repair,
generic analytic continuation, and strict Euler Laplace positivity do not
supply that interaction.

## Scientific status

First-coefficient dominance for a Dirichlet series and the resulting `2 x 2`
determinant calculation are elementary.  The result is recorded for exact
route control and as a formal source boundary, not as new scientific
knowledge.

## Gates

- [x] exact theorem statement
- [x] unconditional Lean proof
- [x] no placeholders or project axioms
- [x] imported by the RHTower umbrella
- [x] scientific classification recorded
