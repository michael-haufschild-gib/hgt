# Real-source microlocal quartet no-go

- **ID:** `real-source-microlocal-quartet-no-go`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** NO-GO / EXACT COUNTERMODEL / POSITIVE OPEN-CORE REDUCTION
- **Scientific status:** `[PAPER-PROVED]` `[NOT RH]`
  `[NO EXTERNAL NOVELTY CLAIM]`
- **Parent:** `../../1-in-progress/prime-incidence-microlocal-reality-law.md`
- **Statement:** A real compactly supported source, real/reflection-symmetric transform, and
  multiplicity-faithful reciprocal acquisition can carry an arbitrary off-line quartet; generic
  microlocal reality does not imply critical-line reality.

## Countermodel

Use centered coordinate \(z=s-\tfrac12\).  For \(a,b>0\), put
\[
  F_{a,b}(z)
  :=
  \bigl((z-a)^2+b^2\bigr)
  \bigl((z+a)^2+b^2\bigr).
  \tag{1}
\]
Then:

1. \(F_{a,b}\) is an even polynomial with real coefficients;
2. \(F_{a,b}(-z)=F_{a,b}(z)\);
3. \(F_{a,b}(\bar z)=\overline{F_{a,b}(z)}\);
4. its four simple zeros are
   \[
     a\pm ib,\qquad -a\pm ib,
     \tag{2}
   \]
   all off the critical axis \(\Re z=0\).

Let the bilateral Laplace transform of a compactly supported distribution be
\[
  {\cal L}T(z):=\langle T(t),e^{-zt}\rangle.
  \tag{3}
\]
For every \(k\ge0\),
\[
  {\cal L}(\delta_0^{(k)})(z)=z^k.
  \tag{4}
\]
Writing \(F_{a,b}(z)=\sum_k c_kz^k\) with real \(c_k\), the real distribution
\[
  T_{a,b}:=\sum_k c_k\delta_0^{(k)}
  \tag{5}
\]
is supported at the single real point \(0\) and satisfies
\[
  {\cal L}T_{a,b}=F_{a,b}.
  \tag{6}
\]
Its reciprocal reporter \(1/F_{a,b}\) has the four off-axis poles `(2)`, with exact
multiplicity.

Thus all of the following can coexist:

```text
real source distribution;
real characteristic support;
Schwarz symmetry;
Riemann-type centered reflection;
entire symmetric completion;
noncensored reciprocal divisor;
off-critical quartet.
```

## Stronger source-reporter form

If \(X(z)\) is any real even completed reporter, then
\[
  \widetilde X(z):=F_{a,b}(z)X(z)
  \tag{7}
\]
is again real and even.  In transform language, `(7)` is obtained by applying the real
finite-order differential operator \(F_{a,b}(\partial)\), up to the fixed transform convention,
to the same real source reporter.  It adds the off-axis quartet without changing the underlying
real line or reflection involution.

Hence even an ordinary-integer reporter does not become critical merely because its transformed
source and microlocal support are real.  A no-surplus or literal prime-incidence condition must
exclude the operation `(7)` for a reason visible before its zeros are read.

## Exact killing mechanism

Real wavefront directions constrain singularities of a linear transform.  Xi zeros are not
singularities of the completed entire reporter.  They become singular only after the nonlinear
operation of inversion or logarithmic differentiation.  Reciprocal acquisition does not preserve
the zero-location restrictions of a real source wavefront.

Therefore this implication is false:
\[
  \text{real source characteristic cycle}
  +\text{reflection}
  +\text{faithful reciprocal acquisition}
  \Longrightarrow
  \text{critical divisor}.
  \tag{8}
\]

## Strongest positive survivor

The source theorem must act on the induced prime-normal transition, not merely on the source
distribution.  The exact surviving target is:

> Construct, before divisor specialization, a literal ordinary-prime incidence lift for which
> the induced conormal endomorphisms
> \[
>   q_2(s)=3-2^s-2^{1-s},
>   \qquad
>   q_3(s)=4-3^s-3^{1-s}
> \]
> have a common real reduction on every nonzero Xi top conormal.

The paired theorem `two-prime-real-euler-transition-selector.md` shows that this target implies
RH.  It is strictly stronger than generic microlocal reality and strictly narrower than
all-prime unitarity.

## New insight

The nonlinear reciprocal graph is where real source geometry can acquire complex divisor
momentum.  Any successful “real conormal” ontology must prove that prime incidence survives this
specific nonlinear operation.  Linear Fourier/Mellin microlocality alone cannot do it.

## Status

Paper proof is dependency-closed.  The polynomial and Laplace-transform identities are elementary.
Lean formalization is useful only together with the two-prime selector; no RH claim follows from
the no-go alone.

## Log

- 2026-07-31 — killed generic real-wavefront selector with an explicit real point-supported
  quartet source; extracted two-prime conormal real reduction as the exact positive survivor.
