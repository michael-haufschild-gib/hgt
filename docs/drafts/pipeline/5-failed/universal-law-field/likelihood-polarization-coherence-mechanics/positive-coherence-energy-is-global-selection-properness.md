# Positive coherence energy is global selection properness

- **ID:** ULF-LPCM-F2
- **Stage:** 5 — failed/retired
- **Type:** FALSIFIED PROPERNESS CONJECTURE WITH SHARP CLASSIFICATION SURVIVOR
- **Claim:** If the canonical lift-coherence energy is strictly positive away from reflection
  invariance, then its operator is bounded below on the full nonneutral response space.
- **Status:** `[FALSIFIED] [DENSE-NONCLOSED COUNTERMODEL]`
  `[EXACT CLOSED-RANGE SURVIVOR PAPER-PROVED] [LEAN NOT YET WRITTEN] [NOT RH]`

## Conjecture

For a reflected pair `P,Q`, let `d` be posterior contrast and let

\[
 Mf=(F_+C-F_-C)f.
\]

Since

\[
 \|M1\|^2=4\int d^2\,d\eta>0
\]

whenever `P ne Q`, the conjecture claimed a constant `c>0` with

\[
 \|Mf\|\ge c\|f\|
\]

on the complement of the neutral kernel.

## Exact countermodel

Take `X=(-1,1)` with normalized Lebesgue measure `eta`, reflection `R(x)=-x`, and densities

\[
 p(x)=1+x,
 \qquad
 q(x)=1-x.
\]

They define equivalent reflected probability measures.  Their posterior contrast is

\[
 d(x)=x.
\]

Hence

\[
 \|M1\|^2=4\int_{-1}^1x^2\,d\eta>0.
\]

But multiplication by `x` on `L^2(-1,1)` is injective with dense nonclosed range.  Let `f_n` be a
normalized indicator of `(-1/n,1/n)`.  Then

\[
 \|f_n\|=1,
 \qquad
 \|Mf_n\|=2\|xf_n\|\longrightarrow0.
\]

Thus canonical state-level separation does not imply operator properness.

## Exact classification survivor

ULF-LPCM-1 proves:

\[
 \operatorname{ran}M\text{ is closed}
 \quad\Longleftrightarrow\quad
 \operatorname*{ess\,inf}_{d\ne0}|d|>0.
\]

Equivalently, stable coherence selection requires a nonzero likelihood gap.  When `d ne 0` almost
everywhere but approaches zero essentially, `M` is injective with dense nonclosed range.

The literal positive theta tilt has exactly this second behavior for every nonzero tilt: canonical
coherence energy is strict, but `tanh(tx)` approaches zero near `x=0`.

## No-go closure

- **Exact killing theorem/mechanism:** strict positivity of one quadratic expectation does not
  bound the multiplication symbol away from zero on adaptive response vectors.
- **Strongest positive survivor:** the full closed-range/likelihood-gap equivalence, plus the
  distinction between faithful-state selection and stable operator selection.
- **New insight:** a final RH argument may need only coherence on one source-canonical faithful
  packet; if it claims robustness under perturbation or cofinal completion, it must produce a
  genuine likelihood gap or a joint frame of several coherence currents.
- **Status:** survivor is dependency-closed on paper in ULF-LPCM-1.  Lean corpus was audited
  read-only; no Lean file was written or built.

## Hostile boundaries

1. Finite sample spaces with all nonzero contrasts separated from zero do have a lower bound.
2. Quotienting by the kernel is insufficient when zero remains in the essential spectrum.
3. Adding an arbitrary weight can make multiplication proper, but is not source-generated.
4. A family of contrasts may be jointly proper even if each is not; that is the next legitimate
   cofinal gate.

## Log

- 2026-08-14 — global properness conjecture killed by the continuous two-point-mixture chart.
- 2026-08-14 — exact likelihood-gap classification and joint-frame successor retained.
