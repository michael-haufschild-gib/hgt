# Reflected formation stratification and properness

- **ID:** ULF-SPCM-02
- **Stage:** 2-fully-proven
- **Status:** dependency-closed; Lean formalized
- **Role:** universal mechanism joining stable class, holonomy, formation work, and singular escape

## Law

For an actual multiplicity-labelled Xi copy `q`, let

\[
a(q)=2\operatorname{Re}(q)-1,
\qquad c(q)=[1-2\operatorname{Re}(q)]_{\rm stable}.
\]

Functional-equation reflection gives `a(q*)=-a(q)`. Use these two values as the forward and
reflected laws of one separating reporter. The orbit-symmetrized three-slot transposition defect is

\[
\Delta_3(q)=\frac{(a(q)-a(q^*))^2}{2}=2a(q)^2.       \tag{F.1}
\]

For `N` independent formation blocks, additivity gives

\[
W_N(q)=N\Delta_3(q)=2N a(q)^2.                       \tag{F.2}
\]

Hence

\[
\sup_N W_N(q)<\infty\iff a(q)=0.                     \tag{F.3}
\]

Corpus also proves

\[
c(q)=0\iff a(q)=0,                                   \tag{F.4}
\]

and, at every nontrivial formation clock, central cofinal holonomy vanishes exactly when `c(q)`
vanishes. Let `I(q)` be the quantized principal escape index from ULF-SPCM-01. Then

\[
I(q)=0\iff c(q)=0,
\qquad I(q)=1\iff c(q)\ne0.                           \tag{F.5}
\]

Combining `(F.3)`--`(F.5)`:

\[
\boxed{
\text{formation work proper}
\iff c(q)=0
\iff \text{central holonomy}=0
\iff I(q)=0.}                                         \tag{F.6}
\]

Globally, proper reflected formation work for every Xi copy is equivalent to RH.

## Proof

The coordinate-free tensor interchange identity

\[
(p\otimes p+q\otimes q)-(p\otimes q+q\otimes p)
=(p-q)\otimes(p-q)
\]

gives the reporter-square law. Substituting `q=-p` yields `(F.1)`. Independent formation
composition is additive, proving `(F.2)`. If `a(q)\ne0`, `(F.2)` diverges linearly; if `a(q)=0`,
all work is zero. This proves `(F.3)`.

The arithmetic three-chart theorem identifies `c(q)` with `1-2 Re(q)`, proving `(F.4)`. The
central-transgression theorem identifies normalized cofinal anomaly with exponential holonomy of
`c(q)` and proves no extra neutral points. ULF-SPCM-01 proves `I(q)=0` exactly at centered modular
rate zero and `I(q)=1` otherwise, giving `(F.5)` and `(F.6)`. The global claim follows from the
existing equivalence between vanishing centered rate on every multiplicity-labelled Xi copy and RH.

## Interpretation

This is the common mechanism, not a route analogy:

\[
\text{signed stable class}
\xrightarrow{\exp}\text{central holonomy}
\xrightarrow{\text{three-slot formation}}\text{extensive work}
\xrightarrow{\text{positive support}}\text{quantized escape}.
\]

- Functional equation reverses signed class but preserves square work.
- Positivity is support tropicalization: every nonzero class becomes one escape unit.
- Noncompactness is extensive formation depth: off-neutral work grows linearly.
- Properness is selection: bounded total work forces neutral class.
- Gamma-six, Möbius prime-normal energy, Green codiagonal, and Kakutani escape are local readers of
  the same final stratum.

## Exact remaining producer

No theorem here asserts formation properness for the Xi source. A valid next law must derive, before
zero-fibre scalarization, one of the equivalent source statements:

1. source-generated three-slot deletion/exchange consistency;
2. a source conservation identity uniformly bounding `W_N`;
3. a source-to-formation bridge whose non-principal correction is summable and whose principal
   history is reflection-dual.

Functional equation alone supplies only the two-periodic alternation and is insufficient. Ordinary
`L²` continuity, fixed-source untwisting, trace-class admission, or post-divisor boundedness merely
restate the zero stratum and do not produce `(F.3)`.

## Gates

- [x] reflected reporter law constructed from actual Xi copy
- [x] exact three-slot defect `2a²`
- [x] exact extensive work `2Na²`
- [x] properness/neutrality equivalence
- [x] stable-class and central-holonomy weld
- [x] singular-support tropicalization
- [x] global RH equivalence
- [x] Lean formalization
- [ ] unconditional source-generation/properness law
