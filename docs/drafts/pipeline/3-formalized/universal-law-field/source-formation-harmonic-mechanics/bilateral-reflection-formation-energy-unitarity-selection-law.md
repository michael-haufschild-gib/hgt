# Bilateral reflection-formation energy and unitarity-selection law

**Status:** `[PAPER-PROVED] [LEAN-FORMALIZED] [EXACT ADMISSION CLASSIFICATION] [REFLECTION FUSION] [RH-EQUIVALENT RECEIVER] [NOT A SOURCE PRODUCER]`

## 1. Selection mechanism

The finite harmonic excess identifies the critical radial character but does not force a physical
zero to have zero excess.  Reflection supplies a stronger mechanism: require the source-formed
history and its reflected reciprocal history to be simultaneously admitted by the same positive
edge energy.

On the prime-exponent ray, the literal normalized Möbius channels are unweighted unit edges.  For
a positive radial character \(q^n\), define its forward formation energy density

\[
\varepsilon_q(n)=\left(q^{n+1}-q^n\right)^2.
\tag{BRF.1}
\]

Reflection of radial drift is \(q\mapsto q^{-1}\).  Bilateral admission is

\[
\sum_{n\ge0}\varepsilon_q(n)<\infty,
\qquad
\sum_{n\ge0}\varepsilon_{q^{-1}}(n)<\infty.
\tag{BRF.2}
\]

## 2. One-sided classification

For \(q\ge0\),

\[
\varepsilon_q(n)
=(q-1)^2(q^2)^n.
\tag{BRF.3}
\]

If \(q=1\), the energy is identically zero.  If \(q\ne1\), multiplication by the nonzero constant
\((q-1)^2\) does not affect summability, so the geometric-series criterion gives

\[
\sum_{n\ge0}\varepsilon_q(n)<\infty
\iff q^2<1
\iff q<1.
\]

Including the zero-energy endpoint,

\[
\boxed{
\sum_{n\ge0}\varepsilon_q(n)<\infty
\iff q\le1.}
\tag{BRF.4}
\]

## 3. Bilateral selection theorem

Let \(q>0\).  Apply (BRF.4) to \(q\) and \(q^{-1}\):

\[
\begin{aligned}
\text{bilateral admission}
&\iff q\le1\ \text{and}\ q^{-1}\le1\\
&\iff q\le1\ \text{and}\ 1\le q\\
&\iff q=1.
\end{aligned}
\]

Therefore

\[
\boxed{
\operatorname{Summable}(\varepsilon_q)
\ \wedge\
\operatorname{Summable}(\varepsilon_{q^{-1}})
\iff q=1.}
\tag{BRF.5}
\]

This is an exact unitarity classification for the stated bilateral admission predicate.  It uses
neither a fitted target norm nor a zero-location premise.  It does **not** prove that the literal
pre-divisor source admits the two histories at a Xi zero.

## 4. Prime-radial and RH receivers

For a prime \(p\) and real drift \(\nu\), put \(q=p^\nu\).  Since \(p>1\),

\[
q=1\iff \nu=0.
\tag{BRF.6}
\]

For the physical receiver \(\nu=2\operatorname{Re}\rho-1\), bilateral formation admission implies

\[
\operatorname{Re}\rho=\tfrac12.
\tag{BRF.7}
\]

Consequently RH follows from the following sharply typed bridge:

> **Bilateral zero-admission bridge.** Every nontrivial Xi zero induces, before divisor
> specialization, a marked radial formation history whose forward and reflected reciprocal edge
> energies are both admitted in the literal source completion.

The corpus audit shows that this bridge is not an independent source theorem currently in hand.
`RHTower.PrimeClockScaleFactor` already proves that perspective-neutral reflected clock admission
at every Xi zero is equivalent to RH, and `source-horizontal-moment-neutral-amplification-no-go.md`
records the same equivalence for the corresponding two-sided normalization domain.  Therefore
asserting the bridge at zeros merely restates the missing selection step.

## 5. Exact positive survivor and field boundary

The theorem fuses four laws:

1. source formation chooses the unit-edge incidence and therefore the energy density;
2. positivity turns edge responses into a summability admission condition;
3. reflection sends radial drift to its reciprocal;
4. completion must admit both histories in one marked doctrine.

Each one-sided completion admits an entire half-space of drifts.  Their reflected intersection is
the unitary wall.  Selection is therefore an **intersection-of-admissions law**, not the zero set
of another scalar observer.

This supplies a valid general classification principle:

\[
\boxed{
\text{dual one-sided formation doctrines select the locus where both generated histories are
admissible}.}
\tag{BRF.8}
\]

It is useful as a receiver test and as a falsifier for proposed completions: any completion which
admits both reciprocal geometric histories off the unit wall cannot be the required unweighted
source completion.  It is not evidence that the arithmetic source actually produces bilateral
admission.  The field programme therefore moves upstream to generated formation, ghost,
dualization, and continuation laws whose conservation can be checked before the zero divisor is
inserted.

## 6. Sharp scope

1. Energy is applied to the radial quotient \(q=|z|\), not the full complex phase history.  A
   nontrivial unit phase has infinite unweighted full-character edge energy.
2. Unweighted incidence is source-native on the prime-exponent ray.  Arbitrary decaying observer
   weights can admit off-unit radial drifts and destroy (BRF.5).
3. One-sided admission alone selects only \(q\le1\); reflection is load-bearing.
4. Reflection symmetry of Xi alone does not prove bilateral source admission.  That completion
   bridge remains the RH-bearing theorem.
5. No claim is made that existing route completions already provide the required common marked
   doctrine.
6. Imposing bilateral admission on the physical Xi divisor is an RH-equivalent receiver premise,
   not progress toward its source derivation.

## 7. Lean status

Formalized in

`GaloisForLFunctions.HTGeometry.SourceFormationHarmonicMechanics`

as:

- `geometricRefinementEnergy`;
- `geometricRefinementEnergy_eq`;
- `summable_geometricRefinementEnergy_iff`;
- `bilateral_geometricRefinementEnergy_summable_iff`;
- `primeRadial_bilateral_geometricRefinementEnergy_summable_iff`.
