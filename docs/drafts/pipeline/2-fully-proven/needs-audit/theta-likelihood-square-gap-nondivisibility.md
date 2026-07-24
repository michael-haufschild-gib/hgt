# Theta likelihood square-gap nondivisibility

- **ID:** theta-likelihood-square-gap-nondivisibility
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper); theta-specific premise THEOREM (Lean)
- **Source:** `docs/handover/connes.md` §§13–18
- **Statement:** Every normalized fixed-measure theta likelihood law on the intrinsic half-line
  \(B>0\) has atoms at \(0\) and \(3\), no atom at \(6=3+3\), and therefore is neither infinitely
  divisible nor a generalized gamma convolution.

Labels: `[PAPER-PROVED] [LEAN-SOURCE-PREMISE] [NO-GO] [POSITIVE-SURVIVOR]`
`[NOVELTY-UNVERIFIED] [NOT-RH]`

## Goal

Decide whether the fixed modular-seam likelihood measure from
`ThetaCuspLikelihoodModularSeam.lean` can be exponentiated into a Lévy/Thorin/subordinator
scattering carrier. This is a source-structure question, not an estimate and not an RH-equivalent
criterion.

## Gates

- [x] 0 → 1: exact source law already available; independent-increment route identified
- [x] 1 → 2: complete paper proof below; standard parent theorem cited explicitly
- [ ] 2 → 3: full infinite-divisibility implication formalized in Lean
- [ ] 3 → 4: independent novelty review and publication packaging

## Exact theorem

For \(B>0\), let

\[
d\nu(t)=\sum_{n\ge2}e^{-3(n^2-1)/2}
\left[n^4\delta_{n^2-1}
+\frac32n^2(n^2-1)\mathbf 1_{(n^2-1,\infty)}(t)\,dt\right],
\]

\[
Z(B)=1+\int_0^\infty e^{-Bt}\,d\nu(t),
\qquad
dP_B(t)=\frac{\delta_0(dt)+e^{-Bt}d\nu(t)}{Z(B)}.
\]

Then:

1. \(P_B\) is a probability law on \([0,\infty)\).
2. \(P_B\{0\}>0\), \(P_B\{3\}>0\), and \(P_B\{6\}=0\).
3. The pair law satisfies \((P_B*P_B)\{6\}>0\): the two-particle sector creates an atom absent
   from the one-particle carrier.
4. The atom support
   \(A(P_B)=\{t:P_B\{t\}>0\}\) is not closed under addition.
5. \(P_B\) is not infinitely divisible.
6. Hence \(P_B\) is not a generalized gamma convolution and cannot be a marginal of a Thorin
   subordinator.

The conclusion holds for every \(B>0\), not only at the modular seam
\(B_0=\pi-3/2\).

## Proof

### 1. Probability normalization

The fixed-measure likelihood theorem gives

\[
\int e^{-Bt}\,d\nu(t)=L(B)<\infty
\]

for every \(B>0\). Therefore \(0<Z(B)=1+L(B)<\infty\), and \(P_B\) is a probability law supported
on \([0,\infty)\).

### 2. Exact atoms

The added \(\delta_0\) gives \(P_B\{0\}=Z(B)^{-1}>0\). Every component of \(\nu\) has one Dirac
mass at the square gap \(n^2-1\ge3\) and an atomless Lebesgue ray. Thus the only contribution at
\(3\) is the \(n=2\) Dirac mass:

\[
P_B\{3\}=\frac{e^{-3B}e^{-9/2}2^4}{Z(B)}>0.
\]

There is no integer \(n\ge2\) with \(n^2-1=6\): \(n=2\) gives \(3\), while \(n\ge3\) gives at
least \(8\). Lebesgue rays charge no singleton, so \(P_B\{6\}=0\). Consequently
\(3\in A(P_B)\) but \(3+3\notin A(P_B)\).

Nevertheless the product atom \((3,3)\) has positive \(P_B\otimes P_B\)-mass and addition maps it
to \(6\). Hence

\[
(P_B*P_B)\{6\}\ge P_B\{3\}^2>0.
\]

This is not merely a missing closure law: convolution produces a genuinely new two-particle
spectral atom.

### 3. Compound-Poisson atom closure

Let \(P\) be compound Poisson with intensity \(\lambda>0\) and jump law \(Q\):

\[
P=e^{-\lambda}\sum_{m\ge0}\frac{\lambda^m}{m!}Q^{*m}.
\]

Its atom support is additively closed. Indeed, if \(P\{x\}>0\), positivity of the series gives an
\(m\) with \(Q^{*m}\{x\}>0\). For finite Borel measures, an atom of a convolution is a sum of
atoms: from

\[
(\mu*\eta)\{x\}=\int \eta\{x-y\}\,d\mu(y),
\]

the integrand is supported on the countable atom set of \(\eta\); a positive integral therefore
contains \(y\) with \(\mu\{y\}>0\) and \(\eta\{x-y\}>0\). Iteration writes \(x\) as a sum of \(m\)
atoms of \(Q\). Do the same for an atom \(y\) using \(n\) jumps. Concatenating the two tuples gives
\(Q^{*(m+n)}\{x+y\}>0\), hence \(P\{x+y\}>0\).

The case \(\lambda=0\) is \(\delta_0\), whose atom support is also additively closed.

### 4. Infinite-divisibility contradiction

A standard classification theorem for probability laws on \([0,\infty)\) says: an infinitely
divisible law with infimum of support \(0\) has a discontinuity (an atom) iff it is compound
Poisson. See Steutel–van Harn, *Infinite Divisibility of Probability Distributions on the Real
Line*, Chapter III, Theorem 4.15. Since \(P_B\{0\}>0\), infinite divisibility of \(P_B\) would make
it compound Poisson. The preceding lemma would then force

\[
P_B\{3\}>0 \Longrightarrow P_B\{6\}>0,
\]

contradicting the exact source calculation. Thus \(P_B\) is not infinitely divisible. Every GGC
law is infinitely divisible, so the GGC/Thorin conclusions follow.

## Lean certificate

Module:

`formal/GaloisForLFunctions/RHTower/ThetaCuspLikelihoodAtomicNondivisibility.lean`

Lean proves exactly:

- singleton formula for every atom-ray carrier;
- higher measure masses at \(0,3,6\);
- preservation under every real exponential tilt;
- failure of additive atom closure;
- persistence under every nonzero scalar normalization.
- birth of a nonzero self-convolution atom at \(6\).

Principal declarations:

- `thetaCuspHigherLikelihoodSpectralMeasure_singleton_three`
- `thetaCuspHigherLikelihoodSpectralMeasure_singleton_six`
- `thetaCuspLikelihoodSeamTiltedMeasure_singleton_three_ne_zero`
- `not_additivelyClosedAtomSupport_thetaCuspLikelihoodSeamTiltedMeasure`
- `not_additivelyClosedAtomSupport_smul_thetaCuspLikelihoodSeamTiltedMeasure`
- `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`

Lean does not yet formalize the general probability-theory parent theorem
“infinitely divisible plus atom at zero implies compound Poisson,” so the full nondivisibility
corollary remains paper-only.

## Hostile audit

1. **Topological support is irrelevant.** The first ray makes every point above \(3\) belong to the
   topological support, including \(6\). The contradiction concerns singleton mass, not support.
2. **Continuous jumps cannot hide the defect.** An atom of a finite convolution can only be
   assembled from atoms of its factors; the countability argument above excludes a continuous
   contribution to a singleton.
3. **Tilt cannot remove or create these atoms.** \(e^{-Bt}\) is strictly positive at every finite
   \(t\); normalization is also strictly positive.
4. **No shifted compound-Poisson escape.** \(P_B\) is supported on \([0,\infty)\), has infimum
   support \(0\), and already charges \(0\). The classification has zero drift/shift here.
5. **No contradiction with Polson's Thorin tiers.** Polson's incomplete-gamma/zero-based GGC
   objects are different probability laws. This theorem forbids exponentiating this specific
   fixed likelihood carrier \(\delta_0+e^{-Bt}\nu\); it does not refute other Xi-related GGC
   representations.

## No-go closure

- **Exact killing theorem/mechanism:** square-gap atom support fails the mandatory
  compound-Poisson closure law at \(3+3=6\).
- **Strongest positive survivor:** the first atomic semigroup defect
  \[
  3\in A(P_B),\qquad 6\notin A(P_B),\qquad 6\in A(P_B*P_B)
  \]
  is an exact, tilt-invariant arithmetic signature of the completed source. Pairing creates a
  new latent sector absent from the one-particle law.
- **New insight:** fixed latent scattering cannot be realized by independent increments, a Lévy
  exponent, or a Thorin carrier. Any source-side phase producer must retain coherent off-diagonal
  interaction among square-gap atoms and Lebesgue rays; exponentiating channels independently
  destroys the arithmetic incidence that distinguishes the actual theta source. The missing
  phase orientation must first be sought in this irreducible two-particle sector, not in another
  one-particle MLR observable.
- **Status:** paper proof dependency-closed modulo cited standard classification theorem;
  theta-specific premise formalized exactly; external priority audit incomplete.

## Literature and novelty audit

- F. W. Steutel and K. van Harn, *Infinite Divisibility of Probability Distributions on the Real
  Line* (2004), Chapter III, Theorem 4.15 and Chapter II/III compound-Poisson material:
  https://www.routledge.com/Infinite-Divisibility-of-Probability-Distributions-on-the-Real-Line/Steutel-Harn/p/book/9780824707242
- L. F. James, B. Roynette, M. Yor, “Generalized Gamma Convolutions, Dirichlet means, Thorin
  measures, with explicit examples” (2008): https://arxiv.org/abs/0708.3932
- N. G. Polson, “Incomplete Gamma Representations of the Riemann Xi Function: a Thorin Bernstein
  Framework” (2026): https://ssrn.com/abstract=6954119

Targeted searches found Xi/GGC constructions and general infinite-divisibility classifications,
but no source treating this fixed theta likelihood law or its \(3+3\notin A(P_B)\) obstruction.
That is insufficient for a priority claim. Label remains `[NOVELTY-UNVERIFIED]`.

## Log

- 2026-07-21 — derived exact square-gap obstruction; completed paper proof; formalized
  theta-specific atom-support theorem.

## Lean progress

- 2026-07-25 — **Correction + reusable-lemma extraction.**  The theta-specific atom content of this
  card was **already** fully formalized in `RHTower/ThetaCuspLikelihoodAtomicNondivisibility.lean`
  (`thetaCuspLikelihoodSeamTiltedMeasure` = `P_B`, its singleton masses at `0,3,6`,
  `not_additivelyClosedAtomSupport_...` on the actual measure, and
  `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`).  An abstract-atom-set
  restatement I had briefly added (`ThetaSquareGapAtomNonClosure.lean`) duplicated that weaker and was
  **removed**.  Net kept contribution: the one genuinely reusable general lemma, now placed in the
  existing module and used to simplify its self-convolution proof (axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `measure_singleton_le_conv` — **atoms add under convolution**: `μ{a}·ν{b} ≤ (μ ∗ ν){a+b}` for any
    measures on an additive monoid (`Measure.conv = map (+) (μ.prod ν)`, `Measure.prod_prod`,
    singleton-`⊆`-preimage monotonicity).  `thetaCuspLikelihoodSeamTiltedMeasure_selfConv_singleton_six_ne_zero`
    now discharges via `measure_singleton_le_conv μ μ 3 3` (step 3) instead of an inline argument.
  **Still open for gate `2 → 3`** (unchanged): the classical parent "an infinitely divisible law on
  `[0,∞)` with an atom at `0` is compound Poisson, whose atom support is additively closed"
  (Steutel--van Harn Ch. III Thm 4.15) is absent from mathlib.  The theta-specific premise is Lean-done;
  only this general probability parent remains.
