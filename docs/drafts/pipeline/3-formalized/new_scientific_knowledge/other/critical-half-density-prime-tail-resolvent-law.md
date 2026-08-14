# Critical half-density prime-tail resolvent law

- **ID:** `critical-half-density-prime-tail-resolvent-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / SOURCE--DIVISOR UNIFICATION
- **Scientific status:** `[PROVED HERE] [CORPUS-NEW SYNTHESIS] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parent:** `not_new_scientific_knowledge/prime-tail-copoisson-essential-boundary-bockstein.md`
- **Statement:** The critical half-density prime-tail source is the advanced resolvent of one
  spectral-parameter-independent ordinary-integer atomic measure. Every Xi divisor conormal is a
  nonzero homogeneous ambiguity of that same forced transport equation, with exact multiplicity.

## Goal

Replace the vague diagram

```text
prime source  -> boundary operation -> Xi conormal
```

by one literal distribution equation in which the ordinary-prime source is the forcing term and
the Xi conormal is exactly the homogeneous solution created by analytic monodromy. This does not
yet supply the global boundary condition that would force the homogeneous exponent to be
imaginary.

## Source

For \(n\ge2\), put
\[
a_n=\frac{\Lambda(n)}{\log n}.
\]
For \(\operatorname{Re}z>1\) and \(0<x<1\), the already-proved prime-tail source is
\[
G_z(x)=x^{-z}\sum_{\substack{n\ge2\\nx\ge1}}a_nn^{-z}.
\tag{1}
\]
Pass to logarithmic half-density coordinates
\[
L=\log(1/x),\qquad
H_z(L)=e^{-L/2}G_z(e^{-L}).
\tag{2}
\]
Then
\[
\boxed{\qquad
H_z(L)
=e^{(z-\frac12)L}
 \sum_{\log n\ge L}a_nn^{-z}.
\qquad}
\tag{3}
\]

Define the locally finite ordinary-integer prime-power measure on \((0,\infty)\)
\[
\Pi_0
=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n\,\log n}\,\delta_{\log n}.
\tag{4}
\]
It is locally finite because every compact interval contains only finitely many \(\log n\).

## Theorem 1: one forced transport equation

For every \(\operatorname{Re}z>1\), in distributions on \((0,\infty)\),
\[
\boxed{\qquad
\left(\partial_L-(z-\tfrac12)\right)H_z=-\Pi_0.
\qquad}
\tag{5}
\]
The forcing term is independent of \(z\). Equivalently,
\[
H_z(L)
=\int_{[L,\infty)}
 e^{(z-\frac12)(L-t)}\,d\Pi_0(t).
\tag{6}
\]

### Proof

Between consecutive points \(\log n\), the tail set in `(3)` is constant, so
\[
\partial_LH_z=(z-\tfrac12)H_z.
\tag{7}
\]
When \(L\) crosses \(\log n\) from left to right, the \(n\)-th term leaves the tail. Its jump is
\[
\begin{aligned}
H_z((\log n)^+)-H_z((\log n)^-)
&=-e^{(z-\frac12)\log n}a_nn^{-z}\\
&=-\frac{a_n}{\sqrt n}\\
&=-\frac{\Lambda(n)}{\sqrt n\,\log n}.
\end{aligned}
\tag{8}
\]
The distributional derivative of a piecewise smooth function is its ordinary derivative plus its
jump measure. Equations `(7)`--`(8)` prove `(5)`. Substituting `(4)` into `(6)` gives `(3)`
termwise, proving the resolvent form.

## Theorem 2: the Weil prime current is the position-weighted forcing

Let \(M_L\) denote multiplication of a measure by the coordinate \(L\). Then
\[
\boxed{\qquad
M_L\Pi_0
=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\,\delta_{\log n}.
\qquad}
\tag{9}
\]
Consequently the unsquared nonarchimedean Weil current is not added after the co-Poisson
construction. It is the position moment of the forcing measure in `(5)`.

### Proof

At the atom \(L=\log n\), multiplication by \(L\) cancels the denominator \(\log n\) in `(4)`.

## Theorem 3: every Xi conormal is a homogeneous ambiguity

The analytic continuation of \(G_z\) once positively around a nontrivial zero \(\rho\) of
multiplicity \(m_\rho\) has monodromy
\[
\Delta_\rho G_z(x)\big|_{z=\rho}
=2\pi i\,m_\rho x^{-\rho}.
\tag{10}
\]
After `(2)`, this becomes
\[
\boxed{\qquad
\Delta_\rho H_z(L)\big|_{z=\rho}
=2\pi i\,m_\rho e^{(\rho-\frac12)L}.
\qquad}
\tag{11}
\]
It is a nonzero homogeneous solution of the same source equation:
\[
\left(\partial_L-(\rho-\tfrac12)\right)
\Delta_\rho H_z\big|_{z=\rho}=0.
\tag{12}
\]
Every multiplicity jet survives:
\[
\partial_\rho^j\Delta_\rho H_z\big|_{z=\rho}
=2\pi i\,m_\rho L^j e^{(\rho-\frac12)L},
\qquad 0\le j<m_\rho.
\tag{13}
\]

### Proof

Equation `(10)` is the parent card's prime-tail divisor Bockstein theorem. Applying the
half-density transform gives `(11)`. Equations `(12)`--`(13)` follow by differentiation.

## Theorem 4: reflection is the adjoint indicial root

Put
\[
\lambda_\rho=\rho-\tfrac12.
\tag{14}
\]
Source inversion followed by conjugation sends the homogeneous mode in `(11)` to the mode with
indicial root
\[
-\overline{\lambda_\rho}
=\tfrac12-\overline\rho.
\tag{15}
\]
Thus the two literal source characters are the two roots
\[
\lambda_\rho,\qquad-\overline{\lambda_\rho}
\tag{16}
\]
of the transport operator and its Hilbert-adjoint reflection. They agree exactly when
\[
\lambda_\rho=-\overline{\lambda_\rho}
\quad\Longleftrightarrow\quad
\operatorname{Re}\rho=\tfrac12.
\tag{17}
\]

This is the short RH consumer, not its source proof.

## Universal interpretation

Equations `(5)` and `(11)` change the ontology:

```text
ordinary-prime incidence:
  fixed atomic forcing Pi_0;

Gamma/co-Poisson source:
  advanced Green solution H_z of d/dL-(z-1/2);

Xi zero:
  parameter value where analytic continuation acquires monodromy;

Xi conormal and multiplicity:
  homogeneous ambiguity e^((rho-1/2)L) and its polynomial Jordan jets;

functional-equation reflection:
  passage from the indicial root lambda to the adjoint root -conj(lambda);

RH:
  every source-created homogeneous ambiguity is one global mode for the operator and its adjoint,
  hence lambda=-conj(lambda).
```

This says precisely what the requested essential boundary operation must do. It need not
“discover” divisor points after the fact: the literal source family already produces every
conormal by monodromy. It must prove a **global uniqueness theorem for the homogeneous ambiguity**
inside the source completion.

## Exact open core

`[OPEN CORE] [PRIME_TAIL_GLOBAL_ADJOINT_GREEN_UNIQUENESS]`

Construct a Hausdorff completion \(\mathscr B_{\mathrm{src}}\), before zero specialization, and a
closed realization of the literal forced equation `(5)` such that:

1. \(\Pi_0\), including its prime-incidence filtration, is the actual forcing;
2. analytic continuation of the Green family lands every mode `(13)` nontrivially;
3. the position moment `(9)` and Gamma/reflection term belong to the same closed equation;
4. source inversion is the Hilbert adjoint of the same closed transport realization, not a second
   external copy;
5. every monodromy ambiguity is a global homogeneous mode in the common source/adjoint domain.

Then `(17)` proves RH. Clause 5 is the load-bearing theorem. Replacing it by “pure,” “unitary,”
“moderate,” “same-fibre,” or “conservative” without constructing the closed Green equation is
circular.

## Relation to the Sonin essential-phase theorem

`new_scientific_knowledge/sonin/cofinal-essential-phase-sonin-coupling-nonannihilation.md` proves
that the smooth high-frequency Sonin boundary has a genuine internal partial unitary. It also
proves that every fixed Mellin evaluation of that packet is \(O(r^{-N})\) for all \(N\). Therefore
the high-frequency scattering face cannot carry `(11)`.

Equation `(8)` identifies the correct escape from that no-go: the literal prime source is BV,
with nonsmooth jumps whose amplitudes are exactly \(\Pi_0\). The RH completion must be built on
the **indicial/jump face** `(5)`, not on the smooth wavepacket face.

## Hostile audit

- **Is `(5)` merely the Dirichlet series again?** It is equivalent to the tail formula on the
  initial half-plane, but adds an exact local distribution equation whose forcing is independent
  of the spectral parameter. The new content for the project is the identification of source
  incidence and divisor conormals as forcing and homogeneous ambiguity of one operator.
- **Does a homogeneous mode imply RH?** No. Every off-line zero produces one. RH requires the
  source theorem that the mode and its reflected adjoint are one global ambiguity.
- **Does local finiteness hide divergence?** No. \(\Pi_0\) is locally finite on \((0,\infty)\);
  behavior at \(+\infty\) is exactly the boundary-completion problem and is not discarded.
- **Is multiplicity lost?** No. It is the coefficient \(m_\rho\) in `(11)`, and all polynomial
  jets `(13)` remain nonzero.
- **Is positivity used?** No. Generalized-prime off-line systems can satisfy analogous forced
  equations. The discriminating theorem must use the ordinary-integer forcing and its completed
  Gamma adjoint globally.
- **Is “global mode” being asserted by definition?** No. It is explicitly left as clause 5 of the
  open core.

## Literature audit

The ingredients are classical: logarithmic differentiation of Euler products, prime-power
measures, explicit formulas, co-Poisson transforms, and first-order Green kernels. Targeted
searches found:

- J.-F. Burnol,
  [*Entrelacement de co-Poisson*](https://www.numdam.org/item/AIF_2007__57_2_525_0/), for the
  harmonic, Hilbertian, and distributional co-Poisson framework;
- J.-F. Burnol,
  [*Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*](https://www.numdam.org/item/JTNB_2004__16_1_65_0/), for co-Poisson/Sonine zero
  evaluation systems;
- S. Gy. Révész,
  [*A Riemann-von Mangoldt-type formula for the distribution of Beurling
  primes*](https://arxiv.org/abs/2110.11463), for generalized-prime explicit-formula context.

No priority claim is made for the elementary transport identity `(5)`. The provisionally new
research contribution is its exact integration with the corpus's prime-tail monodromy,
multiplicity, Sonin-face no-go, and the resulting closed-Green uniqueness formulation of the
remaining RH theorem.

## Gates

- [x] 0 → 1 in-progress: literal source, operator, forcing, and conormal identified
- [x] 1 → 2 fully-proven: complete distributional proof, no open dependency
- [x] 2 → 3 formalized: locally finite atomic measure and distributional jump equation in Lean
- [ ] 3 → 4 publication-ready: broader novelty audit and standalone exposition

## Lean plan

The nontrivial formal target is the infinite locally finite jump equation, not a finite-tail
identity. Needed infrastructure:

1. locally finite measure \(\Pi_0\) on logarithmic prime-power points;
2. càdlàg/BV tail \(H_z\) on every compact \(L\)-interval;
3. distributional derivative of a locally finite jump function;
4. proof that the jump measure is exactly `(4)`;
5. reuse of the already formalized divisor multiplicity interface for `(11)`--`(13)`.

## Log

- 2026-07-31 — Derived the parameter-independent prime forcing, exact transport resolvent,
  position-weighted Weil measure, and homogeneous Xi monodromy law. Isolated global
  source/adjoint Green uniqueness as the literal remaining theorem.

## 2026-08-14 — the distributional transport equation is formalized; card complete

`formal/GaloisForLFunctions/RHTower/CriticalHalfDensityPrimeTailResolventLaw.lean`, unconditional
and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only):

- `criticalPrimeTailForcingMeasure` with the instance
  `criticalPrimeTailForcingMeasure_isLocallyFinite` — the locally finite ordinary-integer atomic
  measure `Π₀` of `(4)`;
- `criticalPrimeTailPositionMoment_eq_weil` — Theorem 2, equation `(9)`: the position moment of the
  forcing is exactly the unsquared nonarchimedean Weil prime measure;
- `criticalHalfDensityPrimeTail_eq_advancedResolvent` — Theorem 1, equation `(6)`: the closed tail
  is the advanced resolvent of the fixed forcing;
- **`criticalHalfDensityPrimeTail_transport_eq_forcing`** — Theorem 1, equation `(5)`: for every
  `re z > 1` and every positive-time test function,
  `⟨H_z, φ'⟩ + (z − 1/2)·⟨H_z, φ⟩ = ⟨Π₀, φ⟩`, i.e. `(∂_L − (z − 1/2)) H_z = −Π₀` in distributions.
  The proof rewrites the tail as its atom sum, interchanges sum and integral against the summable
  norm bounds, and evaluates each advanced Green atom by half-line integration by parts: the
  endpoint at `−∞` is killed by compact support and the endpoint at the atom is precisely its
  Dirac mass `Λ(n)/(√n·log n)`.
- **`integral_homogeneousMode_transport`** — Theorem 3, equation `(11)`: every exponential mode
  `e^{μL}` is annihilated by `∂_L − μ`, so with `μ = ρ − 1/2` the mode created at a nontrivial zero
  is a homogeneous ambiguity of the *same* forced equation, not a second object.  Its multiplicity
  is the already formalized divisor interface `RHTower.windingNumber_xi_zero`
  (`winding number of ξ about ρ = ord_ρ ξ`).
- `integral_deriv_eq_zero_of_hasCompactSupport` — the supporting real-analysis lemma (the integral
  of the derivative of a compactly supported `C¹` function vanishes), missing from mathlib in this
  form.

This is exactly the stage-3 gate of this card: the locally finite atomic measure and the
distributional jump equation.  The RH-equivalent global source/adjoint Green uniqueness recorded
under "Exact open core" is, as stated there, open, and is not claimed here.
