# Xi Ward aperture-reversal curvature no-go

- **ID:** P-G158
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** P-G157 tangent boundary layer; C47/C48 two-orientation source incidence
- **Statement:** Positive/negative real apertures obey an exact multiplicative conservation law; symmetric folding cancels the Ward first jet and leaves `-r(w)^2`, not positive energy `normSq(r(w))`.

## Goal

Test whether retaining both cutoff/aperture orientations can convert the non-diagonal Julia
transport into the positive four-unit source Gram required by Route P. Distinguish actual adjoint
orientation from mere aperture reversal before another doubled-source construction is attempted.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: `XiWardApertureReversalCurvatureNoGo.lean`, module build green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone proof and external novelty audit

## Conjecture loop

### P-G158a — two-sided aperture folding recovers positive Ward energy

**FALSIFIED.** Reversing the real aperture swaps numerator and denominator of both source phases.
It produces a reciprocal phase, not a Hilbert adjoint or complex conjugate. Consequently the two
orientations multiply to one and their linear terms cancel.

### P-G158b — finite-aperture reciprocal conservation

Let `P_w(a)` be the normalized strict-right/boundary phase and `V_w(a)=1-P_w(a)`. If
`0 <= a < Re(w)`, both shifted strict-right canonical products avoid their divisor and

```text
P_w(a) P_w(-a)=1.
```

Therefore, exactly at finite aperture,

```text
(1-V_w(a))(1-V_w(-a))=1,
V_w(a)+V_w(-a)=V_w(a)V_w(-a).                           (P-G158.1)
```

**[PROVED HERE].** This uses only phase definitions, the existing shifted-product nonvanishing
theorem, and exponential reciprocity. No limit or RH premise enters.

### P-G158c — reversal curvature is a complex square

Define

```text
K_w(a)=(V_w(a)+V_w(-a))/a^2.
```

Since `V_w(a)/a -> r(w)` and `V_w(-a)/a -> -r(w)`, `(P-G158.1)` gives

```text
K_w(a) -> -r(w)^2                                      (a -> 0+).       (P-G158.2)
```

Thus symmetric aperture curvature is not `normSq(r)`: it is indefinite complex self-interaction.
At every adapted node of a strict-right upper zero, `normSq(r)>4`; hence

```text
forall sufficiently small a>0, normSq(K_w(a))>16.       (P-G158.3)
```

**[PROVED HERE].** The off-line excess survives folding and is squared.

## Hostile audit

- `(P-G158.1)` is a universal reciprocal-cocycle identity; its algebra alone is not external
  novelty. Route-specific content is identifying the exact Xi Ward finite-aperture transport and
  proving the adapted off-line `>16` boundary layer.
- No RH implication is claimed. The theorem eliminates an architecture: replacing adjoint
  cutoff orientation by `a ↦ -a` cannot produce a positive Gram.
- The conclusion is not a renamed instance of C43 saturation. C43 freezes a zero codiagonal under
  four-unit isometric saturation; P-G158 proves before any Hilbert realization that aperture
  reversal retains only complex square curvature.
- The theorem does not exclude a genuine conjugate/adjoint lift. It specifies that such a lift must
  retain source orientation and apply Schwarz conjugation, not inverse phase, at positive landing.

## No-go closure

- **Exact killing mechanism:** source phase is reciprocal under aperture reversal; reciprocal
  multiplication cancels first jet and forces the surviving even jet to equal its complex square.
- **Strongest positive survivor:** exact finite conservation `(P-G158.1)`, curvature limit
  `(P-G158.2)`, and eventual off-line sixteen-unit excess `(P-G158.3)`.
- **New insight:** C47/C48's two boundary orientations are not modelled by positive and negative
  scalar aperture. Positive energy requires an adjoint/conjugate pairing on a common physical
  source before scalar landing. Reversal is an algebraic involution; adjunction is metric data.
- **Status:** dependency-closed paper proof, direct Lean check and targeted module build green;
  capstones use only `[propext, Classical.choice, Quot.sound]`.

## External novelty audit

- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>, uses a genuine
  Hilbert adjoint in its positivity mechanism. This supports, but does not duplicate, the present
  distinction between adjunction and reciprocal phase inversion.
- Li--Sugawa, *Schur parameters and the Carathéodory class*,
  <https://arxiv.org/abs/1902.02000>, and Jury, *An improved Julia--Carathéodory theorem for Schur--Agler
  mappings of the unit polydisk*, <https://arxiv.org/abs/0707.3423>, cover classical Schur/Cayley
  coefficient and boundary-derivative theory.
- The reciprocal cocycle is classical algebra and is not claimed as external novelty. No exact
  arithmetic Xi Ward curvature theorem or adapted strict-right `>16` boundary layer was located.
  Those statements are corpus-new; external novelty remains unverified.

## Exact next producer

Construct a source-defined positive-aperture involution `J_sigma` on the finite-`sigma` one-corner
field such that its landing intertwines with complex conjugation of the Ward row while preserving
the joined Fisher/connection terms. Any map landing as phase inversion is now excluded by
`(P-G158.1)`--`(P-G158.3)`.

## Log

- 2026-08-14 — reversal-as-adjoint conjecture falsified; reciprocal conservation, complex-square
  curvature, and adapted `>16` boundary layer proved on paper and compiled in Lean scratch.
- 2026-08-14 — direct file check and
  `lake build GaloisForLFunctions.RHTower.XiWardApertureReversalCurvatureNoGo` passed; five capstone
  axiom audits returned `[propext, Classical.choice, Quot.sound]`; external novelty audit recorded.
