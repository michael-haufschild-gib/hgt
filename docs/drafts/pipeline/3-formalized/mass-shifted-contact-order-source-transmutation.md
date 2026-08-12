# Mass-shifted contact-order arithmetic-source transmutation

- **ID:** `mass-shifted-contact-order-source-transmutation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / ARITHMETIC SOURCE PRODUCER / CORRECTED NO-GO SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL CAPSTONE] [EXTERNAL PRIORITY UNVERIFIED] [NOT RH]`
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** At a positive flat canonical shifted-Xi face, first-order inverse-Hankel admission is exactly degree-lowered Möbius tangent, hence every simple hard Gauss coordinate freezes to first order; at tangency arithmetic forcing survives as adaptive completed `P^sharp` norm-flux derivative before reflection aggregation.

## Goal

Replace false absolute-terminal-mass/speed inference by source-pure law valid at singular face
itself. Producer uses actual shifted-Xi moment differentiation and canonical inverse-Hankel
admission before reflection aggregation. No fixed linear observer and no chosen null orientation
enter.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module green, axioms audited, umbrella wired
- [ ] 3 → 4  publication-ready: standalone paper not prepared

## Failed conjecture and no-go closure

- **Conjecture:** Absolute terminal-mass extinction forces nonproper hard-root speed escape.
- **Status:** `[FALSIFIED]`.
- **Exact killing mechanism:** Worldline conservation controls relative mass `Gamma/h_n` only in
  positive chamber. Route U uses absolute `Gamma`; at flat face `h_n=0`. Therefore `Gamma -> 0`
  does not imply `Gamma/h_n -> 0` or speed blow-up.
- **Strongest positive survivor:** Relative mass is exact inverse mobility in positive chamber. At
  flat face first-order hard-root mobility vanishes identically and arithmetic source moves to
  higher norm-flux/contact jet.
- **New insight:** Obstruction is contact-order transmutation, not nonproper escape.

## Paper proof `[PROVED HERE]`

Fix `y=y₀>0`, `n>0`, moment sequence `s`, canonical monic inverse-Hankel admission `P`, and its
coefficient velocity `V`. Assume leading `n` Hankel block is positive definite and canonical
coefficient vector lies in kernel of next `(n+1)` block.

For every lower polynomial `Q`, differentiating canonical orthogonality with literal shifted-Xi
moment ODE gives half-density adjoint law

```text
<V-KP,Q> = <P,KQ>,       KQ = X^2 Q' + (1/2) XQ.
```

This requires only head positivity: it makes solve block locally nonsingular, so lower
orthogonality persists in neighborhood and its derivative is zero.

Let

```text
R = X^2 P' - n X P + coeff(P,n-1) P.
```

Top two coefficients cancel, so `degree R<n`; also `degree V<n`. Put `D=V-R`. Then `degree D<n`
and `degree KD<n+1`. Flat kernel annihilates `P` against `D`, `XD`, and `KD`. Expanding adjoint law
with `Q=D` yields

```text
<D,D>=0.
```

Head positivity forces `D=0`, hence

```text
V = X^2 P' - n X P + coeff(P,n-1) P.                      (COST.1)
```

At a root `P(x)=0`, `(COST.1)` becomes `V(x)=x^2 P'(x)`. For differentiable simple root branch,
implicit chain rule gives

```text
x'=-x^2,
(x⁻¹-y)'=0.                                                (COST.2)
```

If first odd remainder also vanishes, existing singular producer law gives

```text
NormFlux'=(2n+1) * CompletedAdaptivePsharpSource.           (COST.3)
```

Combining `(COST.2)` and `(COST.3)` is exact contact-order transmutation: first-order hard-root
reporter freezes while source-first adaptive aggregate remains active in higher norm-flux jet.

## Hostile loop

1. **C1: absolute mass extinction forces speed escape.** `[FALSIFIED]` Absolute/relative scale
   mismatch at `h_n=0`.
2. **C2: flat source contact freezes hard coordinate to first order.** `[PROVED]` Equations
   `(COST.1)`–`(COST.2)`.
3. **C3: adaptive completed source disappears with frozen hard root.** `[FALSIFIED]` Exact
   `(COST.3)` lands it in norm-flux derivative.
4. **C4: higher source orientation anchors root level.** `[FALSIFIED BY EXISTING COMPLETE-JET
   AUDIT]` Derivative/level separation remains; contact sign alone does not prove `u(y₀)>=0`.

## Higher universal principle

```text
open-chamber relative mass × mobility = source forcing
singular-face mobility = 0
singular-face source forcing = higher contact-order norm-flux jet
```

Positive chamber and flat face are different charts. Dividing by vanishing orthogonal norm erases
boundary source. Division-free adaptive flux retains it.

## Exact remaining burden

Route split is now exact:

1. positive terminal mass: prove source-derived positive-axis Padé-atom extinction/local
   boundedness;
2. zero terminal mass: exploit parity-doubled radical and first nonzero higher contact source.

No speed theorem alone bridges either branch. RH remains open.

## External novelty audit

Broad arXiv audit covered Möbius-transformed orthogonal polynomials, Markov zero-variation laws,
Christoffel/Geronimus moment transformations, and nonisospectral Toda/Painlevé deformations. These
are adjacent but do not state shifted-Xi flat-Hankel coefficient rigidity plus singular adaptive
completed-source transmutation. No direct collision found; external priority remains unverified.

## Lean realization

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionFlatContactSourceTransmutation
```

Capstones:

```text
momentInner_xiShiftedCanonicalAdmissionCovariantVelocity_eq_generatorAdjoint_of_headPosDef
finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_normRemainder_of_flatFace
finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root_of_flatFace
xiShiftedCanonicalAdmission_flatRootCurve_deriv_eq_neg_sq
hasDerivAt_xiShiftedCanonicalAdmission_reciprocalHardRoot_zero_of_flatFace
xiShiftedCanonicalAdmission_flatTangent_hardRootFreeze_and_completedSource
```

## Verification

- direct `lake env lean` on route module: PASS;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionFlatContactSourceTransmutation`: PASS;
- `#print axioms` for all six capstones: only `propext`, `Classical.choice`, `Quot.sound`;
- `scripts/formal_tools.py lint`: PASS in current invocation;
- RHTower umbrella import wired;
- no `sorry`, `admit`, new `axiom`, `opaque`, `unsafe`, or computations.

## Door passport

- **Door-1 source purity:** shifted-Xi reciprocal moment ODE; inverse-Hankel monic admission;
  Hankel flatness; adaptive completed `P^sharp` aggregate.
- **Door-2 proof:** finite polynomial/Hankel algebra, neighborhood persistence of head positivity,
  and differentiable root chain rule.
- **No forbidden shortcut:** no RH-equivalent positivity, numerical tracking, fixed reporter,
  post-hoc null orientation, or generic speed compactness.

## Log

- 2026-08-12 — hostile scale audit falsified speed-escape interpretation.
- 2026-08-12 — paper proof closed and all significant survivors formalized in Lean.
