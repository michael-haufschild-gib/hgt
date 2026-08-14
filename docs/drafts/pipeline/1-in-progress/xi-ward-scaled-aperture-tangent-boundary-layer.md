# Xi Ward scaled-aperture tangent boundary layer

- **ID:** P-G157
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · Route P exterior lane; C42/C45/C49 source-codiagonal frontier
- **Statement:** The real-aperture source-row estimate `normSq(V_w(a)) <= 4 a^2` on the Euler edge is equivalent to RH; every strict-right Xi zero forces the reverse strict inequality at all sufficiently small positive apertures at its adapted node.

## Goal

Decide whether existing finite-aperture Hardy nonexpansiveness supplies the uniformly bounded
non-diagonal source row needed before singular aperture division. Identify exact homogeneity a
successful C49 incidence construction must prove, without assuming root-space orthogonality or RH.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean theorem `riemannHypothesis_iff_xiWardScaledApertureFourUnitLaw`, `lake build` green, axiom audit PASS
- [ ] 3 → 4 publication-ready: standalone paper, external novelty audit, exposition audit

## Conjecture loop

### P-G157a — finite-aperture nonexpansiveness differentiates to the four-unit row budget

**FALSIFIED.** Existing Schur/Hardy control gives an order-one estimate on `V_w(a)`. The Ward row is
obtained after division by `a` and passage to `a = 0`; an order-one bound becomes `O(1/a)` and gives
no derivative control. Ordinary finite-aperture contraction has wrong homogeneity.

### P-G157b — scaled aperture law is the exact missing hypothesis

Define

```text
XiWardScaledApertureFourUnitLaw :=
  forall t a, 0 < a -> normSq(V_(1/2+it)(a)) <= 4*a^2.
```

**[PROVED HERE].** For `w.re > 0`, `V_w(0)=0` and `V_w'(0)=r(w)`. Hence

```text
V_w(a)/a -> r(w),
normSq(V_w(a)/a) -> normSq(r(w))                 (a -> 0+).
```

The scaled law gives `normSq(V_w(a)/a) <= 4` for every positive `a`, so closedness of `(-∞,4]`
gives `normSq(r(1/2+it)) <= 4`. Euler-edge scalar completeness yields RH. Conversely RH makes the
strict-right boundary phase equal to one, hence `V_w(a)=0` for every positive real aperture and the
scaled law follows.

Therefore

```text
RiemannHypothesis <-> XiWardScaledApertureFourUnitLaw.
```

### P-G157c — off-line zeros create a whole boundary layer of violations

**[PROVED HERE].** If `q` is a strict-right upper zero copy, its adapted Euler-edge node satisfies
`normSq(r(w_q)) > 4`. Continuity of `normSq` and `V_w(a)/a -> r(w)` imply

```text
forall sufficiently small a > 0,
  4*a^2 < normSq(V_(w_q)(a)).
```

Thus failure is not an isolated aperture or endpoint artifact. Every off-line pair produces a
punctured one-sided boundary layer with super-four tangent energy.

## Hostile audit

- The equivalence does **not** prove RH; it classifies a candidate producer as RH-complete.
- The proof does not use computation, extra axioms, zero-location hypotheses, or hidden
  orthogonality. It uses corpus theorems `V(0)=0`, `V'(0)=r`, and Euler-edge completeness.
- The core equivalence alone would be a receiver restatement. New route information is the stronger
  eventual-violation theorem: finite-aperture contraction cannot be differentiated unless the
  source construction supplies uniform `O(a)` row control before singular division.
- No claim of external novelty until literature audit. Julia–Carathéodory boundary differentiation
  is classical; exact arithmetic Xi Ward boundary-layer classification may still be corpus-only.

## No-go closure

- **Exact killing mechanism:** finite Hardy nonexpansiveness is order one in aperture, while the
  continued Ward row is the singular quotient `V(a)/a`.
- **Strongest positive survivor:** exact RH equivalence of the scaled `O(a)` law plus eventual strict
  violation near every adapted off-line node.
- **New insight:** C49 cannot target mere contractivity of a prelimit incidence operator. It must
  produce a packet-uniform first-order cancellation `||V(a)|| <= 2a` before residue extraction.
  Earlier failures from ambient source gain, empty complex aperture interior, and frozen
  codiagonals are shadows of this missing tangent-scale neutrality.
- **Status:** dependency-closed paper proof; Lean module
  `RHTower/XiWardScaledApertureTangentBoundaryLayer.lean` direct-check and module-build green;
  capstones depend only on `[propext, Classical.choice, Quot.sound]`. Global lint sees this module
  through the umbrella; unrelated concurrent FieldOne/Suzuki/Sieve modules remain unreachable.

## Exact remaining producer

Construct from finite-prime/source incidence data, without importing the continued target row, a
uniform estimate of the form

```text
normSq(V_(sigma,w)(a)) <= 4*a^2 + epsilon_sigma(a,w),
epsilon_sigma(a,w)/a^2 -> 0
```

in an order of limits compatible with `sigma -> 1+` and `a -> 0+`. Any estimate only bounded by a
constant, or proved after division/landing in the Xi target, is insufficient or circular.

## Log

- 2026-08-14 — P-G157a falsified; P-G157b and P-G157c proved on paper and compiled in Lean scratch.
- 2026-08-14 — final module built (`9042/9042`); four capstone axiom audits passed; umbrella wired.
