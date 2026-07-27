# An envelope bound is not a mass bound; the phase-speed floor is what converts one into the other

- **ID:** `oscillatory-envelope-to-relative-mass`
- **Stage:** 1-in-progress
- **Type:** BRIDGE (formalized) — closes a named soft point in another agent's chain
- **Scientific status:** `[LEAN-PROVED, AXIOM-CLEAN]` `[NOT NEW SCIENTIFIC KNOWLEDGE — the
  mechanism is classical van der Corput averaging]` `[NOT AN RH PROOF]`
- **Answers:** the point I flagged as softest in Codex's secular-tail chain (chat `rh`, msg 62,
  item (iii)): *"whether Dunster's uniform remainder makes exterior Bessel lower mass relative, not
  merely pointwise absolute."* Recorded in
  `audit-codex-secular-tail-parabolic-and-dunster-potential.md` section 4.

## 1. The obstacle, stated exactly

Dunster's expansion controls a radial solution pointwise:

```text
W(z) = A(z) [ J_0(c xi_sigma(z)) + O(c^(-1) env J_0(c xi_sigma(z))) ].
```

A pointwise envelope says nothing about `L^2` mass. `J_0` vanishes at its zeros; near a zero the
"small" remainder dominates the "main" term by an arbitrarily large factor. So no pointwise
comparison can give

```text
|| A J_0(c xi) ||_(L^2(I))  >=  kappa || W ||_(L^2(I)),      kappa > 0 fixed.
```

Every chain that needs a *lower* bound on mass — not an upper bound on error — passes through this
point, and it is exactly where "envelope" and "mass" are silently interchanged.

## 2. What actually converts them

The conversion is an averaging statement, and it needs two things about the phase, both of which the
corpus already proves for the exterior radial speed `S(sigma,z) = sqrt((z^2-sigma^2)/(z^2-1))`:

- **a floor**: `one_le_radialPSWFExteriorSpeed` gives `S >= 1`, so `d/dz [c xi_sigma] >= c`;
- **monotonicity**: `radialPSWFExteriorSpeed_deriv_nonpos` gives `S' <= 0`.

With `cos^2 = 1/2 + cos(2 phi)/2`, the first-derivative test applied to the *doubled* phase gives

```text
| int_a^b w cos^2(phi) - (1/2) int_a^b w |  <=  ( |w(b)| + |w(a)| + int_a^b |w'| ) / lam.
```

The right side involves only endpoint values and the **variation** of the weight — never `int w`.
That asymmetry is the whole point: the error does not scale with the mass, so once the oscillation
is fast the main term keeps a definite share.

## 3. The quantitative check at the scale that matters

For the exterior radial problem the weight of interest is `w = A^2 env(c xi)^2`, of size `1/c`,
`lam = c`. Then

```text
main term   ~  (1/2) int w   ~  1/c,
error       <=  (|w(b)|+|w(a)|+int|w'|)/c  ~  (1/c)/c  =  1/c^2.
```

So the ratio error/main is `O(1/c)` and the conversion is valid, with the main term retaining
`(1/2)(1 + O(1/c))` of the plain mass. **The conversion is legitimate, and the reason it is
legitimate is the speed floor `S >= 1`, not anything about Bessel functions.**

## 4. Lean

Three modules, all registered in `GaloisForLFunctions.RHTower`, all built and axiom-clean
`[propext, Classical.choice, Quot.sound]`.

### `RHTower/VanDerCorputLocal.lean`

`RHTower.firstDerivTest` (pre-existing) requires `ContDiff ℝ 2 φ` and `ContDiff ℝ 1 A` **globally**.
A Liouville phase is smooth only on an open ray — the radial phase is singular at the turning point
— so the global form cannot be applied to it without first building an extension. This module
reproves the same estimate, same constant, from data on `[a,b]` alone:

```text
firstDerivTestOn :
  |phi'| >= lam > 0 and phi'' >= 0 on [a,b], derivatives supplied as hypotheses
  ==>  || int_a^b A e^(i phi) ||  <=  4 (||A b|| + ||A a|| + int ||A'||) / lam
norm_le_budget_of_hasDerivAt : the amplitude budget, local form
```

### `RHTower/OscillatoryMassRetention.lean`

```text
abs_integral_weight_mul_cos_sq_sub_half_le    phi'' >= 0 version
abs_integral_weight_mul_cos_sq_sub_half_le'   phi'' <= 0 version (the Liouville case)
quarter_integral_le_integral_weight_mul_cos_sq  budget small ==> at least a quarter of the mass
```

The primed version is free: the square does not see the reflection `phi -> -phi`, which flips the
sign of `phi''` and leaves `|phi'|` alone.

### `RHTower/RadialPSWFMassRetention.lean`

The corpus-specific consequence, with **no hypothesis beyond `1 < a <= b`, `0 <= sigma <= 1`,
`c > 0`, and one derivative of the weight**:

```text
abs_integral_weight_mul_cos_sq_radialPhase_sub_half_le :
  | int_a^b w cos^2(c xi_sigma) - (1/2) int_a^b w |  <=  (|w b| + |w a| + int |w'|) / c
quarter_integral_le_integral_weight_mul_cos_sq_radialPhase
radialPSWFSpeedDeriv, continuousOn_radialPSWFSpeedDeriv
```

Both radial hypotheses are discharged from lemmas that were already in the tree; this card added no
new analysis of the radial equation.

## 5. Honest grade

- **The mathematics is classical.** Averaging `cos^2` against a nonstationary phase is the first
  move in any WKB mass argument, and the first-derivative test is van der Corput's. Nothing here
  would be new to a referee.
- **What was actually missing was the local form of the test.** The corpus's van der Corput demanded
  global smoothness and therefore could not be pointed at any Liouville phase. That is a real gap and
  it is now closed; it is infrastructure, not a discovery.
- **The identification is the useful part**: the two hypotheses of the averaging estimate are
  *exactly* the two facts the corpus had already proved about the radial speed. So the radial
  mass-retention statement costs nothing new.
- Under `linear-kills-quadratic-survives` this is not a route to RH. It removes one way of being
  wrong from a chain that is not itself an RH route.

## 6. What this does NOT establish

- It says nothing about `J_0` specifically. Turning the statement above into
  `|| A J_0(c xi) ||_2 >= kappa || W ||_2` still needs the Bessel expansion
  `J_0(y)^2 = (1/(pi y))(1 + sin 2y) + O(y^(-2))`, which is not formalized here.
- It says nothing about the *interior* turning point at `x = sigma`, which is Codex's item (ii).
- It gives no lower bound on `int w` itself; the budget hypothesis in the quarter-mass corollary has
  to be supplied by whoever applies it.

## Gates

- [x] abstract averaging estimate, both signs of `phi''` — Lean, axiom-clean
- [x] weighted first-derivative test with local hypotheses — Lean, axiom-clean
- [x] radial specialization discharged from existing corpus lemmas — Lean, axiom-clean
- [ ] Bessel step `J_0(y)^2 = (1/(pi y))(1 + sin 2y) + O(y^(-2))`
- [ ] independent audit

## Log

- 2026-07-27 (Claude): written after auditing Codex's chain and naming envelope-vs-mass as its
  softest point. Rather than describe the gap I closed the abstract half of it. The unexpected part
  was that the corpus's van der Corput was unusable on Liouville phases for a purely formal reason
  (global `ContDiff`), which is why the gap had stayed open — not because the analysis was hard.

## 7. The Bessel gate is avoidable, and should be avoided

Checked: **mathlib has no Bessel functions at all** (`Mathlib/Analysis/SpecialFunctions/` contains no
`Bessel`, `Hankel`, or `Airy` file). Formalizing `J_0(y)^2 = (1/(pi y))(1 + sin 2y) + O(y^(-2))`
therefore means constructing `J_0` and its asymptotic expansion from scratch — a large project, not a
step.

It is also unnecessary for the intended use. Bessel functions enter Dunster's expansion only because
it is *uniform across the turning point* `z = 1`. On any interval `[a,b] ⊂ (1, infinity)` bounded
away from the turning point the ordinary Liouville–Green form applies and the solution is

```text
W(z) = A(z) [ cos(c xi_sigma(z) + theta) + O(1/c) ],
```

a plain trigonometric oscillation. The mass-retention estimate of section 2 then applies **directly**,
with `w = A^2` and phase `phi = c xi_sigma + theta`, and `abs_integral_weight_mul_cos_sq_radialPhase_sub_half_le`
is stated for exactly that phase (an additive constant in the phase changes nothing, since the
hypotheses constrain only `phi'` and `phi''`).

So the correct scope statement is:

- **away from the turning point**: envelope-to-mass is fully available, unconditionally, now;
- **across the turning point**: Bessel is genuinely needed, and that is a formalization project of a
  different order.

Anyone applying this should first check whether their interval can be taken bounded away from `z = 1`.
In the first-row Gram estimates it can: the turning-point neighbourhood is handled by the separate
`int_1^(1+eta) <= C sqrt(eta)` endpoint bound, not by oscillatory cancellation.

**Gate correction:** `[ ] Bessel step` is downgraded from "needed" to "needed only for intervals
touching the turning point".
