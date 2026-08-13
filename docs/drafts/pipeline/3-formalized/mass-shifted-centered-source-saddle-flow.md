# Mass-shifted centered-source saddle flow

- **ID:** `mass-shifted-centered-source-saddle-flow`
- **Stage:** 3-formalized
- **Route:** U, mixed mass--degree source transport
- **Type:** THEOREM / SIGN CLASSIFICATION
- **Scientific status:** `[LEAN-PROVED] [CORPUS-NOVEL] [EXTERNAL NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** `mass-shifted-centered-source-degree-capital`, canonical hard-edge
  worldline/source conservation, positive normalized terminal mass

## Frozen claim

Along every differentiable nonzero canonical shifted-Xi root worldline inside a positive finite
admission chamber, reciprocal hard coordinate

```text
u(y) = x(y)^(-1) - y
```

has strictly positive derivative. If node is super-apex, `1 < y*x(y)`, then its literal centered
source residue local model

```text
R(y) = (y*x(y))^2 - 1
```

has strictly negative derivative. Combined with strict fixed-mass degree capital, Route-U centered
source has saddle geometry: degree renewal increases residue; mass transport decreases it.

## Conjecture -> proof/fail loop

1. **Continuous mass transport might preserve or increase a super-apex residue.** Falsified.
   Worldline/source conservation says `u'(y) M(y)=2 n y x(y)^2`, and normalized terminal mass
   `M(y)` is positive. Hence `u'(y)>0`.
2. **Positive hard-coordinate velocity may be insufficient to sign centered residue.** Falsified
   on super-apex branch. `u'(y)>0` is equivalent to `x'(y)<-x(y)^2`. Therefore
   `(y x(y))' = x(y)+y x'(y) < x(y)(1-yx(y)) < 0`.
3. **Mass and degree signs alone close Route U.** Falsified as inference. They oppose one another.
   Without an exact magnitude budget, a moving-degree path can balance arbitrary discrete gain
   against continuous loss.

## Dependency-closed paper proof `[PROVED HERE]`

Put `V=-x'/x^2-1`. Canonical source/worldline conservation and normalized terminal-mass
positivity give

```text
V * M = 2*n*y*x^2 > 0,
M > 0,
```

so `V>0`. Existing reciprocal-root chain rule identifies `V=u'(y)`.

For `q(y)=y*x(y)`, ordinary product differentiation gives `q'=x+yx'`. From `V>0` and `x^2>0`,

```text
1 < -x'/x^2,
x' < -x^2.
```

If `x>0` and `1<yx`, then

```text
q' < x-yx^2 = x(1-yx) < 0.
```

Since `q>0`, derivative of `R=q^2-1` is `R'=2q q'<0`. Exact de-resistance identifies current
literal centered completed-source residue with `R(y)` at admitted root. Fixed-mass degree-capital
theorem gives a next-degree node with strictly larger literal residue. Thus signs are opposite and
fully source-native.

No computation, limit, RH premise, post-aggregation reporter, or free sign assumption enters.

## Exact residual

Construct quantitative mixed balance comparing finite degree gain with integral continuous mass
loss. Any theorem asserting only persistence, positivity, or one-sided signs is now insufficient.
Correct invariant must retain source magnitude along alternating mass and degree steps.

## Lean certificate `[LEAN-PROVED]`

`RHTower/XiShiftedCanonicalAdmissionCenteredSourceSaddleFlow.lean` proves:

- positive reciprocal hard-coordinate velocity from canonical source/worldline conservation;
- exact derivative of moving centered root residue;
- strict negativity on every positive super-apex branch;
- literal shifted-Xi centered-source identification together with that negative derivative.

The module is wired into `GaloisForLFunctions.RHTower`.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionCenteredSourceSaddleFlow.lean
lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredSourceSaddleFlow
✔ [11851/11851] Built GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredSourceSaddleFlow
```

`#print axioms` for all five exported capstones reports only
`[propext, Classical.choice, Quot.sound]`; no project axiom, `sorry`, `admit`, `opaque`, or
`unsafe` declaration is used.
