# Y-Plane Quartet Minors Are Imaginary-Defect Squares

- **ID:** y-plane-quartet-minor-imaginary-defect
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), bridge-coordinate refinement
- **Source:** random bridge-theorem inline draw 46/72, `y_ρ` in `docs/consolidated/revision01/bridge-theorem.md`
- **Statement:** In the reciprocal seam coordinate `y_ρ`, a folded conjugate pair of non-real atoms has first shifted Hankel minors

```text
det H_1^(0) = -4 mu^2 |y|^2 (Im y)^2,
det H_1^(1) = -4 mu^2 |y|^4 (Im y)^2,
```

where `mu` is the weight of each conjugate `y` atom. Thus the local shifted-square-test obstruction is exactly the square of the off-axis height in the `y`-plane.

## Goal

Make the bridge theorem's coordinate `y_ρ = -(ρ-1/2)^(-2)` carry the local obstruction intrinsically. The earlier quartet card gave the determinant in the original seam variables `(a,gamma)`. This card records the coordinate-free `y`-plane form and shows that `Im y` is the degree-one local obstruction.

## Gates

- [x] 0 -> 1 in-progress: bridge-theorem variable selected by RNG and checked against quartet/folding prior work
- [x] 1 -> 2 fully-proven: algebraic proof complete
- [x] 2 -> 3 formalized: unconditional determinant identities
  `RHTower.reciprocalConjugatePair_det_zero` and
  `RHTower.reciprocalConjugatePair_det_one`, with strict-negativity capstone
  `RHTower.reciprocalConjugatePair_det_both_neg`, in
  `formal/GaloisForLFunctions/RHTower/ReciprocalDiscriminantGuardrails.lean`;
  exact target build passed and the capstone audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- [ ] 3 -> 4 publication-ready: fold into the reciprocal-coordinate bridge exposition

## Proof

[PROVED HERE]

Let one FE-folded conjugate pair in the reciprocal coordinate be

```text
y = u + i v,        conjugate(y) = u - i v,
```

with equal reciprocal atom weight `mu`. Its local moments are

```text
T_k = mu (y^k + conjugate(y)^k).
```

Then

```text
T_1 = 2mu u,
T_2 = 2mu(u^2-v^2),
T_3 = 2mu(u^3-3uv^2),
T_4 = 2mu(u^4-6u^2v^2+v^4).
```

A direct calculation gives

```text
det [[T_1,T_2],[T_2,T_3]]
  = T_1 T_3 - T_2^2
  = -4 mu^2 (u^2+v^2) v^2
  = -4 mu^2 |y|^2 (Im y)^2,
```

and

```text
det [[T_2,T_3],[T_3,T_4]]
  = T_2 T_4 - T_3^2
  = -4 mu^2 (u^2+v^2)^2 v^2
  = -4 mu^2 |y|^4 (Im y)^2.
```

Therefore any non-real reciprocal conjugate pair with nonzero weight violates both degree-one shifted square tests.

For a simple FE/conjugation quartet in seam variables

```text
w = ±a ± i gamma,
y = -(a+i gamma)^(-2),
```

the FE fold gives `mu=2`. Also

```text
Im y = 2a gamma/(a^2+gamma^2)^2,
|y|^2 = 1/(a^2+gamma^2)^2.
```

Substituting recovers the bridge-theorem quartet formula:

```text
det H_1^(0) = -64 a^2 gamma^2/(a^2+gamma^2)^6,
det H_1^(1) = -64 a^2 gamma^2/(a^2+gamma^2)^8.
```

The on-line boundary has `Im y=0` with `y>0`, so these local determinants vanish in the expected rank-one PSD way. A hypothetical negative real reciprocal atom would be excluded already by lower shifted tests such as `Q_0[1]`; the present theorem is the non-real off-axis obstruction relevant to FE quartets with `a gamma != 0`.

## Route Consequence

The reciprocal coordinate is not just a convenient reparametrization. It identifies the first local shifted-square-test defect as the `y`-plane imaginary height. This is the intrinsic version of the bridge theorem's statement that off-line zeros are off-axis atoms.

It also explains the scale of the local witness. In seam variables, the imaginary height is

```text
|Im y| = 2|a gamma|/(a^2+gamma^2)^2,
```

so high zeros or near-line quartets can have very small degree-one defects even though the sign is strictly negative. Finite numerical audits should therefore track the `y`-plane scale of the defect, not just the original horizontal displacement `a`.

## Computation

The symbolic audit is archived at:

- `computations/2026-06-21-conway-y-plane-quartet-minors.py`
- `computations/2026-06-21-conway-y-plane-quartet-minors.txt`

## Log

- 2026-06-21 -- Conway: created from RNG draw of bridge-theorem variable `y_ρ`. Cross-reference: `fe-offline-quartet-shifted-minor-obstruction.md` gives the `(a,gamma)` formula; this card gives the intrinsic `y`-plane invariant form.
