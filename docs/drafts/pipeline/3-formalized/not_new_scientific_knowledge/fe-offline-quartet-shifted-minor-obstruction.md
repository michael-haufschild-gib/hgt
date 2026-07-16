# FE Off-Line Quartet Shifted Minor Obstruction

- **ID:** fe-offline-quartet-shifted-minor-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/gpt/proof-route.md`, sections 4, 7, 8; `docs/consolidated/gpt/research-topics.md` topic 40
- **Statement:** A single functional-equation/conjugation-symmetric off-line quartet already makes both degree-one shifted reciprocal Hankel minors negative.

## Goal

Give the Davenport-Heilbronn gate a concrete shifted-square-test form. Functional-equation symmetry can force the quartet pattern, but it does not imply shifted Stieltjes positivity: an off-line quartet is detected by the first nontrivial shifted Hankel minors.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: unconditional reciprocal-atom coordinate identity,
  both exact shifted determinant formulas, and strict-negativity capstone
  `RHTower.seamOfflineQuartet_det_both_neg` in
  `formal/GaloisForLFunctions/RHTower/ReciprocalDiscriminantGuardrails.lean`;
  exact target build passed and the capstone audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Work in seam coordinates `w=s-1/2` and reciprocal coordinate

```text
y = -1/w^2.
```

An FE-symmetric, real-conjugation-symmetric off-line quartet has points

```text
w in { a+i gamma, -a+i gamma, a-i gamma, -a-i gamma },
```

with `a>0` and `gamma>0`. Define

```text
T_k = sum_{quartet} y^k.
```

Direct algebra gives

```text
det [[T_1,T_2],[T_2,T_3]]
  = -64 a^2 gamma^2 / (a^2+gamma^2)^6,
```

and

```text
det [[T_2,T_3],[T_3,T_4]]
  = -64 a^2 gamma^2 / (a^2+gamma^2)^8.
```

Both determinants are strictly negative when `a gamma != 0`. Therefore the degree-one shifted blocks

```text
H_1^(0) = [T_{i+j+1}]_{i,j=0}^1,
H_1^(1) = [T_{i+j+2}]_{i,j=0}^1
```

are not PSD for an off-line quartet.

At `a=0`, the quartet collapses to duplicated on-line conjugate points. Then `y=1/gamma^2` is positive and the same determinants vanish, giving the expected rank-one PSD boundary case.

## Computation

The symbolic calculation is archived in:

- `computations/2026-06-21-conway-dh-quartet-shifted-hankel.py`
- `computations/2026-06-21-conway-dh-quartet-shifted-hankel.txt`

## Route Consequence

The corrected shifted square-test theorem is not merely FE-sensitive; it is FE-gate robust. A Davenport-Heilbronn-type object with FE-like symmetry but an off-line quartet fails the shifted reciprocal Stieltjes test at degree `1`.

Thus any FE-like counterexample to RH must violate `Q_0` and `Q_1` locally at the quartet level. The remaining global proof problem is not whether the shifted tests can see an off-line symmetric quartet; they can. The hard problem is deriving global shifted positivity for the actual completed divisor from the source/explicit-formula data.

## Log

- 2026-06-21 -- Conway: created after workflow NODE "local stress concentrations near defects or boundaries dominate collapse before nominal connectivity threshold", using method 1 (split into subclaims) on the Davenport-Heilbronn gate.
