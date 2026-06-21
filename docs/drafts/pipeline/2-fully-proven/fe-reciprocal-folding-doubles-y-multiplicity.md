# FE Reciprocal Folding Doubles Y-Multiplicity

- **ID:** fe-reciprocal-folding-doubles-y-multiplicity
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** docs/consolidated/gpt/proof-route.md, reciprocal variable `y_rho=-(rho-1/2)^(-2)`
- **Statement:** In the reciprocal variable `y=-w^{-2}`, the functional-equation pair `w` and `-w` folds to the same atom. Thus a nonzero zero orbit contributes even reciprocal multiplicity to each `y` atom; an off-line quartet contributes weight `2m` to each conjugate `y` atom.

## Goal

Prevent proof-route experiments from testing inadmissible "simple" conjugate atoms in the reciprocal `y` plane. The completed divisor's FE symmetry changes the reciprocal multiplicity before any positivity test is applied.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Write the completed zero coordinate as

```text
w = rho - 1/2.
```

The functional equation makes `Xi(w)=xi(1/2+w)` even. Hence if `w != 0` is a zero of multiplicity `m`, then `-w` is also a zero of multiplicity `m`.

The reciprocal proof-route variable is

```text
y = -w^(-2).
```

But

```text
-(-w)^(-2) = -w^(-2).
```

Therefore the FE pair `{w,-w}` maps to one and the same reciprocal atom `y`, with total reciprocal weight `2m`.

If the zero is off the critical line and not on a symmetry axis, conjugation gives the quartet

```text
{w, -w, conjugate(w), -conjugate(w)}.
```

The first FE pair contributes weight `2m` at `y=-w^(-2)`, and the conjugate FE pair contributes weight `2m` at `conjugate(y)`.

If the zero is on the critical line with `w=i gamma`, the FE pair `{i gamma,-i gamma}` contributes weight `2m` at the positive atom

```text
y = gamma^(-2).
```

So the reciprocal square-test measure is a folded divisor measure, not a support-only list of simple `y` atoms.

## Consequence

The witness in `reciprocal-square-tests-need-divisor-multiplicity.md` is not just a toy warning. Its pair-weight `c=1` case is not FE-admissible for an off-line quartet, while `c=2` is the minimal FE-folded off-line weight. Experiments that test a single conjugate `y` pair with unit weights undercount the completed divisor's off-line contribution.

## Log

- 2026-06-21 -- created in 2-fully-proven as a follow-up to the multiplicity/support invariant run.
