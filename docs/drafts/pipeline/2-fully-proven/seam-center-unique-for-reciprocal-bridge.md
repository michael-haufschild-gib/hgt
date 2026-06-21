# Seam Center Unique For Reciprocal Bridge

- **ID:** seam-center-unique-for-reciprocal-bridge
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/bridge-theorem.md`, RNG-selected `Xi(w)=xi(1/2+w)`
- **Statement:** The centre `1/2` in `Xi(w)=xi(1/2+w)` is forced by the reciprocal bridge. If one uses an
  off-centre coordinate `rho-c` with real `c=1/2+eps`, `eps != 0`, then FE pairs no longer fold to one
  reciprocal atom, and even RH-line zeros no longer map to positive real reciprocal atoms.

## Goal

Make the seam centering load-bearing. The bridge theorem is not invariant under resetting the origin before
forming

```text
y = -(rho-c)^(-2).
```

The centre must be the FE fixed seam `c=1/2`.

## Gates

- [x] 0 -> 1 in-progress: bridge-theorem variable selected by RNG and checked against reset-centre prior probe
- [x] 1 -> 2 fully-proven: algebraic proof complete
- [ ] 2 -> 3 formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 -> 4 publication-ready: fold into bridge-coordinate guardrails

## Proof

[PROVED HERE]

Let the true seam coordinate be

```text
w = rho - 1/2.
```

The functional equation sends `w` to `-w`. Now reset the centre to

```text
c = 1/2 + eps,
```

so the two members of an FE pair have shifted coordinates

```text
w - eps,       -w - eps.
```

The off-centre reciprocal atoms are

```text
y_+(eps) = -(w-eps)^(-2),
y_-(eps) = -(-w-eps)^(-2).
```

They are equal iff

```text
(w-eps)^2 = (w+eps)^2,
```

which is equivalent to

```text
4 w eps = 0.
```

For a nonzero zero orbit, `w != 0`, so equality for the FE pair forces `eps=0`. Therefore only the seam
centre makes every FE pair fold to one reciprocal atom.

The RH-positive direction also forces the same centre. If RH holds, then `w=i gamma` with `gamma != 0`.
The off-centre reciprocal atom is

```text
y_eps = -(i gamma - eps)^(-2).
```

Writing out its imaginary part gives

```text
Im y_eps
  = -2 eps gamma / ((eps^2-gamma^2)^2 + 4 eps^2 gamma^2).
```

Thus `y_eps` is non-real whenever `eps gamma != 0`. In particular, if `eps != 0`, even an RH-line zero is
sent away from the positive real axis.

At `eps=0`, the usual bridge coordinate gives

```text
y_0 = -(i gamma)^(-2) = gamma^(-2) > 0,
```

and FE pairs fold exactly. Hence `c=1/2` is the unique real centre compatible with both FE folding and the
Stieltjes positivity interpretation.

## Computation

The algebra was checked numerically at:

- `computations/2026-06-21-conway-seam-center-uniqueness.py`
- `computations/2026-06-21-conway-seam-center-uniqueness.txt`

The script verifies

```text
y_+(eps)-y_-(eps) = -4 w eps / (w^2-eps^2)^2
```

and the displayed formula for `Im y_eps`.

## Route Consequence

The bridge coordinate is not a family of equivalent reciprocal charts. It is the chart built from the FE
fixed seam:

```text
Xi(w)=xi(1/2+w),       y= -w^(-2).
```

Moving the centre creates two errors at once:

```text
FE pair folding fails;
RH no longer maps to positive real atoms.
```

Thus any source-built proof of shifted square-test positivity must keep the seam-centred completion before
forming reciprocal squares.

## Log

- 2026-06-21 -- Conway: created from bridge-theorem RNG draw `60/78`, `Xi(w)=xi(1/2+w)`.
