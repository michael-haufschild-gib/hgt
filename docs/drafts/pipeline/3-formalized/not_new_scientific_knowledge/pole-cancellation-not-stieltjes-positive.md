# Pole Cancellation Does Not Imply Stieltjes Positivity

- **ID:** pole-cancellation-not-stieltjes-positive
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/revision01/proof-route.md`
- **Statement:** A cancellation/renormalization step that only removes an infinite scalar term need not preserve Hankel positivity. Therefore a bridge theorem from completion + explicit formula + pole cancellation to Stieltjes positivity must prove positivity preservation on square test functions, or move to a shifted finite moment space.

## Goal
Prevent a false bridge proof: finiteness of the completed/renormalized moments is not the same thing as Stieltjes positivity.

## Countermodel
For `L > 0`, let

```text
mu_L = L delta_0 + delta_1.
```

Its first moments are

```text
m_0 = L + 1,  m_1 = 1,  m_2 = 1.
```

The cutoff Hankel matrix

```text
[[m_0, m_1],
 [m_1, m_2]]
```

is PSD for every `L > 0`, since its determinant is `L`.

Now perform a naive cancellation of the divergent zeroth mass by setting

```text
m_0^ren = 0,  m_1^ren = 1,  m_2^ren = 1.
```

The renormalized Hankel determinant is

```text
det [[0,1],[1,1]] = -1.
```

Equivalently, for `p(y)=1-y`, the cutoff quadratic form is

```text
int p(y)^2 dmu_L = L >= 0,
```

but the renormalized quadratic form is

```text
0 - 2 + 1 = -1.
```

Thus cancellation of the infinite `T_0`-type contribution can destroy positivity.

## Consequence
The desired proof-route bridge

```text
completion + explicit formula + pole cancellation => {T_k} Stieltjes
```

cannot be proved by finiteness/cancellation alone. It must prove one of:

1. the induced renormalization is positive on all squares;
2. the argument works in the shifted finite moment space `[T_{i+j+1}]`;
3. a finite-window limiting theorem preserves PSD before the limit;
4. a specified `T_0` finite-part is compatible with all Hankel minors.

## Formalization

The unconditional theorem
`HTGeometry.poleCancellation_can_destroy_momentPositivity` in
`formal/GaloisForLFunctions/HTGeometry/HankelGuardrailConsequences.lean`
constructs the positive cutoff measure, proves its full moment representation,
preserves every positive-degree moment under cancellation, and proves that the
cancelled sequence has no positive representing measure. The exact target
build passed. The recursive capstone axiom printer was resource-bounded, while
the formal lint scan found no forbidden declaration in this proof or its
project dependencies.

## Computation
Artifacts:

- `computations/2026-06-21-penrose-proof-r02-renormalization-positivity-obstruction.py`
- `computations/2026-06-21-penrose-proof-r02-renormalization-positivity-obstruction.txt`

## Log
- 2026-06-21 -- Penrose: created from proof-route node 6 after workflow NODE "renormalization group is a change of description, not merely a trick for removing infinities."

## 2026-06-24 finite hard-edge counterterms cannot hide shifted bad atoms

`finite-hard-edge-counterterm-q0-rh-strength.md` gives the shifted `Q_0` counterpart to this `T_0` warning. A finite hard-edge counterterm may alter low-order or unshifted presentation, but if it vanishes on `y^m R[y]`, it cannot affect polynomials used to isolate any reciprocal atom away from `0`. Therefore all-order positivity of the shifted form plus such a finite counterterm remains RH-strength.
