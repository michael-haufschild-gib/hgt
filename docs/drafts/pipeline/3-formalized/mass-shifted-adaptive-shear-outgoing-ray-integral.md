# Mass-shifted adaptive shear outgoing-ray integral

- **ID:** `mass-shifted-adaptive-shear-outgoing-ray-integral`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / EXACT RH CONSUMER
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3
- **RH used:** no
- **Computation used:** no

## Goal

Close analytic infrastructure between source-first derivative

```text
B_A'(y) = -2 S_A(y),
B_A(y)  = L_y(A * X*A),
S_A(y)  = L_y((X*A) * (X*E_1 A)),
```

and odd-contact exclusion. Prove actual improper-integral identity from corpus primitives, not a
formal placeholder or fixed reporter.

## Conjecture loop

1. **Local nonnegative shear at contact suffices.** **FAIL.** One derivative value controls no
   outgoing interval; successor defect is free.
2. **Far-right positivity of fixed Hankel blocks supplies shear sign.** **FAIL.** It signs square
   forms, not adaptive mixed shear.
3. **Nonnegative adaptive shear on the entire outgoing ray forces odd current nonnegative.**
   **PROVED ON PAPER AND IN LEAN.** Shifted moments vanish at infinity, source law gives `B_A'=-2S_A`, and
   semi-infinite FTC gives `B_A(y)=2∫_(y,∞) S_A(v)dv ≥ 0`.
4. **The all-ray sign follows from contact data.** **FAIL SHARPLY.** Existing adjacent-defect
   perturbation changes source shear arbitrarily while keeping every coordinate through contact.
   Required hypothesis is arithmetic and source-specific.

## Exact target

For `y>0`, fixed polynomial `A`, and

```text
∀ v > y, 0 ≤ L_v((X*A) * (X*E_1 A)),
```

prove

```text
L_y(A * X*A)
  = 2 * ∫ v in Ioi y, L_v((X*A) * (X*E_1 A)).
```

Therefore a genuine odd contact, where left side is strictly negative, is impossible under this
one all-ray arithmetic source inequality.

## Strongest positive survivor `[PROVED HERE]`

Every negative odd current forces a later strictly negative source shear:

```text
B_A(y) < 0
  → ∃ v > y, S_A(v) < 0
  → ∃ v > y, CompletedAdaptivePsharp_A(v) < 0.
```

For a genuine shifted-Hankel crossing above quarter mass, this is already an entirely
pre-aggregation arithmetic statement: there are admitted `A=P X^m` and `w>1/2`, `y<w²`, with

```text
ArchAggregate(w,A) + ChebyshevDiscrepancyAggregate(w,A) < 0.
```

Thus missing theorem is not local contact orientation. It is exclusion of a negative completed
adaptive source packet anywhere downstream of the admitted null flag.

## Lean closure

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearRayIntegral
```

Formalized unconditionally:

- atomwise shifted reciprocal extinction at `+∞`;
- dominated-convergence extinction of every shifted moment;
- extinction of every finite polynomial moment functional and pairing;
- genuine outgoing-ray integrability of nonnegative adaptive shear;
- exact improper-integral identity `B_A(y)=2∫_(y,∞)S_A`;
- negative-shear and negative-completed-packet propagation;
- genuine-crossing negative pre-aggregation arithmetic packet.

Umbrella import: wired.

Final audit: PASS.

```text
lake env lean GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryAdaptiveShearRayIntegral.lean
lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearRayIntegral
scripts/formal_tools.py lint
```

Axiom print for five main declarations: only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining arithmetic theorem

All-ray nonnegativity of completed adaptive mixed shear for amplitudes admitted by an actual null
flag. It must consume ℤ-specific source structure before aggregation; adjacent-defect data,
generic positivity, and fixed finite observation cannot prove it.
