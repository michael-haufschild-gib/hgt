# Shifted-Xi projective vacuum-curvature cancellation

- **ID:** `shifted-xi-projective-vacuum-curvature-cancellation`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM + NO-GO + POSITIVE SURVIVOR
- **Status:** `[LEAN-PROVED] [DEPENDENCY-CLOSED] [CORPUS-NOVEL] [NOVELTY UNVERIFIED] [NOT RH]`
- **External parent theory:** parameter-dependent orthogonal-polynomial recurrences have standard
  Lax/zero-curvature formulations; see Bertola--Gekhtman,
  [arXiv:nlin/0503050](https://arxiv.org/abs/nlin/0503050), and
  Alvarez-Fernandez--Mañas, [arXiv:1202.2898](https://arxiv.org/abs/1202.2898). Ratio recession for
  slowly varying recurrence coefficients is part of the Nevai-class literature; see
  Delvaux--Dette, [arXiv:1108.5155](https://arxiv.org/abs/1108.5155). None of these sources supplies
  the literal shifted-Xi arithmetic source or the constants below.

## Exact claim

For `m>=1`, set

```text
B_m(y) = beta_(m+1)(y),
R_m(y) = A_m(y)/A_(m+1)(y),
C_m(y) = B_m'(y) R_m(y) + y^(-2) + alpha_(m+1)'(y).
```

Here `A_m(y)=P_m(y,1/y)` is the shifted-Xi characteristic-apex coordinate. Then, without an RH
premise or any numerical input,

```text
w^4 C_m(w^2) -> 0.                                      (C1)
```

Moreover, on the eventual positive chamber,

```text
C_m = (W_(m+1)-B_m W_m)/A_(m+1)^2,                      (C2)
```

where `W_m=A_(m+1)A_m'-A_mA_(m+1)'`. If `J_(m+1)` denotes the literal drift-removed adaptive
mixed/completed shifted-Xi arithmetic source action, then

```text
w^4 J_(m+1)(w) -> (2m+3)/2 > 0,
C_m(w^2)/J_(m+1)(w) -> 0.                               (C3)
```

The Lean statement will quantify `m=n+1`; hence all three limits are unconditional theorems with
only a data parameter `n : Nat`, not assumptions supplied by a caller.

## Conjecture/failure/pivot loop

1. **[CONJECTURE]** The projective renewal curvature has a positive leading floor comparable to
   the literal arithmetic source action.
2. **[FALSIFIED]** Its two weight-four contributions have exact limits `-1/2` and `+1/2`.
3. **Exact why:** Jacobi-edge motion and moving-apex diagonal motion are the two components of one
   nonisospectral degree--mass connection. The arcsine recession point is projectively flat, so
   their vacuum parts cancel.
4. **Stronger replacement:** the full literal curvature is asymptotically negligible relative to
   the strictly positive source action, (C3). This survives because it incorporates rather than
   denies the cancellation.

## Paper proof

Fix `m>=1`. Existing shifted-Xi recession and flow laws give

```text
R_m(w^2)/w^2 -> 4,
w^4 B_m(w^2) -> 1/16,
w^2 alpha_j(w^2) -> 1/2,
w^2 E_j(w^2) -> (4j+1)/2,
```

where `E_j` is admission effectivity rate. The last limit follows from

```text
E_j = 2 sum_(k<j) alpha_k + (2j+1) alpha_j
```

and finite summation.

The norm quotient `B_m=N_(m+1)/N_m` and exact norm law `N_j'=-E_j N_j` imply

```text
B_m' = B_m(E_m-E_(m+1)).
```

Therefore

```text
w^6 B_m'(w^2) -> (1/16)(-2) = -1/8,
w^4 B_m'(w^2)R_m(w^2)
  = (w^6 B_m'(w^2))(R_m(w^2)/w^2) -> -1/2.              (1)
```

The exact nonisospectral diagonal Jacobi flow is

```text
alpha_j' = 2(j-1) beta_j - 2(j+1) beta_(j+1) - alpha_j^2.
```

At `j=m+1`, both beta indices are at least two, so both normalized beta limits are `1/16`.
Consequently

```text
w^4 alpha_(m+1)'(w^2)
  -> 2m/16 - 2(m+2)/16 - 1/4 = -1/2.
```

Since `w^4 ((w^2)^(-1))^2=1` eventually,

```text
w^4 ((w^2)^(-2)+alpha_(m+1)'(w^2)) -> 1/2.             (2)
```

Adding (1) and (2) proves (C1).

The already-proved homogeneous renewal law is

```text
W_(m+1)-B_m W_m
 = B_m' A_m A_(m+1)
   + ((y^(-1))^2+alpha_(m+1)') A_(m+1)^2.
```

Far-right admission recession makes `A_(m+1)` nonzero eventually. Division by its square and
`R_m=A_m/A_(m+1)` prove (C2).

Inside the eventual positive chamber, literal source identification gives
`J_(m+1)=D_(m+1)`, cumulative Jacobi dissipation. Coordinate covariance gives
`w^4D_(m+1)(w^2)=Ddim_(m+1)(w)`. The exact projective Cauchy-gap identity is

```text
Surplus_j=(2j+1)Ddim_j-F_j^2.
```

Both `Surplus_j` and `F_j^2` tend to `(2j+1)^2/4`; hence
`Ddim_j -> (2j+1)/2`. Taking `j=m+1` proves the first part of (C3). Dividing (C1) by this nonzero
limit proves the second.

## Hostile audit and significance

- The transfer-matrix identity behind (C2) is classical parent theory; it is not claimed as new.
- Fixed-degree cancellation does not control a diagonal `m=m(w)` contact schedule and does not
  prove RH.
- This is not a restated sign failure. It identifies the exact two leading components, proves
  their cancellation, and compares the surviving curvature to the literal arithmetic producer.
- The result kills any Route-U argument that spends the positive arcsine source floor directly on
  raw projective renewal curvature. The missing invariant must remove the flat vacuum first and
  control the next source-dependent correction uniformly on the parabolic degree scale.

## Lean formalization

```text
formal/GaloisForLFunctions/RHTower/
XiShiftedCanonicalAdmissionCharacteristicApexProjectiveVacuumCurvatureCancellation.lean
```

Public capstones have no proof-valued premises: exact scaled curvature limit zero, eventual
normalized renewal identity, scaled literal-source limit, and curvature/source ratio limit zero.

All required capstones are formalized unconditionally with only `n : Nat` as data. Direct
`lake env lean` and targeted module build pass (`12030/12030`). Every one of the nine public
declarations audits to only `[propext, Classical.choice, Quot.sound]`. The module contains no
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, `native_decide`, `#eval`, or `#reduce`.

## Log

- 2026-08-13 — positive-floor conjecture falsified by exact `-1/2 + 1/2` cancellation.
- 2026-08-13 — stronger source-negligibility theorem paper-proved; advanced to Stage 2.
- 2026-08-13 — exact result formalized, umbrella-wired, and built; advanced to Stage 3.
