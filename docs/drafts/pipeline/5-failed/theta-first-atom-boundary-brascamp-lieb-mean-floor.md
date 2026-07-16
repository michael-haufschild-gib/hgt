# Theta first atom: uniform-curvature Brascamp--Lieb plus a mean floor

- **ID:** `theta-first-atom-boundary-brascamp-lieb-mean-floor`
- **Stage:** 5-failed
- **Type:** `[PROVED NO-GO] [POSITIVE REPLACEMENT] [LEAN]`
- **Formal source:**
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaBornWittenCurvatureGap.lean`

## Killed route

Put

```text
a_j = thetaCuspAtomRawEvenMoment j 1,
c   = 3005 / 2997.
```

The relaxed first-atom gate is

```text
16 c^2 a_0 a_2 <= 45 a_1^2.                              (R)
```

For the exact first Born--Witten density `rho=chi_1^2`, the positive readout coordinate gives

```text
V''(x) = 4q(x) + 6 + 6/q(x) + 9/q(x)^2 >= 19,
q(x) = pi exp(2x) - 3/2 > 0.                              (C19)
```

Replacing the full Brascamp--Lieb weight `1/V''(x)` by the uniform bound `1/19` would give

```text
19 (a_0 a_2 - a_1^2) <= 4 a_0 a_1.                       (BL19)
```

Together with

```text
64 c^2 a_0 <= 19 (45 - 16 c^2) a_1                       (M19)
```

this would imply `(R)`.  The source itself refutes `(M19)`.

## Exact no-go proof

The first superpotential obeys

```text
B_1(0) >= -1/16,
B_1'(x) >= 19/2,
B_1(x) >= -1/16 + (19/2)x.                                (A)
```

The anomalous half-line Ward identity is

```text
integral x B_1(x) rho(x) dx = (1/2) integral rho(x) dx.   (W)
```

Multiplying `(A)` by `x rho(x)` and using

```text
x/16 <= x^2/8 + 1/128
```

gives the unconditional localization law

```text
240 a_1 <= 13 a_0,                                       (L)
E_rho[X^2] <= 13/240.
```

Exact rational comparison of `(L)` with `(M19)`, using `a_0>0`, proves

```text
not (64 c^2 a_0 <= 19 (45 - 16 c^2) a_1).
```

Thus the uniform-curvature/mean-floor route is impossible for the actual theta source, not merely
too weak in the current proof system.

## Significant positive theorem

The route produced two reusable source theorems:

1. the exact absolute log-curvature gap `V''>=19`, stronger than `4 pi` for the first atom and
   inducing the partner-potential floor `19/2`;
2. the Ward localization bound `(L)`, a new upper control on the normalized quadratic clock value.

The corresponding Lean declarations are:

- `thetaCuspBornWittenLogCurvature_eq_readoutProfile`;
- `nineteen_le_thetaCuspBornWittenLogCurvature`;
- `thetaCuspFirstBornWittenSuperpotential_affine_lower`;
- `two_hundred_forty_mul_firstMorseBornMoment_one_le_thirteen_mass`;
- `two_hundred_forty_mul_firstAtomMoment_one_le_thirteen_mass`;
- `not_thetaCuspFirstAtom_uniformCurvature_meanFloor`.

## Surviving route

The full Brascamp--Lieb relation retains the variable inverse curvature:

```text
Var_rho(X^2) <= E_rho[4 X^2 / V''(X)].                    (VBL)
```

This can reduce the fourth-moment gate without demanding any false lower bound on `E[X^2]`.
The exact rational profile `(C19)` may cancel against the Born observable in `(VBL)`.  That is the
live source-specific route recorded by
`../1-in-progress/theta-first-atom-variable-curvature-brascamp-lieb.md`.

## Physics provenance

D. Le Peutrec, *On Witten Laplacians and Brascamp--Lieb's inequality on manifolds with boundary*,
arXiv:1607.08714, supplies the boundary Witten/Brascamp--Lieb mechanism.  The theta-specific
curvature profile, Ward localization, and no-go are proved directly in Lean.

## RH impact

This does not prove RH.  It prevents further work on a false sufficient condition and replaces it
with a strictly sharper weighted-curvature target for the relaxed first-atom Hankel input.  The
independent upper radial ratio remains open.

