# Theta first atom: variable-curvature Brascamp--Lieb certificate

- **ID:** `theta-first-atom-variable-curvature-brascamp-lieb`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE] [PHYSICS-TRANSFER] [SOURCE-SPECIFIC] [RH-DOWNSTREAM]`
- **Primary formal source:**
  `formal/GaloisForLFunctions/RHTower/PrimeArchThetaBornWittenCurvatureGap.lean`
- **Killed predecessor:**
  `../5-failed/theta-first-atom-boundary-brascamp-lieb-mean-floor.md`

## Live target

Let `a_j=thetaCuspAtomRawEvenMoment j 1`, `c=3005/2997`, and let `nu` be the unnormalized
first-atom measure, so `a_j=integral x^(2j) dnu`.  Define

```text
J = integral x^2 / V''(x) dnu(x).
```

The full one-dimensional Brascamp--Lieb inequality for `g(x)=x^2` gives

```text
a_0 a_2 - a_1^2 <= 4 a_0 J.                              (BLvar)
```

Therefore the source-specific weighted certificate

```text
64 c^2 a_0 J <= (45 - 16 c^2) a_1^2                      (Jcert)
```

implies the relaxed first-atom gate

```text
16 c^2 a_0 a_2 <= 45 a_1^2.                              (R)
```

Unlike the failed uniform-curvature route, `(Jcert)` does not require a lower bound on the first
normalized moment.

## Exact source simplification

For `q(x)=pi exp(2x)-3/2`, Lean proves

```text
V''(x) = 4q + 6 + 6/q + 9/q^2
       = (4q^3 + 6q^2 + 6q + 9)/q^2.                     (C)
```

Since the Born density is `rho=4q psi^2`, the weighted integrand has the exact Morse form

```text
x^2 rho(x) / V''(x)
  = 4 x^2 q(x)^3 psi(x)^2 / (4q(x)^3+6q(x)^2+6q(x)+9).   (MorseJ)
```

This is the positive source relation to attack.  It retains the nonlinear readout profile that
was destroyed by replacing `V''` with `19`.

## Proven source controls

- `V''>=19` and `V''>=4 pi`;
- `B_1(0)>=-1/16` and `B_1(x)>=-1/16+(19/2)x`;
- the exact Ward value `integral x B_1 rho=(1/2)integral rho`;
- the localization law `240 a_1<=13 a_0`;
- all polynomially weighted Born and superpotential integrability statements.

The localization law is useful here as an upper input.  The old attempt incorrectly required the
opposite type of estimate.

## Boundary proof obligation

Mathlib and the local corpus do not yet contain the needed half-line Brascamp--Lieb theorem.
The formal proof must make explicit:

1. the Neumann scalar realization on `[0,R]`;
2. disappearance of the endpoint current for `g=x^2`, whose first derivative vanishes at `0`;
3. passage `R->infinity` using existing Born integrability;
4. conversion to the unnormalized moment convention in `(BLvar)`.

## Direct RH impact

`(BLvar)+(Jcert)` discharges the relaxed first-atom hypothesis consumed by
`forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom`.  The upper radial ratio remains an
independent hypothesis, so this route closes one theta Hankel input rather than proving RH alone.

## Next formal steps

1. Formalize half-line Brascamp--Lieb with the inverse-curvature integrand retained.
2. Instantiate it with the exact Born--Witten density and prove `(BLvar)`.
3. Define the raw weighted moment `J` and formalize `(MorseJ)`.
4. Bound `J` using the rational `q` profile, Ward identities, or a supersymmetric resolvent value;
   reject any estimate that collapses back to the false mean floor.
5. Prove the short algebraic consumer `(BLvar)+(Jcert)->(R)` only after the analytic producer is
   present.

## Status

- [x] exact variable-curvature reduction derived
- [x] uniform-curvature mean-floor predecessor killed in Lean
- [x] significant positive localization theorem retained
- [ ] half-line Brascamp--Lieb theorem formalized
- [ ] theta variable-curvature instance proved
- [ ] weighted certificate `(Jcert)` proved
- [ ] relaxed first-atom gate discharged

