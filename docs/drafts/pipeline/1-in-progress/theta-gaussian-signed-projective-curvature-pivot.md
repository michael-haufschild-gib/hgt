# Theta Gaussian signed projective curvature pivot

- **ID:** theta-gaussian-signed-projective-curvature-pivot
- **Stage:** 1-in-progress
- **Type:** FALSIFIED + THEOREM (Lean) + CONJECTURE
- **Source:** completed theta first atom; `p=4/p=2` Gaussian aperture transport
- **Statement:** Global positivity of the leading `p=4` curvature is false in the cold chamber; the literal signed `p=2` correction reverses the cold sign and admits an exact denominator-free projective-flux law.

## Goal

Replace the false global `C_4`-curvature margin behind GABTC by the exact signed source object that
retains the `p=2/p=4` cancellation.  The remaining target is not a generic moment inequality: it is
one source-specific adjacent projective-flux inequality for the completed theta first atom.

## Gates

- [x] 0 → 1 in-progress: exact source object, paper proof, no-go mechanism, and replacement inequality
- [ ] 1 → 2 fully-proven: prove the signed projective flux globally for every physical aperture and degree
- [ ] 2 → 3 formalized: formalize the global sign theorem after its paper proof closes
- [ ] 3 → 4 publication-ready: standalone proof, novelty audit, and Lean certificate

## Cold Watson theorem

For fixed `j`, put

```text
a=j+1/2,
h_a=Gamma(a+1/2)/Gamma(a),
g_a=h_a/(2a),
b_p=p+1/2-2*pi.
```

For the exact positive tail channel

```text
C_(p,j)(-L)=integral_0^infinity x^(2j) exp(-L*x^2) A_p(x) dx,
A_p(x)=exp((p+1/2)x-pi*exp(2x)),
```

the half-line Watson expansion is

```text
C_(p,j)(-L)
 =exp(-pi)/2 * Gamma(a)*L^(-a)
    *(1+b_p*h_a*L^(-1/2)+O_j(L^-1)),

q_j^(p)(-L)
 =L^-1*(1+b_p*g_a*L^(-1/2)+O_j(L^-1)).
```

The Gamma recurrence gives

```text
g_a-2*g_(a+1)+g_(a+2)
 =3*g_a/(4*(a+1)*(a+2)) > 0.
```

Since `b_4=9/2-2*pi<0`,

```text
lim_(L->infinity) L^(3/2) S_j^(4)(-L)
 =(9/2-2*pi)*3*g_a/(4*(a+1)*(a+2)) < 0.      (SPC1)
```

Thus every fixed-degree `C_4` curvature is negative for all sufficiently cold apertures.

## Signed positive survivor

Put

```text
c=3/(2*pi),
rho_j=C_(2,j)/C_(4,j),
d_j=1-c*rho_j,
m_j=d_(j+1)/d_j.
```

The exact shift `A_2=exp(-2x)A_4` gives

```text
rho_j=1-2*h_a*L^(-1/2)+O_j(L^-1),
d_j=1-c+2*c*h_a*L^(-1/2)+O_j(L^-1),
m_j=1+2*c/(1-c)*g_a*L^(-1/2)+O_j(L^-1).
```

For the literal signed first-atom curvature `S_j^F`,

```text
lim_(L->infinity) L^(3/2)
  *(S_j^F-m_(j+1)*S_j^(4))
 =6/(2*pi-3)*3*g_a/(4*(a+1)*(a+2)) > 0,      (SPC2)

lim_(L->infinity) L^(3/2) S_j^F
 =thetaCuspFirstAtomBoundaryLogSlope
    *3*g_a/(4*(a+1)*(a+2)) > 0.               (SPC3)
```

The identity

```text
9/2-2*pi+6/(2*pi-3)=thetaCuspFirstAtomBoundaryLogSlope>0
```

is exact.  The signed correction is therefore the cold curvature producer.  Treating it by
absolute-value leakage discards precisely the cancellation that changes the sign.

## Exact projective law

Define

```text
T_j=d_(j+1)^2-d_j*d_(j+2).
```

Then

```text
T_j
 =c*(rho_j-2*rho_(j+1)+rho_(j+2))
  +c^2*(rho_(j+1)^2-rho_j*rho_(j+2)),          (SPC4)
```

and the compiled transport product rule becomes

```text
d_j*d_(j+1)*d_(j+2)
  *(S_j^F-m_(j+1)*S_j^(4))
 =q_j^(4)*d_(j+2)*T_j
  -q_(j+2)^(4)*d_j*T_(j+1).                    (SPC5)
```

All `d_j` are positive.  Hence the signed correction is nonnegative exactly when

```text
q_j^(4)*d_(j+2)*T_j
 >=q_(j+2)^(4)*d_j*T_(j+1).                    (SPC6)
```

`(SPC6)` is the new global source conjecture.  `(SPC2)` proves its eventual cold-aperture sign for
each fixed degree.  Its validity over the whole physical aperture continuum remains open.

## No-go closure

- **Exact killing theorem/mechanism:** `(SPC1)` rules out any globally positive lower bound for `S_j^(4)`.  The W18 absolute leakage budget is `O(L^-1/2)` in the cold chamber while the actual signed curvature is `O(L^-3/2)`, so it loses a full factor `L` and cannot close the global boundary.
- **Strongest positive survivor:** `(SPC2)`--`(SPC5)` show that the signed amplitude correction reverses the cold sign and is governed exactly by adjacent projective minors.
- **New insight:** the first-atom proof must preserve the signed `p=2/p=4` correction.  Positive `C_4` curvature may be used only inside a genuine cusp chamber; the cold seam must be carried by signed projective transport or the completed-source flow.
- **Status:** `(SPC1)`--`(SPC3)` are paper-proved and novelty-unverified.  `(SPC4)`--`(SPC5)`, the sign equivalence, and the exact positive sign-flip coefficient are formalized in `PrimeArchThetaGaussianApertureSignedProjectiveCurvature.lean`.  The global inequality `(SPC6)` is the named open core.

## Novelty audit

Watson asymptotics, Gamma recurrences, and ordinary Turán theory are parent theory.  The audited
classical Gaussian-moment literature does not supply the exact completed-theta `p=4/p=2` cold sign
reversal or the adjacent projective-flux law.  Those exact source-compiled statements remain
`[NOVELTY UNVERIFIED]` pending a dedicated collision search.

## Do not try again

- Do not seek a globally positive `C_4` curvature bound.
- Do not use W18 as the primary cold-aperture mechanism.
- Do not replace the signed correction by independent absolute bounds before testing `(SPC6)`.

## Log

- 2026-07-20 — cold `C_4` positivity falsified; signed curvature producer and exact projective-flux survivor identified.
- 2026-07-20 — `(SPC4)`--`(SPC5)` and the nonnegative-flux equivalence added to permanent Lean source.
