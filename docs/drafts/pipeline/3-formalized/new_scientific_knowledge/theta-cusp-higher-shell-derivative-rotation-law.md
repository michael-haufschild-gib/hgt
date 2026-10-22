# Theta-cusp higher-shell derivative rotation law

- **ID:** TC-HSDR
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/drafts/non-ccm-rh-proof-chain-working-map.md` · Hedenmalm open core
- **Statement:** For `n ≥ 2`, `a < 1/2`, and `b > 0`, the incomplete-Gamma Ward remainder satisfies `Re R'_n(b-ia) < 0`.

## Goal

Close first missing directional component in exact Gamma formula for actual Hedenmalm shell
current. This is source-pure: `R_n` is already proved equal to twice transform of exact positive
theta Ward shell. Statement contains no Xi zero, RH predicate, or assumed current sign.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: direct Lean compile green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact statement

Put

```text
f_(a,n)(x) = exp(a x) thetaCuspWardGibbsAtom(n,x),
R_n(b-ia) = 2 integral_(0,infinity) f_(a,n)(x) exp(ibx) dx.
```

Then

```text
Re R'_n(b-ia)
  = -2 integral_(0,infinity) x f_(a,n)(x) sin(bx) dx.
```

Theorem:

```text
integral_(0,infinity) x f_(a,n)(x) sin(bx) dx > 0.            (DR)
```

No fixed sign is asserted for `Im R'_n`: even exponential tangent model changes that sign when
frequency crosses shell decay scale. Any valid closure must retain `b/n²` dependence there.

## Corpus-forced evidence

Lean proves, for every higher shell:

```text
f > 0,  f' < 0,  f'' > 0,
integral f sin(bx) > 0,
integral f cos(bx) > 0,
R_n(b-ia) lies in strict first quadrant,
(1/2-a)|R'_n| ≤ 2 Im R_n.
```

Cosine theorem is new:

```text
b² integral f cos(bx)
  = integral f''(x)(1-cos(bx)) dx > 0.
```

It removes value-phase ambiguity for all `n≥2`; `(DR)` is next derivative-phase obstruction, not
an arbitrary route choice.

## Proof

Set

```text
K3(u) = u(2+cos u)-3 sin u.
```

Three derivative sign propagations on `0<u≤3`, followed by elementary trigonometric bounds for
`u>3`, prove `K3(u)>0` for every `u>0`. Three half-line integrations by parts give the exact
all-shell identity

```text
b^4 integral x f_(a,n)(x) sin(bx) dx
  = -integral f'''_(a,n)(x) K3(bx) dx.                 (1)
```

All boundary terms vanish because the kernel and its first two derivatives vanish at zero, while
the tilted Ward density and its first two derivatives decay at infinity.

Write

```text
q = 2 pi n^2 exp(2x),  c=a+5/2,  r=q-c.
```

Exact differentiation gives

```text
f'''/f = -r^3 + 6qr - 4q.
```

For `n≥2`, `x≥0`, and `a<1/2`, one has `q>24`, `c<3`, and `r>21`. Elementary polynomial
inequalities then give `r^3-6qr+4q>0`; hence `f'''<0`. Since `K3(bx)>0` for `b,x>0`, right side
of `(1)` is nonnegative almost everywhere and nonzero on an open subset. Therefore it is strictly
positive, proving `(DR)` and `Re R'_n(b-ia)<0`.

## No-go closure

- **Exact killing theorem/mechanism:** None; conjecture proved.
- **Strongest positive survivor:** Universal kernel identity `(1)` holds for every positive shell,
  not only higher shells.
- **New insight:** Third-order alternation, rather than first-order rotation-density pairing,
  controls every higher-shell horizontal spectral direction.
- **Status:** Formalized.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspShellIncompleteGammaCoordinate.lean
```

Declarations:

```text
thirdOrderSineKernel_pos
integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_thirdOrder_identity
integral_id_mul_thetaCuspTiltedWardDensity_mul_sin_pos_of_two_le
thetaCuspShellGammaCoreRemainderSpectralDerivative_re_neg_of_two_le
thetaCuspShellGammaCoreRemainderSpectralDerivative_reflected_re_pos_of_two_le
thetaCuspHigherShellGammaFourDirectionalCone
```

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspShellIncompleteGammaCoordinate.lean
```

passes. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella
`lake build` is reserved for final full-chain audit under current task rules.
