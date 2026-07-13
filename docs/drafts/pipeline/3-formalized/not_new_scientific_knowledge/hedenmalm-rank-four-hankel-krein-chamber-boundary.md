# Hedenmalm rank-four Hankel--Krein chamber boundary

- **ID:** `hedenmalm-rank-four-hankel-krein-chamber-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM / EXACT ORIENTATION GEOMETRY
- **Scientific status:** `[PROVED] [BRIDGE] [NOT AN RH PROOF]`
- **Parent:** `../../1-in-progress/hedenmalm-rank-four-hankel-krein-chamber.md`

## Theorem

The center-mixed radial kernel

```text
H_a(x,y)=(x+y)sinh(a(x+y))
```

has the exact separable rank-four decomposition

```text
2 H_a(x,y)
 =q_+(x)p_+(y)+p_+(x)q_+(y)
  -q_-(x)p_-(y)-p_-(x)q_-(y),

p_+(x)=exp(ax),     q_+(x)=x exp(ax),
p_-(x)=exp(-ax),    q_-(x)=x exp(-ax).
```

Its coordinate form

```text
Q(u_+,v_+,u_-,v_-)
 =Re(conj(u_+)v_+)-Re(conj(u_-)v_-)
```

has light-cone normal form

```text
4Q=|u_++v_+|^2-|u_+-v_+|^2
   -|u_-+v_-|^2+|u_--v_-|^2.
```

Thus the ambient form is split, with two explicit positive and two explicit negative complex
directions. It is not a Hilbert Gram form.

For the actual theta/Xi source, put

```text
u_+(a,b)=XiC(b-ai)=xi(1/2+a+ib),
v_+(a,b)=-i XiC'(b-ai)=xi'(1/2+a+ib),
u_-(a,b)=XiC(b+ai),
v_-(a,b)=-i XiC'(b+ai).
```

Schwarz reality and the functional equation give, without a nonvanishing premise,

```text
u_-=conj(u_+),
v_-=-conj(v_+).
```

Consequently

```text
Q(u_+,v_+,u_-,v_-)=2 Re(conj(u_+)v_+)
                   =partial_a |xi(1/2+a+ib)|^2.          (1)
```

The same scalar is exactly the Fourier transform of the horizontal autocorrelation tangent of
the exponentially tilted theta source. This supplies a premise-free source-to-chamber incidence:
the Hedenmalm orientation current is the value of one distinguished analytic source orbit in an
ambient split Krein space.

## Positive implementation law

The pointed analytic moment module already determines the Euler--Gamma source, the entire
centered Xi solution, and its Bezoutian. Equation `(1)` identifies the genuinely complementary
datum:

> A successful Hedenmalm Hilbert--Polya construction must prove that the uniquely determined theta
> orbit remains in the nonnegative chamber of this split form throughout the critical aperture.

Source determinacy and orientation are therefore not two approximations to the same information.
Determinacy selects the orbit; orientation chooses its Krein chamber. Positivity of the ambient
kernel is impossible because the ambient form contains explicit negative directions. Only a
source-specific global chamber-avoidance theorem can supply the missing sign.

## Formal certificate

File:
`formal/GaloisForLFunctions/RHTower/HedenmalmHankelKreinChamber.lean`.

Premise-free theorem surface:

```text
hedenmalmHankelKernel_rankFour_decomposition
hedenmalmHankelKreinForm_lightCone
hedenmalmHankelKreinForm_posDirection_one
hedenmalmHankelKreinForm_negDirection_one
hedenmalmHankelKreinForm_negDirection_two
hedenmalmHankelKreinForm_posDirection_two
hedenmalmHankelKreinForm_evenReal_reduction
thetaXiHankelOrbitValuePlus_eq_xi
thetaXiHankelOrbitTangentPlus_eq_deriv_xi
thetaXiHankelOrbitValueMinus_eq_conj
thetaXiHankelOrbitTangentMinus_eq_neg_conj
thetaXiHankelOrbit_kreinForm_eq
hasDerivAt_thetaXiHankelOrbit_normSq
fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm
```

## Boundary

This theorem does not prove that the orbit value in `(1)` is nonnegative. By the already
formalized pointed-moment orientation boundary, that sign is equivalent to RH. The present result
is therefore an exact geometric localization of the missing theorem, not an RH proof.

Honest significance score: **45/100**. The decomposition is elementary and the source incidence is
useful, but publication-level significance requires a new source mechanism forcing chamber
avoidance or a strong natural-category classification theorem.

## Gates

- [x] paper proof
- [x] unconditional Lean proof
- [x] no hard proposition interface
- [x] exact source-to-chamber incidence
- [ ] primary literature audit
- [ ] source-specific chamber avoidance
- [ ] RH
