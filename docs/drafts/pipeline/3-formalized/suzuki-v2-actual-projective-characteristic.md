# Suzuki v2 actual projective characteristic

- **Stage:** 3-formalized
- **Status:** unconditional paper theorem; formalized in Lean
- **Source:** actual finite-aperture Suzuki characteristics at extension angles `0` and `pi`
- **Claimed novelty:** removes the arbitrary one-angle exponential gauge and constructs the
  pole-compatible v2 family directly from two self-adjoint characteristic coordinates
- **RH used:** no
- **Computation used:** no

## Frontier correction

Suzuki v2 asks for a normalization of one entire characteristic.  That category is unsuitable:
the proposed limit is meromorphic and the paper imposes no holomorphy condition on its fitted
factor.  The all-angle finite operator already contains the correct projective coordinate, so no
fitted factor is needed.

For one aperture write the actual characteristic pencil as

```text
W_a^u(z) = A_a(z) + u E_a(z),     |u| = 1,
theta_a(z) = A_a(z) / E_a(z).
```

Here `W_a^1=W_a^0` and `W_a^(-1)=W_a^pi` in the real-angle notation.  Let

```text
c = xiHedenmalmDonoghueScale > 0.
```

Define the actual v2 projective characteristic

```text
F_a(z) = -W_a^pi(z) / (c W_a^0(z) - W_a^pi(z)).              (1)
```

Both entries in (1) are literal characteristic functions of self-adjoint Suzuki extensions.
Every common nonzero normalization cancels.

## Theorem A: exact normalized-Livsic formula

At every point where `E_a` is nonzero,

```text
F_a(z) = (1-theta_a(z)) / ((1+c)+(c-1)theta_a(z)).           (2)
```

Indeed,

```text
W_a^0  = E_a(theta_a+1),
W_a^pi = E_a(theta_a-1),
c W_a^0-W_a^pi = E_a((c-1)theta_a+(c+1)),
```

and cancellation gives (2).

## Theorem B: unconditional upper-half-plane denominator gap

Suzuki's all-angle real-zero theorem and `A_a(i)=0` imply

```text
|theta_a(z)| < 1,       Im z > 0.                            (3)
```

For `c>0`, reverse triangle inequality gives

```text
|(1+c)+(c-1)theta_a(z)|
 >= 1+c-|c-1||theta_a(z)|
 >= 1+c-|c-1|
 =  2 min(1,c) > 0.                                         (4)
```

Consequently `F_a` is holomorphic throughout the upper half-plane.  Moreover

```text
|F_a(z)| <= 1/min(1,c),                                     (5)
```

because `|1-theta_a|<=2`.  Bound is independent of aperture, shift, prime cutoff, and
extension spectrum.  On every ball compactly contained in the upper half-plane, Montel therefore
supplies a uniformly convergent subsequence of the literal `F_a` family.  In particular, the
canonical cofinal aperture schedule has such a subsequence on a fixed compact ball.  This is
unconditional existence of actual projective characteristic limits; target identification is
separate.

## Theorem C: exact v2 target chart

Put `X=XiC(z)` and `D=XiC'(z)`.  The algebraically faithful normalized global Livsic coordinate is

```text
theta_infty(z) = (D+i c X)/(D-i c X).                       (6)
```

Unlike the iterated totalized expression through `(XiC'/XiC)`, formula (6) retains the correct
meromorphic value at a zero of `XiC`: its reduced value is `1`, not the artificial totalized
value `-1`.

Substitution of (6) into the fixed transform in (2) gives

```text
(1-theta_infty)/((1+c)+(c-1)theta_infty)
  = X/(X+iD)                                                (7)
```

wherever the displayed affine charts are finite.  Cross multiplication proves the corresponding
identity of meromorphic functions, so (7) transports through poles in the reciprocal chart.
The right side is exactly Suzuki v2's target.

## Exact remaining frontier

Construction, holomorphy on the upper half-plane, aperture-uniform normality, common-gauge
invariance, and target coordinate algebra are closed.  Full v2 convergence is now precisely:

```text
actual normalized Livsic carrier theta_a
  -> (XiC' + i c XiC)/(XiC' - i c XiC)                      (8)
```

locally uniformly in finite charts, with reciprocal convergence at the limiting pole divisor.
Statement (8), not an arbitrary `phi(a,z)`, is the source-bearing convergence problem.  Since the
finite carriers are Schur and the target is strict Hermite--Biehler exactly under RH, proving (8)
remains RH-strength.  The present result makes that obstacle coefficient-faithful and constructs
the actual convergent normal family without assuming it.

## Hostile audit

- No abstract replacement characteristic appears in (1).
- No fitted pointwise or holomorphic gauge appears.
- Both finite coordinates come from actual self-adjoint extensions.
- Poles are retained projectively rather than suppressed by an entire-limit claim.
- Common source normalization cancels identically.
- Normal-family compactness is proved from the actual all-angle theorem, not assumed.
- No claim is made that compactness alone identifies the Xi target.

## Lean realization

Formal module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiTaV2ProjectiveCharacteristic.lean
```

It proves, for the literal `suzukiTaCharacteristic` family:

- exact `0`/`pi` pencil coordinates and actual all-angle reality;
- strict Schur control for the actual Livsic quotient;
- global meromorphicity and upper-half-plane holomorphy of `F_a`;
- the sharp denominator gap and aperture-uniform norm bound;
- an unconditional canonical cofinal Montel subsequence of actual `F_a`;
- the division-free Xi projective identity retaining the Xi divisor.

No theorem assumes convergence to the Xi target.  Target identification remains exactly the
RH-bearing source problem stated in (8).

### Declaration table

| Card statement | Lean declaration |
|---|---|
| pencil coordinates `A_a`, `E_a` and `W_a^u = A_a + u E_a` | `RHTower.suzukiTaV2CharacteristicA`, `RHTower.suzukiTaV2CharacteristicE`, `RHTower.suzukiTaCharacteristic_eq_v2Pencil` |
| angles `0`, `pi` | `RHTower.suzukiTaCharacteristic_zeroAngle`, `RHTower.suzukiTaCharacteristic_piAngle` |
| actual all-angle reality of the pencil | `RHTower.suzukiTaV2_allAngleRealZeros` |
| `theta_a = A_a/E_a`, strict Schur (3) | `RHTower.suzukiTaV2Livsic`, `RHTower.norm_suzukiTaV2Livsic_lt_one` |
| projective characteristic `F_a` (1) | `RHTower.suzukiTaV2ProjectiveCharacteristic` |
| Theorem A: normalized-Livsic formula (2) | `RHTower.suzukiTaV2ProjectiveCharacteristic_eq_mobius` |
| Theorem B: denominator gap (4) | `RHTower.suzukiTaV2ProjectiveDenominator_ne_zero`, `RHTower.two_mul_min_le_norm_suzukiV2MobiusDenominator` |
| Theorem B: holomorphy on `Im z > 0` | `RHTower.differentiableOn_suzukiTaV2ProjectiveCharacteristic_upperHalfPlane` |
| Theorem B: aperture-uniform bound (5) | `RHTower.norm_suzukiTaV2ProjectiveCharacteristic_le` |
| Theorem B: Montel normal family / cofinal limit | `RHTower.exists_suzukiTaV2ProjectiveCharacteristic_montel_subseq`, `RHTower.exists_suzukiTaV2CanonicalCofinalProjectiveLimit` |
| global meromorphicity of `F_a` | `RHTower.meromorphicOn_suzukiTaV2ProjectiveCharacteristic` |
| Theorem C: target chart (6)–(7), division-free | `RHTower.xiHedenmalmAlgebraicLivsic_v2_projective_identity` |

Every declaration is unconditional; `#print axioms` on each reports only `propext`,
`Classical.choice`, `Quot.sound`.  The module is wired into `GaloisForLFunctions/RHTower.lean`.
