# Physical prime logarithmic-mesh phase escape

- **ID:** `physical-prime-log-mesh-phase-escape`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / NO-GO (Lean)
- **Source route:** D2 / FCRJ physical corrected-prime contour
- **Statement:** At every D2 point and every positive physical window triple, actual two-edge
  transform phase escapes the real axis cofinally on the arithmetic aperture mesh
  `a=log n/2`.

## Goal

Upgrade Loop 91's continuous-translation phase escape to the exact natural logarithmic mesh used
by the physical prime detector. Determine whether discrete aperture sampling can rescue pointwise
D2 scalar-floor transport.

## Gates

- [x] 0 → 1 in-progress: corpus-derived dominant-edge/log-mesh conjecture
- [x] 1 → 2 fully-proven: dependency-closed paper proof and no-go classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go note

## Conjecture C92

Let `w` have negative real part and nonzero imaginary part, and let both edge coefficients be
nonzero. For `F(a)=exp(a w)P+exp(-a w)Q`, the growing `Q` edge dominates as `a→∞`. Choose a
cofinal real phase-aligned target sequence and round `exp(2a)` to natural numbers. The logarithmic
rounding error tends to zero, the normalized growing edge retains nonzero imaginary part, and the
decaying edge vanishes. Hence `Im(F(log n/2))!=0` for arbitrarily large natural `n`.

## Exact theorem

Let `alpha=Re w<0`, `beta=Im w>0`, `Q!=0`, and

```text
F(a)=exp(a w)P+exp(-a w)Q.
```

Lean first proves a reusable logarithmic rounding law. For every real sequence `t_k→∞`,

```text
log(ceil(exp(t_k)))-t_k → 0.                              (1)
```

Choose `theta` from `{0,pi/2}` so that `Im(exp(-i theta)Q)!=0`, and define

```text
t_k=(theta+2 pi k)/beta,
n_k=ceil(exp(2 t_k)),
a_k=log(n_k)/2.                                             (2)
```

Lean proves `t_k→∞`, `n_k→∞`, and `a_k-t_k→0`. The exact phase factor therefore obeys

```text
exp(-i beta a_k) → exp(-i theta).                        (3)
```

After positive real normalization, the full two-edge mode has the limit

```text
exp(alpha a_k) F(a_k) → exp(-i theta)Q.                  (4)
```

Indeed the first edge has norm `exp(2 alpha a_k)|P|→0`, while `(3)` controls the growing edge.
The limit in `(4)` has nonzero imaginary part; hence for all sufficiently large `k`, and therefore
cofinally in natural aperture,

```text
for every N, some n>=N has Im(F(log n/2))!=0.                (5)
```

At a D2 point `s`, put `w=s-1/2` and `z=-i(s-1/2)`. Then `Re w<0`, `Im w>0`, and the physical
coefficient `Q=xiPhysicalThetaAbelEntireModeAmplitude(L,A,c,-w)` is nonzero for every `L,A,c>0`
by Loop 91's open-strip theorem. Thus

```text
for every N, some n>=N has
  Im(xiPhysicalThetaAbelEnergyTwoEdgeTransform
    (L,A,c,log(n)/2,z))!=0.                                 (6)
```

Loop 90's square classifier gives the exact order consequence

```text
for every N, some n>=N has
  not ComplexRealPartMonotoneMultiplier(T(log(n)/2,z)^2).   (7)
```

## Proof

For `(1)`, set `x_k=exp(t_k)` and `m_k=ceil(x_k)`. Ceiling inequalities give

```text
1 <= m_k/x_k <= 1+1/x_k.
```

Since `x_k→∞`, the ratio tends to one. Continuity of logarithm at one and
`log(m_k/x_k)=log(m_k)-t_k` prove `(1)`.

If `Im Q!=0`, take `theta=0`; otherwise `Re Q!=0` and take `theta=pi/2`, so multiplication by
`exp(-i pi/2)=-i` produces nonzero imaginary part. Equations `(1)--(2)` give the vanishing phase
error. Splitting the normalized mode exactly gives

```text
exp(alpha a)F(a)
 = exp(2 alpha a+i beta a)P + exp(-i beta a)Q.
```

The first term tends to zero because `alpha<0`; periodicity at `2 pi k` and the phase error give
the second limit `(3)`. This proves `(4)`. Continuity of imaginary part makes the normalized mode
eventually nonreal, and multiplication by the positive real normalizer cannot create a nonzero
imaginary part from zero. Cofinality of `n_k` proves `(5)`. Physical strip noncensorship and the
exact D2 coordinate identity yield `(6)--(7)`.

## No-go closure

- **Exact killing theorem/mechanism:** `(6)--(7)` close discrete natural aperture sampling as a
  possible rescue of uniform pointwise D2 scalar-floor transport.
- **Strongest positive survivor:** rounding law `(1)`, explicit phase-aligned natural selector
  `(2)`, normalized dominant-edge limit `(4)`, and full physical mesh escape `(6)`.
- **New insight:** natural logarithmic aperture sampling is asymptotically fine enough to inherit
  off-critical phase instability. The nonreal phase can be forced on an explicit cofinal natural
  subsequence without Diophantine assumptions or numerical verification.
- **Status:** dependency-closed; Lean module verified and wired.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeLogMeshPhaseEscape.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12920/12920`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `tendsto_log_natCeil_exp_sub`,
  `tendsto_twoEdgeLogMeshPhaseTranslation_sub_target`,
  `tendsto_realExp_re_mul_twoEdgeExponentialMode_logMesh`,
  `twoEdgeExponentialMode_logMesh_cofinally_nonreal`,
  `xiPhysicalThetaAbelEnergyTwoEdgeTransform_logMesh_cofinally_nonreal_at_gaussianRatD2`,
  `physicalTwoEdgeSquare_logMesh_cofinally_not_realPartMonotone_at_gaussianRatD2`.

## Route impact and remaining burden

This retires both continuous and exact natural log-mesh phase reality as pointwise positivity
bridges. Natural aperture choice cannot make the squared physical kernel preserve real-part order
uniformly on D2 points. Remaining local possibilities must pair conjugate phases before applying
order or jointly control imaginary prime flux; global alternatives must prove corrected-prime
zero-floors without pointwise scalar multiplication. This theorem does not itself prove a negative
weighted prime sample: failure of universal multiplier monotonicity classifies the missing bridge,
not the actual complex source value.

## Novelty audit

Targeted corpus and primary-literature searches through 2026-08-28 found no exact logarithmic
rounding/phase-alignment theorem `(1)--(5)` attached to physical two-edge Weil tests, and no D2
natural-aperture consequence `(6)--(7)`. Recent compact-window work proves finite-window positivity
and decay laws; recent screw/operator work studies continuous finite-interval limits and numerical
spectra. None states this cofinal natural mesh phase obstruction. Candidate-new content is
restricted to this exact route-specific formal synthesis.

Primary comparison points:

- M. Chuk, [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom
  decay law*](https://arxiv.org/abs/2608.24827).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- A. Connes and C. Consani, [*The Scaling Hamiltonian*](https://arxiv.org/abs/1910.14368).

## Log

- 2026-08-28 — Mandatory corpus search found exact physical log-sample dominant-edge identities,
  natural floor/ceiling exponential infrastructure, and phase-alignment machinery, but no theorem
  for nonreal phase of the full physical two-edge transform on `log n/2`.
- 2026-08-28 — Conjectured phase-aligned ceiling selector plus dominant-edge normalization.
- 2026-08-28 — Proved the ceiling/log rounding law, phase-aligned cofinal natural selector, and
  normalized full two-edge limit.
- 2026-08-28 — Proved abstract log-mesh nonreal phase, actual D2 physical phase escape, and
  cofinal failure of squared-weight real-part monotonicity on exact natural apertures.
- 2026-08-28 — Direct source check, targeted `12920/12920` build, standard axiom audit, and
  umbrella wiring passed. Global lint reaches the new module without local violation; unrelated
  unwired RHTower/HTGeometry modules still block repository-wide lint.
