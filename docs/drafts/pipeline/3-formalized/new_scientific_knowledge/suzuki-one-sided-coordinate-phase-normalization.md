# Suzuki one-sided coordinate phase normalization

- **ID:** `suzuki-one-sided-coordinate-phase-normalization`
- **Stage:** 3-formalized
- **Type:** SOURCE CORRECTION / THEOREM / FRONTIER REOPENING
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[NOVELTY SEARCH: NO MATCH] [NOT AN RH PROOF]`
- **Lean:** `GaloisForLFunctions.RHTower.SuzukiCarlemanCoordinatePhase`
- **RH used:** no
- **Computation used:** no
- **Primary sources:** M. Suzuki, *Aspects of the screw function corresponding to the Riemann
  zeta function*, arXiv:2206.03682v4, Theorem 1.1(1); M. Suzuki, *Weil's quadratic form via the
  screw function*, arXiv:2606.09096v1, Sections 8.2--8.3.

## Corpus collision

The corpus already records the centered identity

```text
xi'(1/2-iz)=i XiC'(z),
```

and therefore Suzuki's zero-shift positive-half-line multiplier is

```text
M_phys,0(z)=i XiC'(z)/(z^2 XiC(z))=i G_0(z).            (1)
```

Later one-sided exterior cards use `G_0 W-T_R` while still calling `T_R` the physical right
triangle.  The recently added scalar phase no-go then uses physical source quadrature to conclude
that the source flux is purely imaginary and cannot correct the real Xi curvature.  That
conclusion is valid only for the mixed, source-incompatible expression `G_0 W-T_R`.

## Competing conventions

### C1. Mixed physical triangle `[FALSIFIED]`

```text
E_mix=G_eta W-T_phys.                                   (2)
```

This drops the factor `i` in `(1)` without applying the same scalar to the exterior equation.
It is not the physical convolution sheet and is not a scalar normalization of it.  Its central
phase contradiction therefore cannot falsify a source realization.

### C2. Canonical Weyl normalization `[PROVED]`

For the global Neumann representative `r_0(t)=-|t|/2`,

```text
int_0^infinity r_0(t)e^(izt)dt=1/(2z^2),                (3)
```

so the physical shifted right multiplier is

```text
M_phys,lambda
 =i G_0-lambda/(2z^2)
 =i G_eta(lambda),
eta(lambda)=-i lambda/2.                                (4)
```

Thus the physical exterior and its canonical Xi-real normalization are

```text
E_phys,lambda=i G_eta W-T_phys,
E_norm,lambda=(-i)E_phys,lambda
             =G_eta W-(-i T_phys).                     (5)
```

The interval input to every existing `G_eta W-I` theorem must therefore be

```text
I_norm=-i T_phys,                                       (6)
```

not `T_phys`.

### C3. Absorb the phase into a source gauge `[FALSIFIED]`

Multiplying one source channel by a gauge scales `W` and `T_phys` together.  It does not change
their relative coefficient in `iG_eta W-T_phys`, so it cannot turn `(2)` into `(5)`.

## Immediate consequence under hostile source quadrature

For Suzuki's reflected real deficiency vectors, the effective phase-one compact source is `i`
times a real odd distribution.  Hence

```text
W_lambda'(0) is real,
T_phys,lambda(0) is purely imaginary,
q_phys,lambda=T_phys,lambda(0)/W_lambda'(0) is purely imaginary.  (7)
```

This does not obstruct `(5)`: the normalized quotient is

```text
q_norm,lambda=-i q_phys,lambda in R.                    (8)
```

For two real shifts, let `Phi_phys` be the real affine chord intercept of `q_phys`.  The flux in
the normalized central residue is

```text
Phi_norm=-i Phi_phys,
Re Phi_norm=Im Phi_phys.                                (9)
```

Therefore Herglotz positivity requires the non-vacuous physical condition

```text
Im Phi_phys <= XiC''(0)/XiC(0)<0,                       (10)
```

not the impossible mixed condition `Re Phi_phys<0`.  The scalar jump-Gram conjecture is reopened;
the corpus phase no-go does not apply to the source-normalized sheet.

The direct Neumann triangle cancels from the **central residue**.  From the physical moment law,

```text
q_phys,lambda=q_phys,lambda^EG+i(a/2)lambda,
q_norm,lambda=q_norm,lambda^EG+(a/2)lambda.             (11)
```

Affine interpolation kills this central linear term in either coordinate.  It does not kill the
whole spectral function.  The later full-frequency audit proves the exact survivor

```text
alpha beta sin(az)/(2z(beta-alpha))
 [W_alpha'(0)/W_alpha(z)-W_beta'(0)/W_beta(z)].         (11a)
```

Thus the central phase correction here remains valid, while any prime--Gamma-only full Pick
factorization must be replaced by a Neumann-holonomy-compensated one.  See
`../../3-formalized/new_scientific_knowledge/suzuki/suzuki-full-frequency-neumann-holonomy-survivor.md`.
In the exact centered parameter `eta=-i lambda/2`, the normalized central direct channel has slope
`i a`, not `i a/2`.

## Scientific falsifiers

1. **Source multiplier:** `(4)` must follow simultaneously from Suzuki's 2023 one-sided formula,
   centered Xi chain rule, and `(3)`.
2. **Physical convolution:** direct expansion must prove `(5)` without a divisor assumption.
3. **Real-axis residue:** normalized Xi residues must be real negative at real Xi zeros; the
   unnormalized physical multiplier has imaginary residues.
4. **Source quadrature:** the physical pure-imaginary phase in `(7)` must become a real normalized
   flux under `(6)`, not disappear.
5. **Gauge attack:** unrelated source gauges must leave `(9)` unchanged.
6. **Neumann attack:** both real-shift and centered-parameter descriptions must give the same
   cancellation after the factor-two map.

## Large-negative-shift hostile test

Correct phase reopens scalar positivity but not for arbitrary admissible shifts.  For fixed
aperture, scaled resolvents satisfy

```text
(-lambda)(A_a-lambda)^(-1) -> I,  lambda -> -infinity.
```

Applied to the two deficiency sources, this makes the phase-one effective source converge after
scaling to the endpoint pair

```text
i*2*cosh(a)*(delta_(-a)-delta_a).
```

Consequently

```text
q_norm,lambda^EG
 -> (1/(2a)) integral_0^(2a) g(t) dt.                  (12)
```

The dyadic affine pair `(-2L,-L)` inherits the same intercept limit.  Since `g(0)=0`, `(12)` tends
to zero at small aperture, strictly above the fixed negative Xi curvature.  Thus sufficiently
negative dyadic pairs at sufficiently small aperture cannot yield a Herglotz jump quotient.
The restored route requires an intrinsic non-escaping shift-selection law; uniformity over all
admissible pairs is false.  Full proof is in
`../2-fully-proven/new_scientific_knowledge/suzuki-neumann-dominated-shift-cone-obstruction.md`.

## Actual reopened frontier

All six falsifiers survive.  Corpus semantics and exact connectors are repaired.  Live source
theorem is restored to

```text
construct normalized Euler--Gamma right triangles I_norm=-i T_phys
 -> select shifts outside the Neumann-dominated negative escape cone
 -> prove Re Phi_norm<=XiC''(0)/XiC(0)
 -> prove normalized jump Pick kernel
 -> exclude every nonreal Xi pole
 -> RH.
```

The positivity is allowed to be RH-bearing; it must be proved from an independently positive
prime--Gamma colligation, not inferred from the Xi logarithmic derivative.

## Formalization and priority audit

Lean proves exact one-sided parameter injection, relation to old full-symbol coordinate,
physical shifted multiplier expansion, physical-sheet phase identity, physical/normalized flux
transport, source-quadrature reality, corrected Herglotz threshold, and one-sided Neumann
cancellation.  Main declarations:

```text
suzukiOneSidedCenteredShiftParameter
suzukiPhysicalRightCarlemanMultiplier_eq
neg_I_mul_suzukiPhysicalRightCarlemanExterior
suzukiWeylNormalizedCentralSourceFlux_eq_neg_I_mul_physical
suzukiWeylNormalizedCentralSourceFlux_re_eq_physical_im
suzukiWeylNormalizedCentralSourceFlux_im_eq_zero_of_source_quadrature
suzukiPhysicalCentralSourceFlux_im_le_XiC_curvature_of_normalized_herglotz
suzukiAffineSewnCentralSourceFlux_oneSided_neumann_channel_cancels
```

Primary-paper search found Suzuki's one-sided screw formula and finite Neumann kernel, but no
source stating half-sheet parameter `-i lambda/2`, physical-to-Xi-real interval rephasing, or
resulting retraction of scalar jump phase no-go.  Generic half-line Laplace integration and scalar
rephasing are classical; candidate novelty is exact Suzuki/RH source synthesis and corrected
frontier.  External specialist priority remains unverified.

## Gates

- [x] corpus collision and prior coordinate audit found
- [x] primary source formulas re-read
- [x] three competing conventions stated
- [x] close all six falsifiers on paper
- [x] formalize phase, half-shift, physical-sheet, and central-flux connectors
- [x] repair false scalar no-go and SOTA/handover frontier
- [x] direct module and SOTA checks
- [x] exact module build (`9000/9000`)
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [x] forbidden-token scan; repository lint reached only unrelated concurrent unreachable modules
- [x] later full-frequency audit restricted “Neumann cancellation” to the central residue and
      recorded exact projective-holonomy survivor `(11a)`
