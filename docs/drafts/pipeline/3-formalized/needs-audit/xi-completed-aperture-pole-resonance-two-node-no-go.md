# Xi completed-aperture pole-resonance two-node law

- **ID:** `xi-completed-aperture-pole-resonance-two-node-no-go`
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM / NO-GO WITH POSITIVE SURVIVOR
- **Parents:** `XiCompletedApertureReflectionKernel.lean`,
  `CompletedFluxCrossOrderReflection.lean`, and `XiEndpointStrongHeightGap.lean`
- **Scientific status:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`

## Conjecture under attack

Let

```text
S(s)=-xi'(s)/xi(s),
K_u(x,y)=S(1/2+u+i(x-y)),
O_u(x,y)=K_u(x,y)-K_(-u)(x,y)=2 Re K_u(x,y).
```

For an actual Xi zero `rho=beta+i gamma` of multiplicity `m_rho`, put

```text
delta=beta-1/2,
u_epsilon=delta+epsilon.
```

The packet on nodes `{gamma,0}` has equal diagonal `O_(u_epsilon)(0,0)` and off-diagonal
`O_(u_epsilon)(gamma,0)`.  The exact claim is

```text
lim_(epsilon->0, epsilon!=0)
  epsilon^2 *
    (O_(u_epsilon)(0,0)^2-O_(u_epsilon)(gamma,0)^2)
  = -4 m_rho^2.                                                (PR1)
```

Consequently there is `eta>0` such that every `0<epsilon<eta` gives a strictly negative
two-node determinant.

## Why the previous conjecture dies

The reflection-odd sector is the unique completed sector capable of a nonzero odd determinant,
but it is not itself the required three-node-only response carrier.  At the resonant displacement
`gamma`,

```text
K_(delta+epsilon)(gamma,0)=S(rho+epsilon).
```

The logarithmic derivative has residue `-m_rho` in the `S=-xi'/xi` orientation, whereas the
diagonal samples `S(beta+epsilon)` near the real point `beta`, where Xi is nonzero by the
unconditional height gap.  Hence the off-diagonal grows like `-2m_rho/epsilon`, while the diagonal
remains bounded.  A universal two-node positive-minor claim is therefore impossible even if RH is
true.

## Candidate paper proof

The existing residue-filled germ is

```text
G_rho(z)=z S(rho+z),      z!=0,
G_rho(0)=-m_rho,
```

and is analytic at zero.  Therefore

```text
epsilon O_(u_epsilon)(gamma,0)
 =2 Re G_rho(epsilon) -> -2m_rho.                         (PR2)
```

The real anchor `beta` has imaginary part zero, so
`xi(beta)!=0` by `xi_ne_zero_of_abs_im_le_nine_halves`.  Thus `S` is analytic at `beta`, and

```text
epsilon O_(u_epsilon)(0,0)
 =2 epsilon Re S(beta+epsilon) -> 0.                      (PR3)
```

Subtracting the squares of `(PR2)` and `(PR3)` proves `(PR1)`.  Since the limit is strictly
negative and `epsilon^2>0` for `epsilon!=0`, the unscaled determinant is negative throughout a
punctured positive neighborhood.

## Positive survivor

The exact invariant is the universal resonant determinant residue

```text
-4 m_rho^2.                                               (PR4)
```

This is stronger than saying the raw kernel is indefinite: it recovers the square of the analytic
multiplicity from a two-node aperture resonance.  Therefore the raw completed translation kernel
is a multiplicity tomograph, not the response-correlation cancellation carrier.

The proof-shape consequence is sharp.  To retain the existing unconditional one- and two-node
response barrier, the source construction must remove self-resonant divisor poles before forming
translation packets.  Zero-by-zero polar subtraction would be target-side and circular; the open
source problem is a global prime--Gamma/Poisson joining that performs this cancellation without
access to the divisor.

## Hostile audit

- [x] **Argument and sign.** Direct substitution gives
  `1/2+(beta-1/2+epsilon)+i(gamma-0)=rho+epsilon`; the existing completed germ has
  value `-m_rho`, matching the `S=-xi'/xi` orientation.
- [x] **Diagonal regularity.** The anchor is the real point `beta`; its imaginary part is zero, so
  `xi_ne_zero_of_abs_im_le_nine_halves` makes `-xi'/xi` analytic there.
- [x] **Strict invariant.** `xiSupportMultiplicity_pos` makes `-4m_rho^2<0` at every divisor point.
- [x] **Internal audit.** The corpus has the residue-filled one-point germ and several determinant
  criteria, but no theorem identifying this resonant two-node determinant or its exact scaled
  value.
- [x] **External parent audit.** The partial-fraction/Poisson contribution of a Xi zero to the real
  logarithmic derivative is classical; see Goldstein--Grigutis,
  [On a positivity property of the real part of logarithmic derivative of the Riemann xi-function](https://arxiv.org/abs/2201.08599).
  No exact scaled two-node determinant law or multiplicity-square interpretation was located in
  the targeted audit.  This is not a priority claim; novelty remains unverified.
- [x] **Dependency closure.** Analytic continuation of the filled germ, zero-freeness of the real
  anchor, positivity of multiplicity, continuity of squaring, and positivity of `epsilon^2`
  prove both `(PR1)` and the punctured-neighborhood negativity consequence.

## Formalisation target

Formalise the real reflection-odd kernel, the residue-filled determinant, the exact identity
`Dreg(epsilon)=epsilon^2 D(epsilon)` for `epsilon != 0`, the collision value `Dreg(0)=-4m_rho^2`,
and the resulting positive interval of strict two-node negativity.  No conditional hypothesis and
no zero enumeration is permitted.

## Formalisation result

Implemented in `formal/GaloisForLFunctions/RHTower/XiCompletedAperturePoleResonance.lean`:

- `xiCompletedApertureRegularizedResonantTwoPointDet_eq_scaled` proves the exact punctured identity
  `Dreg(epsilon)=epsilon^2 D(epsilon)`;
- `xiCompletedApertureRegularizedResonantTwoPointDet_zero` proves `Dreg(0)=-4m_rho^2`;
- `tendsto_xiCompletedApertureRegularizedResonantTwoPointDet` packages `(PR1)` as the exact limit;
- `exists_pos_xiCompletedApertureResonantTwoPointDet_neg` proves strict raw two-node negativity on
  a positive punctured aperture interval at every Xi divisor point.

Targeted Lean verification passed.  The capstones use only `propext`, `Classical.choice`, and
`Quot.sound`; there is no project axiom, placeholder, conditional RH hypothesis, or zero
enumeration.
