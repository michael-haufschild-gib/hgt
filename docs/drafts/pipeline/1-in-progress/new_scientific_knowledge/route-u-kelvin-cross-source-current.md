# Route U Kelvin cross-source current

- **ID:** `route-u-kelvin-cross-source-current`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE ATTACK + SOURCE GEOMETRY
- **Parent:** `route-u-antipodal-prime-gamma-polarization`
- **Status:** `[PAPER-PROVED CORE] [LEAN IN PROGRESS] [NOVELTY UNVERIFIED]`

## Live obstruction

False RH now gives one fixed cofinal carrier whose actual antipodal channel pair has, at every
large integral hard-edge mass, a negative even diagonal, negative odd diagonal, or negative
even--odd cross capital.  Diagonal-only closure is false.  This card attacks literal geometry of
the cross branch.

## Conjecture--failure--pivot loop

### U-CROSS-SIGN -- cross density has a fixed pointwise sign

Conjecture: parity makes the archimedean even--odd cross density nonnegative, permitting a direct
source lower bound.

**Verdict:** `[FALSIFIED]`.  Put `A=a^2`, let `d` be common reciprocal-lift degree, and let `Q_E`,
`Q_O` be shifted-reversal polynomials of the antipodal even and odd channels.  Exact Kelvin laws
are

```text
Q_E(A^2/W) =  (A/W)^d Q_E(W),
Q_O(A^2/W) = -(A/W)^d Q_O(W)        (a>0, W>0).
```

Therefore their Gaussian cross density

```text
F_t(x)=Q_E(x^2) Q_O(x^2) exp(-t x^2)
```

obeys

```text
F_t(a^2/x)
 = -(a^2/x^2)^(2d) exp(-t*((a^2/x)^2-x^2)) F_t(x)    (x>0,t>0).
```

The multiplier after the minus sign is strictly positive.  Every nonzero Kelvin orbit contains
opposite signs.  Pointwise nonnegativity or nonpositivity forces orbitwise vanishing and cannot be
the Route-U cross mechanism.

### U-CROSS-CANCEL -- Kelvin partners cancel exactly after integration

Conjecture: anti-reciprocity makes the completed archimedean cross term vanish.

**Verdict:** `[FALSIFIED]`.  The Gaussian heat weight, Gamma phase rate, and inversion Jacobian are
not Kelvin-invariant.  Under `x -> a^2/x`, the paired measure contributes the explicit multiplier

```text
(a^2/x^2)^(2d+1) exp(-t*((a^2/x)^2-x^2)).
```

The cross term is an oriented modular defect, not a cancelling odd integral.

### U-KELVIN-CURRENT -- factor the exact paired modular defect

Replacement conjecture: retain the signed current and expose its only local weight mismatch.

**Verdict:** `[PAPER-PROVED CORE]`; Lean pending.

For any real weight `w`, define the Jacobian-paired cross current on `x>0` by

```text
J_w(x)=F_t(x) w(x) + (a^2/x^2) F_t(a^2/x) w(a^2/x).
```

Then

```text
J_w(x)
 = F_t(x) *
   [w(x) - (a^2/x^2)^(2d+1)
      exp(-t*((a^2/x)^2-x^2)) w(a^2/x)].                 (K.1)
```

At the self-dual seam `x=a`, odd parity gives

```text
Q_O(a^2)=0,  F_t(a)=0,  J_w(a)=0.                       (K.2)
```

For the literal archimedean source take `w=gammaHardyPhaseRate`.  Thus its cross contribution is
controlled exactly by one Gamma--heat modular-weight defect on a Kelvin fundamental domain.  No
pointwise energy argument survives.

## Dependency-closed proof

The common zero-padded coefficient vector reconstructs the reciprocal polynomial
`R_P(Z)=P(2a^2 Z-1)`.  Shifted reversal gives, for `W>0`,

```text
Q_P(W)=(A+W)^d P((A-W)/(A+W)).                           (K.3)
```

Replacing `P` by its antipode `P^-(u)=P(-u)` and substituting `A^2/W` in `(K.3)` gives

```text
Q_(P^-)(W)=(W/A)^d Q_P(A^2/W).                          (K.4)
```

Even and odd antipodal eigencoordinates satisfy `E^-=E`, `O^-=-O`; applying `(K.4)` proves the
two Kelvin laws.  Multiplying them and including `exp(-t x^2)` proves cross-density
anti-covariance.  Multiplication by the inversion Jacobian `A/x^2` and algebraic collection proves
`(K.1)`.  At `W=A`, the Cayley argument in `(K.3)` is zero and the odd channel evaluates to zero,
proving `(K.2)`.

## Significance and next wall

Generic reciprocal-polynomial algebra is `[REDISCOVERED]`; exact landing on the actual cofinal
Gamma--polar channel is a corpus-specific `[BRIDGE]`.  Scientific delta is a no-go plus a sharp
replacement: cross-source negativity is not hidden positive energy.  It is net flux caused by
failure of completed Gamma--heat--prime weights to be self-reciprocal under the physical hard-edge
involution.

After formalization, next hard problem is compare the Gamma modular defect in `(K.1)` with the
polar and prime cross terms of the exact completed-source identity.  Any proposed sign theorem
must preserve all three; dropping prime cross polarization would replay the diagonal mistake.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaKelvinCrossCurrent.lean`

- common-degree shifted-reversal evaluation formula `(K.3)`;
- antipode/Kelvin covariance `(K.4)`;
- actual even/odd Kelvin eigenlaws;
- cross-density anti-covariance and opposite-sign theorem;
- self-dual seam vanishing;
- arbitrary-weight paired current factorization `(K.1)`;
- literal `gammaHardyPhaseRate` specialization.

## Gates

- [x] Internal source audit
- [x] `U-CROSS-SIGN` falsified
- [x] `U-CROSS-CANCEL` falsified
- [x] `U-KELVIN-CURRENT` dependency-closed paper proof
- [ ] Hostile Lean feedback audit
- [ ] Exact Lean formalization and axiom audit
