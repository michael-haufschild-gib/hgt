# A one-sided rectangular power floor gives a zero-free region

- **ID:** `ccm-rectangular-power-lower-zero-free-region`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / QUANTITATIVE BRIDGE
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/CCMRectangularPowerLowerZeroFree.lean`

## Statement

Fix `L>0` and `alpha>=0`.  Suppose the positive-transverse rectangular coefficient has a global
one-sided power correction

```text
S_L(n)+C n^alpha>=0,      n>=1.
```

If the right Xi divisor is nonempty, Lean proves

```text
xiRightTransverseSup<=alpha
```

and hence every right-zero copy satisfies

```text
Re(rho-1/2)<=alpha.
```

The proof reuses the already formalized power-corrected Landau continuation.  If `alpha` were below
the transverse supremum, Landau transfer would make the original rectangular L-series converge at
a real point strictly left of its transverse boundary.  The existing exact shifted-pole order
theorem would then bound the supremum strictly below itself.

## Formal declarations

- `xiRightTransverseSup_le_of_xiRectangularRightPowerLower`
- `xiRightCenteredZero_re_le_of_xiRectangularRightPowerLower`

## Positive source consequence

The theorem quantifies partial progress: a source lower estimate of order `n^alpha` proves the
zero-free half-plane `Re rho<=1/2+alpha`.  Letting source exponents decrease to zero recovers the
already formalized all-epsilon subpower RH gate.  A constant floor is not required.

## Verification

- [x] current producing module rebuilt to eliminate stale-olean ambiguity
- [x] focused module build
- [x] formal lint
- [x] no new axiom, placeholder, opaque, or unsafe declaration

