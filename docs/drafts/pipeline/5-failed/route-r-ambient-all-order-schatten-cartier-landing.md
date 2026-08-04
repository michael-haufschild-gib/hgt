# Route R ambient all-order Schatten Cartier landing

- **Stage:** 5-failed
- **Disposition:** falsified as an ambient producer
- **Positive survivor:** exact all-order Gamma-Bockstein wall, paper-proved and formalized

## Proposed mechanism

Construct before divisor specialization one continuous reporter from the all-prime source
Stokes boundary into

```text
intersection_(q>1) ell^q(P)
```

whose coefficient is the explicit Gamma Bockstein `Delta_t` for every strip parameter `|t|<1`.

## Falsification

The formalized sharp classification is

```text
Delta_t in intersection_(q>1) ell^q(P) <-> t=0
```

for every real `t`.  An ambient reporter with the proposed codomain would therefore imply `t=0`
for every parameter in its strip, contradiction.  Restricting the landing to Xi divisor points
does not repair the logic: its all-order membership is then equivalent to critical-line placement
and is not an independent source theorem.

Product topology, a divisor-fitted family of exponents, and fixed `S_2` landing also fail:
finite-support density erases the cofinal class, fitted exponents encode the selected divisor, and
the outer half-strip escapes fixed Hilbert--Schmidt regularity.

## Positive survivor

For every `q>0`,

```text
sum_p |Delta_t(p)|^q < infinity
  <-> t=0 or q(1-|t|)>1.
```

This is the exact variable-ideal spectrum of the retained Bockstein.  It rules out regularity-only
producer arguments and leaves one noncircular target: construct a source-derived corrected
`det2`/BV Stokes determinant comparison before Xi specialization, then compare source and physical
orientation monodromy without assuming any Schatten landing.

## Formal status

Formalized in
`GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean` and wired through the
`GaloisForLFunctions.RHTower` umbrella.
