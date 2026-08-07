# Burnol finite-holonomy/Cauchy sector separation

- **ID:** `burnol-holonomy-cauchy-sector-separation`
- **Stage:** 1-in-progress
- **Type:** THEOREM / NO-GO CLOSURE
- **Conjecture label:** C13
- **Inputs:** `BurnolCoPoissonQuotientOrder`, `BurnolDividedShiftPhysicalDissipativity`,
  `BurnolReflectedCoShiftCartierContinuation`

## Conjecture under attack

The finite-aperture Berezin holonomy might supply the missing forward/reflected Cartier sewing by
being an aperture discretisation of Burnol's one-sided divided-shift resolvent.

## Hostile audit

This direct identification is false. Every finite bilateral aperture holonomy, and its compression
to the co-Poisson quotient, is self-adjoint and Fourier-odd. Burnol's divided shift is strictly
accretive on every nonzero vector in the open right half-plane. If the two operators were equal,
Fourier oddness would send the strictly positive real quadratic form at `f` to its negative at the
nonzero vector `F f`, contradicting strict accretivity there.

## Positive survivor to prove

For every `Re rho > 1/2`, every positive source/target aperture, and every dilation ratio `r > 1`,
the Mellin divided-shift operator is unequal to the compressed bilateral aperture holonomy. More
generally, no Fourier-odd operator can have strictly positive real quadratic form on every nonzero
vector when the Fourier involution is unitary.

This forces the next viable Frankenstein bridge into a different category: a non-self-adjoint,
one-sided Mellin-phase boundary port. Real finite-holonomy superpositions cannot close Cartier
sewing.

## Paper proof

Let `J` be the cosine involution, `T` the divided shift, and `H` a compressed finite holonomy.
Assume `T = H`. Existing quotient transport gives `J H J = -H`, hence `J T J = -T`. For nonzero
`f`, unitarity and involutivity of `J` give

```text
Re <Jf, T Jf> = Re <Jf, -J(Tf)> = -Re <f,Tf>.
```

Strict accretivity gives both real parts strictly positive because both `f` and `Jf` are nonzero.
Contradiction.

## Novelty audit

Targeted search of Burnol's co-Poisson/Sonine papers found co-Poisson intertwining, Sonine spaces,
and zero-evaluation systems, but no finite-holonomy versus one-sided-Cauchy sector-separation
theorem. Provisional novelty: new synthesis of corpus-owned finite holonomy and strict Cauchy
accretivity. Primary sources checked: Burnol (2004), *Two complete and minimal systems associated
with the zeros of the Riemann zeta function*; Burnol (2007), *Entrelacement de co-Poisson*.

## Gates

- [x] Exact conjecture and failure mechanism frozen
- [x] Dependency-closed paper proof
- [ ] Lean formalization and axiom audit
- [ ] Promote to Stage 2/3 after exact source verification

