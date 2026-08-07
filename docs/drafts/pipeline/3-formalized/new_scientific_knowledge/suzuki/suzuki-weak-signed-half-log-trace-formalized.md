# Bounded weak Suzuki zero modes have signed half-log traces

- **ID:** `suzuki-weak-signed-half-log-trace`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-weak-signed-half-log-trace.md`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/LogNormalEquationTrace.lean`,
  `formal/GaloisForLFunctions/HTGeometry/GammaTransportKernel.lean`,
  `formal/GaloisForLFunctions/HTGeometry/PenalizedMaximum.lean`,
  `formal/GaloisForLFunctions/HTGeometry/HalfLogCesaroAverage.lean`,
  `formal/GaloisForLFunctions/HTGeometry/BumpMollifierFamily.lean`,
  `formal/GaloisForLFunctions/HTGeometry/MollifierUniformApproximation.lean`,
  `formal/GaloisForLFunctions/HTGeometry/MollifierPositionCommutator.lean`

## Formal content

The card's `(4)` is proved end to end as `tendsto_halfLogTrace_mollified`:

```text
equation for f  +  object regularity of rho, f, rho*f
  ==>  Tendsto (fun L => sqrt L * (rho*f) L) atTop
         (nhds (A(L0) + integral_{L0}^infinity P(rho*f)/(4 L^(3/2))))
```

Every numbered step of the paper has a Lean counterpart:

| Card | Lean |
|---|---|
| `(6)` `integral_L^infinity k = -log(1-e^(-L))` | `integral_Ioi_gammaTransportKernel` |
| `(8)`,`(9)` jump-form pairing converges | `integral_abs_jumpFormIntegrand_le`, `integrableOn_id_mul_gammaTransportKernel_Ioi_zero` |
| `(11)` `A' = P F/(4 L^(3/2))` | `hasDerivAt_halfLogAverage` |
| `(12)` the averaged trace exists | `tendsto_halfLogAverage` |
| `(13)` `liminf H <= alpha <= limsup H` | `halfLogAverage_le`, `le_halfLogAverage` |
| `(14)` mollifier family | `BumpMollifierFamily` |
| `(15)` `R_full` commutes with convolution | `gammaTransport_mollify` |
| `(16)` `Y` commutes with convolution | `mollify_fullPrimitive` |
| `(17)` the position defect | `fullLogDirichlet_mollify'` |
| `(18)` the mollified equation | `mollified_equation`, `mollified_equation_halfLine` |
| `(19)`,`(20)` uniform source and profile bounds | `integral_bumpMollifier`, `sqrt_mul_abs_mollify_le` |
| `(22)` the penalized maximizer exists | `exists_isMaxOn_penalized` |
| `(23)` localisation and value | `abs_sub_le_sqrt_mul_of_isMaxOn`, `le_value_of_isMaxOn_penalized` |
| `(24)` the one-sided inequalities | `le_of_isMaxOn_penalized_shift` |
| `(4)` the trace exists | `tendsto_halfLogTrace_mollified` |

Every hypothesis of the top-level theorem is either regularity of the object (`Continuous`,
`Measurable`, boundedness, Lipschitz, vanishing on the negatives) or one of the card's own numbered
assertions. No hypothesis is a theorem proved elsewhere in the corpus: the transport bounds, the
one-sided inequalities, the boundedness side conditions and the averaged-trace limit are all
*derived* inside the chain.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs. Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Correction made to the paper card

The paper's `(11)` stated both `A(L) = Y(L)/(2 sqrt L)` and `A'(L) = P F(L)/(2 L^(3/2))`. These are
inconsistent: differentiating the first gives `P F(L)/(4 L^(3/2))`. The normalisation `A = Y/(2 sqrt L)`
is the one forced by `(13)` (it is the one for which `A` and `H` share a limit) and by the display
preceding `(28)`, so the derivative constant was the error. The card now reads `4 L^(3/2)`, matching
`hasDerivAt_halfLogAverage`.

## Open boundary

The Lean development proves the trace theorem for the *mollified* profile `rho*f`, which is what the
card's §5 argument produces. Transferring the conclusion back to the unmollified `F` — the card's
final sentence — uses `(21)`'s choice of `epsilon_n` and is a limit interchange in `n`, not a new
estimate; it is not formalized here.
