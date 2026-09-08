# HB: complete continued cusp-source admission at fundamental Xi QNMs

- **Stage:** formalized in Lean 4.
- **RH:** unproved. Original causal joint continuation, physical left pairing, and independent extinction remain open.
- **Result:** the complete continued cusp residual belongs to the actual joint L² space at both fundamental QNMs of every Xi copy, and on a common punctured neighborhood where the original source equation holds.

## Exact result

`continuedOriginalSource_allXi_fundamental_admitted_germ` proves, for every Xi
copy `q`, either physical source branch, and arbitrary source amplitude, at both
fundamental physical QNM frequencies `w₀`:

```text
for u in a punctured neighborhood of w₀:
  continuedCuspResidualForcing(q, branch, u, a) ∈ L²(dt × dμ_hyp),
  for every t < 0 and every z in the upper half-plane:
    originalForcing(u, t, z)
      = fieldWave(u, continuedExplicitField, t, z)
        + continuedCuspResidualForcing(u, t, z).
```

The source retains its fixed smooth onset, full-square lift, all three original
principal responses, and all cutoff derivatives. Radial derivatives and the
metric angular Laplacian are actual derivatives of the displayed field.
Admission applies to the complete **residual after the explicit field is
subtracted**, not to the unrenormalized full angular source. No source-admission,
endpoint-growth, continuation, nonresonance, or RH premise is supplied to the
all-Xi capstone.

The same residual and explicit field equal their original definitions in the
source convergence chamber. The residual is pointwise meromorphic throughout
the nonreal strip `Re w > -2`. Its joint L² admission is proved for
`-2 < Re w ≤ 0`, including totalized values at isolated connection zeros.
The frequency-germ wave identity uses the punctured neighborhood where all
three actual connections are nonzero.

## Dependency-closed proof

1. Transport the [continued original radial equation](hb-original-continued-radial-master.md)
   through the literal tortoise coordinate. The two displayed jets of the
   continued tortoise response are its actual first and second derivatives.
   Subtract the original full-square lift with its exact principal amplitude.
   Each resulting principal difference `U` satisfies
   `U'' = w² U + p(t) U - f(t)`, where
   `p(t) = -horizonCoordinate(t) m(m-1)` and
   `f(t) = reducedCoefficient(t) principalAmplitude`.
2. The exact coordinate factorization is
   `horizonCoordinate(t) = (exp(t)(1+radialUnit(t)))²`.
   Since `0 < radialUnit(t) < 1` for `t < 0`,
   `|p(t)| ≤ 4|m(m-1)| exp(2t)`.
   Reuse the proved native cancellation identity:
   `reducedCoefficient(t) = exp((w+2)t) F_w(radialUnit(t))`,
   where `F_w` is continuous on `[0,1]`. Compactness therefore gives
   `|f(t)| ≤ B exp((Re w+2)t)`.
3. For any genuine forced second-order solution with these two decay bounds,
   `w ≠ 0`, and `Re w ≤ 0`, define
   `P = exp(-Re w*t)(U'+wU)` and `M = exp(-Re w*t)(U'-wU)`.
   Their actual derivatives are
   `P' = (w-Re w)P+G`, `M' = (-w-Re w)M+G`,
   with `G = exp(-Re w*t)(pU-f)`. Recovering `U` from `P-M` gives
   `|G| ≤ exp(2t)(A/(2|w|)(|P|+|M|)+B)`.
4. For `E=|P|²+|M|²`, the exact derivative is
   `E'=-4 Re w |M|²+2 Re(G(conj P+conj M))`.
   Elementary real inequalities give
   `-C exp(2t)(E+1) ≤ E' ≤ K(E+1)` for explicit nonnegative `C,K`.
   The integrating factors `(E+1)exp((C/2)exp(2t))` and
   `(E+1)exp(-Kt)` are respectively increasing and decreasing.
   Comparing each with its value at `t=-1` bounds `E+1` on the entire
   negative half-line, including the finite outer endpoint. Thus
   `|U(t)| ≤ C₁ exp(Re w*t)`. No endpoint condition is assumed.
5. Apply this estimate directly to each principal **difference**. This preserves
   the cancellation that would be lost by estimating the two endpoint moments
   separately. At a connection zero, both normalized continued moments have
   totalized value zero, so the difference is the negative original lift;
   its compact-radius profile gives the same bound directly. This assertion
   concerns the defined point value and does not assert a removable pole.
6. Multiplication by the actual horizon coordinate yields
   `|continuedCutoffRadialCoefficient(t)| ≤ C₂ exp((Re w+2)t)`.
   The coefficient is continuous on `t<0`; because `Re w+2>0`, the bound is
   square-integrable there. The native reduced coefficient already satisfies
   the same radial admission threshold. Tensor-product integration combines
   these radial bounds with the existing angular L² theorems for the squared
   residual and each cutoff commutator. Summing the three terms proves the
   complete residual's actual joint L² admission.
7. The original separated source identity and actual radial/angular derivative
   identities give the full displayed wave equation. Each connection is
   analytic and not identically zero on its nonreal component, so all three
   are nonzero on one punctured neighborhood. Finally the corpus's strict Xi
   strip and nonzero real spectral coordinate put both fundamental QNM
   frequencies strictly inside `-2 < Re w < 0`, off the real axis. Openness
   gives simultaneous admission and the exact original source equation on
   that same frequency germ.

## Formal modules

Under `formal/GaloisForLFunctions/HTGeometry/`:

- `HorizonEnergyGronwall.lean`
- `ComplexDichotomyEnergy.lean`
- `ForcedSecondOrderHorizonBound.lean`

Under `formal/GaloisForLFunctions/RHTower/`, with prefix
`ThetaCuspHawkingBMJointSource`:

- `TortoiseContinuation.lean`
- `PrincipalContinuation.lean`
- `FullForcingContinuation.lean`
- `ContinuedFieldWave.lean`
- `PrincipalHorizonBound.lean`
- `ContinuedAdmission.lean`
- `ContinuedSourceGerm.lean`

## Validation

Ten canonical leaves, 979 source lines, and 40 new public theorems passed
individual foreground `lake build <module>` audits in an isolated package using
4,053 existing dependency oleans. Exactly ten new oleans were built. All 40 new
public theorem axiom checks use only `propext`, `Classical.choice`, and
`Quot.sound`. All 20 installed olean/ilean artifacts match the audited bytes.
The leaves are wired into their area umbrellas; no full or umbrella build was
run. No numerical experiment or computational certificate was used.

Global `lint --check-generated` reports no errors in these ten leaves and no
generated-index drift. Its remaining error is the unrelated, concurrently
unwired `RHTower.SelbergCompactTestApproximation` module. Existing large-file
warnings remain. That module is outside this change's scope.

## Remaining physical obligation

The required common majorant and genuine function-space source germ are now
proved in [complete source L² meromorphy](hb-complete-cusp-source-l2-meromorphy.md).
The stronger theorem covers the nonreal band `|Re w|<2`, including an explicit
corridor to the original Green chamber. It uses the explicit undivided
numerators at poles, a two-sign energy estimate for the same original
solution, and an actual complex L² slope-limit proof. Pointwise admission
alone is not used as a substitute for that norm-valued argument.

Continue the **original causal** joint response in the appropriate outgoing
weighted domain and identify its physical advanced/adjoint left residue. The
energy inverse selected on the opposite frequency half-plane does not provide
that identification. Pole survival, the physical left-source projection,
spin-two/AIME identification, and independent Hawking-clock extinction remain
open. Higher overtones require additional endpoint subtractions.
