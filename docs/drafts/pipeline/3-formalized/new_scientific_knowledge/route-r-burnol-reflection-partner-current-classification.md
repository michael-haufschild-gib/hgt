# Route R Burnol reflection-partner current classification

- **ID:** `route-r-burnol-reflection-partner-current-classification`
- **Stage:** 3 — formalized
- **Type:** THEOREM (Lean) / EXACT REFLECTION CLASSIFIER
- **Route:** R
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [NOT RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RouteRBurnolReflectionPartnerCurrent.lean`

## Statement

Put `rho^dagger=1-conj(rho)`, `L=log 2`, and

```text
J(rho)=|(1-rho)^-1|^2-L^2|rho^-1|^2.
```

The functional-equation partner exchanges the reciprocal heads. Consequently

```text
J(rho)+J(rho^dagger)
  = (1-L^2)(|(1-rho)^-1|^2+|rho^-1|^2),

J(rho)-J(rho^dagger)
  = (1+L^2)(|(1-rho)^-1|^2-|rho^-1|^2)
  = (1+L^2)(2 Re rho-1)/(|rho|^2|1-rho|^2)
```

away from `rho=0,1`. Hence the pair sum is strictly positive, the odd difference has exactly the
horizontal sign, and

```text
J(rho)=J(rho^dagger) iff Re rho=1/2.
```

The normal completion current depends only on `Im rho`, which reflection preserves. Thus the same
odd-difference and equality classification holds for the completion-dressed current. On actual Xi
support, global partner equality for either bare or dressed current is equivalent to RH.

Principal Lean theorems:

```text
burnolCartierDividedShiftHeadFlux_add_reflectionPartner
burnolCartierDividedShiftHeadFlux_sub_reflectionPartner_eq_horizontal
burnolCartierDividedShiftHeadFlux_add_reflectionPartner_pos
burnolCartierDividedShiftHeadFlux_eq_reflectionPartner_iff
burnolXiCompletionDressedHeadCurrent_sub_reflectionPartner
riemannHypothesis_iff_forall_xiDivisor_burnolHeadFlux_eq_reflectionPartner
riemannHypothesis_iff_forall_xiDivisor_burnolDressedHeadCurrent_eq_reflectionPartner
```

## Dependency-closed paper proof `[PROVED HERE]`

Reflection gives `1-rho^dagger=conj(rho)` and
`|rho^dagger|=|1-rho|`, so substitution exchanges the two reciprocal squares. Adding and
subtracting gives the even and odd identities. The elementary norm identity

```text
|rho|^2-|1-rho|^2=2 Re rho-1
```

and inversion give the rational horizontal factorization. Since `0<log 2<1`, the even coefficient
`1-L^2` is positive. Both reciprocal squares are positive away from `0,1`. The odd coefficient and
denominator are also positive, so equality is precisely `Re rho=1/2`.

For the dressed current `D(rho)=A(Im rho)+J(rho)`, reflection preserves imaginary part, hence
`D(rho)-D(rho^dagger)=J(rho)-J(rho^dagger)`. Xi divisor points have nonzero imaginary part, so
neither pole occurs. Existing exact Xi/RH endpoint theorems convert pointwise critical-line
placement to the two global equivalences.

## Frontier impact

Functional-equation covariance cannot be used as an independent source annihilator by merely
declaring the scalar current reflection-invariant: that declaration is already RH-equivalent.
Completion does not repair this because it cancels from the reflection-odd coordinate. A valid
producer must yield a genuinely pre-divisor singular relation, not partner equality after scalar
landing.

## Gates and verification

- [x] complete dependency-closed paper proof
- [x] unconditional generic identities and unconditional global equivalences in Lean
- [x] no use of carrier annihilation, source sewing, source-dagger identity, or RH in the forward
  classifier
- [x] wired into `RHTower.lean`
- [x] direct `lake env lean` check
- [ ] final targeted `lake build` and axiom audit (recorded at session close)

## Log

- 2026-08-11 — reflection-partner decomposition extracted after the heavy-loop failures.
- 2026-08-11 — formalized and promoted to stage 3.
