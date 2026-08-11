# Mass-shifted adaptive two-source formation law

- **ID:** mass-shifted-adaptive-two-source-formation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, Conjecture 55
- **Statement:** Completed adaptive mixed-amplitude packet is rational–Gamma continuum formation minus labelwise von Mangoldt formation of same endogenous kernel.

## Result

For `w > 1/2` and polynomial amplitude `A`, define

\[
 \mathcal K_{w,A}(x)=\frac{x^{-(1/2+w)}}{4w^5}
 \int_0^\infty e^{-u}[u(w\log x+u/2)]^2
 Q_{1,c(A)}\!\left(\frac{u(w\log x+u/2)}{2w^2}\right)du.
\]

Then unconditionally

\[
 S_{2,M_1c(A)}(w^2)=
 \mathsf{Arch}_{w,2,M_1c(A)}+\int_1^\infty\mathcal K_{w,A}(x)dx
 -\sum_{m\ge0}\Lambda(m)\mathcal K_{w,A}(m).
\]

The admitted amplitude changes the kernel before Lebesgue or von Mangoldt formation. This is a
source law, not a fixed report on their scalar difference. At a flat null face the full second
null-gauge coefficient equals the odd-contact factor times this arithmetic source. Downstream, the
same identity holds after subtracting the exact lower-flag residual; no renewed flatness is used.

## Paper proof `[PROVED HERE]`

1. Split each completed source jet into rational–Gamma jet minus prime jet, then divide by the
   common nonzero normalization. Finite linearity gives the generic packet split.
2. The prime jet is the Chebyshev–Stieltjes integral of the normalized reverse-Bessel kernel.
   Finite integrability permits exchanging the packet sum and integral.
3. Atomize the Chebyshev–Stieltjes measure. Its atoms have mass `Λ(m)`, giving the literal labelled
   series with all prime-power labels retained until final summation.
4. Compare the generic split with the already proved archimedean plus
   Lebesgue-minus-Chebyshev discrepancy split. Cancellation identifies the rational–Gamma packet
   with archimedean jet plus Lebesgue formation of the same kernel.
5. Specialize the packet to `M₁ c(A)`. The adaptive reverse-Bessel carrier theorem rewrites its
   pointwise radial kernel as the Gamma integral, and the one-Euler midpoint theorem rewrites its
   factorial carrier as the mixed polynomial `Q₁,c(A)`.
6. Substitute both source formations into the completed packet. Existing bilinear-shear and
   null-gauge laws identify this same scalar with twice the adaptive shear, the admitted flat-face
   producer, and the lower-memory-corrected outgoing producer.

Every interchange and atomization uses existing corpus integrability theorems. No numerical
computation, asymptotic assumption, RH assumption, or new axiom occurs.

## Hostile conjecture loop

- Positive Gamma-sewn Gram lift — **failed:** a fixed positive-support null has zero first response;
  completion is signed Archimedean/Lebesgue/Chebyshev cancellation.
- Theta resolvent source — **failed for sign:** determinant weighting erases orientation; available
  quantile boundary source is lightlike but not the shifted null flag.
- Adaptive incoming-port killing — **failed typing:** theta boundary moments and shifted reciprocal
  null flags are different objects without a corpus connector.
- Möbius transport positivity — **failed circularity:** exact transport exists, but its positivity is
  equivalent to target RH-strength statement.
- Metric/Hodge lightlike reduction — **failed:** lightlike does not imply boundary kernel.
- Two-source formation before scalarization — **proved:** both measures see one endogenous signed
  mixed kernel, retaining amplitude and arithmetic labels.

## Strongest new principle

Remaining sign problem is admitted-cone domination of von Mangoldt formation by rational–Gamma
continuum formation. Pointwise positivity is neither needed nor plausible because mixed carrier
can change sign. This identifies exact arithmetic inequality still missing and preserves
lower-flag memory at outgoing events.

## Lean

- Module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Capstones:
  - `xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_arithmeticSource`
  - `two_mul_xiShiftedAdaptiveShear_eq_arithmeticSource`
  - `two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_arithmeticSource`
  - `two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_arithmeticSource`
- Direct check: PASS, `lake env lean ...AdaptiveArithmeticSourceLaw.lean`
- Target build: PASS, `lake build GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveArithmeticSourceLaw`
- Axiom audit: PASS; only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint: new module passes forbidden-declaration scan and is umbrella-wired; repository-wide
  lint remains red only because unrelated concurrently added Hedenmalm/HTGeometry modules are not
  wired into their umbrellas.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 dependency-closed paper proof
- [x] 2 → 3 unconditional Lean formalization, target build, axiom audit
- [ ] 3 → 4 publication-ready standalone paper

## Open successor

Prove admitted-cone source domination

\[
 \sum_m\Lambda(m)\mathcal K_{w,A}(m)
 \le \mathsf{Arch}_{w,2,M_1c(A)}+\int_1^\infty\mathcal K_{w,A}(x)dx
\]

for actual null-flag amplitudes, while transporting lower-contact residual at later events. This is
not proved here and is the exact remaining sign gate.
