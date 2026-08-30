# Complex-character rigidity of finite-variation FZZ reflection

- **ID:** FZZ-P-COMPLEX-CHARACTER-NONLOCAL-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE KILL
- **Source:** `FZZCigarParityDelaySourceContinuation` · `ThetaCuspHawkingFZZParitySignedNonlocalMomentDeterminacyNoGo` · `HTGeometry.FlowCharFunUniqueness`
- **Lean:** `GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParityComplexCharacterNonlocalRigidityNoGo`
- **Status:** `[LEAN-PROVED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## RH proof chain and discharged burden

This kills the finite-variation complex-kernel realization of the surviving pre-divisor arrow

`literal complex FZZ parity-delay Mellin source → finite-variation nonlocal FE reflection → universal reflected-information stationarity → FZZCigarParityMellinComplete → RH`.

Earlier no-gos required positivity or an exponential moment window. This theorem covers every finite signed/complex kernel represented by four finite Jordan parts, including moment-indeterminate kernels. A remaining FZZ-P completion must now be genuinely beyond finite variation, fail universal complex-order covariance, depend on selected spectral modes, or retain the forced essential singularity.

## Theorem `[LEAN-PROVED]`

Fix positive delay `t`, put `a=t⁻¹`, `c=aF(t)`, and use logarithmic output coordinate `x=log u`. Represent a finite complex kernel by real Jordan parts `α₊,α₋` and imaginary Jordan parts `β₊,β₋`. Universal reflection at every imaginary Mellin order says

`(α̂₊-α̂₋)(ξ) + i(β̂₊-β̂₋)(ξ) = c exp(iξ log a)` for every real `ξ`.

For each positive measure, the transform at `-ξ` is the conjugate transform at `ξ`. Comparing covariance at `-ξ` with conjugated covariance at `ξ` forces the imaginary transform to vanish. The real transform then equals the target transform. Fourier–Stieltjes uniqueness yields the exact classification

`β₊ = β₋`, `α₊ = α₋ + cδ_(log a)`.

No support, moment, or exponential-window hypothesis is used. Reciprocal-Fermi undressing gives exact real net mass

`a(exp a+1)/(exp t+1)`

and zero imaginary net mass. Four-part variation dominates this quantity, whose reciprocal-depth ultraviolet sequence exceeds every polynomial envelope by the existing local theorem. Therefore no polynomially tempered data of this class exist.

## Formal certificate

- Exact imaginary classification: `FZZCigarParityComplexCharacterNonlocalFEReflectionData.imaginaryPart_eq`
- Exact real classification: `FZZCigarParityComplexCharacterNonlocalFEReflectionData.realPart_eq`
- Exact undressed mass: `FZZCigarParityComplexCharacterNonlocalFEReflectionData.undressedRealNet_eq`
- Sharp variation lower bound: `FZZCigarParityComplexCharacterNonlocalFEReflectionData.forcedWeight_le_undressedVariation`
- Route kill: `no_polynomiallyTempered_FZZCigarParityComplexCharacterNonlocalFEReflectionData`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingFZZParityComplexCharacterNonlocalRigidityNoGo.lean`
- Targeted audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingFZZParityComplexCharacterNonlocalRigidityNoGo`
- Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- Umbrella: wired into `formal/GaloisForLFunctions/RHTower.lean`
- Lint: module absent from failures; global run currently fails only on unrelated concurrent unwired modules.

## Novelty and hostile audit

- `[CORPUS]` Complex FZZ Mellin source and finite-measure Fourier uniqueness existed separately; neither prior no-go removed moment indeterminacy.
- `[LITERATURE]` FZZ duality/reflection amplitudes and Fourier–Stieltjes uniqueness are established separately. Audit found no Fermi-delay finite-complex-kernel classification, reciprocal undressing law, or FZZ/RH route obstruction of this form.
- Novelty claim is limited to the source-specific assembly, exact classification, and route consequence; priority remains provisional pending independent expert review.
- The law is pre-divisor and quantified over source characters. It contains no Xi zero, RH premise, or divisor-selected parameter.

## No-go closure

- **Exact killing mechanism:** Fourier completeness of every imaginary Mellin character plus conjugate symmetry at `ξ/-ξ`.
- **Strongest positive survivor:** Real net kernel is exactly the reciprocal atom; imaginary net kernel cancels identically.
- **New insight:** Moment indeterminacy is not a genuine FZZ loophole once the full complex Mellin source, rather than only its integer jet, transforms covariantly.
- **Remaining route:** Only non-finite-variation/distributional, non-universal, divisor-dependent, or essentially singular completion survives.

## Gates

- [x] 0 → 1  exact source-derived claim and audits
- [x] 1 → 2  dependency-closed paper proof and hostile proof audit
- [x] 2 → 3  exact Lean theorem, direct/targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4  publication-ready

## Log

- 2026-08-30 — conjectured from corpus complex-Mellin source after signed moment-determinacy collapse.
- 2026-08-30 — paper proof closed via four-Jordan-part Fourier rigidity.
- 2026-08-30 — formalized, targeted-built, axiom-audited, wired, and promoted.
