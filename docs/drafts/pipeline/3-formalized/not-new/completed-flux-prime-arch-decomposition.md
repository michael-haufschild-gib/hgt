# Completed cross-order germ splits into fixed prime and archimedean germs

- **ID:** completed-flux-prime-arch-decomposition
- **Stage:** 3-formalized
- **Type:** NOT-NEW / ARITHMETIC ATTACHMENT BRIDGE
- **Source:** `CompletedFluxCrossOrderReflection` + `CompletedLogDerivStrip`
- **Statement:** `[PROVED]` At every point of the open critical strip, the removable completed-flux germ is locally the sum of a removable continued infinite-prime germ `x(-ζ'/ζ)(ρ+x)` and an analytic archimedean/boundary germ `x(-logDeriv archFactor)(ρ+x)`. The identity holds as analytic germs and therefore coefficientwise at every order.

## Goal

Attach the fixed all-order FE object to the actual continued von Mangoldt source and the completed
Gamma/boundary factor, without a finite prime packet, cutoff, or separately solved truncation.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven: local zeta peel and analytic-germ identity complete
- [x] 2 → 3  formalized: focused build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: requires quotient compatibility and RH-significance audit

## Approach

1. Strengthen the existing strip zeta factorization to retain the peeled identity
   `ζ(z)=(z-ρ)^m h(z)` on a ball with `h` analytic and nonzero.
2. Fill `x(-ζ'/ζ)(ρ+x)` at zero by `-m`; the peel makes this prime germ analytic and proves
   there are no other local zeta zeros.
3. The archimedean factor is analytic and nonzero throughout the strip, so its local flux germ is
   analytic and has zero constant term.
4. On the punctured peel ball, logarithmic differentiation of `ξ=archFactor·ζ` gives the
   completed germ as the sum of the two pieces.  The filled center agrees by residues.  Analytic
   germ equality then gives the same identity for all Taylor coefficients.

## Honest boundary

This would be an actual arithmetic-to-completed germ attachment.  It still does not turn the germ
into a nonzero pinned-affine quotient class or establish the positivity statement equivalent to RH.

## Proof

The retained strip peel gives `ζ(z)=(z-ρ)^m h(z)` on a ball, with `h` analytic and nonzero.
Consequently the residue-filled infinite-prime germ is locally
`-m-x logDeriv h(ρ+x)` and is analytic.  The strip archimedean factor is analytic and nonzero, so
`x(-logDeriv archFactor)(ρ+x)` is analytic with zero constant term.  The peel also excludes every
other local zeta zero.  On the punctured ball, logarithmic differentiation of
`ξ=archFactor·ζ` proves the sum identity; at the center the two filled residues agree.  Thus the
functions agree in a neighbourhood of zero.  Equality of all iterated derivatives yields the
coefficientwise identity for every natural order.

## Lean certificate

- Module: `formal/GaloisForLFunctions/RHTower/CompletedFluxPrimeArchDecomposition.lean`
- Retained peel: `exists_riemannZeta_peel_ball_of_mem_strip`
- Prime removability: `infinitePrimeFluxGermAt_analyticAt_zero`
- Archimedean removability: `archimedeanBoundaryFluxGermAt_analyticAt_zero`
- Germ attachment: `completedFluxGermAt_eq_prime_add_archimedean_eventually`
- All-order attachment: `completedFluxTaylorCoeff_eq_prime_add_archimedean`
- Build: `lake build GaloisForLFunctions.RHTower.CompletedFluxPrimeArchDecomposition` PASS
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
