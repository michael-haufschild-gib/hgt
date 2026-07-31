# Complex-phase Möbius--Sonin Hardy incidence

- **ID:** `complex-phase-mobius-sonin-hardy-incidence`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[CORPUS-NEW FORMAL BRIDGE] [NOT RH]`
- **Statement:** One actual square-summable Möbius source carries arbitrary imaginary
  prime-log phase at no norm cost, reports the full complex squarefree Euler overlap and Fisher
  numerator, and admits contractive cofinal Sonin incidence at every fixed complex node
  \(\Re s>1\).

## Goal

Remove the real-ray restriction between the actual Möbius Hilbert source and the
Gamma/Sonin/Xi transport without assuming positivity, bounded inverse lifts, or a zero-fitted
space.  Establish the strongest source-side independent-quadrant theorem available before the
literal Burnol co-Poisson quotient.

## Theorems

For \(\sigma>1\), \(u\in\mathbb C\), and \(\Re u\ge0\), define
\[
 d_{\sigma,u}(n)
 =
 e^{-u(\sigma-1)\log n}\,w_\sigma(n).
\]
The imaginary factor is unitary, so
\[
 \|d_{\sigma,u}(n)\|
 =
 \|d_{\sigma,\Re u}(n)\|,
 \qquad
 \|d_{\sigma,u}\|_{\ell^2}\le1.
\]

On every safe node \(s=\sigma+u(\sigma-1)\), \(\Re s>1\),
\[
 \langle w_\sigma,d_{\sigma,u}\rangle
 =
 \frac{Z_{\rm sq}(s)}{Z_{\rm sq}(\sigma)}
 \]
and, for the completed critical Fisher tangent \(\chi_\sigma\),
\[
 \langle \chi_\sigma,d_{\sigma,u}\rangle
 =
 {\rm FisherScore}_{\rm sq}
   \bigl(\sigma,\sigma-1,u\bigr).
\]
Thus the existing singular Gamma graph reconstructs the completed squarefree current and the
continued Xi source column at every complex safe node, not only on real inward rays.

Let \(T\) be the actual contractive inward Sonin corner and \(A_N\) the cofinal shell
embedding.  Its reporter satisfies
\[
 \left|
 \left\langle T A_N\chi_\sigma,T A_Nd_{\sigma,u}\right\rangle
 \right|
 \le \|\chi_\sigma\|,
\]
uniformly in \(N\) and \(\Im u\).  For arbitrary moving safe complex nodes, one cofinal schedule
transports the reporter through the singular Gamma graph whenever the exact graph scale
\[
 \left|(\sigma_n-1)
   {Z_{\rm sq}(\sigma_n+u_n(\sigma_n-1))\over Z_{\rm sq}(\sigma_n)}
 \right|
\]
tends to zero.  Every fixed \(s\) with \(\Re s>1\) satisfies this condition along an explicit
critical normal path.

## What this changes

The formal source/Sonin incidence was previously restricted to real \(u\ge0\).  Complex height
is now a unitary prime-clock phase inside the same Hilbert source, while its overlap and Fisher
coefficient remain genuinely holomorphic in \(u\).  Independent-quadrant control on the Euler
side therefore has no imaginary-height energy cost.

This does **not** prove the corpus target
`XI_SOURCE_NORMAL_STOKES_BOCKSTEIN_DAGGER_LANDING`.  Burnol's quotient kernels
\(y_{w,j}=E_jk_{w,j}\), the co-Poisson source-error syzygy, and the first-trace
source-normal edge are still separate constructions.  The missing map remains
\[
 \Phi_{\rm src}:
 {\mathfrak B}_{\rm first\ trace}
 \longrightarrow
 {\mathfrak B}_{\Gamma/{\rm coP}/{\rm Sonin}},
\]
strict before closure, conormal-faithful at all confluent Xi jets, and dagger-natural.

## Hostile audit

1. This theorem controls \(\Re s>1\); it does not put critical-strip evaluations in the Hilbert
   source.  Negative real damping still leaves the source space.
2. The scalar `continuedPrimeArchSourceRelativeTrace` is existing analytic continuation.  Its
   appearance after the Gamma graph is not yet a literal co-Poisson reporter mate.
3. Uniform reporter norm before singular Gamma division does not give subexponential inverse
   lifts or RH.
4. The result does not repair the all-orders-flat/vacuum mismatch by a multiplier.  It supplies
   a complex source edge that a future essential source-normal exact-couple morphism can use.
5. Extending one schedule to finite or countable complex packets is routine diagonalization and
   is not the load-bearing research target.  Literal first-trace-to-co-Poisson Bockstein landing
   is.

## Lean certificate

Modules:

- `GaloisForLFunctions.RHTower.MobiusCriticalComplexPhaseHardySource`
- `GaloisForLFunctions.RHTower.SoninContractiveComplexHardyIncidence`

Principal declarations:

- `inner_infiniteMobiusSignedWeight_complexDamped_eq_squarefreeBoundaryOverlap`
- `inner_fisherTangent_complexDamped_eq_squarefreeFisherScore`
- `squarefreeMobiusGammaXiWardTransportV_actualComplexNode`
- `norm_soninContractive_complexHardyFisherReporter_le`
- `exists_soninContractiveCofinalMobiusGammaXiWardComplexMovingTransport`
- `exists_soninContractiveCofinalMobiusGammaXiWardFixedComplexNode`

Direct `lake env lean` checks pass.  Targeted `lake build` passes for both modules.  Axiom audit
reports only `propext`, `Classical.choice`, and `Quot.sound`.

Repository-wide `scripts/formal_tools.py lint` remains red because of pre-existing unrelated
umbrella-unreachable modules; neither new module is reported unreachable.

## Gates

- [x] 0 → 1: exact source and falsifiers stated
- [x] 1 → 2: exact algebraic/analytic proof closed
- [x] 2 → 3: Lean theorems compiled and axiom-audited
- [ ] 3 → 4: external novelty audit and publication packaging
- [ ] construct literal Burnol co-Poisson interfaces in Lean
- [ ] construct strict source-normal exact-couple morphism
- [ ] prove full Xi conormal Bockstein and dagger landing

## Log

- 2026-07-31 — Formalized complex phase-damped Möbius source, full complex overlap/Fisher
  reporting, depth-independent contractive Sonin bound, arbitrary moving complex incidence, and
  fixed complex Euler-node Rees chart.  Hostile audit keeps critical-strip continuation and
  source-normal co-Poisson dagger landing open.
