# Sonin aperture-covariant Euler graph

- **ID:** `sonin-aperture-covariant-euler-graph`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED IN LEAN] [PROOF-CONTRIBUTING INFRASTRUCTURE]`
- **Statement:** Normalized dilation by `r` and by `r⁻¹` send the Sonin carrier of aperture `a` into the carrier of aperture `a/r`; consequently the symmetric Euler generator `U_r + U_r⁻¹` preserves the inductive Sonin aperture tower.

## Main theorem

Let

\[
K_a=\{f\in L^2(\mathbb R)^{\mathrm{ev}}:
f|_{[-a,a]}=0,\ \widehat f|_{[-a,a]}=0\}.
\]

For `a ≥ 0` and `r ≥ 1`, normalized dilation satisfies

\[
U_rK_a\subseteq K_{a/r},
\qquad
U_r^{-1}K_a\subseteq K_{a/r},
\]

and therefore

\[
(U_r+U_r^{-1})K_a\subseteq K_{a/r}.
\]

The two halves are genuinely polarized.  For `U_r`, the physical cutoff at `a/r` transports
exactly to the cutoff at `a`, while its Fourier cutoff transports to the smaller cutoff at
`a/r²`.  For `U_r⁻¹`, these roles are reversed.  Cutoff nesting closes the smaller constraint.

Lean theorems:

- `dilation_mem_centralSoninCarrier_inv_mul`
- `inverseDilation_mem_centralSoninCarrier_inv_mul`
- `dilationSum_mem_centralSoninCarrier_inv_mul`

in `formal/GaloisForLFunctions/RHTower/SoninEulerCalkinPartialIsometry.lean`.

## Proof contribution

This removes the need to postulate a separate support domain for every prime dilation.  The
algebraic union of positive-aperture Sonin carriers is a canonical aperture-losing domain for
every finite Euler block: each prime acts inside the same nested tower, with an explicit loss
factor equal to that prime.

It strengthens the live top-down chain to

\[
\begin{aligned}
&\text{Xi-zero radical annihilates the resolvent-dressed Mellin-scattering connection}\
&\Longrightarrow \text{finite seam Gram coboundaries are compact}\
\Longrightarrow \text{prime seam coherence}\
\Longrightarrow \text{common charge vanishes by cofinal decay}\
\Longrightarrow \mathrm{RH}.
\end{aligned}
\]

The Euler support-domain part of the first arrow is now unconditional.  Three harder interfaces
remain separate:

1. `[DISCHARGED ON PAPER; LEAN OPEN]` extend the Mellin-scattering commutator and its
   prolate-resolvent dressing to a compatible rigged form core;
2. construct any additional common graph needed by the genuine semilocal prolate grading, which
   is not the same as the dilation support tower proved here;
3. prove the value relation that makes the actual Xi zero evaluator annihilate the dressed
   connection.

The theorem removes only the repeated prime-by-prime Sonin support-domain assumption.  A later
paper theorem,
`../2-fully-proven/not_new_scientific_knowledge/sonin-burnol-conductor-cutoff-bounded-graph-law.md`,
discharges interface 1 at paper level: reflection through Burnol's conductor converts the
logarithmic-position anomaly to a bounded BMO Hankel commutator, and the exact two-projection
resolvent dresses it through the Sonin projection.  This has not yet been formalized in Lean.
Interfaces 2 and 3, and the source-compatible relative trace/positivity theorem, remain open.

## Gates

- [x] 0 → 1: exact Sonin carrier and dilation action identified
- [x] 1 → 2: direct cutoff-conjugation proof with both polarizations
- [x] 2 → 3: three Lean theorems compile; axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4: integrate with a proved Xi-zero connection-annihilation identity

## Verification

- `lake build GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry`
- Direct `#print axioms` audit of all three declarations
