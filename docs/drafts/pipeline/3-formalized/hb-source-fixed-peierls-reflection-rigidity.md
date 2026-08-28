# HB source-fixed Peierls reflection rigidity

- **ID:** HB-SFPRR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · HB `LAND ORIENT DYN`
- **Statement:** In one divisor-independent cyclic/skew Peierls theory, Schwarz covariance of the two linear branch families makes the cubic cut reflection-odd automatically. Incidence with the literal Hermitian BM second-harmonic candidate on both orientations forces the Xi fibre onto the critical line; global incidence forces RH.

## Goal

Eliminate bioriented/global compatibility as an independent HB premise. Reduce remaining producer burden to literal source incidence plus already-corpus Schwarz branch covariance and Peierls axioms.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search found Peierls branch-swap antisymmetry and exact Hermitian BM reflection receiver but no bridge
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean theorems, targeted build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone exposition

## Theorem HC13

Fix one augmented field/residual pairing, symmetric quadratic residual, and retarded-minus-advanced
propagator before choosing an Xi divisor. Assume cyclicity and Peierls skewness. Let `p(q),m(q)` be
branch families obeying Schwarz reflection `p(reflect q)=m(q)` and `m(reflect q)=p(q)`.

Then the phase-normalized cubic Peierls cut is reflection-odd. If its two oriented values equal the
literal unit-seed Hermitian BM candidates at `q` and `reflect q`, then `Re(q)=1/2`. If incidence
holds on every Xi copy, RH follows.

## Proof

Corpus cubic Peierls polarization proves that swapping the two linear branches negates the cut.
Schwarz covariance converts functional-equation reflection into exactly this swap, so a single
source-fixed Peierls construction supplies bioriented compatibility automatically.

Direct expansion shows that the two reflected literal BM candidates sum to twice the existing
Hermitian-source reflection current. The Peierls cut sum is zero, hence this Hermitian current
vanishes. Its exact corpus zero-locus is `Re(q)=1/2`. Applying the same local argument to every Xi
copy and the exact universal Hermitian-current criterion proves RH.

## Novelty audit (2026-08-28)

Corpus search found the separate Peierls swap law, Schwarz frequency/response pairing, and
Hermitian BM reflection receiver, but no theorem composing them into local criticality or a global
RH implication. Literature establishes covariant Peierls brackets for constrained gauge theories,
group invariance of Peierls brackets, reflection-based conserved Kerr bilinear forms, and nonlinear
mode excitation; the audit found no Birmingham--Mokhtari/Xi theorem where one source-fixed
Schwarz-covariant Peierls incidence forces criticality or RH. Primary references: Khavkine,
[Covariant phase space, constraints, gauge and the Peierls formula](https://arxiv.org/abs/1402.1282);
Bimonte--Esposito--Marmo--Stornaiolo,
[Peierls Brackets in Field Theory](https://arxiv.org/abs/hep-th/0301113);
Green--Hollands--Sberna--Toomani--Zimmerman,
[Conserved currents for Kerr and orthogonality of quasinormal modes](https://arxiv.org/abs/2210.15935);
Sberna--Bosch--East--Green--Lehner,
[Nonlinear effects in the black hole ringdown: Absorption-induced mode excitation](https://arxiv.org/abs/2112.11168).

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFixedPeierlsReflectionRigidity`
- Theorems:
  - `d4BMXiSecondHarmonicPeierlsPolarizedCutCandidate_reflection_add_eq_two_mul_hermitianCurrent`
  - `d4GaugeFixedTeukolskySourceFixedPeierlsCubicCut_reflection_odd`
  - `d4BMXiSourceFixedPeierls_BM_incidence_forces_criticalLine`
  - `d4BMXiSourceFixedPeierls_global_BM_incidence_forces_rh`
- Axioms: only Mathlib foundations `propext`, `Classical.choice`, `Quot.sound`.
- Direct `lake env lean` check and target-specific `lake build` pass; module wired into RHTower umbrella.
- No `sorry`, `admit`, added `axiom`, `opaque`, or `unsafe` declaration. Repository-wide lint reports only unrelated unreachable modules.

## Proof-burden reduction

HB no longer needs an additional bioriented/global compatibility theorem after construction of one
fixed cyclic/skew Peierls theory with Schwarz-swapped physical branches. Those structural facts
force compatibility. Remaining hard premise is now singular: prove literal augmented
Einstein--Teukolsky source incidence with the BM candidate before divisor specialization.

## Log

- 2026-08-28 — conjectured from corpus Peierls swap law, Schwarz frequency pairing, and Hermitian BM reflection receiver.
- 2026-08-28 — local two-orientation theorem proved; global RH corollary derived.
- 2026-08-28 — targeted build, axiom audit, umbrella wiring, literature audit, and lint-scope audit completed.
