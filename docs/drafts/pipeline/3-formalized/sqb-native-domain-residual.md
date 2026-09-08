# SQB native scattering in the actual modular domain

Status: formalized; targeted build and all-export axiom audit passed. RH remains
open. The repository lint run reports unrelated concurrent wiring errors.

Full chain: original Maass source → positive modular curvature and exact mass →
Maass-specific quarter domination → Selberg gap → independently constructed Xi
spectral occurrence → RH. This work checks the last gate in the actual constructed
modular operator domain. The frontier map is read-only.

## Corpus starting point

Broad OR searches covered source products (351 declarations / 205 modules),
occurrence (317 / 144), differential lifts (754 / 159), scattering/resonance/spectrum
(6234 / 1347), Eisenstein/modular/eigenfunction (9320 / 672), and residual mechanisms
(5831 / 1865). These are complete returned metadata sets, not complete proof-body
inspection. Inspected original cusp operator, packet, and resolvent proof bodies.

`ThetaCuspHawkingBMOperatorCore` identifies the actual Friedrichs operator A as
`1−Delta_H`. `ThetaCuspHawkingBMCuspPacketApproximation` constructs normalized
compact cusp packets u(tau,L) in its original domain, with exact residual square
`C1(tau)/L²+C2/L⁴` at `5/4+tau²`. This includes the shift by one and cannot be
identified directly with the unshifted Maass Casimir. `SelfAdjointResolvent`
supplies the imaginary residual bound for every domain vector. The exact
Pythagorean identity is already proved in `ThetaCuspHawkingTeukolskyTiltedAngularLeakage`.

## Paper proof target

For every real tau, eta and positive L, the same actual unit packet satisfies

`||A u − (5/4+tau²+i eta)u||² = eta²+C1(tau)/L²+C2/L⁴`.

Symmetry removes the cross term between the real residual and the imaginary
multiple of u. Thus these normalized original-domain residuals converge to
`|eta|`, which the self-adjoint lower bound proves is optimal over all unit
domain vectors. This is a constructed sharp source estimate, with no spectral
occurrence or approximate-vector premise.

For an actual Xi zero rho=beta+i gamma, native scattering has s=rho/2 and
shifted energy `z=1+s(1−s)`. Exact algebra gives

`Re z=5/4+(gamma²−(1−beta)²)/4`, `Im z=gamma(1−beta)/2`.

The existing source-pure Xi height theorem gives gamma²>1; the open strip gives
0<beta<1. Consequently Re z>5/4 and the optimal unit residual is strictly
positive: `|gamma|(1−beta)/2`. Choosing tau=sqrt(Re z−5/4) in the actual packets
attains that floor in the limit. At a critical zero the floor is `|gamma|/4`.
This excludes literal native scattering parameters from approximate eigenvalue
occurrence in this domain even for critical zeros. It does not exclude a different
source construction or the previously constructed entire transform; it specifies
the exact change that a genuine occurrence map must make.

## Checklist

- [x] Broad corpus discovery and inspect actual operator/source proofs.
- [x] Derive exact residual floor and constructive sharpness on paper.
- [x] Check APIs and complete scratch proofs using one foreground Lean process.
- [x] Formalize source theorem and actual-Xi endpoint.
- [x] Wire module and finish targeted audit.
- [x] Targeted final builds, all-export axiom audit, and strongest positive survivor.
- [x] Run repository lint and record unrelated concurrent wiring failures.

## Exact positive survivor and current audit

`formal/GaloisForLFunctions/RHTower/SelbergScatteringNativeResidual.lean` contains
23 public declarations under `RHTower.SelbergScatteringNativeResidual`.
`cuspUnitPacket_complex_residual_sq` keeps both finite-cutoff derivative costs.
`xiNativePacket` is an explicit sequence in the original modular operator domain,
not a witness supplied by a spectrum premise. Its norm is exactly one and its
residual tends to `xiResidualFloor`.

`xi_residual_isGLB` states that this floor is the greatest lower bound of all unit
domain residuals. Its lower-bound half uses self-adjointness. For optimality,
any purported lower bound applies to every constructed packet, so passing to
the proved residual limit bounds it by the same floor. The strict positive floor
then excludes every unit approximate eigenvector sequence at the literal native
scattering energy, not merely the constructed packet family.

Scratch `/tmp/sqb_native_full.lean` and direct source check passed without warnings.
Final audit passed with
`lake build GaloisForLFunctions.RHTower.SelbergScatteringNativeResidual`.
Dependency preflights exposed stale nodes in the actual cusp-packet source chain;
47 necessary modules were audited serially before the final target. Every one of
these 48 commands built exactly its named module, with one foreground Lean compiler
process. The final target took 7.3 seconds including command overhead; no full or
umbrella build ran. RHTower imports the finished module exactly once.

All 23 public exports passed `#print axioms` in a `/tmp` scratch file, with only
`propext`, `Classical.choice`, and `Quot.sound`. The kernel-checked capstones are
`xi_residual_isGLB` and `xi_scattering_no_approximate_eigenvectors`; neither assumes
RH, a Selberg bound, or a spectral occurrence. The actual packet construction
supplies nonempty unit-domain witnesses. No new axioms, proof holes, or numerical
proof certificates were introduced. New source emits no warnings; required
older modules replay existing diagnostics. All exports are indexed, and source
whitespace, proof-token, and umbrella checks passed.

The final repository lint run reports the following unrelated in-progress modules
missing from their own umbrellas. These were not modified by this task:


- `GaloisForLFunctions.RHTower.SelbergMaassCurrentFunctional`
- `GaloisForLFunctions.RHTower.SelbergMaassCurrentTests`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawBounds`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawDivided`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawEndpoints`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawEvolution`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawInteraction`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawScattering`
- `GaloisForLFunctions.HTGeometry.FokasLenellsRawZero`

Existing large-file warnings also remain. This is a repository-wide wiring
limitation; the audited native-residual module has no lint errors.

## Remaining RH work

This retires only literal native-scattering approximate occurrence in the
constructed modular Hilbert domain. Its [narrow no-go closure](../5-failed/sqb-native-scattering-approximate-occurrence.md)
retains the exact constructive infimum law. The source-specific Selberg quarter
inequality and independent Xi occurrence are still open. The entire transform's
scalar compatibility does not itself construct its unbounded operator domain or
transport an original scattering source into it. The frontier map was read-only
for this task.
