# Complete original Fourier reconstruction for weighted top stress

- Stage: paused after duplication audit; no new Lean module promoted
- Parent: [Selberg conjecturing loop](../../selberg-quarter-conjecturing-loop.md), cycle55.
- Objective: derive the complete Fourier expansion of the physical top stress and combine its signed-frequency weights with the proved arithmetic Wronskian/tail kernel.

## Evidence and conjecture

Cycle54 was progress: source hash revalidated unchanged;30 public declarations and all final audits passed. The full Selberg endpoint remains active and unproved.

Explicit-OR weighted Fourier/sawtooth/Fourier commutator/bilinear Fourier/absolute Fourier/Fourier reconstruction search retrieved295 declarations across62 modules. A second explicit-OR Sobolev/absolutely summable/C1 query within Fourier modules retrieved10 declarations across6 modules. Inspected `PeriodicFourierDecay`'s full periodic coefficient decay and pointwise inversion proofs, `DeningerFourierBridge`'s circle identification and uniform evaluation proof, and `EulerMaclaurinSawtooth.integral_sawtooth_trapezoid_cell`, including its exact nonvanishing endpoint terms. Artifacts use `/tmp/selberg_weighted57_`.

First conjecture: actual source C2 regularity is enough for absolute Fourier reconstruction of the source and both first physical derivatives. The existing C2 Fourier lemma directly applies only to the source; its first derivatives have C1 regularity. Instead one integration by parts and actual Parseval give summable squared frequency-weighted coefficients. Combining this with the corpus reciprocal-square summability through `2ab<=a²+b²` should prove absolute summability with exactly C1 regularity. Circle Fourier uniqueness then reconstructs every original first derivative, without assuming additional source smoothness or a modal ansatz.

Then integrate the complete mixed derivative products against the actual horizontal x weight. Preserve the exact boundary exponential, diagonal modes, and same-residue interference. The new identity `W_nm=(k_m²-k_n²)H_nm` is available only after proving the required rearrangements for the actual source. A positive H does not supply a sign for arbitrary frequency reweighting.

## Proof loop

The reconstruction-first implementation is stopped. Its source summability substep duplicates established work; the necessity of the additional C1 derivative reconstruction has not been demonstrated.

## User-triggered duplication audit

The user identified that this route had reached the same point earlier. The subsequent corpus query retrieved1590 SelbergMaass declarations in81 modules. Source/body inspection confirmed:

- `SelbergMaassBoundaryTrace.lean:63`, namespace `SelbergMaassTrace`, already proves actual source coefficient absolute summability. Its weighted inverse-square bound and boundary-form domain were completed much earlier. Together with the existing zero-or-Maass theorem for source readouts and the coefficient/readout identity, this already supplies the source-readout summability being reproved in the draft.
- `SelbergMaassCharacterGradient.lean:51,243,380` already gives horizontal and vertical readout Parseval and the complete original missing-channel gradient Fourier identity (cycle46).
- `SelbergMaassTraceArea.lean:165` already gives the complete unprojected core–cusp quarter identity. `SelbergMaassCharacterCuspGlue.lean:279` gives its characterwise counterpart with the curved seam retained (cycle49).
- `SelbergMaassFullGradient.lean:147,154` already proves full energy equals eigenvalue times full mass and full mass is positive. The needed all-level inequality `fullMass <= 4*fullGradient` remains unproved.

The generic C1 absolute-convergence helper was not established to be an exact prior theorem by this audit. That is insufficient justification to continue it: no dependency-closed argument was given showing that it improves the missing constant or closes a necessary implication. New Fourier or current identities must not be reported as advances on that estimate merely because they are new declarations.

Cycle54's checked complex Wronskian/tail result is retained as a valid intermediate theorem. Its kernel positivity and Cauchy estimate have not been shown to force positivity of the complete frequency-weighted boundary/core form. That unresolved implication must be tested on paper before more reconstruction infrastructure is added. This audit is a workflow correction, not a mathematical no-go theorem.

Scratch `/tmp/selberg_weighted57.lean` was not promoted or wired. Its last check failed; all task-owned Lean handles are terminal. No final build was run. The draft is retained only as `/tmp/selberg_weighted57_deferred.lean` for provenance, not as verified work.

No spectral estimate, extra regularity, outgoing endpoint, or lift is assumed. The root full Selberg1/4 theorem is not yet proved.
