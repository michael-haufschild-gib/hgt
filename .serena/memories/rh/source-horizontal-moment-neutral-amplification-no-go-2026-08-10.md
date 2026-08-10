# Source-horizontal moment-neutral amplification no-go (2026-08-10)

The proposed Claude zeta-23 handoff was hostile-tested.

## Proved positive survivor
For every off-line Xi multiplicity copy `q`, every prime coefficient `sourceZeroHorizontalPrimeCarrier q p` is nonzero and the coefficients tend to zero along the cofinite prime filter. Therefore, for every packet size `m` and epsilon > 0, there is a Finset of `m` distinct prime labels whose hyperbolic blocks `[[0,a_p],[a_p,0]]` are nonzero and have total Frobenius square <= `2 epsilon^2 m`. Trace is zero. Reflection negates coefficients and preserves energy.

Formalized in `formal/GaloisForLFunctions/RHTower/SourceHorizontalMomentNeutralAmplification.lean`:
- `sourceHorizontalHyperbolicBlock_trace`
- `sourceHorizontalHyperbolicBlock_entrySq_sum`
- `exists_sourceZeroHorizontalMomentNeutralPacket`
- `sourceZeroHorizontalMomentNeutralPacket_reflection_energy`
- `sourceHorizontalHyperbolicFrobSq_sum_ge`
Targeted `lake env lean` and `lake build GaloisForLFunctions.RHTower.SourceHorizontalMomentNeutralAmplification` pass. Axioms only propext/Classical.choice/Quot.sound. Umbrella import wired. Repository lint reaches module but currently fails on unrelated concurrent unimported modules.

## Exact no-go
Claude rank-trace has `-c^2 b` in lower-bound form / `+c^2 b` in certificate form, where b bounds positive index. Every nonzero hyperbolic block adds one positive-index unit. Thus raw index amplification increases the allowed error and cannot contradict the certificate; equality examples show price sharp. If every block has spectral magnitude >= delta, Frobenius square >= `2 delta^2` per block, so sublinear moment growth forces spectral collapse. Bounded coefficient-faithful operations preserve collapse. Fixed-size sign/projection quantization requires unbounded normalization; corpus proves simultaneous forward/reflected normalization domain exactly at neutral grade, hence RH-equivalent.

## Frontier correction
Moment-neutral amplification is not missing; source carrier already realizes it. Missing producer remains a source law preventing spectral collapse / legitimate two-sided unbounded normalization, same Route-R simultaneous-orientation/domain law.

Paper/no-go card: `docs/drafts/pipeline/1-in-progress/source-horizontal-moment-neutral-amplification-no-go.md`. Claude audit, current frontier, and SOTA table corrected.