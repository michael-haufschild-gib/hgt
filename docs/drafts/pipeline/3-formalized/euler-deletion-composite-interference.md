# Composite Euler deletion: literal overlap

**Status:** source identity proved in Lean. Standard derived
bridge, not a new RH law or a claim to retire every chronological construction.

**Checked:** whole-corpus research for composite deletion, chronological
interleaving, dilation carry, covariance, and negative overlap;
`EulerDeletionQuasiShuffleConvergence`, `EulerDeletionQuasiShuffleSecondConvergence`,
`EulerDeletionDirichletGram`. No existing composite-overlap declaration found.
Concurrent chronological files are outside this card's write scope.

**RH-chain edge tested:** source interleaving versus independent replication.
The proposed exponent selector requires equality of these genuinely different
operations. This calculation determines their actual arithmetic overlap.

For `E_p(s,n)=(1-p[p|n])n^(-s)` and
`B_pq(s,n)=p[p|n](1-q[q|n/p])n^(-s)`, positive integer `p,q` give

`E_pq = E_p + B_pq`,
`sum E_p conjugate(B_pq)`
`= zeta(alpha) p(1-p)p^(-alpha)(1-q q^(-alpha))`, `alpha=2 Re(s)>1`.

For `p,q>1` this overlap is strictly negative. The exact energy law is

`Q(pq)=Q(p)+p^(2-alpha)Q(q)`
`        -2 zeta(alpha) p(p-1)p^(-alpha)(1-q^(1-alpha))`.

**Proof:** at a multiple `n=pk`, the first source coefficient is `1-p`
and the second is `p a_q(k)`; outside those multiples the second source
vanishes. Reindex by `k`, use the literal first-moment identity already
proved in `EulerDeletionDirichletGram`, and retain the common Mellin factor.
Absolute convergence follows from its doubled-abscissa coefficient bound.
The pointwise composite identity is exact integer divisibility; no zero,
functional equation, or chosen normalization is involved.

**Consequence:** endpoint closure does not make these actual source legs
orthogonal or independent. A refinement-coherence producer must retain and
control this negative overlap, not silently identify the two energy rules.
No numerical experiment is needed.

## Formal statement and scope

`RHTower/EulerDeletionCompositeInterference.lean` proves, in namespace `RHTower`:

- `deletionMellinSource_mul_eq_add_inserted`: literal pointwise composite source,
  all positive moduli, without coprimality.
- `deletionInsertedSource_at_multiple`: exact Euler amplitude and dilation.
- `summable_normSq_deletionInsertedSource`, `tsum_normSq_deletionInsertedSource`:
  genuine inserted-source energy and its cofinal admission.
- `tsum_deletionSource_inserted_pair_re` and `_neg`: exact negative overlap.
- `deletionSourceEnergy_mul`: exact corrected energy conservation.
- `deletionMellinSource_composite_energy_strict`: the energy of the actual
  composite source is strictly less than the sum of its actual two leg energies.

No zero hypothesis occurs. Therefore the overlap also persists at any hypothetical
right-half zeta zero. This is not itself a contradiction: the exact composite
identity already accounts for it. It specifically rules out replacing this
interleaving by orthogonal/independent copies; it does not rule out all QSR,
all-modulus relations, or a law controlling the retained chronological area.

Scratch and published leaf checks passed without warnings; RHTower import wired,
no umbrella build. Nine principal axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`. All own Lean processes completed.
Global lint at audit time reported only five unrelated
concurrent unwired Brizard modules: `AmplitudeCompiler`, `AmplitudeInstances`,
`JacobiSdGlobal`, `RegionIIAmplitude`, `RegionIIJacobi` (each prefixed
`HTGeometry.DispersivePDE.BrizardElastica`). They were not edited here.
