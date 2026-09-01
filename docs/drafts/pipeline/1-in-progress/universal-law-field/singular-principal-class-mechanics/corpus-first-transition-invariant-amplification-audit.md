# Corpus-first transition/invariant/amplification audit

- **Status:** `NO CONJECTURE ADMITTED`
- **Scope:** test three purported higher mechanisms against current Lean corpus and primary
  literature before proposing any new law.
- **Result:** all three explain shadows or transport classes; none generates missing source-side
  arithmetic effectivity.

## Big-picture acceptance criterion

Candidate higher law must act before divisor specialization and prove a zero, sign, upper bound, or
effectivity statement for the actual coefficient-faithful source class. Only then may existing
recovery theorems transport it to the certified RH endpoint. A language that begins with an
already-present obstruction class, comparison map, extension, or spectral parameter is downstream.

## Corpus searches

Executed with `scripts/formal_tools.py research`:

1. `relative admission spectrum killed pointed locus injective naturality Hedenmalm Euler`
2. `zero Fredholm index split nonsplit extension carry holonomy semigroup boundary`
3. `Gamma six weak trace class not trace class strict lift trace ideal`
4. `tensor amplification Adams operation compact recurrence integrality RH receiver producer`

## A. Ordinary gauge atlas / singular transition calculus

Exact facts:

- Hedenmalm Borel relative admission spectrum differs from Euler/Hardy spectrum
  (`hedenmalmBorelRelativeAdmissionSpectrum_ne_eulerPrimitive`). The first contains the centered
  open half-strip; the second is `{0}`.
- No linear transport preserving the common admitted `L2` sector intertwines the two families on
  that strip (`no_l2AdmissionSectorTransport_hedenmalm_to_euler`).
- Under sector-preserving transport, target admission is exactly source admission union the locus
  of nonzero obstruction classes killed by the quotient map
  (`relativeAdmissionSpectrum_target_eq_source_union_killed`). Injective transport preserves the
  spectrum (`relativeAdmissionSpectrum_natural_eq_of_injective`).
- Finite serial chains have a unique first killing edge; heterogeneous parallel records kill
  exactly their common radical (`PointedTransportFirstLossLaw`).

Verdict: `[FALSIFIED AS SELECTOR]`. Routes are heterogeneous presentations joined, when possible,
by lossy singular transitions—not equivalent gauges of one object. Admission and first-loss laws
classify where information disappears. They cannot prove the source obstruction was zero.

## B. Stable K-theory / cyclic / trace-ideal selector

Exact facts:

- Balanced reflection has zero signed Fredholm index independently of positive escape
  (`thetaKakutaniBalancedFredholmIndex_eq_zero`).
- Identical endpoint types and middle size admit split zero-carry and nonsplit nonzero-carry
  histories (`constitutiveSameDefect_split_nonsplit_carry_holonomy`).
- Every trace-class-preserving Gamma-six/Sonin comparison leaves the physical Calkin class
  unchanged (`deningerGammaSixTraceIdealSoninStrictDefect_essentialNorm_eq`). Existence of an exact
  strict lift is equivalent to neutral horizontal grade
  (`deningerGammaSixTraceIdealSoninStrictLiftExists_iff`).
- Current cyclic and relative-boundary constructions retain prime atoms and transport residues,
  but require the extension/comparison whose source-native construction is missing.

Primary literature agrees with this role: excision and bivariant cyclic theory compare supplied
algebras, ideals, and morphisms; cyclic cocycles pair with supplied symbol/K-classes; trace-ideal
theory classifies supplied operators. See Cortinas,
<https://arxiv.org/abs/math/0111096>; Cuntz, <https://arxiv.org/abs/math/0104006>;
Gorokhovsky--van Erp, <https://arxiv.org/abs/2010.02884>; Loreaux--Weiss,
<https://arxiv.org/abs/1712.06702>.

Verdict: `[FALSIFIED AS PRODUCER]`. Stable invariants erase ordered carry and balanced signed
escape; ideal theory preserves the very obstruction to be removed. These theories can encode or
transport a source law after it exists, not manufacture it.

## C. Tensor/Adams amplification, integrality, compact recurrence

Exact facts:

- Adams intervention and tensor polarization already have exact receiver covariance, collision
  memory, and recurrence laws (`WittFormationMechanics`, `TensorPolarizationAmplification`).
- Poisson--Hilbert phase amplification already closes detector, sign, spectral-tail, and
  amplification burdens; its remaining weld is arithmetic explicit-formula transport
  (`XiPoissonHilbertPhaseAmplification`).
- Global prime-circle compact recurrence descent is exactly RH; its missing producer is source-side
  continuity at the completion boundary
  (`forall_thetaXiPrimeModularCompactRecurrenceDescent_iff_riemannHypothesis`).
- Existing integral/multiplicative parity no-gos prevent integrality alone from supplying RH-grade
  neutrality.

Verdict: `[FALSIFIED AS PRODUCER]`. Amplification makes nonneutral response large or reconstructible;
recurrence repackages its absence. Neither supplies the independent arithmetic upper bound or
continuity theorem needed for contradiction.

## Strongest positive survivor

The higher field cannot be an atlas of equivalent routes. Its valid coordinate-free core is a
typed calculus of:

`source formation -> heterogeneous transition -> first loss -> observer admission`.

This calculus explains route inequivalence and all transport no-gos, but selection must enter one
stage earlier. Missing mechanism must be an executable, infinite-support, source-fixed,
coefficient-faithful arithmetic operation that proves effectivity before transition. Stable,
cyclic, ideal, amplification, and recurrence machinery may then carry that theorem to the known
three-channel positivity or compact-descent RH endpoint.

No such operation was identified by these searches. Therefore no conjecture is opened.
