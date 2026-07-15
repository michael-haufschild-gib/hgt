# Finite spectral differential boundary

- **ID:** finite-spectral-differential-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Register:** `[BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`
- **Source:** quantum clocks, relational observables, thermal metrology, and complexified finite partition functions
- **Statement:** No function without a nonzero constant-coefficient differential annihilator is a finite exponential spectral response; hypertranscendence and the existence of one meromorphic simple pole are two independent sufficient conditions.

## Goal

Separate clock observability from finite Hamiltonian propagation. The resulting boundary applies
to general hypertranscendental functions but is strictly broader: the total reciprocal function is
differentially algebraic and nevertheless lies beyond every finite constant-coefficient spectral
realization. The theorem therefore supplies a reusable local-pole route that does not require a
hypertranscendence hypothesis.

## Gates

- [x] 0 → 1 in-progress: finite spectral response and annihilator are explicit
- [x] 1 → 2 fully-proven: finite product annihilator, pole-order obstruction, and strict-containment witness
- [x] 2 → 3 formalized: targeted module cache and direct source checks pass; axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4 publication-ready: no standalone novelty claim

## Formalized content

- `ConstantCoefficientDifferentiallyTranscendental`
- `constantCoefficientDifferentiallyTranscendental_iff_linearIndependent_iteratedDeriv`
- `ne_finset_expSum_of_constantCoefficientDifferentiallyTranscendental`
- `hypertranscendental_imp_constantCoefficientDifferentiallyTranscendental`
- `ne_finset_expSum_of_hypertranscendental`
- `constantCoefficientDifferentiallyTranscendental_of_meromorphic_simplePole`
- `differentiallyAlgebraic_inv_id`
- `exists_constantCoefficientDifferentiallyTranscendental_not_hypertranscendental`
- `iteratedDeriv_finiteComplexGibbsPartition`
- `constantCoeffDifferentialOperator_finiteComplexGibbsAnnihilator_eq_zero`
- `ne_finiteComplexGibbsPartition_of_meromorphic_simplePole`
- `ne_finiteComplexGibbsPartition_of_hypertranscendental`
- `normalizedWeight_pairwiseSqGap_eq_two_mul_variance`
- `thermalGapMoment_finiteGibbsProduct_two_eq_two_mul_energyVariance`

## Corpus value

1. Any existing HT theorem immediately excludes finite-dimensional Hamiltonian response without a
   new spectral or dynamical hypothesis.
2. Any existing simple-pole theorem now gives the same exclusion without proving HT.
3. The class is exactly linear independence of all derivative observables, providing a direct
   interface to the existing jet-independence and clock-capacity modules.
4. The Gibbs specialization converts the existing second thermal gap moment into twice the static
   inverse-temperature Fisher information.
5. The finite-spectrum annihilator is an exact boundary: it does not confuse absence of a finite
   temporal generator with absence of an observable clock structure.

## Physics provenance

- Hausmann--Schmidhuber--Castro-Ruiz, *Measurement events relative to temporal quantum reference
  frames*, arXiv:2308.10967: invariant/twirled observables versus dynamical measurement models for
  finite-resource clocks.
- Faist--Woods--Albert--Renes--Eisert--Preskill, *Time-energy uncertainty relation for noisy quantum
  metrology*, arXiv:2207.13707: clock accuracy and quantum Fisher information as an information
  balance involving energy.
- Woods--Silva--Oppenheim, *Autonomous quantum machines and the finite sized Quasi-Ideal clock*,
  arXiv:1607.04591: finite-dimensional clocks approximate ideal continuous clock behavior.
- Correa--Mehboudi--Adesso--Sanpera, *Individual quantum probes for optimal thermometry*,
  arXiv:1411.2437: thermal sensitivity is governed by energy fluctuations.
- Liu--Shan--Yang--Zou--Li, *Exact Fisher zeros and thermofield dynamics across a quantum critical
  point*, arXiv:2406.18981: complexified partition values are read as Fisher-zero/thermofield data.
- Głowacki, *Operational Quantum Frames*, arXiv:2304.07021: operational equivalence is quotienting
  by indistinguishability under invariant relative effects.

## Scope

`ConstantCoefficientDifferentiallyTranscendental` is a broader class, not asserted to be a field
closed under arithmetic operations. The physics sources motivate the interfaces; every shipped
claim above is an algebraic or meromorphic theorem proved in Lean.
