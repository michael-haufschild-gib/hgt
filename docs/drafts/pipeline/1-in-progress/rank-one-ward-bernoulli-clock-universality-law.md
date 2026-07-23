# Rank-one Ward Bernoulli-clock universality law

## Status

Fully proven on paper; Lean 4 formalization exact-checks.

## Theorem-first source

- finiteRankCutoffWardForm_self_eq_hsNormSq: diagonal finite-packet Ward value is cutoff
  commutator Hilbert--Schmidt energy.
- hsNormSq_rankOneProjection_commutator: rank-one unit-projector cutoff energy is
  2 p (1-p), where p = ‖e ψ‖².
- hsNormSq_rankOneProjection_clockInvolution_commutator: clock involution 2e-1 has energy
  8 p (1-p).
- finiteRankProbe: generic packet representation whose Fin 1 specialization had not been joined
  to rank-one energy surface.

Whole-corpus research found no theorem identifying singleton Ward value, rank-one commutator
energy, clock-involution energy, and pure-occupancy zero locus.

## Universal law

For every complex Hilbert space, orthogonal cutoff e, and unit vector ψ, singleton Ward packet is
Bernoulli variance 2 p (1-p). Ordinary rank-one cutoff commutator has exactly that energy,
clock-involution commutator has exactly four times that energy, and all three vanish precisely when
p is 0 or 1.

## Paper proof

Expand one-entry finite sum to identify its source with |ψ⟩⟨ψ|. Diagonal Ward polarization then
equals ordinary cutoff commutator energy. Substitute two independent rank-one energy identities.
Clock coefficient is 8/2 = 4; factorization of 2p(1-p) gives exact zero locus. No numerical
computation is used.

## Lean formalization

Module:
GaloisForLFunctions.RHTower.RankOneWardBernoulliClockUniversalityLaw.

Exact command:
lake env lean GaloisForLFunctions/RHTower/RankOneWardBernoulliClockUniversalityLaw.lean.

## Novelty audit

Pending literature audit after theorem-generation exhaustion. Corpus audit is negative.
