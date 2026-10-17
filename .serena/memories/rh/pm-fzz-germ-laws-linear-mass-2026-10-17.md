# FZZ-P PM-21 (2026-10-17): germ laws — linear mass at the origin, top-octave log-mean

Module `formal/GaloisForLFunctions/RHTower/FermiNymanWitnessGermLaws.lean` (wired, axioms standard, lint clean).
Mass function `witnessMass w x = ∫_0^x |w|²`.

Unconditional:
- `IsL2FermiWitness.ae_selfSimilar_iff_linearMass`: an L² Fermi witness is a.e. dyadically self-similar ⟺ ∃C, m_w(x) ≤ C x on (0,1].
  Mechanism: linear mass ⟹ every dilation average bounded by η⁻¹(1+η)²√C ⟹ self-similar (bounded continuous witness) ⟹
  ∫_s^t (w(u/2)−w(u))u⁻² = 0 ⟹ Lebesgue differentiation. Converse: m(x/2) = m(x)/2.
- `IsL2FermiWitness.ae_selfSimilar_of_forall_dilationAverage_selfSimilar` (reusable: all dilation averages self-similar ⟹ w a.e. self-similar).
- `measurable_powerWitness`, `dyadicLogMean_powerWitness` = (1−2^{1−z})/(z−1).

Criteria:
- `riemannHypothesis_iff_forall_l2FermiWitness_linearMass`: RH ⟺ every L² witness has at most linear mass at 0.
- `riemannHypothesis_iff_forall_l2FermiWitness_dyadicMass_bounded`: RH ⟺ 2^k m_w(2^{−k}) bounded (dyadic dilation power-bounded on W).
- `riemannHypothesis_iff_fermiNymanWitness_dyadicLogMean_eq_zero`: RH ⟺ ∫_{1/2}^1 w(t)dt/t = 0 for every continuous witness (linear functional).

Meaning: "control L² approximation at 0 ⟺ all witnesses self-similar" is exactly "no witness has superlinear mass at 0".
Structural kill: any inequality derived from the witness equation alone is satisfied by zero witnesses t^{ρ̄−1}; no estimate
internal to W can force linear mass. Only the zero set of η enters. Do not look for an internal energy argument on this lane.
Related: `rh/pm-fzz-germ-rigidity-local-completeness-2026-10-17`.
