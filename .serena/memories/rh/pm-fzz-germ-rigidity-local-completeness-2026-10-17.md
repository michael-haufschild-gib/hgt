# FZZ-P round 3 (2026-10-17): germ rigidity, local completeness, unimodular dyadic factor

Module `formal/GaloisForLFunctions/RHTower/FermiNymanWitnessGermRigidity.lean` (wired, axioms standard, lint clean).

Unconditional theorems:
- `IsFermiNymanWitness.eq_zero_of_eqOn_zero`: continuous Fermi witness vanishing on (0,δ] vanishes on (0,1].
- `IsFermiNymanWitness.selfSimilar_of_selfSimilar_near_zero`: self-similarity on (0,δ] propagates to (0,1].
- `IsL2FermiWitness.ae_eq_zero_of_ae_eq_zero_near_zero`: measurable L² witness vanishing a.e. on (0,δ] vanishes a.e.
  (dilation averages are continuous witnesses vanishing on (0,δ]; primitive form gives ∫_s^t w/u² = 0; Lebesgue differentiation
  via `IsUnifLocDoublingMeasure.ae_tendsto_average`).
- `fermiGenSpanOn_topologicalClosure_eq_top` (δ>0): restricted generators dense in L²(δ,1];
  `exists_fermiNymanCombination_approx_on`: every f ∈ L²(δ,1] is a limit of finite generator combinations on (δ,1].
- `norm_dyadicInnerFactor_eq_one`: I(s) = (1−2^{1−s})/(√2(1−2^{−s})) has modulus 1 on Re s = 1/2;
  `integral_dyadicHaar_mul_cpow_factor`, `mellin_fermiNymanGen_factor`: both sides of the Fermi system carry I(s).

Frontier meaning: no bulk obstruction in FZZ-P; the RH content is the approximant energy on (0,δ) as δ→0 (witness growth at 0,
poles of the Mellin continuation at mirror zeros). FZZ-P ⟺ Ξ(s)/s² = (s−1)ζ(s)/s² outer on Re s > 1/2 (Beurling form).

Paper facts (card `pm-physical-model-clock-reduction.md`, round 3): explicit lattice Blaschke product
B_sp(s) = s(1−2^{1−s})/(√2(s−1)(1−2^{−s})); q(w) = −½∫h|w|²; witness equation w(u) = Σ_{n≥2}(−1)^n w(u/n)/n;
w ⟂ W_sp ⟺ Σ_j 2^{−j} w(2^{−j}u) = c/u on (1/2,1].

Kills C15–C28: integer span ≠ real span (integer generators constant on (1/2,1); C13 closed); quantitative germ control
‖w‖_{(δ,1]} ≤ C‖w‖_{(0,δ]} not provable without RH (corona condition fails with dense off-line zeros); Ψ_ρ ∈ M restatement;
spectral synthesis W = K_B needs Beurling–Lax (deferred, no producer value); Herglotz/Jensen closings = Wall 2;
products of generators leave M (L(s,χ₄)); lattice shift broken by the pole; BV convergence needs Mertens size beyond RH.
Do not retry these. Next real step on this lane would be new input at Wall 1 only.
