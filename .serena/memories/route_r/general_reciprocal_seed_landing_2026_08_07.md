# Route R general reciprocal-seed landing (2026-08-07)

[LEAN-PROVED] General Burnol co-Poisson reciprocal-source landing and actual-zero ladder consequence.

Files:
- formal/GaloisForLFunctions/RHTower/BurnolCoPoissonReciprocalSeedLanding.lean
- formal/GaloisForLFunctions/RHTower/GammaCoPoissonSoninActualZeroEscape.lean
- docs/drafts/pipeline/3-formalized/burnol-general-reciprocal-seed-landing.md
- wired into formal/GaloisForLFunctions/RHTower.lean

Main theorems:
- integrable_coPoissonReciprocalSeed
- burnolCoPoissonRightSum_congr_ae
- BurnolCoPoissonSource.measurableSeed and its measurable/support/integrable/a.e. API
- locallyIntegrable_burnolCoPoissonRightSum
- fourierUnitary_burnolCoPoissonSource_eq_reciprocalSum
- BurnolCoPoissonSource.reciprocal
- burnolCoPoissonAnnihilatorPoint_of_riemannZeta_eq_zero
- coPoissonLadderAnnihilator_iff_riemannZeta_eq_zero
- norm_coPoissonLadderKernel_max_le_of_riemannZeta_eq_zero

Mathematical content:
An arbitrary Integrable source seed is replaced by a canonical measurable window-supported representative, and literal co-Poisson sums are proved a.e.-invariant under seed replacement. Reciprocal integrability is proved by the one-dimensional inversion Jacobian. Reciprocal sums are locally integrable because compact t-regions see fixed finite sums. Burnol pairing plus Plancherel/tempered-distribution uniqueness identifies Fourier(Pg)=P(g^vee) a.e. Thus every cosine generator is another direct source. At each right-half-strip zeta zero, the evaluator annihilates both generator branches and hence the full closed source space. The abstract ladder annihilator is exactly the zeta-zero condition (with a<1, r>=1 for the converse), and the existing exact two-sided escape applies at every actual zero.

Conjecture loop:
1. Bidirectional quotient contractions force unit modulus — FALSIFIED because aperture/carrier changes.
2. Literal pointwise reciprocal landing from Integrable source fields — FALSIFIED AS STATED because source data is a.e.
3. A.e.-faithful measurable-model reciprocal landing — PROVED.

Verification:
- lake env lean on both files: green
- lake build both modules: green
- formal_tools.py lint: green
- axioms: [propext, Classical.choice, Quot.sound]
- no Lean processes from this work remain. A concurrent unrelated SkewFrequencyCurrent process was observed and left untouched.

Frontier impact:
Eliminates direct-vector-only and abstract-annihilator-vacuity gaps. Remaining Route R producer burden is now a pre-divisor subexponential/tightness estimate on actual zero-locus ladder kernels; combining it with exact escape would force centered exponent, then squarefull Stokes summability. Do not claim reciprocal landing alone proves RH.