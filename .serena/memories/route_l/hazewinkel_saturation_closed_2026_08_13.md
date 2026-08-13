# Route L — arbitrary-rank Hankel / Hazewinkel saturation closed (2026-08-13)

Exact literature algebraic gap is closed in Lean.

Modules:
- `DeningerHankelChainSecant.lean`
- `DeningerHankelSecantParameterization.lean`
- `DeningerHankelReducedSecantSeparation.lean`
- `DeningerFiniteHankelSecantSeparation.lean`
- `DeningerHankelHigherRankGroebner.lean`
- `DeningerHankelGlobalSecantPrime.lean`
- `HTGeometry/MvPolynomialProjectiveChartPrime.lean`
- `DeningerHazewinkelIntegralSaturation.lean`

Results:
1. finite arbitrary-rank generic Hankel ideal equals ordered-atom parameterization kernel over every CommRing; maximal minors form degree-lex Gröbner basis; prime over domains;
2. finite-support contraction gives global countable generic Hankel ideal = secant kernel and integral primeness;
3. general projective-chart theorem: homogeneous prime avoiding head coordinate remains prime after head=1 over arbitrary nontrivial CommRing;
4. normalized affine image is exactly Hazewinkel `J_n`;
5. for n>0, `J_n` is prime and `(J_n:D_n)=J_n`;
6. positive universal stage tensors/pair quotients are reduced;
7. corrected finite-Hankel-rank canonical big-Witt multiplication holds over every CommRing, nilpotents included.

Headline theorem: `RHTower.deninger_hankelRankLT_mul_corrected`.
Direct module elaboration and exact leaf build pass. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.
Card promoted to `docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/deninger-hazewinkel-integral-saturation.md`.
Route map updated. Honest remaining Route L core: singular completed Green tensor BV boundary to fixed coefficient-faithful Burnol/Deninger physical comparison before divisor specialization. This algebraic closure is not RH.
