# Anharmonic cubic descent / future-sheet audit (2026-08-23)

- Literature collision: Rouyea--Bourgeois, *The Cubic Descent of the Riemann Xi Function* (alphaXiv 2608.riemann-xi-hankel-criterion), Lemma 2.7 already proves q(s) purely imaginary iff Re(s)=1/2 or |s|=1 or |1-s|=1, with |Im(s)|>1 pruning circle branches. Treat cubic negative-ray RH criterion as literature, not novelty.
- New formal module: `formal/GaloisForLFunctions/RHTower/AnharmonicChebyshevCubicDescentCriterion.lean`.
  - `xiZeroCopy_chebyshevAnharmonicQ_sq_strictlyNegativeReal_iff_re_eq_half`
  - `allXiZeroChebyshevQSquaresStrictlyNegative_iff_riemannHypothesis`
  - Reverse uses exact q-fibre classification + `xiZeroCopy_one_lt_im_sq`.
- New results in `AnharmonicChebyshevNoetherCasimir.lean`:
  - full current chamber for s>2: 0 < b < -c < a;
  - `chebyshevXiQRealTrace_pos`;
  - exterior-real q-log derivative of cyclic Xi product has positive real part unconditionally;
  - exact factorization E-2T^2 = 6*(b^2+(-c-b)*(a+b));
  - positive Lorentz mass gap and normalized gap / T^2 -> 0.
- Interpretation: quotient + exact fibre classification + independent radial/source gap prunes compact aliases but does not generate fixed-locus/RH. Real-ray positive-real/Herglotz control is automatic; remaining cubic/Chebyshev burden is transverse complex positivity / completed trace bound.
- RH neither proved nor falsified.
- Direct `lake env lean` passes for both changed modules. Headline axiom prints: only propext, Classical.choice, Quot.sound. `git diff --check` passes.
- Global `scripts/formal_tools.py lint` reaches new module but fails on unrelated unreachable modules `SquarefreeCutoffJumpInertia` and `EnsembleKrylovGenericity`.
- Updated formalized card, frontier map, ignored generated endpoint ledger, and RHTower umbrella import.
