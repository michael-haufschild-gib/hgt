# Prime/Gamma wall cubic residual negative orientation

- **ID:** route-p-prime-gamma-wall-cubic-residual-negative-orientation
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Labels:** `[PAPER-PROVED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]` `[THETA-LOG-CONCAVITY]` `[REDISCOVERED-GENERAL-LAW]`
- **Source:** strict log-concavity of `thetaCuspFullSource` and cold all-order Malgrange jet law
- **Statement:** The first unresolved wall--Xi Malgrange incidence is strictly negative:
  `normalizedPrimeArchMoment(2) - normalizedPrimeArchMoment(0)^3/4 < 0`.

## Equivalent source inequality

Writing `u_j = thetaCuspNormalizedEvenMoment(j)`, exact cumulant identities reduce the claim to

`u_3 < 15 u_1 u_2`.

Equivalently, for raw half-line moments `M_k = ∫₀∞ x^k thetaCuspFullSource(x) dx`,

`M_6 M_0 < 15 M_2 M_4`.

## Source attack

1. Existing `thetaCuspLogConcavityNumerator_le_firstAtom_sq` makes the full theta density strictly log-concave on the positive half-line.
2. For score `q = -f'/f`, strict log-concavity makes `q` strictly increasing.
3. Integration by parts gives `∫ x^k q f = k M_{k-1}` for `k>0`.
4. Monotone-likelihood order between consecutive size-biased densities `x^(k-1)f` and `x^k f` makes
   `r_k = M_k/(k M_{k-1})` strictly decreasing.
5. Hence `r_6 r_5 < r_2 r_1`, exactly `M_6 M_0 < 15 M_2 M_4`.

## Closed paper proof

Put `f = thetaCuspFullSource`, `M_k = ∫₀∞ x^k f(x) dx`, and
`q = -f'/f`. Existing source positivity makes `q` globally defined. Existing strict negativity of
`f''f-(f')²` gives

`q'(x) = -[f''(x)f(x)-f'(x)²]/f(x)² > 0`,

so `q` is strictly increasing. Schwartz decay supplies all integrability and endpoint limits. For
every `k>0`, integration by parts therefore gives

`∫₀∞ x^k q(x)f(x) dx = -∫₀∞ x^k f'(x) dx = kM_{k-1}`.

Fix `n>0`. Apply the exact two-copy monotone-likelihood identity to carriers
`h(x)=x^n f(x)` and `F(x)=x^(n+1)f(x)`, tested by `q`. Its kernel factors as

`(q(y)-q(x)) x^n y^n (y-x) f(x)f(y)`.

This is nonnegative everywhere in the positive quadrant and strictly positive off the diagonal.
The diagonal has zero restricted product Lebesgue measure, so its integral is strictly positive.
Substituting the integration-by-parts identities into the exact gap identity yields

`n M_{n-1} M_{n+1} < (n+1) M_n²`.

Thus `r_k=M_k/(kM_{k-1})` is strictly decreasing. In particular
`r_6r_5<r_2r_1`; positivity of every `M_k` clears denominators and gives
`M_6M_0<15M_2M_4`. The exact cumulant reduction then gives the stated negative cubic residual.

## Corpus and literature audit

- Corpus contains strict theta-source log-concavity and division-free monotone-likelihood integration, but not the needed score integration-by-parts/strict size-bias chain.
- Factorial-normalized Mellin moments of a log-concave density are classically log-concave (Borell/Berwald theory); the exact completed-theta cubic orientation application was not found.
- Relevant modern moment-comparison discussion: <https://arxiv.org/abs/2211.05210>.
- Absence is audit inference, not priority claim.

## No-fit landing consequence

Strict negativity is necessary before the existing negative Euler--Gamma renormalized cubic current can be tested as a canonical odd Stokes channel. It does not by itself prove equality of the two source masses; that remains a separate arithmetic incidence theorem.

## Formal target

- `normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg`
- No hypotheses, axioms, or numerical computation.

## Lean realization

- Module:
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation.lean`
- Source inequality:
  `thetaCuspRawEvenMoment_three_mul_zero_lt_fifteen_mul_one_mul_two`
- Lower-order strict contraction reused by the quartic Malgrange application:
  `thetaCuspRawEvenMoment_two_mul_zero_lt_six_mul_one_sq`
- Cubic orientation:
  `normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg`
- All analytic bridge lemmas are private: no reusable foundation was added beyond what exact proof
  consumes.
- Direct and targeted module checks passed. Axiom audit of all public theorems added here reports only
  `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-25 — cubic residual reduced exactly to `u_3/120 - u_1 u_2/8`.
- 2026-08-25 — strict log-concavity/size-bias proof route identified; missing corpus bridge isolated.
- 2026-08-25 — hostile audit closed every analytic obligation; strict factorial-normalized moment
  proof completed on paper and card promoted to Stage 2 before formalization.
- 2026-08-25 — exact unconditional theorem formalized and direct module check passed; umbrella import
  wired without umbrella build.
