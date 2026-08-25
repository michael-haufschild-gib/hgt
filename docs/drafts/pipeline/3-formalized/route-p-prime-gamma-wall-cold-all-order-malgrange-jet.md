# Prime/Gamma wall cold all-order Malgrange jet

- **ID:** route-p-prime-gamma-wall-cold-all-order-malgrange-jet
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PROVED HERE]` `[NOVELTY UNVERIFIED]` `[IRREGULAR-RH]` `[SOURCE-HORIZONTAL]`
- **Source:** cold all-order prime/Gamma Fredholm collapse and canonical Xi seam moments
- **Statement:** Every fixed positive logarithmic jet of the cold scaled wall converges to the corresponding jet of `log(1 + c z)`; at Xi first-jet scale, every Malgrange correction jet therefore has an explicit prime--archimedean source limit.

## Goal

Replace order-by-order wall calculations with the complete irregular-RH correction sequence forced by cold prime-2 Stokes condensation.

## Gates

- [x] 0 → 1  in-progress: source-pure statement and corpus/literature audit
- [x] 1 → 2  fully-proven: dependency-closed paper proof
- [x] 2 → 3  formalized: targeted Lean check and new-declaration axiom audit
- [ ] 3 → 4  publication-ready: standalone paper and novelty review

## Exact candidate

For `n > 0`, fixed `c : ℂ`, and scaled finite-wall tau `F_d(z)`, prove

`(log F_d)⁽ⁿ⁾(0) → (-1)^(n-1) (n-1)! c^n`.

With `c = normalizedPrimeArchMoment(0)/2`, prove for the canonical wall--Xi Malgrange correction `M_d = canonicalXiSeamLog - log F_d`

`M_d⁽ⁿ⁺¹⁾(0) → (-1)^n n! (normalizedPrimeArchMoment(n)/2 - c^(n+1))`.

## Approach

1. The `k`-th scaled tau jet is exactly `k! c^k a_k(d)`.
2. Cold condensation gives `a_1(d)=1` eventually and `a_k(d)→0` for every fixed `k≥2`.
3. Faà di Bruno expands the `n`-th logarithmic jet over ordered finite partitions.
4. Every non-atomic partition contains a block of size at least two, so its term vanishes in the cold limit.
5. The unique atomic partition survives, giving the `n`-th jet of `log(1+c z)`.
6. The seam-moment normalization gives the exact Xi jet
   `canonicalXiSeamLog⁽ⁿ⁺¹⁾(0)=(-1)^n n! normalizedPrimeArchMoment(n)/2`.
7. Subtract the cold wall jet.

## Hostile audit

- **Limit scope:** fixed derivative order only; no interchange of cold limit with the infinite Fredholm series.
- **Source purity:** wall limits use prime/Gamma atomic Stokes data; Xi comparison uses canonical completed source moments.
- **Non-tautology:** no correction coefficient or Stokes multiplier is fitted.
- **New content:** all higher Malgrange incidences are forced simultaneously from all-order Fredholm collapse.
- **Open after theorem:** realize the explicit correction sequence by one canonical irregular connection and prove its divisor equivalence.

## Literature audit

- Bertola's Malgrange differential treats arbitrary Stokes-parameter variation: <https://arxiv.org/abs/0902.4716>.
- Cafasso--Gavrylenko--Lisovyy express generic RHP tau functions as Fredholm determinants: <https://arxiv.org/abs/1712.08546>.
- Desiraju gives a six-ray irregular Fredholm tau realization: <https://arxiv.org/abs/2008.01142>.
- Audit found no prime/Gamma cold all-order logarithmic jet law or completed-Xi correction sequence. Absence is audit inference, not priority claim.

## Dependency-closed paper proof

Let `a_k(d)` be complete Fredholm coefficients of the finite prime/Gamma wall. For every `k>0`, scaled tau derivatives satisfy

`F_d⁽ᵏ⁾(0)=k! c^k a_k(d)`.

For positive aperture, `a_1(d)=1`; cold all-order collapse gives `a_k(d)→0` for every fixed `k≥2`. Thus each positive tau jet converges to `c` at order one and zero at every higher fixed order.

Faà di Bruno expands `(log ∘ F_d)⁽ⁿ⁾(0)` over ordered finite partitions of `n`. A non-atomic partition has at least one block of size at least two, so the corresponding product contains a tau jet converging to zero. The unique atomic partition consists of `n` singleton blocks. Its product converges to `c^n`, while

`log⁽ⁿ⁾(1)=(-1)^(n-1)(n-1)!`.

The finite partition sum therefore converges to

`(-1)^(n-1)(n-1)! c^n`.

Finally, canonical seam normalization

`canonicalXiSeamLogMoment(n+1)=normalizedPrimeArchMoment(n)`

and `seamLogCoeff(L,n+1)=L⁽ⁿ⁺¹⁾(0)/(n+1)!` give

`canonicalXiSeamLog⁽ⁿ⁺¹⁾(0)=(-1)^n n! normalizedPrimeArchMoment(n)/2`.

Subtracting the cold wall limit at order `n+1` proves the stated all-order Malgrange correction law. Every sum involved is finite at fixed `n`; no analytic limit passes through the infinite Fredholm series. ∎

## Formal certificate

- **Module:** `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallColdAllOrderMalgrangeJet.lean`
- **Capstone:** `tendsto_iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiMalgrangeCorrectionLog_atTop`
- **Targeted check:** direct module compilation passed.
- **Axiom audit:** three public module declarations and the new general scaled-tau jet theorem use only `propext`, `Classical.choice`, and `Quot.sound`.

## Log

- 2026-08-25 — exact all-order candidate extracted from cold Fredholm collapse via Faà di Bruno.
- 2026-08-25 — corpus and irregular-RH literature audit completed.
- 2026-08-25 — hostile normalization audit corrected general Xi jet factor; orders one through three recover existing certificates.
- 2026-08-25 — dependency-closed Faà di Bruno proof completed; promoted to 2-fully-proven before Lean formalization.
- 2026-08-25 — direct Lean check and four-declaration axiom audit passed; promoted to 3-formalized.
