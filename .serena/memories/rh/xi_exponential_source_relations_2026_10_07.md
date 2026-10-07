# Actual exponentially marked Xi relations

Active RH goal remains OPEN. No significant novelty certified; bridge uses classical differential/toric algebra. Do not reopen arXiv2610.05474 (user explicitly says already read). Respect exclusions: positivity, energy/frequency/Fourier/spectral proof mechanisms, estimates/bounds, numerical experiments. Exact symbolic Lean proof checking is being used.

## Verified leaf
`formal/GaloisForLFunctions/RHTower/XiExponentialSourceRelations.lean`, namespace `RHTower.XiExponentialSourceRelations`, wired into RHTower umbrella immediately after XiUpperEndHypertranscendence (line14853 at check).

Actual carrier `source a i = RHTower.xiRotatedUpperEndCarrier * expMero (a i)`, representing xi(-I*z)*exp(a(i)*z). `expMero` is the literal entire exponential upper-end germ. First-order derivative equation supplies DA over complex constants. `expField = differentialAdjoin C (range expMero)` includes every complex exponential. Xi remains hypertranscendental over it, from existing unconditional Xi theorem plus restriction and DA base change.

Main theorems:
- `xiPolynomialEvaluation_injective`: faithfully embeds `Polynomial (AddMonoidAlgebra C C)` into actual upper-end meromorphic field, polynomial variable sent to Xi, group-algebra elements to exponentials.
- `source_relation_iff_grouped_coefficients`: for any parameter family a and finite MvPolynomial P, actual evaluation vanishes iff every coefficient sum over monomials with same `(degree,weight)` vanishes. degree=sum multiplicities; weight=sum multiplicity*a(i).
- `primeParameter p = I*log(p)`; `prime_source_algebraicIndependent` unconditionally proves algebraic independence of the whole prime-indexed actual family (no unproved source premises).
- `source_pair_algebraicIndependent a b hab`: every two distinct complex parameters give an algebraically independent pair. Uses exact two linear equations in multiplicities.

Proof mechanisms: Artin shortening over embedded constant subfield for exponential linear independence; group-algebra lift; Xi transcendence over all exp coefficients; monomial induction and exact coefficient collection; existing Core `log_prime_nat_relation_eq` for unique prime factorization. No estimates/numerical experiments.

Direct `lake env lean <leaf>` passed warning-free. `lake build --old +GaloisForLFunctions.RHTower.XiExponentialSourceRelations` passed (9157 dependency jobs; leaf90s). Axiom audit (temporary scratch) of HT, faithful evaluation, grouped criterion, prime AI, pair AI all exactly propext/Classical.choice/Quot.sound. Index passed. Scoped diff check passed. Global lint --check-generated FAILED: 15 unrelated umbrella omissions (CCMParityQuartetModel; WeilConeBoundaryDilationInequality/LogAveraging/Rigidity; WeilZetaSquareAveraging/BoundaryInequality/Moments; XiGlobalKummerSquareClasses; ApertureConeCalculus/Winding; ApertureLogTranslation; ApertureOpenHistoryIdeal; BoundaryCoronaCStarAlgebra; GcdWeightedSeriesInversion; MeromorphicPlaneSquareRoot), plus stale LEAN_API and LEAN_OVERVIEW after concurrent changes. Do not call global tree clean or claim preexisting baseline. No commits/push. Own scratch8files removed; all own processes terminal.

## Authoritative card and frontier
`docs/drafts/pipeline/1-in-progress/xi-prime-source-toric-closure.md` updated and frontier map mixed [L/P] entry under unconditional infrastructure updated. Paper ideal J=(XaXb-X1Xab), image C+t*C[x_p][t], blowup Spec C[t,x_p], exceptional Spec C[x_p] remain NOT fully formalized. Current Lean gives complete grouped exponential-parameter kernel, not yet explicit quadratic generator presentation or integer-product translation. Generic no-Hom and actual Proj/Rees chart remain paper-only.

## Stronger paper consequence exposed this cycle
Distinct positive integer channels (not just primes) have pairwise AI. Even for ONE integer channel n>1, FE pullback d_n(1-s)=n^-1*xi(s)*exp(+s log n) is AI with d_n(s)=xi(s)*exp(-s log n). Therefore generic Legendre family has zero Hom to its FE pullback; likewise entire Humbert5factor Jacobian. This forbids a nonzero algebraic fibrewise group-homomorphism lift of FE for these carriers. It does NOT forbid formal base twisting, topological comparison, or FE action on source algebra. n=1 exception is Xi itself. Classical modular-correspondence parent from earlier Elkies audit. Targeted corpus and arXiv searches found no exact hits, NOT certified novelty.

## Next required work
1. Complete explicit quadratic ideal presentation (positive survivor of killed isogeny route).
2. Formalize affine Rees chart, with infinite-generator/nonproper distinction.
3. Formalize geometric no-Hom, including FE pullback, if available interfaces or build required ones.
4. Hard RH OPEN CORE: source-derived operation forcing FE partner onto same zero component. Generic source algebra applies to any HT entire function, so it does not supply arithmetic zero selection.

Potential generic kernel strategy (paper only, no new file/proof yet): arbitrary add-commutative monoid M, normal map R[X_m] -> (R[M])[T], X_m->T*[m], J quadrics XaXb-X0X(a+b). Quotient normal terms for d>0 are qX0^(d-1)*qXa, and d=0 can be assigned1 for any a in an auxiliary linear retraction (only a=0 occurs from image). `Polynomial.lsum` plus `Finsupp.linearCombination` and AddMonoidAlgebra.coeffLinearEquiv construct retraction; normalization modulo J shows quotient map factors through normal form, giving ker=J. Need handle monomial induction, not cancel qX0 without proving regularity. Existing mathlib `MvPolynomial.induction_on_monomial` reduces constants and repeated multiplication by X; its signature read from Basic.lean lines321–335. `Polynomial.lsum` read Coeff.lean69: takes family Nat -> A ->_R M and sums coefficient maps. Do not invent signatures; verify in /tmp as required.

See also `mem:rh/legendre_kummer_and_xi_toric_closure_2026_10_07` for prior LegendreSourceKummer verified obstruction and full paper blowup proof.