# Full finite divisibility statistics under the actual Dirichlet weight

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); classical finite-statistic mechanism classified
- **Source:** `EulerDeletionDirichletGram.lean`, especially its multiples formula and centered coprime covariance; `research` plus `rg` on finite-cylinder expansions.

## Exact classification

Fix `alpha>1` and a finite set `F` of positive pairwise-coprime moduli. For each integer `n`, record the Boolean vector `b_n(p)=[p divides n]`. For every real function `Phi` of that finite vector, the exact law is

`sum_(n>=1) Phi(b_n) n^(-alpha)`

`= Z(alpha) sum_b Phi(b) prod_(p in F) (if b(p) then p^(-alpha) else 1-p^(-alpha))`,

where `Z(alpha)=sum_(n>=1)n^(-alpha)` is the actual mass, not an adjustable normalization. This determines every finite static deletion-coefficient statistic because `a_p(n)=1-p*b_n(p)`.

## Paper mechanism

The existing exact multiples formula gives total weight `Z(alpha) Q^(-alpha)` to the event `Q divides n`. Coprimality identifies simultaneous divisibility by a subset with divisibility by its product, and real powers multiply. Expanding a product of affine indicator functions therefore factors its weighted sum into the product of its one-coordinate sums. Apply this to each finite Boolean atom, then sum the atoms with coefficients `Phi(b)`. Every exchange is a finite sum of absolutely summable multiples streams.

## What this tests

Higher static grades, nonlinear functions of finitely many divisibility coordinates, and their centered moments have an explicit product-distribution description throughout `alpha>1`. Their evaluation is not a missing arithmetic theorem that could produce zero-location selection. The classification does not cover chronological products at different integers, estimates uniform as the chosen modulus family grows, or exponents outside the convergent chamber.

The strongest positive survivor is the full finite pushforward law, including arbitrary observables rather than just pairwise covariance. It retires a claim of unexplained higher static coupling, not every conceivable weighted chronological construction. Its classical ancestry is documented below.

## Complete proof and positive classification

Put `I_p(n)=[p divides n]`. For arbitrary real `u_p,v_p`, expand

`prod_(p in F)(u_p+v_p I_p(n))`

as the finite sum over `S subset F` of

`(prod_(p in S)v_p)(prod_(p in F\S)u_p) [prod(S) divides n]`.

The product-divisibility equivalence uses pairwise coprimality. Every term times `n^(-alpha)` is summable because it is a constant multiple of a restriction of the summable positive Dirichlet weight. The already-proved multiples formula evaluates its sum as that same constant times `prod(S)^(-alpha) Z(alpha)`. Distributing the reverse finite product gives

`Z(alpha) prod_(p in F)(u_p+v_p p^(-alpha))`.

For a Boolean configuration `b`, choose `u_p=0,v_p=1` if `b(p)=true`, and `u_p=1,v_p=-1` otherwise. The affine product is exactly the indicator of the complete configuration. Its mass is consequently the Bernoulli product displayed above. Finally, the identity `Phi(b_n)=sum_b Phi(b)[b_n=b]` proves the result for every real observable, with summability proved even before imposing coprimality. No approximation or limiting modulus argument occurs.

The actual centered deletion coefficient is

`a_p(n) - (1-p*p^(-alpha)) = p*p^(-alpha) - p I_p(n)`.

Substituting these affine factors makes every factor of the weighted product expectation zero. Therefore every nonempty coprime centered product has zero weighted sum throughout `alpha>1`, at arbitrary degree. This is exact centering at the actual Dirichlet mean, not an assertion that the uncentered coefficient or composite-insertion overlap vanishes.

In the Lean indexing the sum includes `n=0`; its weight is zero for `alpha>1`, so this is exactly the positive-integer source. The empty family is covered by the full law, but excluded from the centered-product vanishing theorem.

## Literature collision and retirement boundary

The mechanism is published. Golomb, [*A class of probability distributions on the integers*](https://www.sciencedirect.com/science/article/pii/0022314X70900181), *Journal of Number Theory* 2 (1970), 189–192, explicitly states independence of coprime divisibility events in its publisher-indexed abstract. Direct full-page retrieval returned 403, so no unseen detail from that paper is used. Cranston–Peltzer, [*On properties of the Riemann zeta distribution*](https://escholarship.org/content/qt4kv3q5r6/supp/r-zeta_072721.pdf), equations (5)–(9), gives the multiples probabilities, coprime independence, and independent prime-valuation distributions in the accessible primary text.

- **Retired claim:** higher finite static divisibility-coefficient correlations constitute a new, unexplained arithmetic coupling or a new probabilistic architecture.
- **Exact positive survivor:** full finite Boolean pushforward law for arbitrary real observables, proved summability, and all-order centered-product vanishing.
- **What remains outside it:** temporal ordering between different integers, unbounded observations of infinitely many moduli, and leaving `alpha>1`. None of those remaining problems is solved or claimed novel here.
- **No blanket RH no-go:** an exact product distribution may enter a useful theorem. The present law establishes its classical ancestry and complete finite evaluation; it does not prohibit all future arguments that use it.

## Lean surface

Bounded full-index discovery queries are preserved in [the search manifest](euler-deletion-finite-statistic-law-searches.tsv). Retrieval caps do not establish exhaustive coverage. Exact `rg` inspection checked the supporting definitions and proof bodies.

Module `formal/GaloisForLFunctions/RHTower/EulerDeletionFiniteStatisticLaw.lean`, namespace `RHTower.DeletionFiniteStatistics`:

- `affine_weight_expansion`, `summable_affine_weight`, `tsum_affine_weight`;
- `atom_eq_affine`, `summable_atom_weight`, `tsum_atom_weight`;
- `finite_observable_partition`, `summable_finite_observable`, `tsum_finite_observable`;
- `tsum_centered_product_zero`.

Scratch compilation, `lake build GaloisForLFunctions.RHTower.EulerDeletionFiniteStatisticLaw`, and the imported audit `/tmp/hgt-deletion-finite-law-wsTzjo/FinalAudit.lean` passed. All five capstones report only `propext`, `Classical.choice`, and `Quot.sound`. The module is wired into `RHTower.lean`; no umbrella or full build ran. Repository-wide `scripts/formal_tools.py lint` passed with existing large-file warnings. All owned Lean/Lake processes terminated. No numerical experiment, computational certificate, or added axiom enters. RH and a qualifying novel architecture remain unproved.
