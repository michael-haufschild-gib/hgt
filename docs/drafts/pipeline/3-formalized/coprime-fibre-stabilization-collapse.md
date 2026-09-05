# Exact cancellation counts after multiplication-fibre stabilization

- **ID:** CBMF-002
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); retirement certificate for the specified CBMF count
- **Source:** `RHTower/CoprimeFiberStabilization.lean`; C5 in `1-in-progress/rh-corpus-architecture-audit-2026-09-05.md`.
- **Statement:** Every fixed product fibre stabilizes, and its dyadic–triadic cancellation count is an explicit finite combination of shifted divisor counts.

## Exact statement

Set `a_q(n)=1-q[q|n]` for positive integers and put `w(m,n)=a_2(m)a_3(n)`. In the rectangle `1≤m≤M`, `1≤n≤N`, group cells by their literal product `k=mn`. Let `P(k),N(k)` be the positive and negative integer masses entering a fibre, and cancel opposite-sign unit pairs until only one sign remains. The number cancelled is `O(k)=min(P(k),N(k))`.

Every fibre is complete once `M,N≥k`; hence this count is independent of every further rectangular cutoff. Write `d(n)` for the number of positive divisors, with `d(0)=0`, and set `D_r(k)=d(k/r)` if `r|k`, zero otherwise. Then, for every natural `k`,

`O(k)=D_2(k)+D_3(k)-D_4(k)-D_9(k)-D_6(k)+D_12(k)+2D_18(k)-2D_36(k)`.

## Proof

1. If `mn=k>0`, both factors lie between `1` and `k`. Thus the rectangular fibre is the full divisor antidiagonal as soon as both cutoffs reach `k`. The zero-product fibre is empty under the positive-coordinate convention.
2. Let `C(k)=Σ_(mn=k)w(m,n)` and `A(k)=Σ_(mn=k)|w(m,n)|`. Integer positive/negative decomposition gives `C=P-N`, `A=P+N`, and therefore `2O=A-|C|`.
3. Extend each deletion coefficient to have value zero at `0`. These arithmetic functions are multiplicative: a prime cannot divide both coprime factors. Their Dirichlet convolution `C` is consequently multiplicative. Direct summation along a prime power gives `C(2^e)=1-e`, `C(3^e)=1-2e`, and `C(p^e)=e+1` for every other prime `p`.
4. Pointwise absolute value preserves multiplicativity. Let `τ` be the divisor-count arithmetic function and let `δ_r` denote the arithmetic function supported at `r` with value one there. In the ring of arithmetic functions, multiplication means Dirichlet convolution. Comparing the prime-power values proves

   `|C| = τ * (1-2δ_2+2δ_4) * (1-δ_3+2δ_9)`.

   Indeed the local absolute coefficients are `|1-e|`, `|1-2e|`, and `e+1`. Their second differences have exactly the finite supports displayed above. Equality on prime powers gives equality at every natural number.
5. Since `|a_2(n)|=1` and `|a_3(n)|=1+[3|n]` for positive `n`,

   `A = τ * (1+δ_3)`.

   Substitute these identities into `2O=A-|C|`, expand, and use `δ_r*δ_t=δ_(rt)`. The resulting coefficient formula is the stated eight-term identity. No estimated sums or numerical experiments enter this argument.

As a direct paper corollary on `Re(s)>1`, absolute convergence permits Dirichlet-series multiplication, so the series of `O` is

`(x+y-x²-y²-xy+x²y+2xy²-2x²y²) ζ(s)²`,

where `x=2^(-s)` and `y=3^(-s)`. The Lean result is the stronger coefficient-level identity and exact cutoff stabilization; no analytic-continuation claim is part of its statement.

## No-go closure

- **Exact killing mechanism:** the retained count factors through a fixed finite convolution polynomial times ordinary divisor counts. Its existence and nonzero finite values supply no additional zero-location constraint.
- **Strongest positive survivor:** exact classification of every eventual fibre count, including a source-derived stabilization threshold. This extends the earlier six-cell example to every product.
- **Scope:** this retires the specified two-deletion cancellation-count proposal. It does not classify arbitrary labelled histories, an unspecified infinite-modulus construction, or other arithmetic sources.
- **Novelty:** no claim of literature novelty. The proof uses established finite-sum, multiplicativity, and formal-series mechanisms from the current corpus and mathlib.

## Verification

Main closed theorem: `RHTower.CoprimeFiberStabilization.coprimeFiberStabilization_closed`. Exact coefficient theorem: `cancellation_eq_shifted_divisors`; arithmetic-function factorization: `cancellation_eq_divisorCount_factor`.

Scratch `lake env lean` passed. The targeted command `lake build GaloisForLFunctions.RHTower.CoprimeFiberStabilization` passed, compiling only the new leaf with cached dependencies. The leaf is imported by `RHTower.lean`; no umbrella or full build ran. Scratch axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`. The source contains no added axioms, unproved declarations, `decide`, `native_decide`, or externally supplied computational results.

The final imported-module audit also passed for all three listed capstones. `scripts/formal_tools.py lint` passed with existing large-file warnings, and `git diff --check` passed for the changed paths. Every Lean/Lake process started for this certificate exited.
