# A finite polynomial model with an escaping ramification point

- **ID:** TWO-MARK-END-APPROXIMATION-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean verified)
- **Parent:** `../1-in-progress/xi-capped-surface-uniformization.md`.
- **Source:** installed polynomial covering theorem, complex logarithm error bound, and the current finite cyclic approximation construction.
- **Statement:** Pₙ(z)=(z−1)(1+z/(n+1))ⁿ⁺¹ is a polynomial covering away from {0,−1}, has zeros exactly at 1 and −(n+1), and converges locally uniformly to L(z)=(z−1)exp(z).

## Audit and scope

**BRIDGE.** This explicitly tests how finite ramification can escape while retaining the two marked values. It is not a novel-science certificate, a proof of the finite model's precise monodromy labeling, or a construction of the actual Xi surface's global coordinate. External novelty is unverified under the no-web restriction. The algebraic derivative alone is routine; the geometric obligations are the covering, convergent end model, and ultimately its monodromy identification.

## Complete paper proof [PROVED HERE]

Write m=n+1>0. Pₙ is the evaluation of (X−1)(1+X/m)^m. Its derivative is ((m+1)/m)z(1+z/m)^(m−1), obtained by the product rule and cancellation of the constant terms. Its zeros are exactly 1 and −m. If its derivative vanishes, either z=0, with Pₙ(z)=−1, or 1+z/m=0, with Pₙ(z)=0. (The latter cannot be critical for m=1.) Thus its critical values lie in {0,−1}. The installed `Polynomial.isCoveringMapOn_eval` restricts to give a covering over their complement; no assertion about asymptotic values is substituted for the covering proof.

For locally uniform convergence, fix R>0 and |z|≤R. If m≥2R, put w=z/m; then |w|≤1/2. The checked logarithm error estimate gives |log(1+w)−w|≤|w|², because 1/(2(1−|w|))≤1. Consequently δ=m·log(1+z/m)−z has norm at most R²/m. If also m≥R² then |δ|≤1. The base 1+z/m is nonzero, so (1+z/m)^m=exp(z+δ). The checked estimate |exp(δ)−1|≤2|δ| and |exp(z)|≤exp(R) imply

`|(1+z/m)^m−exp(z)| ≤ 2·exp(R)·R²/m`.

Multiplication by |z−1|≤R+1 yields the common bound

`|Pₙ(z)−L(z)| ≤ 2·(R+1)·exp(R)·R²/m`.

The right side tends to zero independently of z in the closed disk. Every point has a neighborhood in some such disk, so convergence is locally uniform on C. This proof uses symbolic inequalities and the installed logarithm/exponential lemmas, not numerical experiments.

## Remaining identification

The finite cyclic action has one fixed sheet and an m-cycle for the zero mark, and a transposition at the other mark. The polynomial's local ramification pattern suggests that action, but matching these data is not yet a monodromy proof. Need based generators, path transport, and transitivity with exact labeling. General finite-patch polynomial realizations and normalized embeddings of the actual Xi surface remain unresolved.

## Log

- 2026-10-09 — complete covering and uniform-error proof derived from inspected corpus lemmas; formalization next.

- 2026-10-09 — `HTGeometry/TwoMarkPolynomialApproximation.lean` passes its production leaf build. All 13 explicit public declarations pass standard-only axiom audits; the final actual-source `lake env lean` check has an empty log. The common disk error bound and locally uniform convergence are proved. Wired into `HTGeometry.lean`; index refresh passed. Global lint reports seven unrelated unreachable modules and no errors in this work. Logs: `/tmp/hgt-two-mark-polynomial-axioms.log`, `/tmp/hgt-two-mark-polynomial-final.log`.
