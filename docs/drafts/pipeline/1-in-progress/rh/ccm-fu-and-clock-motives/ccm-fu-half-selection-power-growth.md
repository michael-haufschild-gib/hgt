# Power growth of the literal half-selection mean

- **Stage:** 1-in-progress
- **Type:** THEOREM (paper); formal transfer pending
- **Objective:** Determine whether the newly permitted subpower losses can repair independent prime averaging as a source estimate for CCM-FU.
- **Boundary:** RH and the arithmetic subpower bound for the complete signed source remain open.

## Exact source and claim

Keep the existing literal half-selection mean `H(M)=Σ μ(d)K_d(M)/2^ω(d)`, averaged retained energy `E(M)`, and original diagonal `D(M)`. Existing Lean proves `H(M)^2 ≤ E(M)` and `D(M) ≤ 722 M^2`.

Claim to formalize: for every real `β < 3/2`, every constant C and every cutoff M₀, some M≥M₀ satisfies `C M^β < |H(M)|`. Consequently, for every `η < 1`, the half-selection energy exceeds every proposed budget `C M^(2+η)` arbitrarily far out. Thus logarithmic or other subpower losses cannot repair a uniform-in-selection-probability independent average budget.

This does not rule out adaptive selection, the fully processed endpoint, or every integral over selection probabilities. An integral comparison needs an additional polynomial evaluation estimate; no such conclusion is asserted here.

## Paper proof

The exact source convolution is `g=(μ/2^ω)*b`, with `b(n)=log n−τ(n)+2γ`, and its square-root Abel prefix `A_N` equals `H(N+1)`.

For `β≥1`, a hypothetical bound `|A_N|≤C(N+1)^β` bounds the twice-Abel summand by a constant times `n^(β−Re(s)−3/2)`. The series is absolutely and locally uniformly convergent on `Re(s)>β−1/2`. The second boundary vanishes there. The prefix increment identity gives `|Σ_(j≤N)g(j)|≤6C(N+1)^(β+1/2)`, so the first boundary vanishes on `Re(s)>β+1/2`. The continued series therefore agrees with the literal L-series on `Re(s)>2` when `β<3/2`.

The already verified Euler identity forces
`F(s)^2 Z(s)=(s−1)B(s)^2 R(s)`, where `Z(1)=1`, `B(1)≥1/30`, and `R(1)≠0`. Both sides are holomorphic on the connected half-plane `Re(s)>β−1/2`, which contains 1. Analytic uniqueness extends the equality from `Re(s)>2`. Evaluation at 1 gives `F(1)=0`; differentiation gives `0=B(1)^2R(1)`, a contradiction. Exponents below 1 reduce to the existing linear-growth obstruction. Finite prefix absorption makes the violation cofinal. Squaring the mean lower bound gives the energy conclusion.

No numerical experiment is needed: the pole location predicts this obstruction. The positive survivor is a cofinal lower growth law for the literal deformed source, with its arithmetic coefficients and square-root clock retained.

## Source search and forcing audit

Broad deep OR searches `forcing renewal` and `noise hypercontractivity` returned source and toy-proof candidates. The Selberg forcing term is exactly another signed Möbius sum by `tatuzawa_iseki`; the bound `384N` in `SelbergSymmetryCore` takes absolute values termwise. Abstract renewal identities do not bound this sum. The cube hypercontractive estimate requires a degree-dependent factor and concerns a fourth incidence moment, not the literal terminal source.

The exact Bernoulli energy kernel was already documented in the failed PE5 card. The previous half-selection proof excluded only linear mean bounds in its formal statement; its simple-zero argument at 1 motivates the sharper power transfer here. No existing theorem has been promoted from an explicit source hypothesis to an unconditional bound.

## Verification

- [x] Dependency-closed paper mechanism identified.
- [ ] General power-growth twice-Abel transfer checked in Lean.
- [ ] Literal mean and energy growth laws checked in Lean.
- [ ] Exact-leaf audits, new-theorem axioms, umbrella wiring, lint and cleanup.
