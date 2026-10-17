# Multi-chain Toeplitz–Gram coupling across odd cosets

- **ID:** BSU-MCG
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, contribution 1); 100-contribution programme remains active
- **Scope:** Independent Bi-Scale Uncertainty; no RH objective.
- **Goal:** 100 significant contributions, each separately proved and audited. Supporting lemmas do not count separately.
- **Source:** User brief and `docs/reports/BiScaleUncertainty/README.md`.

## Plan and current state

1. [x] Read full field motivation; inspect existing single-chain proofs and research search results.
2. [x] Derive exact coupled packet bound and compare against optimized partitioning.
3. [x] Formalize unconditional packet identities and actual autocorrelation bound, without unproved interfaces or numerical experiments.
4. [x] Audit leaf modules, axioms, umbrella wiring, and formal lint; contribution 1 verified. Total: 1 / 100.
5. [ ] Continue conjecture/proof/obstruction cycles until 100 significant contributions are verified.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card carries the plan; independent reads use parallel tool promises.

## Contribution 1: Gram-resolved origin leverage and partition loss

**Setting.** Real Hilbert space, isometric translation orbit `v_t = U_t g`, real autocorrelation `h`, and `R = ||g||²`. Finite nodes `t_i`, real weights `w_i`, positive origin weight `W`, offset `y`. Set

- `P = Σ_i w_i v_(t_i)`;
- `Q = ||P||² = Σ_ij w_i w_j h(t_i-t_j)`;
- `B = <g,P> = Σ_i w_i h(t_i)`;
- `E = W(R-h(y)) + Σ_i w_i(R-h(t_i-y))`.

**Exact remainder identity, with no zero or orthogonality requirement:**

`E = R Σ_i w_i - B - Q/(2W) + ||W(v_y-g)-P||²/(2W)`.

**Proof.** Expand the final norm square. Isometry gives `||v_y-g||² = 2(R-h(y))`; the cross term is `<v_y-g,P> = Σ_i w_i h(t_i-y)-B`. Substitution gives the identity term by term. All finite sums and signs are retained. Thus

`E ≥ R Σ_i w_i - B - Q/(2W)`.

This also gives a robust version for imperfect zero data: the exact anchor error is `B`, not an assumed zero. On actual zero nodes, `B=0`.

**Exact square-root form.** Cauchy–Schwarz against `Wg+P` gives

`E ≥ R(W+Σ_i w_i) - sqrt(R(W²R+2WB+Q))`.

The radicand is `R ||Wg+P||² ≥ 0`, including `R=0`. With `B=0`, rationalizing yields the preceding inequality. This is exact as a Hilbert support bound, not a claim that an actual one-parameter translation orbit attains it.

**Odd-coset application.** For `h(log n)=0` on `2≤n≤N`, group nodes into odd dyadic cosets, and put `P_m=Σ_k w_(m,k) v_(log(m2^k))`. Every within-coset Gram matrix is `R I`, so `||P_m||²=R a_m²`, where `a_m²=Σ_k w_(m,k)²`. Cross blocks are Toeplitz:

`G_((m,k),(m',l)) = h(log(m/m')+(k-l)log 2)`.

No claim that all cross entries have one sign is needed. Then

`Q = R Σ_m a_m² + Σ_(m≠m') <P_m,P_m'>`.

**Comparison with optimally partitioned leverage.** Allocating `W_m>0` with `Σ_m W_m=W`, the partitioned rational penalty is `R/2 Σ_m a_m²/W_m`. Cauchy–Schwarz shows its infimum is `R(Σ_m a_m)²/(2W)`; for nonzero blocks the minimizer is `W_m=W a_m/Σ_m a_m`. Zero blocks are omitted (or handled by a limiting allocation).

Define the exact partition loss

`D = (Σ_m ||P_m||)² - ||Σ_m P_m||²`

`  = Σ_(m,m') (||P_m|| ||P_m'|| - <P_m,P_m'>) ≥ 0`.

Each summand is nonnegative by Cauchy–Schwarz. Consequently the coupled rational lower bound improves the optimized partitioned one by exactly `D/(2W)`. If two nonzero packets are not positive multiples, their two ordered cross summands are strictly positive, hence improvement is strict. Conversely `D=0` iff every pair of nonzero packets is positively collinear (including the vacuous all-zero case). This equality classification follows from equality in real Cauchy–Schwarz and nonnegative finite sums.

The optimized partitioned square-root penalty is `R sqrt(W²+(Σ_m a_m)²)` by the triangle inequality in `R²`, with the same allocation. The coupled penalty is `sqrt(R(W²R+Q))`, so coupling also improves the exact sphere bound. Its gain, for `R>0`, is

`R D / (sqrt(R(W²R+R(Σ_m a_m)²)) + sqrt(R(W²R+Q)))`.

This is a complete paper proof. Lean coverage must be listed separately: the full equality classification and exact optimized sphere comparison are not automatically certified by the rational-bound theorem.

## Significance and frontier audit

This is one contribution, not a count of helper lemmas: it replaces loss of all cross-coset information by an exact, nonnegative, measured improvement over the **optimized** partition bound. It identifies packet alignment as the precise obstruction to strict improvement. The proof uses classical Hilbert geometry; no claim of literature-wide novelty is made. Internal search found the existing single-chain sphere and rational leverage laws, but no multi-chain packet theorem. Search coverage was source-only with stale compiled metadata; actual source was inspected.

## Next conjecture

Can arithmetic zeros force a quantitative positive lower bound for `D`, independent of the chosen nonzero autocorrelation? Compact support should forbid exact packet alignment for disjoint translate sets, but qualitative strictness alone need not give a uniform gain. Attack both possibilities; do not assume a spectral gap from mere distinctness of cosets.

## Verification state

- Authoritative module: `formal/GaloisForLFunctions/BiScaleUncertainty/MultiChainToeplitzGramCoupling.lean` (261 lines, 14 theorems).
- Source SHA-256: `5fae9738e06f22f6da8e9f54a3b407c7b0c96dbacc48e4debcf4fae8692fecba`.
- Targeted build: `lake build --old +GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling` — PASS. Dependencies replayed existing warnings; no full or umbrella build requested.
- Final audit: `lake env lean GaloisForLFunctions/BiScaleUncertainty/MultiChainToeplitzGramCoupling.lean` — exit 0, empty output (no warnings).
- Axiom audit: all 14 theorems checked via a scratch import with `lake env lean`; each depends only on `[propext, Classical.choice, Quot.sound]`. No added axioms or computation certificates.
- Umbrella import present. All new declarations present in generated API. Index refreshed; final `scripts/formal_tools.py lint --check-generated` PASS (existing unrelated large-file warnings).
- Global check scope: earlier concurrent unwired-module/index failures were resolved in the authoritative shared tree before the final passing check. No unrelated theorem body was modified.
- Existing unrelated worktree edits preserved. No computations, external searches, or hgtl7 workflow used.

## Exact certified scope

The module proves the full actual-autocorrelation remainder and rational bound, odd-coset Toeplitz entry formula, full-Gram nonnegativity, Hilbert packet partition-loss identity, nonnegativity, exact rational gain, and pairwise positive-alignment equality classification. The square-root comparison in the paper argument is not formalized here. Its independent-block benchmark now exists in `SharedOriginMultiCosetLeverage.lean`; that benchmark is not counted as our contribution.

## Working facts and failures

Maintain `docs/reports/BiScaleUncertainty/MultiChainGramLedger.md` as the authoritative mathematical working ledger. It records the verified/pending distinction, invalid shortcuts, current corpus benchmark, and a dependency-closed paper argument for a uniform synchronized-coset sine gap. Candidate contribution 2 is not yet formalized and is not counted.

## Continuation

This turn makes substantive progress through a new checked leaf module and a stronger next theorem. The full objective remains 100 significant contributions. Do not mark the goal complete after contribution 1.


## Active contribution 2 work

Previous goal turn classified as **progress**: contribution 1 has a checked module, axiom audit, and passing formal lint. Current source and ledger revalidated.

The full synchronized-chain sine gap is the target. Formalize a stronger defect-aware form, valid without zero-grid hypotheses: for two synthesis maps `A,B`, split `B†A` into its strictly upper triangular part and lower-diagonal error `F`. With `ρ=cos(π/(L+1))`, prove

`||Ac+Bc||² ≤ (||A||²+||B||²+2ρ||A||||B||+2(1+ρ)||F||)||c||²`.

Strict triangularity gives nilpotence by construction. The normalization needed by the existing numerical-radius theorem is proved internally. Bind the formula to actual compactly supported test-function translates. Exact arithmetic zeros make `F=0` and within-chain Gram matrices scalar, recovering the uniform sine gain. Keep all approximation errors explicit rather than introducing unresolved frame/contractivity/nilpotence interfaces.

Plan: certify the triangular decomposition and unconditional numerical-radius bound; derive synthesis-pair energy; construct actual autocorrelation features and arithmetic entries; audit final modules and update verified count only after the intended bound is established.


Contribution 2 implementation checkpoint:
- `formal/GaloisForLFunctions/BiScaleUncertainty/TriangularGramSineBound.lean` exists; targeted `lake build --old +...TriangularGramSineBound` PASS. It proves constructed triangular nilpotence, the norm-scaled sine bound, robust matrix error control, exact analysis-synthesis identification, and synchronized-frame energy.
- Actual translation feature/Gram/dyadic bridge is being checked in `/tmp/bsu_dyadic.lean`; arithmetic entry identities prepared in `/tmp/bsu_arithmetic_extra.txt`. Do not count this contribution until the actual bound and arithmetic identification pass.
- One owned compile at a time. No numerical experiments or premise interfaces introduced.
