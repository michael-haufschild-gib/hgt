# Multi-chain Toeplitz–Gram coupling across odd cosets

- **ID:** BSU-MCG
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean, contributions 1–2 verified); 100-contribution programme active
- **Scope:** Independent Bi-Scale Uncertainty; no RH objective.
- **Goal:** 100 significant contributions, each separately proved and audited. Supporting lemmas do not count separately.
- **Source:** User brief and `docs/reports/BiScaleUncertainty/README.md`.

## Plan and current state

1. [x] Read full field motivation; inspect existing single-chain proofs and research search results.
2. [x] Derive exact coupled packet bound and compare against optimized partitioning.
3. [x] Formalize unconditional packet identities and actual autocorrelation bound, without unproved interfaces or numerical experiments.
4. [x] Audit leaf modules, axioms, umbrella wiring, and formal lint; contribution 1 verified. Total: 1 / 100.
5. [x] Complete final source, axiom, and lint audits for contribution 2 (actual synchronized-coset sine leverage). Total: 2 / 100.
6. [ ] Continue conjecture/proof/obstruction cycles until 100 significant contributions are verified.

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

Contribution 2 answers the uniform-gap question for synchronized coefficients on two multiplicatively related odd cosets. Next: identify the correct coefficient-mismatch penalty, determine whether translation orbits can approach the abstract sine constant, or extract stronger compatibility from a network of odd cosets. A nilpotent operator can have norm one, so the numerical-radius gain does not extend freely to unrelated coefficient vectors.

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

`docs/reports/BiScaleUncertainty/MultiChainGramLedger.md` is the authoritative working ledger: established facts, failed mechanisms with witnesses, formal/paper boundaries, toolchain proof pitfalls, and next research decisions. Replace obsolete entries instead of accumulating a diary.

## Contribution 2: synchronized-coset sine leverage with explicit errors

**Statement.** For actual `f : C_c(ℝ,ℝ)`, two length-`L=n+1` dyadic chains based at `base` and `base+b`, and the same real coefficient vector `c`, put

`S=Σ c_k²`, `R=h(0)`, `ρ=cos(π/(L+1))`,

`Γ_ij=h((j-i)log 2)`, `C_ij=h((j-i)log 2-b)`,

`δ=||Γ-RI||`, `ε=||C-strictUpper(C)||` (Euclidean operator norms).

Then, without an additional analytic or grid-zero premise,

`Q=||P_base+P_(base+b)||² ≤ 2(1+ρ)(R+δ+ε)S`,

`4RS-Q ≥ 2[(1-ρ)R-(1+ρ)(δ+ε)]S`,

`E ≥ 2RΣ c_k-B-(1+ρ)(R+δ+ε)S/W`.

**Dependency-closed paper proof.** Let `A,B` be finite synthesis maps of the actual translated functions in complex `L²`. Translation invariance gives `A†A=B†B=Γ` and `B†A=C`. The within-chain defect and the norm identity for `A†A` give `||A||²,||B||²≤R+δ`, hence `||C||≤R+δ`. Split `C=T+F`, with `T=strictUpper(C)`. Strict triangularity gives `T^L=0` directly. If `T=0` its numerical-radius bound is trivial; otherwise normalization by `||T||` produces a contraction, and the existing sharp nilpotent theorem gives `|<Tx,x>|≤ρ||T||||x||²`. Since `||T||≤||C||+ε`,

`|<Cx,x>|≤[ρ||C||+(1+ρ)ε]||x||²`.

Expanding `||Ac+Bc||²` proves the first inequality. Algebra gives the second; contribution 1 gives the origin inequality. This proves the claims from actual data, not from an unproved contractivity, orthogonality, or nilpotence interface.

**Arithmetic identification.** For odd `m,q≥3`, take `base=log m`, `b=log q`. The off-diagonal entries of `Γ-RI` are `h(log(2^|i-j|))`; its diagonal is zero. The forbidden entries of `C` are `h(log(q2^(i-j)))` for `j≤i`. Actual anchor nodes are `log(m2^i)` and `log(qm2^i)`. Integer-log pinning through `N≥qm2^(L-1)` therefore makes `δ=ε=B=0`. The result becomes

`Q≤2R(1+ρ)S`, `D≥2R(1-ρ)S`,

with rational improvement at least `R(1-ρ)S/W` over optimized independent chains. Lean proves `ρ<1`, `0<1-ρ`, and the symbolic two-level value `ρ₂=1/2`. For `{m,2m,3m,6m}` and unit weights this yields `Q≤6R` versus `8R`, and gain at least `R/W`.

**Certified scope.** The unconditional error-aware inequalities, actual `L²` feature construction, matrix-entry identities, and coefficient facts are formalized. The finite-cutoff pinned-grid corollary above is a paper substitution; it is not a separate theorem with additional hypotheses. The symbolic two-level coefficient is certified, but the four-node corollary is not separately packaged. Sharpness within actual translation orbits is open. All supporting lemmas count as one contribution.

**Local frontier.** Reuse `RHTower.norm_inner_nilpotent_contraction_le_sine`, `HTGeometry.StrictlyLowering.pow_eq_zero_of_strictlyUpper`, and finite-synthesis machinery. Their Hilbert mathematics is independent of RH despite storage namespaces. The new content is the unconditional error-aware arithmetic bridge and its leverage consequence, not the existing numerical-radius theorem.

## Contribution 2 verification

- `TriangularGramSineBound.lean`: 11 public theorems; constructed triangular nilpotence, scaled numerical-radius bound, robust matrix errors, actual synthesis composition, synchronized-frame energy, and strict coefficient gain.
- `SynchronizedCosetSineLeverage.lean`: 18 public theorems and one private integrability theorem; actual translation features, Gram energies, arithmetic defect formulas, and origin leverage.
- Targeted `lake build --old +GaloisForLFunctions.BiScaleUncertainty.SynchronizedCosetSineLeverage`: PASS, both owned leaves rebuilt.
- Final direct `lake env lean` on both leaves: PASS, empty output, no warnings.
- Axiom audit: all 29 public theorems use only `propext`, `Classical.choice`, `Quot.sound`; no added axiom or computation certificate.
- Both imports wired; generated API entries present; index refreshed. `scripts/formal_tools.py lint --check-generated`: PASS, existing unrelated large-file warnings only.
- Source SHA-256, `TriangularGramSineBound.lean`: `4ba95b34e5069843278eb980af7f627952846eacc1c2d948c0dbf4a8e2c7c8bc`.
- Source SHA-256, `SynchronizedCosetSineLeverage.lean`: `cc95f4f1bb9cbe18e75834237d3ad1310cd9bb46ff5cd7adf16d51f09974d658`.
- Prototype scratch files removed. Successful axiom-audit scratch and logs retained under `/tmp/bsu-synchronized-*`.
- Verified count: **2 / 100**. This completed contribution constitutes progress; the programme remains active.
- One owned Lean process at a time. No numerical experiments, external literature searches, new premises, or commits.

## Continuation

The 100-contribution objective remains active. Contribution accounting and the exact next research decisions live in the working ledger. Do not count supporting lemmas or mark the programme complete after a small number of results.

## Active contribution 3: stability under unequal coefficient profiles

Previous goal turn: **progress** (contribution 2 audited). Current source hashes match the recorded evidence. The new goal is to remove exact coefficient synchronization with a quantitative, useful mismatch penalty.

**Candidate theorem.** Retain the actual matrices and errors from contribution 2. Put `K=R+δ` and `G=(1-ρ)R-(1+ρ)(δ+ε)`. For arbitrary coefficient vectors `c,d`, set `r=||c||`, `s=||d||`, `u=normalize(c)`, `v=normalize(d)`, and

`gain=r s [max(0, sqrt(2G)-sqrt(K)||u-v||)]²`.

Here `sqrt(t)` means `√max(0,t)`, matching Lean's total real square root. In particular a negative separation margin gives zero certified gain, not an undefined expression.

Normalization sends zero to zero. The unconditional target is

`||Ac+Bd||² ≤ K(r+s)²-gain`.

At exact grid pinning, this improves optimized independent-chain leverage whenever nonzero profiles satisfy `||u-v||<sqrt(2(1-ρ))`, independently of their amplitudes. The origin-bound gain is `gain/(2W)`. Thus a useful neighborhood of synchronized profiles survives; a false unrestricted bilinear sine estimate is not being assumed.

**Paper proof.** Gram defect gives `(R-δ)||x||²≤||Ax||²,||Bx||²≤K||x||²`. The cross numerical-radius bound then gives `||Ax-Bx||²≥2G||x||²`. For unit `u,v`, triangle inequality gives `||Au-Bv||≥max(0,sqrt(2G)-sqrt(K)||u-v||)`. Finally use the exact identity

`||r Au+s Bv||²=(r+s)(r||Au||²+s||Bv||²)-rs||Au-Bv||²`.

Zero coefficient cases have zero gain and follow from the synthesis norm bound. This is a dependency-closed paper proof; all displayed inequalities must be formalized on actual test data before counting.

**Stronger actual-partition comparison.** Let `D=(||Ac||+||Bd||)²-||Ac+Bd||²`, the actual optimized partition loss. For normalized nonzero profiles, `p=||Au||`, `q=||Bv||` satisfy `p²,q²∈[R-δ,R+δ]`; hence `(p-q)²≤|p²-q²|≤2δ`. The exact identity

`D=rs[||Au-Bv||²-(p-q)²]`

therefore gives `D≥gain-2δrs`. This distinguishes improvement over the conservative scalar-frame envelope from improvement over the true measured partition penalty. The latter is certified when `gain>2δrs`. At exact grid pinning the correction vanishes. This strengthened survivor belongs to the same contribution.

The corresponding origin theorem adds `(gain-2δrs)/(2W)` directly to the measured optimized independent-packet lower bound, retaining the actual anchor error `B`.

**Plan:** prove actual synthesis upper/lower bounds and synchronized separation; transfer separation to normalized unequal profiles; derive full Gram/origin bound; targeted build, final direct source and axiom audits, index/lint; update working ledger and count only after verification.

**Local frontier evidence:** deep search returned the existing nilpotent inner bounds and no relevant unequal-profile bridge; search was partial (`filter_and_judge` unfinished), source-only, semantic coverage unmeasured. Exhaustive field-source text search found only the existing synchronized theorem. No literature-wide novelty claim.

**Verification checkpoint:** `formal/GaloisForLFunctions/BiScaleUncertainty/ProfileStableCosetLeverage.lean` contains 17 public theorems. Targeted `lake build --old +GaloisForLFunctions.BiScaleUncertainty.ProfileStableCosetLeverage` passed. Umbrella import added. Source SHA-256: `ccf56ddf05e783bde8dc5daebf92761066cbabf38b7b49f5d690fd15c5ca8121`. Final direct-source audit passed with empty output; all 17 theorem axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`; index refresh passed. Global lint found four other new field leaves missing umbrella imports (`AbstractBiScaleSystemAndSchurKreinCoupling`, `CosecantSecantDualDecomposition`, `DisjointCollarCliqueDivergenceAndTuransProblem`, `FiniteSpectralEnvelopeRealization`). Their sources have been inspected for import wiring; a single targeted `--old` build checks those four leaves before adding the missing imports. No theorem bodies in those modules are being edited or counted. Verified count stays 2 until the final gate passes.
