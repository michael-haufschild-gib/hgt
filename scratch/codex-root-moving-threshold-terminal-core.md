# Moving-threshold terminal core at every cutoff — paper proof, Lean open

Own research note. The frontier map is read-only. This is an unconditional paper theorem *assuming the audited paper proof* of two-sided cumulative-action oscillation in `codex-root-critical-admission-action-oscillation.md`; neither theorem is yet Lean-closed. Literature priority remains unverified. It is an endpoint theorem, not a paid history or RH proof.

## Theorem

Let `C(x)=criticalContinuousAbel x`, and let `P_M(k)` be all active primes `p≤k` at integer cutoff `M`. There exist fixed real numbers `1<Y_-<Y_+` and a fixed `B>0` such that, for every sufficiently large integer `M`, some integer threshold `k_M` satisfies

`M/Y_+ ≤ k_M ≤ M/Y_-`,

`|mobiusDivisorSelectionFibre M P_M(k_M) ∅| ≤ B√M`,

`mobiusDivisorSelectionEnergy M P_M(k_M) ≤ B M²`.

Thus a **contiguous prime-prefix terminal core**, not an arbitrary selected subset, has a quadratic physical energy budget at *every* sufficiently large cutoff. No nestedness of `k_M` across cutoffs is asserted; no old-cutoff, covariance, or completed-endpoint payment follows.

## Sharp fluid clock classification

Write `E_M(Y)=mobiusDivisorSelectionEnergy M P_M(⌊M/Y⌋)` for fixed `Y>1`. The same source and PNT argument proves the exact leading-head law

`(log M/M^(3/2)) mobiusDivisorSelectionFibre M P_M(⌊M/Y⌋) ∅ → A(Y)`.

Consequently, if `A(Y)≠0`, then `E_M(Y)/M²→+∞`; no fixed-ratio prime-prefix history of depth `Y` has a quadratic current-energy budget. Conversely `A(Y)=0` only removes this leading obstruction; it does **not** prove quadratic energy for the fixed threshold, since lower-order head terms can still exceed `M`.

The convergence is uniform for `Y` in any fixed compact interval `[a,b]⊂(1,∞)`. Indeed the scaled-prime measures converge against the uniformly continuous profile `t↦√t C(1/t)` on `[1/b,1]`, and moving one endpoint by `δ` changes the normalized sum by at most a constant times the prime mass of an interval of scaled width `O(δ)`; PNT gives the required equicontinuity. Thus for any thresholds `k_M` with `M/k_M∈[a,b]`, an eventual quadratic energy bound forces `A(M/k_M)→0`. Every bounded-energy prefix clock must approach the **zero-action set**. This is a necessary rigidity law, not a nested-history producer.

## Proof

1. Define `A(Y)=∫_1^Y C(y)y^(-5/2)dy`. The separate Landau proof shows `A` takes both signs beyond every cutoff. Pick fixed `Y_-<Y_+` with `A(Y_-)>0>A(Y_+)`. Continuity of `C` on `[1,Y_+]` gives a finite bound `D=max |C(y)|` there.

2. For fixed `Y>1`, the corpus's arbitrary terminal-core source identity gives the literal threshold head

   `H_M(Y)=C(M)+Σ_{M/Y<p<M, p prime} √p C(M/p)`.

   The strong `ψ` PNT gives `C(M)=o(M^(3/2)/log M)`. The prime number theorem, applied to the continuous profile `t↦√t C(1/t)` on `[1/Y,1]`, gives

   `(log M/M^(3/2)) Σ_{M/Y<p<M} √p C(M/p) → ∫_{1/Y}^1 √t C(1/t)dt = A(Y)`.

   The weighted prime convergence follows directly by step-function approximation from `π(bM)-π(aM) ~ (b-a)M/log M` for fixed `0<a<b≤1`; no derivative of `C`, RH estimate, or numerical observation is used. Consequently `H_M(Y_-) >0>H_M(Y_+)` for every large `M`.

3. Let `k` run through the integer thresholds from approximately `M/Y_+` to `M/Y_-`. Its physical head changes only when one prime `p` becomes processed. The exact terminal source formula says that one change removes `√p C(M/p)`, whose absolute value is at most `D√M`. Since the endpoint heads have opposite signs, a discrete crossing yields a threshold `k_M` in the indicated interval with `|head|≤D√M` (allowing one endpoint-rounding step in the constant).

4. For large `M`, `M/Y_+>√M`, so `P_M(k_M)` contains every active prime with `p²≤M` and is terminal. The corpus's exact terminal energy identity is head square plus the singleton squares `p C(M/p)²` of unprocessed primes. Every missing `p` exceeds `M/Y_+`, so `1≤M/p≤Y_+` and `p C(M/p)²≤D²M`. There are at most `M` such primes. Hence energy is at most `D² M+D² M²≤2D²M²`; enlarge `B` to cover rounding and initial cutoffs.

## Whole-route meaning and hostile audit

This reinterprets cumulative Mellin action `A(Y)` as the **fluid limit of the literal terminal head under a sharp prime threshold**. Its unavoidable two-sign oscillation creates a zero-crossing at every large physical cutoff. That is a stronger endpoint-existence geometry than the corpus's special-grid, two-window selected terminal cores: a single monotone prime prefix suffices at each cutoff.

It does **not** imply RH. The selected thresholds may retreat as `M` grows, so they need not form one exhaustive history. Even a nested current-cutoff energy bound would still need payment of previous cutoffs and the final completed-source square. The corpus's fixed-positive-head-weight terminal-completion no-go applies to monotone *energy-descent completion at a fixed cutoff*, not to this endpoint existence. The next discriminating experiment is whether a **transverse** zero of `A` supports a nondecreasing threshold track `k(M)` with bounded current energy; then test old-cutoff transport separately. Do not promote a static endpoint into a claimed all-history payment.

## Baker rigidity: at most one integer source zero (paper proof)

The corpus already proves the full Baker theorem, including the inhomogeneous statement that a finite algebraic-coefficient linear form in distinct prime logarithms cannot be a nonzero algebraic number (`BakerGeneralConsequences`). This supplies an unexpected arithmetic rigidity for the *literal* source, not an added axiom.

For integer `n≥2` put `w_j=√(j+1)−√j`, `L_n=Σ_{1≤j<n}w_j=√n−1`, `T_n=Σ_{1≤j<n}j w_j`, and `B_n=Σ_{1≤j<n}w_j ψ(j)`. The corpus's exact Abel identity gives `C(n)=B_n−T_n+2γ L_n`. All `w_j,L_n,T_n` are algebraic, `L_n>0`, and each `B_n` is a finite algebraic-coefficient linear form in logarithms of distinct primes. If `C(n)=C(m)=0` for `2≤n<m`, eliminating `γ` yields

`B_m/L_m−B_n/L_n = T_m/L_m−T_n/L_n`.

The right side is a **nonzero algebraic number**: `T_n/L_n` is the weighted mean of `1,…,n−1`, and adding the strictly larger indices `n,…,m−1` strictly raises it. Baker's inhomogeneous theorem excludes the equality. Hence `C(n)=0` for **at most one** integer `n≥2`. This argument makes no claim about the transcendence of `γ` itself.

Between consecutive integers `C(y)` is affine in `√y`, with derivative `F(n)/(2√y)`, `F(n)=ψ(n)−n+2γ`. A sign crossing of `A` with `C=0` cannot occur in an open cell: an isolated zero of such an affine `C` is a local extremum of `A`, while an identically zero cell would force `C` to vanish at two consecutive integers, excluded above. Thus every non-transverse sign crossing is at an integer zero of `C`; there is at most one. The separate paper Landau theorem gives infinitely many positive-to-negative crossings of `A`. Therefore **there exists a regular descending zero** `Y₀>2` with `A(Y₀)=0` and `C(Y₀)<0` (indeed infinitely many). This is paper-proved from corpus Baker and the paper Landau argument; the combined result is not Lean-closed.

## Nested all-cutoff prefix and its exact variance barrier (paper proof)

Fix a regular descending zero `Y₀`. Choose `1<a<Y₀<b` sufficiently close that `A(a)>0>A(b)`, `C(y)≤−c<0`, and

`D(y):=(3/2)A(y)+y^(−3/2)C(y)≤−d<0`

throughout `[a,b]`. The uniform fluid-head law puts opposite signs at the two threshold ends for all large `M`. Within the corresponding threshold interval `M/b≤k≤M/a`, every newly admitted prime has `C(M/p)<0`, so its removal from the omitted-prime head makes the head strictly **increase** with `k`.

At fixed integer `k` in this moving corridor, the one-cutoff drift has the uniform asymptotic

`(log M/√M) [H(M+1,k)−H(M,k)] = D(M/k)+o(1)`.

To see the source of this law, the new prime `p=M+1`, if present, contributes `C(1)=0`. For old omitted `p`, the increment is `(1/√p)∫₀¹ C'(M/p+t/p)dt`. Strong `ψ` PNT gives `C(M+1)−C(M)=o(√M/log M)`. The prime-number theorem against the bounded piecewise-continuous profile `t↦t^(−1/2)C'(1/t)` on `[1/b,1]` gives the displayed limit, uniformly in the lower endpoint `k/M∈[1/b,1/a]`; finitely many quotient breakpoints do not affect the Riemann-sum limit. The integral is `∫₁^(M/k) C'(y)y^(−3/2)dy=D(M/k)` by integration by parts. Thus `H(M+1,k)<H(M,k)` throughout the corridor for all large `M`.

Define `k_M` as the **least threshold in this corridor** with `H(M,k_M)≥0`, using a slightly larger fixed corridor to absorb integer rounding. The head increases in `k` and decreases with `M`; hence `k_{M+1}≥k_M`. One prime jump has size at most `max_[1,b]|C|·√M`, so `0≤H(M,k_M)=O(√M)`. Also `k_M/M→1/Y₀` by the uniform fluid-head law and uniqueness of the zero in the chosen corridor. The cores `P_M={p prime:p≤k_M}` are therefore nested, exhaustive, terminal for all large `M`, and have `E_M(P_M)=O(M²/log M)` at **every** large cutoff.

The estimate is sharp, not merely an upper bound. The exact terminal-energy identity and weighted PNT give

`(log M/M²) E_M(P_M) → V(Y₀):=∫₁^Y₀ C(y)² y^(−3)dy > 0`.

The head square is only `O(M)`; the positive limit comes from the unprocessed singleton second moment `Σ_{p>k_M}p C(M/p)²`. Positivity follows from the strict first-cell source `C(y)>0` on `(1,2]` and `Y₀>2`. Thus the scalar free-boundary controller settles a genuine **nested, all-cutoff current-energy** problem, but is provably unable to produce RH-scale current energy: it leaves a macroscopic variance floor. The route-level missing object is not a better equilibrium for the first moment; it is a source-faithful mechanism that cancels/pays the second moment across old cutoffs and eventual completion.

More generally, every prime-prefix terminal core with `limsup k_M/M≤1−η` for a fixed `η>0` retains a fixed first-cell interval of primes `p/M∈[1−η/2,1]`. The exact singleton formula and weighted PNT then give `E_M(P_M)≥c_η M²/log M` for all large `M`, independently of how its head is selected. Therefore **any** prime-prefix route aiming at RH-scale current energy must have `k_M/M→1`: its quotient depth collapses to the birth layer and its head approaches the completed critical source. Fixed macroscopic-depth head cancellation and RH-scale variance reduction cannot coexist in a prefix controller. Non-prefix selection or a truly signed intertemporal payment is structurally necessary for this route to do more than solve the quadratic intermediate gate.

Hostile checks: large prime gaps do **not** refute the controller. `k_M` may jump over a long prime gap when its next prime is admitted early; macroscopic closeness `k_M/M→1/Y₀` does not constrain this microscopic timing. The monotonicity proof uses the exact head and uniform *time drift*, not a false local prime-spacing approximation. This nested theorem is paper-level; weighted-PNT/drift and Baker-specialization bridges are not yet Lean-closed. It does not prove RH or the original all-history payment.

## Temporal-shear no-go for old cutoffs (paper proof)

The nested controller fails the **actual hard gate** of old-cutoff transfer, not merely because no bound was proved. Fix any `y∈(1,2)` and set `λ=y/Y₀∈(0,1)`. For each large current cutoff `M`, put `m_M=⌊λM⌋`. Since `k_M/M→1/Y₀`, we have `m_M/k_M→y`. At this old cutoff the *same* processed core is a terminal prime prefix with moving depth `y`, so the uniform fluid-head law gives

`(log m_M/m_M^(3/2)) H(m_M,k_M) → A(y)>0`.

Consequently its literal old-cutoff energy obeys

`E_(m_M)(P_M) ≥ H(m_M,k_M)² ∼ A(y)² m_M³/(log m_M)²`,

and in particular `E_(m_M)(P_M)/m_M²→+∞`. This is a **source-specific time-shear obstruction**: an equilibrium for the moving current boundary becomes an off-equilibrium, superquadratic source at a fixed fraction of its prior age. It proves the monotone prefix is not CCM-FU's all-cutoff transferred-energy solution even though its current energy is `∼V(Y₀)M²/log M`.

The positive survivor is exact: two different source moments have different roles. The first moment `A` can be set to zero by a macroscopic free boundary; the singleton second moment remains `V>0`; looking backward in time changes the quotient depth and restores a nonzero **first** moment. Any viable growing-core route must pay *all age ratios* by genuinely source-selected non-prefix admission/covariance, or use a mechanism whose old-cutoff energy is signed against later transfer. A single scalar moving threshold cannot do it. This is a paper no-go with a paper positive survivor; no Lean or RH claim is made.
