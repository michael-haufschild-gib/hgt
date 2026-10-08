# WP06 proof register

## C2f: fixed-cutoff feasibility (paper proof; not Lean-audited)

**Statement.** Fix an integer M≥2 and a compact set K of real frequencies containing no critical zeta ordinate. There are constants B, L₀ and N₀, depending on M and K, such that for every real L≥L₀ and integer N≥N₀ there is a finite positive mixture of real coherent sums

`f_i(u)=Σ_(ceil(N/2)≤j≤N) a_ij Φ_L(u−log(j/N))`

with at most N rows, `Σ_i,j a_ij²≤B`, `Σ_i logValue(f_i,n)=0` for every integer 2≤n≤M, and `Σ_i |paperFT(f_i,r)|²≥1` for r∈K. Here Φ_L is the actual smooth truncated Riemann kernel. All mixture weights are absorbed into the real coefficients. There are no positivity or interpolation hypotheses in this statement. M is fixed before B,L₀,N₀ are chosen.

**Verdict: BRIDGE / classical analytic-density ancestry.** This removes a fixed finite-dimensional feasibility obstruction. It does not prove the prescribed joint rate in C2, control the uncancelled arithmetic tail, or imply a vanishing deficit. No new-science claim is made. This paragraph is a paper theorem awaiting formalization, not an audited corpus result.

The complex restricted-interval density component is now audited in `WeilWorkDeficitRestrictedXiDensity.lean` (two public theorems). This does not constitute formalization of the real-coefficient cone and grid construction below.

### 1. Restricted real translates are dense in real L²

Let Φ be the untruncated real Riemann kernel and H(r)=paperFT(Φ,r). The corpus identifies H with the actual entire xi transform, proves it is not identically zero, and identifies its real zeros with the critical zeta ordinates. Therefore H is nonzero almost everywhere: an entire nonzero function has isolated zeros, and its real zero set is countable. Φ is real and even, hence H is real and even on the real line.

For any 0<θ<π/4, `paperFT_tiltedPhi` and integrability of the tilted kernel imply `|H(r)|≤C_θ exp(−θ|r|)`. For r≥0, take absolute values in `paperFT(Φ_θ,r)=exp(θr)H(r)` and bound the transform by the L¹ norm; evenness gives r<0. The integrable majorant in `exists_norm_tiltedPhi_le` pays that L¹ norm. No assertion at the boundary θ=π/4 is needed.

Fix a nonempty open interval I strictly inside (−log 2,0). Suppose a real g∈L² is orthogonal to Φ(·−x) for every x∈I. By Plancherel, its correlation F(x) is the inverse Fourier transform of `conj(ĝ)H`, up to the fixed positive Fourier normalization. Choose 0<a<θ. Cauchy–Schwarz and the displayed exponential bound give

`∫ |ĝ(r)H(r)| exp(a|r|) dr < ∞`.

Consequently the defining integral extends F holomorphically to |Im z|<a. Differentiation under the integral is justified on each narrower strip: every factor |r|^k is bounded by a constant times the remaining exponential margin. Real-valuedness of g and Φ makes F(x) the real Hilbert-space correlation, so orthogonality gives F=0 on I. The identity theorem gives F=0 throughout the connected strip. Fourier injectivity on L¹ then gives `conj(ĝ)H=0` almost everywhere, hence ĝ=0 and g=0. The real orthogonal-complement criterion proves density of finite real linear combinations of these restricted translates in real L².

This argument uses L², not L¹ density. The real zeros of H forbid using the nowhere-zero version of Wiener's L¹ theorem.

### 2. No nonzero dual functional supports the finite defect cone

Put d=M−1 and, for real f∈L², define the continuous quadratic map

`b(f)_n=(2/√n)∫ f(u)f(u−log n) du`, 2≤n≤M.

Continuity follows from Cauchy–Schwarz and translation isometry: each correlation difference is bounded by `(‖f‖₂+‖g‖₂)‖f−g‖₂`. For a nonzero vector α∈ℝ^d, Plancherel identifies α·b(f) with a fixed positive normalization times `∫ q(r)|f̂(r)|² dr`, where

`q(r)=Σ_(n=2)^M (2α_n/√n) cos(r log n)`.

Distinct positive frequencies log n imply that the symmetric interval averages of q tend to zero and those of q² tend to `Σ_(n=2)^M 2α_n²/n>0`. These identities follow by integrating each cosine and using the product-to-sum identity; all nonconstant frequencies have bounded primitives. If q were everywhere nonnegative, `q²≤‖q‖∞ q` would contradict those two limits. Thus q is strictly negative on some nonempty open set. Since q is even, choose a nonzero real even square-integrable frequency function supported in a bounded symmetric subset of that set. Its inverse transform is real and has strictly negative α·b. The density from step 1 and continuity of b supply a finite real combination f of translates with shifts in I and α·b(f)<0.

For each unit α choose such an f. Strict negativity persists on an open neighborhood of α. Compactness of the unit sphere gives a finite family f₁,…,f_s such that every unit α has `min_l α·b(f_l)<0`. The minimum is continuous in α; compactness makes its negative uniformly at least some δ>0. Finite-dimensional separating hyperplanes now imply

`closedBall(0,δ) ⊆ convexHull{b(f₁),…,b(f_s)}`.

Indeed, a point of that ball outside the compact convex hull could be strictly separated; changing the separating direction's sign contradicts `min_l α·b(f_l)≤−δ`. In particular the positive cone generated by these finitely many actual defects is all ℝ^d. This avoids incorrectly assuming that an arbitrary finitely generated collection was known in advance, or that a nonclosed cone is closed.

### 3. Positive repair preserves a spectral baseline

For K nonempty, let m=min_(r∈K)|H(r)|>0; compactness and exclusion of the actual zeros justify m. Choose x₀∈I and f₀=(2/m)Φ(·−x₀). Then |paperFT(f₀,r)|≥2 on K. For K empty take any fixed translate as f₀; the spectral requirement is vacuous. The ball inclusion in step 2 expresses −b(f₀) as a positive linear combination of b(f_l). Add those positively weighted f_l to the mixture containing f₀. Defects cancel exactly, and the nonnegative spectral summands cannot reduce the baseline. Absorb weights by multiplying coefficients by their square roots. All lists and coefficients are finite.

### 4. Stability supplies the actual truncated logarithmic grid

Keep the finite family f₀,…,f_s, its coefficients and shifts fixed. For every sufficiently large N, replace each shift x by log(j/N), where j/N approaches exp x and ceil(N/2)≤j≤N. Such choices exist by rounding, since the finitely many exp x lie strictly inside (1/2,1). Replace Φ by Φ_L. Dominated convergence gives Φ_L→Φ in both L¹ and L²: 0≤Φ_L≤Φ, pointwise convergence holds, and Φ and Φ² are integrable by the corpus's exponential bounds. Translation continuity in L² and the triangle inequality give convergence of each modified test to f_l in L², jointly as N,L→∞. Their defect vectors therefore converge in ℝ^d. This is uniform over the finite family.

The baseline transforms converge uniformly on K. The truncation error is bounded by the fixed coefficient absolute sum times ‖Φ_L−Φ‖₁; the shift error is bounded by |H(r)| times the finite sum of coefficient-weighted phase errors, uniformly for r in compact K. Thus its modulus is eventually at least 1 on K. The modified defect vertices still contain a ball of radius δ/2: perturb each vertex by less than δ/2 and repeat the separating-direction argument. Their baseline defect vectors stay in a fixed bounded ball.

For each such N,L, express the negative modified baseline vector as `t Σ_l θ_l b(f_l^(N,L))`, where θ_l≥0, Σ_l θ_l=1, and t is bounded independently of N,L. One may take t=max(1,2‖b(f₀^(N,L))‖/δ). Add these weighted modified tests. Cancellation is exact. The sum of coefficient squares is uniformly bounded: after colliding rounded shifts are combined, each row's square sum is at most its fixed coefficient absolute sum squared; multiply by the bounded nonnegative weights and add the baseline. Enlarge N₀ so s+1≤N. This proves the stated theorem.

**Quantifier barrier.** The argument gives no bound on B(M,K), L₀(M,K) or N₀(M,K). C2 needs M of order log N while L is of order log log N and B≤N^A with a fixed A<C−1. Taking a diagonal sequence through the fixed-M existence statements does not establish those simultaneous inequalities. A uniform Euclidean interior-ball estimate is also potentially wasteful: high-n target defects of the baseline are extremely small, whereas a unit coordinate vector asks for a large high-n correlation. The next attack must retain this anisotropy and the actual total repair cost.

## C3: affordable finite repair inside the exact radical (OPEN)

The fixed-M proof suggests decoupling the arithmetic horizon from the physical truncation. Let Φ be the actual untruncated real Riemann kernel. For each integer M≥2, require a finite family

`f_0=Φ`, `f_i(u)=Σ_j a_ij Φ(u−x_ij)`, with real a_ij and `−log 2≤x_ij≤0`,

such that `Σ_i (2/√n)∫ f_i(u)f_i(u−log n)du=0` for all integers 2≤n≤M. Define its cost as `A_M=1+Σ_(i≥1)(Σ_j |a_ij|)²`. Positive mixture weights are absorbed into a_ij. **Conjecture C3:** there are constants C>0 and 0≤θ<π/2 such that every sufficiently large M admits such a family with `A_M≤C exp(θM)`.

This is a specific rate assertion for the actual kernel, not an assumption on a hypothetical producer. C2f proves finite feasibility for each M, but no growth bound. The fixed baseline Φ makes the spectral density at least |paperFT Φ|² at every real frequency; a single scalar normalization then covers any prescribed compact set away from the actual critical zeros. No separate spectral interpolation is required.

Why test the threshold π/2: the verified `riemannAutocorr_two_mul_le` bounds κ(log x), x≥2, by `(101/100)² κ(0) exp(−π(x−1)) ((4π²x−6π)/(4π²−6π))²`. For shifts whose differences lie in [−log 2,log 2], n≥4 gives exp(log n+d)∈[n/2,2n]. Consequently each shifted correlation is bounded by a fixed constant times `n² exp(−πn/2)`. Absolute expansion bounds the mixture's n-th defect by a constant times `A_M n^(3/2) exp(−πn/2)`. This is a rigorous direct consequence of the displayed corpus inequality; it does not use an unproved sharper Bessel asymptotic.

The following argument pays the polynomial repair cost and weighted truncation passage. C3r is now Lean-audited; C3t remains paper-only. Physical truncation is chosen separately for each finite family; no uniform inverse or cone-conditioning estimate is assumed.

### C3r. Actual repair cost is at most C(n+1)√n (paper proof; Lean-audited)

Mathlib's `ContDiffBump.toFun` is `base(rOut/rIn)(rIn⁻¹ u)` at center zero. For the actual `narrowBump n`, the ratio is exactly 2 and δ=1/(8(n+1)). Thus there is a single fixed smooth function η, supported in [−2,2], equal to 1 on [−1,1], with values in [0,1], such that `h_n(u)=η(u/δ)`. In particular `J=∫η²>0`, `∫h_n²=δJ`, and `atomWeight n=2δJ/√n`. These are exact scaling identities, not asymptotic shape assumptions.

Write H=paperFT η on the real axis. Compact smoothness gives `U=∫|H(r)|² dr<∞` and `V=∫|r||H(r)|² dr<∞`. For example, two integrations by parts give |H(r)|≤C/r² for |r|≥1, and the L¹ bound covers |r|≤1; the resulting majorants are integrable for both U and V. All boundary terms vanish by smooth compact support.

For either sign σ=±1, the actual pair test is `f=h_n+σ h_n(·−log n)`. Its real transform is `δ H(δr)(1+σ exp(ir log n))`, whose squared modulus is at most `4δ²|H(δr)|²`. The verified `WeilSpectral.abs_gammaBracket_le` gives `|gammaBracket(r)|≤G+|r|` for a fixed nonnegative G (enlarge the displayed source constant if necessary). Change variables s=δr to obtain

`|(1/(2π))∫ |paperFT f(r)|² gammaBracket(r)dr| ≤ (2/π)(GδU+V)`.

Since 0<δ≤1, this is bounded independently of n and σ. For z=±i/2, compact support gives `|paperFT h_n(z)|≤δ e^δ ∫|η|`. Each shifted factor is bounded by `1+√n`, so both |paperFT f(z)| are at most a fixed constant times δ(1+√n). The autocorrelation identity bounds the sum of its two pole transforms by a fixed constant times `δ²(1+√n)²`, uniformly bounded for n≥2. Together with the exact definition of weilArchRe (or `weilArchRe_eq_testPole_add_testGamma`), this bounds both numerator terms in atomCost by one constant independent of n. Divide by `2δJ/√n` to conclude

`atomCost n ≤ C (n+1)√n` for every integer n≥2.

Every ingredient is for the actual repair bumps. No numerical estimate or assumption about unknown coefficients is used. The exponent is sufficient, not claimed sharp.

#### Exact constants used by the formal repair-cost proof

Set `s=n+1`, `h=h_0`, `J=∫h²>0`, and `J₁=∫h≥0`. The exact bump definition gives `h_n(u)=h(su)`, hence `FT h_n(z)=s⁻¹ FT h(s⁻¹z)` for every complex z and `atomWeight n=2J/(s√n)`. Put `G=|digammaVerticalGrowthConst(1/4)+log π+1|+1` and `g(r)=|FT h(r)|²(G+|r|)`. The corpus linear-weight integrability theorem applies to g. For every |σ|≤1, real r, and n≥0,

`|FT(pairTest n σ)(r)|² |gammaBracket(r)| ≤ (4/s) g(r/s)`.

Indeed the Fourier factor has modulus ≤2, and `G+|r| ≤ s(G+|r|/s)` since s≥1. Thus the norm of the gamma integral is at most `Q=4∫g`. For n≥2 and |Im z|≤1, the existing compact-bump estimate gives `|FT h_n(z)|≤e J₁/s`; the translated factor has modulus ≤1+n=s. Therefore `|FT(pairTest n σ)(z)|≤P=e J₁`. The autocorrelation Fourier identity bounds each pole contribution by P², including its conjugate frequency. Consequently the full numerator is ≤`B=2P²+Q/(2π)`. The strictly positive constant `(B+1)/(2J)` proves the stated polynomial bound without dropping a pole or assuming n-dependent regularity estimates.

### C3t. Complete paper reduction from C3 to C

Let a=π/2 and choose θ<a as in C3. The preceding shifted-correlation bound gives, for n≥4, `|b_M(n)|≤C A_M n^(3/2) exp(−a n)`. Since 0≤Λ(n)≤log n and C3r bounds atomCost, the total weighted defect past M is at most

`C A_M Σ_(n>M) n³ exp(−a n)`,

after enlarging C to cover small indices. Absorb n³ into `exp((a−θ)n/2)`; the remaining geometric tail gives `B_M≤C' exp(−(a−θ)M/2)→0`. Below M the defects vanish exactly by C3. Constants do not depend on M.

For each fixed M, replace Φ by Φ_L in every member of its finite family, keeping the coefficients and shifts unchanged. Every arithmetic defect converges to b_M(n) as L→∞. Because 0≤Φ_L≤Φ, absolute expansion of every correlation gives the same upper bound by the corresponding shifted untruncated correlations, uniformly in L. The polynomial repair-cost bound makes these weighted majorants summable. Dominated convergence for the counting measure therefore proves convergence of the ENTIRE weighted absolute defect sum B_(M,L) to B_M. The finitely many small indices have ordinary finite majorants. This argument does not discard the new integer coordinates activated when L increases.

The actual zeta energy of this fixed finite family tends to zero by `norm_W_shiftComb_le` and the existing vanishing tail-energy bound; denote the sum of absolute energies by R_(M,L). For a given nonempty off-zero compact K, the unmodified baseline Φ_L has transforms converging uniformly to H on K by L¹ convergence. For all large L, its squared transform is at least one quarter of the positive minimum of |H|² there. Multiply all mixture weights by the one fixed normalization factor determined by K. This changes every bound by only that factor. If K is empty, its spectral requirement is vacuous and no normalization is needed.

Choose L=L(M) large enough that normalized R_(M,L)≤1/M, normalized B_(M,L)≤normalized B_M+1/M, and the baseline majorizes K. Each family is now a positive compact C² mixture. Apply the actual finite `nullRepair`: its new summands preserve the spectral lower bound, cancel all integer defects exactly, and have energy bounded by the weighted repair budget. The original archimedean energy is bounded above by R plus the Λ-weighted absolute defects, by the exact von Mangoldt Weil decomposition. Hence the repaired energy is at most normalized R_(M,L)+normalized B_(M,L), which tends to zero. These are exactly Conjecture C's requirements.

Thus **C3 implies C by a complete paper reduction**, with C3r formally audited and C3t awaiting formalization. C3 itself is OPEN; this implication is not a proof of the assigned target.

First attack: a Euclidean interior ball for the full defect cone is too demanding to price directly, since its unit high-n coordinates ignore the exponentially small high-n baseline defects. This observation does not refute C3. The next attack must estimate the cost for the particular target `−b(Φ)` or exhibit a dual obstruction to that cost; abstract finite-dimensional separation alone cannot decide it. Main deficit target remains OPEN.

### C3t+ — stronger corpus envelope and complete weighted convergence (packet bounds and limits Lean-audited)

The previous π/2 threshold is unnecessarily restrictive. Existing `ExposingRayTail.autocorr_upper` proves: for every 0<c<π there is C_c>0 with κ(y)≤C_c exp(−2c exp|y|), for every real y. This is prior corpus knowledge, not a new asymptotic theorem. For x_i,x_j∈[−log2,0] and n≥2, the triangle inequality gives exp|±log n+x_j−x_i|≥n/2. Hence each shifted correlation is at most C_c exp(−cn). The same bound holds for every truncated correlation because 0≤κ_L≤κ.

For a finite real packet P=Σ_i a_i Φ(·−x_i), set q(P)=(Σ_i|a_i|)². Expanding both signs of the actual logarithmic defect gives, uniformly in L,

`|b_P(n)|, |b_(P,L)(n)| ≤ 2 C_c q(P) exp(−cn)/√n`.

Here the truncated defect is exactly the existing logValue of shiftComb; the limit uses the same finite quadratic sum with κ. By C3r, atomCost(n)≤D(n+1)√n. Also Λ(n)≤log n≤n≤(n+1)√n for n≥2. Thus the FULL weighted terms satisfy

`(Λ(n)+atomCost(n)) |b_(P,L)(n)| ≤ 2 C_c(D+1) q(P)(n+1)exp(−cn)`,

and the same holds for b_P. The majorant is summable. Pointwise κ_L→κ and finite sums give b_(P,L)(n)→b_P(n). Dominated convergence on all integers n≥2 now proves convergence of the entire weighted absolute-defect sum, including every newly activated coordinate. It also proves the stronger weighted ℓ¹ difference tends to zero, by the twice-majorant inequality |b_(P,L)−b_P|≤|b_(P,L)|+|b_P|. Every statement is for the actual PBAP weight and existing compact shiftComb tests.

For any 0<r<c<π, `(n+1)exp(−(c−r)n)` has a finite uniform bound (one degree-one exponential estimate). Therefore the weighted terms are ≤K_r q(P)exp(−rn), uniformly in P,L. Summing n>M gives at most K'_r q(P)exp(−rM). Positive finite mixtures obey the same bound with total packet cost A. Consequently the original C3→C paper reduction works with **θ<π**, choosing θ<r<c<π, instead of θ<π/2. C3+ denotes this weaker sufficient construction problem. No affordable cancellation construction has been proved.

Formalized in `WeilWorkDeficitRadicalBudget.lean`: actual packet definitions and exact logValue bridge; uniform exponential bounds for full weighted terms and every arithmetic tail; summability; full weighted ℓ¹ convergence under physical truncation. Nine public theorems passed final direct and standard-only axiom audits. The complete mixture/majorant/nullRepair assembly of the C3 implication remains paper-only. These are unconditional analytic bridge results. C3+, C5p and the assigned spectral-deficit target remain OPEN. C4b's lower-cost boundary is unaffected.

## C4b: a quartic lower boundary for finite cancellation (paper proof; not Lean-audited)

**Exact statement.** There are constants c>0 and an integer M₀ such that, for every M≥M₀, every finite family of real-coefficient finite translates `f_i=Σ_j a_ij Φ(·−x_ij)`, with the additional fixed baseline `f_0=Φ`, whose total logarithmic defects vanish for every integer 2≤n≤M, satisfies

`A_M=1+Σ_(i≥1)(Σ_j |a_ij|)² ≥ c M⁴/(log M)³⁴`.

The shifts may be arbitrary real numbers; C3's restricted interval is not needed for this lower bound. This forbids uniformly bounded cost and any fixed polynomial exponent below four, but does NOT refute C3's subcritical exponential upper bound. The exponent 34 is a deliberately coarse logarithmic loss, not asserted optimal.

**Source audit and verdict.** `ThetaCuspChargeXiStripBound.norm_XiC_ofReal_le_strip` supplies an explicit xi bound through `xiStripConst`; `thetaGaussianPowerSum_le` bounds its Gaussian sums by inverse powers of their rate. `RiemannAutocorrFourier.riemannXi_eq_XiC` fixes the Fourier normalization. These sources were read directly. Finite Blaschke division in a strip is classical; Platonov's spectral-synthesis paper, §3, explicitly describes the strip-to-disk Blaschke construction. Verdict: **BRIDGE / classical analytic lower-bound mechanism**, not a claim of new significant scientific knowledge. No existing exact C4b result was located in the partial corpus query `/tmp/wp06-c3-cost-boundary.json`; partial retrieval is not proof of absence. The following dependency-closed paper argument is a candidate for formal verification, not an audited Lean result.

**Proof.** Let `H(r)=paperFT Φ(r)=XiC(r)` and write `P_i(r)=Σ_j a_ij exp(i r x_ij)`. Since all coefficients and Φ are real,

`G(r)=|H(r)|²(1+Σ_(i≥1)|P_i(r)|²)`

is even and nonnegative, and `G(r)≤A_M |H(r)|²`. Its inverse Fourier transform

`F(z)=(1/(2π))∫_R G(r) exp(−i r z) dr`

restricts on the real axis to the sum of the actual autocorrelations, by convolution and Fourier inversion. Therefore `F(0)≥κ(0)>0`, and the given constraints imply `F(±log n)=0` for 2≤n≤M. Positivity is used for the fixed lower bound at zero; the coefficient total controls the strip norm.

For 0<ε≤ε₀, where ε₀ is a sufficiently small fixed positive constant, set θ=π/4−ε. Then `cos(2θ)=sin(2ε)≥4ε/π`, by the chord bound for sine on [0,π/2]. The Gaussian rate `γ=π cos(2θ)/2` satisfies `2ε≤γ≤1`. The source theorem gives Gaussian sums of orders four and two bounded by constants times γ⁻⁵ and γ⁻³. In the exact `xiStripConst` formula, the remaining factor is a constant times γ⁻³. Consequently `xiStripConst θ≤C ε⁻⁸`, with C independent of ε. The explicit strip theorem and evenness of XiC give

`|H(r)|≤C ε⁻⁸ exp(−(π/4−ε)|r|)` for all real r.

Put b=π/2−4ε>0. The integral defining F is holomorphic in `|Im z|<π/2`: on every smaller strip the same exponential bound supplies integrable majorants for all derivatives. On `|Im z|≤b`,

`|F(z)|≤C A_M ε⁻¹⁶ ∫ exp(−2ε|r|)dr ≤ C' A_M ε⁻¹⁷`.

The map `w=tanh(π z/(4b))` maps this open strip conformally onto the unit disk and sends zero to zero. The zeros ±log n map to ±a_n, where `a_n=(n^p−1)/(n^p+1)` and `p=π/(2b)>1`. Apply the disk Schwarz lemma after division by each of these finitely many Blaschke factors. Each division preserves the same supremum bound; evaluating the resulting factorization at zero gives

`κ(0)≤C' A_M ε⁻¹⁷ ∏_(n=2)^M ((n^p−1)/(n^p+1))²`.

Choose ε=(log M)⁻² for M sufficiently large that all preceding smallness conditions hold. Then `p−1≤(16/π)ε`. For 0<u<1, `log((1−u)/(1+u))≤−2u` (differentiate both sides, or integrate `−2/(1−u²)≤−2`). Hence the logarithm of the product is at most `−4Σ_(n=2)^M n⁻ᵖ`. Using `exp(−v)≥1−v`,

`Σ n⁻ᵖ ≥ Σ 1/n − (p−1)Σ(log n)/n ≥ log M−C₀`.

Here `Σ_(n=2)^M 1/n≥log M−1` and `Σ(log n)/n≤log M(1+log M)`, so C₀ is independent of M. Thus the product is ≤`exp(4C₀)M⁻⁴`. Substitution and division by positive constants yield `A_M≥c M⁴/(log M)³⁴`. Every constant is independent of the finite family, the number of rows, and its shifts. ∎

**Research implication.** Qualitative finite feasibility cannot have a bounded coefficient realization. The remaining quantitative question is an upper bound, especially whether the particular baseline defect can be cancelled at polynomial or subcritical exponential cost. The quartic lower boundary alone does not provide that construction. No route is marked retired before this boundary's formal audit.

## Next hard conjecture C5p: polynomial cost for the particular baseline defect

Given the exact internal and external frontier, what would a Fields Medal-winning mathematician conjecture? The competing possibility worth testing is that the particular, rapidly decaying baseline defect is substantially cheaper to cancel than an arbitrary unit defect vector.

**Exact conjecture.** There exist C>0, K>0 and an integer M₀ such that for every M≥M₀ one can choose a finite family of real-coefficient finite translates of Φ with all shifts in [−log 2,0], retain the separate baseline Φ, cancel all total logarithmic defects at 2≤n≤M exactly, and have `1+Σ_i(Σ_j|a_ij|)²≤C M^K`. This is stronger than C3. C4b's paper lower boundary forces K≥4; no asserted bound with K<4 survives that attack.

**[OPEN CORE]** Construct the positive covariance for `−b_M(Φ)` with this cost. Qualitative density and finite-dimensional cone separation supply existence but not the rate. The existing near-radical dimension theorems do not price it. The inspected superoscillation papers price different interpolation data and do not prove either this upper bound or its negation. Preliminary verdict: **SURVIVES PRELIMINARY ATTACK**, with no proof and no novelty certificate from search absence.

If true, polynomial cost lies below every positive exponential threshold, so C3 and its paper reduction apply; after formalizing those dependencies, the exact Weil-positive datum would force critical spectral support. If false, target-specific conditioning has a superpolynomial obstruction, which must be quantified before abandoning C3: superpolynomial cost may still lie below exp(πM/2). The next investigation must price this actual target, not replace it by arbitrary moment interpolation or assume a bounded inverse.

### Competing next rate conjectures C6Q / C6E (OPEN; no formal claim)

The actual unresolved quantity is the least coefficient cost among C3's finite real families with separate Φ baseline and exact cancellation through M, with shifts in [−log 2,0]. Fixed-M feasibility is paper-proved in C2f; no growing-M estimate is known here. The newly verified source envelope suggests testing two incompatible statements rather than inferring an upper bound from C4b.

**C6Q (near-quartic realization).** For every ε>0 there are C_ε>0 and M_ε such that every M≥M_ε admits such a family with `A_M≤C_ε M^(4+ε)`. This strengthens C5p and would nearly match C4b's paper lower boundary. `[OPEN CORE]`: a construction preserving the exact Xi² Fourier factor, positivity of the finite square sum, restricted shifts, and this coefficient cost simultaneously. Generic strip Blaschke products do not supply that construction.

**C6E (critical exponential obstruction).** For every ε>0 there is M_ε such that every admissible cancelling family at every M≥M_ε has `A_M≥exp((π−ε)M)`. This would rule out C3+'s subcritical exponential route, while exposing a quantitative rigidity law. `[OPEN CORE]`: a lower estimate using the positive restricted-Xi covariance constraint, beyond the general analytic-strip zero bound. C4b alone does not imply any exponential lower bound. Neither statement follows from a model replacement of κ by a pure Laplace exponential.

These alternatives are not exhaustive: a larger polynomial cost or a positive subcritical exponential rate could falsify both. Both survive only a preliminary attack; neither has a proof or novelty certificate. Parent audit: the corpus already contains Carlson/Jensen logarithmic-zero machinery; the general moment-cone literature controls representation and atom counts; positive-definite extremal theory does not automatically impose the required Xi² divisibility. Next discriminate these alternatives by estimating the actual finite quadratic dual on signed coefficient measures supported in [−log2,0], pricing the particular target −b(Φ), not arbitrary unit moment vectors. No generic duality reformulation is counted as new science.

### C7: an affordable subsequence at some aperture (OPEN; selected broader attack)

Two restrictions in C3 are not required by its proof: the aperture need not equal log 2, and affordable families need not exist at every sufficiently large M. The source κ envelope is valid at all real shifts, and physical truncation is selected separately for each finite family.

**Exact conjecture.** There exist a>0, C>0, and 0≤θ<2π exp(−a) such that, for every integer R, there is an integer M≥max(R,2) and a finite real family `f_0=Φ`, `f_i=Σ_j a_ij Φ(·−x_ij)` with x_ij∈[−a,0], satisfying total b(n)=0 for all 2≤n≤M and `A_M=1+Σ_(i≥1)(Σ_j|a_ij|)²≤C exp(θM)`.

This retains the actual Xi factor, positive sum-of-squares spectrum, baseline, and exact arithmetic constraints. It is a weaker sufficient construction problem than C3+, not a weakening of the assigned spectral-deficit objective. `[OPEN CORE]`: produce such families and one fixed strict exponential margin at one aperture, along arbitrarily large horizons. C6Q and C6E remain diagnostic stronger alternatives at a=log2; neither settles C7 at other apertures.

**Dependency-closed paper implication.** For |d|≤a and n≥2, exp|±logn+d|≥n exp(−a). For every 0<c<π, the existing kernel envelope therefore gives shifted correlations ≤C_c exp(−2c exp(−a)n), uniformly under truncation. The same finite quadratic expansion and actual atom-cost bound used in C3t+ give full weighted terms ≤C A(n+1)exp(−2c exp(−a)n). Choose fixed rates θ<r<2c exp(−a)<2π exp(−a); absorb the linear factor and sum the geometric tail. For each admissible horizon M the full weighted uncancelled tail is ≤C' A_M exp(−rM)≤C'' exp(−(r−θ)M), tending to zero along the chosen unbounded sequence. For each fixed family, all its shifts are finite, so existing zero-energy truncation bounds and the same dominated weighted-budget convergence apply. Choose L separately to pay its truncation error and zero energy; keep the Φ baseline to majorize every fixed compact set off actual critical zeros after fixed normalization. The actual positive nullRepair adds spectrum and cancels every remaining integer defect at cost bounded by that budget. Thus C7 implies Conjecture C and the critical-support rigidity route by the already recorded exact implication. No all-M uniformity, growing-aperture bound, or asserted coefficient construction is hidden in this argument.

**First attack / verdict:** SURVIVES PRELIMINARY ATTACK, no proof or novelty certificate. Fixed-horizon density does not give the strict rate. The coarse pure-Laplace kernel model does not establish a lower bound for the actual κ. A critical-cost obstruction at one aperture would not retire this route; it would need to cover every fixed aperture. Next estimate the actual positive covariance cost as aperture varies, rather than insist on a polynomial bound at the originally chosen width. The absolute-coefficient envelope is only sufficient: cancellation among outer covariance entries can reduce the actual weighted tail. Failure of C7 would therefore not retire Conjecture C or the assigned deficit route.

### C7 attack: anchored spectral averaging (paper bridge; not a C7 construction)

The quantitative problem is specific to the Xi factor. There is an elementary inexpensive cancellation construction if spectral translations are permitted. Record it explicitly to avoid confusing ordinary positive moment feasibility with the required radical-preserving feasibility.

For an integer M≥2 put `t_n=π/log n`, `ν_n=(1/2)δ_0+(1/4)δ_(t_n)+(1/4)δ_(-t_n)`, and let ν be their convolution for n=2,…,M. This is a finite symmetric probability measure. Its characteristic function is `∏_(n=2)^M (1+cos(t_n y))/2`; therefore it vanishes at every ±log n, 2≤n≤M. The all-zero choices give ν({0})≥2^(−(M−1)), and its support lies in `[−R_M,R_M]`, where `R_M=πΣ_(n=2)^M 1/log n`. Splitting this sum at √M bounds it by `π(√M/log2+2M/log M)`, so R_M=O(M/log M)=o(M). All identities are finite expansions, with no probabilistic limit or computation.

Set `H(r)=XiC(r)` on the real axis. Then

`G_M(r)=2^(M−1) ∫ |H(r−s)|² dν(s)`

is nonnegative, even, integrable, dominates |H(r)|² pointwise, and has every logarithmic Fourier moment through M equal to zero. Indeed, defining `F_G(y)=(1/(2π))∫ exp(iyr)G(r)dr`, finite translation and the already used autocorrelation/Fourier identity give `F_(G_M)(y)=2^(M−1)κ(y)·charν(y)`. The all-zero branch has coefficient exactly 1 before possible collisions; the sum of all coefficients is 2^(M−1).

There is also a target-relative dual statement. For arbitrary real α_2,…,α_M let `Q(s)=Σ α_n κ(log n)cos(s log n)`. Its ν-average is zero. If Q(0)>0, removing precisely the all-zero branch, of probability p=2^(−(M−1)), gives an average `−p Q(0)` over the remaining branches. Consequently one branch s with |s|≤R_M satisfies

`Q(s) ≤ −Q(0)/(2^(M−1)−1)`.

Colliding branches at s=0 cause no problem: the selected all-zero branch is removed in the finite product space, rather than subtracting the whole atom at zero. This prices a negative witness relative to the particular baseline functional, instead of relative to a unit coordinate norm.

**Attack verdict: BRIDGE / classical finite convolution mechanism.** This does not solve C7: the spectra in the construction are |H(r−s)|², while a coherent physical-translate packet has spectrum |H(r)|²|P(r)|². At a real zero γ of H, every latter spectrum vanishes; the former sum is a sum of nonnegative shifted values and would vanish only if every positive-weight shifted value did. No such common-zero property is established. Dividing by H, invoking density, or replacing spectral shifts by physical shifts does not pay the coefficient cost or the error in the actual quadratic form. No impossibility of C7 or Conjecture C follows, and no route is retired.

**Next hard obligation.** Test whether these target-relative negative witnesses can be replaced by actual restricted-Xi packets with controlled cost and sufficiently small signed-form error. A uniform approximation theorem must retain the baseline-relative normalization above; an absolute L² approximation with an unspecified constant does not suffice. The finite convolution construction itself is classical and not selected as new scientific knowledge or as a substitute Lean milestone. C7 remains OPEN.

### C8: zero-preserving approximation has a double-logarithmic cost barrier

**Exact positive statement (paper proof and audited Lean).** Let Φ be the actual Riemann kernel, let γ be any real zero of XiC, and let `F(u)=Σ_j c_j Φ(u−x_j)` be any finite complex packet with |x_j|≤a, a≥0. Put `V=Σ_j|c_j|`, `T_γ(u)=exp(−iγu)Φ(u)`, `E=‖F−T_γ‖_(L²(du))`, and `h=|XiC(0)|>0`. There are universal B>0 and K>1, independent of a, γ and the packet, such that

`h ≤ sqrt(2L) E + 2B(V+1)exp(−exp(2(L−a)))` for every L>0, and

`h² ≤ 8(a+log(N+K)) E²` whenever N≥0 and V≤exp N.

The first inequality is the stronger stability statement; the second exposes its cost scale. At fixed aperture, squared error therefore cannot be o(1/log N) under coefficient budget exp N. Equivalently, achieving sufficiently small error ε forces log log(V+constant) to be at least a positive constant times ε^(−2), up to aperture-dependent constants. No sharpness or matching upper construction is claimed. With the paper Fourier convention, Plancherel gives spectral squared error `∫|XiC(r)Σ_j c_j exp(irx_j)−XiC(r−γ)|²dr = 2π E²`; thus the same obstruction applies to strong L² restoration of a shifted Xi profile.

**Dependency-closed paper proof.** The existing public `riemannPhiKernel_decay_below_theta` at c=2 gives `|Φ(u)|≤C exp(−2exp(2|u|))`. Enlarge C to B>0. Since |u|≤exp(2|u|),

`|Φ(u)|≤B exp(−exp(2|u|))exp(−|u|)`.

For |u|>L and |x|≤a, |u−x|≥L−a. Integrating the resulting bound over this set and enlarging the remaining integral to the real line gives

`∫_(|u|>L)|Φ(u−x)|du ≤2B exp(−exp(2(L−a)))`,

because `∫ exp(−|u−x|)du=2`. The modulation has unit modulus and is the x=0 case. Finite summation gives the tail bound for F−T_γ with factor V+1. All functions are L¹ and L²: the global exponential bounds and finite sums pay these integrability requirements.

The paper Fourier transform of F at γ is XiC(γ) times a finite exponential sum, hence zero. The transform of T_γ at γ is XiC(0). Its norm h is strictly positive by the existing central nonvanishing theorem. Split the Fourier integral of F−T_γ into |u|≤L and its complement. The character has modulus1; Cauchy–Schwarz bounds the first part by sqrt(2L)E, and the preceding tail estimate pays the other part. This proves the first inequality without a simplicity assumption or a lower bound for Xi near γ.

Choose a universal K>1 so large that `4B exp(−K)≤h/2`. Set L=a+log(N+K)>0. Then `exp(2(L−a))=(N+K)²≥N+K`, and `exp N+1≤2exp N`. The tail term is at most `4B exp(−K)≤h/2`. Thus h/2≤sqrt(2L)E; squaring gives h²≤8LE², as claimed.

The exact inverted survivor is `E>0` and `exp(exp(h²/(8E²)−a)−K)≤V+1`. Indeed, take N=log(V+1)≥0, so V≤exp N. The budget inequality and h>0 first exclude E=0. Divide by 8E²>0 to get h²/(8E²)−a≤log(N+K), exponentiate, subtract K, and exponentiate again. Both logarithm arguments are positive. This is an unconditional bound on every actual packet and real Xi zero, not a presumed approximation rate.

**Attack and novelty verdict: BRIDGE / quantitative obstruction to strong-norm transfer.** This is a Fourier cutoff/uncertainty argument specialized to the actual theta tail, not a claimed new general approximation theorem. Current partial corpus search returned tail estimates but no exact packet cost law; no absence certificate. Primary superoscillation and uniform Wiener papers concern adjacent cost/completeness questions, not an imported proof of this inequality. The uniform cheap strong-L²-transfer shortcut is incompatible with this bound. C7 itself is not refuted: it needs only finitely many quadratic moment inequalities, so a transfer adapted to those forms can avoid strong approximation. Its positive-cost construction remains the main open core. The complete stability law, optimized budget and explicit inverted variation bound are now formally audited in `WeilWorkDeficitXiApproximationCost.lean`; only the narrowly stated uniform shortcut is retired.

Scope of that retirement: C8 refutes a uniform cheap strong-L² transfer theorem covering all spectral shifts, since it covers a shift by any real Xi zero. It does not by itself refute transfer of the particular M-dependent Bernoulli branch chosen in C7's dual argument. Such a conclusion would additionally need a quantitative nonzero Fourier mismatch for those specific shifts; that has not been proved. The spectral Plancherel identity remains a paper bridge, separate from the physical L² Lean theorem.

### C9: test the moment cost directly

The next competing conjectures concern the actual signed forms, not approximation of their spectral witnesses. For real coefficients α=(α₂,…,α_M), put `B_α=Σ α_n κ(log n)` and, for a real packet P, `Q_α(P)=Σ α_n b_P(n)`. Normalize packet variation `Σ|c_j|≤1` and restrict shifts to [−a,0]. The strong candidate is: for every a>0 and ε>0 there is C>0 such that every M≥2 and every α with B_α>0 admit P with `Q_α(P)≤−C⁻¹exp(−εM)B_α`. Its competing obstruction is a fixed aperture a and a sequence of normalized dual forms B_α=1 whose most negative unit-variation packet value decays at a genuinely positive exponential rate. These are target-relative statements; qualitative density and generic cone interior do not decide them. The [OPEN CORE] is the uniform cost rate of this exact quadratic witness. This representation does not itself prove C7 or claim a new duality theorem.

Current primary-parent checks: Jorgensen–Niedzialomski's positive-definite extension theorem and Alpay–Colombo–Sabadini's analytic extension construction are qualitative parents; their existence statements do not supply this target-relative rate. A second corpus search is checking positive polynomial spectral multipliers as a possible witness construction. No polynomial positivity, factor preservation, degree bound, or coefficient bound is presumed.

### C10: bounded-order derivative cancellation, competing construction

The corpus already defines `kernelComb a=Σ_k a_k Φ^(k)` and proves `paperFT_riemannKernelDeriv_at_zero` at both actual Weil evaluation points. This is an existing exact radical family, not a new discovery. It avoids converting a shifted Xi profile into a zero-preserving function. The available superexponential-decay theorem fixes derivative order first; it supplies no uniform cost as order grows.

**Exact conjecture.** There are c>0 and an unbounded set of integers M≥2 such that, for each such M, a finite family of derivative packets `f_j=Σ_(k=0)^M a_(j,k) Φ^(k)` with real coefficients a_(j,k) contains f₀=Φ and has total autocorrelation `b_M(n)=Σ_j ∫ f_j(u) conjugate(f_j(u−log n)) du` satisfying both `b_M(n)=0` for 2≤n≤M and `Σ_(n>M)(Λ(n)+atomCost(n))|b_M(n)|≤exp(−cM)`. These autocorrelations are real and even, since the actual derivatives are real on the real axis. The weight is the actual PBAP repair weight, not a surrogate polynomial weight. The retained baseline gives the spectral lower bound away from actual Xi zeros.

This directly prices the complete arithmetic tail and restricts derivative order to M. It competes with C7's physical-translate construction; neither is assumed. Its first [OPEN CORE] is a positive polynomial-square combination of degree at most 2M that cancels the finite cosine moments while retaining that full tail bound. Qualitative polynomial density and the already-proved radical identities do not pay this obligation. No new Lean declaration will encode it as a premise.

**Preliminary attack: SURVIVES PRELIMINARY ATTACK, still unproved.** It may fail already at the bounded-degree positive cone, or at the growing-order tail cost. It has no RH, positivity-of-Xi-Hankel, or prescribed-cancellation premise. The current partial corpus searches and primary kernel/extension papers do not provide this exact degree-and-tail statement. No absence or novelty certificate is claimed. Success would give the positive near-radical families required by C; failure should identify a degree or tail boundary, rather than retire all derivative packets. Its implication still needs the derivative-family version of weighted truncation and the already-recorded null-repair assembly; those are separate obligations, not presumed Lean results.

## Candidate A: sharper arithmetic cost of spectral deficit

Conjecture: for every full-positive `λ`, integer `n ≥ 2` and `ε > 0`, eventually

`|λ(n) − Λ(n)| ≤ 4π√n (D(T)/T + ε)`.

The prior corpus bound had `n` in place of `√n`. Mechanism: subtract the actual shared critical atoms; compare fixed-frequency Fourier averages of the remaining positive measure with those of the deficit divisor. The Poisson Fourier multiplier cancels the excess abscissa. No RH assumption is used.

**Status: complete paper proof and audited Lean capstone.** The final internal proof is recorded below under “internal subtraction route” and “unconditional eventual form”; it replaces separate external ordinate asymptotics. This is a quantitative corollary of classical Fourier theory and the corpus's full-positive measure representation, not a claim of a new foundational theorem. The searches recorded in `EVIDENCE.md` did not locate this precise improvement; they do not certify novelty.

### A1. Truncated Poisson transport

Write `P_b(x)=b/(b²+x²)`, with fixed `b>0`, and `μ=boundaryMeasure hW`. The corpus proves `μ([r−1,r+1])≤C log(|r|+3)`. For every fixed real `k` and `T≥2`,

`∫_0^T exp(ikt)(P_b*μ)(t) dt = π exp(−b|k|) ∫_(0,T] exp(ikr) dμ(r) + O_(μ,b)(log²(T+3)).` (A1)

Here the error bound can be chosen independently of `k`. The full-line Poisson transform is `∫_ℝ exp(ikx)P_b(x)dx=πexp(−b|k|)`. Subtract the full-line transform separately for each `r∈(0,T]`, leaving exactly the transport across the two endpoints. Absolute value of the remainder is bounded by

`∫ μ(dr) ∫ P_b(t−r) |1_(0,T](t)−1_(0,T](r)| dt`.

Tonelli applies because the integrand is nonnegative. On `−T≤r≤2T`, the inner integral is bounded by a constant times the sum of `(1+|r|)⁻¹` and `(1+|r−T|)⁻¹`. Cover by unit intervals. Each has mass `O(log(T+3))`, and summing the two reciprocal-distance bounds costs `O(log(T+3))`. For `r<−T` or `r>2T`, the inner integral is at most `C_b T/r²` after an absolute constant change in the positive tail. The unit-interval sum is bounded by `C_b T Σ_(j≥T) log(j+3)/j²=O_b(log(T+3))`. Endpoint atoms are covered by the adjacent bounded intervals. This proves the finite error estimate and also the absolute integrability needed for Fubini in (A1). The estimates apply to `k=0` as well.

### A1a. A less demanding formal route to the sufficient `o(T)` error

Lean status: interval mass, scalar leakage bounds, the finite four-region estimate and the full `o(T)` leakage limit are formalized in `WeilWorkDeficitMassBounds`, `WeilWorkDeficitPoissonLeakage` and `WeilWorkDeficitLeakageIntegral`. Direct audits and targeted builds passed; the original eleven public theorem axiom audits use standard foundations only. Complex Fourier transport is also audited in `WeilWorkDeficitFourierTransport`.

The coefficient argument needs only `o(T)`, so it need not formalize the sharper logarithmic-square error first. The following complete alternative uses the already proved integrability of `(1+r²)⁻¹` against the canonical measure.

First extend the unit-window bound to all `a≤b`:

`μ([a,b])≤C(b−a+1) log(max(|a|,|b|)+3)`. (A1a)

Cover `[a,b]` by the intervals of radius one centered at `a+j`, with `j=0,…,floor(b−a)`. Every point is covered by taking `j=floor(x−a)`. Every center belongs to `[a,b]`; there are at most `b−a+1` centers. Summing the existing unit-window estimate proves (A1a). This is a bridge, not a novelty claim.

For the leakage integral in (A1), take `H=√T` and `T≥1`. On the two endpoint neighborhoods `[-H,H]` and `[T−H,T+H]`, the leakage kernel is at most `π`. By (A1a), their contribution divided by `T` is `O(log(T+3)/√T)`. On the rest of `[-2T,2T]`, the distance to each relevant endpoint is at least `H`; integration of `b/x²` bounds the leakage by `2b/H`. By (A1a), this contribution divided by `T` is also `O(log(T+3)/√T)`.

For `|r|>2T`, the ordinate lies outside `(0,T]` and the leakage is at most `4bT/r²`. After division by `T`, it is bounded by `8b/(1+r²)` and vanishes eventually for each fixed `r`. Dominated convergence makes this last contribution tend to zero. Thus the full leakage divided by `T` tends to zero, with no tail-rate assumption. All bounds are independent of the Fourier frequency because the character has modulus one.

Formal sequence: arbitrary-interval mass bound; elementary leakage-kernel inequalities; integrable-tail limit; actual canonical Fourier transport. No additional hypothesis is to be added to the capstone.

For the fixed width `b=3/2`, write `L_T(r)=|K_T(r)−π1_(0,T](r)|` and
`Q(T)=∫_(|r|>2T) (1+r²)⁻¹ dμ(r)`. The explicit finite bound being formalized is, for `T≥1,H>0`,

`∫L_T dμ ≤ πμ([-H,H])+πμ([T−H,T+H])+(3/H)μ([-2T,2T])+12T Q(T)`.

Every point belongs to one of the two endpoint intervals, to the remainder of the bulk interval, or to its complement. The first two costs use `L_T≤π`. Outside the endpoint intervals both distances are at least `H`, so the arctangent tail inequality gives `L_T≤3/H`. Outside the bulk, `|r−t|≥|r|/2` for `0≤t≤T`; integrating the resulting bound on `P_(3/2)` gives `L_T≤12T/(1+r²)`. Indicator majorants for these four regions are integrable by (A1a) and Cauchy-weight integrability. This proves the displayed estimate without a prior integrability assumption on `L_T`. Dominated convergence gives `Q(T)→0`. At `H=√T`, (A1a) bounds the other three costs divided by `T` by `(6π+15)C log(2T+3)/√T`, which tends to zero.

The next exact Fourier transport bound follows pointwise before Fubini. Put `U=(0,T]`. For every bounded measurable complex `φ` with `|φ|≤1`,

`|∫_U φ(t)P_(3/2)(t−r)dt − 1_U(r)∫_ℝ φ(t)P_(3/2)(t−r)dt| ≤ L_T(r)`.

For `r∉U` this is the norm bound on the window integral. For `r∈U`, subtract the full integral and bound the integral over `Uᶜ`; its positive kernel mass is `π−K_T(r)`. Integrability of `K_T` follows from `K_T≤L_T+π1_U` and finiteness of `μ(U)`. This also pays absolute product integrability in Fubini, since the character has norm one. For `φ(t)=exp(ikt)`, translation and the corpus Cauchy Fourier identity identify the full integral as `πexp(-(3/2)|k|)exp(ikr)`. Integrate the pointwise bound against `μ`, use Fubini and the canonical Poisson representation. The resulting error is bounded by `∫L_T dμ` for every real `k`. Its normalization by `T` tends to zero even if `k` is chosen as a function of `T`. This uniformity is for the forward transport error; division by the vanishing Fourier multiplier does not give uniform recovery at unbounded frequencies.

### A2. The canonical measure's arithmetic Fourier coefficients

Use `b=3/2`, so `(P_b*μ)(t)=Re Φ(2+it)`. The arithmetic identity in the corpus gives

`Re Φ(2+it)=A(t)−Σ_(j≥2) λ(j)j⁻² cos(t log j)`.

The series is absolutely and uniformly convergent. The archimedean term satisfies `A(t)=½log(t/(2π))+O(1/t)` for `t≥2`; its bounded initial segment contributes `O(1)`. For fixed nonzero `k`, integration by parts of the logarithm shows `T⁻¹∫_0^T exp(ikt)A(t)dt→0`. At `k=log n`, elementary exponential averaging and dominated convergence for the absolutely summable series give

`T⁻¹∫_0^T exp(it log n)Re Φ(2+it)dt → −λ(n)/(2n²)`.

Divide (A1) by `T`; its error tends to zero. Since `exp(−(3/2)log n)=n⁻³ᐟ²`,

`T⁻¹∫_(0,T] exp(ir log n)dμ(r) → −λ(n)/(2π√n)`. (A2)

For `k=0`, (A1) and the already proved smoothed counting law give

`M(T):=μ((0,T]) = T/(2π)log(T/(2π))−T/(2π)+O_μ(log²(T+3))`.

The ordinary zero count `N(T)` has the same main term with error `O(log(T+3))`. Thus `M(T)−N(T)=o(T)`. The count comparison is used only for the surplus left after subtracting shared mass; it is not treated as evidence of overlap.

### A3. Actual zero ordinates

[Ford–Zaharescu, Theorem 1 and Corollary 2](https://arxiv.org/html/math/0405459v2) give an unconditional, multiplicity-counted ordinate limit normalized by `T`. Applying their result to the smooth first character at `α=log n/(2π)` and evaluating its coefficient in their density gives

`T⁻¹ Σ_(q:0<γ_q≤T) exp(iγ_q log n) → −Λ(n)/(2π√n)`. (A3)

For non-prime-powers the coefficient is zero; for `n=p^a` it is `−log p/(2πp^(a/2))`. This invokes neither their RH-dependent extension to rough tests nor their conjecture for interval indicators. Ordinary zero-count-normalized equidistribution would not suffice.

A route using only corpus ingredients is also available in principle: the Poisson Fourier identity for the actual divisor produces an extra factor `cosh((β−1/2)log n)` after reflection pairing. Its excess is bounded by a constant times `Σ(β−1/2)²`. `SelbergExponentialNearLineDensity` supplies a uniform moving-scale exponential density estimate. Transporting its admissible rectangles to multiplicity copies and summing the tails should prove this excess is `o(T)`. **This formal transport has not been completed.** The previously inspected weaker `SelbergNearLineZeroDensity` alone was not a justified replacement.

### A4. Exact shared mass and the comparison

Let `ν_T=Σ_(q:0<γ_q≤T) δ_(γ_q)`. At each actual critical divisor point `ρ=1/2+iγ` in the window, retain mass `min(m_ρ, μ({γ}))`; let `χ_T` be the resulting finite atomic measure. Distinct critical points have distinct ordinates. Hence `χ_T≤μ|_(0,T]` and `χ_T≤ν_T`, even when off-line zeros have those same ordinates. By the exact definition of the copy deficit,

`χ_T(ℝ)=N(T)−D(T)`.

Put `μ_T^+=μ|_(0,T]−χ_T` and `ν_T^−=ν_T−χ_T`. These are positive finite measures, with masses `M(T)−N(T)+D(T)` and `D(T)`. For every measurable `f` with `|f|≤1`, the exact decomposition and estimate are

`∫f dμ|_(0,T]−∫f dν_T = ∫f dμ_T^+−∫f dν_T^−`,

`|∫f dμ|_(0,T]−∫f dν_T| ≤ M(T)−N(T)+2D(T)`. (A4)

Taking the character from (A2)–(A3), dividing by `T`, and using `M(T)−N(T)=o(T)` proves the eventual bound in Candidate A for every positive `ε`. This improves the coefficient scale but gives no upper bound on `D(T)`.

### A5. Attack verdict and formal closure

- A possible diffuse part of `μ` remains in `μ_T^+`; no discreteness assumption enters.
- Multiplicities are retained in both `ν_T` and `χ_T`.
- Shared ordinates involving off-line zeros only make `χ_T≤ν_T` easier; they do not erase off-line deficit.
- All limits use fixed `n`; no uniformity in `n` is asserted.
- No atom is identified from a smoothed window.
- (A4) is formalized for the actual canonical objects in `WeilWorkDeficitSharedMass.lean`, with direct Lean and standard-only axiom audits. Analytic transport and linear-scale Fourier limits have also been compiled and discharged in the unconditional eventual coefficient theorem; none is inserted as a new scientific premise.

## Bridge B: uniform recovery on every prefix of a bounded height window

This bridge is not claimed as novel science. It pays the passage from Poisson values to the exact atom deficits without inserting a uniform convergence assumption.

Lean status: `WeilWorkDeficitRecovery.lean` compiled, directly audited, umbrella-wired; all eight public theorem axiom lists contain only standard Lean foundations.

Fix a full-positive `λ`, with canonical measure `μ` and continuation `Φ`. For each actual zero copy `q`, write `m_q` for its positive multiplicity and `γ_q` for its ordinate. Define

`a_b(q) = b Re Φ(1/2+b+iγ_q)/m_q`,

and `d_b(q) = max(1-a_b(q),0)` at critical copies, `d_b(q)=1` elsewhere. Put

`D_b(T) = Σ_(0<γ_q≤T) d_b(q)`.

For each `M`, let `S_M` be the finite set of copies with `0<γ_q≤M`, and define the complete recovery remainder

`R_M(b) = Σ_(q∈S_M) |d_b(q)-d(q)|`.

Then, unconditionally for this `λ`,

1. `D(T) = D_b(T) + Σ_(0<γ_q≤T)(d(q)-d_b(q))` for every real `b,T`.
2. For every `T≤M`, `|D_b(T)-D(T)|≤R_M(b)`.
3. `R_M(b)→0` as `b→0+`.
4. Consequently, for every `M` and `ε>0`, some `δ>0` satisfies `|D_b(T)-D(T)|<ε` simultaneously for all `T≤M` and all `0<b<δ`.

Proof: `S_M` is finite because it is contained in the bounded ordinate band `|γ_q|≤|M|`, whose finiteness is `finite_xiZeroCopy_band`. For `T≤M`, every summand outside `S_M` vanishes. Thus every infinite sum in (1) and (2) is literally a finite sum over `S_M`. Subtraction and the finite triangle inequality prove (1) and (2). At each critical copy the existing theorem `tendsto_mul_re_weilContinuation_atom` gives `a_b(q)→μ({γ_q})/m_q`; continuity of subtraction, maximum and absolute value gives `|d_b(q)-d(q)|→0`. At off-line copies this difference is identically zero. The finite-sum limit proves (3); the definition of a right-hand limit gives (4). This includes all multiplicity copies and all prefixes, including empty negative-height prefixes. It supplies no rate for `δ(M,ε)` and no small-deficit bound.

## Rejected cycle: total count / surplus balance

Verdict: **REDISCOVERED / BRIDGE**. The earlier singular-deficit card, especially L127 and its cycle-222 addendum, already records surplus compensation, and `WeilFullConePoissonCountingIdentity` formalizes the smoothed balance. A restatement does not advance detection. The paper card's claim that logarithmic local mass alone yields an `O(log T)` unsmoothing error needs a separate audit: absolute Poisson tails generally accumulate a harmonic factor. No contradiction to the compiled smoothed identity is asserted.

## Main target

Still open: derive `∀ η>0, ∃ᶠ T→∞, D(T)/T≤η` from full Weil positivity. Neither Bridge B nor Candidate A supplies this estimate.

## Candidate A, internal subtraction route (2026-10-07)

This replaces the separate archimedean and Riemann–von Mangoldt asymptotics in A2–A3. Classification: **BRIDGE** to the sharper coefficient estimate; no small-deficit conclusion and no novelty claim for the auxiliary density argument.

### Exact arithmetic mean, with no new premise

Fix `hW : WeilPositiveFull λ`, a real `σ>1`, and `n≥2`. Set
`Fσ(t)=Re Φλ(σ+it)−Re ξ'/ξ(σ+it)` and
`a_j=(Λ(j)−λ(j))j^(−σ)` for `j≥2`, zero for `j=0,1`.
`WeilConeSingularDeficitEnvelope.summable_abs_deviationCoeff` proves absolute summability, and `re_weilFunction_sub_re_logDeriv_xi`, together with `weilContinuation_eq`, proves `Fσ=logCosSeries a`. The continuous cosine series is integrable on every bounded interval. The corpus's `tendsto_mean_logCosSeries_mul_cos` and `bohrLimit_eq_coeff` therefore give

`T⁻¹∫_0^T Fσ(t) cos(t log n)dt → (Λ(n)−λ(n))n^(−σ)/2`.

The cited mean starts at 8. Add the fixed finite integral from 0 to 8, divide by T, and use its limit zero. At frequency zero, use `bohrLimit_one_eq_zero` instead: `T⁻¹∫_0^T Fσ(t)dt→0`. This proof is dependency-closed before Lean; both identities are merely exact extraction from an already proved series, not a new rigidity claim.

### Horizontal square moment: paper derivation from the strong corpus estimate

Let `δ_q=|β_q−1/2|` and `Q(T)=Σ_(0<γ_q≤T) δ_q²`, retaining every Xi divisor copy. The theorem `exists_selberg_exponential_nearLine_zeroDensity` supplies constants A,K and common admissible heights `T₁∈(U/4,U/4+1)`, `T₂∈(U/2−1,U/2)` for all permitted scale parameters a. Put `L=log U` and `a=2400 log L`. Eventually `a≥1` and `2a+2≤L`, because `log L/L→0`. Its far-right count, divided by U, is bounded by

`A/(8πaL) + K L²/(2πaU)`.

Indeed the exponential is `exp(−a/1200)=L^(−2)`, and `T₂−T₁≤U/4`. The count is a sum of analytic orders. On these high rectangles zeta is analytic and the Xi and zeta orders agree; the rectangle zero set is finite by isolated zeros on a compact set. Thus it counts exactly the right-hand Xi copies. `xiZeroCopyLineConjEquiv`, with `xiZero_lineConj_eq`, preserves ordinate and multiplicity and exchanges the two sides of the critical line. It doubles this upper bound to control all copies with `δ_q≥2a/L`.

The remaining copies have squared displacement at most `(2a/L)²`. The exact uniform unit-window bound `ncard_xiOrdinateWindow_one_le_log`, summed over a unit cover, bounds the whole dyadic-band count by `O(U log U)`. Thus their contribution divided by U is `O(a²/L)→0`. Far copies have `δ_q²<1/4`, so their contribution divided by U also tends to zero. The two omitted endpoint strips have width at most one and `O(log U)` copies by the same unit-window bound; their contribution is negligible. This proves `Σ_(U/4<γ≤U/2)δ_q²=o(U)`.

For completeness, the passage to the full prefix does not assume a uniform number of dyadic bands. Given ε>0, choose V₀ so every band `(V,2V]`, V≥V₀, has square mass at most εV. For any large T, successively halve T until the lower endpoint lies below V₀. The sum of the band bounds is at most εT; all remaining copies lie in the fixed bounded window `(0,2V₀]`, of finite square mass. Divide by T. Since ε is arbitrary, `Q(T)/T→0`.

This was the initial paper reduction to the cited strong estimate. The smaller uniform weighted-tail argument below was selected for Lean; its rectangle analytic-order transport, endpoint strips, and dyadic prefix sum are now audited in SquareWindow and SquareMoment. `Q(T)=o(T)` is proved, not assumed.

**Stronger corpus input found before implementation.** `ZetaCriticalScaleExponentialTailMoment.exists_offLineTailMoment_window_exponential_le` already proves, with the same admissible heights and every fixed `c≥4`,

`Σ_(δ≥c/L, right side) mδ ≤ A/(2π)(1+4800/c)exp(−c/4800) U + (2K/π)L²`.

Use this in place of the moving-cutoff calculation above. For each fixed c, near copies contribute `O(c²/L)` to `Q/U`; on the far set, `δ²≤δ/2`. Pairing the left side gives
`limsup Q_band(U)/U ≤ A/(2π)(1+4800/c)exp(−c/4800)`.
This bound holds for every `c≥4`; letting c tend to infinity proves the same zero limit. This removes all moving-parameter admissibility work and reuses an existing weighted result. `ZetaRightZeroWeightedCount.windowZeros` and `mem_windowZeros_iff` already construct the exact finite rectangle and were reused. Multiplicity-copy transport, interval endpoints, and prefix assembly are now formalized. No fresh scientific novelty is asserted for this consequence.

An even smaller sufficient input is already proved in `ZetaCriticalScaleTailMoment.exists_offLineTailMoment_window_le`: its tail bound is `(D/c)(T₂−T₁)+K L²` for every `c≥2`. The identical square-moment split gives `limsup Q_band(U)/U≤D/(4c)`, and c is arbitrary. Thus the exponential refinement is unnecessary for this fixed-frequency projection. The earlier warning about the weak count alone remains valid; the inspected, uniform **weighted tail theorem** supplies the additional inference. Prefer this smaller input when formalizing the projection.

### Exact finite-copy estimate to formalize

The preceding tail theorem implies the following unconditional statement. There are D,K≥0 such that, for every sufficiently large U, admissible T₁,T₂ exist and, for every c≥2 and every finite set F of actual Xi copies with ordinates in `[T₁,T₂]`,

`Σ_(q∈F)(β_q−1/2)² ≤ (c/log U)² #F + (D/c)(T₂−T₁)+K(log U)²`.

Here is the multiplicity audit. For any finite F and finite complex set Z containing all its support points, enlarge F to all copies above its support image S. For nonnegative f this gives `Σ_F f(ρ_q)≤Σ_(ρ∈S)m_ρ f(ρ)≤Σ_(z∈Z)ordζ(z)f(z)`, since Xi and zeta have equal analytic order in the open strip. Apply this to the right tail, with `f(z)=max(Re z−1/2,0)` and Z the corresponding filter of the existing `windowZeros T₁ T₂`. Each right tail sum is at most B=`(D/c)(T₂−T₁)+K(log U)²`.

For the left tail, send its copies through the injective `xiZeroCopyLineConjEquiv`. This preserves ordinates and changes the displacement to its negative. Its image is another finite set in the right tail, so its weighted sum is also at most B. No closure of F under conjugation is needed. Write v=`c/log U`>0 and δ=`β−1/2`, with `|δ|<1/2`. Pointwise,

`δ² ≤ v² + (1/2)1_(v≤δ)δ + (1/2)1_(v≤−δ)(−δ)`.

If neither tail condition holds, `|δ|<v`; in either tail use `δ²≤|δ|/2`. Summing proves the claimed estimate. This paper proof precedes the new Lean module. It is a precise corpus consequence and a bridge to the full prefix square-moment limit, not a fresh density conjecture.

### Endpoint and prefix assembly, exact quantifiers

For every ε>0, eventually in U, **every** finite set F of copies with `U/4<γ≤U/2` satisfies `Σ_F δ²≤εU`. To prove this, retain G with `T₁≤γ≤T₂`. The near contribution in the finite-copy estimate is bounded by `(c/log U)² #F`. `XiZeroCountLocalCeiling.exists_card_window_le`, applied at t=U/4 and H=U/4, gives `#F≤(U/(8π)+2C)log(U/2)`. Thus this contribution divided by U tends to zero for each fixed c. The remaining G terms divided by U are at most `D/(4c)+K(log U)²/U`.

Every copy in F outside G lies either in the unit window centered at U/4 or in the unit window centered at U/2. Since δ²≤1/4 and `ncard_xiOrdinateWindow_one_le_log` bounds each window by `16(C₀+log(|t|+4))`, the lost square mass is at most `8(C₀+log U)` for U≥16. Divide by U. Choose c≥2 with `D/(4c)<ε/2`, then choose U large enough that all terms tending to zero total less than ε/2. The choices are independent of F, giving the asserted uniform finite-set bound.

For the full prefix Q, first obtain `∀ ε>0, ∀ᶠ t→∞, Q(2t)−Q(t)≤εt` by substituting U=4t and applying the uniform band bound with tolerance ε/4. Q is nonnegative and monotone, since its finite sums have nonnegative weights. Choose V≥1 after the threshold for a given ε. Induction gives
`Q(2^n V)≤Q(V)+ε·2^n V` for all natural n: the next band contributes at most `ε·2^n V`. For T≥V choose n with `2^n≤T/V<2^(n+1)`. Monotonicity yields
`Q(T)≤Q(V)+2εT`.
Hence `Q(T)/T≤Q(V)/T+2ε`. First let T tend to infinity, then ε tend to zero; the nonnegative quotient converges to zero. This proof uses no unproved uniformity in the number of dyadic bands and no premise about critical support.

### Zero-side transport and cancellation

For each copy use `P_b(t−γ)` with `b=2−β∈(1,2)`. Its full Fourier transform is `π exp(−b|k|)exp(ikγ)`. The finite-window error is its omitted mass inside the window and its included mass outside. Pointwise, `P_b≤(3/2)P_(3/2)` for all `1≤b≤2`, so the error is bounded by `3/2` times the fixed-width leakage at the same ordinate. The zero-copy measure has logarithmic interval mass by `XiWindowZeroCount` and an integrable Cauchy weight by the existing weighted zero-copy summability. Hence the same endpoint-width `√T` and Cauchy-tail argument used for the canonical measure gives total zero-side error `o(T)`.

Pair copies by **line conjugation** `ρ↦1−conj ρ`, not reflection `ρ↦1−ρ` (the latter changes ordinate sign). The multiplier becomes `π exp(−(3/2)|k|) cosh((β−1/2)|k|)`. For fixed k, Taylor's theorem on `[-|k|/2,|k|/2]` gives `|cosh(kδ)−1|≤C_k δ²`; the square-moment result makes the summed multiplier error `o(T)`. At k=0 this replacement is exact and needs no density theorem.

Subtract the canonical and zero transport identities, take real parts at `k=log n`, and use the arithmetic mean at σ=2. This yields
`T⁻¹ Re(∫_(0,T]e^(ir log n)dμ−∫_(0,T]e^(ir log n)dν) → (Λ(n)−λ(n))/(2π√n)`.
At k=0 it yields `(M(T)−N(T))/T→0`. Applying the compiled shared-mass inequality proves Candidate A. These final transports and the capstone are now directly audited in Lean.

### Exact finite-window projection, before Lean

Write `F_T={q:0<γ_q≤T}`, `a=|k|`, and `δ_q=β_q−1/2`. Line conjugation is a bijection of `F_T`; it fixes γ and replaces δ by −δ. Reindexing the finite sum therefore gives exactly

`Σ_(F_T) exp(−(2−β_q)a)e^(ikγ_q) = exp(−3a/2) Σ_(F_T) cosh(aδ_q)e^(ikγ_q)`.

This uses the two exponential summands defining cosh, not an assumed symmetry of any chosen subwindow. The support is the actual entire ordinate prefix, whose invariance is proved from `xiZero_lineConj_eq`.

The corpus scalar inequality `HTGeometry.cosh_sub_one_le`, applied to `|aδ_q|`, and monotonicity of cosh on nonnegative arguments imply

`0≤cosh(aδ_q)−1≤(a²/2)cosh(a/2)δ_q²`,

because every actual zero has `|δ_q|<1/2`. Each character has norm one. The triangle inequality then bounds the norm of the projected multiplier difference by

`exp(−3a/2) (a²/2) cosh(a/2) Q(T)`.

For every fixed real k this divided by T tends to zero by `tendsto_deficitSquareCount_div`. This is unconditional, multiplicity-correct, and exactly the zero-side projection needed by Candidate A. No claim of uniform inverse Fourier recovery or atom matching follows.

### Actual ordinate measure: interval and tail obligations

For `ν=Σ_q δ_(γ_q)`, the measure of `[t−1,t+1]` equals the cardinality of the finite copy window `|γ_q−t|≤1`. Thus the existing bound gives `ν([t−1,t+1])≤16(C₀+log(|t|+4))`. Put `A=(|C₀|+log 2)/log 3`. Since `log(|t|+3)≥log 3>0` and `log(|t|+4)≤log 2+log(|t|+3)`, this is at most `16(A+1)log(|t|+3)`. The already proved finite unit-cover argument therefore gives `ν([a,b])≤C(b−a+1)log(max(|a|,|b|)+3)` for all a≤b. In particular all bounded intervals have finite ν-mass.

The corpus theorem `summable_inv_one_add_sq_im` and the integration formula for a countable sum of Dirac measures give `∫(1+r²)⁻¹dν<∞`. These discharge both inputs of the existing endpoint-and-tail proof for ν itself; no full-Weil-positive witness for the von Mangoldt function is assumed. Reuse the measure-independent leakage argument for both measures, preserving the existing canonical public statements.

### Actual zero transport: discharged implementation obligations

Use the existing counting kernel module, without importing the distinct full-cone counting module: both currently declare the same fully qualified name `RHTower.WeilSpectral.integral_poissonKernel_eq` with different signatures. The needed complex summation argument is independent of that name collision.

For `P_b(r,t)=b/(b²+(t−r)²)` and `1≤b≤2`, clearing positive denominators proves `P_b≤(3/2)P_(3/2)`: the numerator difference is `(9/4)b(b−1)+(9/4−b)(t−r)²≥0`. The existing full-line Cauchy Fourier transform, translated by r, gives `∫e^(ikt)P_b(r,t)dt=πexp(−b|k|)e^(ikr)`. Split into `(0,T]` and its complement. If r lies inside the window, the error is the omitted integral; outside it is the included integral. The norm-one character and the kernel comparison give the same bound `(3/2)L(T,r)` in both cases.

For every finite T, integrate the actual copy series termwise with the summable local majorant `C(T)/(1+γ_q²)` from `copyPoisson_le_local`. The character has norm one, so the existing dominated-summation proof works for its complex product. The expected multiplier has finite support `F_T`. Sum the error norms and use integration over the actual Dirac-sum measure: total error is at most `(3/2)∫L(T,r)dν(r)`. Its normalized limit is zero by the actual-measure leakage theorem. Add π times the audited projection error to replace the true multipliers by the projected character sum.

Finally identify that finite character sum with the integral over the restricted actual ordinate measure. Subtract canonical and zero transports and apply the audited arithmetic cosine and zero-frequency means. ZeroKernel, ZeroTransport and Coefficient now discharge these obligations with standard-only axiom audits. No separate Riemann–von Mangoldt or archimedean asymptotic is introduced.

### Candidate A: unconditional eventual form

The sharpened theorem has no assumed upper deficit bound: for every full-positive λ, integer n≥2, and ε>0, eventually

`|λ(n)−Λ(n)|/(4π√n) ≤ D(T)/T + ε`.

Let `G_k(T)=∫_(0,T]e^(ikr)dμ−∫_(0,T]e^(ikr)dν`. The transport identities and arithmetic means give `Re G_(log n)(T)/T→(Λ(n)−λ(n))/(2π√n)` and `Re G_0(T)/T=(M(T)−N(T))/T→0`. Only real parts are needed; no sine-mean premise is introduced. Since `|Re G_k|≤‖G_k‖≤M−N+2D`, the real function

`S_n(T)=(|Re G_(log n)(T)/T|−(M(T)−N(T))/T)/2`

is at most D(T)/T for T>0 and tends to `|λ(n)−Λ(n)|/(4π√n)`. The eventual ε-bound follows directly from convergence. This improves the old n factor for every n≥2, while making no claim that D(T)/T has a vanishing subsequence. It is the requested quantitative intermediate comparison, not the final producer.

## Next cycle: arithmetic repair and mass outside the actual critical zeros

Status: **CONJECTURE; construction open; no new Lean theorem claimed**.

The source theorem `WeilSpectral.eq_vonMangoldt_of_boundaryMeasure_criticalZeros` already proves rigidity from support on the actual critical zeros, with no atom-size bound and no assumed RH. Thus it is unnecessary to solve the older paper's separate single-zero interpolation problem after support has been proved. The remaining support problem is still substantial.

Let `Z={r: ζ(1/2+ir)=0}`. Use the exact corpus types and normalization:

- `f : WeilOneSided.WeilTestFn` is a complex C² compactly supported test;
- a finite positive mixture is `c : WeilTestFn →₀ ℝ` with `c(f)≥0`;
- `S_c(r)=Σ_f c(f)|paperFT f(r)|²`;
- `b_c=WeilWorkPBAP.defect c`, so `b_c(n)=Σ_f c(f) logValue f n`, including the factor `1/√n` already present in `logValue`;
- `R(c)=Σ_f c(f)|Re(zetaZeroConfig.W f f)|`;
- `B(c)=Σ_(n≥2) [Λ(n)+WeilWorkPBAP.atomCost n]|b_c(n)|`.

Every sum is finite: c is finitely supported, and the corpus's `finite_support_logValue` makes b_c finitely supported. No spectral support or atom mass is assumed in these definitions.

**Conjecture C (weighted arithmetic repair near the Riemann radical).** For every compact `K⊂ℝ\Z` and every ε>0 there is a finite positive mixture c satisfying

`S_c(r)≥1` for all r∈K, `R(c)≤ε`, and `B(c)≤ε`.

This is an assertion about the explicit test functions, actual zeta Weil form, and already defined arithmetic repair costs. It does not take small deficit, RH, support of μ, a functional equation for an arbitrary producer, or convergence of a boundary Dirichlet series as an input. The selected construction to investigate is mixtures of truncated Riemann-kernel convolutions, allowing interference within each test before positive mixing. Merely translating a fixed test leaves its autocorrelation unchanged and cannot repair its arithmetic defects.

### Exact implication, distinguished from the unproved construction

For any supplied hW let μ be its actual canonical measure. Set `c'=nullRepair c` using `WeilWorkPBAPNullRepair`. The proved repair is a positive mixture, its logarithmic defect is exactly zero at every integer, and `S_c'≥S_c`. Its energy E is the full pole-plus-archimedean functional in the corpus normalization.

The explicit formula gives

`E(c)=Σ_f c(f) Re Wζ(f,f)+Σ_(n≥2) Λ(n)b_c(n)`.

The exact repair bound and nonnegativity of Λ give

`E(c')≤E(c)+Σ atomCost(n)|b_c(n)|≤R(c)+B(c)≤2ε`.

The canonical spectral representation, finite linearity, and exact integer cancellation give `∫S_c' dμ=E(c')`. Hence `μ(K)≤2ε`. For arbitrary ε this forces μ(K)=0. The open set ℝ\Z is a countable union of compact intervals contained in it: ζ is continuous on the critical line, and rational closed subintervals form a countable cover of its nonzero locus. Countable subadditivity therefore gives μ(ℝ\Z)=0. The existing carrier-rigidity theorem then gives λ=Λ and RH for the supplied hW. This implication does not construct c and is not the requested unconditional proof.

### Preliminary attack and exact open core

- A small zeta Weil energy alone does not make E(c) small: its arithmetic pairing must also be paid. B(c) includes both that pairing and the cost of exact positive repair. Dropping either term reproduces the failed near-radical trace argument.
- Counting interpolation conditions does not establish a positive mixture with small weighted defect. Nor does a small unweighted defect imply B(c) is small when the active integers grow.
- Under RH, the broad local null-capacity idea is the older L402(N1) programme. The current conjecture asks for an explicit weighted repair construction without RH. It has not passed a scientific novelty gate merely because this formulation differs.
- Connes–Consani's radical construction and the current prolate programme provide near-null tests, not the simultaneous arithmetic repair and pointwise majorization above. No such conclusion is imported from that literature.
- **Verdict: SURVIVES PRELIMINARY ATTACK, OPEN.** No counterexample or proof has been found. The surrounding support reduction is a **BRIDGE**, already dominated by the corpus carrier theorem.
- **[OPEN CORE]** Construct c with `S_c≥1` on a fixed off-zero compact set while simultaneously forcing the actual-copy zeta remainder R(c) and the complete weighted arithmetic repair budget B(c) to zero. This is the next proof obligation; neither a new receiver nor another coefficient lower bound pays it.

If this conjecture fails, the useful survivor must identify the positive lower repair cost or a replacement family with a sharper cost. A failed construction alone will not be labelled a counterexample to the conjecture.

### C0: positive mixtures of translated truncated kernels — FALSE

The first proposed subfamily consists of `f_i(u)=truncatedRiemannKernel L_i (u−y_i)`, with arbitrary finitely many translations y_i, positive weights w_i, and all `L_i≥log 2+1`. Allowing different cutoffs makes the obstruction uniform over more than a single translated profile.

**Positive survivor (complete paper proof).** There is δ>0, independent of the number of tests, all cutoffs, translations, weights and the real spectral point r, such that

`δ Σ_i w_i |paperFT f_i(r)|² ≤ Σ_i w_i logValue f_i 2`.

Proof. Put `M=∫|Φ|`, finite by `integrable_riemannPhiKernel`. Since `0≤χ_L≤1`, the L¹ norm of every truncated kernel is at most M. At a real frequency, translation changes its Fourier transform by a character of norm one, so every squared transform is at most M².

The corpus theorem `exists_weilTest_truncatedRiemannKernel_ge` at `c=log 2` supplies κ>0 such that the real autocorrelation at log 2 is at least κ for every `L≥log 2+1`. Its value at −log 2 is nonnegative. Translation preserves autocorrelation exactly, by the substitution v=u−y. Thus `logValue f_i 2≥a:=κ/√2>0`.

Choose `δ=a/(M²+1)>0`. Then `δ |paperFT f_i(r)|²≤δ M²≤a≤logValue f_i 2`. Multiply by the nonnegative w_i and sum. This proves the displayed assertion for every finite mixture, including mixtures with distinct cutoffs. In particular, normalization of the spectral density to at least one at even one real point forces its n=2 arithmetic defect to be at least δ. The conjecture's B(c) is then at least Λ(2)δ=(log 2)δ>0. No such family can establish Conjecture C.

The no-go is limited to positive mixing of separately translated kernels. Coherent linear combinations inside a test introduce signed cross-correlations; the argument does not exclude them. The survivor is an exact coercivity law for an explicit source family, not new evidence for RH or for failure of Conjecture C. Classification: elementary corpus consequence; no claim of scientific novelty.

### C0 formal closure

`WeilSpectral.exists_logValue_two_ge_translated_radical_density` now proves the exact uniform coercivity statement. Cutoffs are typed as `{L : ℝ // log 2 + 1 ≤ L}` and weights as nonnegative reals. The finite mixture, translations and spectral frequency are unrestricted. Direct source audit, targeted build and the public theorem's axiom audit all passed. The only axioms are Lean's standard `propext`, `Classical.choice`, `Quot.sound`. The module is umbrella-wired. This closes the positive survivor of C0, not Conjecture C.

### C1: polynomial-cost coherent cancellation on logarithmic translates

**Exact new conjecture, unproved.** For each compact `K⊂ℝ\Z`, there exist real constants `A≥0` and `C>A+3` such that for every sufficiently large integer N there are complex coefficients `a_ij` (`1≤i,j≤N`) with the following properties. Set

`L_N=1+(1/2)log(C log N)`,

`f_i(u)=Σ_(j=1)^N a_ij truncatedRiemannKernel L_N (u−log j)`.

Require all three:

1. `Σ_i Σ_j |a_ij|²≤N^A`;
2. `Σ_i logValue f_i n=0` for **every** integer n≥2;
3. `Σ_i |paperFT f_i(r)|²≥1` for every r∈K.

All tests are actual compact C² functions. The arithmetic constraints are finite without an assumed cutoff: their autocorrelations vanish outside `|u|≤2L_N+log N`, hence only integers `n≤exp(2) C N log N` can contribute. The constant C is part of the conjectured construction, and its strict relation to A is essential.

**Why this is stronger than a dimension count or another receiver.** Diagonal coefficient covariances are excluded by the just-proved C0 obstruction. The new assertion asks for cross-correlations that cancel *all* active logarithmic values, with a polynomial coefficient bound on a prescribed logarithmic grid and a prescribed slowly growing kernel cutoff. Counting N² covariance entries against O(N log N) samples proves neither positivity nor the bound. Arbitrary positive repair is already available in the corpus; its energy cost need not tend to zero and does not prove this statement.

**Conditional consequence, not a proof of C1.** Write `EΦ(L)=(5/4) zetaInvSqSum truncatedRiemannTailEnergy(L)²`. The existing actual-copy tail estimate, applied termwise to the Fourier transform of each coherent sum, gives

`Σ_i |Wζ(f_i,f_i)| ≤ EΦ(L_N) Σ_i(Σ_j |a_ij|√j)²`.

Cauchy–Schwarz and `Σ_(j≤N)j≤N²` bound the final factor by `N² Σ_ij|a_ij|²≤N^(A+2)`. The source's fixed-kernel tail comparison gives, for a constant M and all large L, `EΦ(L)≤M exp(−exp(2(L−1)))`. At the prescribed cutoff this is `M N^(−C)`, so the total actual zeta remainder tends to zero. Property 2 makes the full repair cost exactly zero. Property 3 therefore gives C and the already recorded support implication. No step takes critical support, RH, a producer existence theorem, or small deficit as an input.

**Attack / competing outcome.** The central possible failure is that enforcing the many correlated logarithmic constraints inside the positive covariance cone requires coefficient norm larger than every permitted polynomial, or forces the spectral density to vanish on some off-zero compact set. Ordinary interpolation, an unconstrained kernel dimension, and an unweighted approximation theorem do not exclude this failure. A sharp lower bound on this normalization cost would be the positive survivor if C1 fails. The exact shifted-autocorrelation and near-null estimates already exist; reproducing them would be REDISCOVERED.

**Provisional verdict: SURVIVES PRELIMINARY ATTACK; OPEN.** The broad support implication is a BRIDGE; the polynomial-cost construction itself has neither a proof nor a novelty certificate. **[OPEN CORE]** Produce the positive coefficient covariance satisfying 2 and 3 with the quantitative bound 1 and `C>A+3`, or prove a quantitative obstruction. No Lean declaration of C1 is being added before that paper proof exists.

#### First exact attack on C1: the extreme covariance entry must vanish

This is a paper observation, not a new audited Lean result. Let N≥2 and L≥1, and set `Q_jk=Σ_i a_ij conj(a_ik)`. Choose an integer n strictly between `exp(2L)(N−1)` and `exp(2L)N`; the interval has length greater than one. Among ratios j/k with 1≤j,k≤N, the unique largest is N (j=N,k=1), and every other ratio is at most N−1. In the autocorrelation expansion at `x=log n`, all terms therefore vanish by support except

`Q_N1 K_L(log(n/N))`,

where `K_L` is the real autocorrelation of the truncated kernel. The negative-lag value is its complex conjugate. Since `0<log(n/N)<2L`, the overlap interval has positive length and both kernel factors are positive there; thus `K_L(log(n/N))>0`. Here positivity inside the cutoff follows directly from its actual definition `smoothTransition(L−u)smoothTransition(L+u)` and the source's zero-if-and-only-if-nonpositive property.

Consequently all-integer cancellation forces `Re Q_N1=0`. For a symmetric target K, averaging Q with its complex conjugate preserves positivity, trace, cancellation, and spectral majorization, so a real covariance can be used and its extreme entry is zero. This rules out an unconstrained covariance construction. It does **not** kill C1: a positive matrix may have this zero off-diagonal entry. Extending this support peeling through densely spaced rational ratios, with quantitative control of normalization, is a concrete next attack; no such extension is presently proved.
### C1g: coherent cancellation on one geometric grid — FALSE

This restricted attack replaces the shifts `log j` in C1 by `j log b`, where b is any fixed integer at least 2. It does **not** settle C1, whose shifts involve several prime logarithms.

**Exact positive survivor (complete paper proof).** Fix `L≥log b+1` and arbitrary finite complex coefficients `a_ij`. Put `φ=truncatedRiemannKernel L` and `f_i(u)=Σ_j a_ij φ(u−j log b)`, with distinct consecutive nonnegative integer j. Then

`[Σ_i logValue f_i (b^(m+1))=0 for every m≥0] ↔ [all a_ij=0]`.

Proof. Let `κ(k)=truncatedRiemannAutocorr L (k log b)` for integer k. Compact support gives κ(k)=0 when `|k| log b≥2L`. The corpus's uniform positive autocorrelation bound gives κ(1)>0. Thus κ has a largest nonzero index R, and R≥1. Define the finite real coefficient sequence

`C(d)=Σ_i Σ_(j−k=d) Re(conj(a_ik) a_ij)`.

Its constant coefficient is `C(0)=Σ_i Σ_j |a_ij|²`. If a is nonzero, C(0)>0; hence C has a largest nonzero index D≥0. Expanding the actual test autocorrelation, taking real parts, and using its conjugate symmetry gives, for every positive integer m,

`Σ_i logValue f_i (b^m) = (2/√(b^m)) Σ_d C(d) κ(m−d)`.

At `m=R+D`, the sum equals `C(D)κ(R)≠0`: indices d>D have zero C(d), while d<D have `m−d>R` and zero κ(m−d). This contradicts cancellation. Conversely zero coefficients give zero tests and zero logarithmic values.

The exposed invariant is the exact outer-support law `max supp(κ*C)=max supp κ+max supp C`; positivity is used only to ensure C(0)>0. For arbitrary nonzero even finite real sequences, this law and its reflected version also classify constant convolutions: the product is supported only at zero exactly when both factors are. Here κ(1)>0 excludes that case. The survivor is an exact classification for the actual truncated-kernel family, not merely a negative result.

**Novelty/attack verdict:** REDISCOVERED parent mechanism / corpus specialization. Finite sampled autocorrelations and their Laurent-polynomial symbols are standard in wavelet/filter theory; the outer-support argument is elementary polynomial algebra. No claim of scientific novelty. The sharper boundary rules out finite coherent mixtures on one geometric grid at every coefficient size, but supplies no uniform lower cost as the degree grows and leaves full C1 OPEN. Formalization of the displayed actual-kernel equivalence is next; no Lean result is claimed yet.
### C2: centered short-block coherent cancellation — OPEN

Fresh corpus search found the general real-coefficient estimate `WeilExcess.norm_W_shiftComb_le`. It makes the next construction more precise and removes an artificial loss from large common translations. C2 is a new candidate construction for C, not a claimed theorem or a retirement of C1.

**Exact conjecture.** For every compact `K⊂ℝ\Z`, there are constants `A≥0` and `C>A+1` such that, for every sufficiently large integer N, there are real coefficients `a_ij` with `1≤i≤N` and `j∈J_N:={ceil(N/2),…,N}` satisfying the following. Put

`L_N=1+(1/2)log(C log N)`, `x_j=log(j/N)`,

`f_i(u)=Σ_(j∈J_N) a_ij truncatedRiemannKernel L_N (u−x_j)`.

Require (i) `Σ_ij a_ij²≤N^A`; (ii) `Σ_i logValue f_i n=0` for every integer `2≤n<2e²C log N`; and (iii) `Σ_i |paperFT f_i(r)|²≥1` for every r∈K. Real coefficients suffice for this proposed construction; no assertion that every complex construction can be replaced this way is needed.

**Complete support and energy reduction.** For N≥2 the shifts lie in `[−log 2,0]`. Each f_i is C² and supported in `[−L_N−log 2,L_N]`; its autocorrelation vanishes at `|y|≥2L_N+log 2`. Indeed, when the two support intervals have disjoint interiors, the integrand is zero except possibly at one endpoint, a null set. Thus all integer n≥`2e^(2L_N)=2e²C log N` have zero logarithmic value automatically. The conjecture has only O(log N) potentially nonzero integer constraints, unlike the loose O(N log N) support bound for C1.

Write `EΦ(L)=(5/4) zetaInvSqSum truncatedRiemannTailEnergy(L)²`. The corpus's shift-combination estimate gives

`Σ_i |Re Wζ(f_i,f_i)| ≤ EΦ(L_N) Σ_i (Σ_j |a_ij| exp(|x_j|/2))²`
`≤ 2 EΦ(L_N) |J_N| Σ_ij a_ij² ≤ 2M N^(A+1−C) → 0`.

Here `exp(|x_j|/2)≤√2`, finite Cauchy–Schwarz proves the middle inequality, and the already proved source tail estimate gives `EΦ(L_N)≤M N^(−C)`. The fixed smooth-cutoff derivative bound is an existing property, not a new scientific premise. Common translation changes real Fourier transforms only by a unit character and preserves the complete autocorrelation, so centering does not alter arithmetic cancellation, spectral density, or Wζ. Hence C2 implies C with B=0.

**Attack verdict: SURVIVES PRELIMINARY ATTACK; OPEN.** The one-geometric-grid theorem does not apply to this dense grid of rational ratios. Outer support peeling only singles out a covariance term when an integer sample lies between its endpoint and the next endpoint; it gives no such separation for the many close ratios in J_N. Conversely, having O(log N) constraints and many covariance variables does not establish a positive matrix or a polynomial normalization bound. Generic approximation without its coefficient cost is insufficient. **[OPEN CORE]** Construct the positive covariance satisfying (ii)–(iii) within (i), or prove a lower normalization cost that rules it out. No scientific novelty claim; no C2 Lean declaration until a complete construction or exact positive obstruction is proved.
### C1g positive invariant made explicit

The no-go closure audit requires more than `all samples zero iff all coefficients zero`. The positive survivor is therefore exposed as an exact support-and-coefficient theorem for the actual autocorrelation, not left as an unnamed step of the impossibility proof.

For every real spacing c>0, cutoff L≥c+1, and nonzero finite complex coefficient family a, define κ and C as above with c in place of log b, and let `V(m)=Σ_i Re autocorr(f_i)(mc)`. There exist integers R≥1 and D≥0 such that κ(R)≠0, C(D)≠0, κ(k)=0 for k>R, C(d)=0 for d>D,

`V(R+D)=C(D)κ(R)` and `V(m)=0 for every m>R+D`.

**[PROVED HERE]** The complete proof is the same finite-support argument already given: uniform positive kernel correlation at c yields R≥1; the positive trace C(0) yields D≥0; expansion gives V=κ*C. The term d=D is the sole survivor at R+D, and every term vanishes beyond it. This proves an exact additive support law and an explicit nonzero coefficient, not a restated negation. Arbitrary positive real c is the natural domain of this strengthened statement; the integer-power no-go is its specialization c=log b. Novelty audit remains REDISCOVERED parent Laurent-polynomial algebra / actual-kernel specialization, with no new scientific novelty claimed. Final strengthened Lean audit is pending.
### C1g final formal closure

The strengthened actual-kernel outer-support invariant and the integer-power rigidity specialization both pass final direct source audit, targeted build, and public axiom audit. Files: `WeilWorkDeficitGeometricRadicalObstruction.lean`; logs `/tmp/wp06-geometric-strong-first.log`, `/tmp/wp06-geometric-strong-build.log`, `/tmp/wp06-geometric-strong-axioms.log`. Source audit has no diagnostics; build exited 0; both axiom lists contain only Lean's standard foundations. The module is umbrella-wired. The closed restricted-route card records both this positive invariant and C0's uniform coercivity law. This completes C1g's no-go closure; C, C1, C2 and the main target remain OPEN.

### C10u: a uniform factorial budget for growing derivative order

**Verdict: BRIDGE.** This explicit all-order majorant for the actual kernel is not C10's positive cancellation construction and carries no scientific-novelty claim. The existing differential-width result fixes derivative orders before choosing its constant; here two constants serve all orders.

For every `0<a<π`, there is `B>0` and the explicit `C=3+4π/(π−a)>0` such that, for all natural k and real u,

`‖Φ^(k)(u)‖ ≤ B C^k (k+2)! exp(−a exp(2|u|)) exp(−|u|)`.

For every finite complex derivative packet `f=Σ_j c_j Φ^(k_j)`, put `V_C(f)=Σ_j |c_j| C^(k_j)(k_j+2)!`. Every correlation is integrable, with

`|∫ f(u) conjugate(f(u−y)) du| ≤ 2 B² V_C(f)² exp(−2a exp(|y|))`.

With the actual weight `w(n)=Λ(n)+atomCost(n)`, for every `0<r<2π` there is `B_r>0` and the explicit `C_r=3+16π/(2π−r)>0` such that, uniformly in every packet and N≥0,

`Σ_(n≥N+2) w(n)|∫ f(u) conjugate(f(u−log n)) du| ≤ B_r V_(C_r)(f)² exp(−r(N+2))`.

**Dependency-closed paper proof.** Write `P_k=cuspDeriv^[k](4π²X²−6πX)` and `p_(k,j)` for its j-th coefficient. Audited cusp identities give `Φ^(k)=Σ_(n≥1) exp(u/2)P_k(n²exp(2u))exp(−πn²exp(2u))` and `deg P_k≤k+2`. Coefficient extraction gives `p_(k+1,0)=p_(k,0)/2` and, for j≥1,

`p_(k+1,j)=(2j+1/2)p_(k,j)−2π p_(k,j−1)`.

Set `δ=(π−a)/2>0`, `b=π−δ=a+δ>0`, `C=3+2π/δ`. Choose positive A with `|p_(0,j)|j!≤2 A δ^j` for j=0,1,2, e.g. one plus their finite weighted absolute sum. Inductively,

`|p_(k,j)|j! ≤ A C^k(k+2)! δ^j` for all k,j.

For j≥1, the recurrence, triangle inequality and `j!=j(j−1)!` give factor `(2j+1/2)+2πj/δ`, bounded by `C(k+3)` when j≤k+3. When j>k+3 the new coefficient vanishes. The j=0 step has factor1/2, also below `C(k+3)`. This includes every degree-boundary index and has no asymptotic restriction on k. Absolute polynomial evaluation and the nonnegative exponential series imply, for t≥0,

`|P_k(t)| ≤ A C^k(k+2)! Σ_j(δt)^j/j! ≤ A C^k(k+2)! exp(δt)`.

For u≥0 put Y=exp(2u)≥1. The inequality `(n+1)²Y≥Y+n` bounds the ENTIRE cusp sum by

`A C^k(k+2)! exp(u/2) exp(−bY)/(1−exp(−b))`.

Using `δY≤exp(δY)` and `exp(3u/2)≤Y` gives `exp(u/2)exp(−δY)≤δ⁻¹ exp(−u)`. The common envelope follows with `B=A/[δ(1−exp(−b))]`. Audited derivative parity handles u<0.

The finite triangle inequality gives the packet envelope. For every u,y, the triangle inequality and `(exp(|u|)−exp(|u−y|))²≥0` give `2exp(|y|)≤exp(2|u|)+exp(2|u−y|)`. Multiplying the two envelopes and using `exp(−|u−y|)≤1` bounds the full absolute integrand by `B² V_C(f)² exp(−2a exp(|y|))exp(−|u|)`. Continuity gives measurability, and `∫exp(−|u|)=2` proves both integrability and the correlation bound.

Choose `a=(r+2π)/4`, so `r<2a<2π` and `C=3+16π/(2π−r)`. No optimality is claimed for this choice. The audited actual repair estimate and `Λ(n)≤log n` give `w(n)≤D(n+1)sqrt(n)` for n≥2. Set s=2a−r>0. Since `(n+1)sqrt(n)≤2n²` and `n²exp(−sn)≤2/s²` by the quadratic exponential-series term, each weighted correlation is at most `8DB² V_C(f)² exp(−rn)/s²`. Sum the complete geometric tail, adding factor `(1−exp(−r))⁻¹`. No integer, pole term or atomCost is discarded.

**Construction implication and limit.** A baseline-containing family cancelling n=2..M and having summed squared factorial budgets below rate r<2π would have exponentially vanishing full repair tails. Producing that positive family is still [OPEN CORE]. No uniform derivative sign, leading-term approximation, C10 solution or RH consequence follows from this upper majorant.

### C11: can the actual diagonal derivative cone cancel a whole prime prefix?

Given the exact internal and current external frontier, the next structural conjecture is deliberately more rigid than arbitrary polynomial-square synthesis. Define the REAL full correlations

`A(n,k)=∫_(u∈ℝ) Re(Φ^(k)(u)) Re(Φ^(k)(u−log n)) du`.

The new all-order bound pays integrability for every entry. **C11:** for every integer M≥2, there are real `d_0,…,d_M≥0`, with `d_0=1`, such that

`Σ_(k=0)^M d_k A(n,k)=0` for every integer `2≤n≤M`.

This would construct exact prefix cancellation in a much smaller cone: the family consists only of the separate packets `sqrt(d_k) Φ^(k)`, retaining Φ itself. It is not the diagonal-translate family already ruled out by C0; actual derivatives have different, potentially signed correlations. C11 makes no assertion that arbitrary negative moment vectors are representable. It targets precisely the negative baseline vector. Its truth would exhibit a specific finite-dimensional positivity law of the actual Xi-weighted cosine moments, not merely qualitative density with an unspecified degree.

**Competing falsifier:** there is a finite M≥2 and real `α_2,…,α_M` such that `Σ_n α_n A(n,0)>0` while `Σ_n α_n A(n,k)≥0` for every `1≤k≤M`. Such an explicit functional would obstruct this diagonal degree-M cone. It would not obstruct coherent cross terms, larger degree, C7 or C9. Finite-dimensional cone separation is classical; finding and proving the actual functional or actual positive family is the research obligation.

**Attack / verdict: SURVIVES PRELIMINARY ATTACK, OPEN.** Dimension counting gives neither positivity nor a baseline coefficient. The existing polar derivative tail-sign theorem fixes k before its threshold and concerns a related polar source, so it does not certify signs of all these entries. The formal C10u upper bound controls magnitudes, not minors or signs. Touchard limiting-zero theory does not transfer to the complete theta autocorrelation matrix. The current total-positivity literature imposes total positivity before deducing collocation invertibility; no such property of this matrix has been established here. We therefore do not assume a Chebyshev system, invertible positive matrix, or positivity-preserving interpolation.

**[OPEN CORE]** Establish the actual target-specific positive solution or exhibit an exact separating functional. After existence, separately estimate `Σ_k d_k C^(2k)((k+2)!)²` against the C10u decay rate, or bound the signed full tail more sharply. Finite feasibility alone cannot complete C10 or the spectral-deficit target. Neither C11 nor its negation is encoded as a Lean premise.

**C11q, concrete quantitative competitor.** The explicit C10u rate r=π has factorial base C_r=19. Conjecture that there is a fixed real `0<θ<π` and an unbounded set of M≥2 admitting C11's nonnegative coefficients with

`Σ_(k=0)^M d_k 19^(2k)((k+2)!)² ≤ exp(θM)`.

No unspecified inverse constant occurs in this target. For the singleton packets `sqrt(d_k)Φ^(k)`, their squared budgets sum exactly to the displayed quantity. The finite triangle inequality and C10u at N=M−1 then bound the complete tail of their sum by `B_π exp(−π(M+1)+θM)`, which is ≤exp(−cM) along large horizons for any fixed `0<c<π−θ`. Thus C11q would supply C10's actual tail together with exact prefix cancellation and the retained baseline. The finite positive solution and this budget are both unproved. This cost condition can fail even if qualitative C11 holds. Conversely, failure of C11 at one horizon need not disprove the unbounded-horizon C11q. Failure of either restricted candidate would not retire coherent C10 or translate C7. First investigate the actual finite coefficient matrix rather than infer signs from its fixed-order leading tail.

### C11b: exact divisor–Bessel representation and two polynomial channels

**Status: complete paper bridge; NOT Lean-formalized.** This audits the representation previously recorded only as a working calculation. It supplies neither positive interpolation nor C11q's cost. Its classical parent is the Xi-square/Koshliakov divisor–Bessel representation; no scientific novelty claim.

Write `S_R(u)=Σ_(a≥1) exp(u/2) R(a² exp(2u)) exp(−πa² exp(2u))`, using the actual corpus cusp series, and let `d(ell)` count ordered positive factor pairs of ell. For integer j≥0 and x>0 define

`K_j(x)=∫_0^∞ exp(−x cosh v) cosh(jv) dv`.

Here j is Bessel order. It is NOT the corpus `kMoment j x` for j≥2; `kMoment` uses `(cosh v)^j`. The two coincide for j=0,1 only. For real polynomials R,Q, write their finitely supported coefficients r_j,q_l. Then, for EVERY real y,

`∫_ℝ S_R(u) S_Q(y−u) du = exp(y/2) Σ_(ell≥1) d(ell) Σ_(j,l) r_j q_l (ell exp y)^(j+l) K_|j−l|(2π ell exp y)`.  (B1)

All sums and the integral in (B1) converge absolutely. Proof: in the term indexed by a,b≥1 set `v=2u−y+log(a/b)` and `t=ab exp y`. The two cusp variables are `X=t exp v`, `Z=t exp(−v)`, the two front factors multiply to `exp(y/2)`, and `du=dv/2`. Expand the finite polynomial product. Its (j,l) integral is

`exp(y/2) r_j q_l t^(j+l) (1/2)∫_ℝ exp((j−l)v) exp(−2πt cosh v) dv`.

Reflection v↦−v eliminates the odd sinh part, leaving exactly K_|j−l|. This explains both the normalization and the absence of a residual factor two.

For the interchange, bound the absolute polynomial product by its coefficientwise absolute-value expansion. Each term has integral at most the same expression with `|r_j q_l|`. With `t≥exp y`,

`K_h(2πt) ≤ exp(−πt) K_h(πt) ≤ exp(−πt) K_h(π exp y)`.

The first inequality uses cosh v≥1 and the second monotonicity in the positive argument. Each fixed K_h(π exp y) is finite: cosh(hv)≤exp(hv) and cosh v≥1+v²/2 give an integrable Gaussian majorant after completing the square. Thus the sum of all absolute pair integrals is bounded by a finite linear combination of `Σ_(ell≥1) d(ell) ell^J exp(−π exp(y) ell)`. The elementary bound d(ell)≤ell and polynomial-times-geometric convergence make this finite. Tonelli followed by Fubini justifies summing the products, integrating, and regrouping every pair by ab=ell. This proof does not assume that arbitrary cusp terms are nonnegative.

Apply (B1) with `R=Q=P_0=4π²X²−6πX`. Since `XZ=t²` and `X+Z=2t cosh v`, the product is `16π⁴t⁴−48π³t³ cosh v+36π²t²`. Actual Φ is real and even, so its literal autocorrelation is

`κ(y)=exp(y/2) Σ_(ell≥1)d(ell) [(x⁴+9x²)K_0(x)−6x³K_1(x)]`, `x=2π ell exp y`.  (B2)

This is exactly the earlier proposed formula after replacing x by2πt.

For all derivative orders define real polynomials U_m,V_m by

`U_0=X⁴+9X²`, `V_0=6X³`,

`U_(m+1)=X U_m' + U_m/2 + X V_m`,

`V_(m+1)=X V_m' − V_m/2 + X U_m`.  (B3)

Then

`κ^(m)(y)=exp(y/2) Σ_(ell≥1)d(ell) [U_m(x)K_0(x)−V_m(x)K_1(x)]`.  (B4)

Indeed differentiation under the defining Bessel integral gives `K_0'=-K_1`. Integrating the derivative of `sinh(v) exp(−x cosh v)` gives `K_1'=-K_0−K_1/x`: boundary terms vanish at infinity by the same Gaussian/exponential bound and at0 because sinh0=0. Differentiate one summand, using dx/dy=x, to obtain (B3). On any compact real y interval, every finite derivative is a finite polynomial combination of K_h(2πell exp y), bounded by `C ell^J exp(−c ell)` for fixed C,J,c>0. The bound just proved is uniform there. Consequently every derivative series converges locally uniformly and termwise differentiation proves (B4) inductively. Constants here may depend on m; no growing-order estimate is asserted.

All coefficients of U_m,V_m are nonnegative. More precisely, U_m is supported on even powers≥2, V_m on odd powers≥3. For each coefficient, (B3) reads

`u_(m+1,j)=(j+1/2)u_(m,j)+v_(m,j−1)`,

`v_(m+1,j)=(j−1/2)v_(m,j)+u_(m,j−1)`.

The zero constant coefficient and the stated supports remove the only potentially negative scalar in the second recurrence. Induction proves nonnegativity and supports. Their degrees are at most m+4. At even m=2k the top coefficients are

`u_(2k,2k+4)=1`, `v_(2k,2k+3)=(k+2)(2k+3)`.  (B5)

For completeness, track the pair of top coefficients through two steps. If these coefficients at2k are1 and b, the top V coefficient at2k+1 is1, the top U coefficient at2k+1 is `2k+9/2+b`, and the next top V coefficient is `b+4k+9`. Starting at b=6, induction gives b=(k+2)(2k+3). No lower coefficient can enter these degrees because (B3) raises degree by at most one.

Finally, real derivative parity and integration by parts give the actual C11 matrix:

`A(n,k)=(-1)^k κ^(2k)(log n)`

`= (-1)^k sqrt(n) Σ_(ell≥1)d(ell) [U_(2k)(2πell n)K_0(2πell n)−V_(2k)(2πell n)K_1(2πell n)]`.  (B6)

To justify integration by parts, all Φ derivatives have the already audited double-exponential envelope; each boundary product vanishes and every product of the finitely many derivatives involved is integrable. Differentiating the convolution twice k times and moving k derivatives to its first factor yields `∫ Φ^(k)(u) Φ^(k)(y−u)du`; parity changes its second factor to `(-1)^k Φ^(k)(u−y)`. This proves (B6) with the literal full integral, not a theta truncation.

**Consequence for the attack.** Each of the two sums in (B6) is positive, but their difference has no sign from coefficient positivity alone. Even its two top coefficients already have relative scale `(k+2)(2k+3)/(2πell n)`. Leading-term dominance is therefore not a justified approximation at k comparable to n. No total positivity, determinant sign, or positive inverse follows from (B3). Formalization must include (B1)/(B2) and the complete divisor sum before the recurrence can be presented as a theorem about the actual C11 matrix.

### C12: arithmetic limit of normalized derivative correlations

**Conjecture C12.** For each fixed integer n≥2,

`lim_(k→∞) A(n,k)/A(1,k) = 1/sqrt(n)`.

The denominator is the actual positive squared L² norm of Φ^(k). Its positivity follows because the nonzero top coefficient of P_k makes Φ^(k) nonzero, as already established by corpus linear independence. This is an all-order arithmetic assertion, not the fixed-k large-n asymptotic. A competing conjecture is that some fixed n≥2 has negative normalized correlations for arbitrarily large k. They cannot both hold.

Motivation from the inspected corpus: broad-window twisted second moments of the actual |ζ|² have the coefficient `gcd(a,b)/sqrt(ab)` at log(a/b), including1/sqrt(n). Formula(B2) gives coherent divisor phases at the boundary above log n. Neither statement licenses the conjectured derivative-order limit. The derivative spectral weight is `t^(2k)|XiC(t)|²`; after its Gamma factor it concentrates on a window of width comparable to sqrt(k), whereas the inspected corpus moment theorem uses a window comparable to its height. An August2026 reciprocity theorem explicitly requires widths T^δ, δ>1/2, and distinct odd prime twists; it neither covers this endpoint nor removes its dual moment. No endpoint estimate is imported.

**Verdict: SURVIVES PRELIMINARY ATTACK / OPEN.** It may be a consequence of a sufficiently uniform classical twisted-moment theorem; no novelty certificate is claimed. The internal theta logarithmic-jet oscillation theorem concerns the logarithmic derivative of the theta source, not κ, and cannot decide C12. Natural-boundary singularities of a summand need not persist in an even symmetrization or convolution, so a Pringsheim shortcut also remains unproved. First `[OPEN CORE]`: control the literal Xi-weighted degree-k window and its twisted error at this concentration scale, or prove a direct coefficient asymptotic from the full divisor–Bessel expression. Do not replace it by a new Lean premise.

If C12 holds, for each fixed finite set of n all sufficiently high derivative columns are strictly positive at those rows. Such columns alone cannot cancel the positive baseline. This would locate the needed sign-changing orders but would NOT refute C11/C11q, whose positive solution can retain low orders. C11q and the full coherent alternatives C7/C9/C10 remain the principal construction targets.

#### C11b formal interface and C12 attack obligation

The new `WeilWorkDeficitBesselCorrelation.lean` implements (B1) for every pair of real polynomials and every real shift. Its finite coefficient sums sit outside the full divisor series; finite summation commutes with that absolutely convergent series. The formal real Bessel order is `j-l`; evenness in the order identifies it with `|j-l|`. The index-zero term is present with divisor multiplicity zero. Every positive ordered factor pair is retained. The same argument and the corpus derivative parity give the stronger mixed-order specialization

`∫ Re Φ^(k)(u) Re Φ^(l)(u-y) du = (-1)^l ∫ S_(P_k)(u) S_(P_l)(y-u) du`.

This is already a direct specialization of the paper's arbitrary-polynomial identity, not a new scientific claim. The seven-theorem module also proves the explicit actual-kernel formula (B2). Target build and final unchanged direct audit passed; all seven public axiom audits contain only standard Lean foundations. The two-channel polynomial recurrence (B3)-(B5) remains paper-only; it is not needed to identify the actual all-order matrix via (B1).

C12 remains an unconditional conjecture about the actual normalized matrix, with no new Lean premise. A second possible attack, grounded in (B1)-(B2), is to control the complex boundary above `log n` using the divisor summatory function. At `exp(y)=i n`, the leading large-argument Bessel phase `exp(-2πi N n)` aligns for every integer product index. This motivates the rational arithmetic coefficient but does not establish a high-derivative asymptotic. Pointwise or radial cusp growth alone is insufficient: the Cauchy integral at growing derivative order also requires uniform control away from the cusp and of nearby rational cusps. Neither a boundary-growth claim nor a Tauberian/Darboux conclusion is entered as a proved result. Next research must pay that uniformity, or return to the exact weighted twisted moment, before using C12 to restrict cancellation families.

#### C12a: why a radial divisor-error estimate does not yet close the coefficient limit

Source audit: `CCMFUSuzukiMobiusDivisorAbelProducer.abs_primeFreeDivisorDefect_le` bounds
`log(N!) - D(N) + 2γN` by `24√N`. Together with the corpus Stirling estimates this gives the ordinary real summatory remainder `D(X)-X log X-(2γ-1)X = O(√X)`. This is available input, not a new premise to install in Lean.

Test the direct absolute-value Abel estimate for the leading Laplace series suggested by (B2). For `p=7/2`, `Re z=σ>0`, integration by parts against that remainder gives an error envelope

`O(σ^(-4) + |z| σ^(-5))`

for `Σ d(N)N^p exp(-zN)` after subtracting its logarithmic main integral. The two terms come respectively from differentiating `t^p` and `exp(-zt)`; all endpoint terms vanish. This is only an estimate to test the proposed method. The additional complex-sector Bessel reduction and the actual high-order coefficient asymptotic still require proofs.

On a Cauchy circle of radius `(π/2)(1-1/K)` about the real correlation point, an angular displacement of order `K^(-1/2)` from the aligned upper cusp gives `σ` of order `K^(-1)` and `|z|` of order `K^(-1/2)`. Thus this absolute envelope permits size `K^(9/2)` on an arc of width `K^(-1/2)`, giving a coefficient-error bound of order `K^4`. The expected leading logarithmic cusp contributes order `K^(7/2) log K`. The available bound therefore does not prove a relative error tending to zero. It is an upper-bound deficiency, not evidence that C12 is false.

The concrete missing step is angular cancellation or a uniform arithmetic estimate adapted to the growing-order contour. Merely re-formalizing the real square-root summatory bound cannot supply it. C12 and the alternative exact weighted-moment attack remain open; no full route is retired.
# C12g: square-root Gaussian window attack (2026-10-08, OPEN)

For each fixed integer n≥1 and c>0, put H=c√T. Candidate:

`∫ exp(-((t-T)/H)^2) |ζ(1/2+it)|² exp(-it log n) dt = √π H log T / √n + O_(n,c)(H)`.

Proposed mechanism: freeze the balanced Riemann–Siegel polynomial at
N=floor√(T/(2π)). Its two square terms have the exact Gaussian Fourier
transform; the m=nr diagonal supplies the displayed main term. Integrate
before taking absolute values: the remaining near-diagonal lattice sum
is O(H), since H is comparable to N. For the two functional-equation cross
terms, Taylor-expand the unit-modulus chi phase to quadratic order at T.
The resulting chirped Gaussian localizes mr near T/(2πn) or nT/(2π).
For each r comparable to N, only a bounded Gaussian-weighted number of m
contribute; the total is O(N)=O(H). Crude polynomial bounds already price
the cubic phase remainder at O(H). An O(H) error suffices against H log T;
no power saving is required.

Open audit obligations before accepting this as a proof: a verified sharp
balanced approximate functional equation with uniform O(T^-1/4) error;
freezing the moving cutoff with a Gaussian-integrable error; uniform chi
phase Taylor bounds; the product-lattice estimate including far regions;
and transfer from this Gaussian window to the actual Gamma-weighted Xi
derivative moment. The latter has center T=(2k+7/2)/(π/2), width comparable
to √T, and should yield C12 with error O_n(1/log k), but is not yet proved.
No new Lean source, sign conclusion, or scientific novelty claim.

## C12g revised route: product formula and full reciprocal-gap budget

The sharp-cutoff route above is superseded by the already formalized symmetric
product AFE in `ZetaSquareStirlingAFE.exists_norm_zetaSq_sub_symmetricAFE_le`.
The following arithmetic lemma has a complete paper proof and is selected for
formalization. Write P=rm, lambda=log(m/r)-log n, r,m≥1, n≥1, T≥1, and
q_T(P)=min(1,T/P). A zero reciprocal at lambda=0 means that the diagonal is
excluded. Put Z=Σ_(z∈ℤ) 1/z², with the zero summand interpreted as zero. Then

`Σ_(r,m) P^(-1/2) q_T(P)^2 / lambda² ≤ (48 n² Z + 16 pairZeta) T`. (G1)

Here `pairZeta=Σ_(r,m)(rm)^(-5/4)` is the existing corpus constant. Both
series converge absolutely. Proof: if |lambda|≥1/4, the summand is at most
16 times the existing `pairWeight T`, whose total is at most
pairZeta T^(3/4)≤pairZeta T. If 0<|lambda|<1/4, the corpus near-resonance
bounds give nr/2≤m≤2nr. Therefore P≥r²/2, P^(-1/2)≤2/r, and
max(m,nr)≤2nr. The corpus logarithmic gap inequality yields
`1/lambda²≤4n²r²/(m-nr)²`. The summand is consequently bounded by
`8n² r min(1,2T/r²)^2/(m-nr)²`.
For fixed r the integers m-nr are distinct, so their reciprocal-square
sum is at most Z. For a≥0,
`r min(1,a/r²)≤sqrt(a)` and hence
`r min(1,a/r²)^2≤sqrt(a) min(1,a/r²)`.
The existing one-dimensional bound Σ_r min(1,a/r²)≤3sqrt(a) gives
Σ_r r min(1,a/r²)^2≤3a. Set a=2T. This proves (G1), including
summability by the same nonnegative majorants; no unpriced far tail remains.

The remaining analytical assembly is explicit. Let chi be a fixed smooth
cutoff supported in [1/2,2], equal to one on [3/4,3/2], and
F_P(t)=chi(t/T) exp(-((t-T)/H)^2) V(2πP/t), H=c sqrt(T).
The actual V is a Gaussian upper tail on logarithmic scale, already proved in
`SmoothAFECutoffGaussianTail`. Its first two logarithmic derivatives are a
Gaussian and a linear polynomial times that Gaussian. Thus, for j=0,1,2,
`∫|F_P^(j)(t)|dt ≤ C_c H^(1-j) q_T(P)^2`.
This follows by the product rule, t comparable to T on support, H≤T for large
T, and finite Gaussian moments; multiplying each logarithmic derivative by
x² is bounded for x≥1, while all are bounded for 0<x≤1.
Two integrations by parts and (G1) bound all off-diagonal terms by O_(n,c)(T/H).
Absolute integration before rearrangement follows from the j=0 bound and
the summable pair weight. The AFE remainder contributes O_c(log T).

The two diagonals together are
`2/sqrt(n) ∫ chi(t/T) exp(-((t-T)/H)^2) diagHarm(t/(2πn)) dt`.
The existing `exists_norm_diagHarm_sub_le` gives
`diagHarm(x)=log(x)/2+gamma+O(x^(-1/4))`. Consequently the diagonal is
`sqrt(pi) H log(T)/sqrt(n)+O_(n,c)(H)`.
Removing chi costs an exponentially small quantity, using any polynomial
critical-line zeta bound (available through Euler–Maclaurin).
This closes the paper endpoint moment C12g using established corpus inputs
and the displayed derivative/integration estimates. It is a classical-parent
BRIDGE, with no external novelty claim. Lean status: (G1) is now formalized and fully audited in
`WeilWorkDeficitTwistedGapBudget.lean`; the analytical assembly and transfer to the literal Xi derivative moments
remain unformalized. Do not label C12 or the main deficit goal solved.

## C12 transfer on paper: literal Xi moments, with no extra premise

The following completes the paper transfer once G1 and the preceding
endpoint-moment argument are included in the same proof. It is not a Lean
completion claim. The corpus identity `paperFT_riemannKernelDeriv`, realness
of the kernel derivatives, and Plancherel give exactly

`A(n,k) = (1/(2π)) ∫_ℝ t^(2k) |XiC(t)|² cos(t log n) dt`.

All integrals converge: the actual kernel derivatives are Schwartz, and the
Gamma factor also gives exponential decay. At t>0, the exact Xi/Gamma/zeta
identity and the vertical Gamma-ratio limit give

`|XiC(t)|² = C0 t^(7/2) exp(-a t) |ζ(1/2+it)|² (1+epsilon(t))`,
`a=π/2`, `C0=sqrt(π/2)>0`, `epsilon(t)→0`.

For the Gamma input one needs no recalled Stirling theorem: apply
`gamma_vertical_ratio_norm_rpow_tendsto` at a=δ=1/4, combine with the exact
`norm_Gamma_half_add_I_sq`, then use t/2 as height. The exact Xi identity is
in `ZetaNotchSmoothTest`; its factor is `(t²+1/4)²/4`. Continuity on compact
intervals and this limit give a global constant multiple of the same
exponential-power envelope for t≥1.

Put p=2k+7/2, T=p/a, H=sqrt(2T/a), and B=T^p exp(-aT). On T/2≤t≤2T, with
s=(t-T)/H, Taylor's theorem for log(1+u) on -1/2≤u≤1 gives

`|t^p exp(-at)/B - exp(-s²)| ≤ C T^(-1/2) |s|³ exp(-c s²)`.

Indeed the exponent difference is bounded by C T^(-1/2)|s|³, and both
exponents are at most -c s²; use the integral mean-value formula for exp.
The untwisted endpoint estimate at a slightly larger fixed Gaussian width
then bounds the integrated error, after multiplication by |ζ|², by O(log T).
Outside [T/2,2T], `log(t/T)-t/T+1` is negative by a fixed amount, and is
at most a negative constant times t/T for t≥2T. Polynomial zeta bounds
therefore make those tails exponentially small relative to B; the compact
interval [0,1] contributes O(1/B). These statements also apply to the
Gaussian comparison tail.

The epsilon(t) factor costs o(H log T): its supremum on [T/2,2T] tends to
zero, the untwisted integral there is O(H log T), and its outside tail has
the same global exponential envelope. The twist has modulus at most one,
so every error estimate applies uniformly to a fixed n. Evenness doubles
the positive half-axis. Consequently

`A(n,k) / (C0 B H log T / sqrt(π)) → 1/sqrt(n)`

and its n=1 specialization tends to 1. Dividing proves the original C12
limit `A(n,k)/A(1,k)→1/sqrt(n)`. Only convergence is claimed: the available
Gamma-ratio limit does not by itself price a 1/log(k) error. For each fixed
finite M, all rows 2≤n≤M are consequently strictly positive for all
sufficiently large k. This excludes cancellation by those high-order
columns alone. It does not exclude mixtures retaining lower orders, does
not give a threshold uniform on n comparable to k, and does not solve
C11q or the assigned deficit target. Scientific verdict: classical-parent
BRIDGE; paper status complete subject to normal proof audit; Lean status
open beyond the existing ingredients and the completed G1 formalization.

## C13: a coupled truncated-prime dual window (initial conjecture; paper closure below)

**Conjecture:** there exist k0,M0 such that for all integers M≥M0 and
k≥k0 with 100k≤M,

`Σ_(2≤n≤M) Λ(n) A(n,k)/sqrt(n) ≥ (1/4) log(k+2) A(1,k)`.

Competing statement at proposal: there are arbitrarily large such M,k for
which the displayed inequality fails. The later paper closure below resolves
this alternative; analytical Lean formalization remains open.

Motivation uses inspected corpus inputs, not assumed pointwise signs. The
literal `weilFullFunctional` has pole minus prime plus gamma signs. Its
gamma bracket has the proved lower bound
`log(2+|t|)-(10+log 4)` (`joint_gamma_lower_log`). The actual derivative
transforms annihilate every Xi zero. Thus a full-prime identity, if paid
through the noncompact/truncation limit, should give a positive normalized
gamma contribution of size `(1/2) log k` for large k. C10u bounds the entire
omitted prime tail by the explicit factorial budget times exp(-πM). The
untwisted part of the C12 paper argument gives the required lower bound on
A(1,k); factorial comparison should make that tail uniformly negligible
when 100k≤M. Exact pole normalization, noncompact explicit-formula passage,
uniform factorial comparison, and the final finite cutoff must all be
proved before accepting C13. No additional Lean premise is licensed.

The finitely many orders k<k0 are deliberately retained as exceptions.
Positivity of the gamma bracket at large spectral height does not justify
positivity for those low orders. Even C13 would only constrain a band of
C11's columns, not provide a separating functional on the whole cone.
Next research should attack those exceptions and the complementary coupled
order range, while completing C12's remaining formal analytic obligations.

## C13 paper closure: literal poles, cutoff passage, and uniform omitted tail

This closes the preceding C13 paper conjecture, not its Lean obligation.
Put F_k=Re(Phi^(k)), q_k(y)=integral F_k(u)F_k(u-y)du, and
E_k=q_k(0)=A(1,k). All sums below include every prime power through Lambda.

**Noncompact explicit formula.** Let F_(k,L)=bulkCutoff(L,.) F_k.
The fixed smooth transition has bounded derivatives of every fixed order;
its translates have the same bounds. Superexponential decay of every
F_k derivative implies, for j=0,1,2 and any fixed b>0,

`integral exp(b|u|) |(F_(k,L)-F_k)^(j)(u)| du -> 0`.

Indeed each Leibniz term is supported on |u|>=L-1 and bounded by a fixed
finite sum of the corresponding weighted derivative tails. Derivatives of
F_(k,L) have uniformly bounded weighted L1 norms. Fourier integration by
parts therefore gives uniform strip bounds C_k/(1+|Re z|)^2 for |Im z|<=1/2,
and convergence there with the same denominator and a constant tending to
zero. All actual zero evaluations of F_k vanish. The zero-side
summands for the cutoffs are thus bounded in absolute value by
`epsilon_L^2 m(rho)/(1+|Im rho|)^4`, whose sum is finite by the actual
zero-counting bound. Their full sum tends to zero, including off-line
zeros and multiplicities; no RH input occurs.

For q_(k,L), the complex Fourier convolution identity is justified by
weighted L1 Fubini. It converges at both half poles. On the real line its
Fourier transform is |FT F_(k,L)|^2, bounded by C_k/(1+|t|)^4;
the gamma bracket has at most logarithmic growth, so dominated convergence
pays the archimedean integral. For the prime terms, |bulkCutoff|<=1 and
C10u's product-envelope proof give, uniformly in L,
`|q_(k,L)(log n)| <= C_k exp(-pi n)` for n>=2.
The same bound holds at -log n by autocorrelation evenness. Since
Lambda(n)<=log n, the prime series is dominated by a summable sequence.
Pointwise convergence follows from the integrable product envelope.
Taking L->infinity in the existing compact explicit formula now proves
its exact noncompact version with zero left side.

The actual transform is `FT F_k(z)=(-iz)^k XiC(z)`. Both
XiC(i/2)=xi(0)=1/2 and XiC(-i/2)=xi(1)=1/2. At either half pole the
transform of q_k is the product of the two opposite half-pole values,
namely `(-1)^k/4^(k+1)`. Thus the exact real identity is

`P_k := sum_(n>=2) Lambda(n) A(n,k)/sqrt(n)`
`     = (-1)^k/4^(k+1) + (1/(4pi)) integral t^(2k)|XiC(t)|^2 gammaBracket(t)dt`.

In particular the pole correction is signed for odd k. It cannot be
replaced by a nonnegative square at a complex pole.

**Gamma lower bound.** The untwisted C12 proof gives more than total mass:
with p=2k+7/2, a=pi/2, T=p/a, its normalized nonnegative spectral mass
outside [T/2,2T] and its negative reflection tends to zero exponentially.
This follows from the already displayed Laplace tail bound, the global
polynomial zeta bound, and the lower asymptotic E_k~C B H log T with C>0.
The corpus inequality gammaBracket(t)>=log(2+|t|)-(10+log4) gives

`P_k/E_k >= (1/2)(log(T/2)(1-o(1))-(10+log4)) - 1/(4^(k+1)E_k)`.

Here the logarithm is nonnegative outside the central region, and
E_k grows faster than every fixed exponential by C12. Since T/k->4/pi,
there is k0 such that `P_k >= (3/8)log(k+2) E_k` for all k>=k0.
Only this lower bound is asserted; no unproved gamma upper asymptotic is
used.

**Uniform omitted tail.** C10u at r=pi gives one B>0 independent of k,M:

`sum_(n>M) Lambda(n)|A(n,k)|/sqrt(n)`
`  <= B 19^(2k) ((k+2)!)^2 exp(-pi(M+1))`.

This follows from its stronger actual repair-weight sum by
Lambda(n)/sqrt(n)<=Lambda(n) for n>=2. C12 gives eventually
`E_k >= T^(2k) exp(-(2k+7/2))`, after absorbing its positive
C T^4 log T prefactor. Since pi<4, T>=k. The elementary bound
`(k+2)! <= (k+2)^(k+2) <= (3k)^(k+2)` for k>=1 then implies

`19^(2k)((k+2)!)^2/E_k <= exp(20k)`

for all sufficiently large k: take logarithms, use log19<3, log3<2,
and absorb 4log k and fixed constants into the remaining 8k. This is an
analytic bound, not a numerical experiment. Hence for every M>=100k,
the omitted tail divided by E_k is at most
`B exp(20k-pi(M+1)) <= B exp(-280k)`, using pi>3.
Enlarge k0 so this is <=(1/8)log(k+2). Subtracting the entire omitted
tail proves C13, simultaneously for all M>=100k and k>=k0.
Take M0=100k0. No finite-tail sampling is involved.

Verdict: **BRIDGE**, a consequence of the literal explicit formula,
C12's concentration, and the proved full derivative budget. Paper proof
is dependency-closed together with C12/C12g above; C12/C13 analytical
formalization remains open. It gives neither positivity for k<k0 nor
control of the remaining band M/100<k<=M. Main deficit target and C11q
remain open.

## C14: coupled-order prime truncation (OPEN)

For each fixed alpha>0, conjecture

`P_(floor(alpha k)),k / (E_k log(k+2)) -> 1/2` as k->infinity,

where P_(M,k)=sum_(2<=n<=M) Lambda(n)A(n,k)/sqrt(n).
Competing conjecture: some alpha>0 has a subsequence whose normalized
truncation stays a fixed distance from 1/2. C13 only supplies a lower
bound for alpha>=100. Fixed-n C12 cannot be summed over n growing with k.
The exact product AFE suggests a main diagonal on n comparable with k;
its integrated prime contribution below any fixed positive fraction of k
has the same leading logarithmic mass. The open core is control of the
whole coupled prime-weighted off-diagonal, or a signed tail estimate at
n comparable with k. The current absolute factorial envelope does not
pay this range. No hypothesis is added to any Lean result.

## G2 paper primitive for C12g: uniform two-jet cutoff bounds

Let V be the corpus's actual smoothAFECutoff. In logarithmic coordinates,
its already proved first derivative is `-g(y)/(2sqrt(pi))`, where
`g(y)=exp(-y^2/4)`. Differentiation gives second derivative
`y g(y)/(4sqrt(pi))`. For every y,
`(1+|y|)g(y) <= exp(9) min(1,exp(-2y))`:
use 1+|y|<=exp(|y|), and complete the squares
`-y^2/4+|y|<=1` and `-y^2/4+|y|+2y<=9`.
The actual zeroth derivative has 0<=V<=1 and V(x)<=K x^(-2), so increasing
one constant controls all three logarithmic jets by
`C min(1,x^(-2))` on x>0.
For fixed P>0, differentiation of V(P/t), t>0, gives
`g(log(P/t))/(2sqrt(pi)t)` and
`g(log(P/t)) (log(P/t)/2-1)/(2sqrt(pi)t^2)`.
The same envelope therefore bounds orders j=0,1,2 by
`C t^(-j) min(1,(t/P)^2)`, with one constant preceding P,t.
All inputs are literal cutoff identities and elementary real inequalities;
this pays an analytic dependency of the paper C12g proof, with no new
scientific novelty claim. Formalization follows this proof.

## C13 sharpening and the cost-to-tightness consequence

The constant 100 in the first proof is dispensable. Write
`b=2log(19pi/4)>0`. C12's untwisted asymptotic implies

`log E_k = 2k log k + 2k log(4/pi) - 2k + O(log k)`.

To verify this, substitute T=(2k+7/2)/(pi/2), H=sqrt(2T/(pi/2)) in
`E_k~C0 T^(2k+7/2)e^(-(2k+7/2)) H log T/sqrt(pi)` and use
log(1+7/(4k))=O(1/k), with its first-order expansion in the term
multiplied by 2k. The elementary integral comparison for increasing log x
on each [j,j+1] gives
`log(k!)=k log k-k+O(log k)`; shifting k by 2 preserves this error.
Consequently, for Q_k=19^(2k)((k+2)!)^2,

`log(Q_k/E_k)=b k+O(log k)`.

For any fixed beta>b/pi, choose epsilon>0 with b+epsilon<pi beta.
Then the complete omitted tail divided by E_k is at most
`B exp((b+epsilon)k-pi M)`, for all sufficiently large k and every M>=beta k.
The gamma lower bound therefore proves the same C13 inequality uniformly
on this larger range. In particular beta=2 is admissible: pi>3, pi<4 and
the first seven positive terms of exp(3)'s series give exp(pi)>exp(3)>19>
19pi/4; hence log(19pi/4)<pi. This is a symbolic inequality proof.
No sharpness of b/pi is claimed; b comes from the available base-19 bound.

This range interacts with C11q's cost instead of treating k and M
separately. Suppose, for the purpose of deriving a necessary condition,
C11q provides unbounded M, nonnegative d_(M,k) for 0<=k<=M, d_(M,0)=1,
all n=2,...,M cancellations, and `sum d_(M,k)Q_k<=exp(theta M)` with
0<theta<pi. Choose
`theta/b < alpha < pi/b`.
No alpha<1 restriction is needed: if alpha>=1 the high-order block is
empty, and the remaining argument applies to every k<=M.
For k>=alpha M the preceding logarithmic asymptotic gives, uniformly in k,

`sum_(k>=alpha M) d_(M,k)E_k <= exp(-c M)`

for some c>0 and all sufficiently large M. This is obtained by comparing
E_k/Q_k<=exp(-(b-epsilon)k) with the total Q-budget, choosing
(b-epsilon)alpha>theta. Thus these columns' entire normalized L2 mass
vanishes. Their truncated prime pairings also vanish in absolute value:
Cauchy--Schwarz gives |A(n,k)|<=E_k, while
`sum_(2<=n<=M) Lambda(n)/sqrt(n) <= M log M`.

Choose beta with b/pi<beta<1/alpha. C13 controls every remaining order
k>=k0 and k<=alpha M, giving
`P_(M,k)>=log(k+2)E_k/4`. The finitely many k<k0 have
`|P_(M,k)|<=C E_k` uniformly in M, by their full absolutely convergent
prime series. Every E_k is positive: its nonzero Fourier transform is
(-it)^k XiC(t), with XiC nonzero on an interval about zero.
Summing the exact head cancellations against Lambda(n)/sqrt(n) yields

`sum_(k0<=k<=alpha M) d_(M,k)E_k log(k+2)
 <= 4C sum_(k<k0) d_(M,k)E_k + o(1)`.

Let S_M=sum d_(M,k)E_k>=E_0>0 and w_(M,k)=d_(M,k)E_k/S_M,
extended by zero beyond M. These are probability weights. The displayed
bound plus the exponentially small high-order mass (whose log moment is
at most log(M+2) times that mass) gives one uniform bound on
`sum_k w_(M,k)log(k+2)`. In particular the probabilities are tight on N.
Successive subsequence extraction for each coordinate gives a probability
limit w; the uniform logarithmic bound passes to the limit by finite-sum
monotonicity. Since |A(n,k)/E_k|<=1, tightness pays the passage in every
fixed-n cancellation. Therefore C11q necessarily produces

`w_k>=0, sum_k w_k=1, sum_k w_k log(k+2)<infinity,`
`sum_k w_k A(n,k)/E_k=0 for EVERY integer n>=2`.                 (C15-entry)

This is a paper consequence of C12/C13, not a proved existence result.
Its hypotheses are used only in this route audit; no conditional Lean
replacement for the user's target is proposed. A limit may lose w_0, so
claiming w_0>0 would be an error. The nonzero probability and finite log
moment are retained. This tightness law supplies a concrete test for the
whole C11q family; C13 alone was only a band estimate.

## C15: positive derivative-mixture rigidity (OPEN)

Conjecture: no probability w on N with finite logarithmic moment satisfies
all the C15-entry cancellation equalities. Competing conjecture: such a
probability exists, providing an infinite positive mixture of actual
radical derivative energies with every nontrivial integer correlation
zero. A finite collection of fixed-row signs is insufficient. The open
core is the joint infinite family of arithmetic correlations. Positive
weights cannot be silently interchanged with the signed full prime sum:
finite log moment has not yet been proved to dominate its absolute
prime pairing. Even proving C15 would retire only C11q, requiring its
positive tightness survivor to be audited/formalized; it would not solve
spectral deficit. C12/C13 formal obligations remain independent and open.

## G3 paper primitive: complete moving-cutoff oscillatory window

Choose the literal fixed bump psi(s)=bulkCutoff(1,s), supported in [-1,1].
Its first two derivatives are continuous and compactly supported, so one
B>0 bounds all three. For P,H>0 and T>=2H let
`f(t)=psi((t-T)/H) Re V(P/t)`. Outside [T-H,T+H] all bump jets vanish.
At nonpositive t, f and its first two displayed product-rule derivatives
are locally zero; hence the apparently singular P/t produces no failure
of global C2 regularity. On the support, H<=t<=2T and
`min(1,(t/P)^2)<=4min(1,(T/P)^2)`.
G2 therefore bounds |f| by 4BC min(1,(T/P)^2), and its second derivative
by 16BC/H^2 times that minimum. Both are supported on an interval of
length 2H; their L1 norms are at most 8BCH and 32BC/H times that minimum.
All intermediate derivatives are continuous and compactly supported.
The already formal Fourier derivative identity, applied twice, gives
for every nonzero real lambda

`|integral f(t) exp(i lambda t)dt|
 <= 32BC/(H lambda^2) min(1,(T/P)^2)`.

All constants precede P,T,H,lambda. This controls the actual inverse-Mellin
cutoff throughout the whole positive factor-pair sum; it does not replace
V by a sharp cutoff. Its product-rule/regularity, integral proof and G1 summation are now
formalized in WeilWorkDeficitOscillatoryWindow. The actual AFE assembly
is still outstanding.

G3 full off-diagonal assembly. For p=(r-1,m-1), put a_p=(rm)^(-1/2),
q_p=rm and delta_p=log(m/r)-log n. Define the complex window term to be
zero when delta_p=0 and otherwise a_p times the preceding actual-cutoff
oscillatory integral with P=2*pi*q_p and frequency delta_p. Since 2*pi>=1
and T/q_p>=0, min(1,(T/(2*pi*q_p))^2)<=min(1,T/q_p)^2. Hence its norm is
at most (K/H) times G1's exact twistedGapWeight(T,n,p), including diagonal
terms, whose G1 weight is also zero. G1 supplies a summable majorant over
ALL positive pairs. The complex family is therefore summable and its full
sum has norm at most

    K*(48*n^2*integerGapBudget + 16*pairZeta)*T/H.

This is an unconditional full off-diagonal estimate for the fixed actual
profile, with one K before all integer n>=1, T>=1 and 0<H<=T/2. No finite
pair truncation, asymptotic cutoff replacement, or scientific hypothesis is
used. At H=c*sqrt(T), the error has order sqrt(T), below the anticipated
H*log(T) main term for fixed c,n. Gaussian-window extension, diagonal
asymptotics, literal AFE interchange and Xi moment transfer still have to be
formalized; this estimate alone is not C12g or spectral-deficit closure.


## C16: the absolute prime cost of a derivative energy (OPEN)

With the actual A(n,k), E_k from C12, set

    B_k = E_k^(-1) sum_{n>=2} Lambda(n) |A(n,k)| / sqrt(n).

E_k>0 was justified in the C13 tightness proof; C10u implies finiteness of
every B_k. The exact competing conjectures are:

- C16a: there exists C>0 such that B_k <= C log(k+2) for every k>=0.
- C16b: for every C>0 there exists k>=0 with B_k > C log(k+2).

C13 already gives an eventual logarithmic lower bound, so C16a would
identify the correct order and is not a weakening to a vacuous finite
budget. Its consequence for C15 is precise: finite logarithmic moment
would imply absolute convergence of the entire double prime/derivative
sum by Tonelli, justifying the currently unpaid signed interchange.
This alone would NOT refute C15: low derivative orders can still have
signed prime pairings that balance the positive high-order contribution.
The main target is not encoded in C16a.

Preliminary attacks: (1) C10u's factorial estimate proves each B_k finite
but grows exponentially relative to E_k and gives no logarithmic bound.
(2) G3 is fixed-twist uniform with n^2 dependence; summing that estimate
over growing prime labels does not pay C16. (3) Absolute values retain
reflected/stationary AFE contributions. A possible larger cost from these
terms is a competing mechanism, not a proved log-squared asymptotic or
counterexample. (4) The full divisor--Bessel formula is exact, but its
large-order, large-argument signed polynomial sum has not been bounded.
[OPEN CORE]: control this coupled prime sum, or produce an actual
subsequence violating the logarithmic budget. Verdict for both exact
alternatives: SURVIVES PRELIMINARY ATTACK, not proof or novelty certification.
If C16a fails, extract the sharp larger budget and resulting moment
condition before retiring the route.

C15 boundary-family test remains exploratory. For N>=3, reciprocal Gamma
products with a=N+1/4 suggest positive Taylor coefficients for
1/(Gamma(a+i*t/2) Gamma(a-i*t/2)); the Gamma recurrence cancels the Xi
Gamma weight into a rational weight times |zeta(1/2+it)|^2. DLMF 5.8.3
verifies the product identity, and the corpus supplies unconditional
critical-line growth. A normalized derivative probability, its required
moments, and any failure of exponential regularity have NOT been fully
audited here. No arithmetic cancellation, C15 counterexample, or
prime-Fubini obstruction is claimed from this exploratory family.

## C16 refined attack: exact product kernel, avoiding compact spectral cuts

The attempted direct compact-window summation is not accepted. Integration
by parts yields decay in log n, insufficient against sum Lambda(n)/sqrt n;
the strong decay of the full derivative correlation cannot be inferred
from that truncated spectrum. This kills that proof shortcut, not C16.

The existing C11b Bessel formula provides a more exact route. Put
F_0(x)=((2pi x)^4+9(2pi x)^2)K_0(2pi x)-6(2pi x)^3 K_1(2pi x),
and F_k(x)=(-1)^k (x d/dx+1/2)^(2k) F_0(x). Differentiating the actual
correlation formula, with the full convergence passage still to audit,
suggests A(n,k)=sqrt(n) sum_{N>=1} d(N) F_k(nN). The product dependence
also appears directly in the already audited derivative-polynomial formula.
Consequently the candidate absolute upper budget is

    (1/(2 E_k)) sum_{m>=1} d(m) log(m) |F_k(m)|,

using Lambda*d=d log/2. This exact arithmetic identity is already a
consequence of corpus logDerivation_mul/logDerivation_zeta, and was used
in CCMPrimeDeficitEulerForceEnergy. It is not a new scientific discovery.
The missing step is the uniform high-order kernel budget, not arithmetic
prime density in very short intervals. Existing generalized-divisor short
interval bounds are available at square-root width.

## C17: integer-lattice signed Gaussian profile (CONJECTURE; not proved)

Let a=pi/2, p_k=2k+7/2, T_k=p_k/a, b_k=T_k^p_k exp(-a T_k),
u_k(m)=(2pi m-T_k)/sqrt(T_k). Define the real profile

    J_a(u) = Re [exp(-i pi/4) integral_R
                   exp(-a x^2/2) exp(i(x-u)^2/2) dx].

Equivalent closed expression:

    sqrt(2pi) (a^2+1)^(-1/4) exp(-a u^2/(2(a^2+1)))
      * cos(a^2 u^2/(2(a^2+1))-pi/4+atan(1/a)/2).

Exact local conjecture: for every R>0,

    sup_{m>=1 integer, |u_k(m)|<=R}
       |F_k(m)/b_k - J_a(u_k(m))| -> 0.

The stronger budget conjecture needed for C16 is: there are C>0,k0 and
fixed q>3 such that, for all k>=k0 and every integer m>=1,

    |F_k(m)| <= C b_k (1+|u_k(m)|)^(-q)

plus any explicitly priced residual whose d(m)log(m)-weighted total is
O(b_k sqrt(T_k) log(T_k)^2). The residual is NOT permitted as an unbounded
or assumed error. [OPEN CORE]: prove this whole-kernel bound, including
far m and low-height/pole contributions.

Derivation motivating the conjecture, not yet a proof: the Mellin transform
of F_0 is G(s)=s^2(s-1)^2 pi^(-s) Gamma(s/2)^2/4. Thus its proposed exact
Fourier inversion at s=1/2+it gives F_k(m) as
(2pi sqrt(m))^-1 integral t^(2k) G(1/2+it) exp(-it log m) dt.
For t>0, Stirling gives G~sqrt(pi/2)t^(7/2)exp(-pi t/2)
exp(i[t log(t/(2pi))-t-pi/4]). At t=T_k+x sqrt(T_k) and
m=(T_k+u sqrt(T_k))/(2pi), its phase is -2pi m+(x-u)^2/2-pi/4+o(1).
The integer product makes exp(-2pi i m)=1. The positive and negative
height contributions combine into the real profile above, and the
prefactor tends exactly to b_k. The profile is signed, not an everywhere
positive Gaussian; claiming eventual positivity across the entire
square-root band would discard its quadratic phase. This structure could
explain C12/C13 and pay C16, but uniform errors and tails are still open.
No new Lean claim is based on this conjectural saddle calculation.

## G4 dependency-closed paper lemma: the actual full prime budget

For formalization define K_k(x) directly by C11b's finite signed polynomial
sum: (-1)^k sum_{j,l} c_{k,j}c_{k,l} x^(j+l) K_{j-l}(2pi x), with both
indices through the actual riemannKernelPoly(k) degree. This definition
uses no unproved logarithmic-derivative or Mellin inversion identity.
C11b, finite-sum interchange and exp(log n)=n give exactly
A(n,k)=sqrt(n) sum_{N>=1} d(N)K_k(nN) for n>=1.

For every fixed j,l, positivity of K_{j-l}(2pi N) for N>=1 implies
log(N) times its N^(j+l) monomial is bounded by its (j+1,l+1) monomial:
log N<=N^2 and the Bessel order is unchanged. The N=0 divisor coefficient
is zero. C11b's summable_divisor_bessel at y=0 therefore proves absolute
convergence after multiplying the finite polynomial sum by d(N)log N.

The nonnegative double family Lambda(n)d(N)|K_k(nN)| can now be regrouped
by m=nN. Axis terms vanish. Its finite m-fiber is
|K_k(m)| times (Lambda*d)(m)=d(m)log(m)|K_k(m)|/2. The identity follows
by applying the already proved logarithmic derivation to zeta^2, or by
summing log divisors and pairing complementary divisors. Tonelli first
as an extended nonnegative sum, then finiteness of the preceding weighted
kernel budget, proves summability of the whole pair family. Thus every
actual prime correlation is absolutely summable and

  sum_{n>=2} Lambda(n)|A(n,k)|/sqrt(n)
    <= (1/2) sum_{m>=1} d(m)log(m)|K_k(m)|.

All kernels are actual, all positive factor pairs and all prime powers
are retained, and every interchange is paid. This is the exact bridge to
C16; it does not prove the required logarithmic-in-k estimate. No
scientific hypothesis or new axiom enters. Classical-parent BRIDGE.

## C17 local profile and global envelope: paper proof, 2026-10-08

This section supersedes the conjectural status of C17 above **on paper only**.
No Mellin/Gamma asymptotic below is yet a Lean theorem in this work package.
The actual finite product kernel K_k used in G4 is the object throughout.
The proof uses the classical Mellin transform of Bessel K, Mellin inversion,
Stirling with differentiated remainder, and the elementary divisor estimate.
It is a classical-parent bridge; external novelty is not established.

### Exact Mellin identity, without differentiating an infinite divisor sum

Write P_k=riemannKernelPoly(k) and c_kj for its coefficients. The checked
corpus definition is P_(k+1)=P_k/2+2X P'_k-2pi X P_k, with
P_0=4pi^2 X^2-6pi X. Put B_k(s)=sum_j c_kj pi^(-j) Gamma(s/2+j).
For Re(s)>0, termwise integration of the finite polynomial against
x^(s/2-1) exp(-pi x) is absolute. Integration by parts has zero endpoints
at zero and infinity and gives B_(k+1)(s)=(1/2-s)B_k(s).
The Gamma recurrence gives B_0(s)=s(s-1)Gamma(s/2). Thus

  Mellin(K_k)(s) = (-1)^k pi^(-s) B_k(s)^2/4
    = (-1)^k(s-1/2)^(2k) G(s),
  G(s)=s^2(s-1)^2 pi^(-s) Gamma(s/2)^2/4.

The first equality follows for each (j,l) from the classical formula
Mellin[x^(j+l) K_(j-l)(2pi x)](s)
=pi^(-s-j-l)Gamma(s/2+j)Gamma(s/2+l)/4.
Its condition Re(s)+j+l>|j-l| holds for Re(s)>0. There are only finitely
many terms. K_k is continuous for x>0; its weighted Mellin integral is
absolute on each such vertical line. Stirling makes the transformed
function integrable along that line. Fourier inversion after x=exp(v)
therefore yields, at every x>0 and every fixed sigma>0,

  K_k(x)=x^(-sigma)/(2pi) integral_R
    (-1)^k(sigma-1/2+it)^(2k) G(sigma+it) exp(-it log x) dt.  (M)

No contour crossing or residue is needed: inversion holds separately on
sigma=1/2 and sigma=4. The same boundary-free integrations by parts give
K_k=(-1)^k(D_x+1/2)^(2k)K_0. This identifies the earlier F_k notation
without passing derivatives through an infinite arithmetic sum.

Primary analytic formulas: [DLMF 10.43.19](https://dlmf.nist.gov/10.43#E19),
[DLMF 2.5.2](https://dlmf.nist.gov/2.5#E2), and
[DLMF 5.11](https://dlmf.nist.gov/5.11). Their conditions above are paid.

### Local limit, uniform on each fixed square-root band

Keep a=pi/2, p=2k+7/2, T=p/a, b=T^p exp(-aT), and
u=(2pi m-T)/sqrt(T). On the critical line, the multiplier in (M) is t^(2k).
For t>=1, complex Stirling gives

  G(1/2+it)=sqrt(pi/2)t^(7/2)exp(-at)
    exp(i[t log(t/(2pi))-t-pi/4]) (1+O(1/t)).

The constant is fixed and the remainder is uniform. Negative t contributes
the complex conjugate. Substitute t=T+x sqrt(T). The amplitude divided
by b is exp(aT[log(1+x/sqrt(T))-x/sqrt(T)]), converging to exp(-a x^2/2).
For |x|<=sqrt(T)/2 it is bounded by exp(-c x^2). For x>=sqrt(T)/2 it is
bounded by exp(-c sqrt(T)x). For 1<=t<=T/2 the normalized integral is
O(T^C exp(-cT)); for 0<=t<=1 boundedness of G and t^(2k)<=1 give O(1/b).
These bounds pay the full tails uniformly for |u|<=R, for every fixed R.
On a fixed x interval, Taylor's theorem gives, uniformly for |u|<=R,

  t log(t/(2pi m))-t = -2pi m+(x-u)^2/2+O_(R,L)(T^(-1/2)).

For integer m, exp(-2pi i m)=1. The remaining prefactor
sqrt(pi/2)sqrt(T)/(pi sqrt(m)) tends uniformly to 1. Dominated convergence,
first on |x|<=L and then L->infinity using the displayed tails, proves

  sup_{m>=1 integer, |u|<=R} |K_k(m)/b-J_a(u)| -> 0.

The Gaussian integral evaluates to the signed J_a already displayed.
The quadratic phase is retained. In particular, this does not prove
positivity throughout the square-root band.

### Uniform whole-kernel bound, with all low heights paid

Here is the missing global step. Fix sigma=4 and delta=sigma-1/2=7/2.
Let chi be a fixed smooth real cutoff, zero for t<=1 and one for t>=2.
For t=T+x sqrt(T)>0 define the function, extended by zero elsewhere,

  H_k(x)=chi(t) (-1)^k(delta+it)^(2k)G(sigma+it)
    exp(-it log(T/(2pi))) / (b T^delta).

For each fixed integer q>=0,

  integral_R |d^q H_k(x)/dx^q| dx <= C_q                    (S)

uniformly for all sufficiently large k. The proof of uniformity is as
follows. Stirling in a fixed sector, and Cauchy estimates on disks of
radius a fixed fraction of t, give differentiated remainders
O_q(t^(-1-q)). On T/2<=t<=2T, write the nonzero expression defining H_k
as an exponential. Its absolute value is at most C exp(-c x^2): the main
exponent is aT(log(t/T)-t/T+1), the extra factor (t/T)^delta is bounded,
and (1+delta^2/t^2)^k is bounded. Its first logarithmic x derivative is
bounded by C(1+|x|), since its real leading part is
sqrt(T)[(2k+sigma+3)/t-a] and its imaginary leading part is
sqrt(T)log(t/T). The multiplier's remaining imaginary derivative is
O(k sqrt(T)/t^2); all omitted terms are bounded on this interval. Each
logarithmic x derivative of order r>=2 is uniformly bounded: its terms
are O_r(T^(r/2)k/t^r)+O_r(T^(r/2)t^(1-r)), hence O_r(1) there.
Repeated differentiation now bounds the q-th derivative by
C_q(1+|x|)^q exp(-c x^2), which has a fixed finite integral.

On 1<=t<=T/2, the modulus of (delta+it)^(2k)exp(-at), normalized at T,
is exponentially small in T. For large k its logarithmic derivative
2kt/(t^2+delta^2)-a is positive throughout this interval; its maximum is
at T/2, where log of the ratio is
-aT(log 2-1/2)+O(log T). Differentiation of any fixed order adds at most
a polynomial in T and log T, since t>=1. Integration over an interval
of length T therefore still tends exponentially to zero. The fixed chi
transition has the same bound. For t>=2T the logarithmic modulus derivative
is at most -a/2; the value at 2T is exp(-cT) times a polynomial in T.
Polynomial and logarithmic factors produced by differentiation remain
integrable against exp(-a(t-2T)/2). This proves (S), including both tails.
All derivatives vanish at the lower endpoint and decay at infinity.

Integrating by parts twelve times in the Fourier integral, and also using
q=0 in (S), bounds the positive-height contribution to (M) by

  C b (T/m)^4 (1+sqrt(T)|log(2pi m/T)|)^(-12).               (H)

The negative-height contribution has the same bound by conjugation.
The remaining compact heights |t|<=2 cost at most D_k m^(-4), where
D_k=C_0 C_1^(2k) with fixed constants. Since b grows faster than every
fixed exponential times a power of T, D_k<=b/T^2 eventually.

If 2pi m/T is between 1/2 and 2, the logarithm in (H) is comparable to
(2pi m-T)/T, so (H) is bounded by C b(1+|u|)^(-4). If 2pi m/T<=1/2,
then m>=1 and (H)<=C b T^4 T^(-6)<=C b T^(-2), while |u| is comparable
to sqrt(T). If 2pi m/T>=2, (H)<=C b T^(-2)m^(-4), smaller than the
required C b T^2 m^(-4). Finally
(1+|u|)^4<=C T^2 m^4 for T,m>=1, so the compact-height remainder obeys
the same envelope. This proves, with no residual left unpriced,

  |K_k(m)| <= C b (1+|(2pi m-T)/sqrt(T)|)^(-4)              (G)

for every integer m>=1 and all sufficiently large k. No prime cutoff,
negative contour shift, omitted pole, or factorial-in-k constant remains.

### Arithmetic consequences: C12 and C16 on paper

The elementary hyperbola bound, already in the corpus, gives
sum_{X<m<=X+L}d(m)<=C(L log(X+L+2)+sqrt(X+L)) for X,L>=0.
Apply this on the square-root central interval and dyadic distance annuli.
Inside m=O(T), an annulus of width 2^j sqrt(T) costs at most
C 2^j sqrt(T)log(T+2); multiply by its (1+2^j)^(-4) envelope and sum.
For farther m, sum_{m<=Y}d(m)<=C Y log(Y+2) and the fourth-power envelope
pay all annuli. The same argument with log(m) gives

  sum_m d(m)log(m)|K_k(m)| <= C b sqrt(T)log(T+2)^2.        (B)

It also gives uniform tightness of the divisor-weighted fourth-power
profile without the extra logarithm. For fixed real v<w,
D(X)=X log X+(2gamma-1)X+O(sqrt X), at the two endpoints
(T+v sqrt(T))/(2pi) and (T+w sqrt(T))/(2pi), implies

  [sum_{v<u_k(m)<=w}d(m)]/[sqrt(T)log T] -> (w-v)/(2pi).

Thus the local limit and (G), using the preceding annular tightness,
yield E_k=sum_m d(m)K_k(m)~b sqrt(T)log(T)/sqrt(a), because
integral_R J_a(u)du=2pi/sqrt(a). The last integral follows from its
explicit complex Gaussian formula (positive real quadratic coefficient),
so no nonabsolute Fresnel interchange is used.
For fixed integer n>=1, repeat the interval estimate for d(N) on the
lattice m=nN. The limiting measure has density 1/(2pi n), and the same
annular domination applies. G4's exact sqrt(n) factor gives
A(n,k)/E_k->1/sqrt(n). This is a second paper proof of C12 that uses the
actual product kernel directly and does not require an AFE assembly.

Combine (B), the positive asymptotic for E_k, and G4's complete prime
budget to obtain C16a: B_k<=C log(k+2) for all sufficiently large k.
Finitely many remaining k are absorbed using their already proved finite
prime budgets and strictly positive derivative energies. C16b is thereby
refuted on paper. Neither conclusion is yet formalized beyond G4.

This pays absolute prime/derivative interchange for a C15 probability with
finite logarithmic moment. It does NOT refute C15: low-order signed prime
pairings can still cancel its high-order positive terms. Next conjecture
must test that actual signed mixture, while formal work verifies the
Mellin identity and the uniform differentiated estimate (S).

## C14 paper closure from C17; next competing cutoff conjectures

Fix alpha>0 and M>=alpha k. For large k, M>=c_alpha T. The absolute
omitted-prime budget is, by G4's rowwise proof, at most
sum_{n>M,N>=1} Lambda(n)d(N)|K_k(nN)|. Choose a fixed integer
N_0>1/(pi c_alpha). For N<=N_0, use Lambda(n)<=log(n) and (G).
The sum over n>M is at most C_N b sqrt(T)log(T+2): the central lattice
has spacing 2pi N/sqrt(T), and dyadic distance annuli pay all its tails.
There are only finitely many such N and their divisor weights are fixed.
For N>N_0 and n>M one has nN>T/pi. Thus (G) is bounded by
C b T^2/(nN)^4. These remaining terms total at most

  C b T^2 [sum_{n>M}log(n)/n^4] [sum_{N>N_0}d(N)/N^4]
    <= C_alpha b log(T+2)/T.

The last divisor series converges absolutely. Consequently the entire
omitted prime budget is O_alpha(b sqrt(T)log T)=O_alpha(E_k).
The exact C13 signed prime identity and its Gamma concentration give
P_infinity,k/(E_k log k)->1/2; its signed half-pole term is negligible.
Subtracting the fully priced omitted tail proves C14:

  P_floor(alpha k),k/(E_k log k) -> 1/2, for every alpha>0.

This is paper-only and depends on the now paper-proved C17 envelope;
it makes no short-interval prime-density assumption. It strengthens the
previous beta-threshold lower bound, but does not solve C15 or WP06.

New C18a (conjecture, not proved): for every fixed 0<beta<1,

  P_floor(k^beta),k/(E_k log k) -> beta-beta^2/2.

Competing C18b: for some 0<beta<1 this limit fails or differs from that
quadratic. The candidate comes from the exact truncated convolution
sum_{n|m,n<=M}Lambda(n)d(m/n), whose expected local mean is
log(M)log(T)-(log M)^2/2. It is not obtained by assuming a uniform C12.
The elementary divisor summatory remainder, applied separately to each
growing n, is too large; a local arithmetic cancellation estimate at the
actual signed profile is required. This is the next falsification target.
In parallel, the central construction/no-go question remains C15's actual
positive derivative mixture, now with absolute prime Fubini paid on paper.

## C19 arithmetic survivor: finite Euler deletion gives a literal kernel spike

The following paper reduction uses C16's logarithmic budget and is not
claimed as a new scientific theorem. It avoids assuming an unjustified
infinite Möbius interchange. For a candidate C15 probability w, put
f(m)=sum_k (w_k/E_k)K_k(m), m>=1. G4 and C17 imply
sum_m d(m)log(m)|f(m)|<infinity on m>=2. The m=1 series also converges:
C17's global envelope bounds |K_k(1)|/E_k for all sufficiently large k,
and finitely many remaining ratios are finite. Thus sum_m d(m)|f(m)|
is finite. Every row interchange is absolute and
C(n):=sum_N d(N)f(nN)=0 for n>=2, while C(1)=1.

For a finite set P of primes apply product_{p in P}(1-D_p)^2 to C,
where D_p C(n)=C(pn). This is a FINITE linear combination of convergent
rows. Expanding and regrouping the finite terms gives exactly

  product_{p in P}(1-D_p)^2 C(n)
    = sum_{m>=1, no p in P divides m} d(m) f(nm).

At a prime-power exponent e>=1 the coefficient cancels because
(e+1)-2e+(e-1)=0 (the e=1 last term is zero); exponent0 retains1.
Multiplicativity of d supplies the other prime factors. No infinite
inverse series is used. For n>=2 the left side is zero. Exhaust P by
all primes<=B. Every m>1 eventually disappears; the majorant
d(m)|f(nm)| is summable because d(m)<=d(nm). Dominated convergence
therefore proves f(n)=0 for all n>=2. For n=1 the left side is C(1)=1,
since all nonidentity shifts evaluate C at integers>=2; the same limit
proves f(1)=1.

Conversely, these spike values and absolute row interchange immediately
give all C15 cancellations and normalization. Hence within the exact C15
probability/finite-log-moment class, arithmetic cancellation is equivalent
to the literal product-kernel cardinal condition

  sum_k (w_k/E_k)K_k(m) = if m=1 then 1 else 0, every integer m>=1.

This is a BRIDGE, not a no-go or construction. The corpus already has
finite rough-factor inversion (PMPowerDampedMobiusRoughInverse), and the
finite Euler mechanism is classical. The exact scientific question now
has a second representation: can a positive mixture of these actual
Mellin derivative kernels interpolate this cardinal spike? Both existence
and nonexistence remain open. No analyticity of the mixture is assumed:
finite logarithmic moment does not give exponential coefficient decay.

### G5 exact Mellin bridge: dependency-closed assembly, 2026-10-08

For Re(s)>0 and polynomial P, set L_s(P)=sum_j c_j pi^(-j)
Gamma(s/2+j). This is a finite real-linear sum. The recurrence
cuspDeriv(P)=P/2+2XP'-2pi XP and Gamma(z+1)=z Gamma(z), with
Re(s/2+j)>0, give L_s(cuspDeriv P)=(1/2-s)L_s(P).
The actual initial polynomial has L_s(P_0)=s(s-1)Gamma(s/2).
Consequently L_s(P_k)=(1/2-s)^k s(s-1)Gamma(s/2).

For the individual Bessel monomial x^(j+l)K_(j-l)(2pi x), the Mellin
integral is absolutely convergent on Re(s)>0: its shifted chamber is
Re(s+j+l)>|j-l|. The defining full-line exponential integral for K,
Tonelli for its norm, the gamma integral, and the already-proved
hyperbolic beta integral establish

 integral_0^infinity x^(s+j+l-1)K_(j-l)(2pi x) dx
 = pi^(-s)/4 [pi^(-j)Gamma(s/2+j)] [pi^(-l)Gamma(s/2+l)].

Indeed the absolute inner gamma integral is bounded by
Gamma(Re(s+j+l)) times the integrable hyperbolic beta weight with
order Re(j-l). Hence the complex Fubini interchange is justified,
not merely a formal Mellin manipulation. Scaling by positive 2pi
uses the positive-real branch of complex powers. Finite summation
preserves absolute integrability. The double polynomial sum factors
as L_s(P_k)^2, so the exact actual kernel satisfies

 integral_0^infinity x^(s-1)K_k(x) dx
 = (-1)^k (s-1/2)^(2k) s^2(s-1)^2 pi^(-s) Gamma(s/2)^2 /4.

All coefficients and finite ranges are those of riemannKernelPoly;
no surrogate kernel or convergence hypothesis is introduced. G5 is
a classical Mellin bridge supporting C17, not a new high-order bound.

### G6 uniform actual Mellin amplitude: paper proof before Lean (2026-10-08)

Let a=pi/2, delta=7/2, N=2k+7, T=N/a and B=T^N exp(-aT).
This sigma4 amplitude saddle differs from C17's critical-line T by the
fixed amount7/pi; the two normalizations are comparable and must be
explicitly compared when assembling C17. Write M_k(s) for G5's exact
Mellin transform. Gamma reflection and recurrence give, for t>0,

 |M_k(4+it)|=(t^2+49/4)^k t(t^2+4)(t^2+9)(t^2+16)
                  /(32 pi^3 sinh(at)).

This follows from |Gamma(1+iy)|^2=pi*y/sinh(pi*y), applied at y=t/2,
and Gamma(2+iy)=(1+iy)Gamma(1+iy). The scalar pi^(-s) has norm pi^-4.
No Stirling remainder is needed for this amplitude identity.

On T/2<=t<=2T, T>=2 and t>=1. Since 2k<=aT and t>=T/2,
k/t^2<=2a. Hence

 (t^2+49/4)^k <= t^(2k) exp(49pi/4).

For u>=1, sinh(u)>=exp(u)/4: use exp(2u)>=1+2u>=3 in
sinh(u)=exp(u)(1-exp(-2u))/2. Each of the three polynomial factors is
bounded respectively by5t^2,10t^2,17t^2. Thus

 |M_k(4+it)| <= C t^N exp(-at),
 C=850 exp(49pi/4)/(8pi^3), independent of k.

For 0<r<=2, log r<=r-1-(r-1)^2/9. Indeed log r=2log(sqrt r)
<=2(sqrt r-1), while (sqrt r+1)^2<=9 gives
(r-1)^2<=9(sqrt r-1)^2. Put r=t/T and N=aT. Then

 t^N exp(-at)/B <= exp(-a(t-T)^2/(9T)).

Therefore the actual Mellin amplitude has a common Gaussian bulk bound
C B exp(-pi(t-T)^2/(18T)) at EVERY derivative order. This proves the
zeroth-order core of C17's envelope; global tails and differentiated
bounds are separate obligations, not new hypotheses. Verdict BRIDGE:
classical Gamma reflection plus a Laplace bound, no scientific novelty
claim. It is a uniform growing-order theorem for the literal kernel,
not another deficit receiver. Exact norm and this bound will be
formalized together before a completed-module claim.

### C20 competing sharp absolute-prime laws (OPEN, 2026-10-08)

Given the exact internal frontier, conjecture beyond the present O(log k)
budget: with J_a from C17, a=pi/2, set
R_a=(integral_R |J_a(u)|du)/(integral_R J_a(u)du)>1. For the actual
full absolute prime budget B_k=sum_{n>=2}Lambda(n)|A(n,k)|/(sqrt(n)E_k),

 C20a: B_k/log k -> 3/8 + R_a/8.
 C20b: this limit fails or differs from that constant.

These are incompatible exact statements; neither is a Lean premise.
The proposed mechanism is arithmetic, not positivity of J_a. At prime
scale n=T^beta below beta=1/2, each n-row sees many N-lattice points
inside width sqrt(T), so the signed profile should average before
absolute value. Above beta=1/2, a row sees separated N contributions,
so absolute value should retain the signed-profile variation R_a.
C18's candidate logarithmic density is (1-beta)d beta; its masses on
(0,1/2) and (1/2,1) are3/8 and1/8. The transition window and n>T must
be shown lower order. None of these uniform assertions follows from
fixed-n C12. R_a>1 follows from C17's nonzero negative Gaussian lobes.

[OPEN CORE]: joint prime/divisor statistics against the actual signed
sqrt(T)-window, uniformly in the two ranges, and control of the
absolute value before/after row summation. This would identify a sharp
cost of arithmetic resolution inside the positive derivative cone.
Failure would locate arithmetic structure not captured by its current
Gaussian profile. A proof would strengthen C16 but would NOT by itself
construct C15 or prove vanishing deficit. Verdict after exact parent
search: SURVIVES PRELIMINARY ATTACK. No novelty certification or
pointwise asymptotic theorem is claimed.

### C20c: averaged sharp cost — paper assembly (2026-10-08)

Exact competing statements: C20c asserts

  (1/K) sum_{K<=k<2K} B_k/log(k+2) -> (3+R_a)/8;

C20d is its negation. C20a implies C20c, but the converse is not used.
The first attack separates the signed low-row average from the unsigned
high-row average. A generic positive Gaussian would predict1/2; retaining
the actual negative lobes predicts a strictly larger constant. This tests
arithmetic resolution, not merely the order of a norm. Preliminary verdict
SURVIVES PRELIMINARY ATTACK. Current exact searches found no applicable
closure, but partial/stale coverage gives no novelty certificate. The
parent maximal divisor estimate is Ivić–Zhai, arXiv1209.0872v1, Lemma2.1;
its domain is checked below. No numerical experiment is involved.

Here is the paper proof using C17's paper-proved actual profile and global
envelope. It remains unformalized, including that analytic dependency.
Set c=2pi, I=integral J_a=c/sqrt(a), and write T for C17's saddle,
b for its amplitude. Its conclusions, uniformly for all sufficiently
large integer k, are

  E_k ~ b sqrt(T) log(T) I/c,
  K_k(m)/b = J_a((cm-T)/sqrt(T))+o_R(1) for |cm-T|<=R sqrt(T),
  |K_k(m)|/b <= C(1+|cm-T|/sqrt(T))^(-4).

Choose a smooth cutoff chi_R, equal1 on [-R,R], zero outside [-2R,2R],
0<=chi_R<=1, and let J_R=chi_R J_a. Put I_R=integral J_R and
V_R=integral |J_R|. Choose R large enough that I_R>0. The exact G4
convolution Lambda*d=d log/2 and the triangle inequality pay replacement
of the whole prime functional by this compact profile. Indeed the local
replacement error is o_R(1) times sum_{|cm-T|<=2R sqrt(T)} d(m)log(m).
The divisor hyperbola estimate D(x)=x(log x+2gamma-1)+O(sqrt(x)) makes
this O_R(sqrt(T)log^2(T)). The envelope outside that window has total
weighted mass at most O(R^(-3)sqrt(T)log^2(T))+o(sqrt(T)log^2(T)):
split into doubling windows until their width reaches T, then use dyadic
intervals in m with decay T^2/m^4. The lower far region is bounded by
O(T^(-1)log^2(T)). These estimates retain all prime powers. Thus, after
normalization, replacement error has limsup O(R^(-3)).

It remains to average the nonnegative continuous-parameter expression

 F_R(T)=c/(I sqrt(T)log^2(T))
          sum_{n>=2} Lambda(n) |sum_{N>=1}d(N)J_R((cnN-T)/sqrt(T))|.

Work on L<=T<=2L and fix 0<epsilon<1/4. Put beta_-=1/2-epsilon,
beta_+=1/2+epsilon; thresholds n=L^beta are constant on this averaging
block. Changes by fixed multiplicative constants or floor rounding do
not change any logarithmic coefficient below.

LOW ROWS, n<=L^beta_-. Write x=T/(cn), h=sqrt(T)/(cn), so the row is
sum_N d(N)J_R((N-x)/h). Stieltjes integration against D gives its main
term h I_R(log x+2gamma), with smooth-density error O_R(h^2/x).
For the remainder integrate by parts and subtract Delta(x), obtaining
an integral of J_R' times Delta(x+hv)-Delta(x). Its norm is bounded by
C_R max_{|u|<=U}|Delta(x+u)-Delta(x)|, where U=C_R sqrt(L)/n.
For n above a fixed constant depending on R, 2<=U<=sqrt(X), X~L/n.
Ivić–Zhai Lemma2.1 bounds the squared maximal increment integral on a
dyadic X block by O(X U log^5 X); negative increments follow by shifting
the starting point and using two positive increments. A finite number
of dyadic covers handles all endpoints. After x=T/(cn) and Cauchy–Schwarz,
the average absolute row error is O_R(L^(1/4)n^(-1/2)log^(5/2)L).
Chebyshev's bound sum_{n<=Y}Lambda(n)/sqrt(n)=O(sqrt(Y)) shows that its
contribution to the average F_R is

  O_R(L^(-epsilon/2)log^(1/2)L)=o(1).

The finitely many excluded n cost o(1) in F_R: their individual rows
are O_R(sqrt(L)log L) by the same elementary divisor estimate. The
O_R(h^2/x) and constant2gamma density terms cost o(1) after summation.
Since the main term is positive, ||row|-main|<=|row-main|. Mertens'
identity sum_{n<=Y}Lambda(n)/n=log Y+O(1), with partial summation, now
makes the low-row averaged contribution

  (I_R/I)(beta_- - beta_-^2/2)+o(1).

HIGH ROWS, n>=L^beta_+. Distinct N centers have spacing cn, exceeding
4R sqrt(2L) for large L. At most one term in each row meets the support;
absolute value therefore passes through that row sum EXACTLY. Tonelli
then averages positive packets centered at cnN. Substitution
u=(cnN-T)/sqrt(T) gives integrated packet weight V_R/log^2(cnN), with
relative error O_R(L^(-1/2)) away from block endpoints. Endpoint strips
of width O_R(sqrt L) cost o(1): bound their coefficients by the full
convolution d(m)log(m)/2 and the divisor hyperbola estimate.
The needed cumulative coefficient formula, for any fixed0<beta<1, is

 sum_{n>=L^beta, nN<=X} Lambda(n)d(N)
   = (X/2)(log(X/L^beta))^2 + O(X log X),  X~L.

To check its uniform error, sum D(X/n) over n. The divisor remainder
costs sqrt(X)sum_{n<=X}Lambda(n)/sqrt(n)=O(X). Its main term follows
from the same Mertens identity by partial summation; constants cost
O(X log X). Partial summation against 1/log^2(cnN), followed by the
factor c/(I L), therefore makes the high-row average

  (V_R/I)(1-beta_+)^2/2+o(1).

TRANSITION, L^beta_-<n<L^beta_+. Its contribution is nonnegative.
Triangle inequality linearizes it, and the preceding positive-packet
average plus cumulative coefficient formula bounds its limsup by

  (V_R/I) integral_{beta_-}^{beta_+}(1-u)du = (V_R/I)epsilon.

This upper bound needs neither disjointness nor a prime short-interval
asymptotic. There are no missing n much larger than L: compact support
forces cnN~L. The already paid profile tail contains all other labels.
Let L tend to infinity, then epsilon tend to zero. The low/high bounds
squeeze the average of F_R to (3 I_R+V_R)/(8I).

DISCRETE ORDERS. C17's saddle T_k=(2k+7/2)/a is an affine grid with
fixed positive spacing2/a. On each grid cell, the variation of a row
profile is bounded by C_R/sqrt(L) times its positive support majorant.
Sum this variation with Lambda weights and use Lambda*d=d log/2.
The majorant's whole window mass is O_R(sqrt(L)log^2 L). Including
variation of the prefactor shows |F_R(T)-F_R(T_k)|=O_R(L^(-1/2))
within a cell. Hence normalized Riemann sums and block integrals have
the same limit. The endpoints T_K,T_{2K} differ from L,2L by O(1),
which has vanishing normalized effect by the same bound. Also
log(k+2)/log(T_k)->1 uniformly in the block. This proves the stated
average for the actual B_k, after R tends to infinity: I_R->I,
V_R->integral|J_a|, and the paid tail tends to zero.

Status: dependency-closed PAPER proof, UNFORMALIZED. It uses no unproved
prime-distribution premise, RH premise, or pointwise divisor conjecture.
Its external parents are classical; scientific novelty of this particular
sharp coefficient is not certified. C20a/C20b remain open. This result
would quantify an absolute arithmetic cost, not produce C15's positive
mixture or an upper bound for the assigned spectral deficit.

### G7 demodulated first derivative: paper proof before Lean

Let M_k be G5's actual Mellin integral, and T=(2k+7)/(pi/2), B as G6.
Define F_k(t)=M_k(4+it) exp(-it log(T/(2pi))). On t>0, Gamma is
holomorphic and nonzero, so direct product differentiation gives

 F_k'(t)=F_k(t) Z_k(t),
 Z_k(t)=2ki/(7/2+it)+2i/(4+it)+2i/(3+it)
          +i psi(2+it/2)-i log pi-i log(T/(2pi)).

This identity concerns the actual transform via G5; no derivative of an
unjustified integral interchange is taken. All logarithms of positive
real constants use the real branch. On T/2<=t<=2T we have T>4 and t>2,
using pi<7/2. Existing uniform vertical digamma asymptotics supply one
C0>=0 with psi(2+it/2)=log(t/2)+i*pi/2+epsilon(t), |epsilon|<=2C0/t.
For every positive t, |sigma+it|>=t; hence

 |i/(7/2+it)-1/t| <= (7/2)/t^2,
 |2i/(4+it)+2i/(3+it)| <=4/t.

Since 2k=(pi/2)T-7 and t>=T/2, k<=pi*t/2. Combining these estimates
writes Z_k=(2k/t-pi/2)+i log(t/T)+R_k with
|R_k|<=(7pi/2+4+2C0)/t. For1/2<=r<=2, the elementary inequalities
log r<=r-1 and -log r<=1/r-1 imply |log r|<=2|r-1|. Therefore

 sqrt(T)|Z_k(t)| <= C1(1+|t-T|/sqrt(T))

with one C1>0 independent of k,t. Multiplication by G6 proves one
C2>0 with

 sqrt(T)|F_k'(t)| <= C2 B (1+|t-T|/sqrt(T))
                             exp(-pi*(t-T)^2/(18T)).

This is a dependency-closed classical BRIDGE for C17. Higher derivative
orders and tails remain explicit separate obligations; no finite-order
bound is labeled the full uniform Schwartz estimate. Reuse sharp
polygamma decay for those higher orders rather than weak Cauchy bounds.

### C21 actual first-kernel comparison (resolved below)

Given C19's cardinal-spike reduction and the actual C17 profile, a sharper
falsifiable attack on C15 is:

 C21a: K_k(1) < E_k for every integer k>=0.
 C21b: K_k(1) >= E_k for at least one integer k>=0.

The inequalities are signed; replacing K_k(1) by its norm would be a
stronger different conjecture. If C21a holds, every probability mixture
satisfies sum_k w_k K_k(1)/E_k <1, contradicting C19's forced value1.
The strict averaged inequality needs no uniform gap: the expectation of
the everywhere-positive function1-K_k(1)/E_k is strictly positive.
C17 bounds the ratio and forces it to zero, so its convergence and the
weighted interchange are already paid on paper. It follows that only
finitely many derivative orders can violate C21a, but an unspecified
finite exception set is not a proof that it is empty.

This comparison is NOT immediate from Cauchy--Schwarz. K_k(1) is the
signed reflected correlation of a single theta summand; E_k is the
energy of the entire theta sum. Derivative cross terms are signed, so
the whole energy is not automatically larger than one summand's energy.
Original [OPEN CORE]: strict comparison at every remaining low/intermediate
order, or an exact counterexample. Either outcome is informative for
C15: a violation identifies the specific columns that can support a
cardinal spike; universal strictness retires C11q and leaves its proven
positive tightness/logarithmic-budget survivors. No premise added to
Lean. The following subsection resolves this contest: C21a is false and
C21b holds at k=1, with the full sign survivor formalized.

### C21a fails; positive survivor: the entire first-derivative integer column is negative

Verdict: **FALSE** for C21a. The following proof is dependency-closed;
its exact survivor is now formalized in `WeilWorkDeficitLowOrderSigns.lean`
(six public theorems, target/direct/axiom audits passed). This does not retire C15.
Write B_j(z)=realModifiedBesselKOrder z j, reserving K_k for the product
kernel. All B_j(z) are positive for z>0. The corpus Schlaefli integral
and order recurrence give B_2=B_0+(2/z)B_1. Pointwise
cosh(2u)>=4cosh(u)-3, since the difference is 2(cosh(u)-1)^2.
Integrating against exp(-z cosh u) gives B_2>=4B_1-3B_0. Thus

  (2z-1)B_1 <= 2z B_0,
  B_1 <= (1+1/z)B_0                 for z>=1.

The second conclusion follows because 2z/(2z-1)<=1+1/z for z>=1.
All integrals converge by the existing real-order Schlaefli theorem;
there is no asymptotic estimate or numerical approximation here.

The actual corpus polynomial is P_0(X)=4pi^2 X^2-6pi X and
D P=P/2+2X P'-2pi X P. Consequently

  P_1(X)=-15pi X+30pi^2 X^2-8pi^3 X^3.

Expanding the finite product-kernel definition, using B_-j=B_j and
B_2(2y)=B_0(2y)+B_1(2y)/y, gives the exact identities, with y=pi*x:

  K_0(x)=4y^2[(4y^2+9)B_0(2y)-12y B_1(2y)],
  K_1(x)=-y^2[(64y^4+1140y^2+225)B_0(2y)
                            -(480y^3+660y)B_1(2y)].

For x>=2, y>=2pi>6. Apply the preceding ratio bound at z=2y.
The bracket for K_0 is at least (4y^2-12y+3)B_0(2y)>0.
The bracket for -K_1 is at least Q(y)B_0(2y), where

  Q(y)=64y^4-480y^3+900y^2-660y-105
      =64(y-6)^4+1056(y-6)^3+6084(y-6)^2+13596(y-6)+7599 >0.

Hence K_0(x)>0 and K_1(x)<0 for EVERY REAL x>=2. G4's absolutely
convergent divisor expansion now yields A(n,0)>0 and A(n,1)<0 for
every integer n>=2: all nonzero terms have the stated sign and the
N=1 term is strict. At shift zero E_k=sum_m d(m)K_k(m), with d(0)=0
and d(1)=1. Therefore

  K_0(1)<E_0,                    E_1<K_1(1).

The second strict inequality disproves C21a and proves C21b with k=1.
It also identifies exactly why single-summand energy comparison fails.
The useful survivor is the sign separation of the complete k=0 and k=1
integer columns, not merely an isolated counterexample. It supplies
opposite directions for positive-mixture cancellation. It does NOT
construct simultaneous cancellation, prove C15 false, or close WP06.
Classification of the mechanism: classical-parent BRIDGE; no external
scientific novelty certification. Parent audit: DLMF10.29/10.32;
corpus BesselOrderRecurrence and BesselOrderPositiveComparison. Exact
corpus sign query was inspected before formalization.

### C22: test the infinite-weight boundary directly (OPEN)

For integer N>=3 let

  g_N(t^2)=1/|Gamma(N+1/4+it/2)|^2,
  R_N(n)=integral_R |Xi(t)|^2 g_N(t^2) cos(t log n) dt.

Competing exact conjectures: R_N(n)>0 for every N>=3 and integer n>=2;
or R_N(n)<=0 for some such pair. [OPEN CORE]: the sign of these literal
integrals. Neither conjecture is assumed in Lean or in the C15 argument.

DLMF5.8.3 gives positive coefficients of the entire function g_N(z):
g_N(z)=Gamma(N+1/4)^(-2) product_{j>=0}(1+z/[4(N+1/4+j)^2]).
Gamma recurrence and the definition Xi(t)=xi(1/2+it) give exactly

  |Xi(t)|^2 g_N(t^2) = 4^(N-1)/sqrt(pi) *
    (t^2+1/4)|zeta(1/2+it)|^2 /
      product_{j=1}^{N-1}(t^2+(2j+1/2)^2).

This is a concrete boundary family for C15, where exponential Gamma
decay cancels. The coefficient-to-mixture normalization and finite log
moment must be explicitly checked before consuming it as a C15
witness. Rational-weight Mellin autocorrelation is classical ancestry,
not new scientific knowledge. Darses--Hillion2609.36200v2 covers the
sq/ch weights and their reciprocity, not the claimed sign above.
For N=3 the rational factor is exactly
(-3/7)/(t^2+25/4)+(10/7)/(t^2+81/4); positivity of each separately
weighted autocorrelation would not establish positivity of this signed
combination. This is the immediate adversarial test, not a sign proof.

### C22 admissibility for N>=4 (dependency-closed PAPER bridge)

Fix an integer N>=4 and put A=N+1/4. Define the entire function by its
normally convergent product

  g_N(z)=Gamma(A)^(-2) product_{j>=0}(1+z/[4(A+j)^2])
        =sum_{k>=0} c_k z^k.

Normal convergence follows from sum_j (A+j)^(-2)<infinity; hence all
c_k>=0 and c_0>0. DLMF5.8.3 identifies its value on t^2 with the
reciprocal-Gamma expression above. Gamma recurrence gives the displayed
exact rational zeta-square density nu_N(t)=|XiC(t)|^2 g_N(t^2).

The literal corpus bound `RiemannGaussian.norm_riemannZeta_criticalLine_le_linear`
has been checked with an explicit type at s=1/2+iT, T>0, and standard-only
axioms. Its constant is three times the fixed summable paired-eta mass,
not a parameter hypothesis. Conjugation handles T<0; continuity handles
bounded T. Consequently

  nu_N(t) <= C_N (1+|t|)^(6-2N),
  integral nu_N(t) (1+log(2+|t|)) dt < infinity.

Only N>=4 is claimed from this elementary bound. It does not establish
the N=3 endpoint, which needs a stronger zeta estimate.

The finite logarithmic moment of the coefficient mixture also needs
payment; integrability of nu_N alone does not prove it. For t>=0,
differentiate the normally convergent product to obtain

  t^2 g_N'(t^2)/g_N(t^2)
       =sum_{j>=0} t^2/[4(A+j)^2+t^2] <= 1+pi*t/4.

For t>0, the first term is at most1 and the decreasing tail is at most
integral_0^infinity t^2/(4u^2+t^2) du=pi*t/4. At t=0 the sum vanishes.
The elementary tangent bound for log gives, for every k>=0,

  log(k+2) <= log(2+t)+k/(2+t).

Multiply by c_k t^(2k), sum, and use the preceding derivative bound:

  sum_k c_k t^(2k)log(k+2)
    <= g_N(t^2)[log(2+t)+1+pi/4].

The paper Plancherel identity already recorded under C12 gives
E_k=(1/(2pi)) integral t^(2k)|XiC(t)|^2 dt. Tonelli therefore proves

  Z_N=sum_k c_k E_k=(1/(2pi)) integral nu_N(t) dt < infinity,
  sum_k c_k E_k log(k+2) < infinity.

Also Z_N>0 since c_0>0 and E_0>0. Thus w_k=c_k E_k/Z_N is an actual
nonnegative probability sequence with finite logarithmic moment.
Cauchy--Schwarz gives |A(n,k)|<=E_k, so every row sum converges absolutely.
Dominated convergence, using the integrable density nu_N, proves exactly

  sum_k w_k A(n,k)/E_k = R_N(n)/R_N(1),             every integer n>=1.

Here E_k>0 is the previously established derivative-energy fact; no
division by a zero energy is introduced. This pays C22's N>=4 family
membership in C15 on paper. It does NOT settle the sign of any R_N(n),
produce a cancelling mixture, settle N=3, or prove the spectral deficit.
All ingredients are classical; verdict BRIDGE. Formalization of this
assembly remains pending, separate from the already audited source bound.

### C23: arithmetic resonance of the C22 family (exact conjecture)

Fix an integer N>=4, let p=2N-4, and retain the literal R_N above.
The competing statements are:

  C23a: R_N(x) = 16 pi^(9/2-2N) x^(1/2-p)
          sum_{m>=1} d(m) cos(2pi*m*x)/m^p + O_N(x^(-p-1/2)), x>=1.
  C23b: this formula fails for at least one N>=4.

In particular C23a forces

  lim_{n->infinity, n integer} n^(p-1/2) R_N(n)
      =16 pi^(9/2-2N) zeta(p)^2 > 0.

Every fixed member of the explicit admissible C22 family would then fail
the simultaneous C15 cancellation equations. This does not assert signs
at all small integers or exclude general C15 sequences, or positive
mixtures of C22 members with unbounded N. Its falsity would expose a
missing arithmetic/polar term or a failure of the critical-decay Mellin
interchange. The exact mechanism is a rational Mellin symbol whose first
nonzero derivative jump creates cos(2pi*x); all divisor dilates resonate
with the same sign at integers.

Initial [OPEN CORE]: pay the critical-to-Re(s)=2 contour shift uniformly,
the conditionally convergent cosine-Mellin interchange, and the exact
jump/asymptotic constants. No new scientific premise is allowed.

Parent attack: the corpus rational-sign query was partial and returned
general Mellin convolution, not a C22 sign theorem; the derivative-jump
query was complete at source level but compiler coverage remains mostly
source-only/stale. Its proposed proof chains do not prove this statement.
Bettin--Conrey, arXiv:1111.0931v2, equations (9)--(10), gives the parent
weighted divisor/Mellin mechanism; its exponential-sector statement does
not directly pay the present boundary cosine integral. Darses--Ringeling--
Royer, arXiv:2506.22014, treats cosh-weighted L-moments and their period
functions. Neither inspected statement certifies novelty for C23.
Provisional verdict: BRIDGE, not scientific novelty. The useful target
is the exact obstruction inside C15, not a renamed classical transform.

### C23 paper proof: divisor resonance, with all contour debts paid

Retain N>=4 and p=2N-4. Put

  q_N(s)=s(s-1)/product_{j=1}^{N-1}[(s+2j)(s-(2j+1))],
  C_N=(-1)^N 2^(2N-1)/sqrt(pi),
  M_N(s)=s^2(s-1)^2 pi^(-s) Gamma(s/2)^2 /
           [4 Gamma(N+s/2) Gamma(N+1/2-s/2)].

Gamma reflection, N recurrences, and duplication give exactly

  M_N(s)=C_N q_N(s) (2pi)^(-s) Gamma(s) cos(pi*s/2).       (23.1)

This is an identity of meromorphic functions, with removable values
understood. Indeed reflection supplies (-1)^N cos(pi*s/2)/pi;
the two recurrence products supply 2^(2N), duplication supplies
2^(1-s)sqrt(pi), and cancellation of s(s-1) leaves q_N.
The original M_N is holomorphic on Re(s)>0. In particular no residue
is lost at the apparent positive odd poles of q_N.

Let a_r be the residue of q_N at its simple roots r=-2j,2j+1.
Since q_N(s)=s^(-p)(1+O(1/s)), its partial fractions satisfy

  sum_r a_r r^j=0 (0<=j<=p-2),    sum_r a_r r^(p-1)=1.

Define the real integrable kernel

  phi_N(u)=-sum_{r>0} a_r u^(r-1),                 0<u<1,
            sum_{r<0} a_r u^(r-1),                 u>1.

The value at1 is the common one. The jump of its jth derivative at1
is sum_r a_r (r-1)(r-2)...(r-j), hence is zero through j=p-2
and equals1 at j=p-1. On (0,1) it is an even polynomial with zero
constant term. On (1,infinity) it is a finite sum of u^(-2j-1).
Every derivative on the latter interval is integrable and vanishes
at infinity; all odd derivatives at0 vanish. Define

  L_N(x)=C_N integral_0^infinity phi_N(u) cos(2pi*x*u) du.

Piecewise integration by parts p times therefore gives

  L_N(x)=C_N (-1)^(p/2) (2pi*x)^(-p)
           [cos(2pi*x)+integral_0^infinity phi_N^(p)(u)
                                             cos(2pi*x*u) du].

Here phi_N^(p) means the ordinary derivative on each open piece,
not the distributional derivative; the displayed cosine is exactly
the delta mass from the first derivative jump. One more piecewise
integration by parts bounds the last integral by C/x: both derivative
integrals and one-sided endpoint values are finite. Consequently

  L_N(x)=alpha_N x^(-p) cos(2pi*x)+O_N(x^(-p-1)), x>=1,
  alpha_N=8 pi^(7/2-2N)>0.                         (23.2)

L_N is bounded and continuous at0 by phi_N in L1. Thus its Mellin
integral converges absolutely and is holomorphic for 0<Re(s)<p.
To identify it first fix 0<sigma=Re(s)<1. The partial integrals

  integral_0^R x^(s-1) cos(2pi*u*x) dx

are uniformly bounded by C_s u^(-sigma): substitute v=u*x; on
[0,1] use absolute integration, and on [1,V] use one integration by
parts, whose remainder has modulus bounded by |s-1| integral_1^infinity
v^(sigma-2)dv. Since integral |phi_N(u)|u^(-sigma)du is finite,
finite-R Fubini followed by dominated convergence is legitimate.
The ordinary cosine-Gamma integral (obtainable by exponential damping
and the same tail bound) now gives

  integral_0^infinity x^(s-1)L_N(x)dx
    =C_N (2pi)^(-s)Gamma(s)cos(pi*s/2)
                      integral_0^infinity phi_N(u)u^(-s)du
    =M_N(s).

Each monomial integral in the last factor equals a_r/(s-r), with
the minus sign in the inner definition essential. Analytic continuation
on the connected strip extends the equality to 0<Re(s)<p. This uses
no absolute Fubini claim for the infinite undamped cosine integral.

Let F_N(s)=M_N(s)zeta(s)^2. The defining xi identity gives

  F_N(s)=xi(s)^2/[Gamma(N+s/2)Gamma(N+1/2-s/2)],

so F_N is entire; on s=1/2+it it is exactly nu_N(t), real and even.
Uniformly for 1/2<=sigma<=2 and |t|>=1, the elementary fractional-part
identity already formalized in `ZetaFractionalPartTrigEquations` gives

  |zeta(s)| <= |s|/|s-1|+|s|/sigma <=3|s|=O(1+|t|).

The integral remainder is bounded by integral_1^infinity x^(-sigma-1)
dx=1/sigma. Thus no critical-line-only estimate is silently used on
the strip. Uniform compact-strip Stirling in (23.1) yields

  |M_N(s)|=O_N(|t|^(sigma+7/2-2N)),
  |F_N(s)|=O_N(|t|^(sigma+11/2-2N)).

For N>=4 the latter is O_N(|t|^(-1/2)) throughout the strip, enough
to make horizontal edges tend to zero. The critical-line integral is
absolutely integrable by C22; on sigma=2 the absolutely convergent
Dirichlet series bounds zeta uniformly, so F_N is O_N(|t|^(-5/2))
or better. Cauchy's theorem therefore shifts the inverse Mellin line
from1/2 to2 with no residues.

Mellin inversion on sigma2 applies to continuous L_N: its weighted
integral is finite by (23.2), and M_N(2+it) is integrable by the same
Stirling bound. Absolute Dirichlet-series Fubini on that line is paid by
sum d(m)/m^2=zeta(2)^2<infinity and integral|M_N(2+it)|dt<infinity.
For every x>0, evenness on the original line consequently gives

  R_N(x)=2pi sqrt(x) sum_{m>=1} d(m)L_N(mx).          (23.3)

Apply the uniform estimate (23.2) term by term for x>=1. Its errors
sum absolutely since sum d(m)/m^(p+1)=zeta(p+1)^2<infinity. Equations
(23.2)--(23.3) prove C23a with the displayed constant. At integer x=n
all cosines equal1, and sum d(m)/m^p=zeta(p)^2>0. This proves the
positive limiting constant and eventual strict positivity, without a
small-integer sign claim. Every finite nonzero nonnegative mixture of
these normalized C22 members also has eventual positive correlation:
the smallest N with nonzero coefficient has the slowest decay and a
positive leading coefficient; finitely many larger N are lower order.

Status: dependency-closed PAPER bridge. Full Lean assembly is pending.
No C15 construction, universal C15 no-go, or deficit-density conclusion
follows. The exact C22-family obstruction is not retired until its
positive asymptotic survivor is formalized and audited.

The first formal C22/C23 assembly step uses the stronger existing
`norm_riemannZeta_le_sqrt_norm_add_two_half`. On s=1/2+it, take d=1/2;
|s-1|>=1/2, so |zeta(s)|^2<=36(|s|+2)<=108(1+t^2).
The literal density formula at N=4 then gives

  0<=nu_4(t)<=[6912/sqrt(pi)]/(1+t^2),

since all three denominator factors dominate1+t^2 and the numerator
factor t^2+1/4 is at most1+t^2. Gamma recurrence gives
nu_{N+1}(t)=nu_N(t)/[(N+1/4)^2+t^2/4], so nu_{N+4}<=nu_4 for every
natural N. These actual densities are continuous (Gamma has no zeros
in this half-plane). Poisson integrability, including the already
formalized logarithmic weight, proves both integrability assertions
uniformly in this shifted family. This is an unconditional analytic
bridge, not the pending integer-correlation sign theorem.

### C24: continuous Gamma-order resonance (OPEN conjecture)

C23's obstruction survives every finite positive integer-order mixture.
The next competing conjectures test whether moving off that integer
lattice can remove the resonance. For real A>=17/4 put

  R_A(x)=integral_R |XiC(t)|^2/|Gamma(A+it/2)|^2 cos(t log x)dt,
  p_A=2A-9/2.

C24a asserts, uniformly for A in every compact subinterval of [17/4,infinity),

  R_A(x)=16 pi^(5-2A) x^(5-2A)
              sum_{m>=1} d(m)cos(2pi*m*x)/m^(p_A)
             +O_K(x^(4-2A)), x>=1.

C24b asserts failure of this uniform expansion for some such compact
interval. If C24a holds, EVERY nonzero finite positive measure of
Gamma orders supported in a compact interval has eventually positive
integer correlations, even when it has no atom at its smallest order.
The uniform relative error and the positive continuous leading
coefficient prove this pointwise in A before integrating; no Laplace
endpoint asymptotic or exchange of nonuniform limits is needed.

The structural prediction is absence of a tunable leading phase. The
exact candidate Mellin symbol is

  M_A(s)=s^2(s-1)^2 pi^(-s)Gamma(s/2)^2 /
    [4Gamma(A-1/4+s/2)Gamma(A+1/4-s/2)].

Reflection and a Gamma-ratio expansion suggest the leading factor
2^(2A-3/2)/sqrt(pi) times
(2pi)^(-s)Gamma(s)s^(-p_A)sin(pi(A+1/4-s/2)).
The inverse-oscillation phase cancels because
pi(A+1/4)-pi*p_A/2=5pi/2. This is only a mechanism calculation,
not a proof that asymptotic Mellin inversion preserves the remainder.

[OPEN CORE]: derive the uniform inverse-Mellin endpoint asymptotic
for the nonrational Gamma ratio, including both vertical tails and all
interchanges. The C23 polynomial/jump argument does not prove it.
Internal exact-mechanism search was source-complete but found only
Gamma recurrences, reciprocal-Gamma analyticity and unrelated cosine
integrals. It supplies no fractional-order resonance theorem. External
Hansen--Tong2602.17007v2 explicitly gives classical Hankel/PMT
reparametrizations, not this weighted Xi-square asymptotic. A surfaced
Koide preprint on dual-Hahn expansions could not be read at its primary
Zenodo URL; it remains an unverified parent lead. Novelty is uncertified;
provisional verdict BRIDGE. Full C15 still concerns much more general
coefficient sequences, so even C24a would not close its existence problem.

C24's further parent attack identifies the undifferentiated Mellin-Barnes
symbol with the candidate kernel

  H_A(x)=(1/2) G_{1,3}^{2,0}(pi^2*x^2 |
                         A-1/4 ; 0,0,3/4-A),
  L_A=D^2(D-1)^2 H_A,                    D=-x*d/dx.

The parameter/constant matching follows by substituting s=2u in the
Mellin symbol before the factor s^2(s-1)^2. This is a parent-theory
identification, NOT a proved use of a table asymptotic. DLMF16.17(i)'s
stated sufficient vertical-contour condition is strict p+q<2(m+n),
whereas this kernel has equality4=4. Also its two bottom poles overlap.
DLMF16.22 directs to Luke1969a sections5.7/5.10 and Luke1975 section5.9;
those exact boundary/uniform-parameter theorems have not been verified.
Thus a table lookup cannot close C24's open core without its hypotheses
and uniform remainder. These facts reinforce the BRIDGE verdict.

### C23 formal symbol assembly: removal of apparent poles

Before any new Lean source, fix the actual entire F_N=spectralMellin N.
Let P_N(s)=product_{j=0}^{N-1}(s+2j+2)(s-(2j+3)). The reciprocal-Gamma
recurrence, valid also at Gamma poles, gives globally

  (s+2N+2)(s-(2N+3)) F_{N+2}(s) = -4 F_{N+1}(s),
  P_N(s) F_{N+1}(s) = (-4)^N F_1(s).

Indeed the two Gamma arguments at order N+1 are a=N+1+s/2 and
b=N+3/2-s/2; a*b=-(s+2N+2)(s-(2N+3))/4, and
1/Gamma(a)=a/Gamma(a+1) holds globally, including a=0,-1,... .
Induction proves the product identity without division by P_N.

On the safe inversion line s=2+it every factor of P_N is nonzero:
the first has positive real part, the second real part -(2j+1).
The base value is

  F_1(s) = -2/sqrt(pi) * s(s-1) * (2pi)^(-s)
             * Gamma(s) * cos(pi*s/2) * zeta(s)^2.

To prove it, expand xi=s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)/2.
Gamma recurrence removes Gamma(1+s/2). Reflection at z=(s-1)/2
(which and 1-z both have real part1/2) converts the remaining inverse
Gamma to -Gamma((s-1)/2)cos(pi*s/2)/pi. Duplication at (s-1)/2
and Gamma(s)=(s-1)Gamma(s-1) give the displayed value. Positive-real
complex powers combine pi^(-s)2^(-s)=(2pi)^(-s). Dividing the global
product identity by the nonzero P_N now proves (23.1) for the actual
F_{N+1} on the full inversion line, including t=0. No equality at s=1
between a totalized zeta product and the entire quotient is asserted.
This is a classical-parent BRIDGE, not new scientific knowledge.

### C25: critical coefficient-tail necessity (OPEN)

Given C19's exact cardinal condition and C23's boundary resonance, the
next competing assertions concern unrestricted coefficient sequences,
not another Gamma family. Retain the actual E_k and A(n,k).

C25a: every probability w satisfying all A(n,k)/E_k cancellation rows,
n>=2, and finite logarithmic moment must satisfy

  sum_k w_k exp(delta*k) = infinity for EVERY delta>0.

C25b: there exist delta>0 and a cancelling probability w with that
exponential moment finite. The latter would refute C15 and produce a
much stronger regularity class than the currently requested log moment.
Neither assertion is assumed. No claim of novelty is certified.

The representation behind this question is
G_w(z)=sum_k (w_k/E_k)z^(2k). The paper C17 energy asymptotic makes this
an even entire function of type at most pi/2. An exponential moment
improves the upper type to (pi/2)exp(-delta/2). For real t its
coefficients are nonnegative and |XiC(t)|^2 G_w(t) is the actual mixed
spectral density. Thus C25a predicts that exact arithmetic cancellation
forces the maximal exponential type, or at least forbids every
exponential coefficient moment. This is a structural necessity, not a
solution of C15 or WP06. The type implication is one-way; absence of
all exponential moments is not being identified with a proved exact
type without the corresponding coefficient lower bound.

[OPEN CORE]: turn positivity of these Taylor coefficients and the
integer cardinal conditions for the actual inverse-Mellin product kernel
into the claimed coefficient-tail obstruction. Carlson uniqueness alone
does not do this: it requires a holomorphic integer interpolant with
controlled vertical indicator, and the spectral entire-function type is
not the physical interpolant's vertical indicator. Nor does a narrow
strip of analyticity in log(x) imply uniqueness on log(n). The positive
coefficient restriction, actual Gamma symbol and all analytic transports
must be used or a counterexample constructed. Provisional verdict:
SURVIVES PRELIMINARY ATTACK, with this unproved core explicit.

### C25c positive survivor: a quantitative fast-tail obstruction (PAPER)

The following weaker consequence has a complete paper proof, using the
already recorded C17 energy asymptotic and C19 spike reduction:

  NO cancelling probability w can have sum_k w_k(2pi)^(2k)<infinity.

Equivalently every C15 candidate has that moment infinite. This does not
prove C25a for every positive exponential rate. It applies to arbitrary
coefficient sequences in the stated moment class, not only Gamma weights.
Verdict BRIDGE to classical Carlson uniqueness; scientific novelty is
uncertified. No Lean closure or retired route is claimed.

Write c_k=w_k/E_k and G(z)=sum c_k z^(2k). C17 gives
(E_k/(2k)!)^(1/(2k))->2/pi. Hence the moment assumption implies
limsup[((2k)!c_k)^(1/(2k))]<=1/4. Define the Borel function
B(zeta)=sum_k (2k)!c_k/zeta^(2k+1), holomorphic for |zeta|>1/4.
On the positively oriented circle |zeta|=b=1/3, ordinary uniform
convergence and Cauchy's coefficient formula give, for every complex z,

  G(z)=(1/(2pi*i)) integral B(zeta) exp(zeta*z) dzeta.       (25.1)

Let K_0(z) be the holomorphic continuation to the slit plane of the
actual G4 order-zero kernel. Its exact expression is

  4(pi*z)^2[(4(pi*z)^2+9)K_0^Bessel(2pi*z)
                         -12pi*z K_1^Bessel(2pi*z)].

Here the two Bessel terms use the principal branch. The classical
small-argument expansions bound this expression near zero on each
closed subsector of the slit plane. The large-argument expansions
(DLMF10.40.2, uniform for |arg z|<=pi/2+b<3pi/2) give
C(1+|z|)^4 exp(-2pi Re z) on this sector, after enlarging C to cover
bounded annuli. Define for Re x>0

  F(x)=(1/(2pi*i)) integral_|zeta|=b
                B(zeta) exp(i*zeta/2) K_0(x exp(i*zeta)) dzeta.   (25.2)

The integrand is holomorphic in x because |arg(x exp(i*zeta))|<pi/2+b<pi.
Compact contour integration preserves holomorphy. For x=u+iv,u>=0,

  Re(x exp(i*zeta)) >= exp(-b)cos(b)u-exp(b)sin(b)|v|.

Consequently F is continuous on Re x>=1 and obeys

  |F(x)|<=C(1+|x|)^4 exp(-a u+beta|v|),
  a=2pi exp(-b)cos(b)>0, beta=2pi exp(b)sin(b)<pi.           (25.3)

The strict last inequality follows from sin(1/3)<1/3 and
exp(1/3)<3/2; the latter follows from log(3/2)>1/3 by integrating
1/t>2/3 on (1,3/2).

It remains to identify F with the actual positive mixture. On the Mellin
line s=1/2+it, (25.1) gives G(-i(s-1/2)); the order-zero actual Mellin
symbol has exponential decay exp(-pi|t|/2) times a polynomial.
Since b<pi/2, contour/Mellin Fubini is absolute. The inverse Mellin
transform of M_0(s)exp(-i*zeta*s) is K_0(x exp(i*zeta)). First this
holds for imaginary zeta (ordinary positive real scaling); both sides
are holomorphic on |Re zeta|<pi/2 with locally dominated integrals, so
the identity theorem proves the full assertion used in (25.2).
Alternatively applying dominated convergence to the power series gives

  F(x)=sum_k c_k K_k(x), x>0.

The domination is |M_0(1/2+it)| G(|t|), which is integrable because
G(|t|)<=C exp(b|t|). Each finite term is exactly G5's Mellin derivative
symbol. Thus there is no unproved passage from formal power series to
physical kernel. The strong moment implies the C15 log moment, so C19
now gives F(1)=1 and F(n)=0 for all integers n>=2.

Apply the classical half-plane Carlson theorem to H(z)=F(z+2).
It is holomorphic on a neighborhood of Re z>=0. By (25.3), for any
beta<beta'<pi its polynomial factor can be absorbed into C exp(beta'|z|),
so it has exponential type below pi on this half-plane and on both
vertical boundary rays. All H(n),n>=0, vanish. Carlson gives H=0;
analytic continuation in the connected right half-plane gives F(1)=0,
contradicting F(1)=1. This proves C25c. It neither substitutes a spectral
type bound for a physical bound nor assumes coefficient positivity after
complex dilation; that positivity is used only in the genuine C15
normalization and the absolute power-series domination.

Parent comparison: existing `PrimeBlindCarlsonThreshold` already proves
that a nonzero integer-blind spectral density cannot have critical
exp(pi|t|/2-K sqrt|t|) integrability. That result does not alone exclude
an exponential derivative moment: such a moment leaves G of positive
exponential type, not exp(O(sqrt|t|)). The physical Borel/dilation
transfer above is the additional bridge. Hadassi--Sodin2504.13104 uses
unimodular or uniformly nonvanishing Taylor coefficients; those premises
are unavailable here. He2609.38234 concerns a different carrier family
and almost every external parameter; its theorem does not apply to the
fixed divisor resonance or to these coefficients.

C25d extracts the strongest threshold furnished by this circular Borel
argument. Define the geometric constant

  b_* = inf{|zeta| : |Im exp(i*zeta)| >= 1/2}.

Continuity and compactness show that the infimum is attained and positive.
The bound used above gives b_*>1/3; zeta=pi/6 gives b_*<=pi/6<pi/2.
Every cancelling C15 probability must obey

  limsup_(k->infinity) w_k^(1/(2k)) >= 2b_*/pi.              (25.4)

Here k starts at1. To prove this, suppose the limsup rho is smaller.
The exact energy root gives limsup[((2k)!c_k)^(1/(2k))]=(pi/2)rho.
Choose b strictly between that value and b_*. The same Borel circle and
Mellin transport apply. Compactness of |zeta|=b gives
beta=2pi max_|zeta|=b |Im exp(i*zeta)|<pi, while
min_|zeta|=b Re exp(i*zeta)>0 since b<pi/2. These are exactly the two
bounds needed in (25.3). Carlson again contradicts F(1)=1. This proves
(25.4). In particular sum_k w_k R^(2k) diverges for every
R>pi/(2b_*), by the root test. This is the sharp boundary of this
circular-contour bound, not a claim that an actual cancelling sequence
exists at or above it. General C25a still asks for the stronger rho=1
(or, directly, absence of every exponential moment), and remains OPEN.
The boundary, its proof and its Lean status must accompany any later
retirement of the fast-tail route. Current status: PAPER ONLY.

### C26: uniform Gamma-order integer resonance (OPEN)

C23's fixed-order remainder does not exclude positive mixtures with unbounded
Gamma orders. Given the exact corpus and the current parent audit, the next
competing statements are:

C26a: there is an integer n0>=2 such that for every N>=4 and integer n>=n0,
R_N(n)>0. A nonnegative variant alone would need an additional strictness
argument on the support of each proposed mixture.
C26b: for every n0 there are N>=4 and integer n>=n0 with R_N(n)<0.
These statements concern the literal density and Fourier integral of C22;
no support or RH assumption is introduced. C26a would exclude every nonzero
positive mixture of normalized Gamma densities for which the mixture integral
exists, including unbounded orders. C26b would expose a moving-order regime
missed by the fixed-order resonance theorem. Neither statement settles the
unrestricted C15 coefficient cone.

[OPEN CORE]: uniform control in the coupled order/argument region. A minimum
occupied Gamma order exists, but a fixed-order little-o cannot be summed over
all larger orders. Neither coefficient positivity nor Gamma recurrence pays
that interchange. The positive-Taylor-coefficient shortcut to a real Borel
carrier is false: cosh(a*z)+cos(a*z) has nonnegative coefficients, zero quadratic
coefficient and nonzero quartic coefficient, so it cannot be a positive cosh
mixture on real rates. Its Borel singularities also include imaginary rates.
This elementary parent counterexample is not a counterexample to C25 or C26.
Verdict: SURVIVES PRELIMINARY ATTACK, no scientific novelty certification.

### C23 exact residue and endpoint-jet assembly (paper before Lean)

For a natural n put m=n+3, d=2m and p=d-2. The actual clearing product for
F_(n+4) has d distinct real roots r=-2(j+1),2j+3, 0<=j<m. Let

  a_r=r(r-1)/product_{v != r}(r-v),
  J_k=sum_r a_r product_{ell=0}^{k-1}(r-ell-1).

Lagrange interpolation of P(X)=X(X-1) gives its exact partial fraction
identity after evaluation away from the roots. In particular, on s=2+it,
q_(n+4)(s)=sum_r a_r/(s-r). This is the actual rational factor of the
already formalized spectralMellin_two, not an abstract replacement symbol.

For 0<=k<=p-1 use the monic polynomial
P_k(X)=X(X-1)product_{ell<k}(X-ell-1), of degree k+2<d.
The top-coefficient identity for Lagrange interpolation gives
J_k=coefficient_(d-1)(P_k). Consequently J_k=0 for k<p-1 and J_(p-1)=1.
All roots are distinct: roots on each side are injectively parametrized;
negative roots are at most -2 and positive roots are at least3. Thus every
residue denominator is nonzero, without a new premise.

For the actual piecewise monomial kernel phi in C23, the right endpoint jet
minus the left endpoint jet of order k is exactly J_k: differentiating u^(r-1)
at u=1 gives the displayed falling product. These identities pay every lower
boundary cancellation and the first nonzero boundary coefficient. They do
not by themselves pay piecewise integration by parts, Mellin inversion, or
uniformity in n. Lagrange interpolation and jump asymptotics are classical
parent mechanisms; this formal assembly is a BRIDGE.

### C27: moving-order phase rotation attacks C26 (OPEN)

The next endpoint coefficient exposes a coupled scale. With d=2N-2 and
p=d-2=2N-4, the same Lagrange argument, now applied after subtracting the
monic denominator, gives

  J_p = -p^2/2.

Indeed the denominator's root sum is d/2, while the monic numerator
X(X-1) product_(ell<p)(X-ell-1) has root sum1+p(p+1)/2.
Their next-coefficient difference is d/2-1-p(p+1)/2=-p^2/2.
This identity is a dependency-closed paper consequence, not yet audited Lean.
It prevents treating the first remainder constant as uniform in N.

The exact falsifiable conjecture C27 is: for integer sequences N_j>=4,
n_j>=2 tending to infinity, and N_j^2/n_j tending to c>0,

 R_(N_j)(n_j) /
  [16*pi^(9/2-2N_j)*n_j^(9/2-2N_j)*zeta(2N_j-4)^2]
       tends to cos(c/pi).

In particular c=pi^2 would force negative integer correlations and refute
C26a. This is a new conjecture derived from the actual endpoint coefficient,
not a proved asymptotic or an inference from fixed-order estimates. The
formal higher-jet expansion heuristically resums exp(-i*p^2/(4*pi*n));
its leading phase becomes c/pi. Neither that resummation nor its remainder
has been justified. [OPEN CORE]: a uniform actual-kernel inversion bound
and control of every omitted endpoint term for N~sqrt(n), followed by the
full divisor-sum estimate. The m>=2 terms have a strong m^(-p) factor only
if the moving-order remainder is uniformly paid. Current verdict:
SURVIVES PRELIMINARY ATTACK, scientific novelty unestablished.

### C27 uniform phase: dependency-closed PAPER proof

Retain N>=4,p=2N-4,d=p+2 and C_N from C23. Write P_N for the
inner polynomial phi_N, Q_N for its outer inverse-power expression, and
Delta_N(u)=Q_N(u)-P_N(u)=sum_r a_r u^(r-1), analytically for Re(u)>0.
Put H_N(w)=sum_r exp(r*w)/product_(v!=r)(r-v). Then

 Delta_N(exp(w))=exp(-w)*(H_N''(w)-H_N'(w)).

The Genocchi–Hermite formula (de Boor, Divided Differences,2005, equation52,
including its barycentric form) gives

 H_N(w)=w^(p+1)/(p+1)! * E exp(w*U_N),
 U_N=sum_(r) theta_r*r,

where theta is uniform probability on the (d-1)-simplex. The formula holds
for complex w by applying the real-node identity to exp(w*x), or analytic
continuation. The normalization is simplex volume1/(d-1)!.
The elementary simplex moments are E theta_r=1/d,
E theta_r^2=2/[d(d+1)], E theta_r theta_v=1/[d(d+1)] for r!=v;
they follow by successive beta integrals (or two integrations of monomials).
Consequently E U_N=1/2, |U_N|<=2N and
Var(U_N)=sum_r(r-1/2)^2/[d(d+1)]<=4N^2/(d+1)=O(N).
Differentiation under this compact integral is valid to every order. Thus

 Delta_N(exp(w))=exp(-w)*w^(p-1)/(p-1)! *
 E[exp(w*U_N)*(1+(2U_N-1)*w/p+(U_N^2-U_N)*w^2/[p(p+1)])].    (27.1)

For v>=0 put w=log(1+i*v), principal branch. Here |w|<=v, proved by
integrating i/(1+i*t) on0<=t<=v, and Re(w)=log(1+v^2)/2.
Since p>=N and |U_N|<=2N, (27.1) gives the uniform bound

 |Delta_N(1+i*v)| <= C*v^(p-1)/(p-1)! *(1+v)^2*exp(2N*v),    (27.2)

with one absolute C: bound exp(Re(w)U_N) by (1+v^2)^N and use
log(1+v^2)<=2v. The latter follows from derivative2v/(1+v^2)<=2.
On0<=v<=K/N, E|U_N|<=1/2+sqrt(Var U_N)=O(sqrt N) and
|exp(w U_N)-1|<=|w U_N| exp(max(0,Re(w)U_N)) show that the expectation
in (27.1) is1+O_K(N^(-1/2)), uniformly. The two polynomial corrections
are O_K(1/N), even using the deterministic bound on U_N.
Taylor's formula for log on a fixed disk about1 gives

 log(log(1+i*v)/(i*v))=-i*v/2+O(v^2),

with the ratio defined as1 at v=0. The remainder bound follows from the
convergent power series on, say, |v|<=1/2. Since p=O(N), (27.1) yields

 Delta_N(1+i*v)=(i*v)^(p-1)/(p-1)! *
                [exp(-i*p*v/2)+O_K(N^(-1/2))], 0<=v<=K/N.  (27.3)

For each fixed N and x>0, rectangular contour shifts give the exact identity

 L_N(x)=C_N Re[ i*exp(2*pi*i*x) *
                    integral_0^infinity Delta_N(1+i*v) exp(-2*pi*x*v)dv ]. (27.4)

To check every discarded term: integrate the polynomial P_N around the
rectangle0,1,1+iR,iR; its top tends to zero exponentially. Its integral
on the imaginary axis is purely imaginary because P_N is an even polynomial
with real coefficients. For Q_N shift1..infinity to1+i[0,infinity): each
monomial is O_N(|u|^-3), so the remote vertical edge is O_N(R^-3/x), and
the upper horizontal edge vanishes. All remaining vertical integrals
converge by polynomial growth against exp(-2*pi*x*v). These identities
use fixed N; their exact equality introduces no hidden uniform remainder.

Now let N->infinity and integer n->infinity with N^2/n->c>0; set z=2*pi*n.
The probability density z^p v^(p-1) exp(-z*v)/(p-1)! has mean p/z and
variance p/z^2 (ordinary Gamma integrals). On this probability space,
(p/2)*v - p^2/(2z) tends to zero in L2, since p^3/z^2->0.
Also p^2/(2z)->c/pi. Thus the expectation of exp(-i*p*v/2) tends to
exp(-i*c/pi), using |exp(i*a)-exp(i*b)|<=|a-b|.

The tail v>K/N in (27.3) is controlled, not discarded. Choose fixed K
larger than the eventual means N*p/z. Chebyshev gives probability of
that tail tending to zero. Cauchy–Schwarz, (27.2), and the bounded quantity
E[exp(4N*v)*(1+v)^4] show its contribution tends to zero. This last bound
is explicit: expand the fourth power, integrate each Gamma moment at
rate z-4N>0, and use (z/(z-4N))^(p+4)=O_c(1), since z is bounded below
by a positive multiple of N^2. The same argument without a tail gives

 |L_N(x)|<=C_a*alpha_N*x^-p for every x>=a*N^2 and all sufficiently large N,
 alpha_N=C_N*(-1)^(p/2)*(2*pi)^-p=8*pi^(7/2-2N)>0.       (27.5)

In (27.4), exp(2*pi*i*n)=1 and i*i^(p-1)=(-1)^(p/2).
Equations27.2–27.4 therefore prove
L_N(n)/(alpha_N*n^-p)->cos(c/pi).
Finally apply the exact identity23.3 and bound EVERY m>=2 term by27.5:

 sum_(m>=2) d(m)*m^-p <= 2^(-p/2)*zeta(p/2)^2 ->0.

For p>=4 the latter zeta factor is at most zeta(2)^2 by its positive
Dirichlet series. Also zeta(p)^2->1 by the same bound. This proves C27
with the exact stated normalization. Taking integers n nearest N^2/pi^2
makes the limiting cosine -1. Hence C26a is FALSE on paper; arbitrarily
late negative integer rows occur at growing Gamma order.

Positive survivor: the complete moving-order phase law, including uniform
all-divisor control, not merely a negative example. Full Lean formalization
is pending; C26 is NOT retired yet. The parent mechanism is classical
Genocchi–Hermite concentration plus contour rotation; scientific novelty
of the actual-family asymptotic is not certified by this proof.

### C28: every fixed positive Gamma mixture still resonates (PAPER)

C27 kills uniform signs, but does not kill eventual signs for a fixed
mixture. The stronger positive survivor is: for every probability (v_N)
on integers N>=4, with no extra moment condition,

 sum_N v_N*R_N(n)/R_N(1) > 0 for every sufficiently large integer n.

The sum exists absolutely because each normalized correlation has modulus
at most1. This statement excludes every positive mixture of this Gamma
family from C15, but not an arbitrary positive-Taylor-coefficient mixture.

Here is the uniform estimate that pays the formerly missing infinite tail.
Fix an integer M>=5, set a=2M-6 and sigma=a+1/2. Define
H_N(s)=Gamma(N+1/4)^2 * spectralMellin N s. For N>=M, Gamma recurrence gives

 H_(N+1)(s)=H_N(s)*A^2/[A^2-((s-1/2)/2)^2], A=N+1/4.

On s=sigma+i*t, the denominator's modulus is at least A^2-a^2/4>0.
Hence |H_N(s)|<=C_M |H_M(s)| uniformly in N>=M and t, where
C_M=product_(j>=M)(1-a^2/[4(j+1/4)^2])^-1 is finite. To verify finiteness,
each fraction is uniformly below1 and their sum converges; bound
-log(1-u)<=u/(1-q) for0<=u<=q<1. This is not an assumed uniform Stirling
estimate in two growing parameters.

The fixed-order symbol23.1 at this sigma>1 and bounded Dirichlet zeta
series gives |H_M(sigma+i*t)|=O_M(|t|^-2): sigma+7/2-2M=-2.
There are no genuine poles because spectralMellin is entire. For each N>=M,
shift its Fourier/Mellin line from1/2 to sigma. On1/2<=Re(s)<=2 the C23
fractional-part zeta bound makes horizontal edges vanish. On2<=Re(s)<=sigma
the bounded zeta series and fixed-N Stirling give at least |t|^-2 at the
upper edge. Thus the exact shifted identity gives

 |Gamma(N+1/4)^2 R_N(x)| <= C'_M*x^-a, x>=1, N>=M.    (28.1)

For the normalization, Euler's absolutely convergent Gamma integral gives
|Gamma(A+i*t/2)|<=Gamma(A) for A>0. Therefore
Gamma(N+1/4)^2 R_N(1)>=integral |XiC(t)|^2 dt=:Z>0.
The integral is finite by the actual kernel's Plancherel/Gamma decay;
it is positive because XiC is continuous and not identically zero.
Equivalently its positivity follows from the already defined E_0>0.
Consequently (28.1) yields one C''_M with

 |R_N(x)/R_N(1)|<=C''_M*x^(-(2M-6)), x>=1,N>=M.       (28.2)

For a fixed nonzero probability, let N0 be its smallest occupied index.
C23 gives R_(N0)(n)/R_(N0)(1)~b*n^(-(2N0-9/2)), b>0.
Apply28.2 with M=N0+1 to the complete higher-order tail; its absolute
value is at most C''_M*n^(-(2N0-4))*sum_(N>N0)v_N.
This is smaller by n^-1/2 than the strictly positive leading term
v_(N0)*b*n^(-(2N0-9/2)). Thus the claimed eventual positivity follows.
Every interchange has now been paid; no exponential or logarithmic moment
of v is required. Classification: PAPER BRIDGE; actual-family scientific
novelty uncertified. Full formalization, including C23 inversion, is pending.

### C29: a coefficient law beyond the Gamma cone (OPEN)

C28 suggests testing coefficient regularity directly. Define the explicit
probability w_k=1/[zeta(2)*(k+1)^2], k>=0, and its actual correlation
S(n)=sum_k w_k*A(n,k)/E_k. It has finite logarithmic moment and the row
sum exists absolutely because |A(n,k)|<=E_k.

Exact conjecture: n^(3/2)*log(n)*S(n) tends, along integers, to
2*zeta(2)/pi^2>0. More generally, for probabilities with
w_k~C*k^(-alpha),1<alpha<5/2, conjecture

 n^(alpha-1/2)*log(n)*S(n) -> C*(pi^2/2)^(1-alpha)*zeta(alpha)^2.

The predicted constant comes from the ACTUAL C17 signed Gaussian profile:
write kappa=pi^2/2, T=(2k+7/2)/(pi/2). On the band k~kappa*x,
K_k(x)/E_k~sqrt((pi/2)/T)*J_a(u)/log(T), and dk/du~-(pi/4)*sqrt(T).
The signed profile integral2*pi/sqrt(a) gives total coefficient kappa.
Then the actual divisor identity predicts
sum_k w_k*K_k(x)/E_k~kappa*w_(kappa*x)/log(x).
Summing over the literal multiples mn gives the stated zeta(alpha)^2.
This is not yet a proof: [OPEN CORE] make the order sum uniform, pay its
small/large-order tails and the full divisor interchange from C17's
available global envelope. The range alpha<5/2 is chosen so that the
current fourth-power envelope can control the low-order tail; it is not
asserted as a sharp mathematical boundary. A failure would locate a
missing oscillatory or nonuniform contribution. Current verdict:
SURVIVES PRELIMINARY ATTACK, no scientific novelty claim. Unrestricted
C15 remains open even if every displayed power law is eventually positive.

### C29 paper closure: signed approximate identity in derivative order

The same proof gives the wider range1<alpha<4. Suppose a probability has
w_k~C*k^-alpha,C>0. Retain the actual C17 paper profile and global bound,
including E_k~b_k*sqrt(T_k/a)*log(T_k), a=pi/2. Let kappa=pi^2/2.
For all sufficiently large k and x>=2 these give

 |K_k(x)|/E_k <= C0/[sqrt(k)*log(k)] *
             (1+|k-kappa*x|/sqrt(k))^-4.                  (29.1)

Changing the affine offset in T_k alters C0 only; T_k is comparable to k.
The finitely many smaller k are bounded by C1*exp(-r*x), with any fixed
0<r<2pi, by the already proved fixed-order kernel envelope. Set
F(x)=sum_k w_k*K_k(x)/E_k.

We first pay absolute convergence and both remote order ranges. In
kappa*x/2<=k<=2*kappa*x, (29.1) and w_k<=C2*k^-alpha give

 sum w_k*|K_k(x)|/E_k <= C3*x^-alpha/log(x),

since the sum of (1+|k-kappa*x|/sqrt(x))^-4 is O(sqrt(x)). This elementary
sum bound follows by partitioning the distance into successive intervals
of length sqrt(x), each containing at most sqrt(x)+1 integers.
The part with |k-kappa*x|>L*sqrt(x) in this middle range is bounded by
the same quantity times O((1+L)^-3), by summing the integral tail of
(1+u)^-4.

For k<kappa*x/2 the envelope is at most C*k^(3/2)/[x^4*log(k)].
Thus the entire low-order contribution, apart from the finite exponential
head, is bounded by

 C4*x^-4 * sum_(k0<=k<=kappa*x/2) k^(3/2-alpha)/log(k)
 <= C5*x^-4 * [1+x^max(5/2-alpha,0)*log(x)].

The last inequality follows by integral comparison, treating exponent -1
by a logarithm; replacing1/log(k) by a constant only enlarges the bound.
After multiplication by x^alpha*log(x), this tends to zero for every
alpha<4, including alpha=5/2. For k>2*kappa*x, (29.1) is at most
C*k^(-5/2)/log(k), so the weighted sum is O(x^(-alpha-3/2)/log(x)), also
negligible. These bounds prove, after absorbing a finite x interval,

 sum_k w_k*|K_k(x)|/E_k <= C6*x^-alpha/log(x), x>=2.    (29.2)

From this point through (29.3), x tends to infinity through POSITIVE
INTEGERS. The real-argument kernel retains exp(-2*pi*i*x) in its saddle
phase; omitting that phase away from integers would be false. Bounds
(29.1) and (29.2) hold for real x, but the signed profile used next is the
integer profile. Every argument m*n in the divisor assembly is an integer.
On |k-kappa*x|<=L*sqrt(x), the actual C17 convergence is uniform; the
assumed coefficient asymptotic and the energy asymptotic are also uniform
because every k in this band tends to infinity. Write
u_k=(2*pi*x-T_k)/sqrt(T_k). Its mesh is
u_(k+1)-u_k=-(2/a)/sqrt(2*pi*x)*(1+o(1)), uniformly in the band.
Hence the usual Riemann sums, justified by continuity of J_a, give

 x^alpha*log(x)*F(x) ->
 C*kappa^-alpha*(a*sqrt(a)/2)*integral_R J_a(u)du
 =C*kappa^(1-alpha).                                  (29.3)

Here first x->infinity at fixed L, then L->infinity. The middle-range
O((1+L)^-3) estimate and the two remote-order estimates justify this
order of limits. The full signed integral is2*pi/sqrt(a), not its
absolute value; it yields the positive constant pi*a=kappa.

For each integer n>=2, use29.2 to pay the entire double series:

 sqrt(n)*sum_(m>=1)d(m)*sum_k w_k*|K_k(m*n)|/E_k
 <=C6*n^(1/2-alpha)/log(n)*sum_m d(m)*m^-alpha<infinity.

Thus the fixed-order divisor identities may be summed with exact Fubini,
so S(n)=sqrt(n)*sum_m d(m)*F(m*n). After multiplying by
n^(alpha-1/2)*log(n), each summand tends by29.3 to
C*kappa^(1-alpha)*d(m)*m^-alpha. The same summable expression with a
constant dominates every summand, since log(n)<=log(m*n). Dominated
convergence and sum d(m)/m^alpha=zeta(alpha)^2 prove

 n^(alpha-1/2)*log(n)*S(n) ->
 C*kappa^(1-alpha)*zeta(alpha)^2>0, 1<alpha<4.          (29.4)

For the literal w_k=1/[zeta(2)*(k+1)^2], this is exactly the C29 limit
2*zeta(2)/pi^2. Every displayed probability has finite logarithmic moment.
Therefore no C15 cancelling probability can have a positive power-law
asymptotic with exponent in(1,4). This does not exclude irregular tails,
faster polynomial tails, or the full C15 cone. No arbitrary weight is
assumed to have such an asymptotic.

Status: dependency-closed PAPER bridge through the previously completed
C17 paper proof. C17's complete global profile and C29 remain unformalized;
G5–G7 alone are not being presented as that global theorem. Classical
signed approximate-identity reasoning is the parent mechanism, and
scientific novelty of this exact arithmetic law remains unestablished.

## C30: square-root coefficient modulation (new competing conjectures)

Let 1<alpha<4, C>0, L>0, and let h be a continuous nonnegative
L-periodic function with positive mean hbar. Consider an actual C15
probability with w_k=C*k^-alpha*h(sqrt(k))+o(k^-alpha) as k->infinity.
This includes coefficient oscillations at exactly the width resolved by
C17, and is not a power-law asymptotic unless h is constant.

C30a: the Cesaro mean of the normalized ACTUAL correlations obeys

 (1/X) sum_(2<=n<=X) n^(alpha-1/2)*log(n)*
       sum_k w_k*A(n,k)/E_k
 -> C*(pi^2/2)^(1-alpha)*zeta(alpha)^2*hbar > 0.

C30b: some such positive modulation cancels every integer correlation.
They are incompatible. The first OPEN CORE is the signed order-profile
transfer retaining the moving phase h(sqrt(k)); pointwise positivity of
that transfer is neither asserted nor needed. The strongest parents are
C17's actual signed profile, C29's complete absolute order/divisor budget,
and classical periodic averaging. Internal searches returned no applicable
stronger result (partial coverage is recorded separately). Initial verdict
BRIDGE: no scientific novelty certificate, but this tests the actual
remaining coefficient freedom rather than adding a deficit premise.

### Dependency-closed paper proof of C30a

Put a=pi/2, kappa=pi^2/2, b=sqrt(a/8), I=integral_R J_a=2*pi/sqrt(a), and

 (Th)(theta)=I^-1 integral_R J_a(u)*h(theta-b*u) du.

The absolutely integrable signed Gaussian J_a and bounded uniformly
continuous periodic h make Th continuous and L-periodic; Fubini gives
its mean exactly hbar. No positivity of Th is used.

The coefficient hypothesis implies w_k<=C0*k^-alpha eventually, so all
absolute estimates29.1--29.2 still hold. The o(k^-alpha) error contributes
o(x^-alpha/log x): on the middle band its relative supremum tends to zero,
and the two remote-order estimates in C29 pay the rest. On each fixed
|k-kappa*x|<=R*sqrt(x), x an integer, the exact saddle coordinate gives

 sqrt(k)=sqrt(kappa*x)-b*u_k(x)+o(1),

uniformly there, because k=(a*T_k-7/2)/2 and
u_k=(2*pi*x-T_k)/sqrt(T_k). Taylor expansion of sqrt at kappa*x yields
b=a*sqrt(2*pi)/(4*sqrt(kappa))=sqrt(a/8). Uniform continuity of h pays the
replacement even though sqrt(kappa*x) has no limit. C17 and the uniform
Riemann-sum argument of C29 consequently give

 x^alpha*log(x)*F(x)
 = C*kappa^(1-alpha)*(Th)(sqrt(kappa*x))+o(1)          (30.1)

as INTEGERS x->infinity. Uniform continuity is uniform in the moving
phase; the O((1+R)^-3) absolute tail removes the cutoff R. This proves
(30.1) without selecting any phase subsequence.

The absolute divisor budget29.2 permits Fubini exactly as before. With
D(n)=n^(alpha-1/2)*log(n)*sum_k w_k*A(n,k)/E_k, it gives

 D(n)=C*kappa^(1-alpha)*sum_(m>=1)d(m)*m^-alpha*
                  (Th)(sqrt(kappa*m*n))+o(1).         (30.2)

To pay this infinite asymptotic, first restrict m<=M; then30.1 applies
termwise and log(n)/log(m*n)->1. Both complete tails are uniformly bounded
by a constant times sum_(m>M)d(m)*m^-alpha, which tends to zero. The same
argument proves D(n) uniformly bounded.

For every continuous L-periodic g and c>0,

 X^-1 sum_(1<=n<=X) g(c*sqrt(n)) -> L^-1 integral_0^L g.

Here is an elementary proof without invoking an unverified equidistribution
lemma. Approximate g uniformly by a continuously differentiable periodic
function (periodic convolution with a positive smooth approximate identity).
For such a function, comparison of its value at n with its integral over
[n,n+1] costs at most sup|g'|*c/(2*sqrt(n)); the total cost is O(sqrt(X)).
For the integral put y=c*sqrt(t), dt=2*y/c^2 dy. If g0=g-mean(g), its
primitive is bounded and periodic. Integration by parts gives
integral_0^Y y*g0(y)dy=O(Y), so the integral average error is O(X^-1/2).
Uniform approximation removes differentiability and proves the claim.

Apply this with g=Th and c=sqrt(kappa*m) for each fixed m. In30.2,
absolute summability of d(m)*m^-alpha and boundedness of Th pay interchange
with the Cesaro limit. Its value is exactly C*kappa^(1-alpha)*zeta(alpha)^2*
hbar>0, proving C30a and disproving C30b. Since D is bounded, positivity
of its mean also gives some delta>0 for which {n:D(n)>delta} has positive
lower density: split the mean into that set and its complement and use
the uniform upper bound on D. Thus infinitely many actual integer rows
are positive. No eventually-positive claim is made for every modulation.

Status: dependency-closed PAPER BRIDGE through unformalized complete C17.
This excludes the specified modulated class from C15, not arbitrary
irregular weights. Do not retire C30b before formalizing the exact positive
survivor. Novelty/significance beyond the parent methods remain uncertified.

## G8: actual rational-kernel Mellin integral, paper proof before Lean

Retain actual pole/residue/kernelInner/kernelOuter from GammaKernelJets,
with N indexing Gamma order N+4. Define phi_N(x)=kernelInner N x for x<=1,
and kernelOuter N x for x>1. For -2<Re(s)<3,

 integral_0^infinity x^(-s)*phi_N(x) dx
   = sum_r residue(N,r)/(s-r).

Absolute admission is independent of this value identity. Each inner
term is -a_r*x^(r-1-s), r=2j+3>=3; its exponent has real part greater
than -1, so its integral on(0,1] is -a_r/(r-s)=a_r/(s-r).
Each outer term has r=-2j-2<=-2 and exponent with real part below -1;
its integral on(1,infinity) is -a_r/(r-s)=a_r/(s-r).
There are finitely many terms; finite-sum integral interchange and the
split at1 are therefore justified by absolute integrability. In particular
s=0 proves phi_N integrable and s=2+i*t gives, by the already formal
rationalSymbol_two, s(s-1)/clearingProduct(N+3,s). The actual kernel,
not an assumed inverse-transform model, is used throughout. This is a
classical Mellin bridge needed for the pending cosine inversion, not the
full C23 resonance theorem or the deficit producer.

## C31: weak positive coefficient mass without regularity (CONJECTURE)

C30 leaves arbitrarily rapid and aperiodic oscillations. Let1<alpha<4 and
let w be an actual probability with w_k<=C*(k+1)^-alpha. No asymptotic,
periodicity, continuity or lower bound is imposed on its coefficients.
For any smooth compactly supported psi:(0,infinity)->R, conjecture

 (1/X) sum_(n>=2) psi(n/X)*n^(alpha-1/2)*log(n)*S(n)
 - kappa^-alpha/X * sum_(k>=1) k^alpha*w_k*
          sum_(m>=1) d(m)*m^(-alpha-1)*psi(k/(kappa*m*X)) -> 0. (31.1)

Here S(n)=sum_k w_k*A(n,k)/E_k and kappa=pi^2/2. Both sums must be paid
in the actual C17 kernel, not imposed as a new premise. If true, C15 exact
cancellation forces X^-1 sum_(X<=k<=2X) k^alpha*w_k ->0: choose psi>=0
positive on[1,2] and use the m=1 part of the nonnegative right side,
rescaling X by kappa. This tests arbitrary oscillations, beyond C30.
The competing conjecture C31b is a cancelling polynomially bounded
probability with positive limsup of this dyadic coefficient mass.
[OPEN CORE]: prove the weak profile transfer uniformly over every k and
pay the complete divisor tail before asserting31.1.

### C31 dependency-closed weak-transfer proof (PAPER)

Choose0<A<B with supp(psi) subset[A,B]. C29's absolute budget, which uses
only the coefficient upper bound, bounds the m-th summand of the left
side of31.1 by C_psi*d(m)*m^-alpha uniformly in X>=2. The right side has
the same bound: k^alpha*w_k<=C and psi(k/(kappa*m*X)) is supported in an
interval with O(m*X) integers. Thus both infinite m-tails are uniformly
summable; it suffices to fix m.

For this fixed m, put n0=T_k/(2*pi*m). On k in any fixed compact multiple
of X, define

 B_(k,m,X)=sum_n psi(n/X)*n^alpha*log(n)*K_k(m*n)/E_k.

The exact local C17 profile applies because m*n is an integer. Its n-mesh
in u=(2*pi*m*n-T_k)/sqrt(T_k) is2*pi*m/sqrt(T_k). On |u|<=R, the smooth
factor psi(n/X)*n^alpha*log(n) differs from its value at n0 by
O_R(X^(alpha-1/2)*log X), uniformly in these k; extend psi by zero off its
compact support. Energy asymptotics and Riemann sums then give, uniformly
in k in this range,

 B_(k,m,X)= (1/m)*n0^alpha*psi(n0/X)*log(n0)/log(T_k)
             +o(X^alpha).

The constant is exactly sqrt(a)*integral J_a/(2*pi*m)=1/m. The normalized
absolute u-tail is O((1+R)^-3) by the global profile bound; first X->infinity
and then R->infinity pay it uniformly. Since m is fixed,
n0=k/(kappa*m)+O_m(1) and log(n0)/log(T_k)->1. Therefore

 B_(k,m,X)= k^alpha/(kappa^alpha*m^(alpha+1))*
                 psi(k/(kappa*m*X))+o(X^alpha),       (31.2)

uniformly on that compact k-range. Summing its error with w_k<=C*k^-alpha
and dividing by X makes it o(1).

It remains to justify excluding k outside a compact multiple of X.
For n in[A*X,B*X], choose the compact k-range large enough that outside
it either k<kappa*m*n/2 or k>2*kappa*m*n for every such n.
C29's low-order bound gives, after n^alpha*log(n) normalization,
O(X^(alpha-4)*log X*[1+X^max(5/2-alpha,0)*log X])+o(1), tending to zero
for1<alpha<4. Its high-order bound gives O(X^-3/2). These estimates are
uniform in n in the displayed interval, so averaging O(X) such integers
keeps them negligible. The finite low-order head has exponential decay.
The right side vanishes outside the chosen compact range. This pays every
k-tail and proves31.2 after summation, hence31.1 after the already paid
m-tail limit.

If all actual S(n) vanish, use a nonnegative psi with psi>=1 on[1,2].
The nonnegative right side of31.1 tends to zero. Its m=1 part bounds
kappa^-alpha/X * sum_(kappa*X<=k<=2*kappa*X) k^alpha*w_k.
Rescale X to obtain the asserted zero dyadic coefficient mass. C31b is
therefore FALSE on paper with31.1 as positive survivor; no route retirement
until its full actual analytic proof is formalized. This result needs no
regularity or asymptotic shape of the coefficients, but does retain the
explicit polynomial upper bound1<alpha<4. Very sparse, slower or faster
tails are not universally excluded. Verdict PAPER BRIDGE; scientific
novelty beyond classical weak approximate-identity methods unestablished.

### G8 inverse Mellin recovery, additional paper proof before Lean

The actual piecewise kernel is continuous: both finite monomial pieces
are continuous on their relevant half-lines and their values at1 agree
by the proved zeroth endpoint jump. The inner exponents are nonnegative,
so its extension through0 is continuous as well.

For s=2+i*t every pole r is real and |2-r|>=1. Thus
|s|>=sqrt(1+t^2) and |s-r|>=sqrt(1+t^2). The already proved zeroth residue
sum is zero. Therefore the actual rational symbol is

 q_N(s)=sum_r a_r*(1/(s-r)-1/s)
       =sum_r a_r*r/[s*(s-r)],

and |q_N(2+i*t)|<=sum_r|a_r*r|/(1+t^2), an integrable bound.
The reflected transform M(phi)(-1+i*t)=q_N(2-i*t) has the same absolute
admission. Standard Mellin inversion at real part -1, justified by the
proved absolute physical and vertical integrals and continuity, gives

 phi_N(x)=(1/(2*pi))*integral_R x^(1+i*t)*q_N(2+i*t)dt, x>0.

Changing t to -t reconciles this expression with the standard Mellin
convention. This is recovery of the literal rational kernel only; cosine
transformation and the actual Xi-density contour shift are still owed.

## C32: critical stretched-exponential phase (OPEN; incompatible tests)

C29--C31 remove many polynomial tails, while C25 obstructs sufficiently
fast exponential tails. The actual signed Gaussian suggests testing the
intermediate resolving scale, rather than repeating another regularity
no-go. Fix tau>0 and alpha>1, and let the literal probability be

 w_k = C_(alpha,tau)*(k+1)^(-alpha)*exp(-tau*sqrt(k)), k>=0,

where C is the reciprocal of the finite positive sum. It has every
polynomial moment and no positive exponential k-moment. Thus the proved
restricted obstructions do not decide it. Let S(n) be its actual C15 row.
Conjecture C32a is the exact integer asymptotic

 n^(alpha-1/2)*log(n)*exp(tau*sqrt(kappa*n))*S(n)
 -> C_(alpha,tau)*kappa^(1-alpha)*exp(tau^2/16)*cos(pi*tau^2/32). (32.1)

C32b asserts failure for some alpha>1,tau>0 (in particular a remote
order range or divisor tail changes this leading term). The first phase
zero predicted by32.1 is tau=4. This is NOT a conjecture of complete
cancellation at tau=4: a zero leading term leaves all lower orders and
all finite rows unresolved. If true, varying tau permits eventual
negative correlations in explicit infinite positive mixtures and locates
an exact resonance boundary beyond the already excluded classes.

The local evidence is an exact elementary Gaussian identity, not evidence
that the global asymptotic is proved. With b=sqrt(a/8), the square-root
coefficient ratio at the C17 saddle is exp(tau*b*u). Direct completion of
the square in the explicit J_a gives, for real lambda,

 (integral J_a(u)*exp(lambda*u)du)/(integral J_a)
   =exp(lambda^2/(2*a))*cos(lambda^2/2).

Indeed J_a(u)=Re[C_a*exp(-gamma*u^2/2)] with
Re(gamma)>0, 1/gamma=1/a+i, and C_a*sqrt(2*pi/gamma)=2*pi/sqrt(a).
The absolutely convergent complex Gaussian integral therefore gives the
identity. Setting lambda=tau*b produces exactly exp(tau^2/16)*
cos(pi*tau^2/32). If the full kernel mixture shared this local asymptotic,
all divisor m>=2 would be exponentially smaller than m=1; hence32.1 has
no zeta(alpha)^2 factor. The tau->0 and n->infinity limits need not commute.

[OPEN CORE]: prove a GLOBAL exponentially accurate relative order bound
for the ACTUAL kernel mixture, including all k far below/above kappa*n
and all divisor indices. C17's polynomial fourth-power envelope does NOT
pay this: after division by exp(-tau*sqrt(kappa*n)), its low-order bound
can diverge. No dominated-convergence conclusion is currently valid.
The exact candidate and its negation remain open after current corpus
and external searches. Parent Gaussian algebra is classical; novelty of
32.1 is uncertified. A proof or counterexample must attack the remote
order range before any Lean asymptotic claim.

### C32 global relative bound and paper closure

The missing low-order range can be paid without pretending the old
polynomial envelope is exponential. This proof uses the exact G5 transform,
C17's energy/local asymptotics, and the actual complex K0 dilation from C25.
All constants below are fixed; k is sufficiently large unless explicitly
stated otherwise. Set p=2k+7/2, T=p/a, b=T^p*exp(-a*T), a=pi/2.

**Uniform right-shift bound.** For0<=delta<=epsilon*T, sigma=1/2+delta,
there are fixed epsilon,C>0 such that

 integral_R |M_k(sigma+i*t)|dt
 <= C*b*sqrt(T)*(T/(2*pi))^delta*exp(C*delta^2/T).       (32.2)

Here M_k(s)=(-1)^k(s-1/2)^(2k)*G(s),
G(s)=s^2(s-1)^2*pi^-s*Gamma(s/2)^2/4, the literal proved transform.
To prove32.2, uniform sectorial Stirling and digamma remainders on Re(z)>=1/4
(DLMF5.11.1--3, error bounds5.11(ii), with sector distance pi/2) imply

 |Gamma(z)| <= C*|z|^(Re(z)-1/2)*exp(-Re(z)-Im(z)*arg(z)),
 Re(psi(z)) <= log|z|+C/|z|.

The compact part |z| bounded is absorbed into C since this half-plane has
no Gamma poles. These are joint bounds, not fixed-parameter ratio expansions.
For t>=T/2, integrating the digamma inequality horizontally from1/4+i*t/2
through delta/2 gives

 log |Gamma((1/2+delta+i*t)/2)/Gamma((1/2+i*t)/2)|^2
 <= delta*log(t/2)+C*(delta^3+delta)/t^2+C*delta/t.

Indeed the logarithmic correction is bounded by
integral_0^delta (u+1/2)^2/(2*t^2)du and the remainder by C*delta/t.
Since delta<=epsilon*T, its extra terms are at most C+C*delta^2/T.
The factor |delta+i*t|^(2k)/t^(2k) is at most exp(k*delta^2/t^2),
and the degree-four polynomial factor of G changes by a bounded ratio.
Critical-line Stirling now bounds this part of the integral by

 C*(2*pi)^(-delta)*exp(C*delta^2/T)*
           integral_0^infinity t^(p+delta)*exp(-a*t)dt.

The last integral is <=C*b*sqrt(T)*T^delta*exp(C*delta^2/T).
For completeness, its exact Gamma value reduces this to
Gamma(p+delta+1)/Gamma(p+1)<=p^delta*exp(C*(delta+delta^2)/p),
obtained by integrating psi(u)<=log(u)+C/u on[p+1,p+delta+1];
ordinary real Stirling gives Gamma(p+1)/a^(p+1) comparable to b*sqrt(T).
The harmless delta/T term is absorbed into a constant plus delta^2/T.

For0<=t<=T/2 use the full sectorial bound directly. With u=t+delta+1,
|s| and |s-1| are <=u, |s-1/2|<=u, and |s|>=c*u. The possibly negative
Gamma power sigma-1 is bounded below by -1/2, so this comparison costs
only a fixed constant. Also t*arctan(sigma/t)<=sigma, hence the exponential
Gamma factor is at most exp(-a*t). Therefore

 |M_k(sigma+i*t)| <= C*(2*pi)^(-delta)*u^(p+delta)*exp(-a*t).

Choose epsilon small and T large so u<=3*T/4. Substitute u, use
u^delta<=T^delta, and apply the elementary lower Gamma-tail bound
integral_0^(3T/4) u^p*exp(-a*u)du <= C*b*sqrt(T)*exp(-c*T).
This bound follows from log(v)-v+1<0 uniformly on0<v<=3/4,
with the integrable small-v tail bounded by v^(p/2). The substitution costs
exp(a*(delta+1)); decreasing epsilon so a*epsilon<c/2 leaves exponential
decay. This proves32.2 on the entire low-height interval. Conjugation pays
negative heights. No hidden compact-height error remains.

Mellin inversion holds for each positive sigma by G5 absolute admission,
Gamma vertical decay, and continuity of the actual kernel. Divide32.2
by E_k~b*sqrt(T/a)*log(T). For x>=T/(2*pi), obtain

 |K_k(x)|/E_k <= C/[sqrt(x)*log(T)] *
     exp(-delta*log(2*pi*x/T)+C*delta^2/T).             (32.3)

Optimize with delta=min(epsilon*T, T*log(2*pi*x/T)/(2*C)), increasing C
if needed. For each fixed M, on T/(2*pi)<=x<=M*k this proves

 |K_k(x)|/E_k <= C_M/[sqrt(k)*log(k)]*
             exp(-c_M*(k-kappa*x)^2/k).               (32.4)

The affine offset T=(2k+7/2)/a changes constants only. The bounded sliver
k/kappa<=x<T/(2*pi) has width O(1) and is covered by32.3 with delta=0
(the same inequality before imposing x>=T/(2*pi)). Thus32.4 holds for
k/kappa<=x<=M*k. It is a one-sided bound, which is exactly what is needed.

**The far low-order range.** Fix0<theta<pi/2. The actual C25 complex
Bessel formula gives K0 holomorphic on the right-half-plane dilations
x*exp(z), |z|<=theta, with

 sup_(|z|=theta) |exp(z/2)*K0(x*exp(z))| <= C*x^4*exp(-c*x), x>=2,

because Re(x*exp(z))>=exp(-theta)*cos(theta)*x>0; fixed-order Bessel
sectorial decay is uniform on this compact angular sector. The exact
identity K_k=(-1)^k(D+1/2)^(2k)K0 and Cauchy's derivative estimate give

 |K_k(x)| <= C*(2k)!*theta^(-2k)*x^4*exp(-c*x).

C17's energy asymptotic implies E_k>=c0*(2k)!*a^(-2k) for all k, after
absorbing the finitely many small k using E_k>0. Choose a fixed M large
enough that 2*k*log(a/theta)<=c*x/2 whenever x>=M*k. Absorb x^4 into
exp(c*x/4). Then

 |K_k(x)|/E_k <= C*exp(-c'*x), x>=max(2,M*k).           (32.5)

This includes k=0. It pays the entire finite and very-low-order head.
The Cauchy estimate is symbolic analysis, not numerical computation.

**Actual coefficient sum.** Fix alpha>1,tau>0 and the exact probability
from C32. For k<=x/M,32.5 bounds the complete weighted head by C*exp(-c'x).
For x/M<k<=kappa*x,32.4 gives, after dividing by
x^-alpha*exp(-tau*sqrt(kappa*x))/log x, a summable discrete majorant

 C*x^-1/2*exp(C_tau*v-c*v^2), v=(kappa*x-k)/sqrt(x)>=0.

For kappa*x<k<=2*kappa*x, the weight ratio exp(-tau*(sqrt(k)-sqrt(kappa*x)))
is <=1, so C17's polynomial envelope gives C*x^-1/2*(1+v)^-4.
For k>2*kappa*x the C29 high-order calculation is strengthened by
exp(-tau*sqrt(2*kappa*x)); its normalized total tends to zero.
These estimates both pay relative tails and yield the uniform absolute bound

 sum_k w_k*|K_k(x)|/E_k
 <= C*x^-alpha*exp(-tau*sqrt(kappa*x))/log x, x>=2.     (32.6)

Within a fixed square-root band, x an INTEGER, the already established
C17 profile, the actual energy asymptotic, and
sqrt(k)=sqrt(kappa*x)-sqrt(a/8)*u+o(1) apply uniformly. Riemann sums and
the just-paid relative tails prove

 x^alpha*log(x)*exp(tau*sqrt(kappa*x))*F(x)
 -> C_(alpha,tau)*kappa^(1-alpha)*exp(tau^2/16)*cos(pi*tau^2/32). (32.7)

Finally32.6 pays the full fixed-order divisor interchange. In
S(n)=sqrt(n)*sum_m d(m)*F(m*n), the m=1 term gives32.1. Every m>=2
vanishes after its normalization because of
exp(-tau*sqrt(kappa*n)*(sqrt(m)-1)); the summable majorant d(m)*m^-alpha
pays dominated convergence. This proves C32a on paper, including its zero
leading constants; C32b is FALSE on paper. No sign is inferred at a phase
zero. In particular tau=4*sqrt(2) has negative limiting constant, so this
explicit infinite positive mixture has eventually negative integer rows.

Status: dependency-closed PAPER BRIDGE, dependent on the complete C17
paper result and actual C25 dilation proof. Full formalization remains
owed. The new positive survivor is the exact phase law and the one-sided
exponential kernel estimate, not a universal cancellation no-go. C15 and
WP06 remain OPEN. Primary sectorial parent: https://dlmf.nist.gov/5.11 ;
Gaussian parent: https://dlmf.nist.gov/7.7#E3 ; actual Bessel sector bound:
https://dlmf.nist.gov/10.40 . No scientific novelty certification.

### C32 coefficient-tail classification and next critical test C33

The proof of32.6--32.7 uses only w_k~C*k^-alpha*exp(-tau*sqrt(k)),
C>0,alpha>1,tau>0, plus positivity and total probability. The asymptotic
supplies the required eventual upper bound, and its uniform relative error
on each square-root band tends to zero;32.6 pays that error outside the
band. Thus32.1 holds for EVERY such probability, with C in place of the
explicit normalizer. If it cancels every integer row, it must satisfy

 cos(pi*tau^2/32)=0, equivalently tau=4*sqrt(2*j+1) for some integer j>=0.

This is only a necessary tail condition in the specified asymptotic class.
It neither constructs a cancelling sequence nor constrains every C15
sequence to belong to that class.

New competing conjectures C33, after the C32 obstruction:
C33a: there exist alpha>1,C>0 and an actual C15 probability with
w_k~C*k^-alpha*exp(-4*sqrt(k)) that cancels every integer row n>=2.
C33b: no such probability exists. The positive leading obstruction is
exactly zero for this first remaining rate; C32 cannot choose between them.
[OPEN CORE]: actual subleading arithmetic response and simultaneous
finite-row interpolation under coefficient positivity. Leading Gaussian
phase cancellation is not exact row cancellation. In particular, no
all-order expansion for E_k is assumed from its first asymptotic; its
short-window arithmetic fluctuations must be paid before a next-term
sign claim. C33 is a direct construction/no-go question for C15, not an
extra hypothesis attached to the WP06 receiver. Current verdict:
SURVIVES PRELIMINARY ATTACK, with no novelty certificate or proof.


## C34: sparse exact cancellation inside the critical tail

Conjectures before proof. For every alpha>1 and every prescribed integer
threshold sequence B_j, C34a asserts existence of integers n_j>=max(2,B_j),
n_(j+1)>n_j, and a strictly positive probability w with
w_k~C*k^-alpha*exp(-4*sqrt(k)), C>0, such that its ACTUAL normalized
correlation S_w(n_j) vanishes for every j. C34b asserts failure for some
alpha and threshold sequence. These concern actual A(n,k)/E_k, not a
Gaussian surrogate. If true, leading-tail information cannot prove eventual
nonvanishing even in C33's critical class. It still says nothing about
cancelling every integer n>=2.

Preliminary attack: classical gliding-hump selection and inversion of an
operator of norm less than one are the strongest parent mechanism. Search
wp06-c34-sparse-interpolation was complete at68816 files, errors=[];
all candidate/source statements and chains inspected. Lagrange interpolation
and unrelated prime-orientation constructions do not supply the actual
Xi-derivative bands. The all-integer representing-mixture hit concerns
arbitrary test packets, not membership in this positive derivative cone.
External exact searches were largely irrelevant. Primary ADH2022 supplies
Xi-square Gram ancestry, not this tail-preserving interpolation statement.
Verdict: BRIDGE, scientific novelty unestablished. [OPEN CORE] at selection:
show genuine isolated-band response dominates both finite earlier bands
and the total later mass, uniformly over bounded interpolation parameters.

### Dependency-closed paper proof of C34a

Fix alpha>1. Set v_k=Z^-1*(k+1)^-alpha*exp(-4*sqrt(k)); Z is finite
and positive. Write b(n)=sum_k v_k a_nk, a_nk=A(n,k)/E_k.
Cauchy--Schwarz and translation invariance give |a_nk|<=1 for all n,k.
C32 at tau=4 proves b(n)=o(L(n)) through integers, where
L(n)=n^(.5-alpha)*exp(-4*sqrt(kappa*n))/log n, kappa=pi^2/2.
For every fixed finite set of derivative orders, its complete correlations
are O(exp(-c*n)): C32.5 and A(n,k)=sqrt(n)*sum_m d(m)K_k(mn)
pay this after absorbing sqrt(n) and the convergent exponential divisor sum.
The constant and rate may depend on the fixed set; this is sufficient below.

Choose a continuous function h of compact support,0<=h<=1, supported
in an open interval where the actual C17 profile J_a is strictly positive,
and not identically zero. Such an interval exists since integral J_a>0.
Let u_k(n)=(2*pi*n-T_k)/sqrt(T_k), T_k=(2k+7/2)/(pi/2), and
r_n(k)=v_k*h(u_k(n)). Each r_n has finite support in k=kappa*n+O(sqrt(n)).
The proof of C32's local Riemann sum, with this extra bounded factor, gives

 sum_k r_n(k)*a_nk / L(n) -> D>0.                 (34.1)

Explicitly D=Z^-1*kappa^(1-alpha)*(integral J_a(u)*exp(4*sqrt(a/8)*u)
*h(u)du)/(integral J_a(u)du). The m=1 term gives this positive value.
For every m>=2 the absolute contribution is dominated by the full positive
v-mixture; C32.6 sums them to o(L(n)). Thus no unproved fixed-row or
uniform growing-prime limit is used. Also sum_k r_n(k)->0; indeed its
support has O(sqrt(n)) terms, each O(n^-alpha*exp(-4*sqrt(kappa*n))).

Fix epsilon_j=2^(-j-4), j>=0. Inductively choose n_j above B_j, all prior
n_i, and sufficiently large that the following hold. Let
p_j(k)=epsilon_j*r_(n_j)(k), d_ij=sum_k p_j(k)*a_(n_i)k,
d_j=d_jj>0, and m_j=sum_k p_j(k).

(i) The finite supports of p_0,...,p_j are disjoint and increasing.
(ii) |b(n_j)|<=d_j/4.
(iii) sum_(i<j)|d_ji|<=d_j/8.
(iv) For every i<j, m_j<=2^(-j-4)*d_i.

Existence:34.1 gives d_j~epsilon_j*D*L(n_j)>0. The baseline is o(L),
paying(ii) for each fixed epsilon_j. Every earlier p_i has fixed finite
support and exponentially decaying row response, whereas d_j decays only
as a power times exp(-4*sqrt(kappa*n_j)); this pays(iii). The mass m_j
vanishes, paying the finitely many bounds(iv). Support separation follows
from kappa*n+O(sqrt(n)). All conditions are eventual, so any imposed
threshold B_j is allowed. No effective rate or prescribed dense sequence
is asserted.

For a fixed row i, |d_ij|<=m_j for j>i. Condition(iv) gives
sum_(j>i)|d_ij|<=d_i*sum_(j>i)2^(-j-4)<=d_i/16.
Together with(iii), sum_(j!=i)|d_ij|<=3*d_i/16.
On the complete Banach space of bounded real sequences define

 (T theta)_i= -b(n_i)/d_i-sum_(j!=i)(d_ij/d_i)*theta_j.

The absolutely convergent series defines an operator with Lipschitz
constant at most3/16. It maps the closed unit ball to itself since
1/4+3/16<1. For completeness, iterating from zero has successive sup-norm
increments at most(3/16)^q/4; their geometric sum is finite, so the
iterates converge uniformly to a fixed point theta. In particular
|theta_i|<=1 and b(n_i)+sum_j d_ij*theta_j=0 for every i.

Put wtilde_k=v_k+sum_j theta_j*p_j(k). Disjoint supports and
|theta_j|<=1 give (1-epsilon_0)v_k<=wtilde_k<=(1+epsilon_0)v_k,
so all weights are strictly positive and their sum W is finite and positive.
As k->infinity the occupied band index tends to infinity, so
wtilde_k/v_k->1. Normalize w_k=wtilde_k/W. Then
w_k~(Z*W)^-1*k^-alpha*exp(-4*sqrt(k)), with finite logarithmic moment
(and every polynomial moment). Absolute interchange follows from
sum_j sum_k|theta_j*p_j(k)*a_nk|<=sum_j m_j<=epsilon_0*sum_k v_k.
Consequently S_w(n_i)=[b(n_i)+sum_j theta_j*d_ij]/W=0 exactly.
This proves C34a on paper and refutes C34b. Full C17/C32 formalization
is still owed; this is not a Lean theorem or a solution of C33/C15/WP06.

### Stronger competing next conjectures C35

C35a asks whether the same critical-tail positive probability can have
exact cancellation on infinitely many full blocks [N_j,N_j+floor(sqrt(N_j))],
with N_j->infinity. C35b asserts that no such probability exists. The
isolated-row proof does not extend automatically: neighboring rows share
the same square-root band and its limiting smoothing operator can have
a badly conditioned inverse. [OPEN CORE]: a positive coefficient
interpolation law for the entire coupled block, including the actual
subleading arithmetic error. Both alternatives remain OPEN. Even C35a
would still not establish all-integer cancellation or the deficit target.

## G9: cosine Mellin via the actual zero kernel mass, before Lean

The already-proved monomial calculation extends to every -2<Re(s)<3:
int_0^infinity u^-s*phi_N(u)du=q_N(s)=s(s-1)/P_(N+3)(s), absolutely.
Lagrange interpolation proves the same rational partial fractions at
any s in this pole-free strip, not just the line Re(s)=2. Thus int phi_N=0.
Define C_N(x)=int_0^infinity phi_N(u)*cos(x*u)du (unscaled frequency).
Its cosine difference equals C_N because that zero mass is an actual
identity. For -2<Re(s)<0, absolute Fubini is now legitimate:

 int_0^infinity x^(s-1)*C_N(x)dx
 =-pi/[2*Gamma(1-s)*sin(-pi*s/2)]*q_N(s).          (G9)

Indeed for u>0, substitution v=u*x in the already corpus-proved absolute
cosine-difference Euler integral gives the inner Mellin integral
u^-s*pi/[2Gamma(1-s)sin(-pi*s/2)]. Its absolute integral is bounded by
C_s*u^-Re(s). The kernel's absolute weighted admission pays the outer
integral. Both section integrals and the product integral are therefore
absolutely integrable; all rearrangements are justified before evaluating.
The minus sign is from cos-1. In particular s=-1 gives
int x^-2*C_N(x)dx=-(pi/2)*q_N(-1). Rescaling to cos(2pi*x*u)
multiplies the right-hand side by(2pi)^-s. The family prefactor C_N
from C23 can then be restored. This proves an actual negative-strip
Mellin identity without undamped conditional Fubini. It does not pay
C23's positive-strip continuation or Xi-density contour shift. BRIDGE.


## C36: exact finite patterns at the square-root row scale

Conjecture before proof. Given alpha>1, any sequence of nonempty finite
sets C_j of distinct real offsets, and any integer thresholds B_j, C36a
asserts a critical-tail strictly positive probability w and integers N_j
above B_j, tending to infinity, such that

 S_w(floor(N_j+c*sqrt(N_j)))=0 for every j and c in C_j.

All displayed rows must be at least2 and distinct within and between
packets. C36b asserts that this can fail for some such data. The number
of prescribed offsets can grow without bound with j, but is fixed BEFORE
choosing N_j. This is weaker than C35's full sqrt(N_j)-length blocks:
that number of rows depends on the subsequently chosen N_j.

Parent attack: finite translates of a nonzero L1 function are linearly
independent; Rosenblatt, Linear independence of translations, J. Austral.
Math. Soc.59(1995),131–133, primary PDF opened and read, cites Edgar–Rosenblatt
1979 and gives the Fourier-transform parent. The abstract independence
is classical, not a novelty claim. The actual finite-pattern realization
still must preserve all coefficient signs and control infinitely many
other packets. Corpus query wp06-c36-translates completed with partial semantic retrieval
(deadline),68821 indexed files; all candidate/source statements, proof ideas
and proposed ingredients inspected. Returned Vandermonde machinery is useful
ancestry; unrelated translate-periodization does not prove actual response
independence. No absence certificate. Verdict BRIDGE. [OPEN CORE] at selection: construct bounded actual
coefficient controls with an invertible limiting finite response matrix,
then pay every cross-packet interaction.


### C36 finite-pattern paper proof

Fix one finite set of distinct offsets c_1,...,c_m. Put
rho_i=sqrt(2*pi)*c_i, lambda=4*sqrt(a/8), a=pi/2.
For any bounded compactly supported continuous h, the C32 local argument,
now with n_i(N)=floor(N+c_i*sqrt(N)), gives

 sum_k v_k*h(u_k(N))*a_(n_i(N))k / L(N)
 -> C0*int_R exp(lambda*u)*J_a(u+rho_i)*h(u)du,       (36.1)

where C0=Z^-1*kappa^(1-alpha)/(int J_a)>0 and v,L are from C34.
The floor error divided by sqrt(N) vanishes. Uniform compact C17 admission
pays the shifted local profile, sqrt(n_i)/sqrt(N)->1, and the divisor
m>=2 terms vanish by C32.6. Also b(n_i(N))=o(L(N)), since C32 gives
o(L(n_i)) and L(n_i)/L(N)->exp(-2*sqrt(kappa)*c_i)>0.

The real analytic functions J_a(u+rho_i) are linearly independent on
every nonempty open interval. To prove this directly, a relation there
extends to R by real analyticity of the explicit Gaussian-chirp profile.
Take Fourier transforms: J_a is integrable and its transform is continuous
and nonzero on a neighborhood of0 because int J_a>0. Thus the finite
exponential polynomial sum_i z_i*exp(i*rho_i*t) vanishes near0.
Differentiating at0 through order m-1 gives an invertible Vandermonde
system, since rho_i are distinct. Therefore every z_i=0. This is the
classical translate-independence parent; no new analytic assumption.

Choose a nonnegative continuous compactly supported cutoff psi, strictly
positive on some open interval. The finite Gram matrix
G_il=int psi(u)*exp(lambda*u)*J_a(u+rho_i)*J_a(u+rho_l)du
is positive definite: a zero quadratic form forces the corresponding
continuous square to vanish on that interval, and independence applies.
Using G^-1, choose compactly supported continuous real h_l with

 int exp(lambda*u)*J_a(u+rho_i)*h_l(u)du=c*delta_il,
 sum_l |h_l(u)|<=1 for every u, with a fixed c>0.     (36.2)

Explicitly first take h_l=psi*sum_r(G^-1)_rl*J_a(u+rho_r),
then divide all h_l by
max(1,sup_u sum_l|h_l(u)|). This finite bound is positive; its reciprocal
is c. No uniform inverse bound as m increases is claimed.

Do this separately for every prescribed finite pattern C_j. Fix
epsilon_j=2^(-j-4). At height N define the jth coefficient controls
p_(j,l)(k)=epsilon_j*v_k*h_(j,l)(u_k(N)); these may be signed, but their
pointwise absolute sum is <=epsilon_j*v_k. Their common support is finite
and lies in k=kappa*N+O_j(sqrt(N)). Let D_j(N) be the actual m_j by m_j
response matrix on the jth selected rows. Equations36.1--36.2 give

 D_j(N)/(epsilon_j*L(N)) -> C0*c_j*I.

For all sufficiently large N it is invertible, with
||D_j(N)^-1||_infinity <=2/(C0*c_j*epsilon_j*L(N)).
This follows from the finite Neumann series criterion applied to the
matrix minus its scalar identity limit. Only fixed j is involved here.

Inductively choose N_j above B_j and all previous rows, separating all
coefficient supports, and impose the following bounds. Write H_ij for
the response of coefficient block j on row block i, D_i=H_ii,
and b_i for the baseline row vector.

 ||D_j^-1*b_j||_infinity<=1/4;
 sum_(i<j)||D_j^-1*H_ji||_infinity<=1/8;
 ||D_i^-1||_infinity*mu_j<=2^(-j-4) for each i<j,    (36.3)

where mu_j=sum_k sum_l|p_(j,l)(k)|. The first follows from b_j=o(L(N))
and the displayed inverse bound. Previous controls have finite support,
so every entry of H_ji decays exponentially as N->infinity, uniformly
across the finitely many current offsets. This beats the subexponential
inverse bound and pays the second. Finally mu_j->0 because its support
moves into the tail of v; this pays the finitely many last inequalities.
Every condition is eventual for the fixed current j, so prescribed
thresholds and support/row separation can all be imposed.

For a later block j and earlier row i, ||H_ij||_infinity<=mu_j by
|a_nk|<=1 and the triangle inequality. Thus the third part of36.3 pays
the entire future-block operator sum by at most1/16. On bounded vectors
indexed by all pairs(j,l), with sup norm, define

 (T theta)_i= -D_i^-1*b_i-sum_(j!=i)D_i^-1*H_ij*theta_j.

It contracts by at most3/16 and maps the closed unit ball to itself.
The same geometric-iteration proof as C34 gives a bounded fixed point.
Set wtilde_k=v_k+sum_(j,l)theta_(j,l)*p_(j,l)(k). Disjoint supports
and36.2 imply (1-epsilon_0)v_k<=wtilde_k<=(1+epsilon_0)v_k and
wtilde_k/v_k->1. Normalize by its positive finite sum. Absolute
interchanges follow from sum_j mu_j<=epsilon_0*sum_k v_k<infinity.
The fixed-point equations give exact cancellation at every prescribed
row in every chosen packet. This proves C36a on paper.

C36 is still a classical-parent BRIDGE with no novelty certification and
no Lean claim. It sharpens C34's isolated rows to arbitrarily large finite
patterns; their scale must be chosen after the pattern. It neither settles
C35's consecutive blocks nor C33/C15's all-integer problem. The dependence
of c_j on the pattern is the new quantitative boundary exposed by this
positive construction, not an automatically affordable interpolation rate.


G9 normalization corollary: at s=-1, Gamma(2)=1 and sin(pi/2)=1.
For the actual physical-frequency cosine kernel
B_N(x)=int phi_N(u)*cos(2*pi*x*u)du, absolute admission and(G9) give
int_0^infinity x^-2*B_N(x)dx=-2*pi^2/P_(N+3)(-1).
This keeps the 2pi scale visible. No sign or resonance conclusion about
the Xi-weighted correlation follows from this moment alone.


### C35 local multiplier diagnostic (paper identity; no block theorem)

The preceding finite-pattern proof hides the cost of its finite Gram
inverse. The exact Fourier multiplier of the limiting critical operator
makes that boundary explicit. Put lambda=sqrt(pi)=4*sqrt(a/8), a=pi/2,
H(u)=exp(lambda*u)*J_a(u), I=int J_a=2*pi/sqrt(a). With Fourier convention
hatH(xi)=int H(u)*exp(-i*xi*u)du, the same complex Gaussian evaluation
already used in C32 gives

 hatH(xi)=I*exp((lambda-i*xi)^2/(2*a))*
                    cos((lambda-i*xi)^2/2).          (35.1)

This follows by writing J_a as half the sum of its two conjugate Gaussian
terms before integrating; taking a real part after inserting a complex
linear parameter would be invalid. Both terms admit every complex linear
parameter absolutely, and their Gaussian prefactors each reduce to I.
For real xi, a cosine zero must have real argument pi/2+pi*j. The
imaginary part of (lambda-i*xi)^2/2 is -lambda*xi, so the only real
frequency zero is xi=0. At zero lambda^2/2=pi/2 and

 hatH'(0)=i*lambda*e*I !=0,
 int u*H(u)du=-lambda*e*I.                          (35.2)

The first equality is direct differentiation; the second uses
hatH'(0)=-i*int uH. Thus the critical local obstruction is a simple
zero-frequency cancellation, together with rapidly decreasing response
to high frequencies. This identity is a classical Gaussian BRIDGE and
is not a uniform discrete inverse estimate. In particular, nonvanishing
of the symbol away from0 cannot be used to claim a bounded inverse:
its modulus decays with a Gaussian envelope at large real frequency.
The next C35 audit must price that inverse for the ACTUAL baseline
error, including its arithmetic oscillations, rather than arbitrary data.

## C37: consecutive blocks with lengths chosen before heights (CONJECTURE)

For every alpha>1, every sequence of positive integer lengths ell_j, and
any integer thresholds B_j, conjecture existence of a strictly positive
probability w_k~C*k^-alpha*exp(-4*sqrt(k)), C>0, and disjoint blocks
[N_j,N_j+ell_j-1], N_j>=max(2,B_j), on which the ACTUAL correlation is
identically zero. This includes a zero set containing arbitrarily long
intervals (upper Banach density1). It does not prescribe ell_j relative
to the subsequently chosen N_j and therefore does not imply C35.
The competing conjecture asserts failure for some lengths/thresholds.

Given the exact internal and external frontier, the new mechanism to test
is confluent interpolation of actual integer rows. Replace row values by
N^(r/2)*Delta^r,0<=r<ell. For fixed ell the limiting row functions should
be derivatives of J_a, rather than coalescing translates. Their weighted
integrals vanish at the critical tilt because integral exp(lambda*u)J_a=0
and integration by parts multiplies it by(-lambda)^r. Independence of
these derivatives follows from Fourier multiplication by distinct powers.
A finite Gram inverse could then pay each fixed block and reuse C36's
infinite cross-packet contraction.

[OPEN CORE]: prove the scaled finite-difference local limits AND relative
weighted tails for the actual product kernel. C17's zeroth-order little-o
cannot be differentiated. Nor can one complexify the infinite coefficient
sum on a fixed neighborhood: stretched-exponential coefficients need not
pay exponential growth in k there. Integer resonance is essential; naive
real derivatives of K include the carrier exp(-2pi*i*x). A cutoff,
demodulation and fixed-order difference estimate must retain both signs
and pay their discarded low-frequency contribution. C37 is not proved.

Parent attack: Schaback's Multivariate Interpolation by Polynomials and
Radial Basis Functions (Constructive Approximation21(2005),293–317;
author manuscript dated2002) supplies classical flat-limit/discrete-moment
preconditioning ancestry. Its Gaussian interpolation theorem is not an
estimate for the actual Xi product kernel. Corpus GaussianJetPositivity
already has finite-difference Gram algebra; use it rather than duplicating
that parent. Verdict SURVIVES PRELIMINARY ATTACK, novelty unestablished.

### G10: exact signed-profile Laplace identity before Lean

Let a=pi/2, gamma=(1/a+i)^(-1), I=2pi/sqrt(a). The C17 signed profile
can be written

 J_a(u)=Re[I/sqrt(2pi/gamma)*exp(-gamma*u^2/2)].

The square roots are principal; Re(gamma)>0 ensures their Gaussian
branches agree. More generally, divide each complex Gaussian by its
actual positive-real-part Gaussian integral. The two conjugate normalized
Gaussians each have total mass1. For every complex z, their absolutely
convergent tilted integrals are exp(z^2/(2gamma)) and its conjugate-
parameter counterpart. Consequently the normalized REAL profile j=J_a/I
satisfies

 integral exp(z*u)*j(u)du=exp(z^2/(2a))*cos(z^2/2).       (G10.1)

To justify complex z, use the sum of the two conjugate Gaussians BEFORE
integration; a real-part operation does not commute with multiplication
by an arbitrary complex exponential. Each absolute value is bounded by
C_z exp(-c*u^2+|Re(z)|*|u|), which is integrable. Complete the square
using the already proved complex quadratic Gaussian integral. Then
1/gamma=1/a+i and the exponential definition of cosine give(G10.1).
At real lambda=sqrt(pi), the right side is exp(1)*cos(pi/2)=0; at z=0
it equals1. Thus j is nonzero while its critical tilted mass is exactly0.
This is a classical Gaussian identity, an analytic dependency of C32/C37,
not the actual C17 asymptotic, a block theorem, or scientific novelty.

### C37 fixed-order difference estimates and paper construction

This section supersedes C37's OPEN status on PAPER only. It uses the
complete C17/C32 analytic proofs, not their currently partial Lean coverage.
All difference orders below are fixed before n tends to infinity.

Write Delta f(n)=f(n+1)-f(n), a_nk=A(n,k)/E_k, v_k as in C34,
and L(n)=n^(1/2-alpha)*exp(-4*sqrt(kappa*n))/log n. For each fixed
r>=0 and each continuous compactly supported h, the needed limits are

 n^(r/2)/L(n) * sum_k v_k*h(u_k(n))*Delta^r a_nk
 -> C0*(sqrt(2pi))^r * integral exp(lambda*u)*J_a^(r)(u)*h(u)du, (37.1)

 n^(r/2)*Delta^r[sum_k v_k*a_nk]/L(n) ->0,                 (37.2)

where lambda=sqrt(pi), C0=Z^-1*kappa^(1-alpha)/integral J_a>0.
In37.1 the coefficients h(u_k(n)) are frozen BEFORE taking differences
of the row variable. No derivative of h is being asserted.

Here are the analytic bounds paying these limits. First retain only the
m=1 term in the exact divisor representation. All m>=2 terms, even after
multiplying the difference by n^(r/2), are bounded using the triangle
inequality and32.6 by

 C_r*n^(r/2)*L(n)*sum_(m>=2)d(m)m^-alpha*
           exp(-4*sqrt(kappa*n)*(sqrt(m)-1))=o(L(n)).

For domination of the sum, split its exponential in two equal factors;
one is at most exp(-2*sqrt(kappa*n)*(sqrt(2)-1)), which absorbs n^(r/2),
and the other is at most1. Thus the same summable d(m)m^-alpha applies.
A bounded h or a coefficient perturbation dominated by v obeys this bound.

For the m=1 term use the actual Mellin formula on Re(s)=sigma>0.
Its n dependence, after including sqrt(n), is n^(1/2-s). Split positive
and negative t. On positive heights insert exp(2pi*i*y) into

 g_s(y)=exp(2pi*i*y)*(n+y)^(1/2-s), 0<=y<=r.

At integer y it is1, so this changes none of the finite differences.
The negative-height branch uses exp(-2pi*i*y). Repeated FTC gives
Delta^r g_s(0)=integral_[0,1]^r g_s^(r)(y_1+...+y_r)dy.
On t comparable to n, with sigma=1/2+delta, the logarithmic derivatives
satisfy, uniformly on this fixed y interval,

 sqrt(n)*(log g_s)' = i*(2pi*n-t)/sqrt(n)-delta/sqrt(n)
                       +O_r((1+|delta|/n+t/n)/sqrt(n)),
 n^(j/2)*(log g_s)^(j)=O_(j,r)((|delta|+t)*n^(-j/2)), j>=2.

These formulas follow by differentiating (1/2-s)log(n+y)+2pi*i*y;
its j-th derivative for j>=2 is (-1)^(j-1)*(j-1)!*(1/2-s)/(n+y)^j.
Leibniz induction therefore bounds the normalized r-th derivative
by a polynomial, of degree at most r, in
1+|t-T_k|/sqrt(n)+|k-kappa*n|/sqrt(n)+delta/sqrt(n), times |g_s|.
Every constant depends on r, not on k,n in a fixed comparability range.
Derivatives in the scaled t variable of this inserted factor obey the
same type of bound for every fixed number of derivatives.

For local k=kappa*n+O(sqrt(n)), use sigma=1/2 and the C17 saddle
substitution t=T_k+x*sqrt(T_k). The preceding derivative formula and
C17's Taylor expansion give, for every fixed r, uniform convergence
of the demodulated scaled derivatives on bounded x,u intervals to
(sqrt(2pi))^r J_a^(r)(u), with the original prefactors unchanged.
The same polynomial-times-Gaussian bound dominates their central x
integrals. Outside t in[T_k/2,2T_k], Stirling's strict saddle gap absorbs
all fixed derivative factors; compact heights contribute at most
C_r*n^(r/2)*(C_r)^(2k)/E_k and hence tend to zero faster than any power
when k is comparable to n. This proves the LOCAL fixed-order limit.
It does not differentiate an unquantified zeroth-order remainder.

The relative k tails require separate bounds. Choose the constant M
from32.5 larger if needed. For k<=n/M, the complex Bessel/Cauchy argument
in32.5 also controls every fixed derivative with respect to x on a fixed
small relative disk about each real x>=n. Shrinking that disk preserves
Re(x*exp(z))>=c*x and the factor theta^(-2k). Each fixed derivative costs
at most C_r*x^(-r) after Cauchy on the x disk. In particular the much
weaker finite-difference bound C_r*n^(r/2+1/2)*exp(-c_r*n) suffices;
its v-weighted total is o(L(n)). The finitely many small k are included.

On n/M<k<=kappa*n, repeat32.2 on its optimized positive Mellin line,
now retaining the derivative insertion above. Tilted Gamma moments give

 integral |t-T_k|^j*t^(p+delta)*exp(-a*t)dt
 <= C_j*(sqrt(T_k)+delta)^j*b*sqrt(T_k)*T_k^delta*
                                              exp(C*delta^2/T_k).

To see this without a new asymptotic premise, split at distance
2*delta/a+sqrt(T_k) from T_k. In the central region the inserted power
has the displayed bound. In each successive interval of width sqrt(T_k),
concavity of (p+delta)log(t)-a*t gives a Gaussian tail until distance T_k/2;
beyond it the derivative of the exponent has a fixed sign and magnitude,
so a geometric-exponential tail pays every fixed moment. The low-t sector
estimate in32.2 has its strict exponential gap and pays its polynomial
factors separately. Optimize delta exactly as in32.4. Because n and k
are comparable and log(2pi*n/T_k) is comparable to
(kappa*n-k)/n on this interval, the result is

 n^(r/2)*|Delta^r[sqrt(n)*K_k(n)/E_k]|
 <= C_r/log(n)*(1+v)^r*exp(-c*v^2),
       v=(kappa*n-k)/sqrt(n)>=0.                    (37.3)

A bounded O(1) sliver at the affine saddle is absorbed in the constant.
The loss exp(C*delta^2/T_k) is absorbed by choosing the optimized line
with a sufficiently small constant; the remaining power in delta/sqrt(n)
is a power of1+v. This is the moving-line estimate needed for the
exponentially larger low-k coefficients, not a polynomial tail substitute.

On kappa*n<k<=2*kappa*n, use C17's fixed sigma=4 line and its all-fixed-q
L1 derivative bound(S). The difference insertion has derivatives bounded
by C_(r,q)*(1+v)^r times a polynomial in the scaled t displacement,
v=(k-kappa*n)/sqrt(n). Those polynomials are absorbed in the Gaussian
amplitude bound in(S). Integration by parts q+r times in scaled t,
whose Fourier frequency is comparable to v in this range, gives

 n^(r/2)*|Delta^r[sqrt(n)*K_k(n)/E_k]|
 <= C_(r,q)/log(n)*(1+v)^(-q)                        (37.4)

for any fixed q. The compact-height remainder is exponentially small
in k relative to E_k and pays the same bound. No moving q is asserted.
For k>2*kappa*n use the triangle inequality for Delta^r and C17's original
fourth-power envelope. The coefficient exp(-4*sqrt(k)) supplies the
strict extra factor exp(-4*(sqrt(2)-1)*sqrt(kappa*n)); this absorbs every
fixed power n^(r/2) and the remaining polynomial k-tail.

After multiplying by v_k and dividing by L(n),37.3 has a Riemann-sum
majorant C*n^(-1/2)*(1+v)^r*exp(C*v-c*v^2). In37.4 the coefficient
ratio is at most a constant, so choose q>2 and obtain the integrable
majorant C*n^(-1/2)*(1+v)^(-q). The far head and far tail were paid above.
Consequently the local limit extends to the full coefficient sum, with
or without the bounded cutoff h. The divisor estimate pays its full
arithmetic extension. This proves37.1 and gives the limit in37.2 as
C0*(sqrt(2pi))^r*integral exp(lambda*u)J_a^(r)(u)du.

All boundary terms in r integrations by parts vanish, since J_a and its
derivatives are finite sums of polynomial-times-Gaussian functions with
positive real quadratic decay. The last integral is
(-lambda)^r*integral exp(lambda*u)J_a(u)du=0 by G10.1. This proves37.2.
No subleading expansion of E_k was used; its actual equivalent and
uniform bounds suffice because finite differences act on the row variable.

Now fix one finite block length ell. The functions J_a^(r),0<=r<ell,
are linearly independent on every open interval. A relation extends
real-analytically to the real line. Fourier transformation gives
[sum_r c_r*(i*xi)^r]*hatJ_a(xi)=0. Since hatJ_a is continuous and
hatJ_a(0)=integral J_a>0, that polynomial vanishes on an interval,
so every coefficient is zero. Thus the weighted Gram construction from
C36, with functions (sqrt(2pi))^r J_a^(r), produces compact controls h_l
whose pointwise sum of absolute values is at most1 and whose limiting
scaled-difference response is c*identity, c>0. The positive number c
can depend on the fixed ell; no bound as ell grows is inferred.

For block j use ell_j and choose height N_j only after those controls.
Let P_j be the invertible triangular row operation taking the ell_j raw
values at N_j,...,N_j+ell_j-1 to N_j^(r/2)*Delta^r,0<=r<ell_j.
Its norm is at most max_(r<ell_j)2^r*N_j^(r/2). Let p_(j,l)(k)=
epsilon_j*v_k*h_(j,l)(u_k(N_j)), epsilon_j=2^(-j-4), and let D_j be
its response matrix AFTER applying P_j. By37.1,
D_j/(epsilon_j*L(N_j))->C0*c_j*identity, so its inverse is bounded by
2/(C0*c_j*epsilon_j*L(N_j)) for sufficiently large N_j. By37.2 its
scaled baseline vector satisfies ||D_j^-1*P_j*b_j||<=1/4 eventually.

Previous controls have fixed finite coefficient support. Their raw rows
decay exponentially; multiplying by the fixed-degree polynomial norm
of P_j and the subexponential inverse bound still tends to zero.
Thus the total previous-block normalized operator norm can be made<=1/8.
For each already selected block i, the finite number
M_i=||D_i^-1*P_i|| is fixed. Choose N_j still larger to ensure
M_i*mu_j<=2^(-j-4) for all i<j, where mu_j=sum_(k,l)|p_(j,l)(k)|->0.
Supports and row blocks can simultaneously be made disjoint and ordered,
and all prescribed thresholds can be imposed. Every requirement is
an eventual condition for the fixed current ell_j.

For later j, the raw response on block i has operator norm at most mu_j
by |a_nk|<=1. Hence the complete normalized cross-block operator has
norm at most1/8+1/16=3/16. C36's explicit geometric fixed-point iteration
solves all scaled equations with coefficients |theta_(j,l)|<=1. Since
P_j is invertible this solves every RAW row in every selected block.
The probability normalization and preservation of strict positivity and
w_k~C*k^-alpha*exp(-4sqrt(k)) are exactly C36's disjoint-support argument;
absolute interchange is paid by sum_j mu_j<=epsilon_0*sum_k v_k.

This proves C37 on paper. Choosing ell_j->infinity gives exact consecutive
zero blocks of unbounded length. It neither bounds their length in terms
of height nor cancels the initial rows. C35, C33, C15 and WP06 remain OPEN.
Verdict BRIDGE; scientific novelty unestablished. The positive advance
is actual thick zero-set realizability inside the critical positive tail,
not a uniform-cost construction or a formalized asymptotic theorem.

## C38: critical-tail weak transport (conjecture and paper resolution)

C37 permits arbitrarily long consecutive zero blocks. It does not control
an average over every large dyadic interval. The competing C38 claims are:
for every probability w with w_k~C*k^-alpha*exp(-4*sqrt(k)), C>0,alpha>1,
and every smooth compactly supported real psi on(0,infinity),

 (1/X) sum_(n>=2) psi(n/X)*n^alpha*log(n)*exp(4*sqrt(kappa*n))*S_w(n)
   -> -C*exp(1)*kappa^(1-alpha)/sqrt(2)*(alpha-1/4)*integral psi. (38.1)

The alternative is an actual such w for which this weak limit fails.
All rows are the literal A(n,k)/E_k rows; kappa=pi^2/2. The proof below
establishes38.1 on PAPER, using the already recorded C17/C32 paper bounds.
It adds no regularity, monotonicity or convergence rate for w. It does not
assert pointwise first-order asymptotics for arbitrary w.

### Normalization audit

The supposed need for subleading derivative-energy asymptotics is not
intrinsic. Put e_k=b_k*sqrt(T_k/a)*log(T_k), the positive leading expression
from C17. Since E_k/e_k->1 and every E_k,e_k>0, their ratio is globally
bounded above and below by positive constants. For any positive summable
v with finite logarithmic moment, set

 Z=sum_k v_k*E_k/e_k,  w_k=v_k*E_k/(Z*e_k).

Then0<Z<infinity, w is a positive probability with finite logarithmic
moment, and exactly

 S_w(n)=Z^-1 sum_k v_k*A(n,k)/e_k.

Absolute convergence follows from |A(n,k)|<=E_k and the bounded ratio.
Also w_k~v_k/Z. Thus energy-adapted constructions preserve a prescribed
critical tail and remove the actual E_k from every response exactly.
This is an elementary coordinate change, not a cancellation theorem.
The stronger argument below does not even require making that change:
it averages rows first, so E_k is a constant throughout each inner sum.

### First correction of the actual integer kernel

Keep a=pi/2, lambda=sqrt(pi), p=2k+7/2, T=p/a, b=T^p*exp(-a*T),
and u=(2pi*n-T)/sqrt(T). Define the real Schwartz function

 H(u)=Re[exp(-i*pi/4) integral_R exp(-a*x^2/2)*exp(i*(x-u)^2/2)
          *(a*x^3/3-i*(x-u)^2*(x+2*u)/6-u/2) dx].          (38.2)

It is a polynomial times a complex Gaussian followed by real part, hence
Schwartz with a Gaussian envelope. The actual C17 Mellin inversion gives

 K_k(n)/b = J_a(u)+T^-1/2*H(u)+O(T^-1*(log T)^M)           (38.3)

uniformly for integer n with -B*log T<=u<=epsilon*log T, where B is any
fixed positive constant, epsilon>0 fixed, and M is a fixed integer.
This is a new expansion of the explicit integral, not a differentiated
little-o assertion. Here are its error payments. At t=T+x*sqrt(T), the
exact normalized amplitude is

 exp(-a*x^2/2)*(1+a*x^3/(3*sqrt(T))+O(T^-1*(1+|x|)^6)).

The phase after removing the integer carrier exp(-2pi*i*n)=1 is

 (x-u)^2/2-(x-u)^2*(x+2*u)/(6*sqrt(T))
       +O(T^-1*(1+|x|+|u|)^4).

The prefactor is (1+u/sqrt(T))^-1/2=1-u/(2*sqrt(T))+O(u^2/T).
The sectorial Gamma remainder is O(1/T) on this band, so it contributes
nothing at order T^-1/2. Truncate |x|<=L*log T. Taylor's formula with
remainder, and the Gaussian amplitude bound, give38.3 after integration;
all products of discarded terms are bounded by T^-1 times a fixed
polynomial in log T against exp(-c*x^2). The omitted x interval inside
[T/2,2T] has size O(exp(-c*(log T)^2)); the two farther t intervals have
C17's strict exponential saddle gap. Compact t has superpolynomial cost
1/b. These bounds are uniform in the stated u interval. Negative t is
its conjugate, exactly as in C17.

The growing u interval is sufficient for a first-order weighted integral.
For u>=0 with n comparable to T, the C32 right contour shift gives
|K_k(n)|/b<=C*exp(-c*u^2). For u<0, C17 gives C*(1+|u|)^-4.
Concavity of square root gives the exact bound

 exp(4*sqrt(kappa*n)-2*lambda*sqrt(T))<=exp(lambda*u).

Consequently the discarded positive u>epsilon*log T contributes
O(exp(-c'*(log T)^2)); the discarded negative u<-B*log T costs
O(T^(-lambda*B)). Choose lambda*B>2 and 0<lambda*epsilon<1/4.
On the retained band,38.3's error multiplied by exp(lambda*u), integrated
or summed with its u mesh, is O(T^-3/4*(log T)^(M+1))=o(T^-1/2).
All polynomial smooth row factors below are bounded on the comparable
range. Thus every u tail and the local remainder are paid to first order.

### Three exact Gaussian moments and the correction mass

Write I=integral J_a=2pi/sqrt(a). G10 gives the entire transform
L(z)=I*exp(z^2/(2a))*cos(z^2/2). Gaussian domination justifies its first
two differentiated integrals. At lambda=sqrt(pi),

 integral exp(lambda*u)*J_a(u)du=0,
 integral u*exp(lambda*u)*J_a(u)du=-I*exp(1)*lambda,
 integral u^2*exp(lambda*u)*J_a(u)du
       =-I*exp(1)*(1+2*lambda^2/a).                       (38.4)

For the correction38.2, the corresponding exact moment is

 integral exp(lambda*u)*H(u)du
       =-I*exp(1)*(lambda/2+lambda^3/(2a)).              (38.5)

One must not apply absolute Fubini directly to the unregularized double
Fresnel integral. To verify38.5, replace exp(i*v^2/2),v=u-x, by
exp(-(delta-i)*v^2/2), delta>0. All double integrals with polynomial and
real exponential factors are then absolute. Under the tilted normalized
Gaussians, x has mean z/a and variance1/a; v has mean z/(delta-i) and
variance1/(delta-i). Let delta decrease to0. After the x integral, both
sides are polynomial-Gaussian functions of u with a common Gaussian
majorant: the limiting variance1/a+i has reciprocal with positive real
part, uniformly on a sufficiently small closed delta interval. This pays
the limit with every polynomial factor and exp(z*u).

The limiting normalized moment of the multiplier in38.2 is

 P(z)=z/a+i*z/2+z^3*(1/(3*a^2)-1/3+i/(2*a)).

Indeed the multiplier is a*x^3/3-i*x*v^2/2-i*v^3/3-(x+v)/2;
use the independent Gaussian moments with means z/a,iz and variances
1/a,i. Its unnormalized complex transform is
I*exp(z^2/(2a)+i*z^2/2)*P(z). Taking real parts at lambda proves38.5.
In particular, the cubic terms cancel in the combination

 integral exp(lambda*u)*(H(u)-lambda*u^2*J_a(u)/4)du
       =-I*exp(1)*lambda/4.                             (38.6)

### Averaging rows before using coefficient asymptotics

Let supp(psi) be contained in[A,B],0<A<B. Put beta=alpha+1/2 and
n0=T/(2pi),y=n0/X. For k in a fixed compact multiple of X, form

 B_(k,X)=sum_(n>=2) psi(n/X)*n^beta*log(n)
                        *exp(4*sqrt(kappa*n))*K_k(n)/E_k.

The smooth factor has the uniform first-order expansion

 n^beta*log(n)*psi(n/X)/(n0^beta*log(n0))
 =psi(y)+u/sqrt(T)*[beta*psi(y)+y*psi'(y)]
       +o(T^-1/2)*(1+|u|)^2

on the growing retained band. The log derivative costs an additional
O(1/log T) relative to the displayed first-order coefficient and tends
to zero. The exact exponential factor expands as

 exp(4*sqrt(kappa*n)-2*lambda*sqrt(T))
 =exp(lambda*u)*(1-lambda*u^2/(4*sqrt(T))
                       +O(T^-1*(1+|u|)^4)).

Combine38.3--38.6. The u mesh is h=2pi/sqrt(T). Replacing the sums of
the explicit polynomial-Gaussian functions by integrals costs O(h^2) for
the leading term and O(h) for its first correction. For completeness,
partition R into symmetric cells of width h centered on the shifted
lattice. Taylor's integral remainder cancels the linear term in each
cell and bounds the total leading error by C*h^2*integral|f''|; these
explicit functions have integrable second derivatives uniformly in y.
The correction only needs the analogous first-derivative bound. The
actual-kernel errors were paid above, before this replacement.

Hence, uniformly in the compact k range,

 B_(k,X)=-b/E_k * I*exp(1)*lambda/(2pi)
       *n0^beta*log(n0)*exp(2*lambda*sqrt(T))
       *[(beta+1/4)*psi(y)+y*psi'(y)+o(1)].              (38.7)

E_k~b*sqrt(T/a)*log T is used only AFTER the row sum. It is never
differentiated. Also k=(a*T-7/2)/2, so
exp(2*lambda*sqrt(T)-4*sqrt(k))->1. Thus the assumption on w gives

 w_k*B_(k,X)=-C*exp(1)/sqrt(2)*kappa^-alpha
       *[(alpha+3/4)*psi(k/(kappa*X))
                    +(k/(kappa*X))*psi'(k/(kappa*X))+o(1)] (38.8)

uniformly in this compact range. No rate for w_k's relative o(1) is
needed: it multiplies38.7 AFTER the leading critical mass has vanished.
This is why a pointwise row expansion would have been insufficient.

All remaining ranges are paid as follows. Enlarge the compact k interval
so it includes [kappa*A*X/2,2*kappa*B*X]. Below it, n lies a fixed fraction
to the right of the k saddle. For k<=n/M use32.5; for the remaining low
k use32.2 with a sufficiently small fixed positive multiple of T, giving
exp(-c*X). The row weight grows only exp(O(sqrt(X))), so these ranges
vanish even after the displayed polynomial factors and the O(X) row sum.
Above the compact range, use |A(n,k)|<=E_k for the actual full row. The
coefficient tail times exp(4*sqrt(kappa*B*X)) is exp(-c*sqrt(X)) times a
polynomial, hence negligible uniformly over the O(X) rows.

Alternatively for the m=1 row alone, the same bound follows from C17's
polynomial envelope and E asymptotics. The distinction matters because
|A|<=E need not hold for its separate divisor summands.

For the complete m>=2 divisor contribution,32.6 is available for arbitrary
w satisfying the stated asymptotic, by its global upper bound. Relative
to the38.1 scale its absolute value is at most

 C*sqrt(n)*sum_(m>=2)d(m)*m^-alpha
                   *exp(-4*sqrt(kappa*n)*(sqrt(m)-1)).

Split the exponent in half. One half absorbs sqrt(n) uniformly and tends
to zero exponentially; the other is at most1. Since alpha>1,
sum d(m)*m^-alpha is finite. This pays the whole divisor sum and every
interchange. The original row sums are already absolutely convergent
from |A(n,k)|<=E_k and sum w_k=1.

Finally sum38.8 over k, divide by X, and use the ordinary Riemann sum
with y=k/(kappa*X). Compact support gives integral y*psi'=-integral psi.
The remaining factor is alpha+3/4-1=alpha-1/4, with the extra kappa
from the mesh. This proves38.1 and the claimed constant.

### Obstruction, positive survivor, and next conjecture

Choose psi>=0 with positive integral. For alpha>1 the right side of38.1
is strictly negative. Thus there is NO all-row cancelling probability
with w_k~C*k^-alpha*exp(-4*sqrt(k)), C>0,alpha>1. C33's existence
alternative is FALSE on PAPER, and its nonexistence alternative is true
in precisely this stated class. More positively,38.1 is an exact weak
transport law; it also forces a negative actual row in every sufficiently
large interval containing a rescaled fixed positive test support. It does
not contradict C37's zero blocks and does not decide C35.

No route card is retired: full C17/C32/C38 formalization remains owed.
The positive survivor to formalize is38.1 itself, not merely nonexistence.
Scientific novelty is unestablished; classical Gaussian saddle expansion
and adjoint approximate-identity methods are the parents. New corpus
searches and primary-source checks are logged in EVIDENCE.

C39 now asks the competing existence/nonexistence question for a positive
probability with

 w_k~C*k^(-1/4)*log(k+2)*exp(-4*sqrt(k)), C>0,
 S_w(n)=0 for every integer n>=2.                         (C39)

This remains OPEN. The exponent1/4 is exposed by38.1's transport factor;
its extension below alpha>1 and the logarithmic refinement are not
asserted as theorems here. The log factor is motivated by the actual
E_k's log T normalization, not by assuming a subleading E_k expansion.
This sequence shape is summable with every polynomial moment, so it is
not killed by admissibility. Test both C39 alternatives against actual
rows, or prove a stronger weak transport law, without claiming that the
new shape is sufficient. C15 and the assigned spectral-deficit target
remain OPEN.

A precise block consequence of38.1: for every fixed delta>0, every
sufficiently large real X has an integer n in[X,(1+delta)*X] with S_w(n)<0.
Choose a nonnegative smooth test with positive integral supported strictly
inside(1,1+delta). Thus any sequence of consecutive all-zero blocks whose
starting points tend to infinity must have length/start tending to zero.
C37 and this obstruction separate unbounded block lengths from positive
relative lengths; the sqrt(height) boundary C35 is still unresolved.

## G11: global actual Mellin amplitude, paper proof before Lean

This closes a specific C17 analytic dependency on Re(s)=4. Write
T=(2k+7)/(pi/2), B=T^(2k+7)*exp(-(pi/2)*T). Unlike C17's critical-line
T, this is the exact sigma-four amplitude saddle already defined in G6.
For the literal Mellin integral M_k(4+it), conjecture and prove here:
there is one C>0, independent of k and real t, such that

 |M_k(4+it)| <= C*B*exp(-(pi/4)*(sqrt(abs(t))-sqrt(T))^2).  (G11.1)

This is a classical Laplace bound for the actual kernel, not scientific
novelty or a spectral-deficit conclusion. G6's exact Gamma-reflection norm
for t>0 is

 (t^2+49/4)^k*t*(t^2+4)*(t^2+9)*(t^2+16)
                  /(32*pi^3*sinh((pi/2)*t)).

Put a=pi/2,d=7/2,r=sqrt(t^2+d^2). The inequality exp(2at)>=1+2at
implies t/sinh(at)<=(1/a+2t)*exp(-at). Since r>=d>1 and r>=t,
the polynomial factors and 1/a+2t are bounded by one fixed constant
 times r^7. Also0<=r-t<=d. Hence the norm is bounded by
C0*r^(2k+7)*exp(-ar), with C0 fixed (including exp(ad)).
At t=0, the exact Gamma value gives36*pi^-4*d^(2k); increasing the same
constant includes that endpoint. Conjugation gives the negative heights.

For every r,T>0, log(r/T)<=2*(sqrt(r/T)-1). Multiplying by aT=2k+7
and exponentiating gives

 r^(2k+7)*exp(-ar)<=B*exp(-a*(sqrt(r)-sqrt(T))^2).

This estimate is global; no local Taylor approximation is used. Finally
(sqrt(r)-sqrt(t))^2<=r-t<=d, and the elementary square inequality gives
(sqrt(r)-sqrt(T))^2 >= (sqrt(t)-sqrt(T))^2/2-d.
Absorb exp(ad) once more into the fixed constant to proveG11.1.

It also gives integrability and total norm O(B*sqrt(T)). On0<=t<=4T,
(sqrt(t)-sqrt(T))^2 >= (t-T)^2/(9T); for t>=4T it is at least t/4.
Thus the envelope is bounded by the sum of a translated Gaussian of
width sqrt(T) and a fixed exponential tail. Their integrals are
C1*sqrt(T)+C2, at most C3*sqrt(T) since T>=4. No higher derivative,
critical-line local profile, moving-line bound or energy asymptotic is
claimed by this lemma; those remain exact subsequent obligations.

## C40/C41: sharpen the critical transport boundary (CONJECTURES)

C40 asks whether38.1 extends to every real alpha,delta when
w_k~C*k^-alpha*(log k)^delta*exp(-4sqrt(k)), after replacing log(n)
in its row weight by(log n)^(1-delta). The competing alternative is an
actual such coefficient law whose remote orders or divisor tail change
the weak limit. If true, any all-row canceller in this class must have
alpha=1/4, beyond C38's stated alpha>1 range.

C41 asks whether all-row cancellation in the alpha=1/4 class forces
delta=1. The proposed positive survivor is a conserved averaged flux:
with exact T_k,b_k,E_k and n0_k=T_k/(2pi), define

 v_k=w_k*(b_k/E_k)*exp(2sqrt(pi)*sqrt(T_k))*n0_k^(3/4),
 F_psi(X)=X^-1*sum_k v_k*psi(n0_k/X).

For each smooth compactly supported psi, conjecture that all actual rows
zero imply F_psi(X) has a finite limit with a power-saving error. For a
nonnegative test of positive integral, the asserted w tail makes
F_psi(X) asymptotic to a positive constant times(log X)^(delta-1).
The power-saving remainder would force delta=1, including exclusion of
a slowly vanishing limit. This keeps E_k exact, so no derivative or
subleading asymptotic of the energy is introduced.

[OPEN CORE]: turn38.7 into a quantitative error before replacing E_k,
pay all coefficient/divisor tails for arbitrary real exponents, and prove
the differentiated finite sum has an integrable derivative in X. No
conservation law or logarithmic necessity is assumed in Lean.

### C40/C41 paper proof: the only power-log critical shape

This closes C40 and C41 on PAPER, not in Lean. The assumptions remain
only positivity/probability and the stated asymptotic shape of the actual
coefficients; no smoothness or quantitative asymptotic error is added.

First extend32.6 to any fixed real alpha,delta with weight upper bound
C*(k+2)^(-alpha)*(log(k+2))^delta*exp(-4sqrt(k)). The very-low-order head
is exponentially small by32.5. In the comparable range, both power and
logarithm ratios are bounded on fixed ratios of k/x, and the displaced
square-root weight still has the same Gaussian lower-order majorant and
exponentially decreasing upper-order majorant. Any fixed powers produced
by alpha,delta are absorbed into those majorants. Above2*kappa*x, retain
half of exp(-4sqrt(k)) to sum any polynomial/logarithmic growth, and use
the other half, or a split closer to1 if necessary, to preserve a strict
exponential saving against the central exp(-4sqrt(kappa*x)). Consequently

 sum_k w_k*|K_k(x)|/E_k
 <= C*x^-alpha*(log x)^(delta-1)*exp(-4sqrt(kappa*x)), x>=2. (40.1)

One explicit high-tail split chooses theta with1/sqrt(2)<theta<1, uses
exp(-4*theta*sqrt(k)) for the central saving and
exp(-4*(1-theta)*sqrt(k)) to pay all remaining powers. The compact
comparability constants and finitely many low k are absorbed into C.
For the m-th divisor, logarithm ratios contribute at most a fixed power
of m: log(m*n)/log n<=1+log m/log2<=C*(1+m). Split the exponential saving
in two as before, but now retain in one half a factor exp(-c*sqrt(m)).
The sequence d(m)*m^D*exp(-c*sqrt(m)) is summable for every fixed D:
d(m)<=m, group j^2<=m<(j+1)^2, and compare a polynomial times exp(-c*j).
Thus no alpha>1 restriction is needed for the divisor tail. All m>=2
remain exponentially negligible even after the extra sqrt(n) needed by
the first correction.

In38.7 replace log(n) by(log n)^(1-delta). Its logarithmic derivative is
(1-delta)/(n*log n), which is again lower order. Apply the same first-order
integer saddle and quadrature proof. Only AFTER that sum use the leading
w and E asymptotics. The log powers cancel, and the constant is unchanged:

 (1/X) sum_(n>=2) psi(n/X)*n^alpha*(log n)^(1-delta)
                       *exp(4sqrt(kappa*n))*S_w(n)
 -> -C*exp(1)*kappa^(1-alpha)/sqrt2*(alpha-1/4)*integral psi. (40.2)

This proves C40 for every real alpha,delta. It forces alpha=1/4 for any
all-row cancelling probability of this power-log critical shape.

At alpha=1/4 keep the exact v_k defined in C41; do NOT insert an error
term for E_k. Take beta=3/4 and OMIT the logarithmic row factor altogether.
The growing-band argument38.3 now gives a quantitative version of38.7:
for k in a fixed compact multiple of X,

 sum_(n>=2) psi(n/X)*n^(3/4)*exp(4sqrt(kappa*n))*K_k(n)/E_k
  =-c0*(b_k/E_k)*exp(2lambda*sqrt(T_k))*n0_k^(3/4)
       *[psi(n0_k/X)+(n0_k/X)*psi'(n0_k/X)+r_(k,X)],

 |r_(k,X)|<=C_psi*X^(-1/4)*(log X)^M,                  (41.1)
 c0=I*exp(1)*lambda/(2pi)>0.

Here M is a fixed integer. For explicit error accounting,38.3 costs
T^-1 times a fixed power of log T before the positive-u tilt. Choose
0<lambda*epsilon<1/4; after multiplying by sqrt(T) to normalize the first
correction, its cost is bounded by T^-1/4 times a log power. The negative
u cutoff can be chosen with lambda*B>2, and the positive-u and x tails
are superpolynomial. The quadratic prefactor/exponential errors and the
shifted-grid leading/correction errors are O(T^-1/2) after that same
normalization. All smooth test derivatives are bounded. There is no
1/log T loss in41.1, because the logarithmic factor has been removed and
E_k is still exact. These estimates also apply when the test and its
first derivative vanish at n0_k/X; an absolute error bound is asserted,
not a relative bound by the leading bracket.

The coefficient asymptotic and leading energy asymptotic imply

 v_k~c_w*(log k)^(delta-1), c_w=C/(2^(3/4)*sqrt(pi))>0.  (41.2)

The exact offset n0_k=(k+7/4)/kappa is retained in the equations. Thus
on any fixed compact multiple of X, sum v_k<=C*X*(log X)^q for some
fixed nonnegative integer q. Low and high k outside that range have the
same exponential savings as C38, since fixed logarithmic powers cannot
consume them. The complete divisor m>=2 contribution is exponentially
small by40.1. Multiplying41.1 by w_k and summing therefore yields, when
all actual S_w(n)=0,

 |sum_k v_k*[psi(n0_k/X)+(n0_k/X)*psi'(n0_k/X)]|
       <=C_psi*X^(3/4)*(log X)^M', X sufficiently large. (41.3)

Every term in this sum has k in a compact multiple of X; the displayed
bound also includes the already paid errors from all other coefficients
and divisors. It uses no derivative of v,w or E.

For X>0, F_psi(X)=X^-1*sum_k v_k*psi(n0_k/X) is C^1. On every compact
positive X interval, only finitely many k meet the fixed test support,
so differentiation of the sum is literal finite differentiation. It gives

 F_psi'(X)=-X^-2*sum_k v_k*[psi(n0_k/X)+(n0_k/X)*psi'(n0_k/X)].

By41.3, |F_psi'(X)|<=C X^(-5/4)*(log X)^M'. For sufficiently large X,
(log X)^M'<=X^(1/8). Integrating the derivative from X to infinity proves

 F_psi(X)=L_psi+O_psi(X^(-1/8)).                         (41.4)

This is the asserted quantitative conserved averaged flux, with every
energy factor exact. No uniformity over all test functions is claimed.

Choose psi>=0 with positive integral. Ordinary Riemann sums and41.2 give
F_psi(X)~kappa*c_w*(log X)^(delta-1)*integral psi. If delta>1 this
diverges, contradicting the finite limit41.4. If delta<1, the limit is0,
and41.4 would bound a positive logarithmic power-decay term by X^-1/8,
also impossible. Therefore delta=1. In that case, for every test psi,

 L_psi=kappa*c_w*integral psi,
 X^-1 sum_k v_k*psi(n0_k/X)
       =kappa*c_w*integral psi+O_psi(X^-1/8).             (41.5)

The positive survivor is41.4--41.5, including quantitative averaged
coefficient rigidity, not only exclusion of the other exponents.
Within the entire fixed power-log critical class, all-row cancellation
forces precisely alpha=1/4,delta=1. C39 remains OPEN: necessity does not
construct its coefficients or cancel its initial rows. No route is
retired before the actual C17/C32/C38/C40/C41 survivor is formalized.
Verdict PAPER BRIDGE; external scientific novelty unestablished.

## C42: the literal constant-flux candidate (OPEN)

Use the CRITICAL-line quantities a=pi/2,T_k=(2k+7/2)/a,
b_k=T_k^(2k+7/2)*exp(-a*T_k), n0_k=T_k/(2pi), not G11's sigma-four
saddle. Define exact positive coefficients and their normalization by

 q_k=(E_k/b_k)*exp(-2sqrt(pi)*sqrt(T_k))*n0_k^(-3/4),
 Z=sum_k q_k,  w*_k=q_k/Z.

C17 gives q_k~c*k^(-1/4)*log k*exp(-4sqrt(k)) for an explicit c>0.
Thus0<Z<infinity, every w*_k>0, and every polynomial/logarithmic moment
is finite. In C41's EXACT definition, v*_k=1/Z for every k. This passes
the averaged-flux necessity without differentiating E_k or imposing a
rate for its leading asymptotic.

The bold competing conjectures are literal: S_(w*)(n)=0 for every integer
n>=2; or at least one actual row is nonzero. [OPEN CORE]: determine these
actual responses, including the first nonvanishing correction if the
candidate fails. A constant averaged flux is only a necessary condition;
no pointwise cancellation follows from C41. Failure of this exact
candidate would not refute C39's more general coefficient class. Extract
its sharp residual or required correction before abandoning it. Audit
this precise candidate against current corpus/primary parents in the
next cycle; no scientific novelty or Lean claim is attached yet.

## C43: the first correction to critical flux (CONJECTURE)

Keep the critical-line T_k,b_k,n0_k and exact v_k of C41. Suppose
v_k=v0*(1+d/sqrt(T_k)+o(T_k^(-1/2))), v0>0,d real, and w is the
corresponding positive probability. This is a stated coefficient class,
not an assumption introduced into the main deficit target or Lean.
Conjecture the actual second-order weak law

 X^(-1/2) sum_(n>=2) psi(n/X)*n^(1/4)*exp(4sqrt(kappa*n))*S_w(n)
 -> -v0*pi*exp(1)/2 * [D+sqrt(pi)*d/2] * integral y^(-1/2)*psi(y)dy,
 D=(67-4pi^2)/96>0.                                      (43.1)

The competing alternative is failure of this constant through the actual
Gamma correction, signed Gaussian moments, integer quadrature or a
remote coefficient/divisor contribution. If43.1 holds, C42 has negative
rows in every sufficiently large fixed proportional interval, since its
v0=1/Z,d=0. The nontrivial positive survivor would force every all-row
canceller in the stated refined class to have

 d=(4pi^2-67)/(48sqrt(pi)).                              (43.2)

[OPEN CORE]: audit the full second saddle correction and every weighted
remainder to order T^-1; certify the constant rather than inferring it
from a truncated symbolic expansion. This is stronger than C41's flat
leading averaged flux, but does not decide unrestricted C39 or C15.

### C43 paper closure: second weak transport and the C42 residual

Verdict: BRIDGE, with new internal actual-kernel information; external
scientific novelty unestablished. This proves43.1 on PAPER, using the
complete C17/C32 paper estimates. It does not assert their Lean closure.
The following argument pays the second correction independently of an
asymptotic derivative of either w_k or E_k.

Put lambda=sqrt(pi), a=pi/2 and I=2pi/sqrt(a). The exact critical-line
Gamma factor has the strengthened expansion

 G(1/2+it)=sqrt(pi/2)*t^(7/2)*exp(-a*t)
  *exp(i*(t*log(t/(2pi))-t-pi/4))*(1+i/(24*t)+O(t^-2)).

Indeed s^2(s-1)^2=(t^2+1/4)^2 has no inverse-t term. The shifted
log-Gamma formula with z=it/2,h=1/4 has B2(1/4)=-1/48, giving
log Gamma(it/2+1/4)'s correction i/(48t). Squaring gives i/(24t).
DLMF5.11.8 and5.11(ii) supply uniform sectorial remainder bounds; this
vertical ray lies strictly inside their allowed sector.

Write epsilon=T^(-1/2), t=T+x*sqrt(T), u=(2pi*n-T)/sqrt(T), v=u-x.
As in38.3, n is an integer, so the full carrier exp(-2pi*i*n) is1.
The normalized complex integrand, before taking real part, has base
exp(-i*pi/4)*exp(-a*x^2/2)*exp(i*v^2/2). After multiplying by
(n/n0)^beta*exp(4sqrt(kappa*n)-2lambda*sqrt(T)), its additional factor is

 exp(lambda*u) * [1+epsilon*A_beta
                    +epsilon^2*(B_beta+A_beta^2/2)+O(epsilon^3*P)],
 A_beta=a*x^3/3-i*x*v^2/2-i*v^3/3+(beta-1/2)*u-lambda*u^2/4,
 B_beta=-a*x^4/4+i*(x^2*v^2/2+2*x*v^3/3+v^4/4)
                    +(1/4-beta/2)*u^2+lambda*u^3/8+i/24.   (43.3)

Here P is a fixed polynomial in1+|x|+|u| on the retained growing band.
To check the phase term, its second coefficient is
x^4/12-x*u^3/3+u^4/4=x^2*v^2/2+2*x*v^3/3+v^4/4.
The real amplitude has logarithmic terms a*x^3/3 and-a*x^4/4;
the inverse square-root prefactor gives-u/2 and u^2/4; the row power
gives beta*u and-beta*u^2/2; the square-root exponential gives
-lambda*u^2/4 and lambda*u^3/8. The Gamma term contributes i/24.
Thus43.3 retains every term of this order.

For a test psi supported in[A,B] inside the positive line, take beta=3/4.
In addition to43.3, expand psi(y*(1+epsilon*u)) through second order,
y=n0/X. The leading tilted mass is0. Its first coefficient is precisely
-I*exp(1)*lambda*[psi(y)+y*psi'(y)], as in C41. Define real constants

 C0=Re(I*exp(1)*i * E[B_(3/4)+A_(3/4)^2/2]),
 C1=Re(I*exp(1)*i * E[u*A_(3/4)]),
 C2=Re(I*exp(1)*i * E[u^2])/2.

The moment functional E has independent Gaussian coordinates X,V, with
means lambda/a,i*lambda and variances1/a,i. This is shorthand for
regularized Gaussian integrals: replace exp(i*v^2/2) by
exp(-(delta-i)*v^2/2),delta>0, do absolute Fubini and polynomial moment
integration, then let delta decrease to0. The post-X-integral reciprocal
variance has positive real part uniformly near delta=0. A common
polynomial-Gaussian majorant pays the limit with exp(lambda*u), exactly
as in38.5. No unregularized absolute Fresnel interchange is used.

The inner integer-row sum is therefore

 B_(k,X)=(b/E)*exp(2lambda*sqrt(T))*n0^(3/4)/(2pi) *
   {-I*exp(1)*lambda*(psi+y*psi')
             +T^-1/2*(C0*psi+C1*y*psi'+C2*y^2*psi'')
             +o(T^-1/2)}.                               (43.4)

The error is uniform for k in a fixed compact multiple of X. Here is
its full payment. Keep-B0*log T<=u<=epsilon0*log T and|x|<=L*log T,
with lambda*B0>3 and0<lambda*epsilon0<1/4. Taylor remainders through
second order are O(T^-3/2*(log T)^M) before the tilt; afterward they
are O(T^-5/4*(log T)^M)=o(T^-1). The omitted positive-u and x tails
are superpolynomial by C32 and the Gaussian saddle bound; the negative-u
tail is O(T^(-lambda*B0)), even after any fixed polynomial factor.
C17 pays the low/far height intervals exponentially. Multiplication by
the u-grid density sqrt(T)/(2pi) leaves o(T^-1/2) in43.4.
For the explicit polynomial-Gaussian terms, shifted-grid quadrature can
be taken to order4 for the leading term, order3 for the first, and
order2 for the second. Repeated integration by parts with the bounded
periodic Bernoulli functions bounds the respective errors by h^r times
the L1 norm of the r-th derivative, h=2pi/sqrt(T). All those derivatives
are integrable uniformly in y. The resulting errors are o(T^-1) before
the grid density. Compact coefficient ranges and all divisor m>=2 tails
are paid by C38/C40: their exponential savings absorb this extra power
of X. Since v_k is bounded, w_k has C40's quarter-power/log upper bound.
These arguments also cover tests whose displayed leading jets vanish.

Multiply43.4 by w_k, leaving its exact outside factor v_k. In the
constant v0 part, sum(psi+y*psi') has zero limiting integral and in fact
O(X^-1) error: the smooth compactly supported summand has integral0,
and a second-order quadrature bound applies to the exact shifted lattice
n0_k=(k+7/4)/kappa. After division by sqrt(X) this vanishes. The
coefficient remainder o(T^-1/2) in v_k contributes o(sqrt(X)) to the
unscaled sum by uniformity on compact multiples. No difference or
derivative of v_k, w_k or E_k is taken.

For the remaining terms, ordinary Riemann sums with T=2pi*X*y give

 X^-1/2 sum_k T_k^-1/2 f(n0_k/X)
 -> kappa/sqrt(2pi)*integral y^-1/2*f(y)dy.               (43.5)

Integration by parts against y^-1/2 gives factors-1/2 for y*psi' and
3/4 for y^2*psi''. Consequently the second kernel coefficient is
C0-C1/2+3*C2/4. Since A_(1/4)=A_(3/4)-u/2 and
B_(1/4)=B_(3/4)+u^2/4, this equals

 Re(I*exp(1)*i * E[B_(1/4)+A_(1/4)^2/2]).               (43.6)

Here is explicit algebra for its sign and constant, avoiding an
unevaluated Gaussian expectation. Conditional on X=x, write
A_(1/4)=P+Q*V+R*V^2+S*V^3, with

 P=a*x^3/3-x/4-lambda*x^2/4, Q=-1/4-lambda*x/2,
 R=-lambda/4-i*x/2, S=-i/3.

The first six V moments are
 i*lambda, -lambda^2+i, -3lambda-i*lambda^3,
 lambda^4-3-6i*lambda^2, 10lambda^3+i*(lambda^5-15lambda),
 -lambda^6+45lambda^2+i*(15lambda^4-15).
Expanding the square and collecting its imaginary part gives

 Im E_V[A_(1/4)^2]
   =a*lambda*x^3/3+(5/2)*lambda*x+59/48-lambda^4/3.

Using E[X]=lambda/a, E[X^2]=lambda^2/a^2+1/a and
E[X^3]=lambda^3/a^3+3lambda/a^2 therefore yields

 Im E[A_(1/4)^2]
   =lambda^4/(3a^2)+7lambda^2/(2a)+59/48-lambda^4/3,
 Im E[B_(1/4)]
   =-lambda^4/(8a^2)-3lambda^2/(2a)+lambda^4/8-7/12.

Their prescribed sum is
lambda^4/(24a^2)+lambda^2/(4a)-lambda^4/24+1/32
=(67-4pi^2)/96=D. Thus43.6=-I*exp(1)*D. The d/sqrt(T)
coefficient perturbation multiplies the first term in43.4; integration
by parts gives its additional constant-I*exp(1)*lambda*d/2.
Finally kappa*I/(2pi*sqrt(2pi))=pi/2. Equations43.4--43.6 prove43.1.
D>0 follows already from0<pi<4, which gives4pi^2<64<67.

For C42, v0=1/Z,d=0 exactly. For every nonnegative smooth test of
positive integral,43.1 is strictly negative. Hence every sufficiently
large interval[X,(1+epsilon)X],epsilon>0 fixed, contains an actual
negative S_(w*)(n). C42's all-row cancellation conjecture is FALSE on
PAPER. This is stronger than merely finding one nonzero row.

The positive survivor is the exact second weak transport law43.1.
Every all-row canceller in the stated refined coefficient class must
satisfy43.2. This does not assume all C39 coefficients admit such an
expansion. No failed route is retired before this actual survivor and
its C17/C32 analytic dependencies are formalized. Main deficit OPEN.

## C44: positive first-corrected flux candidate (OPEN)

Set d*=(4pi^2-67)/(48sqrt(pi)) and
q**_k=q_k*(1+d*/sqrt(T_k)), w**_k=q**_k/sum_j q**_j.
The factor is strictly positive at every k: -1<d*<0 and T_k>=7/pi>1.
The normalization is finite positive by comparison with C42's q.
Thus this is a literal positive probability with the forced first flux
correction. Competing conjectures: all actual integer rows vanish;
or a further unavoidable residual survives. [OPEN CORE]: determine that
residual or construct an exact correction, including initial rows.
Neither necessary asymptotic condition asserts cancellation.

## G12: actual inverse Mellin recovery, paper before Lean

For each fixed k, the actual finite Bessel polynomial K_k is continuous
on x>0: every Bessel term is differentiable in its positive argument,
and only finitely many terms occur. G5 proves MellinConvergent at4;
G11 proves the actual Mellin transform is absolutely integrable on that
vertical line. The Mellin inversion theorem therefore gives, for every
x>0, with literal M_k(4+it),

 K_k(x)=(1/(2pi))*integral_R x^(-4-it)*M_k(4+it)dt.

This integral is absolute because|x^(-4-it)|=x^-4 and G11 is absolute.
Taking norms and using G11's integral estimate yields

 |K_k(x)|<=10/pi*exp(7pi/2)*B_k*sqrt(T_k)/x^4,

where here T_k=(2k+7)/(pi/2) is G11's SIGMA-FOUR saddle. All parameters
are actual, no convergence or continuity hypothesis is left unpaid.
Classification CLASSICAL ANALYTIC BRIDGE. Critical-line inversion and
its asymptotic/differentiated tails remain subsequent obligations.

## G13: pay critical-line inversion without a new Stirling bound

This is the next analytic BRIDGE, with a complete paper proof before
formalization. For every0<u<v and real y, the beta integral implies

 |Gamma(u+iy)| <= Gamma(u)/Gamma(v) * |Gamma(v+iy)|.       (G13.1)

Indeed Gamma(u+iy)*Gamma(v-u)=Gamma(v+iy)*B(u+iy,v-u).
The defining integral over(0,1) is absolute; taking its norm removes
x^(iy) and bounds it by B(u,v-u). All real Gamma factors are positive,
and the real beta-Gamma identity cancels Gamma(v-u). ThusG13.1 is a
classical exact comparison, including y=0 and negative y.

Apply u=1/4,v=2,y=t/2. In the actual critical-line Mellin transform,
|s-1/2|^(2k)=|t|^(2k) and|s|^2|s-1|^2=(t^2+1/4)^2.
These are bounded respectively by(t^2+49/4)^k and
(t^2+16)*(t^2+9), the sigma-four factors. The pi powers have ratio
pi^(7/2), and Gamma(2)=1. Hence for all k and all real t,

 |M_k(1/2+it)| <= pi^(7/2)*Gamma(1/4)^2*|M_k(4+it)|.     (G13.2)

G11 therefore proves absolute critical-line vertical integrability.
Every even height moment is also absolute: exactly
M_(k+m)(1/2+it)=t^(2m)*M_k(1/2+it). Odd/nonnegative integer moments
follow from|t|^r<=1+|t|^(2r). G5 already supplies absolute Mellin
convergence at1/2 and the actual finite Bessel polynomial is continuous
on positive x. Mellin inversion now recovers K_k on the critical line
with every convergence premise discharged. This does not yet prove the
uniform-in-k local saddle remainder or its differentiated tail estimates.

Corpus search wp06-g13-beta-comparison returned nonpartial/errors[] at
68878 files, but its proposed symmetry chain is inapplicable. Actual
GammaVerticalRatioAsymptotic and SmoothAFEZetaStripBound supply existing
ratio limits/bounded-width large-height bounds. Mathlib Gamma/Beta has
the exact beta-Gamma identity used above. Reuse those sources as needed;
do not presentG13.1 as novel mathematics. Formal status: NOT STARTED.

## C45: one positive probability with an all-orders invisible integer tail

Exact conjecture, stronger than cancelling any fixed finite asymptotic jet:
there exist one strictly positive probability w on the nonnegative derivative
orders, one v0>0, and real coefficients d_j (d_0=1), such that, with the
actual E_k, critical T_k,b_k,n0_k and actual rows S_w(n) defined above,

 v_k/v0 = sum_{j=0}^N d_j T_k^(-j/2) + O(T_k^(-(N+1)/2))

for every nonnegative integer N, and for every M>=0 there are C_M,N_M
such that all integers n>=N_M satisfy

 |S_w(n)| <= C_M n^(-M) exp(-4 sqrt(kappa*n)).

The probability w is chosen BEFORE M and N. The conjecture predicts
d_1=(4*pi^2-67)/(48*sqrt(pi)), as forced by C43. It does not assert
S_w(n)=0, or any spectral deficit estimate. A competing conjecture says
an unavoidable finite-order residual prevents this property.

Motivation from the actual corpus: C40 fixes the leading flux; C43 kills
the uncorrected candidate but exposes a nonzero coefficient lambda/2
for its first correction. G10 proves a simple zero of the critical
tilted profile. These suggest a triangular transport recursion, not an
infinite repetition of unrelated coefficient guesses. At formal order j,
the candidate transport coefficient is j*lambda/2; this formula beyond
j=1 is presently a derivation target, NOT a proved result.

[OPEN CORE] Prove an all-orders, pointwise INTEGER-row expansion for the
actual derivative-order sum, including uniformly controlled remote
orders and all divisor terms. Then prove the triangular coefficient
never vanishes and realize its formal solution by one positive sequence.
Weak averaged C43 alone does not supply this pointwise expansion. Borel
realization alone does not supply any estimate on S_w.

Attack and SOTA audit: wp06-c45-frontier (deep) and wp06-c45-exact
(hybrid) both finished nonpartial/errors[], covering68880/68882 files;
compiler coverage remains mostly source-only/pending. Every returned
candidate lemma/source argument was inspected. The proposed zero-series
ingredient chain is irrelevant: analytic uniqueness cannot identify a
flat asymptotic remainder with zero. Existing ReesAllOrdersFlat machinery
handles already-established flatness, not the actual row expansion.
No applicable all-orders actual-kernel theorem was returned.

External parents are classical asymptotic summation, Borel realization,
and stationary-phase transport. Zagier's Mellin-transform notes,
https://people.mpim-bonn.mpg.de/zagier/files/tex/MellinTransform/fulltext.pdf,
Proposition3 explicitly retain derivative and rapid-decay requirements
in an all-orders sum expansion. NIST DLMF2.11,
https://dlmf.nist.gov/2.11, explains the nonuniqueness hidden by a full
asymptotic expansion. Costin's notes,
https://people.math.osu.edu/costin/806-12/c1.pdf, distinguish formal series
from Borel summability, which additionally requires continuation and
growth control. The2026 Planat preprint
https://www.preprints.org/manuscript/202608.1692 concerns cancellation
between longitudinal/transverse theta sectors, a different object;
its exponentially small remainder is a warning, not a proof of C45.
Exact positive derivative-order weights and this integer-row statement
were not found in the searches. This is not a novelty certification.

Verdict: SURVIVES PRELIMINARY ATTACK; unproved. Even success could expose
only a classical transport mechanism specialized to this kernel. The
scientific discriminator is whether the surviving beyond-all-orders
remainder has a sign or admits exact cancellation. Keep that distinction
visible; do not substitute C45 for the assigned actual-deficit goal.

Additional primary parent checked: Melrose, Introduction to Microlocal
Analysis, Proposition2.3 (asymptotic summation),
https://math.mit.edu/~rbm/iml90.pdf, proves realization modulo symbols of
order minus infinity by cutoffs moving to infinity. A positive leading
constant permits positivity after altering a compact range. This pays
the abstract realization mechanism once the actual row expansion and
recursion are proved; it supplies neither of those missing arguments.
The remainder freedom is mathematically material to any exact-row claim.

### C45 angular construction: dependency-closed paper proof

The open core above can be replaced by a constructive subclass. C25
already proved the complex-dilation/Mellin transport; that mechanism is
NOT new. C26 also warned that positive Taylor coefficients need not have
positive real moment carriers. We use only weights explicitly constructed
from such a carrier, never assert a representation for arbitrary weights.

Put a=pi/2, c=2*sqrt(2)*pi=4*sqrt(kappa), and r=1/sqrt(2).
Choose a smooth nonnegative cutoff chi supported in [0,u0), equal to1
near0, with0<u0<a. A smooth positive function V with V(0)=1 will be
constructed below. Define, for0<u<u0,

 mu(u)=chi(u)*u^6*exp(-pi/u)*V(u),
 c_k=1/(2k)! * integral_0^u0 (a-u)^(2k)*mu(u) du.        (45.1)

Extend mu by0 at0. It is smooth and flat there. Every c_k is strictly
positive. The actual product kernel at order0 has the holomorphic
continuation from C25, denoted K_0(z) here; Bessel order is distinguished
by a superscript B. Its formula and uniform expansion are

 K_0(z)=4(pi*z)^2[(4(pi*z)^2+9)K_0^B(2pi*z)
                                  -12pi*z*K_1^B(2pi*z)],
 K_0(z)=8*pi^4*z^(7/2)*exp(-2pi*z)
                       *[1-49/(16*pi*z)+O(z^-2)].       (45.2)

There is a full expansion in integer inverse powers with uniform
remainders on pi/2-u0<=arg z<=pi/2. These are fixed Bessel orders0,1
in a closed proper subsector of |arg z|<3pi/2; DLMF10.40.2 and its
complex remainder bounds10.40.10--12 apply. The coefficient displayed
in45.2 is -1/(16pi)-3/pi=-49/(16pi). No growing Bessel order is used.

**Exact transfer and convergence.** Let

 G(t)=integral_0^u0 mu(u)*cosh((a-u)*t) du,
 F(x)=Re integral_0^u0 mu(u)*exp(i*(a-u)/2)
                                      *K_0(x*exp(i*(a-u))) du. (45.3)

The positive cosh series gives G(t)=sum_k c_k*t^(2k). For large |t|,
Laplace's method for pi/u+|t|u gives
G(t)=O(exp(a|t|-2sqrt(pi|t|))*|t|^(-15/4)); on bounded t it is bounded.
Indeed u=z/sqrt(|t|) has unique nondegenerate minimum z=sqrt(pi);
its powers contribute |t|^(-7/2) and its Gaussian width |t|^(-1/4).
Outside a fixed compact z interval the exponent has a fixed positive
gap, as in the detailed tail argument below. This bound suffices even
without the leading equivalent. The exact critical Mellin symbol M_0
is O((1+|t|)^(7/2)*exp(-a|t|)). Thus |M_0|G is integrable.

C25's complex-dilation identity, first at each0<a-u<a and then by
absolute Fubini using |M_0|G, proves

 F(x)=sum_k c_k*K_k(x), x>0.                              (45.4)

The phase exp(i*(a-u)/2) is necessary: it cancels the half-line factor
in (x*exp(i*(a-u)))^(-s). Taking the real part averages the two conjugate
dilations, hence produces cosh((a-u)*t). The order identity is exactly
M_k(1/2+it)=t^(2k)M_0(1/2+it), now checked in G13. Absolute power-series
interchange follows by summing c_k|t|^(2k) against |M_0|. This proves
45.4 for the actual finite Bessel kernels, not merely formal symbols.

**All-orders row expansion.** At integer x=n set h=n^(-1/2) and u=h*z.
The factor exp(-2pi*i*n) is1. From45.2 the complex integrand's leading
prefactor is8pi^4*n^(7/2)*u^6*exp(-pi/u), and its remaining phase and
exponent are

 exp(-2pi*n*sin(u)+i*2pi*n*(1-cos(u))-i*4u)
 =exp(-f(z)/h)*exp(i*pi*z^2)
    *[1+h*((pi/3)*z^3-i*4z)+O(h^2)] * exp(pi/(h*z)),
 f(z)=pi/z+2pi*z.                                       (45.5)

The final factor in45.5 only compensates the already displayed
exp(-pi/u); the full exponent is -f(z)/h. Equivalently expand the full
product directly, leaving exp(-f/h) factored out. The unique minimum
is z=r=1/sqrt2, f(r)=c, f''(r)=2pi/r^3>0. There is a full smooth
parameter expansion near r in integer powers of h. The first Bessel
correction is order h^2, so does not enter the first transport term.

Here are the remainder gates for every fixed truncation order L.
Choose0<l<r<R so pi/l>c+1 and2pi*s0*R>c+1, where
s0=min_(0<=u<=u0) sin(u)/u>0. For u<lh or u>Rh the real exponent
pi/u+2pi*n*sin u is at least(c+1)/h. Polynomial factors and all fixed
orders of required derivatives cost only powers of h^-1; this is
smaller than every power times exp(-c/h). On l<=z<=R, Taylor expansion
of sin, cos, the smooth V, and the fixed-order Bessel amplitude has
uniform remainders of arbitrary order. Outside a fixed neighborhood
of r, f>=c+delta. Near r use the smooth coordinate
q=sign(z-r)*sqrt(2*(f(z)-c)/f''(r)); its derivative at r is1, so it is
a local diffeomorphism. Taylor expansion of the transformed amplitude,
integration of the Gaussian exp(-f''(r)*q^2/(2h)), and its exponentially
small truncated tails give the full Laplace expansion and a uniform
O(h^(L+1)) remainder after normalization. Odd q moments vanish; only
integer h powers survive. This also proves the needed expansion for
complex amplitudes by treating real and imaginary parts separately.

For any smooth V with Taylor coefficients v_j (v_0=1), there is therefore
one positive constant A, independent of V, such that

 sqrt(n)*F(n)=A*h^(-1/2)*exp(-c/h)
              *[sum_(ell=0)^L R_ell(v)*h^ell+O_V,L(h^(L+1))]. (45.6)

Every R_ell is a real linear function of finitely many v_j. Coefficients
beyond v_ell cannot enter, since V(hz) contributes v_j*h^j*z^j.
The leading phase exp(i*pi*r^2)=i implies R_0=0. More strongly, every
v_j has zero real contribution at its own order h^j. We compute the
first later contribution exactly, which makes the entire recursion
nondegenerate.

For the amplitude z^beta*exp(i*pi*z^2), divide the first Laplace
coefficient by its leading value at r. The imaginary part is

 (4pi*beta+2pi)/(2*f''(r))
    -(2pi*r)*f'''(r)/(2*f''(r)^2)-4r
 = (beta+2)*r^3-4r = r*(beta-6)/2,                       (45.7)

using f'''(r)=-6pi/r^4 and r^2=1/2. The remaining standard first
Laplace terms, and the real correction(pi/3)z^3, have real ratios and
therefore contribute no real part after the leading factor i. Formula
45.7 can also be obtained directly from the Gaussian Taylor argument
above; its a'' and a'f''' terms are respectively1/(2f'') and
-f'''/(2f''^2). Thus R_1=0 when beta=6. For the monomial v_j*u^j,
beta=6+j and the extra leading ratio is r^j. Consequently, for every
j>=1,

 R_(j+1)=B_j(v_1,...,v_(j-1))-(j*r^(j+1)/2)*v_j.         (45.8)

The coefficient of v_(j+1) is zero by the leading-phase observation;
no still higher coefficient appears. This is the exact triangular law,
not an extrapolation from the first correction. Its diagonal is nonzero
for every j>=1. Define v_j recursively to make45.8 zero. This chooses
one infinite real Taylor jet with v_0=1 and kills every R_ell.

**One positive realization.** Borel's smooth-jet construction realizes
this single jet by a smooth V near0. For completeness one can take
1+sum_(j>=1) v_j*u^j*chi_j(u), with chi_j=1 near0 and supports shrinking
so that each term has supremum at most2^(-j-2), and its C^m norms are
at most2^-j for all m<j beyond the finite initial terms. These conditions
are possible by shrinking the support; they give convergence in every
C^m norm, the prescribed jet, and V>=3/4. No convergence of the formal
Taylor series, analytic continuation, or Borel-Laplace summability is
assumed. A further fixed cutoff supplies the chi in45.1. The same V
works for EVERY L in45.6. Hence for every M,

 |F(n)|=O_M(n^-M*exp(-c*sqrt(n)))                         (45.9)

over all sufficiently large integers n. This is pointwise, not averaged.

**Actual probability, all divisors, exact flux.** Set N=2k and
T=(N+7/2)/a, the critical-line saddle. Applying the same ordinary
Laplace argument to45.1, now with u=z/sqrt(T), gives

 c_k = C*b_k^(-1)*n0_k^(-3/4)*exp(-2sqrt(pi*T))
                *[1+sum_(j=1)^L d_j*T^(-j/2)+O_L(T^(-(L+1)/2))], (45.10)

with C>0 and one full real jet d. To verify all powers, factor
(a-u)^N=a^N*exp(N*log(1-u/a)). Its exponent becomes
-sqrt(T)*(pi/z+z)-z^2/(2a)+O(T^-1/2), with minimum z=sqrt(pi).
The measure and Gaussian width contribute T^(-15/4). Stirling's full
factorial expansion for N! then gives
(a^N/N!)*b_k = T^(7/2)/sqrt(2pi*a*T) * (1+O(T^-1));
the extra (1+(7/2)/N)^N*exp(-7/2) also has a full integer T^-1
expansion. Thus c_k*b_k has leading T^-3/4, exactly45.10 after absorbing
(2pi)^(3/4) into C. All higher corrections are integer powers of
T^-1/2. Remote u and smooth-amplitude remainders are handled as above.
No energy asymptotic is used.

G12 gives |K_k(x)|<=C1*B4_k*sqrt(T4_k)*x^-4. Here
T4=T+(7/2)/a, and direct (1+s)^p<=exp(ps) gives
B4_k/b_k=O(T^(7/2)), sqrt(T4)=O(sqrt(T)). Therefore45.10 implies

 sum_k c_k*B4_k*sqrt(T4_k)<infinity.                     (45.11)

Every actual E_k is positive: the real Schwartz Riemann kernel is
nonzero, and an identically zero kth derivative would make it a
polynomial, contradicting its decay and nonzero value. Its continuous
nonzero kth derivative has strictly positive squared integral. The
actual divisor identity E_k=A(1,k)=sum_(m>=1)d(m)K_k(m), together with
G12 and sum d(m)m^-4=zeta(4)^2<infinity, bounds E_k by the same quantity
in45.11. Thus Z=sum_k E_k*c_k is finite and strictly positive, and

 w_k=E_k*c_k/Z

is one strictly positive probability. Equations45.11 and G12 justify
absolute Fubini of BOTH k and all divisor indices m, at every fixed x>0:

 S_w(n)=sqrt(n)/Z * sum_(m>=1) d(m)*F(m*n).               (45.12)

There is no unproved interchange under conditional arithmetic convergence.
For integer n large, EVERY m*n is an integer in the range of45.9.
Use45.9 with power M+2, factor exp(-c*sqrt(n)), and sum
sum d(m)m^(-M-2)<infinity (or use a still higher power when M=0).
This proves C45's claimed bound for the entire actual row, including
all divisors. Finally w_k*b_k/E_k=c_k*b_k/Z exactly, so45.10 gives its
claimed full flux expansion with v0=C/Z>0. C43 then forces its first
coefficient d_1=(4pi^2-67)/(48sqrt(pi)); that inference needs only the
already proved second weak law, not any subleading energy expansion.

This completes the PAPER construction of C45. Exact cancellation of
all integer rows is not proved. The result says that no finite
algebraic-order tail obstruction can rule out every positive candidate:
one actual positive probability passes all such asymptotic tests at once.
Its remaining row errors are beyond every power at the critical scale.
They can still be nonzero and can still obstruct C15 or the deficit goal.
Full Lean formalization is OWED, and no route is retired.

Novelty/significance audit: positive cosh moments and complex dilation
are classical parents and already present in C25; the all-orders
triangular boundary law45.8 and this actual positive probability are the
new corpus claims to audit. External queries for the exact positive
Bessel/integer/flat mechanism found no applicable theorem, but cannot
certify novelty. The mechanism resembles classical transport plus Borel
realization. Corpus generating search was partial (malformed local-model
JSON and reranker deadline),68893 files; all available20+20 statements
inspected, none supplies this construction. Exhaustive owned text search
exposed C25/C26, explicitly reused above. Status: PAPER PROVED; attack
verdict SURVIVES PRELIMINARY ATTACK. Scientific novelty unestablished;
formal target remains open. The two rational identities in45.7 also
passed /tmp/wp06-c45-algebra.lean (empty log, exit0); this is only an
auxiliary algebra check, not a formal proof of the actual construction.

## C46: exact cancellation inside the positive angular subclass (OPEN)

After C45, test a stronger statement instead of calculating another
finite correction. There exists a nonnegative smooth density mu on[0,a],
a=pi/2, with, for all sufficiently small positive u,

 mu(u)=u^6*exp(-pi/u)*V(u),

where V is smooth up to0, V(0)=1, and V has the unique recursively chosen
Taylor jet from45.8, such that its literal angular integral

 F_mu(n)=Re integral_0^a mu(u)*exp(i*(a-u)/2)
                                  *K_0(n*exp(i*(a-u)))du

is zero for EVERY integer n>=2. Away from0 the nonnegative density is
free; V can vary by functions flat at0. Thus this is not the unsupported
claim that C45's first chosen cutoff already cancels small integers.
The moments45.1 with upper endpoint a would then give a strictly
positive exact C15 probability by the same G12 convergence argument.
F_mu(1)=Z>0 follows from actual energy normalization and all-divisor
inversion; it is not imposed as an extra hypothesis.

The competing conjecture is that positivity supplies a nonzero exact
obstruction for every such density, despite complete asymptotic flatness.
A finite signed combination of actual integer kernels that is nonnegative
on the entire angular interval and strictly positive near its endpoint
would be one possible certificate. No such certificate is assumed.

[OPEN CORE] Solve the countable exact angular equations while preserving
nonnegativity, or prove the obstruction. Neither the triangular Taylor
recursion nor Borel's realization theorem controls these exact values.
Falsity would retire only this positive moment subclass, not all positive
Taylor coefficients or unrestricted C15. Any no-go must retain C45's
nontrivial all-orders positive survivor and formalize it before retirement.

Corpus C46 search finished nonpartial/errors[],68897 files, all20+20
candidate/source statements inspected. Actual sources checked:
CompactCarrierSectorUniqueness's UniformSectorCarrierPositive requires
strict uniform positivity on a compact carrier; this boundary carrier
approaches exp(ia)=i, so even its positive-real-axis minimum is0. Also
CompactCarrierFrequencyCompleteness's Lambert-ray theorem assumes zero
on a real ray, which our integer data do not supply. Neither theorem
settles C46. RiemannXiSuzukiCarrierCayleyMomentDecay concerns a different
arctan-transformed xi-energy density and L2 moment decay, not these
angular moments. C25's strict Carlson type threshold likewise does not
cover an endpoint at a=pi/2. Current exact-mechanism external searches
returned classical cosh/moment and asymptotic parents, no applicable
exact theorem; novelty remains unestablished. Verdict: SURVIVES
PRELIMINARY ATTACK. Continue formalizing the actual C45 transport while
attacking this exact, beyond-all-orders question.

G13 final status: actual critical Mellin inversion and every natural
height moment formalized with seven unconditional public statements.
Leaf, unchanged direct source, and all seven type/axiom audits passed.
Only standard foundations.38 finished modules/163 theorem audits,
all umbrella imports exactly once. No actual deficit upper bound.

## G14 paper bridge: full angular admission and actual derivative series

Before formalization, the exact analytic gates are as follows. For every
real rho<pi/2 and every natural k,m,

 integral_R exp(rho*|t|)*|t|^m*|M_k(1/2+it)| dt < infinity.

Use G13's comparison with M_k(4+it). For t>=1 the exact G11 sigma-four
norm formula and 1/sinh(pi*t/2)<=4exp(-pi*t/2) give

 |M_k(4+it)| <= (53/4)^k*850/(8pi^3)*t^(2k+7)*exp(-pi*t/2).

Indeed t²+49/4<=(53/4)t²; the remaining quadratic factors are at most
5t²,10t²,17t². Conjugation handles negative t. Outside[-1,1], the
weighted critical integrand is bounded by a polynomial times
exp(-(pi/2-rho)|t|), which is absolutely integrable by the bilateral
Gamma integral. Inside[-1,1], exp(rho|t|)<=exp(|rho|), so existing G13
integrability pays the remaining term. Natural moments can also be
recovered from M_(k+j)=t^(2j)M_k and |t|^m<=1+|t|^(2m).

For every real theta with |theta|<pi/2, every k and x>0, dominated cosh
summation then gives the exact actual-kernel identity

 sum_(j>=0) theta^(2j)/(2j)! * K_(k+j)(x)
  = (1/(2pi)) integral_R x^(-1/2-it)*cosh(theta*t)
                                              *M_k(1/2+it) dt.

The equality is complex-valued, with real kernels cast into C. Each
summand's integral is G13's actual inversion and order-raising identity.
The sum of the norms is x^-1/2*cosh(theta*t)*|M_k| and is integrable by
the preceding exponential admission. This proves absolute summability
and Fubini; no formal-series interchange or integrability assumption is
left in the proposed public statements. Natural angle/positive-x domains
are parameters. Identifying the resulting integral with the rotated
Bessel polynomial remains a separate analytic-continuation step; do not
label that identification proved by this series identity alone.

Classification BRIDGE: classical cosh series and exponential admission.
Current corpus search G14 nonpartial/errors[],68899 files, all20+20
statements and the proposed inversion/moment chain inspected; it leaves
exactly the actual domination/link obligations above. Existing
HTGeometry.TwoSidedExponentialMoments supplies the polynomial-exponential
integrability; ComplexRayMellinInversion supplies relevant continuation
patterns, not this actual transform's hypotheses.

## C47: angular first-divisor energy gap (OPEN)

C46 has an exact scalar obstruction worth attacking before attempting an
infinite correction scheme. For0<=theta<a=pi/2 define actual quantities

 E(theta)=sum_(k>=0) theta^(2k)/(2k)! * E_k,
 B(theta)=Re[exp(i*theta/2)*K_0(exp(i*theta))],
 Delta(theta)=E(theta)-B(theta).

Conjecture C47a: Delta(theta)>0 for EVERY0<=theta<a.
Competing C47b: some interior theta has Delta(theta)<=0. This is a
falsifiable assertion about fixed actual kernels, not an assumed positive
carrier or a reformulation of small deficit. Convergence for theta<a
follows from G12's energy bound and ordinary factorial growth; B is the
same literal rotated Bessel polynomial used in C25/C45.

If C47a holds, every nonzero nonnegative C46 density has
integral mu(u)Delta(a-u)du>0. Exact C46 integer cancellation would make
this integral sum_(m>=2)d(m)F_mu(m)=0, a contradiction. Absolute Fubini
is exactly the G12/C45 argument already paid, not a new interchange
assumption. Thus C47a would exclude this entire positive angular moment
subclass while retaining C45's all-orders-flat positive survivor.
It would not exclude arbitrary positive derivative weights: C26 already
shows that positive Taylor coefficients need not be positive cosh moments.

Initial attack: G8 proves E_0-K_0(1)>0 and E_1-K_1(1)<0. Therefore the
Taylor series of Delta has a positive constant but negative quadratic
coefficient. A termwise-positive proof is impossible. Continuity gives
positivity in some interval near0, but does not cover the interior.
The Bessel term stays bounded as theta tends to a, whereas C12's PAPER
energy growth gives E(theta)->infinity by positivity of its coefficients.
That yields another positive endpoint interval on paper, still no
interior conclusion. [OPEN CORE]: control the compact intervening
angular interval, or produce an analytic sign counterexample. No
numerical sampling is authorized or used.

Corpus search C47-gap nonpartial/errors[],68902 files; all20 candidate
and20 source-argument statements plus suggested chain inspected. Real
shift autocorrelation decay and DeBruijn heat-source theorems do not
prove this imaginary-shift first-divisor comparison. Exact G8 low-order
signs are the applicable existing evidence. External search located
Stochel--Stochel arXiv2306.14338 (opened), characterizing positive cosh
transforms via exponential convexity; it supplies a parent class, not
this kernel gap. The adjacent2026 theta-sector paper concerns a different
growth derivative; no result from it is imported. Verdict: SURVIVES
PRELIMINARY ATTACK. C46 and the main spectral-deficit target remain open.

### C47 attack: exact pi/6 sign reversal (PAPER PROVED; Lean owed)

The universal positive-gap conjecture C47a is FALSE. Its positive survivor
is an explicit alternating-sign law for the actual rotated kernel, a
strict negative energy gap at pi/6, and an interior zero of that gap.
This does not retire C46 or prove any individual integer row vanishes.

Put theta=pi/6, c=cos(theta)=sqrt(3)/2, a=sqrt(3)*pi and

 B_m=Re[exp(i*theta/2)*K_0(m*exp(i*theta))],
 A_m=8*pi^4*m^(7/2)*exp(-a*m), m>=2 an integer.

Then the quantitative survivor is

 (4/9)*A_m <= (-1)^(m+1)*B_m <= (5/9)*A_m.        (47.1)

Here K_0 is the actual G4 polynomial in the order-zero/order-one Bessel
functions, with its principal holomorphic continuation. The proof uses
no numerical evaluation or sampling. All constants below are elementary
analytic inequalities.

For Re w>0, the classical Bessel integral (DLMF10.32.9), followed by
u=cosh(t)-1, gives

 K_j^B(w)=exp(-w)/sqrt(2) * integral_0^infty
          exp(-w*u)*u^(-1/2)*g_j(u) du, j=0,1,
 g_0(u)=(1+u/2)^(-1/2), g_1(u)=(1+u)*g_0(u).

The substitution is increasing, has the displayed Jacobian, and both
integrals converge absolutely. Direct differentiation gives

 g_0''(u)=3/16*(1+u/2)^(-5/2),
 g_1''(u)=-(5+u)/16*(1+u/2)^(-5/2).

Thus on u>=0, |g_0''|<=3/16 and |g_1''|<=5/16. Taylor's integral
remainder at0 proves, globally rather than asymptotically,

 |g_0(u)-1+u/4|<=3*u^2/32,
 |g_1(u)-1-3*u/4|<=5*u^2/32.

The complex Laplace gamma integral is valid for Re w>0 (first for w>0,
then by dominated holomorphic continuation). With principal square root,
define R_j(w)=K_j^B(w)/(sqrt(pi/(2*w))*exp(-w)). For w=r*exp(i*pi/6),
the preceding two Taylor estimates and Gamma(5/2)=3*sqrt(pi)/4 give

 R_0(w)=1-1/(8*w)+delta_0, |delta_0|<=9/(128*r^2*c^(5/2)),
 R_1(w)=1+3/(8*w)+delta_1, |delta_1|<=15/(128*r^2*c^(5/2)).

Since c>4/5 and (4/5)^5>1/4, c^(-5/2)<2. The actual polynomial identity is

 K_0(z)=w^2*((w^2+9)*K_0^B(w)-6*w*K_1^B(w)), w=2*pi*z.

Consequently its normalized bracket is

 Q(w)=(1+9/w^2)*R_0(w)-(6/w)*R_1(w)
     =1-49/(8*w)+epsilon(w),
 |epsilon(w)| <= r^-2*(27/4+9/(8*r)
                         +(9/64)*(1+9/r^2)+90/(64*r))
              <8/r^2, r>=12.                         (47.2)

For the last inequality, the three terms after27/4 are respectively
<=1/8, <1/4 and <=1/8; their sum is <8. For m>=2, r=2*pi*m>12.
Principal powers yield

 exp(i*theta/2)*K_0(m*exp(i*theta))
      =A_m*(-1)^m*exp(4*i*theta)*Q(r*exp(i*theta)).

The integer phase is exp(-i*pi*m)=(-1)^m. Exactly
cos(4*theta)=-1/2 and cos(3*theta)=0. Thus the entire first correction
-49/(8*w) has zero real contribution. The remaining real error has
absolute value <8/r^2<1/18. This proves (47.1), including strict signs
for every integer m>=2, with no finite exception list.

To pass to the energy gap, first justify its actual divisor identity:

 Delta(theta)=sum_(m>=2) d(m)*B_m(theta), |theta|<pi/2. (47.3)

For each derivative order G4 gives E_k=sum_m d(m)K_k(m). All the needed
double sums converge absolutely. One direct proof uses G12 inversion on
Re s=4 and the exact G5 multiplier: sum_k |theta|^(2k)/(2k)!*|K_k(m)|
is bounded by m^-4/(2*pi) times

 integral_R cosh(|theta|*sqrt(t^2+49/4))*|M_0(4+it)| dt.

This is finite: sqrt(t^2+49/4)<=|t|+7/2, and the explicit G14 vertical
tail has decay exp(-pi*|t|/2) times a polynomial; the bounded interval
is handled by G11 integrability. Also d(m)<=m, so the m^-4 divisor sum
converges. G13/G14 give the actual derivative sum, and the C25 paper
holomorphic continuation argument identifies it with B_m(theta).
Hence absolute Fubini proves (47.3), without a formal power-series
exchange or an assumed angular-kernel link.

For q=exp(-a), a>5: sqrt(3)>5/3 and pi>3. The exponential series gives
exp(1)>5/2, whence exp(5)>(5/2)^5>64 and q<1/64. For m>=3,

 d(m)*A_m/A_2 <= m*(m/2)^4*q^(m-2).

The ratio of successive m^5*q^(m-2) terms is at most
(4/3)^5*q<5/64. Geometric summation therefore gives

 sum_(m>=3)d(m)*A_m/A_2
       <(1/16)*243/(64-5)=243/944<1/3.

Since d(2)=2, (47.1)-(47.3) now prove the explicit strict gap

 Delta(pi/6)<-(8/9)*A_2+(5/27)*A_2=-(19/27)*A_2<0.   (47.4)

G8 already proves Delta(0)>0. The same absolutely locally uniform
bounds on any compact angular interval prove continuity. Thus there
exists theta_0 in (0,pi/6) with Delta(theta_0)=0. This is an exact
one-scalar cancellation in the positive angular carrier class. It is
not simultaneous cancellation of F_mu(n) for n>=2 and supplies no
upper spectral-deficit bound.

Novelty audit: the Laplace/Taylor remainder argument is classical;
Nemes2017 and DLMF10.40 are stronger parent remainder theories. The
actual integer parity law and its energy-gap consequence have not been
identified in the searched corpus or primary sources; scientific
novelty is not certified by this search. The pi/6 ray already appears
in C25d as a Carlson-type boundary; only its use as a sign counterexample
here is new to this working argument. C47a verdict FALSE; C47b and the
quantitative positive survivor are PAPER PROVED, not yet Lean proved.

Corpus C47-pi6: nonpartial/errors[],68907 files; all20 candidate and20
source-argument statements and the proposed remainder chain inspected.
Existing BesselK1SectorialRemainder and BesselK1C leading-term formulas
are relevant machinery. The proposed Barnes-kernel decomposition is a
different kernel and cannot replace this actual Bessel proof.
