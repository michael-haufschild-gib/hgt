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

### C3t+ — stronger corpus envelope and complete weighted convergence (paper proof)

The previous π/2 threshold is unnecessarily restrictive. Existing `ExposingRayTail.autocorr_upper` proves: for every 0<c<π there is C_c>0 with κ(y)≤C_c exp(−2c exp|y|), for every real y. This is prior corpus knowledge, not a new asymptotic theorem. For x_i,x_j∈[−log2,0] and n≥2, the triangle inequality gives exp|±log n+x_j−x_i|≥n/2. Hence each shifted correlation is at most C_c exp(−cn). The same bound holds for every truncated correlation because 0≤κ_L≤κ.

For a finite real packet P=Σ_i a_i Φ(·−x_i), set q(P)=(Σ_i|a_i|)². Expanding both signs of the actual logarithmic defect gives, uniformly in L,

`|b_P(n)|, |b_(P,L)(n)| ≤ 2 C_c q(P) exp(−cn)/√n`.

Here the truncated defect is exactly the existing logValue of shiftComb; the limit uses the same finite quadratic sum with κ. By C3r, atomCost(n)≤D(n+1)√n. Also Λ(n)≤log n≤n≤(n+1)√n for n≥2. Thus the FULL weighted terms satisfy

`(Λ(n)+atomCost(n)) |b_(P,L)(n)| ≤ 2 C_c(D+1) q(P)(n+1)exp(−cn)`,

and the same holds for b_P. The majorant is summable. Pointwise κ_L→κ and finite sums give b_(P,L)(n)→b_P(n). Dominated convergence on all integers n≥2 now proves convergence of the entire weighted absolute-defect sum, including every newly activated coordinate. It also proves the stronger weighted ℓ¹ difference tends to zero, by the twice-majorant inequality |b_(P,L)−b_P|≤|b_(P,L)|+|b_P|. Every statement is for the actual PBAP weight and existing compact shiftComb tests.

For any 0<r<c<π, `(n+1)exp(−(c−r)n)` has a finite uniform bound (one degree-one exponential estimate). Therefore the weighted terms are ≤K_r q(P)exp(−rn), uniformly in P,L. Summing n>M gives at most K'_r q(P)exp(−rM). Positive finite mixtures obey the same bound with total packet cost A. Consequently the original C3→C paper reduction works with **θ<π**, choosing θ<r<c<π, instead of θ<π/2. C3+ denotes this weaker sufficient construction problem. No affordable cancellation construction has been proved.

Formalization target: actual packet definitions and exact logValue bridge; uniform exponential bound for full weighted terms; summability; full weighted ℓ¹ convergence under physical truncation. These are unconditional analytic bridge results. C3+, C5p and the assigned spectral-deficit target remain OPEN. C4b's lower-cost boundary is unaffected.

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
