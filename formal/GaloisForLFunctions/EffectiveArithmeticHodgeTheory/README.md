# Effective Arithmetic Hodge Theory

Namespace `GaloisForLFunctions.EffectiveArithmeticHodgeTheory`; umbrella `EffectiveArithmeticHodgeTheory.lean`; 13 modules. Every theorem is unconditional; RH appears only inside equivalences or as the hypothesis of one stated implication (`riemannHypothesis_imp_liouville_separation_of_gevrey`). Several modules end with `#print axioms`.

## 1. Motivation

The corpus reads RH as a Hodge index statement on `Γ = ℚ_{>0}`: the Weil kernel `K_ζ` has negative index `κ(K_ζ)` equal to the number of zeros right of the critical line, and RH is `κ = 0`. Over `𝔽_q` the index is controlled by finite objects (a surface, Riemann–Roch, Stepanov auxiliaries). Over `ℤ` every object is infinite. This programme replaces them by finite sections with explicit scale: the height-`T` part of the spectrum, the length-`N` atomic families, two-prime boxes, Dirichlet polynomials of length `N`. Each theorem says what a section carries, at what size, and in which topology the sections converge to the whole. The programme has two halves. The index half shows that explicit sections carry and reach the full index. The auxiliary half builds the zero estimate (Bézout, Riemann–Roch, rigidity of integer auxiliaries) that a Stepanov-type producer over `ℤ` would need, and finds it exact but cost-free of any prime identity.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Height filtration | `rightZerosBelow T`, `heightIndex T` | right zeros with `|Im ρ| ≤ T`; their number `κ_T` |
| Frobenius value | `frobEig ℓ` (ACS) | `e^{ℓ(τ − ½)}`: a zero seen on the tower of scale `ℓ` |
| Blind primes | `heightBlindPrimes T` | primes whose tower aliases two right zeros of height `≤ T` |
| Atomic Gram | `atomicGram ψ N` | Weil Gram of `ψ(· − log n)`, `n ≤ N` |
| Perturbation budget | `weilErrBound`, `weilPerturbationBudget F R e V` | explicit two-sided bound on `|Q(F+D) − Q(F)|` |
| Compressed budget | `compressedEntryBudget S B` | `Σ_ab |S_ai| B_ab |S_bj|` |
| EM / Steklov entry budgets | `emWeilEntryBudget`, `steklovWeilEntryBudget` | Gram-entry errors of the actual synthesis |
| Carrying family | `Carries S x` | evaluation matrix `(χ(x_b))` has full row rank |
| Frobenius progression | `frobPoint p j`, `frobRoot p n` | `s_j = 2πij/log p`; `ω_p(n) = e^{−2πi log n/log p}` |
| Dirichlet derivative | `dirDeriv a N i s` | `Σ_{n≤N} a_n(−log n)^i n^{−s}` |
| Tower quotient / Euler product | `towerQuot a p`, `eulerMul p F` | division / multiplication by `1 − p^{−s}` |
| Vanishing order | `VanishesAlong a N p m` | first `m` derivatives vanish on cofinitely many points of `p`'s progression |
| Sections | `sections N S m`, `dirPolys N` | Dirichlet polynomials of length `N` with divisor `m` on primes `S` |
| Integer auxiliary | `IntegerCoeffs a` | coefficients in `ℤ` (group ring `ℤ[Γ]`) |
| Twist level | `twistLevel j` | `(−1)^{Ω/2^j}Λ` on `2^j | Ω`; level 0 = Liouville twin |

External: `negIndex`, `zetaKernel`, `hermNegIndex` (HKT/HTGeometry); `weilGram`, `cx`, `rightZeros` (ArithmeticCastelnuovoSeveri); `weilQuad`, `weilQuadTw`, `dilate`, `synthLevy`, `OverlapGrowthGevrey`, `StableForm` (SSHA); `steklovDCProfile`, `superGevreyRatio`, `OverlapGrowthSuperGevrey` (TMWP); `sqrtClass` (ArithmeticOfSquareRootPrecision); `atomicTest` (ArithmeticElectrostatics).

## 3. Language

- Section: a finite family (tower window, two-prime box, atomic family) and the Gram matrix the kernel induces on it. Carries `m`: at least `m` negative squares. Certifies height `T`: carries `κ_T`.
- Decides RH: eventual positivity of the sections is RH. Reaches the index: section indices converge to `κ(K_ζ)` in `ℕ∞`. Reaching is stronger.
- Point side vs zero side: auxiliaries vanish at primes (Frobenius progressions); zero-side objects vanish at zeros.
- Degree of a Dirichlet polynomial of length `N` is `log N`; a prime `p` contributes `log p` per order of vanishing along its progression.
- Over `𝔽_q[T]` all places of one degree share a progression; over `ℤ` every prime has its own.

## 4. Mechanisms

**A. Heights and aliasing**
1. `κ_T` is finite, monotone, `≤ 2N(0,T) + c₀ = O(T log T)`; `κ(K_ζ) = sup_T κ_T`.
2. Nyquist: on a tower of scale `ℓ` with `ℓT < π`, points of height `≤ T` never alias; `π` is sharp. The deep-sparse tower law then gives a window carrying `κ_T`.
3. Dirichlet approximation of `log 3/log 2` gives `3^k/2^j` with `k = O(T)` and scale `< π/T`. A distinct pair of zeros aliases at most at one prime, so at most `C(κ_T, 2)` primes are blind.

**B. Transfer of the index along schedules**
1. Real tests: `W(f,g) = (Q(f+g) − Q(f−g))/4` (functional equation makes `W` real symmetric).
2. Two-sided continuity: the upper perturbation bound applied from `F` and from `F + D` (whose norms stay bounded) gives `Q(F + D_n) → Q(F)`; polarization gives entrywise Gram convergence.
3. Upper half: every atomic Gram has `≤ κ(K_ζ)` negative squares (compression + HKT receiver bound). Lower half: cubic-spline translates carry every `m ≤ κ`; mollifying by the profile keeps `m` (lower semicontinuity) and puts the family in the profile's class; synthesis carries it to the atomic Gram.
4. Residue classes: synthesis lives on horizons `nB`; shifts `N ↦ N + ρ` keep the growth law, finitely many classes cover all large `N`, zero padding embeds the family.

**C. Explicit finite tests**
1. Every Hermitian `A` has a complete negative compression `SᴴAS = diag(c)`, `c ≤ −δ`.
2. If `|G − A| ≤ B` entrywise and every compressed budget is `≤ δ/(2(r²+1))`, then `r ≤ hermNegIndex G`.
3. With the actual EM (or Steklov) synthesis errors this is a finite inequality at a given horizon `N` and width `k`.

**D. Carriers of finite spectra**
1. Full row rank evaluation ⇒ the Gram matrix of a Hermitian exponential sum reads its exact index.
2. Lagrange: a window of `|S|` powers of a separating element carries `S`; a box of side `|S|` in two jointly separating commuting elements carries it (generic linear form, binomial expansion). Two distinct primes separate all zero characters.

**E. Zero estimate in the group ring**
1. On `p`'s progression `D(s_j) = Σ_w C_w w^j` with `C_w` the `p`-tower sums; vanishing on cofinitely many `j` kills every `C_w` (Lagrange on ℤ-exponential sums), so `D = (1 − p^{−s})F` with `F` of length `N/p`.
2. The derivative identity lowers the order by one on `p`'s progression and keeps it on every other prime's (progressions meet only at `s = 0`, since `log q/log p` is irrational). Induction gives Bézout `Π p^{m_p} ≤ N`.
3. `eulerMul` and `towerQuot` are inverse isomorphisms between section spaces ⇒ `h⁰(N, m) = ⌊N/Π p^{m_p}⌋`.
4. Approximate: distinct roots `ω_p(n)` are `≥ 4/(Np log p)` apart by integrality alone (`|log A − log B| ≥ 1/max`); mean values on a stretch of `J ≥ N²p log p` points give `Σ|C_w|² ≤ 2ε²`. For integer coefficients `ε < 1/√2` forces `C_w = 0`; peeling Euler factors with Taylor coefficients `k!(log p)^k` gives rigidity to any order.

**F. Selectivity and twists**
1. Residue-class upgrade turns SSHA's "infinitely many horizons" into "every large horizon" for stable forms.
2. Twist tower over `ℤ`: levels `j ≥ 1` live on proper prime powers; partial sums `≤ ψ − θ ≤ 2√x log x`.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| `κ(K_ζ) = sup_T κ_T`; `κ_T ≤ 2F(T) + C log²T + c₀` | `negIndex_zetaKernel_eq_iSup_heightIndex`, `heightIndex_le_rvm` | proved |
| Nyquist separation for `ℓT < π`, sharp at `π` | `injOn_frobEig_of_mul_lt_pi`, `exists_alias_of_pi_le` | proved |
| A tower of scale `< π/T` certifies height `T`; explicit tower `3^k/2^j`, `k ≤ ⌊T log 2/π⌋ + 1` | `exists_window_certifies_height`, `twoPrime_tower_certifies_height` | proved |
| At most `C(κ_T, 2)` blind primes; one of any `C(κ_T,2)+1` primes certifies height `T` | `ncard_heightBlindPrimes_le`, `exists_prime_certifies_height` | proved |
| Two-sided continuity of `Q`; Gram convergence | `tendsto_weilQuad_add`, `tendsto_weilGram_of_perturbation` | proved |
| Atomic Gram index `≤ κ(K_ζ)` at every width | `hermNegIndex_atomicGram_le` | proved |
| Gevrey schedules reach the index; DC profile at `(log log N)^α/N`, `α > 1` | `tendsto_hermNegIndex_atomicGram`, `dcProfile_atomicGram_reaches_index` | proved |
| Log-DC profiles at super-Gevrey overlap reach the index; Steklov at `L(log L)^β/N`, `β > 2` | `tendsto_hermNegIndex_atomicGram_dcLog`, `steklovDCProfile_atomicGram_reaches_index` | proved |
| Explicit two-sided Weil perturbation and Gram-entry bounds | `abs_weilQuad_add_sub_le_explicit`, `norm_weilGram_add_sub_le_explicit` | proved |
| Compressed entry test ⇒ index lower bound; EM and Steklov finite-horizon certificates for every finite part of the index | `le_index_of_compressed_entry_test`, `exists_emWeil_index_horizon_certificate`, `exists_steklov_index_horizon_test` | proved |
| Carrying families read the exact index; two-prime box of side `|S|` | `hermNegIndex_gram_expSum_eq_of_carries`, `hermNegIndex_twoPrime_box_eq` | proved |
| Bézout of `𝔾_m(ℚ)`: `Π p^{m_p} ≤ N`, sharp at `1 − p^{−s}` | `prod_pow_le_of_vanishesAlong`, `eulerFactor_vanishesAlong` | proved |
| Riemann–Roch of the base: `h⁰(N, m) = ⌊N/Π p^{m_p}⌋`; nonzero iff `Π p^{m_p} ≤ N`; `𝔽_q[T]` count `d + 1 − em` | `finrank_sections_eq`, `sections_ne_bot_iff`, `finrank_divisibleLT_eulerFactor` | proved |
| Approximate Bézout: `Σ|C_w|² ≤ 2ε²` | `sum_normSq_towerSums_le` | proved |
| Integer auxiliaries: small ⇒ divisible, to every order; zero estimate; threshold sharp | `vanishesAlong_of_small`, `prod_pow_le_of_small`, `dirDeriv_single_one` | proved |
| Twist levels `j ≥ 1` lie in the square-root class | `twistLevel_mem_sqrtClass` | proved |
| Bounded twin negative at every large section iff not Weil positive; Liouville always | `eventually_negative_iff_of_gevrey`, `liouville_eventually_negative_of_gevrey` | proved |
| A prime identity making vanishing along progressions cheap (arithmetic Stepanov) | — | open |

## 6. Tools

**Developed**
- Height filtration with Riemann–von Mangoldt bound; Nyquist/aliasing calculus on towers.
- Polarization and two-sided continuity of the real Weil form; Gram convergence under perturbation (`weilPair_real_eq`).
- Index transfer from synthesis (`eventually_le_hermNegIndex_of_synthesis`), residue-class upgrade (`eventually_of_residues`), zero padding (`atomicTest_extend`).
- Complete negative compression and compressed entry tests (`exists_complete_negative_compression`).
- Carrier theory: Lagrange span, windows, boxes (`window_carries`, `box_carries`).
- Group-ring division: tower quotient, Euler multiplication, derivative identity (`dirDeriv_quot`), section spaces with exact dimension.
- Root separation by integrality (`norm_frobRoot_sub_ge`) and stretch mean values (`sum_normSq_expSum_ge`); Euler-factor Taylor chain (`dirDeriv_frobPoint_chain`).

**To build**
- An identity on the primes that makes vanishing along their progressions cheap (role of `x^q = x`).
- A section count on a surface over the base whose Euler characteristic is quadratic.
- Arithmetic synthesis (Möbius or Ramanujan cell weights) below the quasi-analytic rate; a signed transfer between the positive plateau profile and the receiver profile.
- A specific certifying prime at height `T`.

## 7. Open questions

1. Arithmetic Stepanov: which identity on `ℤ[Γ]` lets an auxiliary vanish along many prime progressions at length far below `Π p^{m_p}`? By Riemann–Roch, linear algebra alone gives exactly Chebyshev's count.
2. Is there an arithmetic surface over the base with quadratic `χ` (Riemann inequality, subquadratic degree-zero growth)?
3. What is the slowest schedule that reaches the index? Is `L(log L)²` (TMWP's critical overlap) the floor for profile-based synthesis?
4. Which explicit prime certifies height `T`? This is a Diophantine question about `log p` and the zero ordinates.
5. A converse Krein–Langer step on `Γ`: a common invariant negative subspace for all prime translations of a finite-index kernel.
6. What is the flip threshold `c*(p)` at which the complete atomic form first separates a single prime flip from `Λ`? TMWP shows `c*(11) ≤ 99/100`.
7. Can the explicit finite-horizon index tests be evaluated numerically at moderate `N` (they are finite inequalities)?

## 8. Traps

| Trap | Fact |
|---|---|
| "Deciding RH = reaching the index" | Reaching is stronger; for synthesis receivers they coincide because whole negative families are synthesized in Gram norm. |
| "One prime certifies every height" | A prime tower can alias; at most `C(κ_T, 2)` primes are blind, but which prime is unknown. Prime towers never satisfy `log p < π/T` for `T > π/log 2`; the explicit certificate uses `3^k/2^j`. |
| "Small values are cheaper than zeros" | Along a progression, `ε`-small values force `ε`-small tower sums; for integer auxiliaries `ε < 1/√2` forces exact divisibility. |
| "Bézout is lossy" | It is exact: `h⁰ = ⌊N/Π p^{m_p}⌋`. The count it yields is Chebyshev's because nothing makes vanishing cheap. |
| "Over `ℤ` vanishing at a place costs a bounded number of conditions" | Each prime has its own progression; order `m` costs `N − ⌊N/p^m⌋` conditions. Over `𝔽_q[T]` places of one degree share. |
| "The twist tower adds information over `ℤ`" | Every level above the first is in the square-root class; only the Liouville level is visible. |
| "Twin negativity is intermittent" | For Gevrey schedules it holds at every large horizon. |
| "Finite tests are proofs of positivity" | They certify negative squares (lower bounds on the index); they never certify `κ = 0`. |
| "The baseline `ε < 1` threshold can be relaxed" | The auxiliary `1` has `|D| = 1` everywhere and is not divisible. |
| "Height-`T` sections see the whole index" | Only `κ_T`; the full index is the supremum over `T`. |

## 9. Context

**Uses**

| Programme | Imports | Role |
|---|---|---|
| HeckeKreinToeplitz | 5 | negative index, `zetaKernel`, receiver bound, finite exponential sums, prime-tower index |
| RHTower | 4 | zero counts, Riemann–von Mangoldt, Gelfond–Schneider irrationality, Weil–Bochner cone |
| ArithmeticCastelnuovoSeveri | 3 | `weilGram`, `frobEig`, deep-sparse tower law, Hodge defect sectors |
| SpacingScaleHarmonicAnalysis | 1 | Gevrey/DC profiles, EM synthesis, stable forms |
| TransMetzlerWeilPositivity | 1 | Steklov profile and super-Gevrey synthesis |
| ArithmeticOrientationGeometry | 1 | reality of `W` from the functional equation |
| ArithmeticOfSquareRootPrecision | 1 | square-root class `sqrtClass`, Liouville weight |

**Used by**: none (umbrella only).

| Neighbour | Relation |
|---|---|
| HeckeKreinToeplitz | owns the index; this programme makes it effective in height and length |
| ArithmeticKreinLangerTheory | tower Hasse principle, Bézout ledger in `ℤ`, twist tower over `𝔽_q`; here the group-ring Bézout and the collapse over `ℤ` |
| ArithmeticOfSquareRootPrecision | precision classes; the twist levels land in its square-root class |
| SpacingScaleHarmonicAnalysis, TransMetzlerWeilPositivity | atomic families and synthesis; here upgraded from deciding RH to reaching the index |
| ArithmeticCastelnuovoSeveri | scaling surface and tower laws used for certifying windows |

## 10. Big picture

The programme shows that the index of the Weil kernel is a finite, effective object: every zero off the line below height `T` is caught by an explicit tower window, by a two-prime box of size equal to the spectrum, and by atomic Gram matrices along explicit overlap schedules, with explicit finite inequalities certifying each negative square. Nothing in the transfer is lossy; the sections reach the index exactly. So the difficulty of RH is not in seeing zeros in finite sections. Any off-line zero would be visible in a finite computation.

The auxiliary half delivers the opposite message. The zero estimate over `ℤ[Γ]` is exact and sharp, and integrality turns approximate vanishing into exact divisibility, but a dimension count then gives exactly Chebyshev's bound and nothing better. Over `𝔽_q` Stepanov's method wins because `x^q = x` makes vanishing at all points of one degree cheap; over `ℤ` each prime has its own progression and no such identity is known. A producer route to RH therefore needs a genuinely new arithmetic identity on the primes; the geometry of sections around it is complete.
