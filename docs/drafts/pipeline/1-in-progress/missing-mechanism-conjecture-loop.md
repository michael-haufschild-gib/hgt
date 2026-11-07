# Missing mechanism: conjecture loop

- **ID:** missing-mechanism-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-0611 (obstacles-summary, walls-ledger, route-unification-ledger), rh-current-frontier-map, rh-killed-routes
- **Statement:** find an unconditional mechanism that moves a wall, not a reformulation.

## Results (Lean)

All in `PrimeTorusTheory/`. `L = log|t|`, `ℓ = log L`, `‖·‖` = distance to `ℤ`.

| Theorem | Module | Content |
|---|---|---|
| `logForm_nonpos`, `logForm_logConvex` | `TheLogarithmicHankelForm` | `Σ v_i v_j log(x+s_i+s_j) ≤ 0` for total mass zero; derivative is the Hilbert form `∫₀¹ z^{x-1}(Σ v_i z^{s_i})²`; log-convex in `x` |
| `exists_not_aligned_of_large_of_word` | `SquaredWordsForbidAlignment` | some `n ≤ 50L²ℓ` has `‖t log n/2π‖ > 1/(4096L⁴ℓ²)` |
| `exists_band`, `le_sum_phaseDist` | `TheMisalignmentBand` | crossing is an interval; mean of `‖t log n/2π‖` over `n<N` is `≥ 1/(768(M+1)²)` for all `N ≥ 6(M+1)`, `M≍L²ℓ` |
| `le_sum_primes_phaseDist` | `TheMassOfMisalignedPrimes` | `Σ_{p<N}‖t log p/2π‖/p ≥ 1/(10⁵L⁴ℓ²)` for all `N ≥ 48L²ℓ` |
| `le_sum_primes_critical`, `le_sum_primes_liouville` | `TheMassOfMisalignedPrimes` | `Σ_{p<N}(1∓cos(t log p))/√p ≥ c/(L⁸ℓ⁴)` at both corners |
| `exp_neg_le_sum_primes_critical`, `rpow_neg_le_sum_primes_critical` | `TheSavingAtEveryLength` | words of height `H`: for `1<A≤2`, `β>2−A`, `N≥7L^A`: `Σ_{p<N}(1−cos(t log p))/√p ≥ exp(−L^β)`; for all `A>1`, `δ>0`, `N≥L^A`: `≥|t|^{−δ}` |
| `norm_sum_le_of_large`, `norm_sum_ap_le_of_large`, `norm_sum_le_of_length` | `TheSupBoundOfIntegerPowers` | `‖Σ_{1≤n<N} n^{it}‖ ≤ N(1−1/(10⁹L⁸ℓ⁴))` for `N≥48L²ℓ`; same on every progression `r+qm`, `1≤r≤q`, of length `≥48L²ℓ`, uniformly in `q`; `N(1−exp(−L^β))` for `N≥7L^A`, `1<A≤2`, `β>2−A` |
| `totient_div_le_sum_primes_coprime_of_large`, `le_sum_primes_critical_coprime_of_large` | `TheSavingAwayFromSmallPrimes` | `Σ_{p∤q,p<qK}‖t log p/2π‖/p ≥ (φ(q)/q)/(10⁵L⁴ℓ²)` for `K≥48L²ℓ`; if `q` contains all primes `≤P`, the critical sum on `p∤q` is `≥4√P((φ(q)/q)/(10⁵L⁴ℓ²))²` |
| `norm_zeta_le_of_large` | `ZetaStaysBelowItsSupremum` | `σ>1`, large `|t|`: `|ζ(σ+it)| ≤ ζ(σ) exp(−(log|t|)^{−(3σ+13)})` |
| `exists_lowEnergy_word`, `energy_eq`, `sum_powerset_four` | `TheEnergyOfASquaredWord` | word of order `k`, `c_0≠0`, with `Σ_n r(n)² ≤ 12(M+1)²` once `Π_{j≤k}(C(M+1,j+1)+1)<2^M`; `r=c∗c`. The energy is a fourth power mean of the transform, so the difference of two low energy sign patterns has low energy |
| `sq_le_energy_mul_sum`, `norm_sum_le_of_large_energy`, `norm_sum_ap_le_of_large_energy`, `le_sum_primes_sq_phaseDist`, `le_sum_primes_critical_energy` | `TheSavingOfALowEnergyWord` | precision is the energy, not the mass: `‖Σ_{n<N} n^{it}‖ ≤ N(1−1/(10⁷L⁶ℓ³))` for `N≥48L²ℓ`, uniformly on progressions; `Σ_{p<N}‖t log p/2π‖²/p ≥ 1/(10⁹L⁶ℓ⁴)`; `Σ_{p<N}(1−cos(t log p))/√p ≥ 8/(10⁹L⁶ℓ⁴)` |
| `card_letters_ge`, `mem_range_of_consecutive`, `card_nonintegers_ge`, `card_filter_halfChoose`, `sum_exp_halfChoose` | `TheFloorOfAPolynomialPhase` | a word of order `k` has `≥k+2` letters. A degree `k` phase integer at `k+1` consecutive points is integer valued, otherwise it misses the integers once per window of `k+1`. Sharp: `C(a,2^m−1)/2` misses exactly on `a≡−1 mod 2^m`, sum `N−2⌊N/2^m⌋`, so one block saves at most `2/(k+1)` without excluding binomial denominators |
| `exists_not_aligned_of_large`, `exists_prime_not_near_torsion` | `NonAlignmentAtEveryLargeHeight`, `TheOrbitAvoidsTorsionPoints` | earlier route without squares: length `exp(√L ℓ^{3/2})`, precision `ℓ²/L`; torsion points by height dilation |

**Mechanism.** Square an integer word `W` of small `ℓ¹` mass with a high zero at `z=1`. The phase `F(x)=(|t|/2π)Σ(−c_ac_b)log(x+a+b)` is positive, decreasing and log-convex, so there is no cancellation between Taylor terms. `|c_0|=1` keeps `F≥½` up to `x≍L`, the zero at `1` makes `F` small from `x≍M`, and log-convexity bounds the crossing step by a factor `16`. Mass-zero makes this dilation invariant: every progression `x+h(a+b)` with `x/h` in the band carries misalignment.

**Identification.** The word is an auxiliary polynomial from Siegel's lemma; `G_W(x) = −Σc_ac_b log(x+a+b)` is a small linear form in logarithms. Positivity of the square replaces the zero estimate of transcendence proofs.

**Scope.** Uses every integer up to the length. Fails over `𝔽_q[T]` at the periodic heights. Saving is absolute, not proportional to the column size, so no half-space is excluded and Π80 is not resolved.

**Paper remarks, not formalized.**
- Precision by words cannot be constant below `Y ≍ L` (`N = exp Y`): a word of order `J` has `ℓ¹` mass at least `2J` (Prouhet–Tarry–Escott size bound).
- VK exponent: a word of order `k = L/Y` has about `k²` letters. Roughness of all letters costs a sieve of dimension `k²`, giving `N^{1/k²}`. A dense aligned set contains `x+S+S` with `|S| ≈ k²` only when `log N ≳ k²`. Both thresholds are `Y ≈ L^{2/3}`.

- Limits of the energy: `E≥(Σc_a²)²≥(k+2)²`, so one squared word gives mean square at most `≈1/k⁴` at length `M≈k²`. Placements with `W` consecutive shifts in the band would gain a factor `W` (operator norm `sup|Ŵ|⁴` replaces `E·M`), up to `1/M²` at `W≈M`. That needs the crossing `u₁` of the band to be `≳LW`; only `u₁≳L` is proved, because a pigeonhole word may be exponentially small on `e^{−z}`, `1/M≪z≪1/L`.
- Duality for exotic returns: with `V` the polynomials of degree `≤k` on `[0,M]` and `Λ=ℤ^{M+1}∩V^⊥` the words, Poisson summation gives `Σ_{a∈ℤ^{M+1}/(V∩ℤ^{M+1})} exp(−π dist(a,V)²/s²) = covol(V∩ℤ^{M+1})·s^{M−k}·Σ_{w∈Λ} exp(−πs²‖w‖²)`. No exotic return below `s` is the same as the Gaussian word count being its volume prediction to relative precision about `exp(−ck²)`.
- Where VK comes from: Markov at the critical moment `s≈k²/2` saves `exp(−Y/k²)`, which is macroscopic only at `Y≈k²`. A better constant in the mean value theorem does not change this exponent. Going below needs the exceptional set itself, not its measure.
- Words and depth: a zero of depth `d` needs amplitude `≲1/L` at length `L^{1/d}`, not `1−o(1)`. Word savings feed only the sign plane, and even there stop at `≈1/k²`, against the constant required at `y≈L²`.

## Tested and rejected

| Conjecture | Outcome |
|---|---|
| Positive-coefficient series removes the pole at `s=1` | No: positivity at primes forces abscissa 1. `ζ(s)^a/ζ(2s)^b`, sparse prime sets, sieve majorants and rational twists all keep a dominant real singularity |
| Sawtooth positivity: `−ζ(σ+it)/(σ+it)` is positive definite on `0<σ<1`, carry measure `{x}+{y}−{x+y}` | True and elementary; its mean is the pole at `0`, so it gives only `|ζ(σ+it)|≪|t|`. Blind |
| Bernoulli closure `(ζ/s)⋆(ζ/s)` is linear in shifted `ζ` | True; it is Ramaswami's recursion, no constraint |
| Redheffer spectrum: `det(λ−R_N)` is a truncated `1/(λ−ζ)`, eigenvalues are a-values, abscissa explicit by Bohr for `a≠0` | Dictionary only. `a=0` is an exceptional polar point of a subharmonic limit; not selective, holds for every Beurling system |
| Real-rootedness of `Σ_{n≤x}μ²(n)z^{ω(n)}` or `Σ_{n≤x}d_z(n)` | The second fails at `x=16` by hand. No interlacing mechanism for the first: `P={2,3,5}` at `x=15` already has complex roots |
| `ξ(½)/ξ(½+x)` infinitely divisible, Thorin measure on zeros | Lévy density `2G(u)/u`, `G(u)=Σ_{γ>0}e^{−γu}cos((β−½)u)`, positive on `(0,π]` from the strip alone; beyond `π` it needs a located low zero. RH ⇔ `G` completely monotone. Edge level |
| Hecke self-adjointness gives a dispersion lower bound `(Im λ)²` | No: the truncated state has real first moment `p^u+p^{ū}`; Poisson model, blind |
| Pair correlation with `K̂≥0` bounds off-line mass at rate `e^{−2a}` | Off-diagonal sign fails: `Re C≥0` on all of `ℂ` forces `C` constant by Liouville. This is the cluster wall |
| Moment at `s=2k` beats alignment | Needs smooth numbers in short intervals at scale `1/t`, equivalent to non-alignment |
| Prime words (products of primes only) for weight `p^{−½}` | Needs prime tuples or parity; integer words have small unaligned cofactors |
| Word positivity in `s`: `Σc_ac_b(−ζ′/ζ)(s+a+b)=ΣΛ(n)n^{−s}W(1/n)²` | Positive series; `W(1/n)→c_0` keeps the pole at `s=1`. Blind |
| Følner sets for the window rational `R=A/B` give proportional cancellation | Word rationals have `log A≈L⁴ℓ³`, so Følner sets live above `t`; on prime boxes the bound is the same `ℓ¹` inequality |
| Non-squared words supported inside any dense aligned set, chosen by lattice duality | Sign control lost: duality costs `4^{−k}`, so precision is exponential in the order |
| Least character value in depth aspect (`χ mod p^k`) by `p`-adic words | True and easy: ultrametric gives the zero estimate and the group is discrete, `(1−z)^J` suffices. No amplitude problem, so no analogue of the `t`-aspect content |
| The phase `F` is carried by primes near the letters (top-scale localization) | Small primes have mean zero, which gives only a dichotomy. Their independence needs a sieve of dimension `|supp P|` unless their mass is `≲u/M²`; the net gain is a factor `log Y/log log Y` in mass |
| Many words at once beat one word | Bessel: amplitude `1/M` is consistent with every second-moment word test, so words stop at `V≈1/M²` |
| Unsquared words on arbitrary letters (primes, rough numbers) with Chebyshev duality in place of positivity | Needs a word with leading moment near its Chebyshev maximum. That is solvability of a moment system on the letter set, not given by pigeonhole |
| Cyclotomic factors `Φ_q`, `q≤√M`, delete small primes from squared words | First-level valuations cancel exactly. Letters divisible by `p^k>√M` remain with density about `M^{−1/3}`, and no block avoids them |
| Weil form on integer combs: Schur test with `m^{−1/2}` gives norm `≤log X+C` | Already proved (`abs_sum_vonMangoldt_mul_le_half_log`). Integer combs spread over heights, so it is a mean value statement and sees no single height |
| Log-energy expansion `−log|m−n|=−Σ_{d|m−n}Λ(d)` as a prime-weighted Farey comb | Exact identity from `log=Λ∗1`. Linear in `Λ`, blind to zeros |
| Top primes via Heath-Brown factorization of `Λ` into integer sums | Pieces lose powers of `log N`; a saving `L^{−8}` cannot pay that. Would need `|Σ n^{it}|≲X/(log X)^A` at the same length |
| Prime-free tests `A(log n)=0` built as `sin(2πqe^{|u|})`: `Φ≈√(2π/t) Im[e^{2iϑ(t)}B(t)]`, off-line zeros amplified by `(T/2πq)^δ` | Exact and prime-free because `e(nq)=1`, and it is the functional equation restated. With `B=DG`, approximate FE at zeros removes `χ` and returns Landau–Gonek. Against the Cauchy bound on on-line zeros the amplification `T^{¼+δ/2}` only reaches `T^{½}log T` at `δ=½`: no zero-free range |
| Prime-free tests as Bernoulli products `Π cos²(πu/2log n)` | Positive definite and vanish on `log ℕ`, but `A` has width `≈log N/√N`, so `Φ` only counts zeros in windows `√N/log N` |
| Log-energy product formula `Σ_v log|m−n|_v=0` with each local form positive definite (Arakelov energy) on integers | The identity is the large sieve at logarithmic scale; on `n^{it}` points the energy needs a lower bound for `|1−(m/n)^{it}|` at one `t`, which is the problem itself |
| Mahler measure: `∫log|P(p^{it})|≥0` for integer polynomials in prime variables | True by Kronecker–Weyl, and a mean over `t`. It does not see one height |
| Hilbert–Carleman: `−Σv_mv_n log(m+n)=½∫|Σv_n n^{it}|²/(t sinh πt)dt` for mass zero, and `η(ρ)=0` makes `(−1)^n n^{−ρ}` an infinite mass-zero word | Exact, and it explains why words have no reach in `t` by positivity alone. Rotating the ray cancels the `Γ` factor but gives only a local mean square of `ζ`. Parseval, blind |
| Top primes by first level balancing mod all `p≤L` (`Σp≈L²/2ℓ` constraints fit in the budget) | Second moment drops the weight of small primes to `1/max(L,p²)`, but they still supply the deficit with amplitude `≈1/√L`. Prime powers need `(1−z^Q)` factors, cost `4^{π(P)}` |
| Height descent by Dirichlet returns on primes `≤y` | Reduces height only to `exp(π(y)log(1/ε))`, above the reach `exp(√y)` of words at that length |
| Determinant method (Bombieri–Pila) as a nonlinear test | Needs precision below the size of the rounded phases, about `1/t` |
| Pure products of `k` primes near `y`, window `log(A/B)≈1/t` by pigeonhole | Clusters at `(2π/t)ℤ` are exactly the aligned scenario; cluster width needs primes in short intervals of length `X^{1/A}`. Equivalent to near-diagonal energy |

## Open

- **Smooth triples at a prescribed ratio.** If `A=B+C` with all three `y`-smooth, `y=(log t)^κ`, and `B/C≈t`, then `R=A/B` has about `L/log y` letters, so the precision improves from `L⁻⁴` to `(log y)/L`. If such triples equidistribute over primes, the mean of `‖t log p/2π‖` over `p≤y` is `≳(log y)/L`, a saving proportional to the column size up to `(log y/L)²`. Not proved; no route in the corpus.
- **Sparser positive words.** `ℓ¹` mass between `2J` and `J⁴` at order `J`. Any integer `P≥0` on `[0,1]` with mass `≪J⁴` improves every precision above.
- **Exotic returns (paper analysis, not formalized).** A return at amplitude `η` makes the rounded phases an integer vector near the polynomials of degree `<k`, or near a slightly larger space. By lattice duality, the absence of such returns is the same as short words spanning `Λ_k`. Precision `1/mass` is the limit of any single word: a word of order `e` has at least `e+1` letters. Going further needs:
  - **Inverse Weyl at polynomial length.** For `M≥Ck²log k`, a degree-`k` Weyl sum of size `≥δM` forces a major arc. Counting cells supports it: `M^{k²/2}` cells against probability `exp(−cM)`. Taylor-expanding `n^{it}` on blocks then gives a macroscopic bound, so this is at least quasi-RH strength and is a statement about polynomials only.
  - **Collision count with a uniform constant.** If pair counts on `r≈k²` letters exceed the Gaussian prediction by a factor `K`, balanced words exist at length `≈√K·k²`. `K=exp(k^γ)` gives lengths `exp(L^{γ/(1+γ)})`; `γ=2` is the Vinogradov–Korobov exponent `2/3`.
  - **Scale coincidence.** The word threshold `M≈k²log k` with `k≍L` is the size horizon `y≈L²` up to logarithms. No explanation is known.

## Log
- 2026-11-07 — created; squared words, band, prime mass, every-length saving, sup bound, deletion of small primes, floor of a word, energy of a word formalized
