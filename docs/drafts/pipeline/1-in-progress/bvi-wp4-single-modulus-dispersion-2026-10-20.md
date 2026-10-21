# WP4: single-modulus bilinear dispersion on the pronic Gram

- **ID:** bvi-wp4-single-modulus-dispersion-2026-10-20
- **Stage:** 1-in-progress
- **Type:** CANDIDATE (contribution loop, goal 100)
- **Source:** `docs/reports/work-packages.md` WP4; BVI README §5 research topic 1
- **Statement:** bound `Σ_{p∼P} Σ_{q∼Q} a_p b_q 𝒢^{ec}(p,q)` at one modulus with exponent `θ > 1`,
  or prove which input classes cannot, with the replacement hypothesis.

## Units used by this card

- Window `M ∼ X` of the pronic measure; moduli `∼ P`. Exponent `θ = 2 log P / log X`.
  Large sieve is diagonal-quality at `X ≥ P²` (θ ≤ 1); the pronic mass of the prime block
  sits at `X ∼ P` (θ = 2, the receiver).
- Diagonal scale of a prime packet: `D(a) = Σ_p p a_p²` (`𝒢^{ec}(p,p) ≍ p`).
- Trivial (Cauchy–Schwarz) loss: `|S|`, the number of moduli.

## Significance criteria (WP4)

1. θ > 1 for a stated coefficient class. 2. Interior rate > 7/24 with all terms.
3. Type-II input at one modulus with exact loss. 4. No-go for a named class + replacement.
Not significant: reciprocity error, window constants, horizons, large-sieve factor two, ε ≥ 1/2.

## Ledger of contributions

(count = number of entries marked DONE; Lean module named on each)

- **C1 DONE (criterion 4).** `BVI/BrownianBridgeLawOfThePrimeBlockAndCodimensionNoGo`.
  First-jump window: `V(n) = L − nA + C(n)`, `C(n)=Σ_{p≤n}a_p p`, for `n < 2 min S`; for `S⊆(P,2P]`,
  `A=L=0`: window energy `= Σ a_p a_q (min(p,q) − pq/(2P+2))` (Brownian bridge) `≤ 𝒢^{ec}`-form.
  No-go: any `J` linear side conditions admit `a≠0`, `A=L=0`, with
  `Q^{ec}(a) ≥ (k²−1)/(24(2P+1)) Σ p a_p²`, `(J+3)k ≤ |S|`. Named class: Type-II ℓ² inputs with
  `J` side conditions; loss `≳ |S|/((J+3)² log P)` vs trivial `≲ 3|S|`. Replacement: square-root
  size of the summatory jump function `C` on the block (θ = 2 window).
- **C2 DONE (criterion 4).** `BVI/CoherentPrimeBlocksAndTheTypeIIWindowNoGo`.
  `k` primes in `[p₀,p₀+ℓ]`, unit jumps: on clean regions `j(p₀+ℓ) ≤ n < (j+1)p₀` the packet is
  exactly affine `L + kj − ns`; on `[J₀p₀, 2J₀p₀)`, `4J₀ℓ ≤ p₀`: window energy `≥ (k/2304)·k Σ_W w`
  (window diagonal bound). Pigeonhole: every `S⊆(P,2P]` has such a block with
  `k ≥ |S|/((P−1)/(ℓ+1)+1)`. Large-sieve loss `P²/X` attained at every window below `P²`:
  no Type-II input reaches any θ > 1. Replacement: square-root cancellation of the jump measure
  `Σ_{p∈I} a_p p` on intervals of length `P²/X`.
- **C3 DONE (criterion 1; criterion 3).** `BVI/SummatoryFunctionBoundForTheDyadicPronicGram`.
  Row `c` on `(N₀,2N₀]`, `|Σ_{n≤m}c(n)| ≤ B`: hyperbola identity `Σ c(n)⌊M/n⌋ = Σ_j S(⌊M/j⌋)` +
  Abel ⇒ `|V(M)−R₀| ≤ 2BM/(N₀+1)`; `sieveEnergyCenteredPronicGramForm N c ≤ 11B² + 4Σc(n)²/n`
  (`|R₀| ≤ B` via Abel on `log n/n`). Receiver-quality (θ = 2) dispersion for every bounded-
  partial-sum class (alternating, fixed character, …); Cauchy–Schwarz loses `N₀`.
- **C4 DONE (criterion 3).** `BVI/CrossScaleFactorizationOfThePrimePronicGram`.
  `V_a = m(a) + Ṽ_a` (fast, interval sums ≤ `K_a = Σ|a_p|p²/2`), `V_b = L_b − nA_b + Σ_q b_q q⌊n/q⌋`
  (slow steps). `|Σ a_p b_q 𝒢^{ec}(p,q) + m(a)L_b| ≤ K_a(|A_b|/2 + 2Σ_q|b_q|/q)`; on `A_b=L_b=0`:
  `|·| ≤ Σ|a_p|p² · Σ|b_q|/q`, arbitrary coefficients, one modulus: power saving `(P/Q)^{3/2}`
  over Cauchy–Schwarz for `a∼P`, `b∼Q`. Cross-scale Gram = rank-one coupling `−m(a)L_b` + mass term.
- **C5 DONE (criteria 3+4).** `BVI/ExactTypeIILossOfTheReceiverGram`. Receiver form
  `sieveEnergyCenteredPronicGramForm` (all moduli), log-free: (i) first window `V = R − MH + S(M)`;
  codim-J no-go `Q ≥ (k²−1)/(24(2N₀+1)) Σc²/n`, `(J+3)k ≤ N₀` ⇒ Cauchy–Schwarz sharp up to
  `48(J+3)²`; (ii) unit integer block, every window `[J₀n₀,2J₀n₀)`: energy `≥ (k/2304)·kΣ_W w`,
  `k=ℓ+1≈n₀²/(4X)` — exact Type-II loss `Θ(N²/X)` (large sieve matches). Abstract lemma
  `window_energy_ge_of_clean_affine` reusable.
- **C6 DONE (criterion 3; README open boundary "sign of signed prime packets").**
  `BVI/ExactRankTwoCrossScaleLawOfTheReceiverGram`. Rows `c,c'` (all moduli):
  `|B(c,c') + m(c)R(c') + β(c)H(c')| ≤ 2K_c Σ|c'(n)|/n²`, `β(c) = Σ_{M≥1}F_c(M)/(M+1)` (Dirichlet).
  Unit rows: `|eqB(δ_e,δ_q) − (D_e log q − (e+1)/2(H_e−1) + (e−1))| ≤ e/2 + e²/q`, `D_e=(e−1)/2−log e`;
  `D_e<0 ⟺ e∈{2,3}`; eventual sign of `B(δ_e,δ_q)` = sign `D_e`. Primes: `pqB(δ_p,δ_q)=𝒢^{ec}(p,q)`,
  so `𝒢^{ec}(p,q) = (p/2)log(q/p) + O(p)` for `q ≥ p²`. Unbalanced regime `Q ≥ P²` is solved
  (rank two + power saving, arbitrary coefficients); the open regime is `P ≤ Q ≤ P²`.
- **C7 DONE (criteria 1+3; WP4 core).** `BVI/LargeSieveDispersionOfTheCrossScaleRemainder`.
  `c` on primes `≤ Q₀`, `c'` on a window of length `L`:
  `|B + mR' + βH'| ≤ ½√(Σc(p)²p²)·√(L+2Q₀²−1)·√(Σc'(n)²/n⁴) + ½Σ|c(p)|p²·Σ|c'(n)|/n³`.
  Mechanism: `F_c(M) = Σ_p (c(p)/p)Σ_{ζ prim p} ζ/(ζ−1) ζ^M`; pronic summation by parts
  `Σ_{M≥A} w ζ^M = w(A)ζ^A/(1−ζ) + O(w(A)/(A|1−ζ|²))`; remainder = `Σ_j Σ_ζ α(ζ) Σ_n c'(n)w(jn)(ζ^j)^n`
  (residues of the large moduli mod the small primes); fibre count ≤ j + log-free large sieve;
  `Σ_{ζ prim p}|1−ζ|^{-4} ≤ p⁴/64` (Farey). For `a∼P`, `b∼Q`: loss `P^{5/2}/Q^{3/2}` ⇒ rank two at
  diagonal quality for `Q ≥ P^{5/3}` (was `Q ≥ P²`). One modulus, arbitrary coefficients.
- **C8 DONE (criterion 3; all moduli).** `BVI/LargeSieveDispersionInSelbergCoordinates`.
  Abstract: any fluctuation `F_c(M) = Σ_{ζ∈T} κ(ζ)ζ^M` over nontrivial roots of order `≤ Q₀` gives
  `|B + mR' + βH'| ≤ 4√(Σ_T|κ|²/|ζ−1|²)√(L+2Q₀²−1)√(Σc'²/n⁴) + 8Σ_T|κ|/|ζ−1|²·Σ|c'|/n³`.
  Every row `c` on `[1,Q₀]` (`F_c = W_{N,c}`, canonical primitive `κ = Y_c(ord ζ)ζ/(ζ−1)`):
  `|B + mR' + βH'| ≤ ½√(Σ_e Y_c(e)²e⁴)√(L+2Q₀²−1)√(Σc'²/n⁴) + ½Σ_e|Y_c(e)|e³·Σ|c'|/n³`.
  Removes the prime-support hypothesis of C7: Möbius/Selberg/Λ rows at the small scale are covered,
  with the Jordan weight `e⁴` on Selberg coordinates.

- **C9 DONE (criterion 3; exact second-order structure).** `BVI/SecondOrderCrossScaleLawAndTheBernoulliKernel`.
  Residue potential `Φ_d(M) = (d²−1)/12 − ρ(d−ρ)/2 = (d²/2)B₂(ρ/d) − 1/12` (second primitive of the
  centered residue, `|Φ| ≤ d²/8`, interval sums `≤ d³/8`); Bernoulli kernel `𝔅(d,n) = Σ_{j≥1}Φ_d(jn)/j²`
  (`= 𝔅(d, n mod d)`, `|𝔅| ≤ π²d²/48`). All rows, no support hypothesis:
  `|B + mR' + βH' − Σ_{n,d} c'(n)c(d)𝔅(d,n)/(dn²)| ≤ ¾ Σ|c(d)|d² · Σ|c'(n)|/n³`.
  Two primes: `|𝒢^{ec}(p,q) − D_p log q + pβ_p − 𝔅(p,q)/q| ≤ ¾ p³/q²`. The C6/C7 remainder is
  identified: a function of `q mod p` of size `p²/q` (Estermann cosine series at s=2 via B₂ Fourier),
  plus the rank-one piece `−(π²/72)(Σc/d)(Σc'/n²)`; the next error is smaller by `p/q`.

- **C10 DONE (criterion 4; sharpness of C7).** `BVI/CoherentNearMultipleObstructionToCrossScaleDispersion`.
  Bernoulli positivity `32(n mod d) ≤ d ⟹ 𝔅(d,n) ≥ d²/25 − 1/4`. Coherent shift (double counting,
  `Nat.filter_Ico_card_eq_of_periodic`): any `S ⊆ [1,D]`, any `Q` ⇒ `∃ n₀ ∈ [Q,Q+2D)` with
  `|S| ≤ 128|{d∈S : 64(n₀ mod d) ≤ d}|`. For `S ⊆ [64H, D]`, `n₀ ≥ 75D`, nonnegative `c` on coherent `S'`,
  `c'` on `[n₀,n₀+H)` (primes allowed): `E ≥ (1/100)(Σc(d)d)(Σc'(n)/n²) = (1/100)·[C6 bound]`.
  Against the diagonal (`a=1/d` on `S' ⊆ (D/2,D]`, `b=1/n` on the window):
  `E² ≥ (1/80000)·D³|S'|Hn₀/(n₀+H)⁴·D(a)D(b)` ⇒ loss `≍ P^{5/2}/(Q^{3/2}√log P)` for prime packets:
  the C7 threshold `Q ≥ P^{5/3}` is sharp up to `√log`. Named class: Type-II cross-scale inputs
  (arbitrary nonnegative large-scale coefficients on intervals of length `≤ P/64`). Replacement:
  low-frequency equidistribution of `c'` at the rationals `k/d`, `d ∈ supp c` (cancellation of
  `Σ_{n∈I}c'(n)` on intervals of length `≍ P` against coherent residues).

- **C11 DONE (criterion 3; exact loss).** `BVI/FourierFormOfTheBernoulliKernelAndTheExactCrossScaleLoss`.
  Spectral forms on the nontrivial `d`-th roots `T_d`: `r_d(M) = −Σ η^{M+1}/(η−1)`,
  `Φ_d(M) = Σ_{η∈T_d} η^M/|η−1|²` (positive-definite on `ℤ/d`, coefficients sum to `(d²−1)/12`).
  With `S(z) = Σ_n (c'(n)/n²)zⁿ`, `S₀ = Σ|c'|/n²`, `σ_p ≥ |S|` on `T_p`:
  `|Σ_n c'(n)𝔅(p,n)/n²| ≤ ((p²−1)/12)(π²σ_p/6 + 2S₀/p²)`, and for every row `c` on primes
  `|B + mR' + βH'| ≤ (π²/72)Σ_p|c(p)|pσ_p + (S₀/6)Σ_p|c(p)|/p + ¾Σ|c|p²Σ|c'|/n³`.
  The rank-two remainder bound improves exactly by `σ_p/S₀` (Fourier mass of `c'` at `k/p`);
  C10's coherent windows have `σ_p ≍ S₀`. Type-II input = `Σ_n c'(n)e(kn/p)/n²`, loss `σ_p/S₀`.

- **C12 DONE (criterion 4 replacement proven sufficient; criterion 3).** `BVI/BlockEquidistributionSufficesForCrossScaleDispersion`.
  Block discrepancy `Δ_H(c') = Σ_m |Σ_{block m} c'(n)/n²|` on `[A, A+KH)`. Block Abel:
  `|Σ (c'/n²)ζⁿ| ≤ Δ_H + H|ζ−1|S₀`; first-power Farey `Σ_{η∈T_d}|η−1|^{-1} ≤ (d/2)h_d` (corpus
  `circle_row_sum_le`). Every modulus: `|Σ_n c'(n)𝔅(d,n)/n²| ≤ (π²/72)(d²−1)Δ_H + H S₀ (d/2)h_d h_J + S₀d²/(8J)`.
  Every row `c` (all moduli): `|B + mR' + βH'| ≤ (π²/72)Δ_H Σ|c(d)|d + (Hh_N²/2 + 1/8)S₀Σ|c(d)| + ¾Σ|c|d²Σ|c'|/n³`.
  Gain over the rank-two bound: `Δ_H/S₀ + H log²N/P + P/Q`. With C10: block equidistribution at
  `H = o(P/log²P)` suffices; concentration on one window of length `P/64` defeats. The Type-II
  replacement hypothesis is exactly block equidistribution at the scale of the small moduli.

- **C13 DONE (criterion 3; the reciprocity).** `BVI/ReciprocityFormOfTheBernoulliKernel`.
  Cosine form `Φ_d(M) = Σ_{k<d} cos(2πkM/d)/(4sin²(πk/d))`; with `Σ_j cos(2πjx)/j² = π²B₂(x)` the infinite
  kernel is finite: `𝔅(d,n) = (π²/4)Σ_{k=1}^{d−1} B₂({kn/d})/sin²(πk/d)`; for `nn̄ ≡ 1 (d)`:
  `𝔅(d,n) = (π²/4)Σ_{k=1}^{d−1} B₂(k/d)/sin²(πkn̄/d)`. Two primes (inverse exists):
  `|𝒢^{ec}(p,q) − D_p log q + pβ_p − (π²/(4q))Σ_k B₂(k/p)csc²(πkq̄/p)| ≤ ¾p³/q²`.
  The reciprocity `{N/pq} ↔ p̄/q + q̄/p` at second order: beyond rank two, `Σa_pb_q𝒢^{ec}` is a
  bilinear form in the Kloosterman fractions `kq̄/p` with Dedekind-type cosecant–Bernoulli weights.

- **C14 DONE (criterion 1: θ up to 4/3 for a stated class).** `BVI/KuzminLandauGainForFlatSmallScaleRows`.
  Kuzmin–Landau (corpus `kuzminLandau_band`) for `Σ_{D₁≤d<D'} e(x/d)` (increments `x/(d(d+1))` monotone in
  `[x/D₂², 1/2]` for `2x ≤ D₁(D₁+1)`): `≤ 3D₂²/(2x) + 1`; Abel against `d²`: `|Σ d²cos(2πx/d)| ≤ 3D₂⁴/x + 2D₂²`.
  Flat column `Col(n) = Σ_{D₁≤d<D₂}𝔅(d,n)`: `|Col(n) + (π²/72)(D₂−D₁)| ≤ (12D₂⁴/n + 8D₂² + 2W₂h_J n/X₀)/(2π²) + W₂/(5J)`
  (`W₂ = Σd²`, `X₀ = D₁(D₁+1)/2`; truncations in `j,h`; divisor-type tail count `Σ_{(h+1)a>X}1/(h+1)² ≤ 2a/X`).
  Flat row `c(d) = d` on `[P,2P)` (`a_d = 1`), arbitrary `c'` above `Q`: remainder `≍ S₀(P⁴/Q + PQ log P)` vs rank-two
  bound `S₀P³` ⇒ diagonal quality for `Q ≥ P^{3/2} log P`. The `P^{5/3}` barrier (C10) is a Type-II phenomenon:
  Type-I (flat) small scales pass it.

- **C15 DONE (criterion 3, balanced regime: the window loss is spectral clustering).**
  `BVI/DiscreteGallagherInequalityAndTheWindowSpectrum`. Discrete Gallagher on `μ_M` (exact, finite):
  for `T ⊆ μ_M`, `1 ≤ L`, `4KL ≤ M`, `Σ_{j<K}|Σ_{ζ∈T}a(ζ)ζ^{A+j}|² ≤ (4M/L²)Σ_{ξ∈μ_M}|Σ_{y<L}1_T(ξωʸ)a(ξωʸ)(ξωʸ)^A|²`
  (Dirichlet kernel `Re Σ_{y<L}ω^{−yj} ≥ L(1−π²/24)`, Parseval). Window energy of every row on `[1,N]`:
  `Σ_{X≤M<X+K}F_c(M)²/(M(M+1)) ≤ (4N!/(L²X²))Σ_ξ|Σ_{y<L}κ(ξωʸ)(ξωʸ)^X|²`, `κ = Y_c(ord ζ)ζ/(ζ−1)`.
  Below the quadratic horizon the window energy is the clustering energy of the row's Farey spectrum at
  resolution `1/K`; C2's coherent blocks are exactly such clusters (numerators `a ≤ P²/X`).

- **C16 DONE (criterion 3, balanced regime: only `O(P²/X)` numerators matter).**
  `BVI/NumeratorSplitOfTheWindowEnergy`. Prime packet on `S ⊆ (2a₀, N]`: Farey form
  `F_c(M) = Σ_pΣ_{a<p} u(p,a)ω_p^{aM}`, `u = (c(p)/p)ω_p^a/(ω_p^a−1)`; split `a ≤ a₀`, `p−a ≤ a₀` (one-numerator sums
  `Ψ_{±a}`) vs large numerators (`|ω_p^a−1| ≥ 4min(a,p−a)/p` ⇒ `Σ_{large}|u|² ≤ Σc(p)²/(8a₀)`; log-free large sieve).
  `Σ_{X≤M<X+K}F_c(M)²/(M(M+1)) ≤ (2/X²)(2h_{a₀}Σ_{a≤a₀}aΣ_M(|Ψ_a|²+|Ψ_{−a}|²) + (K+2N²−1)Σc²/(8a₀))`.
  Large numerators cost `≍ (K+N²)/(a₀X)·diag`: on `[X,2X)` only `a ≲ P²/(εX)` numerators matter (bounded at θ→1⁺).

- **C17 DONE (criterion 4 replacement, balanced regime: clusters = short twisted interval sums).**
  `BVI/OneNumeratorClustersAreShortIntervalSums`. `a/p = ω^{a(M/p)}`, `M = N!`; with `4PL ≤ aM` the Gallagher arcs never
  wrap, each nonempty arc has `x > aM/(4P)` and collects exactly the primes in `(aM/(x+L), aM/x]` (length
  `≤ 16P²L/(aM)`), and only the arcs `a(M/(2P)) < x+L`, `x < a(M/P)` are nonempty. If all twisted sums
  `|Σ_{p∈S∩(t₁,t₂]} u(p,a)ω_p^{aX}| ≤ B` (`t₂−t₁ ≤ 16P²L/(aM)`): `Σ_{X≤m<X+K}|Ψ_a(m)|² ≤ (4M/L²)(a(M/(2P))+L)B²`.
  `Ψ_{−a} = conj Ψ_a`.

- **C18 DONE (criteria 1+4, balanced regime: replacement hypothesis proven sufficient).**
  `BVI/TwistedShortIntervalCancellationGivesWindowDispersion`. C16 + C17: for a prime packet on `(P,2P]` and
  bounds `B_a` on twisted sums of `u(p,a)ω_p^{aX}` over prime intervals of length `16P²L/(aN!)`:
  `E_{[X,X+K)} ≤ (2/X²)(2h_{a₀}Σ_{a≤a₀}a·2(4N!/L²)(a(N!/(2P))+L)B_a² + (K+2N²−1)Σc²/(8a₀))`.
  With `L = N!/(4K)`: intervals `4P²/(aK)`, factor `64K²a/P + 32K`. Twisted square-root cancellation
  (`B_a ≤ η√(4P²/(aK))|c|_∞/(4a)`, `a ≤ P²/(εX)`) ⇒ window energy within `(η²log² + ε)log P` of the diagonal
  for every `P ≤ X ≤ P²` (every `1 ≤ θ ≤ 2`). With C2 (coherent blocks, `B_a ≍ |I_a|`): the Type-II window
  barrier and its replacement are now both theorems.

- **C19 DONE (criterion 3: exact constant of the Type-II loss).** `BVI/SharpConstantOfTheRankTwoRemainder`.
  `Φ_d(M) ≤ Φ_d(0) = (d²−1)/12`, `|Φ_d| ≤ (d²−1)/12` (`d ≥ 2`), `𝔅(d,0) = π²(d²−1)/72`, `|𝔅(d,n)| ≤ π²(d²−1)/72`.
  Sharp rank-two law (`c(1)=0`): `|B+mR'+βH'| ≤ (π²/72)Σ|c(d)|(d²−1)/d·Σ|c'|/n² + ¾Σ|c|d²Σ|c'|/n³`.
  Attained: `c ≥ 0` with all moduli dividing `n₀`: `B(c,δ_{n₀}) + mR + βH ≥ (π²/72)Σc(d)(d²−1)/(dn₀²) − ¾Σcd²/n₀³`.
  The C6 constant 1 improves to the exact `π²/72`; extremal = coherence at residue zero (common multiples).

- **C20 DONE (criterion 3: Type-II dispersion for every bounded receiver row).** `BVI/LargeSieveDispersionForBoundedRows`.
  `Σ_{k≤m}1/k ≤ 2√m`; `|Y_c(e)| ≤ 2√(Q₀/e)/e` for `|c| ≤ 1` on `[1,Q₀]`; `Σ_{e≤Q₀}Y²e⁴ ≤ 2Q₀²(Q₀+1)`,
  `Σ|Y|e³ ≤ Q₀²(Q₀+1)`; hence `|B+mR'+βH'| ≤ ½√(2Q₀²(Q₀+1))√(L+2Q₀²−1)√(Σc'²/n⁴) + ½Q₀²(Q₀+1)Σ|c'|/n³`
  for every bounded row (μ, λ, characters, truncations), no arithmetic input. Gain over rank-two bound `≍ √(Q₀/L)`.

- **C21 DONE (criterion 4: no one-sided improvement; README sign question).** `BVI/TwoSidedSignLawOfTheSecondOrderKernel`.
  `B₂({k(1/2+σ)}) = (kσ)²−1/12` (k odd), `≤ (kσ)²+1/6` (k even) for `|kσ| ≤ 1/4`; `Φ_d(M) = (d²/2)B₂({M/d}) − 1/12`;
  `|n mod d/d − 1/2| ≤ 1/64 ⟹ 𝔅(d,n) ≤ −d²/100` (16 terms exact + tail `1/16`). Two primes:
  `𝒢^{ec}(p,q) − [D_p log q − pβ_p] ≤ −p²/(100q) + ¾p³/q²` near the half, `≥ (p²/25 − 1/4)/q − ¾p³/q²` near zero.
  The second-order cross-scale term oscillates in sign with `q mod p` at amplitude `≍ p²/q`.

- **C22 DONE (criterion 1: θ up to 4/3, flat large scale × arbitrary prime small scale).**
  `BVI/FlatLargeScaleRowsAndTheTypeIGain`. `c' = n·1_{[A+1,A+L]}` (`b = 1`): `|Σ_I ζⁿ/n| ≤ 2/((A+1)|ζ−1|)` (Abel +
  geometric), `|ζ−1| ≥ 4/p` ⇒ `σ_p ≤ p/(2(A+1))`; via C11: `|B+mR'+βH'| ≤ (π²/144)Σ|c(p)|p²/(A+1) + (Σ_I1/n)/6·Σ|c(p)|/p
  + ¾Σ|c|d²Σ_I 1/n²`. Gain `≍ P/Q` ⇒ diagonal quality for `Q ≥ P^{3/2}`. With C14: Type I at either scale beats `P^{5/3}`.

- **C23 DONE (criterion 4: parity barrier for the cross-scale method; README topic 4).**
  `BVI/CrossScaleParityBlindnessOfThePronicGram`. Residue masses `ρ_{c'}(d,r) = Σ_{n≡r(d)}c'(n)/n²`;
  `Σ_n c'(n)𝔅(d,n)/n² = Σ_{r<d}𝔅(d,r)ρ_{c'}(d,r)`. If `c'₁, c'₂` share all residue masses mod every modulus of `c`:
  `|B(c,c'₁) − B(c,c'₂) + m(c)ΔR + β(c)ΔH| ≤ ¾Σ|c|d²(Σ|c'₁|/n³ + Σ|c'₂|/n³)`. The cross-scale Gram sees the large
  scale only through local distribution mod the small moduli + two readouts: it is parity-blind (primes vs
  matched almost-primes, λ vs 1 on rough numbers). Parity-breaking input must come from the large-scale
  self-Gram or from near-diagonal scales.

- **C24 DONE (criterion 3: the sharp constant is attained within the primes).**
  `BVI/SharpConstantAttainedByPrimesInTheUnitClass`. `Φ_d(0) − Φ_d(j) ≤ min(jd/2, d²/8)` ⇒
  `π²(d²−1)/72 − (d/2)(h_d + 1/4) ≤ 𝔅(d,1) ≤ π²(d²−1)/72`. Dirichlet (mathlib `Nat.forall_exists_prime_gt_and_eq_mod`):
  for every prime `p` and bound `n` there is a prime `q > n`, `q ≡ 1 (p)`, with
  `𝒢^{ec}(p,q) − [D_p log q − pβ_p] ≥ (π²(p²−1)/72 − (p/2)(h_p+1/4))/q − ¾p³/q²` (vs upper `π²(p²−1)/(72q) + ¾p³/q²`).
  The extremal second-order coupling is realised by the Bézout seeds `q ≡ 1 (mod p)`.

## Queue

- C1 first-jump window: Brownian-bridge law and codimension no-go.
- Hyperbola (summatory) form of the truncated pronic Gram: dilated min kernels.
- Type-II exact loss: trivial `|S|` vs block lower bound; Type-I ⟺ short-interval PNT.
- Bézout ray reduction of window covariances; Chowla-type replacement hypothesis.

## Log
- 2026-10-20 — created
