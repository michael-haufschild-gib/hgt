# Constituent theory of the zeros (CTZ)

- **ID:** CTZ
- **Stage:** 1-in-progress
- **Type:** programme (THEOREM (paper) per section; THEOREM (Lean) where a module is named)
- **Source:** `docs/reports/review-1011/obstacles-summary.md` §2.11 (questions), §2.6 (B153), §1.5
- **Statement:** which functions with an arithmetic expansion can share zeros with `ξ`: exactly, on
  a half-plane, in a strip, in a box, in the limit.

## Goal
Answer Q1–Q7 of the README of `formal/GaloisForLFunctions/ConstituentTheoryOfTheZeros/`. Every
statement is pointwise and sign-free. Nothing here locates a zero of `ξ`.

## Lean
Folder `formal/GaloisForLFunctions/ConstituentTheoryOfTheZeros/`, umbrella
`ConstituentTheoryOfTheZeros.lean`.

| Module | Content | State |
|---|---|---|
| TheJumpLawHoldsOnEveryStripAboutTheLine | P1, P2 | to do |
| TheWienerAlgebraOfAStrip | P3 (algebra) | to do |
| WienersLemmaOnAStrip | P3 (characters, inversion) | to do |
| NoAbsolutelyConvergentDirichletSeriesIsAConstituent | P4 | to do |

## Paper proofs

Notation: `{u}` fractional part; `K(s) = −ζ(s)/s = ∫_0^∞ {u} u^{−s−1} du` for `0 < Re s < 1`
(`RHTower.integral_Ioi_zero_fract_cpow`); `g_{b,a}(u) = Σ_i b_i {a_i u}` (`fractSeries`).

### P1. The jump law on a strip of any width, any scales
Let `0 < η ≤ ½`, countable families `(b_i, a_i)`, `(c_j, q_j)` with positive scales and
`Σ ‖b_i‖ a_i^σ < ∞` for `σ ∈ (½, ½+η]`, `Σ ‖c_j‖ q_j^σ < ∞` for `σ ∈ [½−η, ½)`. Let `Φ` be
holomorphic on `½−η < Re s < ½+η`, bounded on `½−η/2 ≤ Re s ≤ ½+η/2`, with
`Φ = K · Σ b_i a_i^s` right of the line and `Φ = K · Σ c_j q_j^s` left of it (inside the strip).
Then `g_{b,a} = g_{c,q}` on `(0, ∞)` and for every `u₀ > 0`
`Σ_{a_i u₀ ∈ ℤ} b_i = Σ_{q_j u₀ ∈ ℤ} c_j`.

*Proof.* Put `κ = 2η`, `c₀ = ½ − η`, `s = κ s' + c₀`. For measurable `g` let
`g̃(v) = κ^{−1} v^{−c₀/κ} g(v^{1/κ})`. Then `mellin g̃ (−s') = mellin g (−(κ s' + c₀))`
(substitution `u = v^{1/κ}`). `‖g(u)‖ ≤ C u^σ` gives `‖g̃(v)‖ ≤ κ^{−1} C v^{(σ − c₀)/κ}`, and
`σ ↦ (σ − c₀)/κ` maps `(½, ½+η]` onto `(½, 1]` and `[½−η, ½)` onto `[0, ½)`. `Φ̃(s') = Φ(κ s' + c₀)`
is holomorphic on `0 < Re s' < 1` and bounded on `¼ ≤ Re s' ≤ ¾`. The gluing theorem
`eq_of_mellin_eq_two_sided` applies to `g̃_{b,a}`, `g̃_{c,q}`, `Φ̃`: they agree at every point of
continuity `v ≠ 1` of their difference, hence `g_{b,a} = g_{c,q}` at the points of continuity
`u ≠ 1` of the difference. Both are right continuous and the exceptional set is countable, so they
agree everywhere; left limits then agree, and the jump of `g_{b,a}` at `u₀` is
`−Σ_{a_i u₀ ∈ ℤ} b_i`. ∎

### P2. Merged weights agree; the expansion continues across the line
Under P1, for every `t > 0`: `Σ_{a_i = t} b_i = Σ_{q_j = t} c_j`. Consequently
`H(s) = Σ_t w(t) t^s`, `w(t)` the common merged weight, converges absolutely on the closed strip
`½−η ≤ Re s ≤ ½+η`, is holomorphic inside, and `Φ = K·H` on the strip.

*Proof.* Fix `t`. On the disjoint union of the index sets take the weights `b_i` and `−c_j`,
restricted to the indices whose scale is `t` times a natural number `n ≥ 1`, with the scales
`a_i/t`, `q_j/t`. The restricted family is absolutely summable and summable against
`scale^{1/4}`, because `1 ≤ n^{1/4} ≤ n^σ` for the exponent `σ ≥ ¼` at which the full family is
summable. The jump law at `u₀ = 1/(kt)` says that its total weight on the scales divisible by `k`
is zero for every `k ≥ 1`. Möbius inversion (`tsum_eq_of_tsum_dvd`) gives weight zero at the scale
`1`: `Σ_{a_i = t} b_i − Σ_{q_j = t} c_j = 0`.
Regrouping by scales, `Σ_t ‖w(t)‖ t^σ < ∞` for `σ ∈ [½−η, ½) ∪ (½, ½+η]`, hence, by
`t^σ ≤ t^{σ₁} + t^{σ₂}` for `σ₁ ≤ σ ≤ σ₂`, on the whole closed interval. So `H` is holomorphic on
the open strip, `K·H = Φ` right of the line, and the identity theorem gives it on the strip. ∎

*Corollary (ζ cancels no pole of a two-sided expansion).* If `G` is meromorphic on the strip,
`Φ = K·G` off the poles of `G`, and `G` has the two expansions, then `G = H` has no pole in the
strip.

### P3. Wiener's lemma on a strip
For `σ₁ ≤ σ₂` let `𝒲[σ₁, σ₂]` be the functions on the closed strip `S = {σ₁ ≤ Re s ≤ σ₂}` of the
form `f(s) = Σ_{q ∈ ℚ₊} c_q q^{−s}` with `‖f‖ = Σ ‖c_q‖ w(q) < ∞`, `w(q) = max(q^{−σ₁}, q^{−σ₂})`.

(a) *Uniqueness of coefficients.* For `σ ∈ [σ₁, σ₂]` and `r ∈ ℚ₊`,
`(1/2T) ∫_{−T}^{T} f(σ + it) r^{σ + it} dt → c_r`: termwise the mean of `(r/q)^{it}` is
`sin(T log(r/q))/(T log(r/q)) → 0` for `q ≠ r`, dominated by `‖c_q‖ q^{−σ} r^σ`.

(b) *Banach algebra.* `w(qr) ≤ w(q) w(r)`, so the pointwise product of two elements is the
element with coefficients `Σ_{q r = m} c_q d_r`, and `‖fg‖ ≤ ‖f‖‖g‖`. The coefficient map is an
isometry onto the weighted `ℓ¹`, which is complete. `‖1‖ = 1`.

(c) *Characters.* Let `φ` be a character and `χ(q) = φ(δ_q)`, `δ_q(s) = q^{−s}`. `χ` is a
homomorphism `ℚ₊ → ℂ^×` with `‖χ(q)‖ ≤ w(q)`. Write `‖χ(p)‖ = p^{−τ_p}`. For primes `p₁, p₂` and
`b ≥ 1` let `a = ⌈b log p₂ / log p₁⌉`, `q = p₁^a p₂^{−b}`, so `1 ≤ q < p₁`. Then
`‖χ(q)‖ = q^{−τ_{p₁}} p₂^{b(τ_{p₂} − τ_{p₁})}`... precisely
`log ‖χ(q)‖ = −τ₁(a L₁ − b L₂) − b L₂(τ₁ − τ₂)`, `L_i = log p_i`; the bounds
`‖χ(q)‖ ≤ w(q)`, `‖χ(q^{−1})‖ ≤ w(q^{−1})` bound `b L₂ |τ₁ − τ₂|` uniformly in `b`: `τ₁ = τ₂ = σ`.
From `‖χ(p)‖ ≤ p^{−σ₁}` and `‖χ(p^{−1})‖ ≤ p^{σ₂}`: `σ₁ ≤ σ ≤ σ₂`. So `χ(q) = q^{−σ} ω(q)` with
`ω` unimodular and multiplicative.

(d) *Density.* By Kronecker's theorem for the prime logarithms
(`SquareRootThreshold.exists_height_prime_phase_approx`), for every finite set of primes and
`ε > 0` there is `t` with `‖p^{−it} − ω(p)‖ < ε` on the set. For `q` a quotient of products of
these primes, `‖q^{−it} − ω(q)‖ ≤ (number of prime factors) · ε`. Hence for `f ∈ 𝒲` with finitely
many terms, and then for every `f` by `‖φ‖ ≤ 1`: `φ(f)` is a limit of values `f(σ + it)`.

(e) *Wiener's lemma.* If `‖f(s)‖ ≥ δ > 0` on `S`, every character has `‖φ(f)‖ ≥ δ`, so `f` is a
unit (Gelfand): `1/f ∈ 𝒲[σ₁, σ₂]`. ∎

### P4. No absolutely convergent Dirichlet series is a constituent with a zero
Let `Σ ‖a_n‖ n^{−x} < ∞` with `x < ½`, `F(s) = Σ a_n n^{−s} ≢ 0`. If every zero of `F` in
`Re s > x` is a zero of `ξ`, then `F` has no zero in `Re s > x`. More precisely, if `F` has a zero
in `Re s > x`, infinitely many of its zeros there are not zeros of `ξ`.

*Proof.* Suppose all zeros of `F` in `Re s > x` but finitely many are zeros of `ξ` and `F` has a
zero. By recurrence against density (`exists_zero_not_xi_zero_of_re_ne_half` applied above the
finitely many exceptions, as in `infinite_zeros_not_xi_zeros_of_re_ne_half`) all zeros lie on the
line; by recurrence there are infinitely many. Treat first the case of no exception.
Choose `η` with `max(x, 0) < ½ − η`. `F` is almost periodic on closed substrips of `Re s > x` and
zero-free on `x < Re s < ½` and on `Re s > ½`; a zero-free almost periodic holomorphic function is
bounded below on closed substrips (normal limit of translates and Hurwitz). By P3 on the strips
`[½−η, ½−η']` and `[½+η', ½+η]`, `0 < η' < η`, `1/F` and then `G = F'/F` (the derivative has the
coefficients `−a_n log n`, summable on the open half-plane) lie in the Wiener classes of these
strips; the coefficients on nested strips agree by (a). Letting `η' → 0` gives families with
`Σ ‖b_q‖ q^{−σ} < ∞` for all `σ ∈ (½, ½+η]` and `Σ ‖c_q‖ q^{−σ} < ∞` for all `σ ∈ [½−η, ½)`
representing `G`. `Φ = K·G` extends holomorphically to the strip (`ζ` vanishes at the zeros of `F`)
and is bounded near the line by the maximum principle between good heights. P2 gives `G = H`
holomorphic on the strip: `F` has no zero there. With finitely many exceptional zeros `p` on the
line, `Φ` has simple poles there; the two series of fractional parts differ by the continuous
function `Σ_p r_p u^p` and the jump law is unchanged
(`InfiniteRankPurityTheory.fractSeries_sub_eq_polarPart`), so `G − Σ_p r_p/(s − p)·(…)` — precisely
`K·G` and `K·H` differ by the polar parts, and `G = H + (\text{polar parts})/K` has at most the
finitely many poles `p`: but `F` has infinitely many zeros on the line. ∎

### P5. Bohr's inequality; Q1 for `x < 0`
If `F` is bounded and holomorphic on `Re s > x` and equals `Σ a_n n^{−s}` where that converges
absolutely, then `Σ ‖a_n‖² n^{−2σ} ≤ sup ‖F‖²` for `σ > x` and `Σ ‖a_n‖ n^{−σ} < ∞` for
`σ > x + ½`. With P4: for `x < 0` a constituent of the bounded class on `Re s > x` has no zero.

*Proof.* For `σ > x` the mean of `F(σ + it) n^{σ + it}` over `[−T, T]` tends to `a_n`: on a line of
absolute convergence termwise, and the two vertical means differ by the horizontal sides of a
rectangle, `O(1/T)`, by Cauchy's theorem and boundedness. Bessel's inequality for the finite
sections gives the square sum; Cauchy–Schwarz with `Σ n^{−1−2ε}` gives the absolute sum. ∎

### P6. Uniform heights in bounded length
For `N ≥ 2` and `0 < c ≤ 1` there is `H₀` such that every Dirichlet polynomial
`D = Σ_{n ≤ N} a_n n^{−s}` with `‖a_n‖ ≤ 1` and two coefficients of modulus `≥ c` has a zero with
`|Im ρ| ≤ H₀` that is not a zero of `ξ`.

*Proof.* Otherwise there are `D_k` with every zero of height `≤ k` a zero of `ξ`. The coefficient
vectors lie in a compact set; a subsequence converges to a polynomial `D` with two nonzero
coefficients. Every zero of `D` is a limit of zeros of `D_k` (Hurwitz), whose heights are
eventually `≤ k`, so every zero of `D` is a zero of `ξ`, against `exists_zero_not_xi_zero`. ∎

## Open
- Q1 for the bounded class on `Re s > x`, `0 ≤ x < ½`, without absolute convergence left of the
  line: the left expansion of `F'/F` has square summable coefficients only, and the sums over the
  progressions `{mt}` of scales converge absolutely exactly for exponents `> ½`.
- Q3 with explicit heights; Q4 for growing length; Q5–Q7.

## Log
- 2026-11-10 — created in 1-in-progress
