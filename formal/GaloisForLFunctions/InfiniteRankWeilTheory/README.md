# Infinite-Rank Weil Theory over Spec ℤ (IRW)

Namespace `GaloisForLFunctions.InfiniteRankWeilTheory`; umbrella `InfiniteRankWeilTheory.lean`.
Specification: §2.8b of [the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

## 1. Motivation

Weil's theorem for a curve of genus `g` over `𝔽_q` has, in the form proved in this corpus for
every hyperelliptic curve, three steps:

1. **Crude count.** At every level `n` of the base-change tower, `|N_n − qⁿ − 1| ≤ C q^{n/2}` with
   `C` independent of `n` (Stepanov's auxiliary polynomial).
2. **Self-improvement.** Power sums of `2g` numbers that are `O(1)` at every level have every
   number of modulus `≤ 1` (finite-rank elimination). The constant `C` is irrelevant.
3. **Reflection.** The functional equation `β ↦ 1/β` turns `|β| ≤ 1` into `|β| = 1`.

A fourth reading packages the result as a **count**: the channel numbers extend to an `ℕ`-valued
count whose Tate limit is the intersection form.

Over `Spec ℤ` the modes are the zeros of `ξ`: infinitely many, growing like `T log T`, with
infinite Kronecker rank. Each step changes character at infinite rank:

| Step | Finite rank (curve) | Infinite rank (`ℤ`) |
|---|---|---|
| crude count | `O(q^{n/2})` at every level | false in the size coordinate (`|ψ(x)−x| ≤ C√x` fails); survives only in the exceptional coordinate as ZAL (finitely many zeros beyond each depth), which is ≥ quasi-RH |
| self-improvement | finite elimination; any constant | AAL: a bound valid for all but finitely many modes holds for all; its base case at `σ=½` is B13 |
| reflection | `β ↦ 1/β` | `ρ ↦ 1−ρ`; consistent with every finite off-line layer |
| count | Tate limit of `ℕ`-valued counts | exists at weight `δ>0`; at the critical weight `δ=0` it is RH |

IRW is the theory of Weil data of infinite rank. It asks, for each step, what its infinite-rank
form is, exactly when it holds, what it costs, and which arithmetic input each infinite-rank form
needs that the finite-rank form gets for free. Its working hypothesis is that every failure of a
curve step over `ℤ` is a **rank phenomenon**, and that a proof of RH must build the infinite-rank
version of each step at the place the corpus has located: the crude step at the dark range, the
self-improvement at the critical line, the count at the critical weight.

## 2. Objects

| Object | Meaning |
|---|---|
| Weil tower `(z_i)_{i∈ι}` at base `ℓ` | countable family of nonzero modes `z_i = e^{ℓ(ρ_i−½)}`, closed under conjugation and under the reflection `z ↦ 1/z̄`; a curve datum is a tower of finite rank at `ℓ = log q`; a prime tower of `ζ` is the tower at `ℓ = log p` |
| Weights `w_i` | summable (trace-class) coefficients attached to the modes by a test; `Σ|w_i|` is the **trace norm** |
| Level sum `S(ν) = Σ w_i z_iⁿ` | the infinite-rank power sum; for `ζ` at base `ℓ` it is a sampled Weil lag / Lefschetz sequence |
| Outer, critical, inner part | `|z|>1`, `|z|=1`, `|z|<1`; reflection exchanges outer and inner |
| Top layer | modes of maximal modulus `R`; **isolated** if the rest has modulus `≤ r < R` |
| Rank | number of modes of a layer; the **exceptional rank** is the rank of the top layer |
| Configuration | multiset of modes `ρ` in the strip, closed under `ρ ↦ ρ̄` and `ρ ↦ 1−ρ` |
| Abscissae | `Θ = sup Re ρ`, `Θ∞ = limsup_{|γ|→∞} Re ρ`; `Θ₂` the second abscissa |
| Exceptional set at depth `h` | modes with `Re ρ > ½+h`; in a tower, `|z| > e^{ℓh}` |
| Level sets of indices | sets `G ⊆ ℕ` of levels on which a bound is known: windows, thick sets (containing arbitrarily long intervals), syndetic sets, sets of positive density |
| Dirichlet polynomial at a return | `A(s) = Σ_{n≤N} c_n n^{−s}` evaluated at heights `t` with `|p^{it}−1| ≤ δ` for `p ≤ y` |
| Collision form | `Σ_{m,n} a_m ā_n K(T log(m/n))`, the off-diagonal of a mean value of a Dirichlet polynomial longer than the height |
| Calibration battery | curve data (finite rank, complete proof); golden fake (FE, integrality, an outer mode); periodic configurations (function fields); cosh models (FE, order one, any finite layer); Beurling one-offs (Euler product, no FE); shifted products `ξ(s+a)ξ(s−a)` |

## 3. Language

- **Level**: an exponent `ν` of the tower; for `ζ`, the scale `x = e^{νℓ}`.
- **Crude bound** on `G`: `|S(ν)| ≤ C r^ν` for `ν ∈ G`, any constant `C`.
- **Self-improves** on `G`: a crude bound on `G` at rate `r` forces every visible mode to `|z| ≤ r`.
- **Visible**: the weight of the mode's modulus class is not cancelled (top-group weights bounded below).
- **Well-founded outer part**: finitely many modes above every radius `> 1` (the tower form of ZAL).
- **Isolated top**: finitely many modes of maximal modulus above a gap (the tower form of ¬AAL).
- **Rank barrier**: any statement whose constants or windows depend on the total rank is void at
  infinite rank; what survives depends only on the exceptional rank and the trace norm.
- **Eventual-to-global**: a right bound valid above some height is valid at all heights (AAL).
- **Reflection**: `ρ ↦ 1−ρ`, in towers `z ↦ 1/z`; with conjugation `z ↦ 1/z̄`.
- **Return**: a height at which every prime phase up to `y` is within `δ` of `1`.
- **Forced vanishing**: approximate vanishing at every return, produced by moment conditions.
- **Critical weight**: `δ = 0` in the weighted spaces `ℓ²(n^δ)` of the count.

## 4. Mechanisms

1. **Turán windows.** A finite-rank power sum with a top mode of modulus `R` is `≥ c(k,M)R^ν` at some
   level of every window of `k` consecutive levels, `c(k,M)` polynomial in `M`. One far window, or a
   thick set of levels, therefore self-improves; at infinite rank the remainder below the top is paid
   in trace norm and does not enter the window length.
2. **Roots of unity.** A top layer `R·μ_k` has vanishing power sums off `kℤ`: a bound on a set of
   density `1−1/k` does not self-improve. Windows of length equal to the exceptional rank are
   necessary; at unbounded rank only thick sets work.
3. **Vandermonde hiding.** Finitely many unimodular modes cancel a top mode on any finite window;
   Turán fixes the trace norm such hiding costs. Trace norm, not rank, is the currency.
4. **Well-founded elimination.** If the outer part is finite above every radius, a crude bound with
   any constant at every large level removes it; reflection then puts every visible mode on the
   unit circle. Without well-foundedness, Wolff configurations have vanishing level sums.
5. **The exceptional coordinate.** ZAL is well-foundedness of the outer part; ¬AAL is an isolated
   top of finite rank; so the ¬AAL world is a finite-rank Weil datum riding on an infinite-rank
   remainder, which is exactly the regime of mechanisms 1–3.
6. **Reflection is consistent with every finite layer.** `cosh(s−½)` times any finite reflection-closed
   polynomial factor is an entire function of order one with functional equation, reality and any
   prescribed finite off-line layer; the functional equation acts on level sums only by
   `S(−ν) = conj S(ν)`.
7. **Returns freeze smooth polynomials.** At a `δ`-return, a Dirichlet polynomial supported on
   `y`-smooth integers moves by at most `δ` times its logarithmic mass; moment conditions give
   approximate vanishing to high order at every return at once (the archimedean shadow of
   `x^q − x`).
8. **Long mean values are collision counts.** A band-limited mean value of a Dirichlet polynomial of
   any length is the diagonal plus a form on pairs `|log(m/n)| < 1/T`; beyond the height the
   off-diagonal dominates, and for prime coefficients it is a count of prime pairs in short
   multiplicative ranges.

## 5. Questions

| # | Question (§2.8b) | Form in IRW |
|---|---|---|
| Q1 | What replaces "finitely many power sums" when the modes are infinite and grow like `T log T`? | which level sets `G` self-improve, at which exceptional rank, at which trace norm |
| Q2 | Which exceptional-set bound self-improves under the FE? | classification of eventual-to-global laws over the calibration battery |
| Q3 | What is the infinite-rank analogue of `|α| ≤ √q` from `Σαⁿ = O(q^{n/2})`? | elimination for well-founded towers; failure modes (sharp cutoffs, walls) |
| Q4 | Is a finite top layer compatible with the FE once the bottom layer is reflected into the power sums? | reflection-closed models; what the FE forces on level sums |
| Q5 | Which auxiliary function has forced vanishing at the returns of the prime orbit with controlled size? | moment-annihilated smooth Dirichlet polynomials; their size at returns |
| Q6 | What survives of a positive count at `δ>0` as `δ→0`? | damped and tilted towers; positivity at the critical weight |

## 6. Tools

| # | Tool (§2.8b) | IRW form |
|---|---|---|
| T1 | infinite-rank Turán theorem with tail controlled by the reflected bottom layer | window lower bounds depending only on the exceptional rank, remainder paid in trace norm, inner layer included |
| T2 | Frobenius substitute for auxiliary functions at the archimedean place | freezing at returns, forced vanishing by moments |
| T3 | mean-value theorems for Dirichlet polynomials longer than the height with main terms | band-limited mean value = diagonal + collision form; main terms |
| T4 | count on correspondences at the critical weight | positivity of damped/tilted level kernels as `δ → 0` |

## 7. Pillar theorems

To be filled as the modules are proved; every entry will name its Lean declaration.

## 8. Traps

| Trap | Truth |
|---|---|
| A crude constant-factor bound over `ℤ` is the analogue of Stepanov's | `|ψ(x)−x| ≤ C√x` is false; smoothed it is RH; the crude regime is the exceptional coordinate |
| Turán's theorem works at infinite rank | its constants decay like `(kM)^{−k}` in the total rank; only the exceptional rank may enter |
| A bound on most levels self-improves | roots-of-unity layers vanish on density `1−1/k`; windows of the exceptional rank are needed |
| The FE excludes a top layer through the power sums | every finite reflection-closed layer has an FE model of order one |
| Elimination holds for every summable tower | Wolff configurations: walls make every level sum vanish |
| AAL uses the position of the line | symmetric shifts preserve AAL; only the involution may be used |
| Height averages see a finite layer | density statements miss every finite set |
| Returns make every polynomial small | only moment-annihilated, smooth-supported ones, at precision set by the logarithmic mass |
| A long mean value is a diagonal | beyond the height the collision form dominates; for primes it is a binary problem |

## 9. Open research topics

1. A producer of a crude bound on a thick set of levels of one tower, in the finite stratum.
2. A reflection-sensitive statement on the critical line that a finite top layer violates.
3. Rouché stability of forced vanishing at constant precision, and a Stepanov count of returns.
4. Main terms of the prime collision form at lengths `T^{1+θ}`.
5. The critical-weight count (B87/B88).

## 10. Calibration

Every IRW statement must reduce to the corpus curve proof at finite rank, fail on the golden fake
through the crude count, hold automatically on periodic configurations, be invariant under
symmetric shifts, and fail on Beurling one-offs through the missing functional equation.

## 11. Context

| Neighbour | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | curve data, Frobenius eigenvalues `frobEig`, prime towers, Wolff walls |
| ArithmeticOrientationGeometry | orbit correlations, eventual Hasse–Weil, rate = depth |
| CountingHolography | count law of every hyperelliptic curve; crude count ⇔ count law |
| ZeroConfigurationGeometry, RHTower | AAL, eventual-to-global, shift invariance, finite oscillation of `ψ` |
| HTGeometry | Turán's second main theorem, separation-free, weighted |
| HeckeKreinToeplitz, ArithmeticKreinLangerTheory | finite stratum, Krein–Langer structure, towers decide |
| ArithmeticPositiveDuality | one-offs, positive annihilators, relocation |
| TailArithmeticOfThePrimeOrbit, PrimeTorusTheory | returns, precision law, Kronecker scale |
| HeightHomotopyArithmeticCounts | renormalized torsion forms on `ℓ²(n^δ)` |

## 12. Success criteria

IRW succeeds when each of Q1–Q6 has a theorem-level answer (positive, or a sharp no-go with its
positive survivor), each tool T1–T4 exists in Lean in its strongest unconditional form, every
pillar reduces to the curve proof at finite rank, and the open core is stated as one precise
infinite-rank statement per step.

**A contribution** must: be unconditional; state its rank dependence (total, exceptional, or none);
say which calibration models it holds on and which it fails on; be invariant under symmetric
shifts or say why not; and not be an exact restatement of an RH-equivalent already in the corpus.
