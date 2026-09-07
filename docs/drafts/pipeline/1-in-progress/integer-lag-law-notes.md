# The integer lag law — consolidated notes (NOT a stage-4 item; proof-hunting reference only)

## Abstract

Let `ψ` be the Chebyshev function, `Λ` the von Mangoldt function, `γ` Euler's constant, and
`S(n) = Σ_{k≥1} n^{−2k}/(2k(2k+1))`. For `n ≥ 1` put

```text
a_n = [ (n − ψ(n)) + n·(Σ_{m≤n} Λ(m)/m − log n + γ) − log 2π + S(n) ] / √n .
```

Then `a_1 = 2 + γ − log 4π = 0.0461…`, and the Riemann Hypothesis is equivalent to the single
one-sided inequality `a_n ≤ a_1` for all `n ≥ 1` (Theorem 3). The constant is exact and the sequence
sees it: without any hypothesis, `a_n > a_1 − ε` for infinitely many `n` (Theorem 4), and under RH
the supremum of every tail `{a_n : n ≥ N}` is `a_1`, approached along the powers of every base
(Theorem 4). The sign of the numerator carries no information about the zeros: unconditionally it is
`> (a_1 − ε)√n` infinitely often and `≤ −η√n` infinitely often (Theorem 5). The floor is
arithmetic: under RH, `−a_1` is the exact infimum of `{a_n : n ≥ 2}` if and only if every integer
relation among finitely many distinct ordinates of zeros has even coefficient sum (Theorem 6), a
parity condition implied by, and weaker than, the linear-independence conjecture. The mechanism is
the lag function `Φ(L) = Σ_ρ e^{L(ρ−½)}/(ρ(1−ρ))`, whose genus-kernel explicit formula makes
`a_n = Φ(log n)`; RH is equivalent to `Φ` being bounded, bounded above, bounded below, or Bohr
almost periodic (Theorems 1, 2, 5). All statements are certified in Lean 4 with no axioms beyond
`propext`, `Classical.choice`, `Quot.sound`.

## 1. Setting

`ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` is entire, real on the real axis, `ξ(1−s) = ξ(s)`, with all
zeros in `0 < Re s < 1`, none real. Zeros are counted with multiplicity (the Lean type `XiZeroCopy`
is the sigma type of zeros and copies below the multiplicity). `Σ_ρ 1/(ρ(1−ρ))` converges absolutely
and equals `2 + γ − log 4π`; we write `a_1` for this constant. The lag function is

```text
Φ(L) = Σ_ρ e^{L(ρ−½)} / (ρ(1−ρ)),   L ∈ ℝ,
```

absolutely convergent for every `L`, real-valued (the zero set is symmetric under `ρ ↦ 1 − ρ̄`),
even (`ρ ↦ 1 − ρ`), continuous, with `Φ(0) = a_1`.

**Genus-kernel explicit formula.** For real `X > 1`,

```text
Σ_ρ X^ρ/(ρ(1−ρ)) = (X − ψ(X)) + X·(Σ_{n≤X} Λ(n)/n − log X + γ) − log 2π + S(X).
```

It is proved by termwise residues on the Mittag-Leffler expansion of `−ζ'/ζ` with the kernel
`X^s/(s(s−1))` on `Re s = 2`, a two-centre majorant, and `Σ_ρ |ρ−½|^{−3/2} < ∞`; no zero-density
input and no truncated Perron formula enter. Consequently, for `L > 0` and `X = e^L`,

```text
Φ(L) = e^{−L/2}(X − ψ(X)) + e^{L/2}(Σ_{n≤X}Λ(n)/n − L + γ) − e^{−L/2}(log 2π − S(X)),
```

and `a_n := Φ(log n)` is the sequence of the abstract.

## 2. The lag criterion

**Theorem 1 (two-sided).** RH ⟺ `Φ` is bounded on `ℝ`; and then `|Φ(L)| ≤ Φ(0) = a_1`.

*Proof sketch.* Under RH each term has modulus `|ρ(1−ρ)|^{−1}`. Conversely, if `|Φ| ≤ M`, the Mellin
transform `F(s) = ∫_0^1 Φ(−log y) y^{s−1} dy` is holomorphic on `0 < Re s < 2` and equals the
Mittag-Leffler series `G(s) = Σ_ρ (ρ(1−ρ))^{−1}/(s − (ρ − ½))` on `Re s > ½`. An off-line zero with
maximal real part on its horizontal line gives a pole of `G` whose right horizontal ray is pole-free
(finitely many zeros on a compact segment); the real-analytic identity theorem along the ray forces
`F` to blow up at the pole. ∎

**Theorem 2 (one-sided).** RH ⟺ `Φ` is bounded above ⟺ `Φ` is bounded below.

*Proof sketch.* If `Φ ≤ M`, the measure `(M − Φ)du + du` on `(0,∞)` is nonnegative; by Landau's
theorem its Laplace transform has a genuine singularity at its abscissa of convergence, but the
transform agrees on `Re s > ½` with `(M+1)/s − G(s)`, analytic at every real point `> 0` because `ξ`
has no real zeros; the real-analytic identity theorem carries the agreement down to the abscissa,
which is therefore `0`, and Theorem 1's extension argument gives RH. The lower bound is symmetric. ∎

## 3. The integer lag law

**Lemma 3.1 (interval bound).** For `L ≥ log 2` and `n = ⌊e^L⌋`,
`|Φ(L) − a_n| ≤ 3(log n + 2)²/√n` (and in particular `≤ 30`).

*Proof.* With `X = e^L`, `ψ(X) = ψ(n)`, the difference is the sum of six pieces:
`(√X − √n)`, `ψ(n)(n^{−½} − X^{−½})`, `(√X − √n)(M(n) − L + γ)`, `√n(log n − L)`,
`log 2π (n^{−½} − X^{−½})`, `S(X)X^{−½} − S(n)n^{−½}`, each of which is monotone in `X` on
`[n, n+1)`. The elementary bounds `√(n+1) − √n ≤ 1/(2√n)`, `ψ(n) ≤ (n+1) log n`,
`M(n) ≤ log n·(1 + log n)`, `0 ≤ L − log n ≤ 1/n`, `0 ≤ S ≤ S(1) = 1 − log 2`, `log n ≤ 4n^{1/4}`
give pieces of size `≤ (½ + log n + (log n+2)²/2 + 6)/√n` above and `≥ −((log n+2)²/2 + 2)/√n`
below. ∎

**Theorem 3 (integer lag law).** The following are equivalent: (i) RH; (ii) `a_n ≤ a_1` for all
`n ≥ 1`; (iii) `(a_n)_{n≥2}` is bounded above; (iv) `(a_n)_{n≥2}` is bounded below; (v) for all
`n ≥ 2`,

```text
(n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + S(n) ≤ (2 + γ − log 4π)·√n .
```

Moreover (dichotomy) either `|a_n| ≤ a_1` for all `n`, or `(a_n)` is unbounded above and unbounded
below.

*Proof.* (i)⇒(ii): Theorem 1 at `L = log n`. (iii)⇒(i): for `L ≥ log 2`, `Φ(L) ≤ a_{⌊e^L⌋} + 30` by
Lemma 3.1; for `|L| ≤ log 2`, `|Φ(L)| ≤ √2·Σ_ρ|ρ(1−ρ)|^{−1}`; `Φ` is even; so `Φ` is bounded above
and Theorem 2 applies. (iv)⇒(i) is symmetric. (ii)⟺(v) is `a_n = Φ(log n)` and `√n > 0`. The
dichotomy is (i) versus the negations of (iii) and (iv). ∎

## 4. The ceiling is universal

**Theorem 4.** (a) Under RH, for every base `b` and every `ε > 0` there is `m ≥ 1` with
`a_1 − ε < a_{b^m} ≤ a_1`; hence `a_1` is the least upper bound of every tail `{a_n : n ≥ N}`.
(b) Unconditionally, for every `ε > 0` there are arbitrarily large `n` with `a_n > a_1 − ε`; so
`limsup a_n ≥ a_1`, with equality iff RH.

*Proof.* (a) Under RH `Φ(L) = Σ_ρ w_ρ cos(γ_ρ L)` with `w_ρ = (¼ + γ_ρ²)^{−1} > 0`, `Σ w_ρ = a_1`.
Choose a finite set `F` of zeros carrying all but `ε/4` of the weight and `Q ≥ 8π²a_1/ε`.
Simultaneous Dirichlet approximation of the `|F|` numbers `γ_ρ log b/2π` gives `m ∈ [1, Q^{|F|}]`
with `‖mγ_ρ log b/2π‖ < 1/Q` on `F`, hence `cos(γ_ρ m log b) ≥ 1 − (2π/Q)²/2` there, and
`a_{b^m} ≥ (a_1 − ε/4)(1 − (2π/Q)²/2) − ε/4 > a_1 − ε`. (b) Under RH use (a) with base `N`;
otherwise `(a_n)` is unbounded above by Theorem 3. ∎

The return time `Q^{|F|}` is doubly exponential in `1/ε`; numerically the records of `a_n` up to
`2·10^7` reach only `0.40·a_1`, at `n = 3100`.

## 5. The unconditional `Ω±(√n)` law and almost periodicity

**Theorem 5.** (a) RH ⟺ `Φ` is Bohr almost periodic (`Φ` is continuous unconditionally).
(b) Unconditionally, there is `η > 0` with `a_n ≤ −η` for infinitely many `n`; together with
Theorem 4(b), the numerator `E(n) = a_n√n` satisfies `E(n) > (a_1 − ε)√n` infinitely often and
`E(n) ≤ −η√n` infinitely often.

*Proof.* (a) Under RH `Φ` is an absolutely convergent exponential series, hence almost periodic;
an almost periodic continuous function is bounded, so Theorem 1 gives the converse. (b) Under RH:
`Φ` has Bohr mean `0` because no zero has ordinate `0` (`ξ(½) ≠ 0`). If `Φ > −η` eventually for
every `η`, then `Φ⁻ = max(−Φ,0)` is almost periodic and tends to `0`, so vanishes identically
(vanishing lemma); thus `Φ ≥ 0` everywhere, and a nonnegative almost periodic function with mean `0`
is `0`, contradicting `Φ(0) = a_1 > 0`. Hence `Φ ≤ −η` at arbitrarily large lags for some `η > 0`,
and Lemma 3.1 transfers this to `a_n ≤ −η/2`. Without RH use the dichotomy. ∎

So the sign of `E(n)` is not sensitive to the zeros; only the size of the positive excursions is,
and its exact ceiling is `a_1√n`.

## 6. The floor is arithmetic

Say the ordinates have **no odd relation** if for every finite set `Γ` of distinct ordinates and
every `c : Γ → ℤ` with `Σ c_γ γ = 0` the sum `Σ c_γ` is even. (Conjugate pairs `γ, −γ` give the
relation `γ + (−γ) = 0` with sum `2`; the condition is equivalent to the same condition on positive
ordinates, and is implied by their linear independence over `ℚ`.)

**Theorem 6 (floor law).** Under RH, `−a_1` is the greatest lower bound of `{a_n : n ≥ 2}` if and
only if the ordinates have no odd relation.

*Proof.* (⟹) Let `Σ_{γ∈Γ} c_γ γ = 0` with `Σ c_γ` odd. Given `ε`, pick `L` with `Φ(L) < −a_1 + ε`.
Since `Φ(L) + a_1 = Σ_ρ w_ρ (1 + cos γ_ρ L)` with positive terms, each `γ ∈ Γ` has
`1 + cos γL < ε(¼+γ²)`, i.e. `‖e^{iγL} + 1‖ < √(2ε(¼+γ²))`. With `u_γ = −e^{iγL}`,
`1 = e^{iL Σ c_γ γ} = Π(−u_γ)^{c_γ} = (−1)^{Σc_γ} Π u_γ^{c_γ} = −Π u_γ^{c_γ}`, so
`‖Π u_γ^{c_γ} − 1‖ = 2`, while for unimodular `u_γ`, `‖Π u_γ^{c_γ} − 1‖ ≤ Σ |c_γ|‖u_γ − 1‖ → 0`
as `ε → 0`. (⟸) Fix `ε`; take `F` with tail weight `< ε/8`, `Γ` its ordinates, and a rationally
independent integral basis `b_1,…,b_k` of the group generated by `Γ`, `b_i = Σ_γ m_{iγ}γ`,
`γ = Σ_i n_{γi} b_i`. Put `θ_i = π Σ_γ m_{iγ}`. For `γ ∈ Γ`, `Σ_i n_{γi}θ_i = πN_γ` where
`γ − Σ_{γ'}(Σ_i n_{γi} m_{iγ'})γ' = 0` is a relation with coefficient sum `1 − N_γ`, even by
hypothesis, so `N_γ` is odd and `Π_i e^{in_{γi}θ_i} = −1`. Kronecker's theorem gives `t` with
`e^{ib_i t}` within `δ` of `e^{iθ_i}` for all `i`, whence `cos γt ≤ −1 + Kδ` on `Γ` with
`K = max_γ Σ_i|n_{γi}|`; for `Kδa_1 ≤ ε/8` this gives `Φ(t) ≤ −a_1 + 3ε/8`. An `ε/8`-almost period
moves `t` beyond `log(N₁+2)`, and Lemma 3.1 gives `a_n < −a_1 + ε` for `n = ⌊e^{t'}⌋`. ∎

Ceiling and floor of the same explicit sequence are thus governed by different mathematics: the
ceiling by nothing (Theorem 4), the floor by the parity of the integer relations among the
ordinates (Theorem 6). Under RH the infimum is never attained at an `n ≥ 2`; whether it equals
`−a_1` is a Diophantine statement, and `inf a_n < 0` in every case (Theorem 5).

## 7. A discrete criterion left open

For a fixed base `b ≥ 2`, is RH equivalent to boundedness above of the single subsequence
`(a_{b^m})_{m≥1}`? The direction ⟹ is Theorem 3. For ⟸ the generating function
`Σ_m a_{b^m}z^m = Σ_ρ w_ρ/(1 − b^{ρ−½}z)` has poles at `b^{½−ρ}`; bounded coefficients force
analyticity in `|z| < 1`, contradicting an off-line pole unless that pole is an accumulation point
of other poles — a sequence of zeros with real parts converging to the supremal abscissa and
`b^{iγ_j} → 1`. The Landau route meets the same configuration. The continuous criterion (Theorem 2)
avoids it because `ξ` has no real zeros. Excluding this `b`-resonance is the open core.

## 8. Numerical illustration (no proof depends on it)

For `n ≤ 2·10^7`: `max a_n = 0.018674` at `n = 3100` (`0.40·a_1`), `min a_n = −0.022681` at
`n = 319439`, no `n` with `a_n > a_1`, record sites `6, 15, 34, 205–208, 3084–3100`; the powers of
two oscillate in sign with `|a_{2^m}| ≤ 0.0173`.

## 9. Relation to the literature

Classical criteria of this type are two-sided and lose a power of a logarithm: RH ⟺
`|ψ(x) − x| ≤ √x log²x/(8π)` for `x ≥ 73.2` (Schoenfeld 1976), or `ψ(x) = x + O(√x log²x)`. The
integer criteria of Robin (1984), Lagarias (2002) and Nicolas concern `σ(n)` and `φ(n)` with the
constant `e^γ`. The kernel `1/(ρ(1−ρ))` makes the zero side absolutely convergent, which is why the
present criterion needs no logarithm, is one-sided (Landau), and has an exact constant equal to
its own value at `n = 1`. The recurrence and floor arguments are Bohr's almost periodicity and
Kronecker's theorem, in the tradition of Ingham's Ω-results and of the linear-independence
hypothesis used by Montgomery and by Rubinstein–Sarnak; the parity characterisation of the floor
appears to be new, as does the unconditional `Ω±` law with the exact positive constant.

## 10. Lean certificate

All theorems are in the `RHTower` namespace of the corpus, wired into the `GaloisForLFunctions.RHTower`
umbrella, and depend only on `propext`, `Classical.choice`, `Quot.sound`.

| Statement | Lean |
|---|---|
| genus-kernel explicit formula | `LagExplicitFormula.lag_explicit_formula` |
| `Φ` real, even, `Φ(0) = a_1`, prime side | `WeilLagFunction.weilLagFunction_eq_prime_side`, `weilLagFunction_zero`, `weilLagFunction_neg` |
| Theorem 1 | `WeilLagFunctionCriterion.riemannHypothesis_iff_weilLagFunction_bounded` |
| Theorem 2 | `WeilLagFunctionOneSided.riemannHypothesis_iff_weilLagFunctionReal_bddAbove`, `…_bddBelow` |
| Lemma 3.1 | `WeilLagFunctionInteger.weilLagFunctionReal_integerLag_interval`, `WeilLagFunctionOmega.abs_weilLagFunctionReal_sub_integerLag_le` |
| Theorem 3 | `WeilLagFunctionInteger.riemannHypothesis_iff_integerLag_le_one`, `…_bddAbove`, `…_bddBelow`, `riemannHypothesis_iff_integerLagInequality`, `integerLag_dichotomy` |
| Theorem 4 | `WeilLagFunctionRecurrence.exists_pow_integerLag_gt_of_riemannHypothesis`, `isLUB_integerLag_tail_of_riemannHypothesis`, `frequently_integerLag_gt`, `integerLag_law` |
| Theorem 5 | `WeilLagFunctionOmega.riemannHypothesis_iff_isBohrAlmostPeriodic_weilLagFunction`, `frequently_integerLag_le_neg`, `genusKernelError_omega_pm` |
| Theorem 6 | `WeilLagFunctionFloor.integerLag_floor_law` (predicate `NoOddRelation`) |

## Addendum: the unconditional frontier (Lean, `WeilLagFunctionFrontier`)

`|Φ(L)| ≤ C e^{L/2} e^{−c L^{1/10}}` and `|a_n| ≤ C √n e^{−c (log n)^{1/10}}` for large `L`, `n`, from the corpus PNT with
error term via `M(x) − log x + γ = E(x)/x − ∫_x^∞ E(t)t^{−2}dt`. RH is exponent `0`; provable is exponent `½`; every
exponent in between is a fixed-width zero-free region. See STATUS MUST-242.

## Addendum: the Gram interface (Lean, `WeilLagFunctionGram`)

RH ⟺ `K(x,y) = Φ(log x − log y)` positive semidefinite on `(ℝ_{>0}, ×)` ⟺ all `(Φ(log(n/m)))_{n,m≤N}` PSD. Under RH the form
is `Σ_ρ w_ρ |Σ c_x x^{iγ}|²`; the converse uses the `2×2` minors on `{1,n}` = `2(a_1 − a_n)`. This is the interface a
geometric producer must fill (STATUS MUST-243).

## Addendum: the carrier form (Lean, `WeilLagFunctionCarrier`)

On functions of the zero copies, `B(f,g) = Σ_ρ f(ρ)g(1−ρ)/(ρ(1−ρ))` and `v_x(ρ) = x^{ρ−½}` give `B(v_x,v_y) = Φ(log x − log y)`
unconditionally; RH ⟺ `B ≥ 0` on the Frobenius orbit. This is the Hodge datum in carrier language (STATUS MUST-243).

## Addendum: dense lag sets (Lean, `WeilLagFunctionDense`)

Continuity of `Φ` + density: RH ⟺ `Φ` bounded above on `{k log p + l log q}` for any two distinct primes (`{p,q}`-rationals).
Single-base, prime, and arithmetic-progression lag sets are discrete: continuity gives nothing; the prime case is not
trivial (prime gaps `p^{0.525}` too large for the interval bound), it needs the Landau route with the prime zeta function.
STATUS MUST-244.

## The prime criterion: exact route and missing bricks (analysis, not built)

**Claim (paper route, not yet Lean):** RH ⟺ `sup_p a_p < ∞` over primes. With `c_p = (M − a_p)(log p)/p ≥ 0` the Laplace
transform of `Σ_p c_p δ_{log p}` is `M·(−ζ'/ζ)(1+s) − Σ_ρ w_ρ (−ζ'/ζ)(s + 3/2 − ρ)` up to prime-power tails analytic for
`Re s > −½`. Its poles are at `s = ρ − ½` (residue `m_ρ w_ρ ≠ 0`, never real, no finite accumulation since zeros are
discrete with ordinates bounded away from `0`), at `s = ρ + ρ'' − 3/2` (real part `≤ 2Θ − 3/2 < Θ − ½`), and at `s = 0`,
`s = ρ' − 1` (real part `< 0`). Hence the abscissa of the nonnegative series is exactly `Θ − ½` (a pole at `ρ − ½` with
`β > max(2Θ−1, Θ−½)` cannot be cancelled), Landau forces a real singularity at `Θ − ½`, and the right side is analytic
there provided `Σ_ρ w_ρ ζ'/ζ(s + 3/2 − ρ)` converges locally uniformly, which needs `|ζ'/ζ(w)| ≪ log|Im w|` on a fixed
half-plane `Re w ≥ Θ' > Θ`. Missing corpus bricks: (i) polynomial growth of `ζ` in a vertical strip through the
critical strip (needs vertical Stirling decay of `Γ` and Phragmén–Lindelöf; Mathlib has `PhragmenLindelof.vertical_strip`,
the corpus has no complex-Gamma vertical decay); (ii) the local zero count `N(t+1) − N(t) ≪ log t` (corpus has Jensen for
`ξ`, `xi_zeroCount_disc_le`, but no polynomial bound for `ξ` on spheres); (iii) the partial-fraction bound for `ζ'/ζ` from
the corpus explicit formula. Dual-use: these are the same bricks any Lean zero-free-region argument beyond PNTPlus needs.
Not started: it is a receiver and a multi-week build.

## Brick built: local zero count (Lean, `ZetaLocalZeroCount`)

`card_le_of_ordinates_in_window : |t| ≥ 4 → (∀ q ∈ F, |Im ρ_q − t| ≤ 1) → F.card ≤ 40 log(180|t|)` for finite sets of
zero copies. Route: Jensen for `ζ` on `closedBall (2+it) 1.85` (outer 1.95), sphere bound from Zeta23's Euler–Maclaurin
at `N = 1`, centre `‖ζ(2+it)‖ ≥ 1/3`, order transfer `ξ = xiUnit · ζ`, reflection for `β < ½`. No Gamma decay, no PL.
Next bricks for the prime criterion: `ζ'/ζ(s) ≪ log|t|/δ` at distance `δ` from all zeros on `½ ≤ Re s ≤ 2` (partial
fractions from `xi_explicitFormula_logDeriv` + this count), then the Landau assembly.

## Brick built: `ζ'/ζ ≪ log t / δ` (Lean, `ZetaLogDerivZeroDistance`)

`norm_logDeriv_zeta_le`: `½ ≤ σ ≤ 2`, `t ≥ 4`, `0 < δ ≤ 1`, all zero copies at distance `≥ δ` ⟹
`‖ζ'/ζ(σ+it)‖ ≤ (3700 + 5K₀) log t/δ`, `K₀ = #{copies with |γ| ≤ 6}`. Anchor `3+it`, windows `k = ⌊|t−γ|⌋`, window count
from `card_le_of_ordinates_in_window` on both sides of `t` (the lower window may dip below height 4: absorbed by `K₀`),
tails `Σ 1/k² ≤ 1`, `Σ log(k+2)/k² ≤ 7`. STATUS MUST-247. Remaining for the prime criterion: the Landau assembly.

## Prime criterion: the Landau assembly has a blind spot at Θ = 1 (analysis, 2026-09-06)

With `Θ := sup β`, the transform `F(s) = Σ_p (M − a_p) log p · p^{−1−s}` (nonnegative coefficients when `a_p ≤ M`)
equals `M P(1+s) − Σ_ρ w_ρ P(s + 3/2 − ρ)` (+ prime-power tails), `P = −ζ'/ζ`, for `Re s > Θ − ½`. The `ρ`-term has
its pole at `s = ρ − ½` (from the pole of `ζ` at `1`) and singularities at `s = ρ + ρ' − 3/2` (zeros of `ζ`), real
part `≤ 2Θ − 3/2`; the sum over `ρ` converges locally uniformly only on `Re s > 2Θ − 3/2` (needs MUST-247). The pole
of the zero `ρ₀` is visible iff `β₀ − ½ > 2Θ − 3/2`, i.e. `β₀ > 2Θ − 1`: such zeros exist iff `Θ < 1`. Hence the
Landau argument (corpus `landau_local_summability_transfer` on the Dirichlet series over primes) gives exactly:
**`sup_p a_p < ∞ ⟹ RH ∨ Θ = 1`**, i.e. `RH ⟺ (sup_p a_p < ∞ ∧ Θ < 1)`. The blind spot is intrinsic to prime-only
data: any prime-restricted transform of `Σ_ρ w_ρ p^{ρ−½}` is a `ρ`-sum of prime series at shift `ρ`, whose
singularities sit at `ρ + ρ'`. Not built in Lean (a receiver with a known hole; the two-prime criterion MUST-244 is
unconditional). Real poles at `2β − 3/2` with residue `2m Re w_ρ > 0` are a side remark.

## Correction and upgrade (2026-09-06): prime lags decide a zero-free strip; the Θ = 1 blind spot is gone

Earlier notes said the interval route fails for primes because prime gaps `p^{0.525}` exceed `√p`. That is true for
RH but not for strips: over a gap `g` the lag function moves by `≤ 11(g+1)(log 2n+2)²/√n` (Lean `abs_integerLag_sub_le`,
`abs_weilLagFunctionReal_sub_integerLag_le_of_gap`), so with the corpus Hoheisel exponent `71/100`, `a_p ≤ M` on primes
gives `Φ(L) ≤ M + C e^{0.23 L}`, and the growth criterion (`re_le_half_add_of_weilLagFunctionReal_le_exp`) gives
`Re ρ ≤ 3/4` for all zeros (`re_le_three_quarters_of_primeLag_le`). Hence in the Landau route above, `Θ ≤ 3/4 < 1`:
every off-line pole `ρ₀ − ½` is visible (`β₀ > 2Θ − 1` holds since `2Θ − 1 ≤ ½ < β₀`), `G` is meromorphic on
`Re s > 2Θ − 3/2 ≥ ... ≤ 0`, and the assembly would close **`RH ⟺ sup_p a_p < ∞`** (prime powers first, avoiding the
tail `T(w)`; primes with the tail). Bricks: MUST-246/247, corpus `landau_local_summability_transfer`,
`LSeries_vonMangoldt_eq_deriv_riemannZeta_div`, summability of `Σ_q |w_q| log(2+|γ_q|)` (dyadic windows via
MUST-246), residue of `−ζ'/ζ` at `1`, a convex-tube identity-theorem step as in `WeilLagFunctionShadow`.

## The prime-power criterion is closed (Lean, 2026-09-06): `RH ⟺ sup_{p^k} a_{p^k} < ∞`

`PrimeLagLandauCriterion.riemannHypothesis_iff_primePowerLag_bddAbove`. The assembly follows the route above with
`Θ ≤ 3/4` from MUST-250: nonnegative series `Σ (M − a_n)Λ(n)n^{−1−s}` = `M(−ζ'/ζ)(1+s) − Σ_ρ w_ρ(−ζ'/ζ)(s+3/2−ρ)` on
`Re s > Θ−½`; analytic continuation of the right side to the box `Θ−½−η < Re s < ¾`, `|Im s| < 3η` (η below a sixth of
the least `|γ|`, so no near pole meets the box); `landau_local_summability_transfer` moves the abscissa to
`Θ−½−η/4`; a maximal zero `ρ₀` on its horizontal line with `Re ρ₀ > Θ−η/8` has a ray `ρ₀−½+t` on which the right side
is `≥ ‖W₀‖/t − C`; the real-analytic identity theorem along the ray meets the continuity of the series at `ρ₀−½`.
STATUS MUST-251. What is not yet done: primes only (subtract the `k ≥ 2` part, analytic on `Re s > Θ−1`); a
quantitative Ω-rate at prime powers under `¬RH` (the argument gives unboundedness, not `Ω(n^{Θ−½−ε})` along prime
powers — that would need a Landau–Ingham oscillation theorem at prime powers rather than a summability transfer).
What this settles: the RH content of the lag sequence sits entirely in its prime-power values; the sequence
`a_{p^k}` is the one-sided observable, and the Landau argument is the only tool used beyond MUST-246/247.

## The `k`-th power criterion and the counting-function law (Lean, 2026-09-06)

`riemannHypothesis_iff_powLag_bddAbove`: for every `k ≥ 1`, `RH ⟺ sup_m a_{m^k} < ∞`. The proof is the Landau
assembly with `ζ(kw)` in place of `−ζ'/ζ`: series `Σ (M − a_{m^k}) m^{−k−u} = M ζ(k+u) − Σ_ρ w_ρ ζ(u + 3k/2 − kρ)`,
poles at `kρ − 3k/2 + 1` (imaginary part `kγ ≠ 0`), far terms by the exponent-½ vertical bound and
`Σ |w_ρ| √(2+|γ|) < ∞`, residue `‖ζ(1+t)‖ ≥ 1/(2t)`. STATUS MUST-252. The structural lesson: the gap law of
MUST-250 (gaps `≤ n^θ` decide `Re ρ ≤ θ`) is only what the Lipschitz route sees; the Landau route sees the analytic
continuation of the counting series `F_N` of the subsequence, and decides RH whenever `F_N` continues past its
abscissa with real poles only and sub-linear vertical growth. Bases fail exactly because `1/(1 − b^{−w})` has the
non-real poles `2πij/log b` on its abscissa (the shadow law). Open: (a) the general statement with an abstract `F_N`
(a `Prop` interface: meromorphic continuation, real poles, growth exponent `< 1`); (b) Beatty-type and other sparse
sets whose counting series is known; (c) a producer remains absent — the criteria certify that these subsequences see
every off-line zero, nothing more.

## The counting-function law as a theorem (Lean, 2026-09-06)

`LagWeightSystem.riemannHypothesis_iff_lag_bddAbove` (STATUS MUST-253): the abstract form of MUST-251/252 with the
generating function `F` of the weight as data and four hypotheses (series identity right of `α`, differentiability
right of `α`, continuation with growth exponent `A < 1` on `α − η₀ ≤ Re w ≤ α + 2` away from the real axis,
`‖F(α + t)‖ → ∞`). Only the last two carry arithmetic content. Next instance to build: `c = 1_{primes}`, `F = P`
(prime zeta), which needs a bound `|log ζ(w)| ≪ log|Im w|` on `Re w ≥ 1 − η₀`, `|Im w| ≥ g`, under `Θ ≤ ¾`
(MUST-250 supplies `Θ ≤ ¾` from the same hypothesis `a_p ≤ M`); the `j ≥ 2` terms of `P(w) = Σ μ(j)/j · log ζ(jw)`
are bounded. Outcome would be `RH ⟺ sup_p a_p < ∞` with no prime powers.

## Primes only (Lean, 2026-09-06): `RH ⟺ sup_p a_p < ∞`, sharp constant `a_1`

`PrimeLagLandauPrimesOnly.riemannHypothesis_iff_primeLag_le_sharp`. No prime-zeta continuation was needed: the proper
prime powers contribute a Dirichlet series analytic on `Re s > Θ − 1`, subtracted from the prime-power continuation.
STATUS MUST-254. The lag route's sampling question is now completely answered: primes, prime powers, `k`-th powers,
all integers, and every weight covered by the counting-function law are RH-complete; bases are shadowed.

## Two-sided prime sampling is not configuration-free (analysis, 2026-09-06)

The one-sided criteria (MUST-251–254) are Bohr–Landau theorems: the contradiction comes from the pole `α + ρ₀ − ½`
of `Σ_ρ w_ρ F(s − ρ + ½)`, which no other zero can share, with residue of positive real part. The mean-square prime
criterion `Σ_{p≤x} (a_1 − a_p)² log p / p ≪ x^ε ⟹ RH` (Cramér-type; its continuous version `∫ Φ(L)² e^{−2aL} dL < ∞
∀ a > 0 ⟹ RH` is a Plancherel statement and configuration-free) goes through the double sum
`Σ_{ρ,ρ'} w_ρ w_ρ' (−ζ'/ζ)(s + 2 − ρ − ρ')`, whose poles `ρ + ρ' − 1` are shared by every pair with the same sum.
Landau plus the box argument give exactly: if the prime mean-square series converges at some `σ₁ < 2Θ − 1`, then
`Σ_{ρ+ρ'=z} w_ρ w_ρ' = 0` for every `z` with `Re z > σ₁ + 1` (all residues cancel), in particular at `z = 2ρ₀` for
a zero of maximal real part. When `Θ` is attained by a single conjugate pair the residue `w₀² ≠ 0` cannot cancel and
the criterion holds; in general it depends on additive coincidences `ρ + ρ' = ρ'' + ρ'''` in the zero set (sumset
structure), which no positivity argument controls. Verdict: the two-sided prime criterion is a conditional receiver
(additive genericity of the top zeros); not pursued further.

## Growth exponent at the primes (Lean, 2026-09-06)

`PrimeLagGrowthExponent.exists_prime_gt_primeLag_gt_rpow_of_not_rh`: under `¬RH`, `a_p > M + p^a` for infinitely many
primes, for every `a < Θ − ½`; with `|a_p| ≤ W p^{Θ−½}` the one-sided growth exponent along primes is exactly `Θ − ½`.
STATUS MUST-255. This quantifies MUST-254 and is the sampled-at-primes analogue of the classical Ω-results for
`ψ(x) − x`; the mechanism is unchanged (power ceiling absorbed into `−ζ'/ζ(1 + s − a)`).

## Direct source attempts on the ceiling `F(x) ≤ c√x` (paper, 2026-09-07, both failed)

Notation: `c = 2 + γ − log 4π`, `F(x) = √x Φ(log x) = x m(x) + (x − ψ(x)) − log 2π + τ(x)`,
`m(x) = Σ_{n≤x} Λ(n)/n − log x + γ`, `F' = m` a.e., `F'' + 1/x = Σ_n (Λ(n)/n) δ_n ≥ 0`.

**Attempt A: Selberg-symmetry bootstrap.** Multiplying the Mellin identity `ζ · F̂ = R̂` (`R` elementary) through
by `ζ'/ζ` gives the exact identity `F(x) log x + Σ_{n≤x} Λ(n) F(x/n) = (μ ∗ S)(x) =: T(x)` with `S` elementary,
`T̂ = −F̂' − (ζ'/ζ) F̂`. Since `F = o(x)`, `F̂` is analytic at `s = 1`, so `T(x) ∼ K x` with
`K = F̂(1) = ∫_1^∞ F(x) x^{−2} dx = Σ_ρ w_ρ/(1−ρ) = ½ Σ_ρ (ρ(1−ρ))^{−2} > 0`
(the ρ ↔ 1−ρ symmetry averages `1/(1−ρ)` and `1/ρ`). The elementary-PNT bootstrap
(lower ceiling `F ≥ −c√y` on `y < x` fed into the sieve term, `Σ_{n≤x} Λ(n)√(x/n) ≈ 2x`) yields only
`F(x) log x ≤ (K + 2c) x + o(x)`: the two main terms carry the same sign and no cancellation to scale `√x` is
available. Selberg's method gains one logarithm over its input precision `O(x)`; the ceiling needs `√x`.
Verdict: FAILED, mechanism exhausted. Side product (not formalized, not RH-bearing): the second-genus identity
`2γ₁ + γ² + 1 + γ − log 2π + Σ_{k≥1} 1/(2k(2k+1)²) = ½ Σ_ρ (ρ(1−ρ))^{−2} ≈ 4·10^{−5}`
(numerically consistent: `0.18755 + 1.57722 − 1.83788 + 0.0732 ≈ 1·10^{−4}` against `½ Σ_γ (¼+γ²)^{−2} ≈ 4·10^{−5}`).

**Attempt B: gap concavity.** `G = F − c√x` has `G'' = −1/x + c/(4x^{3/2}) < 0` on every prime-power gap, so on
each gap the ceiling holds iff it holds at the endpoints and at the unique turning point `x*` with
`m(x*) = c/(2√x*)`, where `a_{x*} = 2√x* m(x*)`. Hence the real-`x` ceiling is equivalent to the integer ceiling
plus `√x* m(x*) ≤ c/2` at turning points — weaker than the already-formal integer ceiling (`RH ⟺ a_n ≤ a_1`).
Verdict: FAILED (reduction only, no source input).

**Attempt C (not pursued): Möbius/divisor renewal for `F`.** `Σ_{k≤X} F(X/k)` is elementary
(`X[2Σ_{m≤X} log m/m − H_X(log X − γ)] + X H_X − log⌊X⌋! − ⌊X⌋ log 2π + Σ_k τ(X/k)`), so
`F = μ ∗ (elementary)`; the absolute inverse is `≍ X` because `|F(y)|` is bounded away from zero on most of
`[1,2)` (`F(1) = c > 0`, `F(2) ≈ −0.0246 < 0`), exactly the obstruction recorded for `D(X)` on the
`weil-pole-direct-sign-attack` card. Not repeated.

Hard obligation unchanged: a source-derived one-sided bound on `∫_1^x m(t) dt` at scale `√x`.

**Attempt D (2026-09-07): zero-side product positivity.** `Ξ(t) = ξ(½+it)` is real, and in the Hadamard
product each off-line quadruple contributes the non-vanishing factor `|1 − t²/z²|² = [(t² − (γ² − a²))² + 4γ²a²]/|z|⁴`
(`z = γ − ia`), so all sign changes of `Ξ` are on-line zeros and all off-line information sits in `log|Ξ|`.
Every global identity for `log|Ξ|` against a kernel is Jensen/Littlewood, i.e. the `(L)` first moment
`Σ_{γ≤T} (β − ½)_+`, whose unconditional ceiling is `O(T)` (Selberg density) and whose vanishing `o(T)` is
itself open (it is "almost all zeros within `o(1/log T)` of the line"). Verdict: FAILED — reduces to the
`(L)` receiver; no new mechanism.
