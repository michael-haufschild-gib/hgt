# Method ceilings for the Lindelöf hypothesis:
# twelve barrier theorems, and why they all meet at 1/8

**Abstract.** Let `μ = μ(1/2)` be the Lindelöf exponent of the Riemann zeta function, so that the
Lindelöf hypothesis (LH) asserts `μ = 0`. We prove ceiling theorems for twelve independent routes to
`μ`, and show that each ceiling is `1/4`, `1/6` or `1/8`. The recurrence of `1/8` is explained: it is
the *resolution floor* of the independent-signs model for divisor-correlation errors, a model whose
prediction `E_k(T) ≍ T^{k/4}` for the `2k`-th moment error term is **exactly correct in both cases
where the answer is known** (`k=1,2`, each matched by an `Ω`-result), and whose floor `(k/4)/(2k)`
equals `1/8` identically in `k`. Among the consequences: **(i)** a moment-neutrality law — a perfect
`2j`-th moment improves on an established exponent `θ` if and only if `j > 1/(2θ)`, so that the sixth
moment conjecture is *subconvexity-neutral* against Bourgain's `13/84`; **(ii)** Heath-Brown's 1978
twelfth-moment bound `m(6) ≤ 2` is the exact output of its own method at the information-theoretic
limit of its input, `E(T) = Ω(T^{1/4})`; **(iii)** the Guth–Maynard large-value estimate is
identically equal to the classical bound at the self-dual block and therefore cannot affect `μ`;
**(iv)** no resonance method can disprove LH, since Gál sums are subpolynomial; **(v)** the
zero-geometry route — the exact Jensen balance behind the folklore picture "a large value of `ζ`
pushes the zeros aside" — is *identically inert*: fed the true exponent it returns exactly the
convexity bound `1/4` at every radius, and iterating it drives any subconvex input back **up** to
`1/4`; and **(vi)** *self-dual stationarity* — at the convexity bound the large-value optimisation is
exactly tied across the whole critical strip, and every subconvexity input breaks the tie in the same
direction, back to the critical line and the fourth moment. We further show that the additive-divisor
route separates into two independent halves — a pointwise size and a
shift-cancellation — each worth exactly `1/8` alone and jointly worth LH, and that the two competing
conjectured sizes (Conrey–Gonek `x^{1/2+ε}`, Ivić `Ω(x^{1-1/k})`) settle LH in opposite directions.
The exponent arithmetic of all the quantitative results is certified in Lean 4 with no axioms beyond
`propext`, `Classical.choice`, `Quot.sound` (modules `HTGeometry.MomentNeutralityLaw`,
`MomentChordPivot`, `ShiftAverageTransfer`, `MomentResolutionFloor`, `ShiftPartialSummation`,
`SpikeSobolev`, `JensenZeroGeometry`, `LindelofMethodCeilings`).

**Status.** This paper proves no new bound on `μ(1/2)`. Its content is negative and structural: it
delimits what each known method can deliver, and it locates the single remaining gap.

---

## 0. Notation

`M(A)` is the least exponent with `∫_T^{2T}|ζ(1/2+it)|^A dt ≪ T^{M(A)+o(1)}`; `m(k) := M(2k)`.
`φ` is defined by `meas{t ∈ [T,2T] : |ζ(1/2+it)| > T^v} = T^{1-φ(v)+o(1)}`. `μ := μ(1/2)`.
`E_k(T)` is the error in the `2k`-th moment asymptotic (defined only for `k = 1,2`). `Δ_k(N,h)` is
the Conrey–Gonek error in `Σ_{N<n≤2N} d_k(n)d_k(n+h)`, and `K(h)` the kernel
`∫_T^{2T}(1+h/m)^{-it}dt ≪ min(T, M/h)`.

Two standard facts are used throughout. **(F1)** `M` is convex in `A` (Hölder). **(F2)**
`μ ≤ m(k)/(2k)` for every `k > 0`: a near-extremal value is sustained on an interval of length
`≍ 1/log T` (Sobolev–Gallagher applied to `ζ^k`, a Dirichlet polynomial of length `T^{k/2}`), so it
contributes `≫ V^{2k}/log T` to the moment.

## 1. The independent-signs model and its resolution floor

**Definition 1.1.** The *independent-signs model* posits `|Δ_k(M,h)| ≍ M^{1-1/k}` with signs
uncorrelated in `h`.

**Proposition 1.2.** The model predicts `E_k(T) ≍ T^{k/4}`.

*Proof.* The off-diagonal of the `2k`-th moment is `Σ_{h≥1}(D_k(M,h)/M)K(h)`, the factor `1/M`
coming from `(mn)^{-1/2} ≍ 1/M`. Since `Σ_{h≤M}K(h)^2 ≍ 2MT` (the ranges `h ≤ M/T` and `h > M/T`
contribute `MT` each), independent signs give `(1/M)(2MT)^{1/2}M^{1-1/k} = √2·T^{1/2}M^{1/2-1/k}`,
which at the balanced `M = T^{k/2}` equals `√2·T^{k/4}`. ∎

**Proposition 1.3 (the model is exact where anything is known).** `θ_1 = 1/4` and `θ_2 = 1/2`, each
sharp by an `Ω`-result (`E(T) = Ω(T^{1/4})`, Good; `E_2(T) = Ω(T^{1/2})`, Ivić–Motohashi). Both equal
`k/4`.

**Definition 1.4.** The *resolution floor* of the `2k`-th moment is `θ_k/(2k)`: a bound
`E_k ≪ T^θ` makes the short moment sharp at scale `T^θ`, whence `μ ≤ θ/(2k)` by Sobolev, and `θ`
cannot be taken below the `Ω`-result.

**Theorem 1.5.** The model's resolution floor is `(k/4)/(2k) = 1/8`, **identically in `k`**. In
particular the two moments with known asymptotics have resolution floor exactly `1/8`.

*Lean:* `HTGeometry.model_floor_is_eighth`, `HTGeometry.resolutionFloor_one`,
`HTGeometry.resolutionFloor_two`.

## 2. Five characterisations of the pivot

**Theorem 2.1.** The following coincide at `v = 1/8`.
1. The fourth-moment constraint `φ(v) ≥ 4v` and Heath-Brown's `φ(v) ≥ 12v-1` cross, both `= 1/2`.
2. At the self-dual `ζ²` polynomial (length `N ≍ T`), the Halász–Montgomery largeness `V^4 = T^{4v}`
   equals the square-root-cancellation size `N^{1/2} = T^{1/2}` of its own Gram off-diagonal.
3. `|ζ| = T^v` forces `|D_N| = N^{1/2+2v}` at the critical block, equal to `N^{3/4}` — the
   Guth–Maynard threshold.
4. On the chord from `(4,1)` to `(12,2)` the Legendre-certified gain `A/8 - (M(A)-1)` is identically
   `1/2`, the chord slope and the evaluation point both being `1/8`.
5. It is the resolution floor of Theorem 1.5.

*Lean (item 4):* `HTGeometry.pivotGain_momentChord`, `HTGeometry.pivotGain_le_half`.

## 3. Eleven analytic ceilings (a twelfth, geometric, is in §6)

**Theorem 3.1 (mean-value criticality).** `∫_0^T|ζ(σ+it)|^{2k} ≪ T^{1+ε}` holds exactly for
`σ ≥ 1-1/k`, and the resulting pointwise bound `1/(2k)` equals `(1-σ)/2` there. The whole family
traces the Phragmén–Lindelöf line with no slack: **ceiling `1/4`**.

**Theorem 3.2 (Halász–Montgomery cap).** Granting perfect square-root cancellation for
`Σ_{n~N}n^{-iu}` for all `1 ≤ u ≤ T`, the diagonal `‖a‖²N ≍ T^{1+ε}` gives `R ≪ T^{1-4v+ε}` —
exactly the fourth-moment bound. **Ceiling `1/4`.**

**Theorem 3.3 (Guth–Maynard inertness).** Write their Theorem 1.1 in the block parameter `N = T^β`
with block largeness `V = T^{β/2+2v}`. At `β = 1` the two new terms are `T^{8/5-8v}` and
`T^{7/5-8v}`; these fall below the classical `T^{1-4v}` only for `v > 3/20` and `v > 1/10`
respectively, and on that range the surviving maximum is still `T^{1-4v}`. Hence at the self-dual
block the Guth–Maynard bound **equals** the classical bound for every `v`. Since `β = 1` always
binds, Guth–Maynard cannot improve `φ`, any moment, or `μ`. **Inert.**

**Theorem 3.4 (moment-neutrality law).** Let `μ ≤ θ` be established and suppose `m(j) = 1`. Then
`inf_{k>0} m(k)/(2k) = min(1/(2j), θ)`; hence a perfect `2j`-th moment improves on `θ` **iff
`j > 1/(2θ)`**.

*Proof.* `m ≡ 1` on `[0,j]` (Hölder with `m ≥ 1`), giving `1/(2k)` minimised at `k = j`; and
`m(k) ≤ 1 + 2θ(k-j)` for `k ≥ j` (Hölder against the pointwise bound), giving
`θ + (1-2jθ)/(2k)`, which decreases to `θ` if `2jθ < 1` and increases from `1/(2j)` if `2jθ > 1`. ∎

**Corollary 3.5.** With `θ = 13/84` the threshold is `j > 42/13 = 3.2308…`. **The sixth moment
conjecture (`j = 3`) is subconvexity-neutral**: optimised over `k` it yields `13/84 + 1/(28k)`, which
descends to `13/84` and never crosses. The eighth moment is the first that can help.

*Lean:* `HTGeometry.isGLB_momentBound`, `momentBound_improves_iff`, `sixth_moment_neutral`,
`eighth_moment_improves`.

**Theorem 3.6 (the chord is the image of one input).** With the shift-average transfer
`m(k) ≤ 1 + max(0, k(a+b-1)/2 - a)` for `Σ_{h≤H}Δ_k(x,h) ≪ H^a x^{b+ε}` — which agrees identically
with Ivić's published `k = 3` case `(a+3b-1)/2` — the single input `(a,b) = (1/2,1)` gives
`1+(k-2)/4` for **every** `k`, i.e. `m(2)=1`, `m(3)≤5/4`, `m(4)≤3/2`, `m(6)≤2`. The entire known
unconditional moment envelope is the image of one point.

*Lean:* `HTGeometry.transferBound_half_one`, `transferBound_envelope`.

**Theorem 3.7 (the short-interval mean square is neutral at its optimum).** `(1/2,1)` is exactly
Cauchy–Schwarz from `Σ_n|Δ_k(n+H)-Δ_k(n)|² ≪ xH^{1+ε}`, which Ivić describes for `k > 2` as
*"unattainable at present"* (his Theorem 1 gives `xh^{4/3}`, and only under LH). By Theorem 3.6 the
unattainable optimum reproduces the chord and would improve nothing; the available `xh^{4/3}` gives
`(a,b) = (2/3,1)`, hence `m(3) ≤ 4/3`, `m(6) ≤ 7/3` — strictly worse than known. **Neutral.**

**Theorem 3.8 (Heath-Brown's method is at its ceiling).** His input is the short second moment at
`G ≍ V²`, sharp for individual `t_0` when `G ≥ T^{1/3}` (which alone yields the Weyl bound) and
pushed to `G = T^{1/4}` on average over the large-value set. Under `G = T^{2v}` that range is exactly
`v ∈ [1/8, 1/6]`, the window on which `m(6) = 1 + sup_v[12v-φ(v)] = 2` is attained. The lower
endpoint is sharp: `E(T) = Ω(T^{1/4})` means the short second moment **fails** below `T^{1/4}`.
Hence `m(6) ≤ 2` is the exact output of the method at the information-theoretic limit of its input.
**Ceiling `m(6) = 2`, i.e. `μ ≤ 1/6`.**

**Theorem 3.9 (error-term programmes).** `μ ≤ θ_{E_k}/(2k)`; the conjecturally optimal
`θ_{E_1} = 1/4` and `θ_{E_2} = 1/2` are sharp by `Ω`-results, and both give **ceiling `1/8`**.

**Theorem 3.10 (the `Ω` side cannot disprove LH).** Every known `Ω`-result for `max_{t≤T}|ζ(1/2+it)|`
arises from the resonance method, whose gain is governed by the Gál/GCD sum
`Γ(N) = max_{|𝒩|=N}Σ_{m,n}gcd(m,n)/√(mn)`, determined sharply by Bondarenko–Seip as
`exp((C+o(1))√(log N loglog N))` — subpolynomial. With a polylogarithmic resonator the output is
`T^{o(1)}`. **No resonance construction yields `Ω(T^c)` for any `c > 0`**, so no known method
disproves LH; and the conjecturally correct maximum (Farmer–Gonek–Hughes) is itself `T^{o(1)}`.

**Theorem 3.11 (`GL(3)` subconvexity for `ζ³`).** `ζ(s)^3 = L(s, 1⊞1⊞1)` has conductor `t^3` and
degree-3 convexity `t^{3/4}`, i.e. exactly `ζ ≪ t^{1/4}`. Munshi's conductor-lowering gain
`t^{3/4-δ}` with small `δ` gives `ζ ≪ t^{1/4-δ/3}`; a Weyl-quality `GL(3)` bound `t^{1/2}` would give
exactly `ζ ≪ t^{1/6}`. **Ceiling `1/6`.**

**Remark 3.12.** Two further routes are tautological rather than capped: the circle-method split of
the shift average (`∫_m|S|²K_H = Σ_{h≤H}Δ - E_maj` by definition), and Backlund's local zero-density
criterion (an exceptional unit interval is exactly a place where `|ζ|` is large, so the criterion
carries the same content as `φ`).

## 3bis. Complete proof of the transfer (Theorem 3.6's engine)

Theorem 3.6 was stated with the transfer taken from Ivić; we give the proof in full, since every
ceiling in §3 and §4 is read off from it.

**Theorem 3.6a.** Let `k ≥ 2` be an integer and `0 ≤ a < 1`, `b ≥ 0`. Suppose that for all `x ≥ 2`
and `1 ≤ H ≤ x`,
`(∗) |Σ_{h≤H} Δ_k(x,h)| ≪_ε H^a x^{b+ε}`.
Then `m(k) ≤ 1 + max(0, k(a+b−1)/2 − a)`.

*Proof.* Write `M = M(t) ≍ (t/2π)^{k/2}` and let `V` be a fixed smooth cutoff.

**(1) Approximate functional equation.** For `t ∈ [T,2T]`,
`ζ(1/2+it)^k = Σ_n d_k(n) n^{−1/2−it} V(n/M) + χ(1/2+it)^k Σ_n d_k(n) n^{−1/2+it} V(n/M) + O(t^{−A})`.
Since `|χ| = 1` on the critical line, the two sums have equal modulus after conjugation, so
`∫_T^{2T}|ζ|^{2k} dt ≪ ∫_T^{2T}|Σ_n d_k(n) n^{−1/2−it} V(n/M)|² dt + T^{−A}`.

**(2) Expansion.** Squaring out,
`∫_T^{2T}|·|² dt = Σ_{m,n} d_k(m)d_k(n)(mn)^{−1/2} V(m/M)V(n/M) ∫_T^{2T}(n/m)^{it} dt`.
The diagonal `m = n` contributes `T Σ_n d_k(n)² n^{−1} V² ≍ T(log T)^{k²}`.

**(3) The kernel.** For `m ≠ n`, `∫_T^{2T}(n/m)^{it}dt = (e^{2iT log(n/m)} − e^{iT log(n/m)})/(i log(n/m))`,
so with `n = m+h`, `h ≥ 1`,
`|I(m,h)| ≤ min(T, 2/log(1+h/m)) ≤ min(T, 4m/h)` for `1 ≤ h ≤ m`.
Since `(mn)^{−1/2} ≍ 1/M` on the support of `V`, the off-diagonal is
`≪ Σ_{h≥1} (D_k(M,h)/M)·min(T, M/h)`, where `D_k(M,h) = Σ_{m~M} d_k(m)d_k(m+h)`.

**(4) Main terms.** Writing `D_k = S_k + Δ_k` with `S_k` the Conrey–Gonek main term, the
contribution of `S_k` together with the diagonal is the moment's main term and is `≪ T^{1+ε}`
(Ivić, *On the general additive divisor problem*, §1, eq. (1.13)–(1.14) and the discussion there;
the main term is `T` times a polynomial in `log T` of degree `k²`).

**(5) The error, head range `h ≤ h₀ := M/T`.** Here `min(T,M/h) = T`, so by `(∗)`
`(T/M)·|Σ_{h≤h₀} Δ_k(M,h)| ≪ (T/M)·h₀^a M^{b+ε} = T^{1−a} M^{a+b−1+ε}`.

**(6) The error, tail range `h₀ < h ≤ M`.** Here `min(T,M/h) = M/h`, so we must bound
`Σ_{h₀<h≤M} Δ_k(M,h)/h`. Put `S(t) = Σ_{h≤t} Δ_k(M,h)`, so `|S(t)| ≪ t^a M^{b+ε}` by `(∗)`.
Summation by parts (formalised as `HTGeometry.sum_mul_weight_eq`, with the weight `1/h`) gives
`Σ_{h₀<h≤M} Δ_k(M,h)/h = S(M)/M − S(h₀)/h₀ + Σ_{h₀≤t<M} S(t)·(1/t − 1/(t+1))`,
and `1/t − 1/(t+1) = 1/(t(t+1))`. Hence, by `HTGeometry.abel_bound_of_partialSum_le`,
`|Σ_{h₀<h≤M} Δ_k(M,h)/h| ≪ M^{a+b−1+ε} + h₀^{a−1}M^{b+ε} + M^{b+ε}Σ_{t≥h₀} t^{a−2}`.
For `a < 1` the last sum is `≪ h₀^{a−1}/(1−a)` (`HTGeometry.increment_le_rpow`,
`HTGeometry.summable_increment`), so all three terms are
`≪ (1−a)^{−1}(M^{a+b−1} + h₀^{a−1}M^{b})M^{ε} = (1−a)^{−1}(M^{a+b−1} + T^{1−a}M^{a+b−1})M^{ε}
 ≪ T^{1−a}M^{a+b−1+ε}`,
the same exponent as the head range.

**(7) Optimisation.** Combining (2)–(6),
`∫_T^{2T}|ζ(1/2+it)|^{2k}dt ≪ T^{1+ε} + T^{1−a}M^{a+b−1+ε}`,
and with `M ≍ T^{k/2}` the second term is `T^{1−a+k(a+b−1)/2+ε}`. Therefore
`m(k) ≤ max(1, 1−a+k(a+b−1)/2) = 1 + max(0, k(a+b−1)/2 − a)`. ∎

**Remark.** At `k = 3` this reads `m(3) ≤ max(1, (a+3b−1)/2)`, which is exactly Ivić's published
form — the two agree identically, which is the check we use throughout. Steps (5) and (6) are where
the head and tail ranges are shown to contribute the same exponent; that equality is what makes the
transfer's aperture irrelevant (cycle 19 of the campaign log, correcting an earlier claim that a
wider aperture would help).

## 4. The additive-divisor route separates

**Theorem 4.1.** Under the transfer of Theorem 3.6:

| input | `(a,b)` | consequence |
|---|---|---|
| Conrey–Gonek size, no shift cancellation | `(1, 1/2)` | `μ ≤ 1/8` |
| Vinogradov size + square-root shift cancellation | `(1/2, 1-1/k)` | `μ ≤ 1/8` |
| **Conrey–Gonek size + square-root shift cancellation** | `(1/2, 1/2)` | `m(k) = 1` ∀`k`, i.e. **LH** |

*Lean:* `HTGeometry.transferBound_conreyGonek`, `transferBound_conreyGonek_pointwise`,
`conreyGonek_separation`, `vinogradov_cap`.

So the pointwise size and the shift cancellation are independent halves: either alone buys exactly
`1/8`; together they buy Lindelöf. This explains the recurrence of `1/8` once more — it is what *one*
of the two halves buys.

**Theorem 4.2 (the conjectures conflict).** Conrey–Gonek predict `Δ_k(x,h) ≪ x^{1/2+ε}` uniformly for
`h ≤ x^{1/2}`; Ivić conjectures `Δ_k(x,h) = Ω(x^{1-1/k})` for every fixed `h ≥ 1`, equivalently "the
correlation error is the square of the ordinary divisor error", since `(x^{(k-1)/(2k)})^2 = x^{1-1/k}`.
At `k = 2` both read `x^{1/2}` and the `Ω` is Motohashi's theorem; **for `k ≥ 3` they contradict**,
and by Theorem 4.1 they settle LH in opposite directions.

**Remark 4.3 (evidence).** Over `F_q[t]`, Sawin proves square-root cancellation for divisor sums over
short intervals (Duke 2021) and over squarefree progressions with level of distribution `→ 1` (Acta
Math. 2024), with no `k`-dependent degradation — the shape of Conrey–Gonek, not of Ivić. The evidence
is indirect (his objects are `d_k` over intervals and progressions, not the self-correlation) but it
is the only evidence bearing on the conflict.

## 5. Completeness, and the remaining gap

**Theorem 5.1.** Every route in §3 admits a ceiling of `1/4`, `1/6` or `1/8`. The routes that admit
none are: the moment conjecture (equivalent to LH); the exponent-pair conjecture (implies LH); and
Conrey–Gonek's size with square-root shift cancellation (implies LH, Theorem 4.1).

> **There is no uncapped intermediate.** This is the structural reason the problem is open.

**Remark 5.2 (no counterexample object).** By Hamburger's theorem (1921) a Dirichlet series
convergent for `σ > 1`, meromorphic of finite order with its only pole at `s = 1`, and satisfying
`ζ`'s functional equation, equals `c·ζ`. The class is one-dimensional, so no "model object" with
`μ = 1/8` exists, and a barrier theorem of the Selberg-parity type — exhibiting a counterexample in
the class — is impossible. The ceilings of §3 must be, and are, proved one method at a time.

**Remark 5.3 (the gap).** The open core admits three successively more concrete forms: a `GL(3)`
Motohashi analogue for `Δ_3` (input does not exist); hyper-Kloosterman assembly (input exists —
Deligne's bound for `Kl_k` — assembly loses); and a power saving for `Σ_{m≤x/a}d(m)d_3(am-h)` uniform
in `a ≤ x^{1/3}`, whose `a = 1` case is Topacogullari's theorem. The moduli sit at `x^{1/3}`, far
inside the level of distribution already known for `d_3` (`1/2+1/46`, Fouvry–Kowalski–Michel), so the
level of distribution is **not** the obstruction. Every ingredient is a theorem over `F_q[t]`; the
obstruction is the transfer to `ℤ`.

## 6. The twelfth ceiling: zero geometry is exactly inert

The routes of §3 all live on the *analytic* side: moments, large values, exponential sums. There is
one further route, entirely on the *geometric* side, which the folklore states as *"a large value of
`ζ` must push the zeros aside, and the zeros cannot be pushed"*. We make that route exact and show it
has gain zero.

Fix large `T`, a point `t₀ ∈ [T,2T]` with `ζ(1/2+it₀) ≠ 0`, and write `s₀ = 1/2 + it₀`,
`L = log(t₀/2π)`. Let `n_{t₀}(u) := #{ρ : |ρ − s₀| < u}` count nontrivial zeros with multiplicity,
in the **two-dimensional** disc — not in a vertical window.

### 6.1 The Jensen balance

**Lemma 6.1.** *For `0 < R ≤ √T`,*

    log|ζ(s₀)| = (R/π)·L + 𝔈_R(t₀) − ∫_0^R n_{t₀}(u) du/u + O(R²/T),

*where*

    𝔈_R(t₀) = (1/2π)[ ∫_{cos θ>0} log|ζ(s₀+Re^{iθ})| dθ + ∫_{cos θ<0} log|ζ(1−s₀−Re^{iθ})| dθ ],

*every sample point of `𝔈_R` having real part `1/2 + R|cos θ| ≥ 1/2`.*

*Proof.* Apply Jensen's formula to `ξ(s) = ½s(s−1)π^{−s/2}Γ(s/2)ζ(s)` on `D(s₀,R)`; `ξ` is entire and
its zeros are exactly the nontrivial zeros of `ζ`. Write `ξ = H·ζ` with
`H(s) = ½s(s−1)π^{−s/2}Γ(s/2)`. On `D(s₀,R)` the function `H` is analytic and zero-free: the poles of
`Γ(s/2)` sit at `s = 0,−2,−4,…` and the zeros of `s(s−1)` at `s = 0,1`, all at distance `≥ t₀ − R`
from `s₀`. Hence `log|H|` is harmonic on the disc and its circle mean equals its centre value, so it
cancels from Jensen's formula, leaving

    (1/2π)∫_0^{2π} log|ζ(s₀+Re^{iθ})| dθ − log|ζ(s₀)| = ∫_0^R n_{t₀}(u) du/u.       (6.1)

On the arc `cos θ < 0` the sample point `s = s₀+Re^{iθ}` has `Re s = ½ + R cos θ < ½`. Apply
`ζ(s) = χ(s)ζ(1−s)` with `|χ(s)| = (|Im s|/2π)^{½−Re s}(1+O(1/|Im s|))`, valid for `|Im s| ≫ 1`. The
`χ`-factor contributes `(−R cos θ)(L + O(R/T))`, whose mean over the left arc is

    (R/2π)·L·∫_{π/2}^{3π/2}(−cos θ)dθ + O(R²/T) = (R/π)·L + O(R²/T),

and the remaining `log|ζ(1−s)|` has `Re(1−s) = ½ + R|cos θ| ≥ ½`. Substituting into (6.1) gives the
claim. ∎

**Remark 6.2 (the exact duality).** If the zeros were distributed exactly as Riemann–von Mangoldt
predicts *and* all lay on the critical line, then `n_{t₀}(u) = (u/π)L + O(1)` and the zero potential
would be `∫_0^R (u/π)L du/u = (R/π)L` — **exactly** the `χ`-factor mean, at every radius. So
Lemma 6.1 is equivalent to

    log|ζ(1/2+it₀)| = 𝔈_R(t₀) + D_R(t₀) + O(R²/T),   D_R(t₀) := ∫_0^R ((u/π)L − n_{t₀}(u)) du/u,

i.e. **the size of `ζ` at a point equals the folded circle mean of `log|ζ|` on `Re ≥ ½` plus the
scale-integrated deficiency of the two-dimensional zero-counting function.** This is the folklore
picture, made into an identity. In particular `LH ⟺ D_R(t₀) = o(log T)` uniformly in `t₀`: the zero
set of `ζ` has no logarithmic holes around critical-line points.

### 6.2 The two available inputs

**(Z-a) Analytic input.** If `μ(1/2) ≤ θ₀` then Phragmén–Lindelöf gives `μ(σ) ≤ 2θ₀(1−σ)` on
`[½,1]` and `μ(σ) = 0` for `σ ≥ 1`, i.e. `μ(σ) ≤ 2θ₀(½ − (σ−½))_+` for `σ ≥ ½`. Since every sample
point of `𝔈_R` has `σ = ½ + R|cos θ|`,

    𝔈_R(t₀) ≤ 2θ₀·J(R)·log T + ε log T,     J(R) := (1/2π)∫_0^{2π}(½ − R|cos θ|)_+ dθ.

**(Z-b) Geometric input.** Every zero satisfies `|β − ½| ≤ ½`, so for `u ≥ ½` any zero with
`|γ − t₀| ≤ w(u) := √(u²−¼)` lies in `D(s₀,u)`. With `S` the argument function and
`S_max := sup_{|w|≤R}|S(t₀+w)|`, the Riemann–von Mangoldt formula gives

    n_{t₀}(u) ≥ (w(u)/π)L − 2S_max + O(1/T)  (u ≥ ½),        n_{t₀}(u) ≥ 0  (u < ½),

hence, for `R ≥ ½`,

    ∫_0^R n_{t₀}(u) du/u ≥ (I(R)/π)L − 2S_max·log(2R),
    I(R) := ∫_{1/2}^R √(u²−¼) du/u = √(R²−¼) − ½·arccos(1/(2R)).

**Evaluation of `J`.** `J(R) = ½ − 2R/π` for `R ≤ ½`; and for `R ≥ ½`, writing
`θ_R := arccos(1/(2R))`,

    J(R) = (2/π)[ π/4 − ½θ_R − R + √(R²−¼) ].

The two formulas agree at `R = ½` (value `½ − 1/π`), and `J` decreases from `½` at `R = 0` to `0` as
`R → ∞`.

### 6.3 The ceiling

**Theorem 6.3 (zero-geometry inertness).** *Assume `μ(1/2) ≤ θ₀ ≤ ¼` and `S(t) = o(log t)`. Then
Lemma 6.1 together with (Z-a), (Z-b) yields, for every `R ≥ ½`,*

    μ(1/2) ≤ ¼ + 2J(R)·(θ₀ − ¼),

*and for every `0 < R ≤ ½`,*

    μ(1/2) ≤ θ₀ + (R/π)(1 − 4θ₀).

*Consequently:* **(i)** *with `θ₀ = ¼` the output is exactly `¼` at every radius — the convexity
bound is a fixed point of the route at all scales;* **(ii)** *the output always lies in `[θ₀, ¼]`, so
the route never improves its input;* **(iii)** *`¼` is the unique fixed point of
`θ ↦ ¼ + 2J(R)(θ − ¼)`, and the map contracts toward it with ratio `2J(R) < 1`, so iterating the
route raises any subconvex input back up to `¼`.*

*Proof (case `R ≥ ½`).* Lemma 6.1 with (Z-a) and (Z-b) gives, after dividing by `log T` and letting
`ε → 0`,

    μ ≤ R/π + 2θ₀ J(R) − I(R)/π.

Put `A := R − √(R²−¼) ≥ 0`. Then `R − I(R) = A + ½θ_R`, while from the evaluation of `J`,

    1 − 2J(R) = 1 − (4/π)[π/4 − ½θ_R − R + √(R²−¼)] = (2/π)(θ_R + 2A).

Therefore `4(R − I(R)) = 4A + 2θ_R = 2(θ_R + 2A) = π(1 − 2J(R))`, i.e.

    (R − I(R))/π = (1 − 2J(R))/4.                                          (6.2)

Substituting, `μ ≤ (1 − 2J)/4 + 2θ₀J = ¼ + 2J(θ₀ − ¼)`. The case `R ≤ ½` is the same computation
with `I ≡ 0` and `J = ½ − 2R/π`; both branches give `θ₀ + (1−4θ₀)/(2π)` at `R = ½`. Statements
(i)–(iii) are immediate from the affine form. ∎

**Corollary 6.4 (the route closed on itself is exactly the convexity bound).** Taking `θ₀ = μ(1/2)`
in Theorem 6.3 gives `μ(1 − 2J) ≤ (1 − 2J)/4`, i.e. `μ ≤ ¼`, for every `R > 0`. The Jensen balance,
made self-consistent, is *equivalent to* the convexity bound: it reproduces it exactly, with no slack
at any radius, and yields nothing else.

**Corollary 6.5 (where the gain actually lives).** Suppose instead every zero `ρ` with
`|γ − t₀| ≤ R` has `β = ½`. Then `n_{t₀}(u) = (u/π)L + O(S_max)` for all `u ≤ R`, the potential
attains its full expected value `(R/π)L`, the `χ`-factor cancels completely, and the output is

    μ(1/2) ≤ 2J(R)·θ₀ + O(S_max·log R / log T).

Since `J(R) → 0`, iterating drives `θ₀ → 0`. This is a zero-geometry proof that **RH ⟹ LH**, with
contraction ratio `2J(R)` per step; under RH, `S(t) ≪ log t/log log t` and the choice
`R ≍ log log t` returns `|ζ(½+it)| ≤ exp(C log t · log log log t / log log t)`, the correct shape.

**Corollary 6.6 (the dichotomy).** The entire gain of the route is the **horizontal** position of the
zeros. The **vertical** input contributes nothing: any bound `S(t) ≤ c_S log t`, *including the
unproved `c_S = 0`*, leaves the output at `¼`. The intermediate hypothesis that would extract partial
gain is precisely

    #{ρ : β > ½ + δ, |γ − t₀| ≤ R} = o(log T)   pointwise in `t₀`,

which is Backlund's criterion — LH itself. **The zero-geometry route is exactly circular: it is worth
`¼` with no zero information and worth everything with full zero information, and there is no
intermediate.**

**Remark 6.7.** Theorem 6.3 explains a persistent numerical coincidence: several distinct
"large values force gaps" heuristics all terminate at `¼` rather than at some route-specific
constant. They must, by (6.2): the arc-average of the surviving convexity allowance and the disc
average of the guaranteed zero potential are the *same* linear functional of the disc geometry, so
their difference is pinned to `¼(1 − 2J)` independently of `R`.

### 6.4 The sharp form: the slope-`½` barrier

Theorem 6.3 fed the balance the *chord* `μ(σ) ≤ 2θ₀(1−σ)`. The chord is not what is known; the
known `μ*(σ)` lies below it in the interior. So the correct question is what the balance does when
fed the *actual* known curve. The answer is again exact, and it identifies the obstruction precisely.

Let `μ*` be any admissible upper bound for `μ` on `[½,1]` and put

    Φ(R) := (1/2π) ∫_0^{2π} μ*(½ + R|cos θ|) dθ,    Out(R) := (1 − 2J(R))/4 + Φ(R),

so that Lemma 6.1 with (Z-b) gives `μ(1/2) ≤ Out(R)` for every `R` (using (6.2)).

**Lemma 6.8 (gain criterion).** *`Out(0) = μ*(½)` and*

    Out'(0⁺) = (1 + 2·μ*'(½⁺))/π.

*So the route gains — i.e. `Out(R) < μ*(½)` for small `R>0` — if and only if `μ*'(½⁺) < −½`.*

*Proof.* For `R ≤ ½`, `J(R) = ½ − 2R/π` so `(1 − 2J(R))/4 = R/π`, with derivative `1/π`; and
`Φ'(0⁺) = μ*'(½⁺)·(1/2π)∫_0^{2π}|\cos θ|dθ = (2/π)·μ*'(½⁺)`. ∎

**Theorem 6.9 (slope-`½` barrier).** *Suppose the bound on the critical line is attained at the
self-dual block: `μ*(½) = b(½) − ¼`, where `t^{b(α)}` bounds a Dirichlet block of length `t^α`.
Since the same block remains admissible at every `σ`, `μ*(σ) ≥ b(½) − σ/2`, i.e.*

    μ*(σ) ≥ μ*(½) − (σ − ½)/2   for all σ ≥ ½.                        (6.3)

*Then for every `R > 0`,*

    Out(R) ≥ μ*(½),

*with equality exactly on the plateau `0 ≤ R ≤ 2μ*(½)` when (6.3) holds with equality.*

*Proof.* Write `a := 2μ*(½) ≤ ½`. By (6.3), `Φ(R) ≥ ½·G(a,R)` where
`G(c,R) := (1/2π)∫_0^{2π}(c − R|cos θ|)_+dθ`, and `J(R) = G(½,R)`.
For `R ≤ a` the positive part is inactive: `G(a,R) = a − 2R/π`, so

    Out(R) ≥ R/π + ½(2μ*(½) − 2R/π) = μ*(½),

**identically in `R`** — the explicit factor and the folded-mean loss cancel exactly. For `R ≥ a`,
`G(c,R) = (2/π)[c(π/2 − arccos(c/R)) − R + √(R²−c²)]` and a direct differentiation gives

    d/dR G(c,R) = (2/π)[√(R²−c²)/R − 1] ≤ 0,

whence, using `(1 − 2J(R))/4 = (1 − 2G(½,R))/4`,

    d/dR[ (1 − 2G(½,R))/4 + ½G(a,R) ] = (1/π)·( √(R²−a²) − √(R²−¼) )/R ≥ 0

because `a ≤ ½`. So the lower bound for `Out` is constant `= μ*(½)` on `[0,a]` and non-decreasing
after; in particular `Out(R) ≥ μ*(½)` for all `R`. ∎

**Corollary 6.10 (what must break for the route to give anything).** By Theorem 6.9 the zero-geometry
route improves nothing as long as the critical Dirichlet block at `σ = ½` is the self-dual block of
length `√(t/2π)`. The route gains **iff** one can prove

    μ(σ) < μ(½)_known − (σ − ½)/2   for some σ > ½,                    (6.4)

that is, a bound off the critical line that beats the slope-`½` line through the current on-line
record. Equivalently: a bound whose critical block is *longer* than `√(t/2π)`. Since the approximate
functional equation caps the block length at `√(t/2π)`, (6.4) is exactly the statement that the
self-dual block is *not* the binding one — the same condition that makes Guth–Maynard's large-value
estimate inert at `β = 1` (Theorem 3.3). **The twelfth ceiling and the third are the same
obstruction seen from two sides.**

Note the direction of (6.4): it is a *bootstrap*, converting off-line subconvexity into an
improvement **on** the critical line. This is the opposite of the usual direction (Phragmén–Lindelöf
converts on-line into off-line), and it is the only lever the zero-geometry route offers.

### 6.5 Self-dual stationarity: why every ceiling in this paper lands in the same place

The barrier of §6.4 is one instance of a pattern that runs through §3 as well. Here it is in its
smallest form.

Fix the abscissa `σ = ½ + x`, `0 ≤ x < ½`. Two facts, from opposite ends of the theory, are in play:

* the self-dual block traces the ceiling `μ*(½+x) = θ₀ − x/2` (inequality (6.3));
* the mean value theorem `∫_T^{2T}|ζ(½+x+it)|^{2k}dt ≪ T^{1+ε}` holds exactly for `σ ≥ 1 − 1/k`,
  i.e. for `k ≤ k(x) := 1/(½ − x)` — the **largest** admissible order, equal to `2` on the critical
  line (Theorem 3.1).

Pairing them at that largest admissible order gives the large-value saving

    Sav(x) := 2·k(x)·μ*(½+x) = (2θ₀ − x)/(½ − x),      Sav'(x) = 2(θ₀ − ¼)/(½ − x)².

**Theorem 6.11 (self-dual stationarity).**
**(i)** *At the convexity bound `θ₀ = ¼`,* `Sav(x) ≡ 1` *for every `x ∈ [0,½)` — the whole strip is
exactly tied, and no abscissa is preferred.*
**(ii)** *For any subconvex `θ₀ < ¼`, `Sav` is strictly decreasing, so the unique optimum is the
critical line `x = 0`, with* `Sav(0) = 4θ₀` *— the fourth moment, and nothing else.*
**(iii)** *For `θ₀ > ¼` the optimum would move off the line.*

*Proof.* `Sav(x) = (2θ₀−x)/(½−x)`; at `θ₀ = ¼` the numerator is `½ − x`, giving `1` identically.
For the monotonicity, `(2θ₀−y)(½−x) < (2θ₀−x)(½−y)` reduces after cancellation to
`2θ₀(y−x) < (y−x)/2`, i.e. to `θ₀ < ¼`. ∎

The content is a *tangency*: the slope-`½` line through `(½, ¼)` reaches `0` exactly at `σ = 1`,
which is exactly the abscissa at which the mean value theorem becomes available for all `k`. Two
unrelated features of `ζ` — the value `¼` of the convexity bound and the criticality `σ = 1 − 1/k` —
touch at one point. **The convexity bound is a degenerate tie across the whole strip; every
subconvexity input breaks the tie, and always in the same direction: back to the critical line and
the fourth moment.**

This is the mechanism behind the census of §5. Five independent packagings — Halász–Montgomery
(§3.2), Guth–Maynard blocks (§3.3), the Jensen balance (§6.3), folded-circle moments, off-line
moments — are five parametrisations of the same optimisation, and all five are stationary at the
self-dual point (`α = ½`, `β = 1`, `x = 0`, `k = 2`), which is a maximum precisely because
`μ < ¼`.

**Conjecture 6.12.** *Every optimisation over a block, abscissa, or moment parameter built from
(i) the approximate functional equation and (ii) a mean value theorem is stationary at the self-dual
parameter, and attains its global optimum there whenever the input exponent is `< ¼`.* Falsifiable:
exhibit one such optimisation whose optimum is strictly off the self-dual point. If true it predicts
that **any method improving `μ` must break the approximate functional equation's symmetry rather
than optimise within it.**

**Lean.** `HTGeometry.JensenZeroGeometry` certifies the exponent arithmetic: `foldedWidth` (`= J`)
with `0 ≤ J < ½` for every `R > 0` and the two branches agreeing at `R = ½`; the cancellation
identity (6.2); `jensenOutput J θ₀ = ¼ + 2J(θ₀−¼)` with `θ₀ ≤ jensenOutput ≤ ¼`, `¼` as unique fixed
point, and the iterate formula `(2J)^n(θ₀−¼)`; and `rhOutput J θ₀ = 2Jθ₀` with strict contraction and
`Tendsto … 0`. For §6.4: the structure `AFEBound` with `half_lipschitz_lower` (inequality (6.3) from
self-duality of the critical block), `afe_plateau_identity` (the exact cancellation `R/π + ½(2θ₀ −
2R/π) = θ₀`), `gain_derivative`, `no_gain_of_half_lipschitz`, and the capstone `afe_slope_barrier`.
Axioms `[propext, Classical.choice, Quot.sound]`.

## References (as used)

Bondarenko–Seip (GCD sums); Bourgain, *Decoupling, exponential sums and the Riemann zeta function*,
JAMS 2017; Bourgain–Watt (mean square of `ζ`, divisor and circle problems); Conrey–Gonek
(high moments); Fouvry–Kowalski–Michel (exponent of distribution of `d_3`); Good (`E(T) = Ω(T^{1/4})`);
Guth–Maynard, arXiv:2405.20552; Hamburger (1921); Heath-Brown, *The twelfth power moment of the
Riemann zeta-function*, QJM 29 (1978); Ivić (general additive divisor problem; mean square of the
divisor function in short intervals); Ivić–Motohashi (`E_2 = Ω(T^{1/2})`); Ivić–Wu, arXiv:1106.4744;
Baier–Browning–Marasingha–Zhao, arXiv:1101.5464; Kwan (spectral moment formulae for `GL(3)×GL(2)`);
Milićević–White, arXiv:1908.04833; Motohashi (fourth moment; shifted divisor); Munshi (conductor
lowering); Sawin, Duke 2021 and Acta Math. 2024; Tao–Trudgian–Yang (ANTEDB); Topacogullari (shifted
convolution of divisor functions).
