# Method ceilings for the Lindelöf hypothesis:
# eleven barrier theorems, and why they all meet at 1/8

**Abstract.** Let `μ = μ(1/2)` be the Lindelöf exponent of the Riemann zeta function, so that the
Lindelöf hypothesis (LH) asserts `μ = 0`. We prove ceiling theorems for eleven independent routes to
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
**(iv)** no resonance method can disprove LH, since Gál sums are subpolynomial. We further show that
the additive-divisor route separates into two independent halves — a pointwise size and a
shift-cancellation — each worth exactly `1/8` alone and jointly worth LH, and that the two competing
conjectured sizes (Conrey–Gonek `x^{1/2+ε}`, Ivić `Ω(x^{1-1/k})`) settle LH in opposite directions.
Four of the results are certified in Lean 4 with no axioms beyond `propext`, `Classical.choice`,
`Quot.sound`.

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

## 3. Eleven ceilings

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
