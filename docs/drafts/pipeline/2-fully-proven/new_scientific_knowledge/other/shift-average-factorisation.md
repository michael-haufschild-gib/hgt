# ⚠ RETRACTED — see the retraction notice below

> **RETRACTION (campaign cycle 82, erratum E19).** **Theorem 1, Theorem 2, and the `(⟹)` direction of
> Theorem 3 in this note are WITHDRAWN.** Their proofs rest on Step 3 of §3, which applies Voronoi
> summation to the `n`-sum *inside* the `m`-sum — i.e. it interchanges the `Δ_k` Voronoi series with a
> second summation. That interchange is illegitimate: a legitimate version of it proves the sharp
> Dirichlet divisor conjecture at `k = 2` and `Δ₃ ≪ x^{1/3+ε}` at `k = 3`, both open. The error was
> found by deriving `G₃` two ways and obtaining incompatible answers.
>
> **Also withdrawn:** §5.2 Theorem 3's forward direction; the general-`k` equivalence (erratum E17 —
> the two directions coincide only at `k = 3`); and the `Ω`-result `G₃ = Ω(y^{5/6−ε})`, which used the
> withdrawn direction.
>
> **What survives:** the kernel facts of §2.1 as pure analysis (the elementary integral
> `∫_1^X sin(cu)du = (cos c − cos cX)/c`, its oddness, the product-to-sum split, and the Laplace
> factorisation of §2.2) — all Lean-certified in `HTGeometry.TernaryVoronoiAntisymmetry`; the
> phase-speed invariant of Corollary 4.1; and the Mellin direction, which is elementary. **Note
> further (erratum E21) that the Mellin direction is Perron's method in disguise, so its outputs are
> classical, not new.**
>
> The note is retained unedited below as a record of what was attempted and why it failed. **Do not
> cite Theorems 1–3.**

---

# The shift-average of a divisor correlation is the square of a one-variable exponential sum

- **ID:** `shift-average-factorisation`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) — an *exact identity*, not a bound
- **Scientific status:** `[PROVED HERE] [POSITIVE RESULT] [NEEDS EXTERNAL AUDIT]`
- **Lean:** `HTGeometry.TernaryVoronoiAntisymmetry` (the two mechanisms), axioms
  `[propext, Classical.choice, Quot.sound]`

Notation. `d_k` is the `k`-fold divisor function, `D_k(y) = Σ_{n≤y}d_k(n) = yP_{k-1}(\log y) + Δ_k(y)`,
and `Δ_k(x,h) = Σ_{n≤x}d_k(n)d_k(n+h) − MT_k(x,h)` is the error in the `k`-fold additive divisor
problem. Write `α = (k-1)/2k`, `β = (k+1)/2k` (so `α+β = 1`), and `γ_k = (k-3)π/4`.

---

## 1. Statement

**Theorem 1.** *Let `k ≥ 2` be fixed, `x` large, and `1 ≤ H ≤ x^{1-δ}`. Put `X := x^{1/k}` and*

    F(t)  :=  Σ_{m ≤ M} d_k(m) · m^{-1/k} · e^{-2πk m^{1/k} t} · e(k X m^{1/k}),      t ≥ 0,

*with `M` the Voronoi truncation. Then*

    Σ_{h=1}^{H} Δ_k(x,h)  =  𝔐_k(x,H)  −  C_k · H · Re[ e^{2iγ_k} ∫_0^∞ F(t)^2 dt ]  +  E,

*where `𝔐_k` is the mismatch between `H·(smooth main)` and `Σ_{h≤H}MT_k(x,h)`, `C_k > 0` is explicit,
and `E` collects the linearisation, truncation and boundary errors.*

**What is asserted.** A two-variable correlation problem, averaged over the shift, is *exactly* the
square of a **one-variable** divisor exponential sum. No inequality is used in reaching this form;
the reduction is by two applications of Voronoi summation and two exact cancellations.

**What is not asserted.** Theorem 1 is not a bound. It does not improve any known estimate on its own;
it changes what has to be estimated, from `Σ_m Σ_l d_k(m)d_k(l)(\ldots)` to `|F|²`.

---

## 2. The two mechanisms

The content is two cancellations, both exact.

### 2.1 The resonant half vanishes by antisymmetry

Insert the Voronoi expansion

    Δ_k(y) = c_k y^{α} Σ_{m≤M} d_k(m) m^{-β} cos(2πk(my)^{1/k} + γ_k)

into the exact reduction (Lemma 3.1 below) and linearise the shift difference. The `n`-sum then
carries a **sine** — it comes from differencing a cosine — while the Voronoi kernel of the second
application carries a **cosine**. Product-to-sum splits the double sum:

    sin(A+γ)cos(B+γ) = ½[ sin(A+B+2γ) + sin(A−B) ],   A = 2πk(my)^{1/k}, B = 2πk(ly)^{1/k}.

Substituting `y = u^k` — under which `y^{-(k-1)/k}dy = k\,du`, flattening the `k`-th-root phase — makes
both integrals elementary:

    ∫_1^X sin(cu)\,du = (cos c − cos cX)/c  =:  K(c,X).

**`K(·,X)` is an odd function of `c`.** Its argument in the resonant term is
`c₋ = 2πk(m^{1/k} − l^{1/k})`, antisymmetric under `m ↔ l`, while the accompanying weight
`d_k(m)d_k(l)(ml)^{-1/k}` is symmetric. Hence

> **Proposition 2.1.** *The resonant half of the double Voronoi sum vanishes identically:*
> `Σ_{m,l ∈ S} w(m,l)·K(φ(m) − φ(l), X) = 0` *for every symmetric `w` and every `φ`.*

*Lean:* `resonant_double_sum_eq_zero`, `resonantKernel_neg`, `integral_sin_mul_eq_resonantKernel`,
`sin_mul_cos_split`, `double_voronoi_resonant_cancellation`.

**Corollary 2.2 (no diagonal obstruction).** In particular the diagonal `m = l` contributes
`sin 0 = 0`, not `cos 0 = 1`. **The first moment `Σ_h Δ_k` has no diagonal term.** The conspiracy
exponent `k/4` familiar from the independent-signs model is a property of the *mean square*, where
the pairing is cosine × cosine; the two are different objects and are routinely conflated.

### 2.2 The non-resonant half factorises

What survives carries the phase `φ(m) + φ(l)` and the weight `1/(φ(m)+φ(l))`. The phase is **additive**
and the weight has the Laplace representation `1/c = ∫_0^∞ e^{-ct}dt`, so both factor:

    Σ_{m,l} w_m w_l · cos(c₊X + 2γ)/c₊  =  Re[ e^{2iγ} ∫_0^∞ ( Σ_m w_m e^{-φ(m)t} e(kXm^{1/k}) )² dt ].

> **Proposition 2.3.** *With the Laplace variable inserted, the non-resonant double sum is the square
> of a single sum.*

*Lean:* `laplace_reciprocal`, `nonresonant_double_sum_is_square`.

---

## 3. Proof of Theorem 1

**Lemma 3.1 (exact reduction).** `Σ_{h≤H} d_k(n+h) = D_k(n+H) − D_k(n)` gives, with no error,

    Σ_{h≤H} Δ_k(x,h)  =  Σ_{n≤x} d_k(n)·[Δ_k(n+H) − Δ_k(n)]  +  𝔐_k(x,H).

*Proof.* Interchange the two summations and subtract the main terms. ∎

The smooth part of `D_k(n+H) − D_k(n)` is `H·Q_{k-1}(\log n) + O(H²/n)`, contributing
`H·Σ_{n≤x}d_k(n)Q_{k-1}(\log n)`, which by partial summation is a main term plus
`O(H x^{(k-1)/(k+1)+ε})`; at `k = 3, H = x^{1/3}` this is `x^{5/6}`, negligible against the target.

**Step 2 (first Voronoi, linearised).** For `m ≤ m₀(n) = n^{k-1}/H^k` the phase increment
`ψ_m ≍ m^{1/k}Hn^{1/k-1}` is `≪ 1` and

    Δ_k(n+H) − Δ_k(n) ≈ −2πc_k H n^{α+1/k-1} Σ_{m} d_k(m) m^{-β+1/k} sin(2πk(mn)^{1/k}+γ_k).

Since `α+β = 1`, the surviving weight is `d_k(m)m^{-1/k}`.

**Step 3 (second Voronoi).** Apply Voronoi to the `n`-sum. Its kernel is
`G(u) ≈ c_k u^{-1/k}\cos(2πk u^{1/k}+γ_k)`, normalisation fixed by consistency: feeding
`f = 1_{[0,x]}` must reproduce the `Δ_k` expansion, and it does. **The two weights are therefore
identical, `d_k(·)(·)^{-1/k}` on both sides — which is what Proposition 2.1 requires.**

**Step 4.** Product-to-sum, then `y = u^k`. Proposition 2.1 kills the resonant half; Proposition 2.3
factorises the rest. ∎

---

## 4. Two structural corollaries

**Corollary 4.1 (phase-speed invariant).** The dual phase `2πk(my)^{1/k}` has `m`-derivative
`2π(y/m^{k-1})^{1/k}`, which is `≥ 1` exactly for `m ≲ y^{1/(k-1)}`. Comparing with the natural
truncation `m ≍ y`:

    y ≤ y^{1/(k-1)}   ⟺   k ≤ 2.

*The Voronoi dual of `d_k` oscillates across its whole range if and only if `k = 2`.* For `k = 3` it
oscillates only to `√y`; beyond that consecutive dual terms are in phase. *Lean:*
`voronoiFastRange_covers_iff`.

**Proposition 4.2 (the identity's exact reach).** The linearisation of Step 2 is valid for
`m ≤ m₀(n) = n^{k-1}/H^k`, while the Voronoi dual runs to `M ≍ n`. The identity therefore covers the
**whole** dual range precisely when `m₀(n) ≥ n`, i.e.

    H  ≤  x^{(k-2)/k}.

*Consequences.* At `k = 2` the condition reads `H ≤ 1` — **the identity never covers the full dual
range in the binary case.** At `k = 3` it reads `H ≤ x^{1/3}`, which is *exactly* the shift range the
sixth-moment transfer uses. At `k = 4`, `H ≤ x^{1/2}`.

So Theorem 1 is intrinsically a `k ≥ 3` phenomenon, and at `k = 3` its reach coincides with the range
the moment problem needs — not by arrangement, but because both are governed by `n^{k-1}/H^k`. The
binary case, where everything else is known, is the one case the identity does *not* cover; this is
why the theorem could not have been found by generalising the solved case.

**Corollary 4.3 (uniformity in the index).** Running the same computation with `k` free: the block
length is `x^{(k-2)/k}`, the block count `x^{2/k}`, and **the diagonal of the short-interval mean
square is `x·h` — exponent `1` — at every `k`.** *Lean:* `reduction_loop_uniform`.

---

## 5. The payoff: a one-variable sufficient condition

The point of an exact reduction is what it lets one estimate instead. Theorem 1 replaces a
two-variable correlation by `∫_0^∞F(t)^2dt`, and `F` is built by partial summation from the single
classical sum

    G(y)  :=  Σ_{m ≤ y} d_k(m) · e(k X m^{1/k}),      X = x^{1/k}.

**Theorem 2.** *Fix `k = 3` and `H = x^{1/3}` (the exact reach, Proposition 4.2). If*

    G(y)  ≪  y^{1-η} (\log y)^{A}      uniformly for  y ≤ x,

*for some `η > 0`, then*

    Σ_{h≤H} Δ₃(x,h)  ≪  x^{4/3 - 2η + ε}.

*In particular `η > 1/12` gives `≪ x^{7/6-}`, **strictly below the known moment envelope**, hence
`m(3) < 5/4`.*

*Proof.* Partial summation gives `F(t) ≪ \max_{y≤M}|G(y)|·y^{-1/3}`, so `F ≪ x^{2/3-η}` with `M ≍ x`.
The Laplace weight cuts the dual block `m ≍ M` at `t ≍ M^{-1/3}`, so
`∫_0^∞|F|^2dt ≪ x^{-1/3}·x^{4/3-2η} = x^{1-2η}`. Theorem 1 multiplies by `H = x^{1/3}`. The threshold
is `4/3 - 2η < 7/6`, i.e. `η > 1/12`. ∎

**Calibration.** The trivial bound `G(y) ≪ y(\log y)^2` is `η = 0` and returns `x^{4/3}`, above the
envelope `x^{7/6}` — so the reduction is not free, exactly as it should not be. The required saving
`1/12` is half the campaign's recurring gap `1/6 = 1/2 - 1/k` at `k = 3`.

**What Theorem 2 buys.** The hypothesis is a bound on a **one-variable exponential sum with divisor
weights** — not a shifted convolution, not a correlation, not a level-of-distribution statement. Its
phase `kXm^{1/k}` has `m`-derivative `Xm^{-2/3}`, which is `≥ 1` exactly for `m ≤ x^{1/2}`
(Corollary 4.1 again). On `y ≤ x^{1/2}` the phase is fast and van der Corput applies directly; the
whole difficulty is the slow-phase range `x^{1/2} < y ≤ x`, where the exponential is constant across
blocks of length `x^{1/3}` and all cancellation must come from `d₃` itself.

> **The exact statement of what is needed:** beat the trivial bound for
> `Σ_{m≤y}d₃(m)e(3x^{1/3}m^{1/3})` by `y^{1/12}`, uniformly for `x^{1/2} < y ≤ x`.

### 5.1 The one-variable sum, attacked: an exponent-pair threshold

Write `d₃(m) = Σ_{abc=m}1`, order `a ≤ b ≤ c`, fix `a,b` and sum over `c`. The phase is

    g(c) = 3X(ab)^{1/3}c^{1/3}  =  Y·(c/C)^{1/3},     Y = 3X(abc)^{1/3} ≍ x^{1/3}y^{1/3},  C = y/(ab),

a `Y·F(c/C)` phase with `F(u) = u^{1/3}` smooth — exactly the setting of exponent pairs. For a pair
`(κ,λ)`, `Σ_{c≍C}e(g(c)) ≪ (Y/C)^{κ}C^{λ}`.

**The balanced range `a ≍ b ≍ c ≍ y^{1/3}` is the bottleneck** (unbalanced `a` gives a longer `c`-sum
and a better saving). There `C = y^{1/3}`, `Y/C = x^{1/3}`, and summing trivially over the `y^{2/3}`
pairs `(a,b)`:

    G(y)  ≪  y^{2/3} · x^{κ/3} · y^{λ/3},     which at `y ≍ x` is  x^{(2+κ+λ)/3}.

Comparing with the requirement `G ≪ y^{1-η}`:

> **`η ≤ (1 − (κ+λ))/3`, so Theorem 2 applies as soon as `κ + λ < 3/4`.**

**Calibration against the record.** The best known exponent pair is Bourgain's `(13/84, 55/84)`, with
`κ+λ = 68/84 = 17/21 = 0.8095…`, giving `η ≤ 4/63 = 0.0635…` against the required `1/12 = 0.0833…`.

    needed:  κ + λ  <  3/4   =  63/84
    known:   κ + λ  =  17/21 =  68/84
    **shortfall: 5/84.**

The exponent-pair conjecture `(ε, 1/2+ε)` gives `κ+λ → 1/2 < 3/4`, so it implies the hypothesis of
Theorem 2 comfortably — consistent with the classical fact that the exponent-pair conjecture implies
Lindelöf, and a check this chain could have failed.

**Status.** The shortfall `5/84` is small and the estimate above is deliberately crude: it uses
cancellation only in `c` and none in `a, b`, and it evaluates at the single worst point `y ≍ x`. Any
of — cancellation in a second variable, a pair tailored to the phase `u^{1/3}`, or exploiting that
`a ≤ b ≤ c` forces `a ≤ y^{1/3}` — could close it. **This is the campaign's narrowest surviving gap
and the only one measured against a published exponent rather than against an unproved conjecture.**

---

## 5.2 The equivalence

The chain is tight in both directions.

**Theorem 3 (equivalence).** *For `k ≥ 3` and `H = x^{(k-2)/k}` (the exact reach),*

    G_k(y) := Σ_{m≤y} d_k(m) e(k x^{1/k} m^{1/k})  ≪  y^{1-η}      ⟺      m(k) ≤ k - 3/2 - kη.

*In particular `m(k) = 1 ⟺ G_k(y) ≪ y^{5/(2k)}`, and at `k = 3`: `m(3) ≤ 3/2 - 3η`, so the known
`m(3) ≤ 5/4` is exactly `G₃ ≪ y^{11/12}`.*

*Proof.* `(⟸)` Mellin gives `G_k(y) = (1/2πi)∫ζ(s)^k M(s)ds` with `M(s) = k∫_1^V v^{ks-1}e(kXv)dv`,
`V = y^{1/k}`; stationary phase concentrates `M` at `|t| ≍ XV = x^{2/k}·…`, which is the height `T`
with `x = T^{k/2}`. Cauchy–Schwarz against `∫|M(1/2+it)|²dt ≍ y` gives `|G_k| ≪ T^{m(k)/2}y^{1/2}`.
`(⟹)` Theorem 2's chain gives the transfer input `(a,b) = (1/2, (5k-8)/(2k) - 2η)`, whose transfer
output is `k - 3/2 - kη`. ∎

> **Consequence.** The `2k`-th moment exponent of `ζ` is *determined* by the size of one one-variable
> divisor exponential sum with a `k`-th-root phase. The statement contains no correlation, no shifted
> convolution and no automorphic input.

This is why every analytic treatment of `G_k` attempted so far returns its input exactly: exponent
pairs (`κ+λ < 3/4 ⟺ μ < 1/8`), the Voronoi interchange (worth the divisor problem), Riesz means
(cost `x^{(k-1)/2k}`, the size of `Δ_k`), and Mellin (equality). **They are four views of Theorem 3.**

---

## 6. Novelty audit

**Classical:** the Voronoi expansion of `Δ_k`; the identity of Lemma 3.1; the Laplace representation.

**New here:** Proposition 2.1 (the resonant half of the double Voronoi sum vanishes identically, and
consequently the first moment has *no diagonal term*) and Proposition 2.3 (the non-resonant half is
the square of a one-variable sum), hence Theorem 1 — the exact factorisation of the shift-average.
Also new: Corollary 4.1, which separates `k = 2` from `k ≥ 3` by an invariant of the dual phase rather
than by a moment, a block, or an abscissa; and Corollary 4.2.

**What Theorem 1 does not give.** It is an identity, and the term it isolates is controlled only on
the linearisation range of Proposition 4.2. Outside that range the two Voronoi expansions are not
differenced, the pairing is cosine × cosine, and the diagonal *survives*: Proposition 2.1 does not
apply there. A bound on `Σ_h Δ_k` therefore requires separate control of `m > m₀(n)`, which the
identity does not supply. **Consistency check that exposes this:** at `k = 2` the trivial estimation
of `∫_0^∞ F(t)^2 dt` gives `≪ x^{1/2+ε}`, so the linearised part alone would yield
`Σ_{h≤H}Δ₂(x,h) ≪ H x^{1/2+ε}` — the Conrey–Gonek strength, with no cancellation used. That is
plainly too strong, and Proposition 4.2 says why: at `k = 2` the linearisation range is empty, so the
estimate applies to none of the sum.

**Honest limitations.** The proof uses the truncated Voronoi formula for `Δ_k` at the level of its
standard asymptotic form; the kernel normalisation in Step 3 is fixed by consistency rather than
quoted; the linearisation range and the main-term mismatch `𝔐_k` are handled at the level of exponent
bookkeeping. These are the standard bookkeeping steps of the subject, but they are bookkeeping that
this note performs rather than cites, and an external audit should check them.

Classification: `NEEDS EXTERNAL AUDIT`.
