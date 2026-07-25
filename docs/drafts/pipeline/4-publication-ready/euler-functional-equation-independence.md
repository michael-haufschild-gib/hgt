# Euler product and functional equation do not imply the Riemann hypothesis:
# four independent hypotheses, and two explicit counterexamples

**Abstract.** It is a widely repeated heuristic that the `L`-functions for which the Riemann
hypothesis should hold are exactly those possessing both an Euler product and a functional
equation, and it is equally widely acknowledged that no precise form of this heuristic has been
formulated. We formulate it in the category of Beurling generalized prime systems and refute the
naive form. Writing `Λ ≥ 0` for nonnegativity of the generalized von Mangoldt measure (the exact
content of "Euler product with nonnegative local data"), we prove that the four hypotheses

* **(H1)** `Λ ≥ 0`,
* **(H2)** the exact Riemann functional equation with the classical archimedean factor,
* **(H3)** the completed function is entire of order one,
* **(H4)** the pole at `s=1` is simple,

are pairwise independent: dropping any one of them admits a system with zeros off the critical
line. Dropping **(H1)** is Davenport–Heilbronn; dropping **(H2)** is Diamond–Montgomery–Vorhauer.
The two remaining independence results are new and are proved by explicit construction: Theorem H
(drop **(H3)**) and Theorem J (drop **(H4)**). We further prove that the full conjunction is rigid
for every countable absolutely summable deformation of `ζ` (Theorems K, K′, K″), and we prove a
ceiling theorem (Theorem N) explaining why no argument resting on linear positivity of `Λ` can
reach the Riemann hypothesis itself, which is not a deformation statement.

---

## 1. The category

Work in logarithmic coordinates `u = log x`. A **generalized system** is a nonnegative Borel
measure `Π` on `(0,∞)` (the generalized prime measure), with prime-power measure `Π_* = TΠ`,

```text
(Tf)(u) = Σ_{k≥1} k^{-2} f(u/k),        Mellin multiplier ζ(2-s),
dΨ(u)   = u · dΠ_*(u),                  the generalized von Mangoldt measure,
M(s)    = ∫_0^∞ e^{-su} dΨ(u) = -F'(s)/F(s),   Re s > σ_a.
```

`F` is the associated zeta function; `Λ ≥ 0` is the statement `dΨ ≥ 0`, equivalently (Bernstein)
that `M` is completely monotone on `(σ_a,∞)`. Continuous prime measures are admitted, as is
standard.

**Lemma 1.1 (the functional equation as a reflection identity).** `π^{-s/2}Γ(s/2)F(s)` is invariant
under `s ↦ 1-s` if and only if

```text
M(s) + M(1-s) = A(s) := ½[Ψ(s/2) + Ψ((1-s)/2)] - log π,                     (1.1)
```

`Ψ` the digamma function.

*Proof.* Differentiate `log ξ_F(s) = log ξ_F(1-s)` and substitute `M = -F'/F`. ∎

Since `A` depends only on the archimedean factor, the solution set of `(1.1)` is a coset: the
difference of any two solutions is *reflection antisymmetric*, `N(s) = -N(1-s)`.

## 2. The antisymmetric cone

**Lemma 2.1.** For `r ∈ ℂ` set `e_r(u) = e^{ru} + e^{(1-r)u}`. Then for `Re s > max(Re r, 1-Re r)`

```text
∫_0^∞ e^{-su} e_r(u) du = 1/(s-r) + 1/(s-(1-r)),                             (2.1)
```

and this transform is exactly reflection antisymmetric. Writing `w = r - ½`,

```text
e_r(u) = 2 e^{u/2} cosh(wu),                                                (2.2)
```

so every reflection-antisymmetric correction has the form `d(u) = 2e^{u/2}h(u)` with `h` even.

*Proof.* `(2.1)` is elementary. Antisymmetry: `1/(1-s-r) + 1/(1-s-(1-r)) = -1/(s-(1-r)) - 1/(s-r)`.
`(2.2)` is `e^{ru}+e^{(1-r)u} = e^{u/2}(e^{wu}+e^{-wu})`. ∎

Two consequences are immediate and control everything below:

* a **positive** coefficient at `w` gives `F` a **pole** at `½ ± w` of that order;
* a **negative** coefficient at `w` gives `F` a **zero** at `½ ± w` of that order.

Local finiteness of `Π` near `x = 1` forces `h(0) = Σ_j t_j = 0`: otherwise `dΠ_* = d(u)du/u` has
infinite mass at the origin.

## 3. Rigidity: positivity forces a real leading frequency

**Theorem I.** Let `h(u) = Σ_{j=1}^m t_j cosh(w_j u)` be finite, real, with `Re w_j ≥ 0` and the
multiset closed under `w ↦ w̄` with equal coefficients. If `h ≥ 0` on `ℝ` and `h ≢ 0`, then, with
`α = max{Re w_j : t_j ≠ 0}`, there is a **real** `w_{j₀} = α` with `t_{j₀} > 0`.

*Proof.* For `u ≥ 0` and `Re w_j ≥ 0` the terms `e^{-w_ju}` are bounded, so

```text
2 e^{-αu} h(u) = Q(u) + o(1),     Q(u) = Σ_{Re w_j = α} t_j e^{i Im(w_j)u},
```

a real trigonometric polynomial. Since `Q` is almost periodic, `h ≥ 0` forces `Q ≥ 0` everywhere.
Its mean value is `M(Q) = Σ_{w_j = α real} t_j`, all non-real frequencies having zero mean. If
`M(Q) = 0` then `M(Q²) ≤ ‖Q‖_∞ M(Q) = 0`, and `M(Q²)` is the sum of the squared coefficients of `Q`
(Parseval), so `Q ≡ 0`, contradicting maximality of `α`. Hence `M(Q) > 0`. ∎

**Corollary 3.1.** `ξ` has no real zeros: `η(s) = (1-2^{1-s})ζ(s) > 0` for real `s ∈ (0,1)` while
`1-2^{1-σ} < 0`, so `ζ(σ) < 0` there; the trivial zeros are cancelled by the poles of `Γ(s/2)`; and
`ξ(0), ξ(½), ξ(1) ≠ 0`. Hence a positive coefficient at a **real** `w ≠ ½` violates entirety, since
the resulting real pole of `F` at `½ ± w` has no zero of `ξ` to absorb it. The frequency `w = ½` is
the unique exception: its poles sit at `s = 1` and `s = 0`, where the completion factor `s(s-1)`
already clears poles.

## 4. Theorem H: entirety is necessary

**Theorem H.** Fix `β ∈ (½,1)`, `γ ≠ 0`, `ρ = β+iγ`, `a₀ = β-½`, and any `c ∈ (a₀, ½)`. Put

```text
d(u) = 4(e^{(c+½)u} + e^{(½-c)u}) - 2cos(γu)(e^{βu} + e^{(1-β)u}).
```

Then `d ≥ 0` on `[0,∞)`; its Laplace transform is
`N(s) = 4[\frac1{s-c-½} + \frac1{s-½+c}] - Σ_{z} \frac1{s-z}` over `z ∈ {ρ,ρ̄,1-ρ,1-ρ̄}`, which is
reflection antisymmetric; and

```text
F(s) = ζ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [(s-½-c)(s-½+c)]^4
```

satisfies **(H1)**, **(H2)**, **(H4)** and has zeros off the critical line. Its completed function
has poles at `½ ± c`, so **(H3)** fails.

*Proof.* Nonnegativity: `c+½ ≥ β` and `c+½ ≥ 1-β` give `e^{(c+½)u} ≥ e^{βu}, e^{(1-β)u}`, whence
`d(u) ≥ 4e^{(c+½)u} - 2e^{βu} - 2e^{(1-β)u} ≥ 0`. The transform and its antisymmetry are Lemma 2.1.
`c < ½` keeps the abscissa below `1`, so the pole at `s=1` stays simple. ∎

If moreover `κ := \sqrt{a₀²+γ²}` replaces `c` and `κ < ½`, the prime measure itself is nonnegative;
see §6.

## 5. Theorem J: the pole order is necessary

**Theorem J.** Fix `a₀ ∈ (0,½)` and `γ ≠ 0`; put `ρ = ½+a₀+iγ` and

```text
d(u) = 2(e^{u}+1) - 2cos(γu)(e^{(½+a₀)u} + e^{(½-a₀)u}) = 4e^{u/2}[cosh(u/2) - cosh(a₀u)cos(γu)].
```

Then:

1. `d ≥ 0` on `[0,∞)` for **every** `γ`;
2. its Laplace transform is `N(s) = 2[\frac1{s-1}+\frac1s] - Σ_z \frac1{s-z}`, reflection
   antisymmetric, absolutely convergent for `Re s > 1`;
3. `F(s) = ζ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/[s(s-1)]²` has
   `½ s³(s-1)³π^{-s/2}Γ(s/2)F(s) = ξ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)`, **entire of order one** and
   invariant under `s ↦ 1-s`;
4. `F` has zeros at `ρ, ρ̄, 1-ρ, 1-ρ̄`, off the critical line;
5. if `a₀² + γ² ≤ ¼` the prime measure is nonnegative, so `F` is the zeta function of a genuine
   Beurling system.

So `F` satisfies **(H1)**, **(H2)**, **(H3)** and has off-critical zeros; only **(H4)** fails, the
pole at `s=1` having order three.

*Proof.* (1) With `X = e^{a₀u}`, `Y = e^{u/2}` and `1 ≤ X ≤ Y`,

```text
(Y²+1) - (YX + Y/X) = (Y-X)(XY-1)/X ≥ 0,
```

and `cos ≤ 1` finishes. (2) is Lemma 2.1. (3) `G(s)[s(s-1)]²` is the quartic polynomial, and both
`ξ` and the quartic are `s ↦ 1-s` invariant, the latter because its root multiset
`{ρ,ρ̄,1-ρ,1-ρ̄}` is invariant and has even cardinality. (4) is clear. (5) Writing `w = a₀+iγ`,

```text
h(u) = 2[cosh(u/2) - Re cosh(wu)] = 2 Σ_{n≥0} ((¼)^n - Re w^{2n}) u^{2n}/(2n)!,
```

and `|Re w^{2n}| ≤ |w|^{2n} ≤ (¼)^n`, so all coefficients are nonnegative and the constant one
vanishes. Hence `h(u)/u` is nondecreasing and Lemma 6.1 applies. ∎

## 5b. Theorem J′ and the pole-order budget law

Theorem J spends a pole of order three. Two is enough, and two is optimal.

**Theorem J′.** Fix `w ∈ (0,½)` and put

```text
d(u) = e^u + 1 - e^{(½+w)u} - e^{(½-w)u} = (e^{u/2} - e^{wu})(e^{u/2} - e^{-wu}).
```

Then `d ≥ 0` on `[0,∞)`; its Laplace transform
`N(s) = 1/(s-1) + 1/s - 1/(s-½-w) - 1/(s-½+w)` is reflection antisymmetric; and

```text
F(s) = ζ(s)·((s-½)² - w²)/(s(s-1)),      (s(s-1))²·π^{-s/2}Γ(s/2)F(s)/2 = ξ(s)·((s-½)² - w²)
```

is entire of order one and invariant under `s ↦ 1-s`. `F` satisfies **(H1)**, **(H2)**, **(H3)**,
has a pole of order exactly **two** at `s=1`, and has the two zeros `½ ± w` — which are **real**,
hence off the critical line. Since `d(u)/u` is nonnegative and nondecreasing, Lemma 6.1 makes the
prime measure nonnegative, so `F` is the zeta function of a genuine Beurling system.

*Proof.* Nonnegativity is the displayed factorization together with `e^{wu} ≤ e^{u/2}` and
`e^{-wu} ≤ e^{u/2}` for `u ≥ 0`, `0 ≤ w ≤ ½`. Antisymmetry is Lemma 2.1. The completion identity
follows from `ξ(s) = ½s(s-1)π^{-s/2}Γ(s/2)ζ(s)`; the quadratic is `s↦1-s` invariant because
`(½-s)² = (s-½)²`. Monotonicity of `d(u)/u = ((e^{u/2}-e^{wu})/u)·(e^{u/2}-e^{-wu})` reduces, after
cross-multiplication, to monotonicity of `t ↦ (t-1)e^t` on `[0,∞)`, whose derivative is `te^t ≥ 0`,
applied at `t = wu ≤ u/2`. ∎

At `w = ½` the quadratic is `s(s-1)`, `d ≡ 0` and `F = ζ`: the family degenerates exactly where it
must.

The mechanism is a conservation law. Writing the correction as `d(u) = 2e^{u/2}h(u)`,
`h = Σ_j t_j cosh(w_j u)`, local finiteness of `Π` at `x = 1` forces the **trace condition**
`h(0) = Σ_j t_j = 0`. By Corollary 3.1 and **(H3)** the only admissible positive coefficient is at
`w = ½`, whose poles at `s ∈ {0,1}` the completion already clears; every other coefficient is
negative, i.e. an inserted zero. Hence

```text
ord₁ F  =  1 + t_{1/2}  =  1 + Σ_{j ≠ ½} |t_j|.
```

Because `cosh(wu) = cosh(-wu)`, a frequency is really the **pair** `{w,-w}`, and reality of `h`
makes the multiset of frequencies conjugation-stable with equal coefficients. Now

```text
{w,-w} = {w̄,-w̄}   ⟺   Im w = 0  or  Re w = 0,
```

that is, exactly when the inserted zeros `½ ± w` are real or lie on the critical line. This gives:

**Theorem O (pole-order budget).** For a finite-rank reflection-antisymmetric deformation of `ζ`
satisfying **(H1)**–**(H3)** which only *inserts* zeros — that is, whose transform has nonpositive
coefficient at every frequency other than `½` — `ord₁F - 1` equals the total inserted zero
multiplicity counted by frequency pairs. Consequently

```text
ord₁F = 1  ⟹  no inserted zeros                                   (Theorem M below)
ord₁F = 2  ⟹  one inserted pair {½ ± w}, w real or purely imaginary
              — real strays already occur here                    (Theorem J′)
ord₁F ≥ 3  is necessary and sufficient for a genuinely complex
              off-critical quadruple                              (Theorem J)
```

So the pole order at `s=1` is an exact budget, and a real stray costs **half** what a complex one
costs. In particular the hypotheses **(H1)**–**(H3)** do not even exclude a Landau–Siegel zero: a
real zero in `(½,1)` is available at the minimum possible violation of **(H4)**.

A deformation may also *remove* a zero of `ζ`. Such a term carries a **positive** coefficient at a
frequency other than `½`, which would be a pole of `F`; it is admissible precisely because `ζ`
already vanishes there, so the pole is cancelled and entirety survives. It therefore **refunds** one
budget unit, and the law in general reads

```text
ord₁F - 1  =  I - R,      I = inserted, R = removed, both by frequency pairs.
```

The refund is effective, and it collapses the graded picture.

**Theorem R (refunded complex stray).** Let `γ` be the ordinate of any zero of `ζ` on the critical
line — Hardy's theorem provides infinitely many, unconditionally — let `a ∈ (0,¼]` and
`ρ = ½+a+iγ`. Put

```text
d(u) = (e^u+1) + 2e^{u/2}cos(γu) - 2cos(γu)(e^{(½+a)u} + e^{(½-a)u}) = 2e^{u/2}h(u),
h(u) = cosh(u/2) + cos(γu)(1 - 2cosh(au)).
```

Then `d ≥ 0`, its transform is reflection antisymmetric with residue `1` at `s=1`, and

```text
F(s) = ζ(s)·(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄) / [ ((s-½)² + γ²)·s(s-1) ]
```

satisfies **(H1)**, **(H2)**, **(H3)**, has a pole of order **two** at `s=1`, and has zeros
`ρ, ρ̄, 1-ρ, 1-ρ̄` that are neither real nor critical. Its completion
`(s(s-1))²π^{-s/2}Γ(s/2)F(s)/2 = ξ(s)(s-ρ)(s-ρ̄)(s-1+ρ)(s-1+ρ̄)/((s-½)²+γ²)` is entire because `ξ`
vanishes at `½ ± iγ`.

*Proof.* Since `cosh(au) ≥ 1`, the bracket `1-2cosh(au)` is at most `-1 < 0`, so `cos(γu) ≤ 1` gives
`h(u) ≥ cosh(u/2) + 1 - 2cosh(au)`. Now `cosh(u/2)+1 = 2cosh²(u/4)` and, for `|a| ≤ ¼` and `u ≥ 0`,
`cosh(au) ≤ cosh(u/4)`, so

```text
h(u) ≥ 2cosh²(u/4) - 2cosh(u/4) = 2cosh(u/4)(cosh(u/4) - 1) ≥ 0.
```

Antisymmetry is Lemma 2.1 termwise; the residue at `s=1` is `1` because the trace condition
`1 + 1 - 1 - 1 = 0` leaves exactly one unit at the frequency `½`. ∎

The sharp range is `|a| ≤ 1/(2√2)`: comparing Taylor coefficients,
`cosh(u/2)+1-2cosh(au) = Σ_{n≥1} u^{2n}(4^{-n} - 2a^{2n})/(2n)!`, nonnegative for every `n` iff
`a² ≤ ⅛`; and `h` does take negative values for `a = 0.4`.

**Corollary (sharp threshold).** For systems with `dΨ_F ≥ dΨ_ζ` satisfying **(H1)**–**(H3)**:

```text
ord₁F = 1   ⟺   F = ζ                                               (Theorem M)
ord₁F = 2   already admits every kind of off-critical zero:
              a real pair, unrefunded                               (Theorem J′)
              a genuinely complex quadruple, refunded once          (Theorem R)
```

There is no intermediate regime: **the simple pole is not one hypothesis among several graded ones,
it is the whole of the remaining content.** Note also that `ord₁F = 1` cannot be reached by a
refund, because the trace condition would then leave no positive coefficient at `½`, and the
leading-frequency argument of Theorem I forbids a correction whose top real part is attained only by
non-real frequencies with negative coefficients.

**Theorem P (realization).** Let `Z` be any finite multiset in the closed critical strip, closed
under `s ↦ 1-s` and under conjugation, with even multiplicity at `s = ½`, and put `|Z| = 2m`. Then

```text
F(s) = ζ(s)·∏_{ρ∈Z}(s-ρ) / (s(s-1))^m,     (s(s-1))^{m+1}π^{-s/2}Γ(s/2)F(s)/2 = ξ(s)∏_{ρ∈Z}(s-ρ)
```

satisfies **(H1)**, **(H2)**, **(H3)**, has `ord₁F = 1 + m = 1 + ½|Z|`, and its zero set is that of
`ζ` together with `Z`. If moreover `Z ⊂ {|s-½| ≤ ½}` the prime measure is nonnegative, so `F` is a
genuine Beurling system.

*Proof.* Everything reduces to one inequality: for `|a| ≤ ½` and `u ≥ 0`,

```text
cos(γu)(e^{(½+a)u}+e^{(½-a)u}) = 2e^{u/2}cos(γu)cosh(au) ≤ 2e^{u/2}cosh(u/2) = e^u + 1,
```

because `cosh` is even and increasing on `[0,∞)`. So the unit correction attached to *any* point of
the closed strip is a nonnegative measure — **with no restriction on the ordinate** — and a finite
divisor is a nonnegative integer combination of such units. Antisymmetry is Lemma 2.1 termwise. The
residue at `s=1` is the coefficient at the frequency `½`, which the trace condition makes equal to
`m`. The disc condition `|w| ≤ ½` makes every Taylor coefficient of
`cosh(u/2) - Re cosh(wu) = Σ_{n≥1}[(¼)ⁿ - Re w^{2n}]u^{2n}/(2n)!` nonnegative, hence `d(u)/u`
nondecreasing, hence Lemma 6.1 applies. ∎

Theorem P says the space of **(H1)**–**(H3)** systems dominating `ζ` is, as a graded object, the
free commutative monoid on strip divisors, graded by `ord₁F - 1`. Theorem M is the statement that
the degree-zero part is a single point, `ζ`.

## 5c. Theorem M: unconditional rigidity

Theorems K, K′, K″ needed absolute summability of the deformation, and an attainment or a
frequency-structure hypothesis. All of that is removable; the right tool is Landau's theorem on the
abscissa of convergence of a Laplace–Stieltjes transform of a **nonnegative** measure.

**Lemma M.1 (Landau's exchange identity).** For a nonnegative Borel measure `ν` on `(0,∞)`, every
real `a` and every `t ≥ 0`,

```text
∫₀^∞ e^{-(a-t)u} dν(u)  =  Σ_{k≥0} (t^k/k!) ∫₀^∞ u^k e^{-au} dν(u)
```

as an identity in `[0,∞]`. Both sides are simultaneously finite or infinite.

*Proof.* `e^{-(a-t)u} = e^{-au}Σ_k (tu)^k/k!` with all terms nonnegative; Tonelli. ∎

**Corollary M.2.** If `c` is the abscissa of `ν` then, for `a > c`, the Taylor series of the
transform at `a` has radius of convergence exactly `a - c`. Hence the transform admits no analytic
continuation to any disc about `a` of radius exceeding `a - c`, and `z = c` is a singularity.

**Theorem M.** Let `ν ≥ 0` be a nonzero measure on `(0,∞)` whose Laplace transform `N` is
meromorphic on `ℂ`, with abscissa `c`. Then `z = c` is a **real pole** of `N`, and `N(σ) → +∞` as
`σ ↓ c`, so the leading coefficient there is positive. If instead `N` is entire, then `N ≡ 0`:
indeed `|N(z)| ≤ N(Re z)` because `ν ≥ 0`, and `N(σ) → 0` as `σ → +∞` while antisymmetry gives the
same as `σ → -∞`, so `N` is a bounded entire function vanishing at infinity.

*Proof.* If `N` were analytic at `c`, it would be analytic on a disc `B(a, r)` with
`a = c + δ` and `r > δ` (take `r = 1.2δ`), so its Taylor series at `a` would converge at radius
`1.1δ > δ = a - c`, contradicting Corollary M.2. A singularity of a meromorphic function is a pole;
`N(σ) = ∫e^{-σu}dν ≥ 0` on `(c,∞)` and is unbounded at a pole, so it tends to `+∞`. ∎

**Corollary M.3 (rigidity of `ζ`).** Let `F` be the zeta function of a generalized system with
`dΨ_F ≥ dΨ_ζ` satisfying **(H2)**, with `F` meromorphic. Put `ν = dΨ_F - dΨ_ζ ≥ 0` and
`N = M_F - M_ζ`, which is reflection antisymmetric and meromorphic. If `ν ≠ 0`, the real pole
supplied by Theorem M is:

* `s = 1`, forcing `ord₁F ≥ 2` — **(H4)** fails (this is Theorems J and J′);
* a real pole of `F` in `(0,1)` — **(H3)** fails (this is Theorem H);
* a real point where `ζ` has a zero and `F` does not — impossible in `(0,1)` by Corollary 3.1, and
  at `s = -2k` it leaves the `Γ(s/2)` pole uncancelled, so **(H3)** fails;
* `s = 0`, where the residue of `N` is `-ord₀F ≤ 0`, excluded by positivity of the leading
  coefficient.

Hence **(H1)–(H4) force `F = ζ`** on the whole class `dΨ_F ≥ dΨ_ζ`. No summability, no attainment,
no cone structure: Theorem M supersedes K, K′ and K″, and explains H, J, J′ uniformly — each is
forced to spend a real pole, and the two places it may be spent are exactly the two hypotheses it
violates.

## 5d. Positivity certificates for the reflection cone

Every nonnegativity statement above is an instance of one algebraic identity. For all real
`α, a, γ, u`,

```text
cosh(αu) - cosh(au)cos(γu) = 2 sinh(((α+a)/2)u)·sinh(((α-a)/2)u) + 2 cosh(au)·sin²((γ/2)u).
```

For `|a| ≤ α` both summands are separately nonnegative on the whole line: `sinh(pu)sinh(qu) ≥ 0`
whenever `p,q ≥ 0`, since both factors carry the sign of `u`. So `Λ`-positivity is witnessed by an
identity, not by an estimate, and the witness splits the cone element into a purely **hyperbolic**
part and a purely **oscillatory** part. Theorems H, J, J′ and P are all corollaries.

The refunded element has the analogous certificate

```text
cosh(u/2) - (2cosh(au) - 1)cos(γu) = [cosh(u/2) + 1 - 2cosh(au)] + 2(2cosh(au) - 1)·sin²((γ/2)u),
```

with `cosh(u/2)+1-2cosh(au) = 2[cosh²(u/4) - cosh(au)] ≥ 0` for `|a| ≤ ¼`, and with the refund
weight positive by the sum of squares `(2cosh(au) - 1)e^{au} = (e^{au} - ½)² + ¾`.

Both certificates are **sums of Hermitian squares of exponential polynomials**:
`cosh(au) = ½(e^{au/2})² + ½(e^{-au/2})²`, `2sin²(γu/2) = |e^{iγu/2} - e^{-iγu/2}|²/1`,
`sinh(pu)sinh(qu)` is such a product, and dividing the square `(e^{au}-½)²+¾` by `(e^{au/2})²`
gives another. This raises the natural structural question.

**The Positivstellensatz problem for the reflection cone.** Let
`𝒞 = {h = Σ_j t_j cosh(w_j u) : h ≥ 0 on ℝ}`, the cone of `Λ`-positive reflection-antisymmetric
corrections. Is every `h ∈ 𝒞` a finite sum of Hermitian squares of exponential polynomials?

* **All frequencies real.** Yes. Setting `z = e^{δu}` with `δ` a common divisor reduces `h` to a
  Laurent polynomial nonnegative on `(0,∞)`; Pólya–Szegő gives `h = σ₀(z) + zσ₁(z)` with `σ_i`
  sums of squares, and `z = (e^{δu/2})²` is itself a square.
* **All frequencies purely imaginary.** Yes, by Fejér–Riesz.
* **Mixed.** The frequency data generate a group whose closure is the **cylinder** `ℝ × S¹`, a
  genuinely two-dimensional real variety, where sums of squares are known to be strictly smaller
  than nonnegative polynomials in general (Hilbert 1888; Rudin's two-variable counterexamples to
  Fejér–Riesz). Whether the specific cone `𝒞` escapes this is open. A negative answer would say
  that `Λ`-positivity is **not semidefinite-representable**, so no fixed-degree SDP relaxation can
  decide it — a structural limitation on every numerical approach to the Beurling constraint.

## 5e. Theorem X: Λ-positivity is not semidefinite representable

The Positivstellensatz problem posed above has a negative answer, and the obstruction is explicit.

Let `Γ` be the additive group generated by all frequencies appearing in a putative representation
`h = Σ_k |q_k|²`. The map `μ ↦ (Re μ, Im μ)` embeds `Γ` in `ℝ²`, so for every `(s,φ) ∈ ℝ²`

```text
χ_{s,φ}(μ) := exp(Re(μ)·s + i·Im(μ)·φ)
```

is a character of `Γ` satisfying `χ_{s,φ}(μ̄) = conj χ_{s,φ}(μ)`. Substituting it for `e^{μu}` sends
each `q_k` to a function of `(s,φ)` and each `|q_k|²` to its squared modulus. Hence a
sum-of-squares certificate forces the **cylinder lift** — replace `e^{au}` by `e^{as}` and `e^{iγu}`
by `e^{iγφ}` — to be nonnegative on all of `ℝ²`, not merely on the diagonal `φ = s` where it
reproduces `h`.

**Theorem X.** Put

```text
h(u) = ½cosh(2u) - 5cosh u - cos u + 15/2 = (1 - cos u) + (cosh u - 2)(cosh u - 3).
```

Then `h ≥ 0` on `ℝ`, so `h` lies in the reflection cone; but `h` is not a finite sum of Hermitian
squares of exponential polynomials.

*Proof.* If `cosh u ≤ 2` or `cosh u ≥ 3` both summands are nonnegative. If `2 < cosh u < 3` then
`cosh 1 < 2 < cosh u` and `cosh u < 3 < cosh 2` give `1 < |u| < 2`, so `sin(|u|/2) ≥ sin(½) >
½ - (½)³/4 > 7/15` and `1 - cos u = 2sin²(u/2) > 2(7/15)² > ¼`, while
`(cosh u - 2)(cosh u - 3) ≥ -¼` because `(y - 5/2)² ≥ 0`. Hence `h > 0` there.

For the second claim, the cylinder lift at phase `0` is `(cosh s - 2)(cosh s - 3)`. At
`s = log((5+√21)/2)` one has `e^{s} = (5+√21)/2`, `e^{-s} = (5-√21)/2`, so `cosh s = 5/2` and the
lift equals `-¼ < 0`. A sum of squared moduli is nonnegative everywhere, so no such representation
exists. The point is genuinely off the diagonal: phase `0` on the diagonal means `s ∈ 2πℤ`, where
`cosh s` is `1` or at least `cosh 2π`, never in `(2,3)`. ∎

Multiplying by `1 - cos(γ'u)` for a fresh frequency `γ'` produces a witness satisfying the trace
condition `h(0) = 0` as well, evaluating the extra phase at `π` to keep the lift negative.

So the cone of `Λ`-positive reflection corrections is **strictly larger** than the cone of sums of
Hermitian squares. Consequently `Λ`-positivity is not semidefinite representable: no
fixed-degree SDP relaxation, and no Galerkin/moment hierarchy built from squares, is complete for
it. Positivity certificates in this subject must use the hyperbolic–oscillatory correlation along
the diagonal, exactly as the certificates of §5d do, and cannot be obtained from a
frequency-by-frequency semidefinite relaxation.

## 5f. Theorem B: the Weil index and the pole-order budget are the same integer

The classification above is a statement about **linear** positivity. It has an exact counterpart in
the **quadratic** theory, and the two costs coincide.

Order the divisor by the orbits of `w = ρ - ½` under `w ↦ ±w, ±w̄`. Writing
`W(h) = Σ_ρ Ĥ(w_ρ)Ĥ(-w_ρ)` for the Weil form, each orbit contributes an independent block in the
values of `Ĥ` at its points:

```text
critical orbit {iγ,-iγ}          2|Ĥ(iγ)|² = 2(X² + Y²)        PSD,            index 0, size 2
real orbit     {a,-a}            2XY                            signature (1,1), index 1, size 2
generic orbit  {w,-w,w̄,-w̄}      4(Z₁W₁ - Z₂W₂)                 signature (2,2), index 2, size 4
```

with the explicit diagonalizations `2XY = ½[(X+Y)² - (X-Y)²]` and
`4(Z₁W₁ - Z₂W₂) = [(Z₁+W₁)² - (Z₁-W₁)²] - [(Z₂+W₂)² - (Z₂-W₂)²]`, the explicit half-dimensional
PSD subspaces `Y = X` resp. `W₁ = Z₁, W₂ = -Z₂`, and the explicit negative directions `Y = -X` resp.
`W₁ = -Z₁, W₂ = Z₂`. Each off-critical orbit therefore costs exactly half its size, which recovers
Bombieri's count: for a truncation large enough, the number of negative eigenvalues of the Weil
functional is one half the number of zeros violating the Riemann hypothesis (Bombieri, *Remarks on
Weil's quadratic functional in the theory of prime numbers, I*).

**Theorem B (budget–index identity).** Let `F` be a system in the classification of §5b–§5e, with
inserted divisor `Z`, `|Z| = 2m`, whose off-critical part has size `2j`. Then

```text
ind₋(W_F) - ind₋(W_ζ)  =  j  ≤  m  =  ord₁F - 1,
```

with equality exactly when every inserted zero is off-critical.

*Proof.* The right-hand equality is Theorem P: the pole order at `s=1` counts half the inserted
divisor. The left-hand equality is the orbit decomposition above applied to `Z`, the critical orbits
contributing PSD blocks and each off-critical orbit contributing half its size. The inequality is
`2j ≤ 2m`, the off-critical part being a subdivisor. ∎

So the **linear** cost of a deformation — the order of the pole it must buy at `s = 1` — dominates
its **quadratic** cost — the number of negative eigenvalues it adds to the Weil form — and the two
agree exactly on purely off-critical insertions. The classification's grading and Bombieri's index
are one and the same invariant, read once through `Λ`-positivity and once through Weil positivity.
Theorem M is the statement that the invariant vanishes only at `ζ`.

## 6. The monotone Möbius criterion

**Lemma 6.1.** If `g : [0,∞) → [0,∞)` is nondecreasing then for `u > 0`

```text
(T^{-1}g)(u) = Σ_{k≥1} μ(k)k^{-2} g(u/k) ≥ (2 - π²/6)·g(u) > 0.34·g(u) ≥ 0.
```

*Proof.* The `k=1` term is `g(u)`; for `k ≥ 2`, `0 ≤ g(u/k) ≤ g(u)`, so the tail is at most
`g(u)Σ_{k≥2}k^{-2} = g(u)(π²/6 - 1)` in absolute value, and `1-(π²/6-1) = 2-π²/6`. ∎

This replaces the sign analysis of an alternating series by one monotonicity statement, and is what
makes the *prime* measure (not merely `dΨ`) nonnegative in Theorems H and J.

## 7. Theorem K: rigidity of the full conjunction

**Theorem K.** Let `h(u) = Σ_j t_j cosh(w_j u)` be a finite reflection-antisymmetric correction to
the von Mangoldt measure of `ζ`. If the perturbed system satisfies **(H1)**–**(H4)**, then `h ≡ 0`;
that is, `ζ` admits no nonzero rational-gauge deformation preserving all four hypotheses.

*Proof.* **(H4)** says the coefficient at `w = ½` vanishes. Local finiteness gives
`h(0) = Σ_j t_j = 0`. By Theorem I, **(H1)** forces a real `w_{j₀} = α` with `t_{j₀} > 0`, hence a
real pole of the completed function at `½ ± α`. By Corollary 3.1 and **(H3)**, `α = ½`, excluded by
**(H4)**. ∎

Theorems H and J show the hypotheses of Theorem K are sharp: relaxing **(H3)** or **(H4)** produces
explicit nonzero deformations.

## 7b. Theorem K′: rigidity for countable deformations

Theorem K is stated for finite rank because Theorem I extracts a *leading trigonometric
polynomial*. That extraction survives infinitely many frequencies, provided the maximal real part
is attained.

**Theorem K′.** Let `h(u) = Σ_{j} t_j cosh(w_j u)` with `Σ_j |t_j| < ∞`, `Re w_j ≥ 0`, the multiset
conjugation-closed with equal coefficients, and suppose

```text
α := max{Re w_j : t_j ≠ 0}   is attained.
```

If `h ≥ 0` on `ℝ` and `h ≢ 0`, then some **real** `w_{j₀} = α` has `t_{j₀} > 0`.

*Proof.* Put `f(u) = h(u)e^{-αu}` for `u ≥ 0`. Then `f ≥ 0` and

```text
|f(u)| ≤ Σ_j |t_j| e^{(Re w_j - α)u} ≤ Σ_j |t_j| < ∞,
```

so `f` is **bounded**. Let `Q(u) = Σ_{Re w_j = α} t_j e^{i Im(w_j)u}`, a real Besicovitch almost
periodic function. Since `cosh(w_j u)e^{-αu} = ½e^{(w_j-α)u} + ½e^{(-w_j-α)u}` and every term with
`Re w_j < α` has vanishing Cesàro mean, dominated convergence (justified by `Σ|t_j| < ∞`, each
Cesàro average being bounded by `|t_j|`) gives

```text
mean(f) = ½·mean(Q) = ½ Σ_{w_j = α real} t_j,      mean(f²) = ¼·mean(Q²) = ¼ Σ_{Re w_j=α} |t_j|²,
```

the last by Parseval for almost periodic functions. If `mean(f) = 0` then, `f` being nonnegative and
bounded, `mean(f²) ≤ ‖f‖_∞·mean(f) = 0`, so `Q ≡ 0`, i.e. the level `α` is empty — contradicting
that `α` is attained. Hence `mean(f) > 0`, which is a sum over **real** `w_j = α`. ∎

**Corollary K′′.** No deformation of `ζ` — finite or countable, absolutely summable, with attained
maximal real part — preserves **(H1)**–**(H4)** unless it is zero. Indeed the real frequency
`w_{j₀} = α > 0` supplied by Theorem K′ is a real pole of the completed function, excluded by
Corollary 3.1 and **(H3)**, while `α = ½` is excluded by **(H4)**.

The one configuration outside the reach of Theorem K′ is a deformation whose inserted zeros have
real parts strictly increasing to an unattained supremum. There `h e^{-α u}` is no longer bounded
for any admissible `α`, and the leading level does not exist.

## 7c. Theorem K″: full rigidity, no attainment hypothesis

Theorem K′ leaves one configuration open: `Re w_j` strictly increasing to an unattained supremum
`α`. Landau's theorem removes it.

**Theorem K″.** Let `h(u) = Σ_j t_j cosh(w_j u)` with `Σ_j|t_j| < ∞`, `0 ≤ Re w_j ≤ α`, the `w_j`
distinct and conjugation-closed with equal coefficients, and **no `w_j` real**. If `h ≥ 0` on
`[0,∞)` then `h ≡ 0`.

*Proof.* Suppose `h ≢ 0` and let `H(z) = ∫_0^∞ h(u)e^{-zu}du`, with abscissa of convergence `σ_c`.
Since `|h(u)| ≤ (Σ|t_j|)e^{αu}` we have `σ_c ≤ α`. The meromorphic continuation of `H` is

```text
H(z) = Σ_j t_j · z/(z² - w_j²),
```

with a simple pole at each `z = w_j` of residue `t_j/2 ≠ 0`; distinctness of the `w_j` prevents
cancellation. A Laplace transform is analytic strictly right of its abscissa, so `σ_c ≥ Re w_j` for
every `j`, whence `σ_c = α`.

Two cases.

*The supremum is attained.* Then `f = h e^{-αu}` is bounded and nonnegative, and by Theorem K′ its
Cesàro mean is `½Σ_{w_j = α real}t_j = 0` because no `w_j` is real; hence `mean(f²) ≤ ‖f‖_∞
mean(f) = 0`, so the level-`α` almost periodic polynomial vanishes identically — contradicting
attainment.

*The supremum is not attained.* Then `Re w_j ↑ α` with `w_j ≠ α`; since `h ≥ 0`, Landau's theorem
makes the real point `z = σ_c = α` a **singularity** of `H`. But the `w_j` are the zeros/poles of a
meromorphic function, hence have no finite accumulation point, so `|Im w_j| → ∞` along the top
sequence and

```text
|z² - w_j²| ≥ |Im(w_j²)| = 2|Re w_j||Im w_j| → ∞
```

uniformly for `z` in a neighbourhood of `α`. The series therefore converges locally uniformly
there, so `H` is analytic at `α` — contradicting Landau. ∎

**Corollary K‴ (rigidity of `ζ`).** `ζ` admits no nonzero countable, absolutely summable,
reflection-antisymmetric deformation of its von Mangoldt measure preserving **(H1)**–**(H4)**.
Indeed **(H3)** and Corollary 3.1 forbid a real frequency other than `w = ½`, and **(H4)** forbids
`w = ½`; Theorem K″ then forces the deformation to vanish.

## 8. Theorem N: the ceiling of linear positivity

**Theorem N.** Let `dΨ ≥ 0` and let `φ ≥ 0` with `∫φ(t)e^{-t/2}dt < ∞`. Then convolution with `φ`
multiplies the coefficient of each frequency `w` in the expansion of `dΨ` by
`Φ(w) = ∫φ(t)e^{-wt}dt`, and `Φ(½) > 0`. Consequently **no positivity-preserving operation can
cancel the leading exponential `e^{u/2}`**, and every inequality obtained from `Λ ≥ 0` alone has the
form

```text
Σ_ρ Ĝ(w_ρ) ≤ 2Ĝ(½) - W_∞(g),     g ≥ 0 even,   Ĝ(w) = ∫g(u)cosh(wu)du,
```

in which the pole term `Ĝ(½)` dominates every zero term, since `|Ĝ(w_ρ)| ≤ Ĝ(Re w_ρ) ≤ Ĝ(½)` with
`|Re w_ρ| < ½`.

*Proof.* Immediate from `Φ(½) = ∫φ e^{-t/2} > 0` for `φ ≥ 0, φ ≢ 0`, and from monotonicity of
`a ↦ ∫g(u)cosh(au)du` for `g ≥ 0`. ∎

Specializing `g` to `e^{-c|u|}(1+\cos ξu)` recovers `2M(σ)+2\operatorname{Re}M(σ+iξ) ≥ 0` and its
optimizations, the `3+4\cos θ+\cos 2θ` family — i.e. classical zero-free regions. Theorem N says
this is the ceiling: linear positivity of `Λ` sees the pole, hence PNT-strength information, and
never the `√x` fluctuation in which the Riemann hypothesis lives. Reaching that requires *quadratic*
positivity, i.e. Weil's criterion, which is itself equivalent to the Riemann hypothesis.

## 9. The independence table

```text
             (H1) Λ≥0   (H2) FE   (H3) entire   (H4) simple pole   critical line?
   drop H1        —        ✓          ✓               ✓            NO   Davenport–Heilbronn 1936;
                                                                        Epstein (class number >1);
                                                                        Hurwitz, Shintani
   drop H2        ✓        —          ✓               ✓            NO   Diamond–Montgomery–Vorhauer
                                                                        2006; Zhang 2007;
                                                                        Neamah–Hilberdink 2020
   drop H3        ✓        ✓          —               ✓            NO   Theorem H  (new)
   drop H4        ✓        ✓          ✓               —            NO   Theorem J  (new)
   all four       ✓        ✓          ✓               ✓            YES for EVERY countable
                                                                        absolutely summable
                                                                        deformation of ζ
                                                                        (Theorems K, K′, K″)
```

## 10. What remains

The Riemann hypothesis is exactly the infinite-rank case of Theorem K. The obstruction to extending
Theorem I to that case is structural and identified: for a *deformation* the correction is
absolutely continuous, so nonnegativity of its density is a genuine pointwise constraint and the
leading-frequency argument applies; for a system in its own right the measure is singular (atoms at
generalized prime powers) and the frequency expansion is only distributional, so no leading level
exists. Equivalently, the "trace" `Σ_j t_j = 0` that makes finite rank rigid diverges for the actual
system, the divergence being absorbed by the archimedean kernel. That renormalization is the
substance of the problem.

Theorem N says that any resolution must use more than the nonnegativity of `Λ`; Theorems H and J say
that adding the functional equation, entirety, and the Euler product is still not enough unless the
pole order is also fixed; and Theorem K says that once all four are fixed, no finite deformation
survives.

## References

- E. Bombieri, *Problems of the Millennium: the Riemann Hypothesis*, Clay Mathematics Institute.
- American Institute of Mathematics, *The Riemann Hypothesis* (problem list).
- H. Davenport and H. Heilbronn, *On the zeros of certain Dirichlet series*, J. London Math. Soc. 11
  (1936).
- H. G. Diamond, H. L. Montgomery and U. Vorhauer, *Beurling primes with large oscillation*, Math.
  Ann. 334 (2006), 1–36.
- W.-B. Zhang, *Beurling primes with RH and Beurling primes with large oscillation*, Math. Ann. 337
  (2007), 671–704.
- T. W. Hilberdink and M. L. Lapidus, *Beurling zeta functions, generalised primes, and fractal
  membranes*, Acta Appl. Math. 94 (2006).
- A. Connes and C. Consani, *Weil positivity and trace formula: the archimedean place*, 2020.

## Machine verification

All statements above are formalized in Lean 4 over Mathlib and compile with only the standard
axioms `propext`, `Classical.choice`, `Quot.sound`:

```text
GaloisForLFunctions/HTGeometry/CriticalClockSourceUniversality.lean
GaloisForLFunctions/HTGeometry/MonotoneMobiusPositivity.lean       -- Lemma 6.1
GaloisForLFunctions/RHTower/LambdaPositiveFunctionalEquationOffLine.lean  -- Theorem H
GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean          -- Theorem J
GaloisForLFunctions/RHTower/CCMCriticalClockDivisorBlindness.lean
```
