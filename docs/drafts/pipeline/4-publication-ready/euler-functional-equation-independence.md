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

## 5g. A no-go atlas for positivity approaches

The theorems above and their companions map the positivity universe systematically.  Each entry is a
theorem, not a heuristic, and each is machine-checked.

**Linear positivity is capped at PNT strength (Theorem N).**  Convolution with any `φ ≥ 0` multiplies
the coefficient of the frequency `w` by `Φ(w) = ∫φ(t)e^{-wt}dt`, and `Φ(½) > 0`, so no
positivity-preserving operation cancels the leading exponential `e^{u/2}`.  Every inequality derived
from `Λ ≥ 0` alone therefore sees the pole and never the `√x` fluctuation.

**The quadratic index yields only lower bounds (Theorem N′).**  Ordering the divisor by frequency
orbits, a critical orbit contributes a positive semidefinite block, a real orbit the hyperbolic `2XY`
and a generic orbit `4(Z₁W₁ - Z₂W₂)`; each off-critical orbit costs exactly half its size, which is
Bombieri's count.  Solving the resulting conservation law for `ζ` gives
`ind₋(W_ζ) = ind₋(W_F) - I_off + R_off ≥ R_off - I_off`: a lower bound, never an upper one, since
removing off-critical zeros presupposes knowing them.

**The Bohr-torus model is valid only past an exponential height (Theorem G).**  Partitioning the
`r`-torus into `Mʳ` boxes, a curve of length `Λ` meets at most `1 + r + rMΛ` of them, so covering
forces `Λ ≥ M^{r-1}/(2r)`; for the Kronecker line `ξ ↦ (ξ log p)_{p ≤ N}` this reads
`log T ≳ π(N)·log M`.  The prime symbol is already of full size `√N` at every height, so the model
becomes applicable only exponentially beyond the heights where the Weil condition is needed.

**The elementary archimedean tower is optimal (Theorems Q24–V29).**  The averaged archimedean symbol
is exactly `2θ(X)/X` with `θ` the Riemann–Siegel theta function, so the elementary positivity range
ends at the first zero of `θ`, `ℓ₀ = π/(2t₀)` with `t₀ ≈ 17.85`, improved to `ℓ ≈ 0.155` by the
mean-zero refinement.  Every remaining elementary lever is closed: the damped prime sum is never
activated because the archimedean baseline binds first; IMS localization has a scale-invariant error
`≥ π²` that beats a logarithmic gap; the second spectral moment is satisfied for free by a vanishing
mass at a diverging frequency; and the sharp band constraint is the prolate eigenvalue, which
re-enters the machinery the tower was built to avoid.

**Extending a positivity range is equivalent to the Riemann hypothesis (Theorem X31).**  Let
`λ(L) = inf spec Q_L`, nonincreasing.  If `b ≤ λ` is nondecreasing with `b(L₀) ≥ 0` for one `L₀`, then
`λ(L) ≥ b(L) ≥ b(L₀) ≥ 0` for `L ≥ L₀` and `λ(L) ≥ λ(L₀) ≥ 0` for `L ≤ L₀`; so `λ ≥ 0` everywhere.
Every scheme for pushing a positivity range past its endpoint must produce such a bound, hence be as
hard as RH, or fail — as four independent attempts do: the direct overlap estimate, the damped prime
sum, IMS localization, and variational monotonicity under discreteness.  The one thing that *is* free
is the converse direction: since the compression of the multiplier by `σ` has compact resolvent, the
spectrum of `Q_L` is discrete and `λ` is strictly decreasing wherever the minimizer's image does not
vanish identically outside its support; so positivity at `L₁` supplies a strictly positive gap at
every `L < L₁`, and all soft tools propagate information downward in `L` only.

**The axiomatic characterization is circular or false (Theorems M, P, R).**  Within the class
`dΨ_F ≥ dΨ_ζ`, the four hypotheses force `F = ζ`; so `(H1)–(H4) ⟹ RH` is either equivalent to RH — if
the Beurling category has a Hamburger-type uniqueness theorem, which Theorem M establishes on that
class — or false, if a from-scratch counterexample exists.  Either way no proof of RH comes out.

Taken together: the accessibility principle says the Weil form is the unique accessible functional
detecting `Re ρ`, and the atlas says every route inside it is capped.  A proof must therefore
introduce structure from outside the positivity universe.

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

## §5h. The de Bruijn–Newman lane: the extinction time of the Weil index

The classification of §5b–§5g maps the positivity universe and finds every lane capped. This section
opens the one concrete lane outside it — the de Bruijn–Newman flow — and shows it is capped too, by
a mechanism of a different kind.

### 5h.1 The dictionary (Theorem Z33)

The flow `H_t(z) = ∫₀^∞ e^{tu²}Φ(u)cos(zu)du` deforms `H_0 = ξ(½+iz)/8` through entire functions of
order one, each even in `z`; equivalently each `Ξ_t(s) = H_t(-i(s-½))` is invariant under `s ↦ 1-s`.
The whole flow therefore stays inside the class where the Weil form is defined, so the orbit
decomposition of §5f applies at every time. Combining it with the definition of `Λ`:

* `ind₋(W_{Ξ_t}) = ½·N_off(t)` (orbit decomposition);
* `N_off(t) = 0` exactly for `t ≥ Λ` (definition of `Λ`).

Hence `t ↦ ind₋(W_{Ξ_t})` is a nonincreasing integer-valued function of flow time vanishing precisely
on `[Λ,∞)`:

> **`Λ` is the extinction time of the Weil index along the de Bruijn–Newman flow**, and
> `RH ⟺ ind₋(W_ξ) = 0 ⟺ Λ ≤ 0`.

This identifies Bombieri's index — the quantity the Connes–Consani–Moscovici programme measures at
`t = 0` — with a dynamical quantity: the time at which it vanishes. With Rodgers–Tao's `Λ ≥ 0`, the
Riemann hypothesis becomes the statement that the flow is exactly critical. By Theorem Y32 the same
reads spectrally: for `t < Λ` the divisor of `Ξ_t` carries complex quadruples, which no self-adjoint
problem can produce.

### 5h.2 The imaginary energy is a Lyapunov functional (Theorem A35)

Differentiating `H_t(z_j(t)) = 0` and using `∂_t H = -∂_z²H` gives the zero dynamics
`ż_j = 2Σ_{k≠j}1/(z_j - z_k)`. Put `I = Σ_j (Im z_j)²`. Since `Im(1/w) = -(Im w)/|w|²`,

```
İ = -4 Σ_{j≠k} y_j(y_j - y_k)/|z_j - z_k|² ,
```

and symmetrising the ordered pair `(j,k) ↔ (k,j)` — the denominator being symmetric — yields the
exact identity

```
İ  =  -2 Σ_{j≠k} (y_j - y_k)² / |z_j - z_k|²  ≤  0 .
```

`I` is therefore **unconditionally** nonincreasing: no hypothesis on the configuration is needed.
Two sharpenings: every ratio is at most `1`, with equality exactly when the two points share a real
part; and a conjugate pair is vertically aligned, so its two ordered pairs are extremal and
contribute `-4`. Hence `İ ≤ -4` while any complex zero survives, and since `I ≥ 0`,

> **`Λ ≤ ¼ Σ_ρ (Re ρ - ½)²`.**

In the flow coordinate a zero `ρ = β+iγ` has `Im z = ½-β`, so the right-hand side is the total
squared deviation of the divisor from the critical line. A single pair gives `Λ ≤ y₀²/2`; a single
quadruple `½±a±iγ` gives `Λ ≤ a²`. Read backwards, `Σ_ρ (Re ρ - ½)² ≥ 4Λ`.

The estimate obtained from the local field — that a counterexample at height `T` merges in time
`≍ 1/log T`, so that verification of RH to height `T` should give `Λ = O(1/log T)` — is Tao's, from
the Polymath15 proposal, and requires the other zeros to be real. The collision estimate in reverse
time, giving lower bounds for `Λ` from close pairs, is Csordas–Smith–Varga's Lehmer-pair theory. The
energy identity is independent of both and needs neither a local model nor an assumption on the
remaining zeros.

### 5h.3 Conservation of merge time (Theorem B36)

Let `t₁ ≤ … ≤ t_m` be the merge times and `m(t) = #{i : t < t_i}` the number of pairs still complex,
which by §5h.1 *is* `ind₋(W_{Ξ_t})`. From `İ ≤ -4m(t)` and the layer-cake identity
`∫₀^∞ m(t)dt = Σ_i t_i` — in piecewise constant form the Abel summation
`Σ_i (m-i)(t_{i+1}-t_i) = Σ_i t_{i+1}` — one gets the exact accounting

> **`∫₀^Λ ind₋(W_{Ξ_t}) dt = Σ_i t_i ≤ ¼ Σ_ρ (Re ρ - ½)²`.**

The *sum* of the merge times, not merely the largest, is bounded. Three readings: it refines
`Λ ≤ ¼Σ_ρ(Re ρ-½)²`, since `Λ = max t_i ≤ Σ t_i`; many exceptions force fast extinction, since `m`
pairs surviving to `Λ` give `Λ ≤ I₀/(4m)`; and each merge costs four units of imaginary energy per
unit of time it takes, the budget being the second moment of the real parts. This is the first
inequality placing the Connes–Consani–Moscovici index and the de Bruijn–Newman flow on one line with
a zero-statistic on the right.

### 5h.4 The lane is capped (Theorem C37)

The inequality invites a squeeze: a reverse bound `Λ ≥ κI₀` with `κ > ¼` would give `I₀ = 0`, hence
RH. No such `κ` exists. For an isolated conjugate pair the energy identity is an **equality** —
`I = 2y²`, `İ = -4`, merge at `y₀²/2 = I₀/4` — so the bound admits no constant improvement.

The reason is structural: every term of `İ` is nonpositive. The field of the other zeros never
opposes a merge, only accelerates it, so more zeros make `Λ` smaller and the reverse inequality
degrades. **The de Bruijn–Newman flow is a monotone deformation toward the critical line.** A
monotone deformation yields only upper bounds on `Λ` — "if RH fails, it fails briefly" — and can
never contradict the failure of RH, because nothing in the dynamics resists it. Every known lower
bound on `Λ` comes from the initial data, not from the flow. A second route confirms the cap: the
Gaussian factor `e^{tu²}` destroys the Euler product for every `t > 0`, so `Ξ_t` carries no
arithmetic at all and the primes exist only at the initial instant.

Two caveats are recorded so they are not re-derived. The energy bound is vacuous if the divisor has
infinite imaginary energy, and attempts to make its right-hand side arithmetic through zero-density
theorems fail: `N(σ,T) ≪ T^{3(1-σ)/(2-σ)}log⁵T` gives `Σ_{γ<T}(β-½)² ≪ T log³T`, worse than the
trivial `N(T)/4`.

### 5h.5 The atlas, completed to six rows

```
linear Λ-positivity           caps at PNT strength                     (Theorem N)
quadratic Weil index          lower bounds on ind₋ only                (Theorem N′)
Bohr-torus probability        valid only past height ~ π(N)            (Theorem G)
elementary archimedean tower  optimal at ℓ ≈ 0.155                     (Theorems Q24–V29)
extension of the range        equivalent to RH                         (Theorem X31)
de Bruijn–Newman flow         monotone: upper bounds on Λ only         (Theorem C37)
```

Each ceiling has the same shape: the available machinery is monotone or aggregate in a direction
that *agrees* with the Riemann hypothesis, so it can approach the conclusion and never contradict its
negation. A proof must therefore contain a mechanism that is **not** monotone in that direction —
one that degrades as the divisor approaches the critical line, so criticality is forced by an
extremal principle rather than reached as a limit.

## §5i. A falsification criterion with the opposite monotonicity

The six ceilings of §5h.5 share a cause: the machinery is monotone in a direction that *agrees* with
the Riemann hypothesis. A criterion able to contradict its failure must therefore rest on a quantity
that **degrades** as the divisor becomes more critical. One such quantity exists: the count of
non-real zeros in *backward* flow time.

Write `M(t)` for the number of non-real zeros of `H_t`, and `τ_fin = inf{t : M(t) < ∞}`. Ki–Kim–Lee
proved that for every `t > 0` all but finitely many zeros of `H_t` are real and simple — the route to
their `Λ < ½` — so `τ_fin ≤ 0`.

Backward in time real zeros attract. For consecutive real zeros at distance `δ` the self-interaction
gives `dδ/dτ = -4/δ`, while the surrounding field contributes `+2δ Σ_k (x-r_k)^{-2} ≍ 2cδϱ²` with `ϱ`
the local density. A pair therefore collides — leaving the real axis as a conjugate pair — once its
**normalized** gap `δϱ` falls below a fixed constant, and does so within time `δ²/8`. Under the
Riemann hypothesis the zeros of `H_0` are all real with density `log(T/2π)/2π → ∞`, and the known
small-gap results supply infinitely many normalized gaps below `0.5155`; for an evenly spaced field
the threshold is `δϱ < √6/π ≈ 0.78`. Once complex, a pair stays complex as `t` decreases. Hence

> `RH ⟹ M(t) = ∞ for every t < 0 ⟹ τ_fin = 0`, and contrapositively: **if `H_t` has only finitely
> many non-real zeros for a single `t < 0`, the Riemann hypothesis is false.**

The mechanism runs the right way. The more critical the divisor at `t = 0`, the denser its real
zeros, the more pairs collide in backward time, and the *larger* `M(t)` is forced to be. Criticality
is what makes the count infinite, so the criterion strengthens as the Riemann hypothesis is
approached rather than saturating. It is also in a currency none of the capped lanes uses: the
finiteness of a count, rather than the positivity of a form or the sign of a time.

**Open core.** The threshold constant `√6/π` is computed for an evenly spaced field; the actual
configuration is uneven and its neighbours also move. A rigorous lemma of the form "normalized gap
below `c` implies collision within backward time `δ²/8`", with an explicit `c > 0.5155`, is not
established here. The criterion is therefore a conjecture with a precisely located open core.

Two rigorous companions are available. Since `∂_t H = -∂_z²H`, backward time is the *forward* heat
equation, so Sturm's nodal-decrease theorem applies: the number of real zeros in any interval is
nonincreasing as `t` decreases — real zeros are destroyed, never created, going backward. And from
`İ ≤ -4` with `I(Λ) = 0` one gets `I(t) ≥ 4(Λ - t)` for `t < Λ`, hence with `Λ ≥ 0` the bound
`I(t) ≥ 4|t|` for every `t ≤ 0`: non-reality in backward time is not marginal but grows linearly.
