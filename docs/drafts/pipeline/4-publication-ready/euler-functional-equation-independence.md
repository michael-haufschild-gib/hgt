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
GaloisForLFunctions/RHTower/CCM/CCMCriticalClockDivisorBlindness.lean
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

## §5j. The lattice is stationary: what the collision criterion actually needs

### 5j.1 Burgers structure and the damping of the field

Backward flow time is the *forward* heat equation `∂_τ H = ∂_z²H`. With `L = H'/H` and the Riccati
identities `H''/H = L' + L²`, `H'''/H = L'' + 3LL' + L³`, the log-derivative satisfies the viscous
Burgers equation `L_τ = L_zz + (L²)_z`, and therefore the field quantity
`V = -L_z = Σ_k (z-x_k)^{-2} > 0` satisfies

```
V_τ = V_zz + 2 L V_z - 2 V² .
```

The nonlinearity carries a **minus** sign: `V` is damped, not amplified, and comparison with the
uniform solution `v(τ) = v₀/(1+2v₀τ)` of `v' = -2v²` shows decay like `1/τ`. Freezing the field at
its initial value is therefore a legitimate upper bound over a collision interval; the only residual
loss is the first-order transport term.

The frozen-field problem is exactly solvable. For a gap `δ` between consecutive real zeros,
`dδ/dτ = -4/δ + 2δΔ`, so `u = δ²` obeys `u' = 4Δu - 8` with solution
`u(τ) = 2/Δ + (u₀-2/Δ)e^{4Δτ}`, vanishing at `τ* = (4Δ)^{-1}log(2/(2-θ))` where `θ = Δu₀`. The
collision time is finite exactly when `θ < 2`, which is thus the **sharp** threshold.

### 5j.2 The equally spaced configuration is an exact equilibrium

For zeros on a lattice `dℤ` the field sum telescopes:

```
Δ = (2/d²) Σ_{m≥1} 1/(m(m+1)) = 2/d² ,   hence   δ²Δ = 2 ,   dδ/dτ = 0 .
```

A uniformly spaced configuration neither contracts nor expands; it sits exactly at the threshold.
Consequently the collision criterion is **not** "the gap is small" but "the gap beats the lattice".

An explicit sufficient condition follows from Basel's sum. If every *other* consecutive gap is at
least `γ`, the `m`-th neighbour on either side lies at distance at least `mγ` from both endpoints, so
`Δ ≤ 2Σ_{m≥1}(mγ)^{-2} = π²/(3γ²)` and `δ²Δ < 2` holds as soon as

> `δ/γ < √6/π ≈ 0.7797` ,

after which the pair collides by backward time `u₀/(8-4Δu₀)`. The estimate localizes: the tail of the
field beyond the `M`-th neighbour is bounded by the density divided by `M`, so `γ` may be taken to be
the minimum gap in a bounded neighbourhood.

### 5j.3 The corrected open core

This changes the input the criterion of §5i requires. It is **not** enough that infinitely many gaps
be small in absolute or normalized terms: a uniformly spaced cluster, however dense, never collides.
What is needed is infinitely many gaps that are *relatively* small — below `√6/π` times the
surrounding minimum gap. The known small-gap results, bounding the `liminf` of the normalized gap by
`0.5155`, do not have this form, since they say nothing about the neighbours of the small gap.

The corrected statement is therefore:

> The failure of the Riemann hypothesis at negative flow time is governed by **relative** gap
> statistics of the zeros — the distribution of `δ_n / min(δ_{n-1}, δ_{n+1}, …)` — and not by the
> absolute or normalized gap statistics that the literature studies.

That object appears not to have been studied. Identifying it as the governing quantity is the
content of this section.

## §5k. The moment hierarchy and the index as a discriminant sign

### 5k.1 Li coefficients are transported by the flow

With `q_n = Σ_j z_j^{-n}` and `ż_j = 2Σ_{k≠j}(z_j-z_k)^{-1}`, symmetrising the ordered pair with
`(a-b)^{-1}(a^{-3}-b^{-3}) = -(a²+ab+b²)/(a³b³)` gives the closed polynomial law

```
q̇₂ = 2(2q₁q₃ + q₂² - 3q₄) ,   and since H_t is even,   q̇₂ = 2q₂² - 6q₄ .
```

This is the moment form of the Burgers equation `L_τ = L_zz + (L²)_z` of §5j.1. The whole hierarchy of
negative moments — hence, through their explicit polynomial relations, the whole family of Li
coefficients — evolves along the de Bruijn–Newman flow by a closed system of ordinary differential
equations. Li's criterion and the flow are not merely two criteria for the same statement: the Li
coefficients are *transported* by the flow.

The hierarchy is a transport statement and not itself a criterion: holomorphic moments do not detect
the Riemann hypothesis on their own, since a complex quadruple high up contributes *positively* to
`q₂`.

### 5k.2 The sign of the discriminant is the parity of the index

```
conjugate pair x ± iy :  z² - 2xz + (x²+y²) ,  disc = -4y² < 0
real pair      x ± a  :  z² - 2xz + (x²-a²) ,  disc = +4a² > 0
```

Discriminants multiply over factors up to positive squares, so a real divisor with `m` conjugate
pairs has `sign(disc) = (-1)^m`; by the orbit decomposition `m = ind₋(W)`. Hence

> **the sign of the discriminant is the parity of the Weil index.**

The Riemann hypothesis asserts `ind₋(W_ξ) = 0`. A *negative* regularized discriminant for `ξ` would
make `ind₋(W_ξ)` odd, hence nonzero, and disprove it. Parity is strictly weaker than the count, so
this is the weakest falsification target the classification has produced — at the price that the
discriminant of an order-one entire function requires regularization, its sign carried by the
imaginary part of a regularized log-sum modulo `2πi`.

A tempting stronger claim — that the Riemann hypothesis is *not* a holomorphic condition on the
divisor, so that all holomorphic moment criteria must be infinite families of inequalities — is
false: the discriminant is a symmetric holomorphic function whose sign decides reality. The genuine
obstruction is not blindness but regularization.

### 5k.3 Status of the governing statistic

The gap literature treats only *absolute* normalized gaps: infinitely many below `0.515396`,
infinitely many above `2.7328` (`3.18` on the critical line). Whether infinitely many gaps fall below
half the average is open even under the Riemann hypothesis. Nothing addresses a gap relative to its
neighbours — the quantity §5j.3 identifies as governing. In the adjacent holomorphic lane the
corresponding no-go is known: Jensen polynomials are not a plausible route to the Riemann hypothesis.

## §5l. No discrete invariant detects the Riemann hypothesis

The discriminant-sign criterion of §5k.2 is vacuous, for two independent reasons, and the reason
generalizes.

**The functional equation trivializes the sign.** `H_t` is even in `z` and real on the real axis, so a
zero `z₀` forces `-z₀`, `z̄₀`, `-z̄₀`. A non-real zero with `Re z₀ ≠ 0` therefore arrives as a
quadruple — *two* conjugate pairs — so the number of conjugate pairs is always even and
`sign(disc) = (-1)^m = +1` whatever the divisor does off the critical line.

**The one escape is closed.** The only configuration making `m` odd is a purely imaginary zero of
`H_t`, i.e. a real stray `s = ½ ± w` of `Ξ_t`. At `t = 0` there are none: for real `s ∈ (0,1)`,
`(1-2^{1-s})ζ(s) = Σ(-1)^{n-1}n^{-s} > 0` as an alternating series with decreasing terms, so `ζ` has
no real zero in the critical strip. The sign is unconditionally `+1`.

**The general statement.** Deform a critical double pair into a complex quadruple,

```
((s-½)² - (a+iγ)²)((s-½)² - (a-iγ)²) ,      a ∈ [0,a₀] ,
```

which at `a = 0` is `((s-½)² + γ²)²` — a doubled critical pair — and for `a > 0` a genuine
off-critical quadruple. The family is continuous in `a` and stays inside the class of divisors
invariant under `s ↦ 1-s` and conjugation. The critical and off-critical loci therefore lie in **one
connected component** of the symmetric class, joined through a double zero, and any invariant that is
continuous with values in a totally disconnected set is constant along the path.

> **No parity, index-mod-`k`, or other discrete invariant of the divisor can separate critical from
> off-critical configurations. Every criterion for the Riemann hypothesis must be metric — an
> inequality on a continuously varying quantity — never topological.**

The Weil index itself is not continuous along the path (it is `2` for `a > 0` and `0` at `a = 0`),
which is precisely why it is usable as a criterion and precisely why limiting arguments can bound it
but never compute it.

This is the first constraint in the classification that restricts the *form* of any future proof
rather than a particular lane. It rules out in one stroke parity arguments, index-mod-`k` arguments,
regularized-discriminant signs, winding and degree arguments, and any invariant of `K`-theoretic or
cobordism type. Together with §5h.4 (the flow is monotone in the direction that agrees with the
hypothesis) and §5g (extending a positivity range is equivalent to the hypothesis), the admissible
shape of a proof is now sharply constrained: a metric inequality, not monotone under the heat
deformation, and not an aggregate of a positivity form. Of the objects surfaced so far only one meets
all three conditions — the relative gap statistic of §5j.3.

## §5m. The open core closes: a gap below all its running means collides

The relative-gap requirement of §5j.3 was an artefact of a crude bound.

### 5m.1 The exact comparison

The field of a gap `δ` between consecutive real zeros is

```
Δ = Σ_{m≥1} [ 1/(D_m^L(D_m^L+δ)) + 1/(D_m^R(D_m^R+δ)) ] ,
```

with `D_m^L = δ_{n-1}+…+δ_{n-m}` and `D_m^R = δ_{n+1}+…+δ_{n+m}`. For the lattice `D_m = mδ`, each
term is exactly `1/(m(m+1)δ²)` and `δ²Δ = 2Σ 1/(m(m+1)) = 2` — the equilibrium of §5j.2. Comparing
**term by term** rather than through a single minimum,

```
D_m ≥ mδ   ⟹   1/(D_m(D_m+δ)) ≤ 1/(m(m+1)δ²) ,
```

so `δ²Δ ≤ 2`, strictly as soon as one `D_m` exceeds `mδ`. And `D_m ≥ mδ` says exactly that `δ` is at
most the **running mean** of the `m` gaps on that side. Hence:

> **A gap that is at most the running average of the gaps on each side, for every window length, and
> strictly below one of them, satisfies `δ²Δ < 2` and collides in backward time.**

### 5m.2 Why the hypothesis is available

*Inside a window*: the minimal gap of a window satisfies the running-mean condition for every `m`
inside it, since a sum of `m` gaps each at least `δ` is at least `mδ`. No relative-gap statistics are
needed. *Outside*: the running means converge to the local mean spacing, so the condition reduces to
the normalized gap being at most `1`; the minimum of `N` gaps of mean `1` is at most `1`, and by the
known small-gap results infinitely many normalized gaps fall below `0.515396`. *Persistence*: the gap
velocity is `-4/δ + 2δΔ`, so among comparable fields the smallest gap has the most negative velocity;
the minimal gap contracts fastest and stays minimal, and the hypothesis persists over the collision
interval — exactly what the frozen-field estimate of §5j.1 requires.

### 5m.3 Consequence

```
RH at t = 0 ⟹ all zeros of H₀ real, density → ∞, window minima with normalized gap < 1
            ⟹ infinitely many gaps satisfy the running-mean condition
            ⟹ infinitely many backward collisions
            ⟹ M(t) = ∞ for every t < 0 ,
```

and contrapositively: **if `H_t` has only finitely many non-real zeros for a single `t < 0`, the
Riemann hypothesis is false.** Against Ki–Kim–Lee's theorem that `M(t) < ∞` for every `t > 0`, the
finiteness threshold is exactly `0` under the Riemann hypothesis.

The analytic input — the zero dynamics for an infinite order-one configuration and the validity of
the frozen-field comparison over the collision interval — is standard for the de Bruijn–Newman flow
and is used as stated. The relative-gap requirement is gone; it was self-inflicted.

## §5n. The persistence problem dissolves, and the margin is explicit

§5m left one question: does the running-mean hypothesis persist over the collision interval? It need
not. Track the **window minimum** `u_min(τ) = min_i δ_i(τ)²` rather than a fixed gap. A minimizing gap
satisfies the running-mean hypothesis *by definition* at every time, since a sum of `m` gaps each at
least the minimum is at least `m` times the minimum. If the minimizer changes, the criterion
transfers to the new one. Only a uniform margin is needed, and it is explicit.

### 5n.1 The sharpened field bound

If the running means exceed the gap by a factor `a = 1+η ≥ 1`, i.e. `D_m ≥ a·mδ`, then

```
δ²/(D_m(D_m+δ)) ≤ 1/(am(am+1)) ≤ (1/a)·1/(m(m+1)) ,
```

the second step because `am+1 ≥ m+1` for `a ≥ 1`. Summing against the telescoping lattice sum,

```
θ := δ²Δ ≤ 2/a = 2/(1+η) < 2 ,
```

with collision time at most `u₀(1+η)/(8η)`. This is the correct sharpening: the Basel bound
`Σ 1/m² = π²/6` used in §5j discards the `+1` and produces the spurious threshold `√6/π`; keeping the
`+1` telescopes and gives the clean `2/a`.

### 5n.2 The margin

For small `m` the immediate neighbours give only `a = 1` and contribute at most the lattice value.
Past a window length `M₀` the running mean approaches the local mean spacing, and the minimum of a
window of gaps of mean `1` is at most the known small-gap constant `0.515396`, so `a ≈ 1.94` there:

```
θ ≤ 2(1 - 1/(M₀+1)) + (2/a)(1/(M₀+1)) = 2 - (2/(M₀+1))(1 - 1/a) ,
```

an explicit margin `c/(M₀+1)` with `c = 2(1-1/a) ≈ 0.97`.

### 5n.3 Universal survival and the conclusion

Every gap obeys `u_i' = -8 + 4θ_i` with `θ_i ≥ 0`, so `u_i' ≥ -8` and no gap vanishes before time
`u_i(0)/8`. With the margin, `u_min' ≤ -c' < 0` and the minimum reaches zero in finite time. Absolute
gaps shrink as the height grows while `M₀` grows only mildly, so collision times tend to `0` up the
critical line and for every `t < 0` infinitely many collisions have already occurred.

The analytic input is now minimal and checked. Implicit differentiation of `H_t(z_j(t)) = 0` at a
simple zero gives `ż_j = H''/H'(z_j)`. The sum form `H''/H'(z_j) = 2Σ_{k≠j}(z_j-z_k)^{-1}` follows
from the Hadamard factorization of the even order-one function `H_t` in `z²`, convergent because
`Σ|z_k|^{-2} < ∞`, with the pairing `k ↔ -k` making it absolutely convergent. A multiple real zero is
already a degenerate collision and splits off the axis immediately in backward time, so no simplicity
hypothesis is needed.

What remains soft is the passage from the pointwise differential inequality to the running minimum — a
Dini-derivative argument — and the tail estimate past `M₀`, which uses the counting function. No
unstudied statistic is required.

## §5o. The height–time scaling law

The zero dynamics is quadratically homogeneous, so flow time has the dimensions of length squared. At
height `T` the only available length is the mean spacing `2π/log(T/2π)`, so the natural time scale
there is

```
natTime(T) = spacing(T)²/8 = π²/(2 log²(T/2π)) ,   with inverse   flowHeight(t) = 2π·exp(π/√(2t)) .
```

Both sides of the flow are governed by this one curve.

For `t > 0`, Ki–Kim–Lee prove that all but finitely many zeros of `H_t` are real, and Polymath15 made
this effective, producing an explicit height beyond which the zeros are provably real. That height
must diverge as `t ↓ 0`, and the scaling law says it diverges like `exp(c/√t)`. For `t < 0`, the
collision estimate of §5m–§5n says a gap at height `T` reaches the axis within backward time
`≍ spacing(T)²/8`, so by backward time `|t|` every sufficiently relatively-small gap above
`flowHeight(|t|)` has already collided.

The two thresholds share a functional form because they are the same dimensional statement. The sign
flip is visible in the effective analysis itself: the mollification gain is a factor
`e^{t log²x/16}`, which beats any fixed loss once `t log²x ≫ 1` — reality above `exp(c/√t)` — and
which *decays* for `t < 0`, reversing the conclusion to non-reality, exactly as the collision picture
predicts from the other direction. `t = 0` is where the threshold escapes to infinity: the flow has
acted nowhere and marginally everywhere. That is the structural reason to expect `Λ = 0`.

**Numerical corollary.** Proving `Λ ≤ t` by the barrier method means verifying below the threshold
and estimating above it, so the reachable `t` scales as `π²/(2 log²X)` in the verification height `X`.
Each halving of the bound on `Λ` costs a factor `√2` in log-height — it squares the verification
height. This explains, with no computation, why the numerical programme stalls where it does.

## §5p. The touching comparison closes the last soft step

The running minimum `u_min(τ) = min_i δ_i(τ)²` is only Lipschitz, so the differential inequality
`u_min' ≤ -c` is not literally available. The touching structure is:

> **Touching comparison.** Let `f` be continuous on `[0,T]` and suppose that for every `x ∈ [0,T)`
> there is a function `g` with `f ≤ g` everywhere, `f x = g x`, and a right derivative `g' ≤ -c` at
> `x`. Then `f x ≤ f 0 - c·x` for all `x ∈ [0,T]`.

For `z > x` the difference quotient of `f` is at most that of `g`, because `f z ≤ g z` while
`f x = g x`; the quotient of `g` tends to `g' ≤ -c`; so the lower right Dini derivative of `f` is at
most `-c`, and the fencing theorem for continuous functions compares `f` against the line. A finite
minimum supplies the hypothesis for free: the minimizing index gives a function lying above `f` and
touching it there, whose derivative is at most `-c` by the collision estimate — applicable precisely
because the minimizing gap satisfies the running-mean hypothesis by definition.

No Dini theory beyond the fencing theorem is needed, no persistence hypothesis, and no unstudied
statistic. The chain of §5i–§5p has one analytic input left, the zero dynamics itself, checked in
§5n.

**The effective route cannot trigger the criterion.** The Ki–Kim–Lee argument, made effective by
Polymath15, rests on a mollification gain `e^{t log²x/16}`. For `t > 0` it beats any fixed loss above
`x ≈ exp(c/√t)`, giving reality; for `t < 0` the same factor decays, so the argument reverses and
predicts non-reality. There is no route to finiteness at `t < 0` by that method.

The picture is a sharp finiteness transition at `t = 0`:

```
M(t) < ∞  for every t > 0        (Ki–Kim–Lee)
M(t) = ∞  for every t < 0        (§5i–§5p, under RH)
```

with `M(0) = 0` under the Riemann hypothesis.

**Unconditional version.** The chain uses the Riemann hypothesis only to know the zeros of `H₀` are
real. Unconditionally `H₀` still has infinitely many real zeros, of density tending to infinity, and
off-critical zeros only help: a conjugate pair at vertical distance `y` much larger than the gap
contributes `≈ -2/y² < 0` to the field, accelerating collision. So one expects `M(t) = ∞` for every
`t < 0` unconditionally; the residual input is a definite spread of the gaps between consecutive
*critical* zeros in some window, which under the Riemann hypothesis is the known small-gap constant.

## §5q. The finiteness transition is exactly at `t = 0`, unconditionally

The conditionality of §5m–§5p disappears under a case split whose branches use different mechanisms.

**Case A: `H₀` has infinitely many non-real zeros.** Non-reality persists in backward time: since
`∂_tH = -∂_z²H`, backward time is the forward heat equation, so Sturm's nodal-decrease theorem gives
that the number of real zeros in any interval is nonincreasing as `t` decreases. Real zeros are
destroyed, never created, going backward, so `M(t) ≥ M(0) = ∞`.

**Case B: `H₀` has finitely many non-real zeros.** Then all but finitely many zeros are real with
density tending to infinity. The unconditional small-gap results give infinitely many consecutive
ordinates at normalized distance below `0.515396`, all but finitely many of them between real zeros.
Each is a window minimum below the window mean by a definite factor, so the running-mean hypothesis
of §5m holds with the margin of §5n, the touching comparison of §5p drives the squared gap to zero in
finite backward time, and by §5o the collision time tends to `0` up the critical line. Infinitely many
collisions have therefore occurred by any fixed `t < 0`.

```
M(t) < ∞   for every t > 0      (Ki–Kim–Lee)
M(t) = ∞   for every t < 0      (this section)
```

**The transition of the de Bruijn–Newman flow is exactly at `t = 0`, unconditionally**, with
`M(0) = 0` under the Riemann hypothesis.

**Consequence.** The criterion of §5i — finiteness of the non-real count at a single `t < 0` implies
the Riemann hypothesis fails — is now vacuous as an attack, since its hypothesis is never satisfiable.
What survives is the structural theorem above, the exact complement of Ki–Kim–Lee.

**A route that fails.** The partial sums of `1 - δ̂_k` are exactly `S(T)`, so one might hope Selberg's
unconditional `∫₀^T S² ∼ T log log T/(2π²)` forces the gaps away from `1`. It does not: bounded
deviations `|1-δ̂_k| ≤ η` still permit `S` to grow like `η√n` through cancellation. The definite
spread must come from the small-gap results, not from the moments of `S`.

### The atlas, eight rows

```
linear Λ-positivity              caps at PNT strength                 (Theorem N)
quadratic Weil index             lower bounds on ind₋ only            (Theorem N′)
Bohr-torus probability           valid only past height ~ π(N)        (Theorem G)
elementary archimedean tower     optimal at ℓ ≈ 0.155                 (Theorems Q24–V29)
extension of the range           equivalent to RH                     (Theorem X31)
de Bruijn–Newman flow            monotone; criterion vacuous          (Theorems C37, N47)
discrete/topological invariants  impossible                           (Theorem H42)
```

## §5r. Boundary zeros are free, interior zeros are not

The Nyman–Beurling / Báez-Duarte lane is the one approach the classification leaves admissible: it is
metric, not monotone under the heat deformation, and an extremal quantity rather than an aggregate of
a positivity form. Its mechanism is the quantitative form of a closure obstruction — the qualitative
version, that a continuous evaluation killing every generator but not the target puts the target
outside the closed span, is standard. Here the evaluation is measured.

**The exact distance.** In an inner product space, for `v ≠ 0`,

```
dist( f , { g : ⟪v,g⟫ = 0 } ) = |⟪v,f⟫| / ‖v‖ ,
```

the upper bound by the projection `g = f - (⟪v,f⟫/‖v‖²)v` and the lower bound by Cauchy–Schwarz. In a
reproducing kernel Hilbert space with `v = K_w` this is `dist(f, {g : g(w)=0}) = |f(w)|/√K(w,w)`.

**The dichotomy.** For the Hardy space of a half-plane, `K(w,w) = 1/(4πσ)` with `σ` the distance from
`w` to the boundary, so the cost of forcing a vanishing at `w` is

```
|f(w)|·√(4πσ) → 0   as σ → 0 ,      > 0   for σ > 0 ,
```

and is monotone increasing in `σ`. Constraining an approximant to vanish at a boundary point is free;
at an interior point it is not.

**Why this is the right mechanism.** In the Báez-Duarte formulation the approximants have Mellin
transforms divisible by `ζ`, so they must vanish at every zero of `ζ`, while the target does not. A
zero *on* the critical line is a boundary point: the pointwise constraint costs nothing, and the
observed `d_N² ≍ 1/log N` is the cost of imposing it at the scale a Dirichlet polynomial of length
`N` resolves near the line. A zero *off* the line is an interior point at distance `σ = |β-½|`, and
the constraint costs a definite amount independent of `N`.

The Nyman–Beurling distance therefore separates the two cases by their **rate**: `d_N² ≍ 1/log N` is
critical behaviour, and an off-critical zero forces a constant floor proportional to `√|β-½|` times
the target value there. This is the asymmetry every capped lane lacked — the mechanism gets *worse*,
not better, as the divisor moves off the line, which is exactly the property §5l requires of a viable
criterion and exactly the property §5h.4 showed the flow does not have.

## §5s. A quantitative Nyman–Beurling criterion, and universal height degradation

### 5s.1 The space

Every Báez-Duarte generator is supported in `(0,1]`: for `t ≥ 1` both `1/t < 1` and `θ/t < 1`, so
`ρ_θ(t) = {θ/t} - θ{1/t} = θ/t - θ/t = 0`. The target is supported there too. The Mellin transform
`f ↦ ∫₀¹ f(t)t^{-s}dt` therefore converges for `Re s < ½` and maps `L²((0,1],dt)` unitarily onto the
Hardy space `H²` of the half-plane `Re s < ½`, with `‖f‖² = (1/2π)∫|f̂(½+iu)|²du`; the target confirms
the normalization, since `1̂(s) = 1/(1-s)` has boundary modulus squared integrating to `2π` against
`‖1_{(0,1]}‖² = 1`. This is what makes evaluation *off* the critical line legitimate: the functions
extend to a half-plane and evaluation there is bounded.

### 5s.2 The floor

Generators have transforms `ζ(s)(n^{-s}-1/n)/s`, so every finite combination has transform
`ζ(s)P(s)/s` with `P` entire, vanishing at every zero `ρ ≠ 0` of `ζ`; vanishing survives `L²` limits
because evaluation is continuous. The target does not vanish there. With the diagonal kernel
`K(w,w) = 1/(2σ)`, the exact vanishing cost gives, for a zero `ρ = β+iγ` with `β < ½`,

```
lim_N d_N ≥ |1̂(ρ)| / √K(ρ,ρ) = √(1-2β) / |1-ρ| .
```

By the functional equation the Riemann hypothesis fails exactly when such a `ρ` exists, so **if it
fails, the Báez-Duarte distances are bounded below by the explicit constant `√(1-2β)/|1-ρ|`** — the
quantitative form of the easy direction of the criterion, with a modulus in the deviation.

### 5s.3 Universal height degradation

The floor is at most `1/|γ|`, since `√(1-2β) ≤ 1` and `|1-ρ| ≥ |γ|`. Closing the criterion against
verification to height `X` would need `d_N ≤ 1/X`, i.e. `N ≥ exp(X²)`. The same degradation appeared
in the flow lane, where verification to height `X` bounds `Λ` only by `π²/(2 log²X)`.

> **Every quantified lane loses strength at a putative counterexample polynomially or exponentially
> in its height. Numerical verification and analytic estimate never meet unless the analytic estimate
> is itself as strong as the verification height.**

This is the unified reason the "verify below, estimate above" architecture stalls. Unlike the other
entries in the atlas it is a statement about the *interaction* of the two halves of every known
effective programme rather than about a single lane.

## §5t. The admissible shape of a criterion is a threshold count

Three constraints have accumulated on any functional `Φ` of the divisor that could decide the Riemann
hypothesis: it must be **metric** (§5l), **height-neutral** (§5s.3), and **non-monotone under the
flow** (§5h.4). For additive functionals `Φ = Σ_j φ(y_j)` of the deviations, one computation decides
whether the three are compatible. The flow gives `ẏ_j = -2Σ_{k≠j}(y_j-y_k)/|z_j-z_k|²`, so

```
d/dt Σ_j φ(y_j) = -2 Σ_{{j,k}} (φ'(y_j) - φ'(y_k))(y_j - y_k)/|z_j - z_k|² ,
```

and every term is nonpositive exactly when `φ'` is nondecreasing, i.e. when `φ` is convex.

> **Every convex even weight gives a functional monotone along the flow, hence capped. A
> height-neutral, non-monotone additive functional must have a non-convex weight.**

The square is convex, recovering the imaginary energy and its cap; so is the quartic, since
`(a³-b³)(a-b) = (a-b)²(a²+ab+b²) ≥ 0` — raising the power does not escape. The truncated weight
`min(y²,ε²)` is not convex: `φ'(ε/2) = ε` while `φ'(2ε) = 0`, so the pair term there is strictly
positive and the functional can increase.

The three conditions are therefore simultaneously satisfiable, and the functionals satisfying them
are the truncated ones — counts of zeros whose deviation exceeds a threshold, up to a bounded weight.

> **The admissible shape of a criterion for the Riemann hypothesis is a threshold count of
> off-critical zeros — an `N(σ,T)`-type quantity — and nothing smoother.**

The derivation is the content: the conclusion follows from three independent no-go results, one
topological, one effective, one dynamical. It explains why every smooth criterion in the atlas stalls
in its own way, while the unconditional progress that exists lives in the zero-density literature.

### The atlas at nine entries

```
linear Λ-positivity              caps at PNT strength                 (Theorem N)
quadratic Weil index             lower bounds on ind₋ only            (Theorem N′)
Bohr-torus probability           valid only past height ~ π(N)        (Theorem G)
elementary archimedean tower     optimal at ℓ ≈ 0.155                 (Theorems Q24–V29)
extension of the range           equivalent to RH                     (Theorem X31)
de Bruijn–Newman flow            monotone; criterion vacuous          (Theorems C37, N47)
discrete/topological invariants  impossible                           (Theorem H42)
verification + estimate          never meet (height degradation)      (Theorem Q49)
admissible functional shape      threshold count only                 (Theorem R50)
```

## §5u. The degradation-exponent scale

The admissible shape of a criterion is a threshold count; the threshold count with threshold `σ` is
`N(σ,T)`, and its vanishing for all `T` is a zero-free region `{Re s > σ}`. The classification
therefore closes on itself: **the unique admissible shape is the zero-free region**, and density
estimates are its quantitative surrogates.

**Integrality does not rescue the composition.** `N(σ,T)` is an integer, so a bound below `1` forces
exact vanishing, and verification to height `X` gives `N(σ,X) = 0`. But `N(σ,·)` is nondecreasing, so
that carries no information above `X`, and a bound `N(σ,T) < 1` valid for all `T` *is* the statement.
Verification and estimate fail to compose here exactly as everywhere else.

**The degradation is slower, and that is the point.** A zero-free region degrades in its *width*:
`c/log t` classically, `c/((log t)^{2/3}(log log t)^{1/3})` after Vinogradov–Korobov. Both shrink with
height, so the lane degrades in kind — at the slowest rate in the atlas:

```
Nyman–Beurling floor      ≍ 1/γ                  polynomial        (worst)
de Bruijn–Newman bound    ≍ 1/log²X              log exponent 2
zero-free region width    ≍ 1/(log t)^{2/3}      log exponent 2/3  (best)
Riemann hypothesis        ≡ 1/2                  log exponent 0
```

> **The Riemann hypothesis is the statement that the degradation exponent is zero.**

Every lane is a point on one scale, and the zero-free lane is furthest along it. The nine no-go
results of the preceding sections are not unrelated obstructions: they are the same statement
measured in different units — a criterion's strength at a counterexample of height `t` decays like
`(log t)^{-a}`, and the lane is characterised by `a`. Progress means lowering `a`; the known
technology has moved it from `1` to `2/3`, and exponent `0` at any positive fixed width is already a
famous open problem strictly weaker than the hypothesis.

## §5v. The last lane is not capped

The classification left one lane, and the question was whether it too has a method-intrinsic floor.
It does not, and a plausible argument that it does is false.

A zero-free region from the Borel–Carathéodory bound and the `3 + 4cos + cos2` positivity has width
`w ≍ r/M(r,t)`, where `M(r,t) = sup\{log|ζ(s)| : |s-(1+iγ)| ≤ r\}` and `r` is the radius of the disk
on which the growth of `ζ` is controlled. Classically `M ≍ log t` with `r ≍ 1`, giving exponent `1`;
Vinogradov–Korobov improve `M` to `(log t)^{2/3}`, giving `2/3`. **The degradation exponent is exactly
the quality of the growth bound.**

**The proposed floor.** Montgomery's unconditional Ω-results make `log|ζ|` unbounded on every vertical
line `σ<1`, schematically `M(r,t) ≳ (log t)^r/log log t` for a disk reaching abscissa `1-r`. With a
fixed radius this does kill a fixed width: writing `B = log t` and `x = r log B`,

```
w ≤ r log B / B^r = x·e^{-x} → 0 .
```

**Why it does not cap the method.** Nothing forces a fixed radius. At the shrinking radius
`r = 1/log B` the same Ω-bound gives `B^r = e` and hence `w ≤ 1/e`, a positive constant. The
Ω-results obstruct fixed-radius arguments only.

**Conclusion.** The exponent is limited by the quality of the growth bound, not by the method. The
effective programme reduces to one quantitative question:

> **How small can `sup log|ζ|` be made on a disk of radius `≍ 1/log log t` reaching to abscissa
> `1 - c/log log t`?**

Known there: Vinogradov–Korobov strength. Permitted by the Ω-results: `O(1)`. The gap between them is
the entire remaining distance to a fixed-width zero-free region, and hence — by the
degradation-exponent scale — the entire remaining distance from the effective programme to exponent
zero. This is the one place in the classification where the obstruction is technical rather than
structural.

## §5w. The critical scale is `1/log log t`

**Calibration.** With the Vinogradov–Korobov growth `M(r,t) ≍ B r^{3/2}log t + log log t`, the width
`w ≍ r/M` is maximised where the two terms balance, giving
`r ≍ (log log t/log t)^{2/3}` and `w ≍ 1/((log t)^{2/3}(log log t)^{1/3})` — the Vinogradov–Korobov
region exactly. The width formula reproduces the state of the art, so it may be used predictively.

**The finding.** The believed size of `ζ` just left of `σ = 1` — a theorem under the Riemann
hypothesis, a conjecture without it — is `log|ζ(1-r+it)| ≍ (log t)^{2r}/log log t`. With
`L = log log t` and `x = 2rL`,

```
w = r L / (log t)^{2r} = (x/2)·e^{-x} ,
```

independent of `t`, maximised at `x = 1` — the radius `r = 1/(2 log log t)` — with value `1/(2e)`. A
zero-free region of **fixed width**: degradation exponent zero.

**One factor decides it.** Without the `1/log log t` in the growth the width is `(x/(2L))e^{-x}`,
maximised at `1/(2eL)`, which tends to zero. The `log log t` in the denominator of the conjectured
growth is exactly what makes the optimised width scale-invariant; nothing else in the computation
matters.

**What the programme reduces to.** Not a bound for all `σ`, but an unconditional Littlewood-type
bound on the single creeping line `σ = 1 - 1/(2 log log t)`. Under the Riemann hypothesis such a
bound is a theorem; unconditionally it is open, and it would yield a fixed-width zero-free region.
This is the narrowest target the classification produces: one line, one bound.

The critical scale `1/log log t` is the same scale at which the Ω-results cease to obstruct
fixed-radius arguments — two independent computations landing on the scale where `(log t)^r` becomes
`O(1)`.

## §5x. The Borel–Carathéodory mechanism is capped at `1/log log t`

The optimisation of §5w used the growth `M ≍ (log t)^{2r}/log log t`. That formula is wrong near
`σ = 1`: it tends to `0` there, whereas the true size of `log|ζ(1+it)|` is `≍ log log log t` — bounded
above and, by Granville–Soundararajan, attained. The correct shape carries an irreducible additive
term, `M(r,t) ≍ (log t)^{2r}/log log t + log log log t`, and that term changes the conclusion.

Write `L = log log t`, `ℓ = log log log t`. Two unconditional lower bounds hold: `M(r,t) ≥ ℓ` for
every `r`, since the disk meets the line `σ = 1`; and `M(r,t) ≥ e^{rL}/L` by Montgomery's Ω-result on
`σ = 1-r`. Hence `w = r/M ≤ min(r/ℓ,\ rLe^{-rL})`. The first branch increases in `r`, the second
decreases past `rL = 1`, and they cross at `rL = log(Lℓ)`, where the common value is

```
w ≤ log(Lℓ)/(Lℓ) ≤ 2ℓ/(Lℓ) = 2/L ,
```

using `log(L log L) = log L + log log L ≤ 2 log L`.

> **Every zero-free region obtained from the Borel–Carathéodory bound on a disk around `1+iγ` has
> width `≪ 1/log log t`. The mechanism cannot produce a fixed-width region, whatever growth bound it
> is fed.**

This is unconditional and intrinsic: the obstruction is the irreducible `log log log t`, the true size
of `log|ζ|` on `σ = 1`. It supersedes the earlier reading that the lane was uncapped, which used the
growth formula without the additive term.

The ceiling `1/log log t` is far above the Vinogradov–Korobov region `(log t)^{-2/3}` currently
achieved, so there is real room inside the mechanism; but the ceiling is not `1/2`, so **the classical
zero-free-region mechanism cannot reach the critical line even in principle**.

## §5y. The cap is about the range of `log|ζ|`, not the norm

The ceiling of §5x came from the supremum of `log|ζ|` on a disk around `1+iγ`, and the natural escape
is to replace it by a mean. There is such a version — Parseval applied to `Re log f` bounds
`a₁ = f'/f(s₀)` by the `L²` norm of `log|f|` on the circle — and the mean square of `log|ζ(1+it)|` is
`O(1)` while its maximum is `≍ log log log t`. The substitution fails, for two independent reasons.

First, the circle is centred at the height of the *putative zero*, so a bound is needed at every `γ`,
not on average over `γ`. Second, Jensen's formula exhibits the obstruction with no norm at all:

```
n(r/2)·log 2 ≤ (1/2π)∫ log|ζ(s₀ + re^{iθ})| dθ - log|ζ(s₀)| ,
```

so the zero count is controlled by the `L¹` circle average minus the central value — the difference
of two functionals of `log|ζ|` near `σ = 1`, hence at most its **oscillation** there. That
oscillation is `≍ log log log t` unconditionally in both directions, since `max|ζ(1+it)| ≍ e^γ log log t`
and `min|ζ(1+it)| ≍ 1/log log t`.

> **Any zero-free-region mechanism whose input is a functional of `log|ζ|` on a disk around `1+iγ` —
> supremum, `L¹`, `L²`, or any quantity dominated by the oscillation — is capped at width
> `≍ 1/log log t`.**

The cap is a property of `ζ` near `σ = 1`, not of the supremum.

**Terminal statement.** The escape must not read `ζ` near `σ = 1` at all; the remaining family reads
it on or near the critical line, and that technology yields proportions of zeros on the line, capped
below `1`. So

```
near σ = 1   →  zero-free regions,    capped at width 1/log log t
near σ = ½   →  positive proportions, capped below 1
```

and neither family reaches the Riemann hypothesis.

## §5z. The functional equation transports but does not create

Two capped families remain — mechanisms near `σ = 1` and mechanisms near the critical line — and the
untested move is to couple them through the functional equation. It gains nothing. From `ξ(s) = ξ(1-s)`
and Stirling,

```
log|ζ(σ+it)| - log|ζ(1-σ+it)| = log|χ(σ+it)| = (½-σ)·log(t/2π) + O(1/t) ,
```

and at a fixed height the right-hand side is a **constant**. The oscillation of `log|ζ|` on the line
`σ` therefore equals the oscillation on the reflected line `1-σ`: the functional equation shifts the
values without spreading them, so a mechanism reading a reflected pair sees the same oscillation twice
and is capped exactly as a one-sided mechanism is.

> **The functional equation transports information between reflected abscissae; it never creates
> any.**

This is the quantitative counterpart of the earlier finding that the functional equation does not pin
down `ζ`: there a failure of rigidity, here a failure of information gain.

What remains is the interior of the strip, where the only admissible functional is the threshold
count `N(σ,T)`. That family is capped for an elementary reason: mean-value and large-sieve methods
produce bounds of the form `T^a log^B T`, which are at least `1` for large `T`, while the hypothesis
needs the count to be exactly `0`. A bound that grows in `T` can never certify a vanishing integer
count.

> **Density estimates cannot prove the Riemann hypothesis. They can only approach it.**

### The complete classification

```
σ near 1      zero-free regions       capped at width 1/log log t
σ interior    density estimates       bounds grow in T, never reach 0
σ = ½         moments and mollifiers  proportions capped below 1
functional eq transports, no gain
```

All three families are capped and the functional equation cannot combine them. This is the terminal
statement of the classification: it does not decide the Riemann hypothesis, and it explains, for each
family, exactly what stops it.

## §6. The construction side: an `xp` model needs a quadratically growing box

The classification covers mechanisms that *read* `ζ`. The remaining family constructs an operator
whose spectrum is the zero set, and the counting function pins the candidate at once:
`N(T) = (T/2π)(log(T/2π) - 1) + O(log T)` is not a power law, so no elliptic operator on a compact
manifold has this spectrum; the `log` factor is the semiclassical signature of `xp`.

For `xp` on the box `0 < x < X`, `0 < p < P`,

```
Area{xp < E} = ∫₀^X min(P, E/x) dx = E + E·log(XP/E)      (E < XP) ,
```

so the semiclassical count is `N(E) = (E/2π)(1 + log(XP/E))`. Equating with the Riemann count gives

```
1 + log(XP/E) = log(E/2π) - 1   ⟺   XP = E²/(2π e²) :
```

the phase-space cutoff must grow **quadratically** in the spectral parameter, with the explicit
constant `1/(2πe²)`. A fixed box is excluded outright: with `XP = A` constant the count is
`(E/2π)(1 + log A - log E)`, which becomes negative once `E > eA` — absurd for a counting function.

> **No `xp`-type semiclassical model on a fixed phase-space region can carry the zeta spectrum. The
> box must expand like `E²/(2πe²)`, so the object is a family indexed by the spectral parameter, not
> a single operator.**

This is the precise sense in which the Berry–Keating picture requires an energy-dependent
regularization, and it is consistent with the adelic construction producing an absorption spectrum
rather than a genuine discrete one. It complements §5f's result that a complex quadruple is
incompatible with any self-adjoint problem: that maps what such an operator would imply, this maps
what its semiclassical shadow must look like.

## §6b. The truncation family is incoherent

For the family of box-truncated `xp` models to describe *one* spectrum, the low-lying eigenvalues must
not move as the box grows. They do. The truncated operator is defined variationally, so enlarging the
box enlarges the form domain and by min–max every eigenvalue is nonincreasing in the area; the
semiclassical count makes this strict, since `N(A,E) = (E/2π)(1 + log(A/E))` is strictly increasing
in `A`.

A family `{H_{A(E)}}` required to share the zeros as spectrum would need `N(A(E₁),E) = N(A(E₂),E)`
for energies below both cutoffs. Strict monotonicity forbids it whenever `A(E₁) ≠ A(E₂)`, and the
required area is strictly increasing.

> **No family of box-truncated `xp` models has a common spectrum. The counting law can be matched at
> each energy by choosing the box, but the individual eigenvalues then move with the box, and no
> single operator emerges.**

This is exactly the status of the Berry–Keating model: a correct heuristic for the *density* of zeros
that does not produce the zeros. The obstruction is not the quality of the semiclassical
approximation; the family is not coherent.

Consequently a genuine Hilbert–Pólya operator cannot arise as a limit of box-truncated `xp` models.
It must be non-semiclassical — which is where the adelic construction lives, and there the spectrum
appears as absorption rather than as eigenvalues.

### The classification, complete

```
read near σ = 1          zero-free regions        capped at 1/log log t
read interior            density estimates        bounds grow, never 0
read σ = ½               moments and mollifiers   proportions below 1
construct semiclassical  Berry–Keating xp         family incoherent
construct non-semiclassical  adelic               the remaining target
functional equation      transports, no gain
```

Every mechanism examined is capped except one: a non-semiclassical construction.

## §6c. The carrier must be scale-invariant modulo a discrete subgroup

Two obstructions point the same way and together determine the shape of the carrier. This is the
first *positive* statement of the classification: it derives the carrier rather than positing it.

**Scale-covariance is forced.** A family of truncated models indexed by a scale has spectra that move
with the scale, so it is incoherent. The only way a scale-indexed family can have one spectrum is for
its members to be unitarily equivalent under the scaling — for the operator to be scale-covariant —
and then the family collapses to a single object.

**Full scale-invariance destroys discreteness.** If the spectrum `S` satisfies `λS = S` for every
`λ > 0` and contains one positive point, it contains every positive point: given `x > 0` and `s ∈ S`
with `s > 0`, take `λ = x/s`. A fully scale-covariant operator therefore has a spectrum that is a
union of rays — continuous, never discrete. That is exactly why the dilation generator `xp` on
`L²(0,∞)` has purely absolutely continuous spectrum: it *is* the generator of the scaling group.

**A discrete subgroup restores it.** `q^ℤ` is invariant under multiplication by `q` and misses every
point strictly between `1` and `q`, so invariance under a discrete subgroup is compatible with a
discrete spectrum.

> **The carrier of a Hilbert–Pólya operator must be a scale-invariant space quotiented by a discrete
> subgroup of the scaling group: fully invariant enough for the family to be coherent, discretely
> invariant enough for the spectrum not to be a continuum.**

The unique arithmetic realisation of "scale-invariant space modulo a discrete scaling subgroup" that
also carries the primes is the adele class space with the idele action. The classification therefore
ends by singling out that carrier from two independent obstructions rather than by assumption.
