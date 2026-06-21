# 01 — The Landscape and Geometry of ζ / Hypertranscendental Functions, and the Weld/Seam

> **Scope.** A consolidation of what the corpus says about the *shape* of the completed zeta
> object — its geometry, its layers, where its zeros live, and the seam `Re(s)=½`. Synthesised
> through the light tower (`publications/hgt/docs/experiments/draft.md`) and the computational
> synthesis (`publications/hgt/logs/synthesis.md`), cross-checked against the `2-fully-proven`
> cards and the `where_we_stand` ledger. **Nothing here is new mathematics**; every claim is
> tagged by the register its source assigns it (`[PROVED]` / `[BRIDGE]` / `[OBSERVED]` /
> `[CONJECTURE]` / `[OPEN CORE]`). This is the static-geometry companion to
> `02-transport-system.md` (the dynamic/mechanism view).

---

## 0. The one object

All the experiments converge on a single statement about *what kind of object* the completed
zeta is:

> **The completed zeta object is not a scalar-amplitude object.** It is a **completed logarithmic
> transport connection**
> ```
>   ω = d log ξ(s),   or   H(s) = ∂_s log Λ(s) = A(s) + P(s),
> ```
> with `A(s) = ∂_s log Γ∞(s)` the **archimedean (dilation-generator) term** and
> `P(s) = ζ'/ζ(s)` the **prime (difference-base) term**. (light tower §0; synthesis §1.)

The two summands are the field's **two native generators** made literal: `∂_s` (the archimedean
differential generator) and `{σ_p}` (the infinite prime difference base). **The weld is the
seam.** The discriminating observable across *every* surviving experiment is built from this weld,
most often as the **phase-carrier defect**

```
   Δ(σ,t) = max(log|A|, log|P|) − log|A+P|         (large when A and P are antiphase)
```

— "how much phase information the prime term must supply for the weld to close" (synthesis §1).

The hidden invariant is not magnitude, phase alone, event rate, or lane occupancy. It is
**constraint-preserving, measure-covariant, coupled-lane phase-space transport capacity of
`d log ξ`** (light tower §0, §1.3) — *not how big the signal is, but whether it can keep carrying
the law.*

---

## 1. The two sources and the seam — the static skeleton

`[PROVED — BRIDGE]` (`two-sources-of-hypertranscendence.md`, `multiplier-dichotomy-theorem.md`)

The hypertranscendence of `Λ = Γ·ζ` splits by the **multiplier type** of the rank-1 difference
operators, and this split *is* the geometry:

| | **Source A — archimedean Γ** | **Source B — infinite prime base** |
|---|---|---|
| operator | one shift `s↦s+1`, **non-constant** multiplier `a = s/2π` | `σ_p : x_p ↦ p^{-1}x_p`, **constant** multipliers |
| character | differential-hypertranscendent (Hölder 1887), difference-tame | per-lane holonomic (CC), decoupling |
| CC-class | **non-CC** (the unique non-CC place) | CC (every lane a pure coboundary) |
| over `F_q` | absent | all places (every place is a Frobenius power) |

The **complete invariant** that separates them `[PROVED HERE]`: a multiplier `a` is
constant-up-to-coboundary (CC) `⟺` `div(a)` has **σ-orbit-degree 0 on every orbit**. The
Γ-multiplier `a(z)=z` has `div(z)=[0]−[∞]`, `deg_{ℤ}(z)=+1≠0` — **non-CC, imbalance localized to
the single orbit `ℤ`**; every prime lane is orbit-balanced. So:

> The archimedean place is the **unique σ-orbit-unbalanced (Source-A) place**, and
> `C5 = the weld = {the one non-CC place} × {the CC places}`, welded by the functional equation.

The **functional equation welds the two sources**, and the seam is its fixed locus:

```
   Λ(s) = Λ(1−s),   ι : s ↦ 1−s,   Fix(ι) = { Re s = ½ }.
```

As a one-form `ω = H(s)ds` this is reflection-compatible: with `r(s)=1−s`, `r*(H ds) = H ds`
(light tower §1.2), so `H(s) = −H(1−s)` away from zeros/poles. **`Re(s)=½` is not a midpoint; it
is the fixed seam of the involution `ι`** where the two sides must glue consistently.

---

## 2. The affine `ax+b` geometry and the universal curvature

`[STRUCTURAL FACT / PROVED]` (synthesis §2 dyson-meta; `phase-cancellation-crux.md` §8;
`archimedean-generator-axis-mode.md`)

The weld lives on the **affine `ax+b` group** `𝔾_a ⋊ 𝔾_m`:
- `𝔾_m` = scaling = `∂_s` (the archimedean dilation generator);
- `𝔾_a` = translation-by-`log p` = `M_p`, the prime shifts;
- with the **universal curvature**
  ```
     [∂_s, M_p] = − log p.
  ```

Both generators are **Fourier-diagonal** on the boundary modes `e_m` (`m ∈ ℤ^{(P)}`):
```
   σ_p · e_m = p^{−m_p} · e_m,    ∂_s · e_m = −(m·ℓ) e_m = −(Σ_p m_p log p) e_m = −(log n) e_m,
```
so `∂_s = −Σ_p (log p) θ_p` and the **generator/connection/curvature level carries no combination
modes** (`archimedean-generator-axis-mode.md`). This is decisive for the landscape's geometry:

> The weld **curvature** `[∂_s, M_p] = −log p` is **object-independent (universal)** — it is the
> same for every object on this geometry. Hypertranscendence (and any RH content) therefore lives
> **in the holonomy, not the curvature** (synthesis §2). The affine orbit is the *flat,
> RH-blind* part; the genuine content is the **non-affine seam** `[𝔾_a, 𝔾_m]` (the curvature+,
> higher modes).

This is "Hölder made mechanical": ζ *carries* the affine flows (scaling, translation) but is
*fixed by a constraint* in the transverse seam (`phase-cancellation-crux.md` §8). See
`02-transport-system.md` §6 for the dynamical consequence.

---

## 3. The corank `∞ − 1` — the seam as one number

`[PROVED — BRIDGE for the object + level separation; OPEN for the apex realization]`
(`corank-seam-invariant.md`)

The seam has a single computable shadow, the **corank** of the difference-Galois relation lattice
`Λ_M ⊂ ℤ^{(P)}`, and it is **one number with three faces**:

- **(G1) holonomicity:** `corank < ∞ ⟺ M` holonomic;
- **(G2) continuation transcendence:** `trdeg(T_{s_0}) ≤ corank`;
- **(G4) weight/Tate torus:** `dim W = corank`.

```
   corank(Λ_{M_ζ}) over ℚ = ∞      (unique factorization ⟹ {log p} ℚ-linearly independent)
   corank(Λ_ff) over F_q  = 1      (one Frobenius; all multipliers powers of one q)
   gap = ∞ − 1  =  the archimedean seam = the missing single Frobenius (F₁).
```

So **`ζ` non-holonomic ⟺ no single Frobenius ⟺ corank = ∞ ⟺ archimedean seam non-trivial.**

**The level-separation theorem (the honest sharpening) `[PROVED — BRIDGE]`:** corank is an
*inherently linear* invariant —
```
   corank = ∞  ⟺  {log p} ℚ-LINEARLY independent      (Baker, PROVEN)
```
— whereas the G2/G4 realizations are *algebraic*:
```
   trdeg = ∞   ⟺  {log p} ℚ-ALGEBRAICALLY independent  (Schanuel, OPEN).
```
Since `trdeg ≤ corank` is only an upper bound, **`corank = ∞` does NOT force `trdeg = ∞`**:
**G1 (linear floor) ⊊ G2/G4 (algebraic apex)**, and the gap is *exactly*
Schanuel-for-prime-logs. The **graded corank** `corank^{(T)}` (rank of ℚ-relations among
degree-`≤T` prime-log monomials) is the ladder from the proven floor (`T=1`) to the open apex
(`all T = ∞`); the first open rung is `corank^{(2)}` (open even for `{log 2, log 3}`), with the
pairwise-homogeneous bottom already climbed by Gelfond–Schneider
(`{(log p)², (log p)(log q), (log q)²}` ℚ-LI).

> **Honest correction the consolidation must carry** (`corank-arithmeticity-not-cardinality.md`,
> `[PROVED]` no-go): the naive corpus reading "*the obstruction is corank = ∞ / missing F₁*" is
> **refuted**. Twin witnesses with identical native invariants (corank 2, `dim G_L = 2`, flat,
> additive, Frobenius-less) can have `trdeg = corank = 2` *or* `trdeg = 1 < 2 = corank`. The real
> obstruction is **value-arithmeticity** (algebraic independence of `{log p}`), a non-native datum
> the seam invariant is *provably blind to*. And `f1-inversion-single-prime-stieltjes-collapse.md`
> sharpens it further: *supplying* a single Frobenius would **falsify** DSS (collapse `trdeg → 1`),
> not prove it — "F₁-absence is the *mechanism* of transcendence, not the obstacle." The `∞−1` gap
> is real as a **linear** fact; the geometry's hard content is one level above it.

---

## 4. The layers of the landscape

The completed object lives in a feature space where phase, amplitude, lane coupling, timing,
measure, and topology are all linked. Single-coordinate statistics destroy the constraint
(`mean ≠ survival`, `marginals ≠ joint association`, `amplitude ≠ phase weld`,
`lane balance ≠ Berry-relative phase`; light tower §1.1). The landscape stratifies into layers
(light tower §3):

1. **Scalar layer** — `|P|`, `log(1+|P|)`. Finite Euler can look good here; **misleading**.
2. **Phase-weld layer** — where `A` and `P` satisfy the cancellation relation `Δ > 0`.
3. **Cross-lane layer** — σ-lanes are *not* independent: co-failure sheets, association-graph
   eigenstructure, a **non-product joint measure** (the "initial measure" / entropy-gate layer).
4. **Phase-space layer** — the amplitude coordinate `O(t)` needs its correct momentum
   `θ(t)=arg P(t)`; finite Euler sees the projected caustic with the **wrong momentum**.
5. **Two-clock layer** — finite-prime phase agreement and true analytic tension can run on
   different clocks (anti-timed in the strip, synchronised at `σ>1`).
6. **Berry seam layer** — left/right lanes around a critical-line zero behave like two interfering
   paths; completion equalises magnitudes and moves the obstruction into *relative phase*.

These layers are not metaphors stacked arbitrarily; each is a distinct experimental discriminator
that finite Euler / random-phase controls fail in the critical strip and reproduce at `σ>1` (see
`06-experimental-findings.md`).

---

## 5. Where the zeros live in the geometry

`[PROVED for the local pole model; PROVED for concavity; CONJECTURE for the global bridge]`

The logarithmic derivative makes zeros **source charges / vortices** of the connection:
```
   ξ'/ξ(s) ~ m/(s−ρ)   near a zero ρ;     (1/2πi)∮_γ d log ξ = #zeros inside γ.
```
So `ω` is a **divisor-sensitive transport law**, and zeros are the singularities of the source
measure `μ_ξ = (1/2π) Δ log|ξ|`, supported exactly on the zeros (light tower §5.1).

The **transverse geometry near a zero** is the curvature hierarchy (`phase-cancellation-crux.md`
§3, self-verified ≥1e-18):
```
   (log Ξ)''(t) = Σ_ρ (½+it−ρ)^{-2},     Ξ(t) = ξ(½+it),
   P^{(k)}(t)   = Σ_ρ (½+it−ρ)^{-k},  k ≥ 2   (the higher log-derivatives = the seam content).
```
- **Under RH** (`ρ = ½+iγ`): `(log Ξ)''(t) = −Σ_γ (t−γ)^{-2} < 0` everywhere — `log|ξ(½+it)|` is
  **concave**.
- **An off-line FE-quartet** `{β±iγ, 1−β±iγ}` (`a := |½−β| > 0`, `τ := t−γ`) contributes
  ```
     2(a² − τ²)/(a² + τ²)²  > 0  for |t−γ| < a
  ```
  — a **local convex (anti-smoothing) window** of half-width `a` centred at the off-line height.

> **RH ⟹ `log|ξ(½+it)|` concave; an off-line zero forces a convex window.** This is the leading
> member of the Laguerre–Turán / Hankel hierarchy (`det H_d ≥ 0 ∀d,t ⟺ RH`); concavity is
> necessary, not sufficient.

This is the precise geometric content behind the light tower's "reset-occupation centre at
`σ=β`," "observed-volume concentration," and "phase-space signed area" — all are readings of the
local pole model `ξ'/ξ ~ m/(s−ρ)` (light tower §6.2, Theorem I).

---

## 6. The seam `Re(s)=½`, localized many ways

The corpus pins `½` as a distinguished locus through several *independent* geometric facts, each
`[PROVED — BRIDGE]` and each RH-blind on its own (they locate the seam; they do not prove RH):

- **Abscissa of a.s. convergence** (`critical-line-abscissa-of-convergence.md`): the random Euler
  observable `𝓛(σ) = −Σ_p log(1 − X_p p^{−σ})` converges a.s. **iff `σ > ½`**;
  `Var(Re 𝓛) = ½ V(σ) ~ ½ log log X` matches **Selberg's CLT**. `½` is built only from the primes
  (`Σ_p p^{−2σ}`, Mertens), never from the zeros.
- **Erosion / marginal-variance threshold** (`erosion-cocycle-reducibility.md`,
  `erosion-threshold.md`): the additive Euler cocycle is a bounded `L²`-coboundary **iff `σ ≥ ½`**
  — a sharp inclusive pinch at the seam.
- **Fisher signature wall** (`critical-line-fisher-signature-wall.md`):
  `‖ψ(s)‖² = ζ(2σ)` changes signature `+ / pole / −` at `σ=½`; the Fisher metric
  `g = (log ζ)''(2σ) = Var_p(log n) ~ 1/(2σ−1)²` blows up — `½` is a signature-change horizon.
- **Berry lane-equalization** (`id773`, light tower Theorem E): completing `ζ'/ζ → ξ'/ξ` **exactly
  equalizes the two `σ=½±δ` lane magnitudes at `σ=½`** (imbalance `→0`) and reroutes the residual
  into pure relative phase; moving the lane-centre off `½` reintroduces imbalance.
- **Reset-occupation slope** (`id757`, light tower Theorem I): reset-age occupation slopes single
  out `σ=½` (`−3.7/−4.2` vs neighbours `−1.1/−1.5`).
- **Susceptibility balance** (`prime-zero-susceptibility-transverse.md`): the mirror-pair
  susceptibility ratio `χ_n(ρ)/χ_n(1−ρ) = (n^{1−2β}/|χ_FE|)^{1/m}` is **frequency-`n`-independent
  ⟺ β=½** — and `χ = P^{(k)}(t) = Σ_ρ(½+it−ρ)^{−k}`, i.e. *susceptibility = curvature*.

---

## 7. The geometry's deepest verdict: two orthogonal axes

`[PROVED — BRIDGE]` (`orthogonality-meta-theorem.md`, `fe-fourier-quasicrystal.md`,
`omega-rh-coupling-vs-orthogonality.md`)

The landscape has **two orthogonal axes**, and conflating them is the recurring error:

- **The weld/constraint axis** — the functional equation, crystallinity, realization (`ω=0`).
  `Λ(s)=Λ(1−s) ⟺ θ(1/t)=√t·θ(t) ⟺ Poisson summation (Ш̂=Ш)`. This axis is **RH-blind**:
  Davenport–Heilbronn satisfies the FE (is crystalline) yet has off-line zeros. And `ω=0`
  (realization / a motive exists) **does not force RH** — already over `F_q` both can hold for
  separate reasons.
- **The positivity/localization axis** — RH itself. RH is the **positivity of the FE-polarization**
  (Weil), and *that polarization is archimedean*: the prime structure `𝓜` (Source B) carries **no
  polarization** (`g_p = g_p^{-1} ⟹ g_p = ±1`, false). Every known RH-equivalent positivity
  (Hilbert–Pólya, Nyman–Beurling, de Branges, Connes, Mertens amplitude) is archimedean.

> **`polarization-present ⟺ single Frobenius ⟺ corank 1 ⟺ F_q`**, and its absence
> (`⟺ corank ∞ ⟺ ℚ`) is exactly the seam. **RH-positivity is the one archimedean/timelike
> direction**: in the explicit-formula quadratic form `Q_W` of signature `(1|∞)`,
> **RH ⟺ Q_W ⪰ 0 ⟺ κ₋ = 0**, where `κ₋ = #off-line zero-pairs` (the *faithful* Krein–Langer
> index, not a measured density). The prime block `−Δ_prime` is free.

So the **geometry of the landscape is: a mirror-seamed, coupled-lane, measure-covariant,
Berry-interfering phase/transport landscape whose defects are zeros, in which the FE-weld axis and
the RH-positivity axis are orthogonal, and the seam `Re(s)=½` is the single archimedean locus where
source charge can be carried without breaking completion** (light tower §3, §7). RH is then the
statement that all nontrivial source-carrying defects of `d log ξ` are confined to the seam.

---

## Source map

- Light tower: `publications/hgt/docs/experiments/draft.md` §0–§7.
- Synthesis: `publications/hgt/logs/synthesis.md` §1–§2.
- `2-fully-proven/`: `two-sources-of-hypertranscendence`, `multiplier-dichotomy-theorem`,
  `corank-seam-invariant`, `corank-arithmeticity-not-cardinality`,
  `f1-inversion-single-prime-stieltjes-collapse`, `archimedean-generator-axis-mode`,
  `archimedean-prime-cross-term`, `phase-cancellation-crux`, `orthogonality-meta-theorem`,
  `explicit-formula-as-constraint`, `fe-fourier-quasicrystal`, `omega-rh-coupling-vs-orthogonality`,
  `critical-line-abscissa-of-convergence`, `critical-line-fisher-signature-wall`,
  `erosion-cocycle-reducibility`, `erosion-threshold`, `prime-zero-susceptibility-transverse`.
- Ledger corroboration: `docs/where_we_stand/{pure_facts,object_x,proof_shape,f1_j_index}.md`.
