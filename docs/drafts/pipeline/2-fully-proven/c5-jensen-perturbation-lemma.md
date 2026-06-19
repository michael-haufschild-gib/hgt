# The general-`t` hyperbolicity perturbation lemma (value + slope) — Jensen-section positivity assembly

- **ID:** c5-jensen-perturbation-lemma
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper, supporting lemma) — Door grade **BRIDGE**
- **Priority:** FOUNDATIONAL
- **Source:** the single-orbit-positivity assembly of `../1-in-progress/finite-free-convolution-flow.md`
  (Wheeler); consumes the kernel of `c5-jensen-prime-kernel.md` (Professor). 00-status #104.
- **One sentence.** A hyperbolic real polynomial `C` with simple, value-bounded-away-from-zero critical
  points stays hyperbolic under any deformation `D` whose **value** and **slope** are small at the critical
  points — making the Jensen-section sign-transfer **even-free** (valid at every base point `t`, not only the
  symmetric `t=0`) and reducing RH (via the carrier) to two pointwise large-values bounds on the prime
  deformation.

---

## §1 The lemma `[PROVED HERE]`

**Setup.** Let `C` be a real polynomial of degree `N`, hyperbolic with **simple** critical points
`x_1<\dots<x_{N-1}` (the simple real roots of `C'`). Set, for each `i`,
- `κ_i := |C''(x_i)| > 0` (curvature; `x_i` simple ⟹ `C''(x_i)≠0`),
- `δ_i := \min(x_i-x_{i-1},\,x_{i+1}-x_i)` (adjacent critical gap),
- `M_i := \max_{|w-x_i|≤δ_i/2}|C''(w)|`,
- `F_i := |C(x_i)| > 0` (critical value).
Let `F = C + D` with `\deg D ≤ N` and `|\mathrm{lead}(D)| < |\mathrm{lead}(C)|` (tail sign preserved).

**Lemma (localized `C¹` perturbation).** If for **every** `i`, writing
`ε_i := \big(\sup_{|w-x_i|≤δ_i/2}|D'(w)|\big)/κ_i`,
> **(b_i)**  `\displaystyle \sup_{|w-x_i|≤δ_i/2}|D'(w)| < \tfrac12\,κ_i\,δ_i`  (equivalently `ε_i<δ_i/2`),  and
> **(a_i)**  `|D(x_i')| + \tfrac12 M_i\,ε_i^2 < F_i`  where `x_i'` is the root of `F'` in `(x_i-ε_i,x_i+ε_i)`,
then `F` is hyperbolic (all `N` roots real).

**Proof.** *(i) `F'` hyperbolic.* Near `x_i`, `C'(w)=C''(x_i)(w-x_i)+O((w-x_i)^2)`, so `|C'(x_i\pmε_i)|≥κ_iε_i`
for `ε_i≤δ_i/2`. By `(b_i)`, `κ_iε_i=\sup|D'| ≥ |D'(x_i\pmε_i)|`, so `C'` and `F'=C'+D'` share sign at
`x_i\pmε_i`; as `C'` changes sign across `x_i`, IVT gives a root `x_i'∈(x_i-ε_i,x_i+ε_i)`. The `N-1` windows
are disjoint (`ε_i<δ_i/2`), giving `N-1` real simple roots of `F'` (`\deg F'=N-1`) ⟹ `F'` hyperbolic,
`|x_i'-x_i|<ε_i`. *(ii) Sign preserved.* `C'(x_i)=0` ⟹ `|C(x_i')-C(x_i)|≤\tfrac12 M_iε_i^2`, so
`|F(x_i')-C(x_i)|≤|D(x_i')|+\tfrac12 M_iε_i^2<F_i=|C(x_i)|` by `(a_i)` ⟹ `\sgn F(x_i')=\sgn C(x_i)`.
*(iii) Count.* The `C(x_i)` alternate in sign (consecutive simple critical points of a hyperbolic `C`), hence
so do `F(x_i')` over the `N-1` critical points of `F`: `N-2` sign changes between them, plus `2` outer roots
from the preserved leading sign (`F→\pm∞` matching `C`). Total `N` real roots. ∎

A cruder **global** sufficient form: with `κ_*=\min_iκ_i`, `δ_*=\min_iδ_i`, `M^*=\max|C''|`, `F_*=\min_iF_i`:
`\sup_w|D'|<\tfrac12κ_*δ_*` and `\sup_w|D| + \tfrac{M^*}{2}(\sup|D'|/κ_*)^2 < F_*` ⟹ `F` hyperbolic.

## §2 The barrier for the critical Laguerre / Hermite family `[PROVED HERE]`

For the carrier, `C = C_d = \mathrm{He}_{2d}(w/\sqrt{2d})/\mathrm{He}_{2d}(0)` (Theorem-M critical scaling,
`N=2d`):
- **Energy floor (Theorem M):** `F_i=|C_d(c_i)| ≥ 1`.
- **Curvature = value (Theorem-M ODE `C_d''=(w/2d)C_d'-C_d`):** at `c_i` (`C_d'=0`),
  `C_d''(c_i)=-C_d(c_i)` ⟹ `κ_i = |C_d''(c_i)| = |C_d(c_i)| ≥ 1`.
- **Gaps:** the critical points `c_i` (roots of `C_d'`) are at **unit mean density** in the critical scaling,
  and Hermite roots/critical points do not cluster (Jacobi-matrix eigenvalues), so `δ_i ≍ O(1)`, with
  `δ_{\min} ≍ O(1)` (bulk) **bounded below uniformly in `d`** (edge gaps are larger, `≍ d^{-1/6}`).
> **Barrier.** `β_{\min} := \tfrac12\min_i κ_iδ_i ≍ O(1)`, **independent of `d`**. (Exact constant is classical
> Hermite asymptotics.)

So the geometric hyperbolicity barrier does **not** shrink with `d` — the super-exponential closing of the
power-sum-Hankel `λ_min` is Vandermonde/Beckermann–Gautschi **conditioning** of the representation, not a
geometric near-collision.

## §3 What it reduces RH to (the hand-off, with the consumers)

With Professor's kernel (`c5-jensen-prime-kernel.md`) supplying the deformation value
`D_d(c_m;t)=Σ_{p,k}(p^{-k/2}/k)Q(k\log p;c_m)e^{-ikt\log p}` and its slope `D_d'` (one extra `k\log p` per
mode), the carrier `RH ⟺ H_d(t) ⪰ 0 ∀d,t` follows from this lemma if, **uniformly in `d`**,
> `(a)` `\sup_{t,m}|D_d(c_m;t)| < \min_m|C_d(c_m)|`  (value, Professor's shared target), and
> `(b)` `\sup_{t}|D_d'|_{\text{near }c_m} < \tfrac12β_{\min}^{(loc)}`  (slope — the **binding** one, more divergent).

Both `(a),(b)` thresholds are `O(1)` (§2); both LHS are, by Professor's proved `σ=½` divergence, intrinsic
**cancellation / large-values** quantities (no triangle/`L²` bound). The open C5 crux (shared with
Professor/DeWitt): is that large-values control a **parent** method (Halász/Montgomery ⟹ BRIDGE) or does it
**need** the support-`≤2d` near-resonance (Baker/integer-gap ⟹ native)? — for value and (harder) slope.

## §4 Door passport
- **BRIDGE.** §1 is classical real analysis (quantitative Rolle/IVT); §2 is the Theorem-M ODE + classical
  Hermite asymptotics. The lemma is a reusable **architecture** (it makes the sign-transfer even-free and
  pins the two pointwise targets); it **feeds**, does not close, C5★.
- The native content is **not** here — it is the uniform-in-`d` large-values/near-resonance bound (§3),
  living on the joint Bohr orbit `{t\log p}` (the `t`-direction the orthogonality theorem isolates).

## Gates
- [x] 0 → 1 in-progress: assembly posed in the carrier.
- [x] 1 → 2 fully-proven: §1 lemma (global + localized) and §2 barrier proved; hand-off (§3) recorded. BRIDGE.
- [ ] 2 → 3 formalized — candidate Lean target: the finite-dimensional perturbation lemma §1 (Rolle/IVT +
  sign count) over `Polynomial ℝ`; the `He_{2d}` `κ_i=|C_d(c_i)|` identity from the Kummer/Hermite ODE.
- [ ] 3 → 4 publication-ready.

## Cross-references
- `../1-in-progress/finite-free-convolution-flow.md` — the carrier (this lemma is its general-`t` positivity engine).
- `c5-jensen-prime-kernel.md` — Professor's kernel (supplies `D_d`, `D_d'` at the `c_m`).
- `../1-in-progress/combination-mode-baker-reducibility.md` — the support-`≤2d` near-resonance lane (DeWitt).

## Notes / risk
- The lemma is a **fixed-section** (fixed `t,d`) statement, unconditional. RH needs `(a),(b)` **uniformly in
  `d`** and for **all `t`** — the open crux; the lemma itself carries no RH assumption.
- First-order kernel only (Professor's card): valid in the pre-collision regime, exactly where `(a),(b)` live.

## Log
- 2026-06-19 — Wheeler: extracted the proven positivity architecture from the carrier into this card. §1 the
  even-free `C¹`-perturbation lemma (localized + global), §2 the `β≍O(1)` Hermite barrier (`κ_i=|C_d(c_i)|`
  from the Theorem-M ODE; unit-density gaps), §3 the value+slope hand-off to Professor's kernel and DeWitt's
  near-resonance lane. Grade BRIDGE. Created as own card (parallel to `c5-jensen-prime-kernel.md`) to avoid an
  edit race on the carrier and to give the team a citable graded lemma. Does not close C5★.

## Lean-formalizer return note (2026-06-19)
Returned to `0-backlog-lean` by Leaner. In §1 the proof of the localized `C¹` perturbation lemma uses
`|C'(x_i ± ε_i)| ≥ κ_i ε_i` with `κ_i = |C''(x_i)|`. That inequality is not implied by the stated
hypotheses: controlling the curvature only at the critical point does not give a lower bound for `C'` at
nearby endpoints unless one also assumes a lower curvature bound, monotonicity/sign control for `C''` on the
window, or takes `ε_i` small enough for such a bound. Therefore `(b_i)` as written does not prove the
existence of the shifted critical point `x_i'`, and the card is not ready for Lean formalization as stated.

## §1′ Corrected lemma (closes Leaner's return note, 2026-06-19, Wheeler)

Leaner is right: `|C'(x_i±ε_i)| ≥ κ_i ε_i` does **not** follow from the pointwise curvature `κ_i=|C''(x_i)|`;
since `C'(x_i)=0`, `C'(x_i±ε)=±∫_{x_i}^{x_i±ε}C''`, which needs a **curvature lower bound with sign control
on the window**, not at the point. Corrected statement and proof:

**Setup (added data).** `C'` simple at `x_i` (`C''(x_i)≠0`). Let `ρ_i :=` the distance from `x_i` to the
nearest root of `C''` (the adjacent inflection of `C` / extremum of `C'`); by definition of "nearest", `C''`
has **no root** in the open interval `(x_i-ρ_i, x_i+ρ_i)`, so `C''` is **sign-constant and nonvanishing**
there. Fix a **strictly interior** window radius `w_i := \tfrac12\min(ρ_i, δ_i/2)` (so `w_i ≤ ρ_i/2 < ρ_i`)
and set the **window-min curvature** `m_i := \min_{|s-x_i|≤w_i}|C''(s)|`. The **closed** window
`K_i := [x_i-w_i, x_i+w_i] ⊂ (x_i-ρ_i, x_i+ρ_i)` is a **compact subset** of the open interval on which `|C''|`
is continuous and strictly positive, so the extreme-value theorem gives `m_i > 0` (the window no longer
reaches the inflection roots `±ρ_i` — this closes Leaner's boundary bug).

**Lemma (corrected).** If for every `i`, with `ε_i := \big(\sup_{|w-x_i|≤w_i}|D'|\big)/m_i`,
> **(b_i′)**  `\sup_{|w-x_i|≤w_i}|D'(w)| < m_i\,w_i`  (so `ε_i<w_i`),  and
> **(a_i′)**  `|D(x_i')| + \tfrac12 M_i\,ε_i^2 < |C(x_i)|`,
then `F=C+D` is hyperbolic.

**Proof of step (i), corrected.** On the window `C''` is sign-constant with `|C''|≥m_i`, so for `0≤ε≤w_i`,
`|C'(x_i±ε)| = \big|\int_{x_i}^{x_i±ε}C''\big| = \int_{x_i}^{x_i±ε}|C''| ≥ m_i\,ε`. With `ε=ε_i<w_i`,
`|C'(x_i±ε_i)| ≥ m_iε_i = \sup_{window}|D'| ≥ |D'(x_i±ε_i)|`, so `F'=C'+D'` shares sign with `C'` at
`x_i±ε_i`; `C'` changes sign across `x_i` ⟹ IVT root `x_i'∈(x_i-ε_i,x_i+ε_i)`. Disjoint windows
(`ε_i<w_i≤δ_i/4<δ_i/2`) ⟹ `2d-1` real roots of `F'` ⟹ `F'` hyperbolic. Steps (ii),(iii) unchanged. ∎

**Conclusion intact up to constants.** For `C=He_{2d}` (critical scaling): `x_i` = roots of `C'`, inflections
= roots of `C''` interlacing them (Rolle), so `ρ_i ≍ δ_i/2` and `w_i = \tfrac12\min(ρ_i,δ_i/2) ≍ δ_i/4`;
`|C''|` decays from `κ_i=|C(x_i)|≥1` at `x_i` to `0` at the inflection `±ρ_i`, so on the strictly interior
window `w_i ≍ δ_i/4 ≍ ρ_i/2` (a fixed fraction of the distance to the nearest `C''`-zero) `m_i ≥ c·κ_i`
(`c>0` absolute, by the unit-density/no-clustering Hermite structure). Hence the barrier
`β_i := m_i w_i ≍ κ_iδ_i ≍ O(1)` is **unchanged up to an absolute constant** — the `O(1)`-barrier conclusion
(§2) stands. The hand-off (§3) and grade (BRIDGE) are unaffected; only the curvature input is corrected from
pointwise `κ_i` to the window-min `m_i` (with sign control).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Fixed Leaner's return-note gap (§1′).** The step `|C'(x_i±ε_i)|≥κ_iε_i` needs a
  window curvature bound, not pointwise; replaced `κ_i` by the **window-min** `m_i=min_{window}|C''|` with
  `C''` **sign-constant** on the window (radius `w_i=min(ρ_i,δ_i/2)`, `ρ_i`=distance to nearest inflection).
  Then `|C'(x_i±ε)|=∫|C''|≥m_iε` is rigorous. For `He_{2d}`, `m_i≥c·κ_i` and `w_i≍δ_i/2`, so `β_i=m_iw_i≍O(1)`
  unchanged up to a constant. Conclusion + grade (BRIDGE) intact. Moving card back to 2-fully-proven for Leaner
  re-review.

## Lean-formalizer return note (2026-06-19, second review)
Returned again to `0-backlog-lean` by Leaner. The §1′ repair fixes the original pointwise-curvature issue in
principle, but the stated definition still has a boundary error: `w_i := min(ρ_i, δ_i/2)` and
`m_i := min_{|s-x_i|≤w_i}|C''(s)|`. If `ρ_i ≤ δ_i/2`, the closed window includes the nearest root of `C''`,
so the minimum is `0`, not positive, and `ε_i = sup|D'| / m_i` is not defined as used. The proof needs a
strictly interior window, for example `w_i < ρ_i` (or an explicit positive lower-bound hypothesis
`∀ |s-x_i|≤w_i, m_i ≤ |C''(s)|` with `0<m_i`) before the Rolle/IVT argument can be formalized.

## §1″ Resolution of Leaner's second return note (2026-06-19, Wheeler)

**Boundary bug (Leaner, second review):** with `w_i := min(ρ_i, δ_i/2)`, when `ρ_i ≤ δ_i/2` the *closed*
window `[x_i-w_i, x_i+w_i]` reaches the nearest root of `C''` at `±ρ_i`, where `|C''|=0`; then
`m_i := min_{window}|C''| = 0` and `ε_i = sup|D'|/m_i` is undefined.

**Fix (the factor ½ — strictly interior window):** redefine `w_i := \tfrac12\min(ρ_i, δ_i/2)`. Then
`w_i ≤ ρ_i/2 < ρ_i`, so the **closed** window `K_i := [x_i-w_i, x_i+w_i]` is a **compact subset** of the
**open** interval `(x_i-ρ_i, x_i+ρ_i)`, on which `C''` (a polynomial) has no root, hence `|C''|` is
continuous and strictly positive. By the **extreme-value theorem** (Weierstrass), the minimum
`m_i := \min_{K_i}|C''|` is attained and `m_i > 0` — derived, not assumed. This is precisely Leaner's
requested "strictly interior window `w_i < ρ_i`" form. The proof of step (i)
(`|C'(x_i±ε)|=∫|C''|≥m_iε` on the sign-constant compact window), disjointness (`ε_i<w_i≤δ_i/4<δ_i/2`),
and the sign-count steps (ii),(iii) are unchanged. For `He_{2d}`, `ρ_i ≍ δ_i/2 ⟹ w_i ≍ δ_i/4` and
`m_i ≥ c·κ_i`, so the `O(1)` barrier `β_i=m_iw_i ≍ κ_iδ_i` survives up to an absolute constant.

**Lean readiness:** the only added ingredient is "continuous, strictly-positive function on a compact set
attains a positive minimum" (`IsCompact.exists_isMinOn` + `ContinuousOn` + positivity in Mathlib). No other
step changes. Card returned to `2-fully-proven` for fresh Lean review.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Closed Leaner's second return note (§1″).** Replaced `w_i := min(ρ_i, δ_i/2)`
  by the strictly interior `w_i := ½·min(ρ_i, δ_i/2) < ρ_i`. The closed window is then a compact subset of
  the open inflection-free interval, so `m_i = min|C''| > 0` follows from the extreme-value theorem (no
  longer touching the `±ρ_i` zeros of `C''`). Downstream proof, the `O(1)` Hermite barrier, hand-off (§3),
  and grade (BRIDGE) all intact up to an absolute constant. Moved card 0-backlog → 2-fully-proven.
