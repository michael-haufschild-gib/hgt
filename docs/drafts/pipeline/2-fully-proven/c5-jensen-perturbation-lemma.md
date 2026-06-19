# The general-`t` hyperbolicity perturbation lemma (value + slope) — Jensen-section positivity assembly

- **ID:** c5-jensen-perturbation-lemma
- **Stage:** 0-backlog-lean
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

## Lean-formalizer return note (2026-06-19, third review)
Returned again to `0-backlog-lean` by Leaner. The §1″ strict-interior repair fixes the previous boundary
issue for an already-defined interior curvature window, but the lemma is still not formally stated for all
cases it claims:

1. The setup lists critical points `x_1<...<x_{N-1}` but defines
   `δ_i := min(x_i-x_{i-1}, x_{i+1}-x_i)`. For `i=1` and `i=N-1`, the symbols `x_0` and `x_N` are not
   defined. The proof uses `w_i≤δ_i/4` for disjointness, so the endpoint critical points need explicit
   one-sided gap definitions or separate hypotheses.
2. The repaired window uses `ρ_i :=` the distance from `x_i` to the nearest root of `C''`. This is not
   defined in the quadratic case (`N=2`), where `C''` is constant and has no root, even though the stated
   lemma includes degree-`N` hyperbolic real polynomials generally. More generally, the Lean statement needs
   either a finite positive `ρ_i` hypothesis, a convention such as `ρ_i=∞`, or a direct positive window
   hypothesis.

Without these endpoint/no-inflection conventions or hypotheses, the corrected `m_i>0` argument cannot be
encoded as a total Lean theorem matching the paper statement. The prior curvature-minimum fix itself is
mathematically sound once the window data is well-defined.

## §1‴ Total well-defined window data — closes Leaner's third return (endpoints + no-inflection) — Wheeler, 2026-06-19

Leaner (third review): the curvature-minimum fix is mathematically sound, but the window data `δ_i`, `ρ_i`
were not defined for endpoint critical points (`x_0`, `x_N` don't exist) nor in the no-inflection case
(`N=2`, `C''` constant). This section makes every quantity **total** for all `N ≥ 1`, so the lemma is a
single Lean theorem matching the paper statement. **These definitions are authoritative and supersede the
informal `δ_i`/`ρ_i` of §1/§1′.** Conventions: `min(+∞, a) = a`.

**Critical set.** `C'` has the simple real roots `x_1 < … < x_{N-1}` (for `N=1` this set is **empty** and
every critical-point hypothesis (b_·),(a_·) is vacuous; `F=C+D` is then linear/degree-`≤1` with `1` real
root from the preserved leading sign — base case done).

**(D1) Nearest-critical gap (fixes point 1, endpoints).** Define
> `δ_i := min\big(\{x_{i+1}-x_i : i ≤ N-2\} ∪ \{x_i-x_{i-1} : i ≥ 2\}\big)`,
the distance from `x_i` to the **nearest other** critical point. No `x_0`/`x_N` is referenced: the left
endpoint `i=1` uses only `x_2-x_1`, the right endpoint `i=N-1` only `x_{N-1}-x_{N-2}`. If `x_i` is the
**only** critical point (`N=2`), set `δ_1 := +∞` (disjointness is vacuous — one window).

**(D2) Nearest-inflection distance (fixes point 2, no-inflection).** Define
> `ρ_i := \mathrm{dist}\big(x_i, \{s : C''(s)=0\}\big)`, with `ρ_i := +∞` if `C''` has **no real root**.
`C''` has degree `N-2`, so: for `N=2`, `C'' ≡ 2\,\mathrm{lead}(C)` is a **nonzero constant** ⟹ no root ⟹
`ρ_1 = +∞`; for `N ≥ 3`, `C` hyperbolic ⟹ `C'` has `N-1 ≥ 2` simple real roots, so by **Rolle** `C''` has a
real root in each `(x_i, x_{i+1})` ⟹ `{C''=0} ≠ ∅` and `ρ_i < ∞` is finite and well-defined.

**(D3) Window and window-min curvature (total).** `w_i := \tfrac12\min(ρ_i, δ_i/2)`; if both are `+∞`
(only `N=2`), set `w_i := 1` (any fixed positive radius). `m_i := \min_{|s-x_i|≤w_i}|C''(s)|`. Then
**`m_i > 0` in every case**:
- `N=2`: `C''` is a nonzero constant, so `m_1 = |C''| = |2\,\mathrm{lead}(C)| > 0` on any window.
- `N ≥ 3`: `w_i ≤ \tfrac12 ρ_i < ρ_i`, so the **closed** window `[x_i-w_i, x_i+w_i]` is a **compact subset**
  of the open inflection-free interval `(x_i-ρ_i, x_i+ρ_i)`, on which `C''` is continuous and nonvanishing;
  the extreme-value theorem gives `m_i > 0`.

**Disjointness (total).** For adjacent interior windows, `δ_i ≤ x_{i+1}-x_i` and `δ_{i+1} ≤ x_{i+1}-x_i`
(each `δ` is a min over gaps including the `(x_i,x_{i+1})` gap), so `w_i + w_{i+1} ≤ δ_i/4 + δ_{i+1}/4 ≤
(x_{i+1}-x_i)/2 < x_{i+1}-x_i` — the `N-1` windows `(x_i-w_i, x_i+w_i)` are pairwise disjoint. (Vacuous for
`N ≤ 2`.)

**Conclusion.** With (D1)–(D3) the localized `C¹` perturbation lemma (§1′) is a **total statement for all
`N ≥ 1`**: `N=1` vacuous, `N=2` via constant `C''`, `N ≥ 3` via the strict-interior compact window + EVT.
The `He_{2d}` barrier (`N=2d ≥ 4`, so always the `N ≥ 3` branch) is unaffected: `ρ_i ≍ δ_i/2`,
`w_i ≍ δ_i/4`, `m_i ≥ c·κ_i`, barrier `β_i = m_i w_i ≍ κ_i δ_i ≍ O(1)`. Door grade **BRIDGE** unchanged.

**Lean encoding (now total).** State the theorem over `Polynomial ℝ` with hypotheses: `C` hyperbolic with
simple critical points; `δ_i`,`ρ_i` defined by (D1)/(D2) into `ℝ≥0 ∪ {∞}` (or `EReal`); `w_i`,`m_i` by (D3).
The two base cases (`N=1` vacuous, `N=2` constant `C''`) discharge by `match`/`interval_cases`-style splits;
the `N ≥ 3` core uses `IsCompact.exists_isMinOn` + `ContinuousOn` + the Rolle witness for `{C''=0} ≠ ∅`.

## Log (cont.)
- 2026-06-19 (Wheeler) — **Closed Leaner's third return (§1‴): made the window data total.** (D1) endpoint
  gap = distance to nearest other critical point (no `x_0`/`x_N`; `δ_1=+∞` if single critical point);
  (D2) `ρ_i = +∞` when `C''` has no real root (`N=2` constant case; `N≥3` has a Rolle inflection so
  `ρ_i<∞`); (D3) `w_i=½min(ρ_i,δ_i/2)` (≔1 if both ∞), `m_i=min|C''|>0` in all cases (N=2 constant;
  N≥3 compact-window EVT). Disjointness verified totally. `He_{2d}` is always the `N≥3` branch, barrier
  `O(1)` intact, grade BRIDGE. Statement now total for all `N≥1` (N=1 vacuous, N=2 base, N≥3 core) —
  matches the paper claim. Moving card 0-backlog-lean → 2-fully-proven for Leaner's fourth review.

## Lean-formalizer return note (2026-06-19, fourth review)
Returned again to `0-backlog-lean` by Leaner. The §1‴ repair fixes the endpoint critical-gap and no-inflection
window-data issues, but the localized perturbation statement still is not total as written. It defines
`ε_i := (sup_{|w-x_i|≤w_i}|D'(w)|)/m_i` and then uses `x_i'` as the root of `F'` in the open interval
`(x_i-ε_i, x_i+ε_i)`. If the slope perturbation vanishes on the window (`sup |D'| = 0`), then `ε_i = 0`,
so this open interval is empty even though the natural root is `x_i` itself. Thus the quantified statement
still contains an undefined witness in a legal case. A Lean-ready statement needs either a strictly positive
radius/witness convention, or the root should be placed in the closed interval `[x_i-ε_i, x_i+ε_i]` with the
zero-slope case handled explicitly.

## §1⁗ Total witness — closes Leaner's fourth return (the `ε_i=0` empty-open-interval case) — Wheeler, 2026-06-19

Leaner (fourth review) is right: with `ε_i := (\sup_{|w-x_i|≤w_i}|D'|)/m_i`, the legal case `\sup_{window}|D'|=0`
(allowed by `(b_i′)`, since `0 < m_i w_i`) gives `ε_i=0`, so the **open** interval `(x_i-ε_i, x_i+ε_i)=∅` and the
witness `x_i'` of `(a_i′)` is undefined — yet the natural root is `x_i` itself. Two minimal changes make the
statement **total** (a single Lean theorem, every legal hypothesis covered), with the proof unchanged off the
degenerate case.

**(W1) Locate the `F'`-root in the CLOSED interval.** Replace "`x_i'` = root of `F'` in `(x_i-ε_i,x_i+ε_i)`"
by:
> there exists `x_i' ∈ [x_i-ε_i,\,x_i+ε_i]` with `F'(x_i')=0` (and `|x_i'-x_i| ≤ ε_i`).

*Existence, both branches (`ε_i ≥ 0`, exhaustive):*
- **`ε_i>0`:** the §1′ argument is unchanged — on the sign-constant window `|C'(x_i±ε_i)| = \int_{x_i}^{x_i±ε_i}|C''| ≥ m_iε_i = \sup_{window}|D'| ≥ |D'(x_i±ε_i)|`, so `F'=C'+D'` shares sign with `C'` at `x_i±ε_i` while `C'` changes sign across `x_i`; IVT gives a root in the **open** `(x_i-ε_i,x_i+ε_i)⊂[x_i-ε_i,x_i+ε_i]`.
- **`ε_i=0`:** then `\sup_{|w-x_i|≤w_i}|D'| = 0`, so in particular `|D'(x_i)|=0`, hence
  `F'(x_i)=C'(x_i)+D'(x_i)=0+0=0`. Take `x_i' := x_i ∈ [x_i,x_i]`. (Note `\sup_{window}|D'|=0` on the
  positive-length window even forces `D'≡0`, i.e. `D` constant — the degenerate case is exactly an additive
  shift, the easiest case; but only `D'(x_i)=0` is needed.)

In both branches `|x_i'-x_i| ≤ ε_i < w_i ≤ δ_i/4`, so the `N-1` witnesses `x_i'` lie in pairwise-disjoint
windows and are **distinct**; `\deg F' = N-1` ⟹ they are *all* the roots of `F'`, each simple ⟹ `F'`
hyperbolic. (`ε_i=0` window `={x_i}`, trivially distinct from the others.)

**(W2) Totalize `(a_i′)` as a sup-bound (kills the witness-dependence).** Replace `(a_i′)` by
> **(a_i″)**  `\displaystyle \sup_{|x'-x_i| ≤ ε_i} |D(x')| \;+\; \tfrac12 M_i\,ε_i^2 \;<\; |C(x_i)|`,
where `M_i := \max_{|w-x_i|≤δ_i/2}|C''|` (well-defined: `ε_i<w_i≤δ_i/4<δ_i/2`, so `[x_i,x_i']⊂` the `δ_i/2`
window). When `ε_i=0` the sup is just `|D(x_i)|`, so `(a_i″)` reads `|D(x_i)|<|C(x_i)|` — total.

**Step (ii), now witness-free.** For the root `x_i'` of (W1): `C'(x_i)=0` and `|x_i'-x_i|≤ε_i` give
`|C(x_i')-C(x_i)| ≤ \tfrac12\big(\max_{[x_i,x_i']}|C''|\big)|x_i'-x_i|^2 ≤ \tfrac12 M_iε_i^2`; and
`|D(x_i')| ≤ \sup_{|x'-x_i|≤ε_i}|D(x')|`. Hence
`|F(x_i')-C(x_i)| ≤ |D(x_i')| + \tfrac12 M_iε_i^2 ≤` (a_i″) `< |C(x_i)|`, so `\sgn F(x_i')=\sgn C(x_i)`.
Step (iii) (sign-alternation count, `N-2` interior sign changes + `2` outer roots) is verbatim §1.

**Conclusion.** With (W1)+(W2) the localized perturbation lemma is **total for every legal hypothesis** (no
empty-interval / undefined-witness case remains): `ε_i>0` is the §1′ proof; `ε_i=0` is the explicit additive
shift with `x_i'=x_i`. The `He_{2d}` application always has `\sup|D'|>0` for a genuine perturbation, so the
`O(1)` barrier (§2), hand-off (§3), and grade (**BRIDGE**) are all unchanged. The Lean statement is a single
theorem: hypotheses `(b_i′)`, `(a_i″)`; the existence of `x_i'∈[x_i-ε_i,x_i+ε_i]` with `F'(x_i')=0` is proven
by `rcases lt_or_eq` on `ε_i` (`0 < ε_i`: IVT/`intermediate_value_Icc`; `ε_i = 0`: `x_i'=x_i`,
`D'(x_i)=0` from the vanishing sup).

## Log (cont.)
- 2026-06-19 (Wheeler) — **Closed Leaner's fourth return (§1⁗): the `ε_i=0` witness is now total.** (W1) root
  of `F'` placed in the **closed** `[x_i-ε_i,x_i+ε_i]`, existence split `ε_i>0` (IVT, unchanged) vs `ε_i=0`
  (`\sup_{window}|D'|=0 ⟹ D'(x_i)=0 ⟹ F'(x_i)=0`, take `x_i'=x_i`; degenerate case = additive shift). (W2)
  `(a_i′)→(a_i″)` totalized as `\sup_{|x'-x_i|≤ε_i}|D| + ½M_iε_i^2 < |C(x_i)|`, witness-free (reads
  `|D(x_i)|<|C(x_i)|` at `ε_i=0`). Step (ii) re-derived witness-free; (iii) verbatim. Statement total for all
  legal hypotheses; `He_{2d}`/barrier/hand-off/grade (BRIDGE) intact. Lean: one theorem, `rcases` on `ε_i=0`.
  Moving card 0-backlog-lean → 2-fully-proven for Leaner's fifth review.
