# The Arakelov Height of the Zeros (B7) — the critical line as the unit circle, RH as Bogomolov minimality

> **NASCENT / SEARCH channel. Air-marked; no proof of RH claimed.** District D2/B7 of the charter (`hypertranscendental_galois_program.md`). Supplies the height whose absence is the §17.3 *height-vacuum* meta-theorem of `…field_foundations.md`. Core geometry is Bombieri–Lagarias (the `1−1/ρ` coordinate, Li's criterion); the **height / product-formula / Bogomolov framing is the contribution here.** Numerics archived: `computations/arakelov_w_coordinate/`.

## 1. The multiplicative coordinate and the unit-circle theorem `[THEOREM — Bombieri–Lagarias; re-derived + certified]`

For a zero `ρ = β + iγ` define the **multiplicative coordinate**
```
   w_ρ := 1 − 1/ρ = (ρ−1)/ρ .
```
Elementary computation (with `A := β²+γ²`):
```
   |w_ρ|² − 1 = A(1 − 2β)/A² = (1−2β)/A .
```
Hence the **trichotomy**:
```
   Re ρ = ½  ⟺  |w_ρ| = 1   (ON the unit circle) ;
   Re ρ > ½       ⟹  |w_ρ| < 1   (INSIDE) ;
   Re ρ < ½       ⟹  |w_ρ| > 1   (OUTSIDE) .
```
> **The critical line is exactly the unit circle in the `w`-coordinate.** *Certified* (`computations/arakelov_w_coordinate/`): for the first 50 genuine zeros `|w_ρ|=1` to `<10⁻³¹`; off-line test points obey the inside/outside dichotomy with the predicted sign `(1−2β)`.

**Lean note (ledger-proven scalar skeleton).** `WCoordinate.lean` proves the exact finite algebra behind §§1–2:
`wCoordinate_normSq_sub_one` proves `|1−1/z|²−1=(1−2Re z)/|z|²` for `z≠0`,
`wCoordinate_normSq_eq_one_iff` proves the norm-square unit-circle criterion `|w(z)|²=1 ↔ Re z=1/2`, and
`wCoordinate_sigma_mul` / `wCoordinate_sigma_eq_inv` prove the FE-pair identity
`w(z)w(1−z)=1` / `w(1−z)=w(z)⁻¹` for `z≠0,1`. This is only scalar coordinate algebra: the Hadamard/global
product over zeros, Arakelov height, Bogomolov-minimality, Li positivity, and RH remain SEARCH-side.

## 2. The functional equation is inversion `w ↦ 1/w` — a product formula for free `[PROVED HERE]`

Compute the FE partner's coordinate:
```
   w_{1−ρ} = 1 − 1/(1−ρ) = −ρ/(1−ρ) = ρ/(ρ−1) = 1/w_ρ .
```
So `w_ρ · w_{1−ρ} = 1` **identically** (for every zero, on or off the line). Therefore the FE involution `ρ ↔ 1−ρ` is **inversion on the coordinate**, and taking `log|·|`:
```
   log|w_ρ| + log|w_{1−ρ}| = 0          (THE PRODUCT FORMULA, exact, from the FE).
```
*Certified:* `|w_ρ|·|w_{1−ρ}| = 1.0` to machine precision, even off-line (`β=0.7`: `0.99900…×1.00100…=1`).

> **This is the Arakelov skeleton.** A height with a product formula needs: (i) local sizes `|·|_v`, (ii) a global relation `Σ_v log|·|_v = 0`. Here the two ends of an FE-orbit `{ρ, 1−ρ}` are the "two places" and the FE is the product formula. The unit circle `{|w|=1}` is the **norm-one (`Σ`-balanced *and* termwise-zero) locus** — the analog of the `S`-units / the Kronecker "absolute value 1 at every place" locus.

## 3. The canonical height and RH = Bogomolov minimality `[REFRAME]`

Define the **canonical height** of a zero
```
   ĥ(ρ) := |log|w_ρ||  =  |log|1 − 1/ρ||  ≥ 0,    with   ĥ(ρ) = 0  ⟺  Re ρ = ½ .
```
This is a **Kronecker-type height**: it vanishes exactly on the canonical locus (the critical line = unit circle), precisely as the Weil height of an algebraic number vanishes exactly on the roots of unity (`|α|_v=1 ∀v`, Kronecker). The FE product formula (§2) makes `ĥ` *balanced* over each orbit; RH is the stronger termwise statement:
```
   RH  ⟺  ĥ(ρ) = 0 for every zero  ⟺  the zero-divisor is BOGOMOLOV-MINIMAL
        ⟺  every w_ρ lies on the unit circle (the spectrum is a "set of w-roots-of-unity").
```
> **RH = Bogomolov height-minimality of the spectrum.** Off-line zeros are *positive-height* excess (one inside, its FE-partner outside, balancing to zero but each non-zero) — exactly the configuration the Bogomolov/Ullmo–Zhang philosophy forbids for a "special" 0-cycle. RH says the zeros are the height-minimizing (canonical) configuration. This is the B7 face of the charter's Face A.

## 4. Li's criterion is the height's positivity, and Bilu equidistribution is its shadow `[REFRAME; ties to §20, `li_closedform/`]`

The Li coefficients are the `w`-power sums:
```
   λ_n = Σ_ρ [1 − (1 − 1/ρ)^n] = Σ_ρ (1 − w_ρ^n),     RH ⟺ λ_n ≥ 0 ∀n  (Li).
```
On the unit circle `w_ρ = e^{iθ_ρ}`, so `λ_n = Σ_ρ(1 − e^{inθ_ρ})` and **Li-positivity = Fejér positivity of the angles `{θ_ρ}`** = the `w_ρ` are not only on the circle but **equidistribute** with a positive-definite defect. This is **Bilu's theorem in reverse**: small canonical height (`ĥ→0`, §3) forces equidistribution on the unit circle; the Li-positive, equidistributed `{θ_ρ}` is the Bilu small-height limit measure. Face A (Hankel positivity of `s_m`, foundations §22) and Li-positivity are the **same statement about the `w`-angles**; `li_closedform/` already certifies the archimedean-vs-prime split `λ_n = Z_n − A_n` that RH needs (`Z_n ≻ A_n`).

## 5. The finite places — the genuine Weil height (open core) `[OPEN CORE]`

§§1–4 give only the **archimedean** local height (`log|w_ρ|` is one complex absolute value). A true Weil height is `Σ_v`. The finite-place local heights `λ_p(ρ)` must come from the **explicit formula**: the prime-`p` term `Σ_k (log p) p^{-k/2}(…)` is the `p`-adic contribution of the spectrum, and the explicit formula `Σ_ρ = (poles) − Σ_p − (arch)` is the global product/balance (`prime-zero-period-comparison.md` §1). *Open:* assemble the `λ_p` into a sum-over-places height for which §2's FE product formula is the case `v∈{archimedean orbit}` and the explicit formula is the full `Σ_v λ_v = 0`. Then Northcott + Bogomolov become available as genuine Arakelov theorems.

## 6. What this does and does not do for the transcendence program (honest) `[HONEST LIMITATION]`

- **Does:** supplies the *geometric* height the §17.3 meta-theorem said was missing — the zeros now sit in a height space (`w`-coordinate), with RH = Bogomolov-minimal and the FE = a product formula. The "no canonical locus / no height" gap of §17.3 is **closed for the geometry**.
- **Does NOT (yet):** supply the *Liouville lower bound* (Pillar 3 of the infinite-base S–S, §17.4). `ĥ` is a **Kronecker height that vanishes on the whole canonical locus** — it does not *separate* zeros, so it cannot bound a nonzero auxiliary from below. Liouville needs the **secular-period height** (B2 / foundations §17.4, the heighted `P_k`), a *different* height for a *different* job. Honest split: §17.3's geometry-gap is closed here (B7); §17.4's Liouville-gap stays open (B2). Two heights, two pillars.

**House status.** §1 (unit-circle trichotomy) and §2 (`w_ρ w_{1−ρ}=1`, the FE-as-inversion product formula) are elementary + numerically certified (`arakelov_w_coordinate/`). §3–4 reframe RH as Bogomolov minimality and Li-positivity as Bilu equidistribution on the `w`-circle (rests on §1–2 + the certified `li_closedform/`). §5 (sum-over-places Weil height) and the Liouville pillar (§6) are open. Crosses CITY districts D2 (RH/height), D4 (transcendence/Liouville split), D8 (the `w`-trichotomy and `w_ρw_{1−ρ}=1` are Tier-A Lean-able). Credit: the `1−1/ρ` coordinate and its disc geometry are Bombieri–Lagarias / Li; the height / product-formula / Bogomolov framing is this draft. Next: (i) Lean the trichotomy + `w_ρ w_{1−ρ}=1` (Tier A); (ii) attempt the finite-place `λ_p` from the explicit formula (§5).

---

## 7. The global product formula, and why the finite structure is CYCLE-level not per-zero (corrects §5) `[PROVED HERE + honest correction]`

Attempting §5 (a per-zero finite height `λ_p(ρ)`) exposes a category error worth recording.

**The global product formula `[PROVED HERE]`.** From the Hadamard product `ξ(s)=ξ(0)∏_ρ(1−s/ρ)` (paired) and the FE `ξ(0)=ξ(1)`:
```
   ξ(1) = ξ(0)·∏_ρ(1−1/ρ)   and   ξ(1)=ξ(0)   ⟹   ∏_ρ (1 − 1/ρ) = ∏_ρ w_ρ = 1 ,   i.e.   Σ_ρ log|w_ρ| = 0 .
```
This is the **spectrum-level product formula** — the global `Σ log|·| = 0` — and it is *automatic from the FE*, independent of RH (it is the cycle-sum of §2's pairwise `w_ρ w_{1−ρ}=1`). **RH is the strictly stronger termwise statement** `log|w_ρ|=0 ∀ρ` (every term vanishes, not just the sum) — exactly the Bogomolov-minimal condition of §3. So: product formula = FE (free); Bogomolov-minimality = RH (the content).

**Why §5 (a per-zero finite height) does not exist `[honest correction]`.** A zero `ρ` is a transcendental complex number: it has **no number field, no finite places, no `p`-adic embeddings**. There is no `|ρ|_p`. So a per-zero sum `Σ_v λ_v(ρ)` over finite places `v=p` is ill-posed — §5's premise was wrong. The archimedean Kronecker height `log|w_ρ|` (§§1–4) is genuine and complete *on its own*; there is no per-zero finite companion to it.

**Where the finite places actually live (cycle level) `[REFRAME → Connes–Consani / Deninger; ties to the team's Hodge-index work]`.** The primes enter not against individual zeros but against the **whole zero-cycle** `Z = Σ_ρ [ρ]`. The explicit formula
```
   Σ_ρ ĝ(ρ)  =  (poles)  −  Σ_p Σ_k (log p) g(k log p) p^{-k/2}  −  (arch)
```
is an **arithmetic intersection pairing** `⟨ Z , (prime divisors) ⟩` on the conjectural Arakelov surface (Connes–Consani trace formula; Deninger's cohomology). In this reading:
```
   RH  ⟺  the intersection form on the spectral cycles has Hodge-index signature (1, ∞)
        ⟺  Weil/Bogomolov positivity of ⟨·,·⟩   (one positive direction; the rest negative).
```
This is **the same Hodge-index core** the team already works (`scForm_sigNeg`, the CKS nilpotent orbit `±b²`, the `n₊=1` one-stone face): the finite, cycle-level positivity is the Weil pairing's signature, and B7's per-zero `w`-height is its **archimedean diagonal restriction** (the self-intersection `⟨[ρ],[ρ]⟩_∞ = log|w_ρ|`).

> **B7, resolved into three honest layers.**
> 1. **Archimedean per-zero (PROVEN, §§1–4):** `w`-coordinate, critical line = unit circle, `ĥ=|log|w_ρ||` Kronecker height, RH = Bogomolov-minimal.
> 2. **Global product formula (PROVEN, §7):** `∏_ρ w_ρ=1` from the FE; RH = termwise vanishing.
> 3. **Finite / cycle-level (OPEN = the existing frontier):** explicit formula = Arakelov intersection; RH = Hodge-index `(1,∞)` positivity = the team's `n₊=1` / `scForm` core. *Not a new open problem — it is the known positivity wall, now seen as the finite half of the height.*
>
> The contribution of B7 is layers 1–2 (a clean, certified, FE-compatible **archimedean height** with RH = Bogomolov-minimality) and the honest localization of layer 3 onto the already-identified Hodge-index positivity — *not* a fabricated per-zero `p`-adic height.

**House status (updated).** §§1–2 elementary + certified; §3–4 reframe (Bogomolov/Bilu); §7 adds the proven global product formula `∏w_ρ=1` and corrects §5 — the finite height is cycle-level (Arakelov intersection / Hodge-index), identical to the team's positivity core, **not** per-zero. Open core narrows to: layer 3 = the explicit-formula intersection form's Hodge signature (the standing wall), now explicitly the finite half of the spectral height. Tier-A Lean-able (unchanged): the `w`-trichotomy and `w_ρ w_{1−ρ}=1`; additionally `∏_ρ w_ρ=1` is a clean consequence of the Hadamard/FE pair (Tier B — needs the Hadamard product).

---

## 8. Cross-weld: the no-margin IS the Kronecker-degeneracy of the height (B7 §6 = dyson Thm 7) `[REFRAME — weld]`

dyson's `rh-byproduct-secular-hankel-overdetermination.md` Thm 7 (the no-margin, made exact): a zero displaced off the line by `δ` breaks Toeplitz total positivity, but **the first violated minor has order `→∞` and magnitude `→0` as `δ→0`** — no finite-order certificate. Welding to §6:

**The two are the same phenomenon.** Off-line `β=½+δ`, the `w`-height excess (§1, §3) is
```
   ĥ(ρ) = |log|w_ρ||,    |w_ρ|² − 1 = (1−2β)/A = −2δ/A   ⟹   ĥ(ρ) ≈ δ/A  →  0   (linearly in δ).
```
So the **TP-violation magnitude (dyson Thm 7) and the canonical-height excess (§6) both vanish as `δ/A`** — they are one quantity in two coordinates (Toeplitz minor vs `w`-height). Therefore:

> **The no-margin = the Kronecker-degeneracy of the height.** §6 said `ĥ` is a *Kronecker* height (vanishes on the whole critical line, no uniform floor) and hence cannot serve as a *Liouville* lower bound. dyson's "no finite-order TP certificate" is the **same statement on the Toeplitz face**: there is no fixed order at which positivity is bounded away from failure, because the controlling quantity (`ĥ ≈ δ/A`) has no positive floor off the line. *The no-margin filter, the missing Liouville bound, and the Kronecker (not Liouville) nature of the Bogomolov height are one fact.*

**Three coordinates, one no-margin.** The "order of first violated minor `→∞` as `δ→0`" (dyson Thm 7) is also berry's **resolution law** (finite Weil/Gram certificates need growing dimension to detect off-line zeros nearer the line: `dim_min`: `δ=.31→5`, `.07→9`) and the §16 **discrepancy** growth. Toeplitz-order, certificate-dimension, and equidistribution-resolution are three meters of the same vanishing margin:
```
   δ → 0  ⟹  ĥ ≈ δ/A → 0   (height, §1–6)
            =  Toeplitz first-violated-minor order → ∞, magnitude → 0   (dyson Thm 7)
            =  Weil-certificate dim_min → ∞   (berry resolution law)
            =  discrepancy resolution needed → ∞   (foundations §16).
```

**Consequence for B7's program.** Closing B7's Liouville gap (§6) — finding a height that *separates* zeros (a positive floor off-line) — is **identically** dyson's open inch (a *uniform-in-order* total positivity, a fixed-order certificate). They are not two problems. The unblock would be a height upgrade `Kronecker → Liouville`, i.e. a uniform floor `ĥ(ρ) ≥ c(δ) > 0` with `c` controlled — which is exactly the uniform multiplicity/equidistribution estimate (§16 / B10). *The three drafts (B7 height, dyson Toeplitz, B10/§16 discrepancy) meet on this single missing uniform bound.*

**House status (re §8).** A reframe welding §6 to dyson Thm 7 and berry's resolution law: the no-margin, the missing Liouville floor, and the Kronecker-degeneracy of `ĥ` are one fact, with the common rate `ĥ ≈ δ/A`. No new theorem; the value is the identification that B7's Liouville gap = dyson's uniform-TP inch = the §16 discrepancy = one missing uniform bound. (Respecting dyson's "own file" boundary, this weld lives here, not in their draft; cross-referenced for them.)
