# 06 — Noteworthy Experimental Findings (Consolidated, With Effect Sizes)

> **Scope.** The corpus's noteworthy *computational* findings, consolidated with their effect sizes
> and controls. Two streams: (I) the **light-tower carrier battery** (the `id7xx`/`Rxx` experiments
> distilled in `synthesis.md`), and (II) the **RH-corp numerical lab** (worklogs: faithful-index
> separators, no-margin curves, transcendence PSLQ). Numbers are quoted as recorded in the source
> files. **No new computation; nothing added.** Methodological keepers are at the end. Every finding
> is `[OBSERVED]` unless tagged otherwise; an `[OBSERVED]` finding is an experiment worth banking,
> *not* a proven theorem.

---

## I. The light-tower carrier battery (synthesis §2 catalog)

The discriminating observable everywhere is the weld phase-carrier defect
`Δ(σ,t) = max(log|Γ∞|, log|P|) − log|Γ∞+P|`. Controls: finite Euler `P_N` (`N→∞`),
amplitude-matched random-phase surrogate, and the `σ>1` collapse control.

**A. Existence / non-reproducibility of the carrier**
- **id731/733 (ultradiscrete sign carrier):** true `σ=0.3` positive-fraction **0.8–1.0**, median
  **0.3–0.55**; finite `≈ 0`; random-phase median goes **negative**.
- **Margin-neutralized residual:** after regressing out all amplitude features, true left-strip
  phase residual survives, `σ=0.3` gap **+0.45** over controls; over-controls including `|Γ∞+P|`
  kill it (as they must).

**B. Time-domain coherence (the carrier is alive over long t)**
- **id744 proofreading off-rate:** true has **low entry rate, long positive-run lifetimes**
  (survives depth-16); finite fires often, dies fast. *The weld wins by lifetime, not on-rate.*
- **id750 transition-path softness:** true `Δ=0` crossings are **soft** (edge-softness **~45** vs
  finite **~6–12**).
- **Context-fragility monotone:** true catch-window decays **monotonically (0 violations)** under
  phase-context scrambling; controls keep violations.
- **id752 survival-conditioned spine:** conditioning on survival-to-depth-8 isolates a full-window
  true spine (`σ=0.3` spine-frac **1.0**; finite **~0.05**; random **0**).

**C. 2-D / cross-lane rigidity**
- **id749 zero-shadow topology:** at `R<1.00` true forms **one component spanning σ and t**; finite
  (any `N`) never t-spans (**35–50 fragments**); sparse `p=0.75` destroys, `p=0.90` restores.
- **id768 coupled-reserve frailty:** true low-reserve failures arrive in **coordinated cross-σ
  sheets** (co-failure excess over product/shift nulls); fails for the 2-lane case (genuinely
  multi-lane).
- **id771/772 initial-measure association:** true high-threshold lane fields have **cross-lane
  association excess**; productizing marginals destroys it.

**D. Orientation / signed structure (finite-prime gets the sign backwards)**
- **id758 gate–tension two-clock:** finite-prime phase gates **anti-timed (corr −0.4)** with true
  tension in the strip, **positively timed (+0.4)** at `σ>1`; sign crossing near `σ ≈ 0.6–0.8`.
- **id761 observed-volume covariance:** true **positive** (high values on high-gradient/curvature
  regions); finite/random **negative**; right-strip both negative.
- **id762 phase-space caustic / wrong momentum:** true signed area `∫O dP` has **z ≈ 18**;
  finite-prime phase momentum is **opposite-signed for every cutoff `P = 5…97`** and does not
  converge. *Finite-prime is anti-symplectic relative to the true lift.*

**E. Critical-lane localization**
- **id757 resetting occupation slope:** true reset clocks lane-synchronous across `σ=.3/.5/.7`, but
  reset-age occupation slopes **single out `σ=½`** (**−3.7/−4.2** vs neighbours **−1.1/−1.5**);
  shared-clock control preserves the centre excess for true, kills it for controls.
- **id773 Berry lane-interference switch:** completing `ζ'/ζ → ξ'/ξ` **exactly equalizes** the two
  `σ=½±δ` lane magnitudes at `σ=½` (imbalance **→0**) and reroutes the residual into pure relative
  phase; off-centre, imbalance returns. *Γ-completion = archimedean boundary-condition operator.*

**F. Crossover / selection facets**
- **id734/735 hypercycle specificity:** finite wins broad/amplitude selection; true wins
  **phase-specific** selection.
- **Near-neutral hidden layer:** at `σ≈0.7`, sub-resolution `Δ_true − Δ_finite` has **positive mean
  and compounds** (hidden-fraction **0.71**).

---

## II. The RH-corp numerical lab (worklogs)

### B. Faithful-index separators (the strongest empirical results)

- **`[ledger-grade]` Conductor-5 Weil–Gram separator** (dps40, nmax16000, residuals `~1e-28`):
  genuine `χ_odd` (Euler L) **positive at every off-line height** `+2.270, +1.843, +2.890, +2.959`;
  Davenport–Heilbronn (no Euler product) has **one negative direction each** `−11.21, −2.219,
  −0.452, −4.705`, inertia `(1,0,10)` (`κ₋=1`); all controls positive. Separator scores
  `0.018 / 0.081`. `Q_DH < 0` e.g. `−0.483`.
- **`[firewall]` High-dps reality test** (N=18): ζ `max|Im|` of carrier eigenvalues tracks the
  precision **floor** `4.0e-36 (dps60) → 5.1e-95 (dps120) → 5.8e-175 (dps200)` = **REAL**; DH stays
  `O(1)` dps-stable `2.73 → 0.168 → 1.51` = **COMPLEX**. At N=14, dps200: ζ `= 4.1e-180`, DH `= 2.98`.
- **`[level-repulsion]`** (dps200, sha256 725b6133): ζ recovers the **actual `γ_n` as all-real
  eigenvalues** (`#real = N` at N=14/18/22/26; matches `γ_6, γ_8, γ_11, γ_13`); min-gap **converging**
  `2.510 → 2.10 → 1.77 → 1.487 ≈ γ_13–γ_14 gap 1.48` (finite, not uniform). DH: **~0 real
  eigenvalues**, no matches.
- **`[Spec₂ pollution-free probe]`** (sha256 ce5c6157): ζ `CERTIFIES_NEGATIVE = FALSE` everywhere,
  `min(Re+|Im|)` positive `→ 0⁺` (`1.2e-8 → 7.3e-20`); DH `CERTIFIES_NEGATIVE = TRUE`, interval
  `≈ [−5.3, −2.8]`. (ζ raw `λ_min` reads `−3.9e-51` yet Spec₂ refuses to certify negative — the
  faithful test rejects the measured artifact.)

### C. No-margin / positivity numerics (the apex, probed)

- **Q_W bottom steepens** with truncation: `1e-43 (N14) → 3.7e-52 (N18) → 6.7e-60 (N22)` — the
  no-margin **steepens**, does not stabilize away from 0.
- **CCM `t→1` no-margin** (N=20): ζ bottom `→` machine-zero as `t→1`: `−4.54, −2.26, −0.90, −0.22,
  −1.6e-16` (gap `→ 1e-17`, cond `→ 3e16` = singular at `t=1`); ζ `qw_ground = 2.9000e-56`,
  off_count `0`; DH `qw_ground = −4.6415`, gap `2.92`, 40 off-circle.
- **`[Li blind-spot / #88 constant]`** `[verified to <1e-20]`: first-negative index
  `m = πγ/(4δ)` (`m = 135/68/34` for `δ = 0.5/1/2` vs `134.6/67.3/33.7`); `c = m·δ/γ ≈ 0.79 ≈ π/4`
  in all cases.
- **GUE order parameter:** `⟨r⟩ = 0.611` to `γ ≈ 75000` (GUE, no Anderson transition). **Lehmer
  scan** tightest gap `0.0219 @ γ ≈ 71733`; Lehmer poly Mahler measure `M = 1.176280818`.
- **Ramanujan/symplectic no-margin curves:** non-trivial `|μ| = √q` exactly (defect `~1e-16`);
  normalized margin `1 − q^{−½} = 0.29, 0.42, 0.55, 0.62, 0.70` for `q = 2,3,5,7,11`.
- **berry resolution-law:** `dim_min: δ=.31 → 5, δ=.07 → 9` (SUB-linear in `1/δ`; closer to `log` or
  `1/√δ` than the `1/δ`-fit's predicted 22).

### D. Transcendence / DSS numerics

- **`[DSS-cross PSLQ — strong null]`** Stieltjes `{γ_0..γ_3}` vs period field `{π², ζ(3), ζ(5),
  ζ(7)}`, maxcoeff `1e12`, **dps 150 AND dps 300**: **ALL "NO relation"**; positive control
  `2ζ'(0) + log 2π = 0` correctly detected (`[2,1]`). Consistent with `{log p} ∪ {γ_n}` joint
  independence (Schanuel-entangled).
- **Free-cumulant Hankel:** `κ_n = ζ(2n+1)`, 5×5 Hankel eigenvalues `0.00165, 0.0692, 0.694, 8.04,
  2618.9` (all positive); negated-`κ_3` control `−0.221`. Zero-measure free cumulants alternate
  `κ_2>0, κ_4<0, κ_6>0, κ_8<0`.

### F. The DH log-derivative separator (#84)

- ζ: all `c_n = Λ(n) ≥ 0` (`negative_count = 0`); DH: `kappa = 0.2840790438…`,
  **59 negative / 62 positive**, first negatives `[3,4,9,12,13,14,19,23,27,29]`; 20 random
  non-multiplicative controls all-nonnegative (`0/20`). *The Euler product is the all-positive
  log-coefficient signature.*

### E. Phase-cancellation probes (R30/R31) — the transverse no-margin

- **R30:** the open transverse hierarchy `det H_d ≥ 0` is **NOT local-gap-controlled** — smallest
  gap (1.77) gives middling margin (`2.2e-4`); tightest margins sit at low-curvature midpoints;
  `corr(log margin, gap) = −0.25` (wrong direction). Margin is **non-monotone in `d`** with sharp
  sparse dips (≈100× near-collisions), e.g. `t=8.4` dips at `d=8` (`9e-5`), recovers at `d=10`.
- **R30 fine-scan:** coarse sampling **undercounts the no-margin ~30×** (`d=8` dip bottom `2.95e-6`
  vs grid `9.2e-5`); resonances **migrate in `t`** with `d` (`8.41 → 7.73`). The no-margin is a
  system of sharp, sub-grid, migrating **sparse resonances** — a concrete reason the apex resists
  numerical settlement.
- **R31:** both local controllers (zero-gap, local curvature `|K|`) FAIL ⟹ the no-margin is
  **collective** (`det H_d`), not pointwise. Closes the "local-controller shortcut."
- **Off-line-quartet curvature** `[verified ≤1e-18]`:
  `(½−β+iτ)^{-2}+(β−½+iτ)^{-2} = 2(a²−τ²)/(a²+τ²)²`, positive ⟺ `|τ| < a`; `(logΞ)''(t) < 0`
  confirmed real-negative on a γ-range (`t = 5, 20, 50`).

---

## III. What the experiments collectively establish (and do not)

**Establish `[OBSERVED]`:**
1. A **real, structured, positive** weld phase-carrier that finite Euler / random-phase controls do
   not reproduce in `σ ∈ [0.3, 0.7]` and that collapses at `σ>1` (the right-strip sanity boundary
   holds throughout).
2. A **faithful integer separator** (`κ₋`) that cleanly distinguishes genuine ζ (all-real carrier,
   `κ₋=0`) from a Davenport–Heilbronn fake (off-line zeros, `κ₋ ≥ 1`) across many independent probes
   (Weil–Gram, high-dps firewall, level-repulsion, Spec₂, log-positivity #84).
3. The **no-margin is real-looking but sub-grid/sparse/collective** (Q_W steepens, CCM `t→1 → 0`,
   R30/R31), explaining why it resists numerical settlement.
4. A **strong transcendence null** (DSS-cross PSLQ: no relation at dps300, maxcoeff `1e12`).

**Do not establish:**
- The carrier battery (Group A–F) has **not been run against the surrogate ladder** (an FE-exact
  correct-zeros fake), so it does not yet separate native HT from "analytic ≠ truncation" (synthesis
  §4–§5). The Davenport–Heilbronn separators above are *not* the surrogate ladder — DH lacks the FE
  in the exact correct-zeros sense the ladder demands.
- No experiment proves any all-scale statement; all are windowed/finite-`d`/finite-`N`.

---

## Methodological keepers (synthesis §6; worklogs)

- Use **medians, not tails**; always include the `σ=1.2` collapse control and the amplitude-matched
  random-phase surrogate.
- Treat any statistic containing `|Γ∞+P|` or the phase cosine as **contaminated** (it trivially
  reconstructs the carrier).
- Prefer the **faithful index** `κ₋` (Sylvester inertia) and the **pollution-free** Spec₂ certifier
  over raw `λ_min` (which reads spurious negatives that the faithful test rejects).
- **Stop re-discovering the carrier through a 21st metaphor** — the carrier is found; the open work
  is the §4 surrogate ladder and the apex (uniform-in-`d` `det H_d`, Schanuel-for-prime-logs).

## Source map

- `publications/hgt/logs/synthesis.md` §2 (id731–id773), §4, §6.
- `2-fully-proven/phase-cancellation-crux.md` (R30/R31, off-line-quartet curvature, self-verified).
- `docs/rh-corp/worklog-theorist.md`, `worklog-critic.md`, `worklog-engineer.md` (conductor-5,
  firewall, level-repulsion, Spec₂, Q_W, CCM, Li `#88`, GUE/Lehmer, DSS-cross PSLQ, free-cumulants,
  `#84`).
- `publications/hgt/docs/drafts/pipeline/2-fully-proven/computations/` (archived runs).
