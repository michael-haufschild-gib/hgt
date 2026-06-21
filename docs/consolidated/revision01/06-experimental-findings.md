# 06 — Noteworthy Experimental Findings (Consolidated, With Effect Sizes)

> **Scope.** The noteworthy *computational* findings, consolidated with their effect sizes and controls.
> Two streams: (I) the **light-tower carrier battery**, and (II) the **numerical lab** (faithful-index
> separators, no-margin curves, transcendence relation-searches). Every finding is `[OBSERVED]` unless
> tagged otherwise; an `[OBSERVED]` finding is an experiment worth banking, *not* a proven theorem. No
> proof of RH.

---

## I. The light-tower carrier battery

The discriminating observable everywhere is the weld phase-carrier defect
`Δ(σ,t) = max(log|Γ∞|, log|P|) − log|Γ∞+P|`. Controls: finite Euler `P_N` (`N→∞`), amplitude-matched
random-phase surrogate, and the `σ>1` collapse control.

> *Notation.* The weld phase-carrier defect proper uses the archimedean weld *term* `∂_s log Γ∞`, namely
> `Δ = max(log|∂_s log Γ∞|, log|ζ'/ζ|) − log|∂_s log Γ∞ + ζ'/ζ|`, matching the weld `H = ∂_s log Γ∞ +
> ζ'/ζ`. The battery here was run with the gamma *factor* `Γ∞` in place of `∂_s log Γ∞`; the two are not
> literally equal. The findings stand as measured with the factor form, kept distinct from the weld-term
> defect.

**A. Existence / non-reproducibility of the carrier**
- **Ultradiscrete sign carrier:** true `σ=0.3` positive-fraction **0.8–1.0**, median **0.3–0.55**; finite
  `≈ 0`; random-phase median goes **negative**.
- **Margin-neutralized residual:** after regressing out all amplitude features, the true left-strip phase
  residual survives, `σ=0.3` gap **+0.45** over controls; over-controls including `|Γ∞+P|` kill it (as they
  must).

**B. Time-domain coherence (the carrier is alive over long t)**
- **Proofreading off-rate:** true has **low entry rate, long positive-run lifetimes** (survives depth-16);
  finite fires often, dies fast. *The weld wins by lifetime, not on-rate.*
- **Transition-path softness:** true `Δ=0` crossings are **soft** (edge-softness **~45** vs finite
  **~6–12**).
- **Context-fragility monotone:** true catch-window decays **monotonically (0 violations)** under
  phase-context scrambling; controls keep violations.
- **Survival-conditioned spine:** conditioning on survival-to-depth-8 isolates a full-window true spine
  (`σ=0.3` spine-frac **1.0**; finite **~0.05**; random **0**).

**C. 2-D / cross-lane rigidity**
- **Zero-shadow topology:** at `R<1.00` true forms **one component spanning σ and t**; finite (any `N`)
  never t-spans (**35–50 fragments**); sparse `p=0.75` destroys, `p=0.90` restores.
- **Coupled-reserve frailty:** true low-reserve failures arrive in **coordinated cross-σ sheets**
  (co-failure excess over product/shift nulls); fails for the 2-lane case (genuinely multi-lane).
- **Initial-measure association:** true high-threshold lane fields have **cross-lane association excess**;
  productizing marginals destroys it.

**D. Orientation / signed structure (finite-prime gets the sign backwards)**
- **Gate–tension two-clock:** finite-prime phase gates **anti-timed (corr −0.4)** with true tension in the
  strip, **positively timed (+0.4)** at `σ>1`; sign crossing near `σ ≈ 0.6–0.8`.
- **Observed-volume covariance:** true **positive** (high values on high-gradient/curvature regions);
  finite/random **negative**; right-strip both negative.
- **Phase-space caustic / wrong momentum:** true signed area `∫O dP` has **z ≈ 18**; finite-prime phase
  momentum is **opposite-signed for every cutoff `P = 5…97`** and does not converge. *Finite-prime is
  anti-symplectic relative to the true lift.*

**E. Critical-lane localization**
- **Resetting occupation slope:** true reset clocks lane-synchronous across `σ=.3/.5/.7`, but reset-age
  occupation slopes **single out `σ=½`** (**−3.7/−4.2** vs neighbours **−1.1/−1.5**); shared-clock control
  preserves the centre excess for true, kills it for controls.
- **Berry lane-interference switch:** completing `ζ'/ζ → ξ'/ξ` **exactly equalizes** the two `σ=½±δ` lane
  magnitudes at `σ=½` (imbalance **→0**) and reroutes the residual into pure relative phase; off-centre,
  imbalance returns. *Γ-completion = archimedean boundary-condition operator.*

**F. Crossover / selection facets**
- **Hypercycle specificity:** finite wins broad/amplitude selection; true wins **phase-specific** selection.
- **Near-neutral hidden layer:** at `σ≈0.7`, sub-resolution `Δ_true − Δ_finite` has **positive mean and
  compounds** (hidden-fraction **0.71**).

---

## II. The numerical lab

### Faithful-index separators (the strongest empirical results)

- **`[ledger-grade]` Conductor-5 Weil–Gram separator** (dps 40, `n_max` 16000, residuals `~1e-28`): a
  genuine `χ_odd` (Euler L-function) is **positive at every off-line height** (`+2.270, +1.843, +2.890,
  +2.959`); Davenport–Heilbronn (no Euler product) has **one negative direction each** (`−11.21, −2.219,
  −0.452, −4.705`), inertia `(1,0,10)` (`κ₋=1`); all controls positive.
- **`[firewall]` High-precision reality test** (N=18): ζ's carrier-eigenvalue `max|Im|` tracks the
  precision **floor** (`4.0e-36 → 5.1e-95 → 5.8e-175` at dps 60/120/200) = **REAL**; DH stays `O(1)`,
  dps-stable (`2.73 → 0.168 → 1.51`) = **COMPLEX**.
- **`[level-repulsion]`** ζ recovers the **actual `γ_n` as all-real eigenvalues** (`#real = N`; matches
  `γ_6, γ_8, γ_11, γ_13`); min-gap **converging** (`2.510 → 2.10 → 1.77 → 1.487 ≈` the `γ_13–γ_14` gap
  1.48; finite, not uniform). DH: **~0 real eigenvalues**, no matches.
- **`[pollution-free probe]`** ζ `CERTIFIES_NEGATIVE = FALSE` everywhere, `min(Re+|Im|)` positive → `0⁺`
  (`1.2e-8 → 7.3e-20`); DH `CERTIFIES_NEGATIVE = TRUE`, interval `≈ [−5.3, −2.8]`. (ζ's raw `λ_min` reads
  `−3.9e-51`, yet the faithful test refuses to certify negative — it rejects the measured artifact.)

### No-margin / positivity numerics (the apex, probed)

- **`Q_W` bottom steepens** with truncation (`1e-43 → 3.7e-52 → 6.7e-60` at N=14/18/22) — the no-margin
  **steepens**, does not stabilize away from 0.
- **`t→1` no-margin** (N=20): ζ bottom → machine-zero as `t→1` (`−4.54, −2.26, −0.90, −0.22, −1.6e-16`;
  gap → `1e-17`, cond → `3e16` = singular at `t=1`); ζ ground `2.9e-56`, off-count `0`; DH ground
  `−4.6415`, gap `2.92`, 40 off-circle.
- **`[Li blind-spot]`** `[verified to <1e-20]`: first-negative index `m = πγ/(4δ)` (`m = 135/68/34` for
  `δ = 0.5/1/2` vs `134.6/67.3/33.7`); `c = m·δ/γ ≈ 0.79 ≈ π/4` in all cases.
- **GUE order parameter:** `⟨r⟩ = 0.611` to `γ ≈ 75000` (GUE, no Anderson transition). Lehmer scan
  tightest gap `0.0219 @ γ ≈ 71733`; Lehmer-polynomial Mahler measure `M = 1.176280818`.
- **Symplectic no-margin curves:** non-trivial `|μ| = √q` exactly (defect `~1e-16`); normalized margin
  `1 − q^{−½} = 0.29, 0.42, 0.55, 0.62, 0.70` for `q = 2,3,5,7,11`.
- **Berry resolution-law:** `dim_min: δ=.31 → 5, δ=.07 → 9` (SUB-linear in `1/δ`; closer to `log` or
  `1/√δ` than the `1/δ` prediction of 22).
- **`[Φ_2 line-curvature is necessary-not-sufficient]`** `[verified, 900 zeros]`: an off-line zero adds a
  positive curvature bump `C_a(0)=2/a²` to `Φ_2(t)=Σ_ρ(½+it−ρ)^{−2}`, so near-line zeros are always caught,
  but the bump is bounded (`≥8`, `a≤½`) while the on-line `|Φ_2|~(log γ)²` grows — a far-off-line `a=0.45`
  quartet goes **undetected** at `γ≈180, 260` (detected at `60,120,240,262–265`). RH-blind to far-off-line
  high zeros — a **permanent** blind spot, unlike the **all-order-faithful** reciprocal-Hankel `Q_0`
  (obstruction `Im y`, fixed sign; its finite-`d` resolution is height-graded but always eventually catches).
- **`[Q_0 moment-problem is one-atom-dominated]`** `[verified, dps200]`: `T_k=2Σγ^{−2k}` is dominated by
  `y_1=1/γ_1²` (`T_k→2y_1^k`; `y_1/y_2≈2.2`); the Jacobi recurrence of `m_n=T_{n+1}` has `β_n>0` (PD) but
  is catastrophically ill-conditioned — `α_n` leave `[0,y_1]` at the precision wall (broke at `n=4`/dps40,
  `n=6`/dps200, ~80 guard digits/order). Raw Jacobi/CF is a bad proof coordinate — and **atom deflation
  does not rescue it**: both moment-subtraction and Christoffel `∏(y−y_j)q` make conditioning strictly
  worse (`cond 5.6e30→1.9e40`/`2.0e38`), the atoms clustering ever-tighter toward the hard edge. The
  ill-conditioning is intrinsic ⟹ the proof handle must be analytic (closed-form `S_k`), not numerical.
- **`[arch/prime cancellation is rank-1]`** `[verified d≤6, S_k^A via closed-form polygamma cross-checked to
  1e-121]`: the split `Q_0=Q_arch+Q_prime` has `(2γ_1)^{2k}~10^{2.8k}`-deep cancellation, but the archimedean
  Hankel `[T^A_{i+j+1}]` has signature **exactly `(d,1)`** — one negative direction, and that direction *is*
  the pole-evaluation vector `u_i=(−4)^i` (overlap `û` `=1.0` to 120 digits, every `d≤6`; `y=−(½)^{−2}=−4`
  is the `s=1` pole image, `⟨c,u⟩=p(−4)`); the prime Hankel is indefinite; the two sum to PD `Q_0`. On `u`,
  `Q_arch[u]=−Q_prime[u]` to depth `1.5·10⁻⁷→3.6·10⁻¹⁷` (`d:2→6`), leaving a *fixed positive* residue
  `Q_0[u]=0.04564` independent of `d` (= `∫2y²/(1+4y)² dν_0`, since `Σ(−4)^i y^i=1/(1+4y)`). `Q_arch|_{u^⊥}`
  is PD. The cancellation lives entirely on the one pole direction (= entireness).
- **`[the rank-1 pole strip is exact but NOT a reduction]`** `[verified, d≤6]`: restricting `H_d^(0)` to `u^⊥`
  keeps it PD but improves `cond` by only a **fixed** `~10^{6.5}` factor (`4.5e37→5.9e30` at `d=6`; `min`-eig
  still `~10⁻³³`) — the residual is *still* the generic hard-edge problem, as FID-ill-conditioned as the full
  form. The most-dangerous direction `p_d` (`λ_min` eigenvector) is `0.97·u`, and on it `|Q_arch/Q_prime|=1.0`
  with `Q_0[p_d]=λ_min` a tiny positive residue: the wall's near-degeneracy is **prime-delicate** (prime side
  cancels the arch pole-deficit), not arch domination. So the pole split is a clean closed-form **Part A**,
  but **Part B (residual PSD on `u^⊥`) is still the full transfer problem** — settling the rank-1 dichotomy in
  the "only part of the story" branch.
- **`[the off-line defect is orthogonal to the pole]`** `[verified, d=6]`: pushing one on-line atom off the
  line (`β:0→0.4`) flips `λ_min<0` (inertia `(7,0)→(6,1)`); the new negative direction has overlap only
  `0.057→0.014` with `u` and `~10⁻⁵` with the on-line `p_d`. RH-sensitivity lives in a **new** direction at
  the off-line atom's coordinate, *not* the always-cancelled pole `u` — so Part A (pole cancellation, RH-
  independent) and Part B (the RH-sensitive off-line direction) act on essentially orthogonal subspaces.
- **`[fused four-way split: even-ζ protects the residual, β/Catalan cancels it, prime closes the gap]`**
  `[verified, d=4..8]`: splitting zero-side `S_k` into `POLE=2^{2k+1}`, `ZETA=−½(2^{2k}−1)ζ(2k)`,
  `BETA=−2^{2k−1}β(2k)`, `PRIME=(−1)^kT_k−`(arch) and evaluating on the genuine residual direction
  (`λ_min` of `H_d^(0)|_{u^⊥}`, `p(−4)=0` ⟹ `Q_pole→0` `~10⁻¹³⁴`): the even-`ζ` term is the **sole positive**
  contributor, the **β/Catalan term nearly cancels it** (`d=6`: `Q_ζ=+5.201·10⁻⁵`, `Q_β=−5.201·10⁻⁵`), and the
  **prime is sub-dominant** (`Q_prime=−1.7·10⁻⁹`, matching only the arch-even net `Q_ζ+Q_β`). Two-stage cascade:
  `ζ`-vs-`β`(Catalan) at `10⁻⁵` → arch-even surplus `10⁻⁹` → prime cancels it → `λ_min~10⁻³³`. So the residual
  delicacy is **arch-even (`ζ`-vs-Catalan), prime as closing correction** — distinct from the *pole* direction
  `p_d≈0.97u`, where the four are in clean ratio `POLE:ZETA:BETA:PRIME=−4:1:1:2` and the prime is dominant.
  (Arch closed form cross-checked to polygamma at `1e-121`; four pieces sum to `λ_min`.)
- **`[Q_ζ+Q_β is positive-definite — the ζ-vs-β opposition is a residue-class artifact]`** `[verified d=4,6,8]`:
  `inertia(H^{ζ+β}) = (d+1,0)` (PD), and `Q_ζ+Q_β = 4p(−4)² + R_d^A[p]` (cross-checked `1e-81`) — the pole-square
  plus the trivial-zero budget. The `ζ`/`β` halves are that one PD object split by character mod 4 (`β=L(·,χ₄)`),
  individually large and oppositely signed but summing PD. So the apparent "`ζ`-vs-`β` battlefield" is not real;
  the sole RH content is `Q_prime` vs `R_d^A`, and it is tight (prime saturates the budget).
- **`[character (mod 4) decomposition is the wrong representation — route demoted]`** `[evaluated, d=4,6,8]`:
  splitting the budget by Dirichlet character mod 4 gives `inertia(H^ζ)=(d+1,0)` (PD, all-odd-integer principal
  sector) but `inertia(H^β)=`indefinite (`≈(d−1,⌈d/2⌉)`, stable `min`-eig `≈−0.226`); the `χ₄=L(·,χ₄)` sector is
  genuinely indefinite. Since the `1`-mod-`4` residue-class budget is PD only as a *positive measure*, the
  character split breaks manifest positivity (PD-principal must dominate an indefinite `χ₄`). Positivity lives in
  the measure cone, not the character basis ⟹ the proof must use square test functions over the actual divisor,
  not a Dirichlet decomposition. (Hurwitz identities `ζ(2k,¼)±ζ(2k,¾)` and `ZETA=−2^{2k−1}Σ_{odd}m^{−2k}` verified.)
- **`[the prime/arch-budget relation is ONE-sided, not a sandwich]`** `[verified d=4,6,8]`: testing `|Q_prime|≤
  Q_ζ+Q_β`, the lower side `H^{ζβ}+H^prime⪰0` holds (`min`-eig `+7.8·10⁻³³`, = the bridge/RH side) but the upper
  side `H^{ζβ}−H^prime` is **not** PSD (`min`-eig `−5.2·10⁻¹¹`, stable). So `Q_prime` can *overshoot* the arch
  budget on the positive side; only the one-sided `Q_prime≥−(Q_ζ+Q_β)` (= RH, tight) is the content — the prime
  is not two-sided-bounded by the budget. (`H^prime` itself is indefinite, inertia `(2,3)/(2,5)/(3,6)`.)
- **`[FID has none of the arch/pole/β structure — RH lives in the structure, not the numerics]`** `[verified d≤8]`:
  the RH-empty integer divisor `H_FID=[ζ(2(i+j)+3)]` is **strictly PD** `(d+1,0)` for all `d`, and `Q_FID[u]`
  (`u_i=(−4)^i`) is **positive** (`+4.2·10⁴→+2.7·10⁹`) — no `s=1` pole, no `−uuᵀ` direction, no `(d,1)`. So the
  entire arch/pole/trivial-zero/`β`/`χ₄` structure is **zero-divisor (completed-ζ) specific**, absent from FID.
  FID shares only the hard-edge *conditioning* (the earlier calibration), none of the *structure* — confirming the
  RH content is structural, not numerical.
- **`[Q_0 obstruction is broad / auto-deflating]`** `[verified, d=6]`: the most-dangerous polynomial (`λ_min`
  eigenvector of `H_d^(0)`) is the degree-`d` orthogonal polynomial with roots exactly on the dominant atoms
  `y_1..y_5` (auto-deflation — why explicit deflation fails), and its residual mass is mid-range (atoms
  `n≈4–20`, `γ≈25–80`; 67% by `n=8`, 94% by `n=30`), not at `y_1` or the hard edge. The `Q_0` obstruction is
  distributed ⟹ the proof needs **uniform**, not local, control.
- **`[Q_0 finite-d resolution is height-graded]`** `[verified, dps140]`: injecting an off-line quartet
  `{±a±iγ0}` into the on-line bulk, the smallest `d` with `λ_min(H_d^(0))<0` is `d*≈γ0/3` (`γ0=14→4`,
  `30→11`, `80→>14`); `d*≠1` even at `γ0=14` (bulk masks the isolated-quartet `d=1`). Finite (caught
  eventually, unlike Φ_2's permanent blind spot), but a height-graded resolution — a height-`γ0` quartet
  maps to a tiny atom `|y0|≈1/γ0²` near the hard edge. So a finite-`d` numerical Q_0 check has height-
  limited reach; the certificate is irreducibly all-order.
- **`[the Q_0 numerical difficulty is GENERIC, not RH-specific]`** `[FID calibration]`: the RH-empty FID
  integer divisor (`y_n=1/n²`, `H_FID[i,j]=ζ(2(i+j)+3)`) shows the **same** structure as the zero-divisor
  `Q_0` — exponential ill-conditioning (`cond 6e3→5e9→9e16` at d=2/4/6), auto-deflating dangerous polynomial
  (roots on `1,0.25,0.111,…`), mid-range distributed obstruction (94% by n=8) — differing only quantitatively
  (zero divisor `~10^{15}×` more ill-conditioned at d=4, atoms tighter). So the whole numerical battery
  carries zero RH content; the RH content is only the integer→zero explicit-formula transfer ⟹ no
  Hankel/conditioning/deflation argument is RH-relevant; the proof must be the analytic transfer.

### Transcendence / relation-search numerics

- **`[strong null]`** Stieltjes `{γ_0..γ_3}` vs the period field `{π², ζ(3), ζ(5), ζ(7)}`, max-coefficient
  `1e12`, **dps 150 and dps 300**: **all "NO relation"**; the positive control `2ζ'(0) + log 2π = 0` is
  correctly detected. Consistent with `{log p} ∪ {γ_n}` joint independence (Schanuel-entangled).
- **Free-cumulant Hankel:** `κ_n = ζ(2n+1)`, 5×5 Hankel eigenvalues `0.00165, 0.0692, 0.694, 8.04, 2618.9`
  (all positive); negated-`κ_3` control `−0.221`. Zero-measure free cumulants alternate `κ_2>0, κ_4<0,
  κ_6>0, κ_8<0`.

### The log-derivative separator

- ζ: all `c_n = Λ(n) ≥ 0` (`negative_count = 0`); DH: `kappa = 0.28408…`, **59 negative / 62 positive**,
  first negatives `[3,4,9,12,13,14,19,23,27,29]`; 20 random non-multiplicative controls all-nonnegative.
  *The Euler product is the all-positive log-coefficient signature.*

### Phase-cancellation probes — the transverse no-margin

- The open transverse hierarchy `det H_d ≥ 0` is **NOT local-gap-controlled** — the smallest gap (1.77)
  gives a middling margin (`2.2e-4`); the tightest margins sit at low-curvature midpoints; `corr(log
  margin, gap) = −0.25` (wrong direction). The margin is **non-monotone in `d`** with sharp sparse dips
  (≈100× near-collisions): `t=8.4` dips at `d=8` (`9e-5`), recovers at `d=10`.
- **Fine-scan:** coarse sampling **undercounts the no-margin ~30×** (`d=8` dip bottom `2.95e-6` vs grid
  `9.2e-5`); resonances **migrate in `t`** with `d` (`8.41 → 7.73`). The no-margin is a system of sharp,
  sub-grid, migrating **sparse resonances** — a concrete reason the apex resists numerical settlement.
- Both local controllers (zero-gap, local curvature `|K|`) FAIL ⟹ the no-margin is **collective**
  (`det H_d`), not pointwise. Closes the "local-controller shortcut."
- **Off-line-quartet curvature** `[verified ≤1e-18]`: `(½−β+iτ)^{-2}+(β−½+iτ)^{-2} = 2(a²−τ²)/(a²+τ²)²`,
  positive ⟺ `|τ| < a`; `(logΞ)''(t) < 0` confirmed real-negative on a γ-range (`t = 5, 20, 50`).

---

## III. Further discriminators and controls

**New RH-side discriminators:**
- **Period-domain `D_∞`:** completed `ξ` quenched gap `0.000295`, boundary `0.309967`; random-γ gap
  `0.432769`; an off-line FE quartet lowers the boundary to `0.168687` *without* masking.
- **Ito/Stratonovich corank:** Strat−Ito effective rank true `+1.8593` vs finite `+0.2181`, random
  `+0.2323` (`[100,170]`, N=30); collapsed at σ=1.2. *(State-dependent completion can shift the observed
  finite corank near the seam.)*
- **Jensen anti-collective:** suppression ratio true/shuffled `0.22–0.35` (< 1 everywhere); late window
  true `0.278` vs shuffled `3.533`, sorted `4.333`.
- **State-law abscissa:** wall `= max(½, 1/k₀)`; `U(1)` gives `k₀=∞`, Rademacher even-power drift at the
  seam, Bernoulli mean wall `1`, `q≥3` drift below `½`. `[bridge-candidate]`
- **Off-line curvature detector:** broad filter width `8a` → peak ratio `0.0159` (`a`-independent); matched
  Gaussian unimodal at `width/a = 0.50` (z `73.4` at a=.10).
- **FID Hankel:** `κ_n=ζ(2n+1)` det collapses (`log₁₀ −0.86 → −45.3`, sizes 2–7; cond `1.36e17`); double
  precision loses the PSD sign at size 8 (`min_eig −8.5e-17`) — a numerical underflow, not a positivity
  failure (it is PSD at high precision).
- **Affine passport:** `Π(S)=(|S|,Σm)`; two blocks sharing `(3,(2,2,0))` have identical trace
  `−3.5835189…`; universal shift `−|S|log p`.
- **Scalar layer:** true β-conditioned `weighted_spread 0.7803` vs controls max `0.3573`; interaction-rms
  `0.1921` vs random `0.0926`.

**Gatekeeper controls (each becomes a required certificate):**
- **Isospectral cross-lane:** lane spectra preserved to `~1e-15`, cross-lane top eig collapses (true
  `5.28–5.59` vs surrogate `≤1.0`).
- **Domain-corank leak:** internal fraction `T/(N+T)` (`T=2, N=100` leak `0.980`).
- **Multiscale rounding:** Gaussian false-seam `21/36` rows; a contour half-width `< δ` sees charge `0`.
- **Memory-kernel:** same-`ξ` kernels differ in memory lift (`+0.458` vs `+0.575`).
- **Guard-band:** critical guard-band stable `11/12`; right collapse `6/6`.
- **APEX-B mask:** a centered mask hides the core only `1/17` off-center.
- **Weld orientation:** true left-first `8/8` (`mean_orientation +0.037`); finite/random right-first `7/8`.
- **Sampling retention:** `Δ>1` events `9/9` critical, right `0/3`; peak retention `0.724→0.412`.
- **Affine recurrence:** exact prime-logs `0.001–0.070`; quantized `1.000000` in all 18 cases.

**Falsifications (specific candidate forms, not of RH):**
- **Naive scalar oriented 2-form:** no scalar `(O,φ)` variant passes the combined gate; a minimal
  counterexample gives identical scalar samples with opposite oriented areas (`±5.63`).
- **Scalar Layer / `H=A+P` selection:** every scalar-scale rescue and `H`-threshold fails (`H` residual
  `0.8922` vs `Δ` `0.0014`).
- **FE-fake:** an adversarial constant-phase FE-exact fake forces full carrier positivity (matched longest
  run `121`).

---

## IV. What the experiments collectively establish (and do not)

**Establish `[OBSERVED]`:**
1. A **real, structured, positive** weld phase-carrier that finite Euler / random-phase controls do not
   reproduce in `σ ∈ [0.3, 0.7]` and that collapses at `σ>1`.
2. A **faithful integer separator** (`κ₋`) that cleanly distinguishes genuine ζ (all-real carrier, `κ₋=0`)
   from a Davenport–Heilbronn fake (off-line zeros, `κ₋ ≥ 1`) across many independent probes (Weil–Gram,
   high-precision firewall, level-repulsion, pollution-free certifier, log-positivity).
3. The **no-margin is real-looking but sub-grid/sparse/collective** (`Q_W` steepens, `t→1 → 0`, the
   phase-cancellation probes), explaining why it resists numerical settlement.
4. A **strong transcendence null** (no Stieltjes-vs-period relation at dps 300, max-coefficient `1e12`).

**Do not establish:**
- No experiment proves any all-scale statement; all are windowed/finite-`d`/finite-`N`. The
  Davenport–Heilbronn separators distinguish a fake *with* off-line zeros; they are not a transcendence
  test (the carrier is a continuation/divisor-geometry diagnostic — see §V).
- The naive scalar oriented 2-form is falsified, not the oriented-structure conjecture.

---

## Methodological keepers

- Use **medians, not tails**; always include the `σ=1.2` collapse control and the amplitude-matched
  random-phase surrogate.
- Treat any statistic containing `|Γ∞+P|` or the phase cosine as **contaminated** (it trivially
  reconstructs the carrier).
- Prefer the **faithful index** `κ₋` (Sylvester inertia) and the **pollution-free** certifier over raw
  `λ_min` (which reads spurious negatives the faithful test rejects).
- The carrier is found; the open work is the apex (uniform-in-`d` `det H_d`, Schanuel-for-prime-logs) and
  the bridge arrow — not a 21st re-discovery of the carrier.

---

## V. The "native-HT" framing is resolved (deflationary)

`[ARGUMENT — verified]` Every "is the carrier native to hypertranscendence, or merely analytic?" reading
above is **resolved**: no FE-exact, ζ-exact-zeros, non-HT object exists (by Hadamard every such object is
`e^{q((s−½)²)}ξ`, still HT). The carrier is **invariant** under that surrogate, hence a `{zeros, FE,
source-measure}` detector — an **analytic-continuation / divisor-geometry instrument, not a transcendence
detector** (the adversary it would need is empty). ξ's hypertranscendence is *divisor-encoded* (the
arithmetic of `{γ_n}` = the value axis). Read any "native-HT" language above as historical.
