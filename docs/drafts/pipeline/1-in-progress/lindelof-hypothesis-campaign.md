# Lindelöf hypothesis — long-running campaign log

- **ID:** `lindelof-hypothesis-campaign`
- **Stage:** 1-in-progress
- **Type:** CAMPAIGN LOG / CONJECTURE FACTORY
- **Target:** prove or disprove `mu(1/2) = 0`, i.e. `zeta(1/2+it) << t^eps`.
- **Scientific status:** `[SEARCH REGISTER]` — everything here is `[CONJECTURE]` unless marked
  `[PROVED HERE]` or `[THEOREM]` with a source.
- **Opened:** 2026-07-25

This file is the durable memory of the campaign. It survives context compaction. Every cycle
appends: (a) the exact conjecture attacked, (b) the verdict, (c) the *mechanism* that killed it,
(d) the strongest survivor. Do not re-attack a route listed under DEAD without a new mechanism.

---

## 0. Frozen frontier (audited 2026-07-25)

**External SOTA**
- `mu(1/2) <= 13/84 = 0.154761...` (Bourgain, JAMS 2017, via `l^2` decoupling for the moment
  curve). Confirmed still the record in July 2026 (ANTEDB / Tao–Trudgian–Yang; 2026 explicit
  sub-Weyl papers arXiv:2602.05614, arXiv:2302.13444 quote it as the asymptotic record).
- Convexity `mu(1/2) <= 1/4`; Weyl/Hardy–Littlewood `1/6`; Bombieri–Iwaniec `9/56`; Huxley
  `32/205`; Bourgain `13/84`.
- Exponent-pair route: `mu(1/2) <= (k+l-1/2)/2` for any exponent pair `(k,l)`. Exponent-pair
  conjecture `(eps, 1/2+eps)` implies LH. A/B-process closure bottoms out at `k+l ≈ 0.8290`
  (Rankin), i.e. `mu <= 0.1645`; Bourgain's pair `(13/84, 55/84)` is outside that closure.
- Moment route: LH `<=>` `M_{2k}(T) := int_0^T |zeta(1/2+it)|^{2k} dt << T^{1+eps}` for all `k`.
  Known only for `k = 1, 2`. `M_{12} << T^{2+eps}` (Heath-Brown). `M_6 << T^{1+eps}` (sixth
  moment) is a famous open problem tied to the ternary additive divisor problem (Ng 2016).
  arXiv:2304.07581 claims `M_6 << T^{1+eps}` unconditionally but the author's own comment says
  "Temporary version. Still need to be fixed" — NOT accepted into the ledger.
- Backlund (1918): LH `<=>` for every `delta > 0`,
  `#{rho : beta > 1/2 + delta, T < gamma < T+1} = o(log T)`.
- Guth–Maynard (arXiv:2405.20552, rev. 2026-04) improved large values of Dirichlet polynomials
  near the `N^{3/4}` threshold, giving zero-density `N(sigma,T) << T^{30(1-sigma)/13+o(1)}` and
  primes in `x^{17/30}`. It does **not** improve `mu(1/2)`.
- Extreme values: `max_{t<=T}|zeta(1/2+it)| >= exp((1+o(1)) sqrt(2 log T logloglog T/loglog T))`
  (Bondarenko–Seip, de la Bretèche–Tenenbaum). Conjecturally
  `exp((1/sqrt2+o(1)) sqrt(log T loglog T))` (Farmer–Gonek–Hughes). Both are `T^{o(1)}`, so the
  Omega-side gives no evidence against LH.

**Internal corpus** — no card attacks `mu(1/2)`. Adjacent Lean machinery that exists:
`RHTower/VanDerCorput*.lean` (several), `GaussLattice`, `WindingCurvature`, `FirstMoment`,
`ReflectedModeSum`, `BernoulliFourierBridge`, `XiLaguerrePolya`,
`SuzukiFiniteApertureHermiteBiehler`, `hardy-critical-line-moment-anchor` card. The corpus is
RH-centric; LH is a genuinely new axis for it.

---

## 1. Standing structural map (derived here, cycle 1)

Notation: `C := mu(1/2)`, `L := log T`.

**(M1) Moment exponent function.** `m(k) := limsup_T log M_{2k}(T)/log T` for real `k >= 0`.
- `m` is convex (Hölder), `m(0) = m(1) = m(2) = 1`, `m >= 1`, hence `m ≡ 1 on [0,2]`.
- `m(k) >= 2Ck` (a near-maximal spike is sustained on an interval of length `≍ 1/log T`, because
  `zeta(1/2+it)` on `[T,2T]` is band-limited with bandwidth `≍ (1/2)log T`; Bernstein).
- `m(k) <= 1 + 2C(k-2)` (Hölder against the 4th moment).
- Hence `m'(k) <= 2C` for `k>=2` and `m(k)/k -> 2C`. `LH <=> m` is bounded `<=> m ≡ 1`.
- `D(k) := m(k) - 2Ck` is nonincreasing, `D(2) = 1-4C >= 0`, `D_inf := lim D(k) >= 0`.

**(M2) Large-deviation form.** Write
`meas{t in [T,2T] : |zeta(1/2+it)| > T^v} = T^{1-phi(v)+o(1)}`.
Then `m(k) = 1 + sup_v [2kv - phi(v)]` (Legendre transform) and `phi(C) = 1`.
Known: `phi(v) >= 4v` (4th moment), `phi(v) >= 12v - 1` (Heath-Brown 12th moment),
`phi(v) = +inf` for `v > 13/84`. `LH <=> phi(v) = +inf for every v>0`.
`D_inf = 1 - phi(C^-)`, so `D_inf in [0, 1-4C]`, giving the dichotomy
- `D_inf = 0`: near-maximal values sit on a set of measure `T^{o(1)}` (isolated spikes);
- `D_inf = 1-4C`: near-maximal values occupy measure `T^{1-4C}` and saturate *every* moment.

**(M3) Bernstein saturation.** On `[T,2T]` the Riemann–Siegel `Z` is (up to `O(t^{-1/4})`) a real
function with spectrum in `[-B,B]`, `B = (1/2)log(T/2pi)`. Bernstein caps its real-zero density at
`B/pi = (1/2pi)log(T/2pi)` per unit length — which is **exactly** `N(T+1)-N(T)`. So RH is
precisely the statement that `Z` saturates the Bernstein zero-density bound.

---

## 2. Cycle ledger

### Cycle 1 (2026-07-25)
- Phase 1–2 done; frontier frozen above.
- Structural map (M1)–(M3) derived.

**DEAD routes recorded this cycle** (do not repeat without a new mechanism):
- **D1. Bohr almost-periodicity recurrence.** "A large value of `zeta(1/2+it_0)` recurs on a
  relatively dense set of `t`, contradicting the 4th moment." KILLED: the almost-period gap of
  `sum_{n<=N} n^{-1/2-it}` is `exp(c pi(N) log(1/eps))`, astronomically larger than `T ≈ N^2`.
  Recurrence never happens inside the window where the approximation is valid.
- **D2. Naive Halász–Montgomery large values on the length-`sqrt T` block.** Gives
  `R << T^{1/2-2C} + T^{1-6C}`; the binding mean-value term reproduces exactly the convexity bound
  `C <= 1/4`. Same for `zeta^k` (AFE length `T^{k/2}`): the `1/4` is scale-invariant under `k`.
- **D3. Baker / linear forms in logarithms to forbid simultaneous prime alignment.** To force
  `sum_{p<=y} p^{-1/2} cos(t log p) >> log T` one needs `y ≈ (log T)^2 (loglog T)^2`. Baker–Wüstholz
  on `m_p log q - m_q log p` with `m <= T` gives only `> T^{-c(loglog T)^2}` — far too weak; the
  linear forms genuinely can be that small.
- **D4. Littlewood-lemma / `S_1` route.** `int_{1/2}^inf log|zeta(sigma+iT)| dsigma = pi S_1(T)+O(1)`
  with `S_1 << log T` unconditionally. Integrating `d/dsigma log|zeta| = sum_rho (sigma-beta)/|s-rho|^2
  - (1/2)log(T/2pi) + O(1)` from `1/2` to `1/2+eta` reproduces `mu(1/2) <= mu(1/2+eta) + eta/2` plus
  an off-line-zero term — i.e. exactly convexity + Backlund. No gain.
- **D5. de Branges / Hermite–Biehler `A_2` reformulation.** Attractive (LH as a Muckenhoupt
  condition on the phase `theta`), but building the Hermite–Biehler `E` presupposes RH. Circular for
  a route to LH.

**SURVIVING lines (carried to cycle 2):**
- **S1. Resonance/clustering dichotomy.** Make rigorous: a large value forces either (A) an extreme
  value of a prime Dirichlet polynomial of length `(log T)^{2+o(1)}` (Diophantine branch) or (B) a
  quantitative clustering of zeros near `t_0` (large-value branch). Each branch needs different
  technology; the dichotomy itself is the new object.
- **S2. `D_inf` dichotomy** from (M2): the two extremes need genuinely different attacks; a theorem
  ruling out either extreme is progress on `phi`.
- **S3. Bernstein-saturation rigidity** (M3): among band-limited real functions with maximal zero
  density, largeness forces zero clustering *on the line*. Unconditional content unclear yet.

---

## 3. Cycle 1 result — the block-moment (zeta-free) reformulation

All statements below are `[PROVED HERE]` on paper unless marked otherwise. Notation:
`N = T^alpha` with `0 < alpha <= 1/2`, `w` a fixed smooth bump on `[1,2]`,
`D_N(t) = sum_n w(n/N) n^{-it}`, `G_N(t) = sum_n w(n/N) n^{-1/2-it}`.

**Definition (block-moment exponent).**
`beta_k(alpha) := limsup_T log( int_T^{2T} |D_{T^alpha}(t)|^{2k} dt ) / log T`.

**(B1) Diagonal floor.** `beta_k(alpha) >= 1 + k*alpha`.
*Proof.* The diagonal `n_1...n_k = m_1...m_k` contributes `T * E_k^x(N)` where `E_k^x(N)` is the
multiplicative energy of `(N,2N]`, and `E_k^x(N) >= N^k` by Cauchy–Schwarz (the `N^k` tuples have
products spread over an interval of length `≍ N^k`). Alternatively Hölder:
`int|D|^{2k} >= (int|D|^2)^k / T^{k-1}` and `int_T^{2T}|D|^2 ≍ TN`. ∎

**(B2) Trivial ceiling and the exact criticality point.** The unsmoothed off-diagonal bound is
`beta_k(alpha) <= 2k*alpha`. Floor = ceiling exactly when `k*alpha = 1`. So for each `k` the
mean-value method is *exactly critical* at `N = T^{1/k}`: below it the diagonal dominates and the
bound is unconditional; above it every term needs cancellation.

**(B3) Mellin comparison.** `int_T^{2T}|G_N|^{2k} dt << T^eps int_{T/2}^{3T}|zeta(1/2+it)|^{2k} dt`
(write `G_N(t) = (1/2pi) int_R W(iv) zeta(1/2+i(t+v)) dv`, `W` = Mellin transform of `w`, rapidly
decaying; then Minkowski). Conversely the smoothed AFE gives
`int|zeta|^{2k} << (log T)^{2k} max_N int|G_N|^{2k}`. Hence, with `m(k)` the zeta-moment exponent,

  **`m(k) = max_{0 < alpha <= 1/2} [ beta_k(alpha) - k*alpha ]`.**

**(B4) Sup transfer.** `sup_{t in [T,2T]}|D_N(t)| << (k log N)^{1/2k} (int_{T-1}^{2T+1}|D_N|^{2k})^{1/2k}`
(Sobolev/Gallagher applied to `D_N^k`, a Dirichlet polynomial of length `N^k`).

**(B5) THEOREM (block-moment subconvexity).** For every real `k >= 1`,

  **`mu(1/2) <= sup_{0<alpha<=1/2} [ beta_k(alpha)/(2k) - alpha/2 ]`.**

*Proof.* Smoothed AFE: `|zeta(1/2+it)| << log t * max_{N dyadic <= C sqrt t} |G_N(t)| + t^{-A}`;
`|G_N| ≍ N^{-1/2}|D_N|` after partial summation; then (B4). ∎

**(B6) COROLLARY (zeta-free form of LH).**

  **LH `<=>` for every `k in N` and every `alpha in (0,1/2]`,
  `int_T^{2T} | sum_n w(n/T^alpha) n^{-it} |^{2k} dt <<_{k,eps} T^{1 + k*alpha + eps}`.**

i.e. LH is exactly *square-root cancellation in every even mean of the pure exponential sum
`sum_{n ~ N} n^{-it}` along the vertical line*, uniformly for `N <= sqrt T`. No divisor function,
no `zeta`, no functional equation appears in the statement. `beta_k(alpha) = 1+k*alpha` is
unconditionally true whenever `k*alpha <= 1` (B2), so every open case has `k*alpha > 1`.

### Exact numerology of the frontier

Perfect blocks (`beta_k = 1+k alpha`) give `mu(1/2) <= 1/(2k)`, uniformly in `alpha`. Hence:

| `k` | perfect `beta_k(1/2)` | perfect `mu` bound | `beta_4(1/2)` needed to beat Bourgain |
|---|---|---|---|
| 2 | `2`   | `1/4`  (= convexity, and `beta_2(1/2)=2` is a theorem) | — |
| 3 | `5/2` | `1/6`  (= Weyl; equivalent to the sixth moment of zeta) | — |
| 4 | `3`   | `1/8 = 0.125` | `beta_4(1/2) < 8(13/84 + 1/4) = 68/21 = 3.238095...` |

- `k = 42/13 ≈ 3.2308` is the exact break-even with Bourgain: **no `k <= 42/13` block-moment bound,
  however perfect, can beat `13/84`.** The first competitive integer case is `k = 4`.
- Current knowledge: `beta_4(1/2) <= 2 + m(4) <= 2 + 3/2 = 7/2` (B3 plus `m` convex with
  `m(2)=1`, `m(6)=2` Heath-Brown). Floor is `3`. **Target window: `[3, 68/21)`, i.e. the excess
  over the diagonal must be cut from `1/2` to below `5/21 = 0.238`.**

### [CONJECTURE Λ-8] (self-dual block, eighth moment)
`int_T^{2T} | sum_{n} w(n/sqrt(T/2pi)) n^{-it} |^8 dt <<_eps T^{3+eps}`.
Implies `mu(1/2) <= 1/8`, beating Bourgain. Falsifiable: any `beta_4(1/2) > 3` disproves it.
`[OPEN CORE]`: the off-diagonal `sum_{h != 0} R_4(h) K_T(h)`, `R_4(h) = #{n_1..n_4 - m_1..m_4 = h,
all ~ sqrt T}`, must cancel by a factor `T^1` below its trivial size `T^4`. Cancellation of at
least `T^{1/6}` is already forced at `k=3` (see D6), so the phenomenon is real, not hypothetical.

**New DEAD/CAUTION entries from cycle 1:**
- **D6 (calibration, not dead).** For `k=3, alpha=1/2` the *trivial* off-diagonal is `T^3` while
  Bourgain's pointwise bound forces `beta_3(1/2) <= 17/6 = 2.8333`. So the off-diagonal already
  cancels by `>= T^{1/6}` unconditionally. Any "no-cancellation" heuristic for these off-diagonals
  is wrong; do not use it again (it briefly appeared to disprove LH — it does not).
- **D7. Block route is not stronger than the moment route.** By (B3) `beta_k(alpha) <= k alpha+m(k)`,
  so `mu <= beta_k(1/2)/(2k)-1/4 <= m(k)/(2k)`: the block formulation is *equivalent* to the zeta
  moment problem, not weaker. Its value is that it is decoupling-shaped, not that it is easier.
- **D8. Mean-value hierarchy is exactly critical at every `sigma` and every `k`.** From the
  Montgomery–Vaughan mean value plus the AFE for `zeta^k`, `int_0^T|zeta(sigma+it)|^{2k} << T^{1+eps}`
  holds exactly for `sigma >= 1-1/k`, and the resulting pointwise bound is `mu(sigma) <= 1/(2k)`,
  which at `sigma = 1-1/k` is exactly `(1-sigma)/2` — the Phragmén–Lindelöf convexity line. The
  whole family of mean-value bounds traces the convexity line with zero slack. Mean-value input
  alone can never beat convexity.

---

## 4. Cycle 1 — Phase 4 verdict and interrogation

**Verdict on the block-moment reformulation (B6): `REDISCOVERED` (in substance).**
The Mellin comparison (B3) is *lossless*: `m(k) = max_alpha [beta_k(alpha) - k alpha]`. So the block
moments carry exactly the information of the zeta moments — the reformulation is a change of
coordinates, not new content. Its value is presentational (it is decoupling-shaped) plus the
calibration below. `[NOT NEW SCIENTIFIC KNOWLEDGE]` as a theorem; retained as campaign
infrastructure.

### Calibration table — what it actually takes to beat Bourgain (`13/84`)
Using `mu(1/2) <= m(k)/(2k)` (moment + Sobolev spike), with the known
`m(2)=1`, `m(6) <= 2` (Heath-Brown), `m` convex:

| lever | known | needed to beat `13/84` | gap |
|---|---|---|---|
| `m(3)` — sixth moment `int|zeta|^6` | `<= 5/4` (convexity) | `< 6*13/84 = 13/14 = 0.9286` | **impossible** (`m >= 1`) |
| `m(4)` — eighth moment `int|zeta|^8` | `<= 3/2` (convexity) | `< 8*13/84 = 26/21 = 1.2381` | `0.262` |
| `m(6)` — twelfth moment `int|zeta|^{12}` | `<= 2` (Heath-Brown) | `< 31/21 = 1.4762` via `m(4) <= 1+(m(6)-1)/2` | `0.524` |
| `k` at which a *perfect* moment first beats `13/84` | — | `k > 42/13 = 3.2308` | — |

**Consequence worth stating plainly.** *The sixth moment of zeta, even in its perfect form
`M_6 << T^{1+eps}`, can never beat Bourgain's `13/84`* — it only gives `1/6`. The first moment
whose full strength surpasses the current subconvexity record is the **eighth**. Any programme
aiming at `mu(1/2)` through moments should target `k = 4`, not `k = 3`. This reverses the usual
emphasis of the moment literature, which is overwhelmingly focused on the sixth moment.

### Relentless interrogation — what survives the kill
What killed (B6) is that *every* object built from a single AFE block at a single height is a
Mellin slice of `zeta` itself. To gain, the object must use information the marginal distribution
of one block cannot see. Exactly one such resource was located:

**The exact multiplicative dilation identities.** For every `q >= 1` and every scale `N`,
  `sum_{n ~ N, q | n} n^{-it} = q^{-it} D_{N/q}(t)`   (exact, no error term).
These couple *different scales at the same `t`*. No exponential-sum method (van der Corput,
Bombieri–Iwaniec, decoupling) uses them: they all treat `n^{-it}` as a generic smooth-phase sum.
No moment method uses them either: moments integrate each scale separately and only ever see
marginals. This is the one genuinely unused resource identified in cycle 1.

**[CONJECTURE Λ-SIM] (multi-scale simultaneity).** `[CONJECTURE]` If `|zeta(1/2+it_0)| = T^v` with
`v > 0`, then the largeness is *simultaneous across a positive proportion of dyadic scales*: there
is `c = c(v) > 0` such that
  `#{ j <= (1/2)log_2 T : |G_{2^j}(t_0)| >= T^{v}/(log T)^{C} } >= c * log T`.
Falsifiable, and structurally opposite to the "one bad block" picture that all current upper-bound
methods implicitly assume. If true, the measure of such `t_0` is controlled by a *joint* large-value
estimate for `log T` simultaneously-large Dirichlet polynomials of different lengths, which is a
far more rigid constraint than any single-scale large-value estimate.
`[OPEN CORE]`: no mechanism yet forces simultaneity; the dilation identities give the coupling but
not the lower bound.

**Carried to cycle 2:** attack Λ-SIM, and its contrapositive ("largeness can be concentrated on a
single scale") which would be a genuine structural obstruction if true.

---

## 5. Cycle 2 (2026-07-25) — corrected calibration, and the subconvexity-neutrality of the sixth moment

The cycle-1 table routed `m(4)` through `m(6)` and therefore understated how accessible the
thresholds are. Corrected and sharpened below. `[PROVED HERE]`, elementary but the conclusions are
strategic.

**(C1) Threshold law.** `mu(1/2) <= m(k)/(2k)` for every `k >= 1` (moment + Sobolev/Gallagher
spike). Hence a moment bound beats Bourgain's `13/84` **iff** `m(k) < 13k/42`.

| `k` | moment | needed `m(k)` to beat `13/84` | best known `m(k)` | source of the known bound |
|---|---|---|---|---|
| 2 | 4th  | `26/42 = 0.6190` | `= 1` | classical; **impossible**, `m >= 1` |
| 3 | 6th  | `13/14 = 0.9286` | `<= 5/4` | convexity; **impossible**, `m >= 1` |
| 4 | 8th  | `26/21 = 1.2381` | `<= 3/2` | Cauchy–Schwarz between 4th and 12th (Ivić); best known |
| 5 | 10th | `65/42 = 1.5476` | `<= 7/4` | convexity |
| 6 | 12th | `13/7  = 1.8571` | `<= 2`   | Heath-Brown 1978, QJM 29; no improvement located as of 2026-07 |
| `>= 6` | — | `13k/42` | `<= 2 + 13(k-6)/42` | Hölder with Bourgain's pointwise bound — constant gap `1/7` |

- Break-even index: `k = 42/13 = 3.2308...`. **No moment with `k <= 42/13` can beat `13/84`, however
  perfect.** The sixth moment conjecture in its strongest possible form yields only `1/6`.
- Most accessible lever, by relative gap: **`k = 6`.** Needed excess over the perfect value `1` is
  `6/7 = 0.857`; the known excess is `1`. A `14%` improvement of Heath-Brown's forty-eight-year-old
  twelfth-moment exponent, from `T^2` to `T^{13/7}`, beats the current subconvexity record.
  (`k = 4` needs a `52%` cut of its excess; `k = 3` is impossible.)

**(C2) THEOREM (subconvexity-neutrality of the sixth moment).** `[PROVED HERE]`
Assume the sixth moment conjecture `m(3) = 1` together with Heath-Brown's `m(6) <= 2`. Then
  `min_{k >= 1} m(k)/(2k) = 1/6`,
and the minimum is attained at *every* `k in [3,6]` and asymptotically for every `k > 6`.
That is: **proving the sixth moment conjecture does not improve the subconvexity exponent at all —
it reproduces exactly the Weyl bound `1/6` and does not reach Bombieri–Iwaniec's `9/56`, let alone
Bourgain's `13/84`.**

*Proof.* `m` is convex (Hölder) with `m >= 1`. From `m(2) = m(3) = 1` and convexity, `m ≡ 1` on
`[0,3]`. On `[3,6]` convexity gives `m(k) <= 1 + (m(6)-1)(k-3)/3 <= 1 + (k-3)/3 = k/3`. The chord
from `(3,1)` to `(6,2)` is the **ray `m = k/3` through the origin**, so `m(k)/(2k) <= 1/6` with
equality throughout `[3,6]`; and `m(k) >= 2 mu(1/2) k` (spike lower bound) forbids anything smaller
on that range unless `mu < 1/6`. For `k > 6`, Hölder gives `m(k) <= m(6) + 2 mu (k-6)`, whence
`mu <= [2 + 2 mu(k-6)]/(2k)`, i.e. `6 mu <= 1`. For `k < 3`, `m ≡ 1` gives `mu <= 1/(2k) >= 1/6`. ∎

*Sharp form.* If instead `m(3) = 1` and `m(6) = M <= 2`, then `min_k m(k)/(2k) = M/12`, attained at
`k = 6`. So under the sixth moment conjecture the subconvexity exponent is governed **entirely** by
the twelfth moment, and beating `13/84` requires exactly `M < 13/7`.

**Strategic consequence for the campaign.** The moment literature's flagship target (`k = 3`) is
provably subconvexity-neutral. Every unit of effort aimed at `mu(1/2)` through moments should go to
`k = 6` (or `k = 4`), never to `k = 3`. Recorded as the campaign's primary lever:

**[TARGET Λ-12] `int_T^{2T} |zeta(1/2+it)|^{12} dt <<_eps T^{13/7 - delta}` for some `delta > 0`.**
Implies `mu(1/2) < 13/84`. Equivalent large-deviation form: the rate function must satisfy
`phi(v) >= 12v - 6/7` for all `v <= 13/84`, versus Heath-Brown's `phi(v) >= 12v - 1`.

### (C3) The pivot point `v = 1/8` — a triple coincidence

Work in the large-deviation coordinates of (M2): `phi(v)` defined by
`meas{t in [T,2T] : |zeta(1/2+it)| > T^v} = T^{1-phi(v)+o(1)}`, and
`m(k) = 1 + sup_v [2kv - phi(v)]`.

Known unconditional constraints, in full:
- `phi(v) >= 4v`      (fourth moment, Ingham/Heath-Brown);
- `phi(v) >= 12v - 1` (Heath-Brown 1978, twelfth moment);
- `phi(v) = +infinity` for `v > 13/84` (Bourgain).

**The two moment constraints cross exactly at `v = 1/8`:** `4v = 12v - 1 <=> v = 1/8`, both equal
`1/2`. Below `1/8` the fourth moment is binding; above it the twelfth moment is.

**At the same point, the self-dual block sits exactly at the Guth–Maynard threshold.** With
`N = sqrt(T/2pi)` the critical block, `|zeta| = T^v` forces `|D_N| = N^{1/2} T^{v} = N^{1/2+2v}`,
and `1/2 + 2v = 3/4` **exactly when `v = 1/8`** — i.e. `|D_N| = N^{3/4}`, which is precisely the
regime Guth–Maynard single out as "the critical situation for several estimates in analytic number
theory connected to prime numbers and the Riemann zeta function" (arXiv:2405.20552).

So three independently-arrived-at critical points coincide: the 4th/12th-moment crossover, the
Guth–Maynard `N^{3/4}` large-value threshold, and the density-hypothesis line `sigma = 3/4`.

**(C4) Exact statement of what must be beaten.** `m(6) <= 2 - delta` is equivalent to
`phi(v) >= 12v - 1 + delta` for all `v`, and the supremum defining `m(6)` is attained precisely on
the window
  **`v in [1/8, 13/84]`** (below `1/8` the fourth moment already gives `12v - phi(v) <= 8v < 1`;
  above `13/84` Bourgain gives `phi = infinity`).
Hence:

> **[TARGET Λ-φ]** Prove `phi(v) >= 12v - 1 + delta` uniformly for `v in [1/8, 13/84]`, i.e.
> `meas{t in [T,2T] : |zeta(1/2+it)| > T^v} << T^{2 - 12v - delta}` on that window.
> Any `delta > 0` improves Heath-Brown's twelfth moment. **`delta > 1/7` beats Bourgain's `13/84`.**
> At the left endpoint this reads: `meas{|zeta(1/2+it)| > T^{1/8}} << T^{1/2 - delta}`, versus the
> currently forced `T^{1/2+o(1)}` — i.e. *the fourth moment must be shown not to be saturated by
> values of size `T^{1/8}`*.

**Cycle-2 negative finding (record, do not repeat).**
- **D9.** General-coefficient large-value estimates (Montgomery mean value, Halász–Montgomery,
  Huxley, and Guth–Maynard) do **not** currently help at the pivot. At `v = 1/8`, `N = sqrt T`:
  Halász–Montgomery gives `R << T^{3/4}`, Guth–Maynard improves the general-coefficient exponent,
  but the *specific* coefficient structure already does better — the fourth moment of the block
  (`int_T^{2T}|D_{sqrt T}|^4 ≍ T^2`, unconditional) gives `R << T^{1/2}`, which is what
  Heath-Brown's bound reproduces. Beating `T^{1/2}` at `v = 1/8` needs the multiplicative structure,
  not a sharper general large-value theorem. Guth–Maynard's improvement is therefore *not* a route
  to `mu(1/2)`, which is consistent with their paper claiming only a zero-density consequence.
- Also checked: the sixth moment of the block (`beta_3(1/2) <= 17/6`) gives `R << T^{7/12}` at the
  pivot — worse than the fourth. The fourth moment is the strongest available tool at `v = 1/8`.

### (C5) THEOREM — the moment-neutrality law  `[PROVED HERE]`

Let `theta` be any established subconvexity exponent (`mu(1/2) <= theta`; currently `theta = 13/84`),
and suppose the perfect moment bound `m(j) = 1` is established for some real `j >= 2`
(i.e. `int_0^T |zeta(1/2+it)|^{2j} dt <<_eps T^{1+eps}`). Then

  **`inf_{k >= 1} m(k)/(2k) = min( 1/(2j), theta )`.**

Consequently the perfect `2j`-th moment yields a *new* subconvexity bound **iff `j > 1/(2 theta)`**;
otherwise it is exactly neutral — it cannot improve on `theta` by any amount, at any `k`.

*Proof.* In large-deviation coordinates, `m(j) = 1` is equivalent to `phi(v) >= 2jv` for all `v`, and
`mu(1/2) <= theta` is equivalent to `phi(v) = +infinity` for `v > theta`. Hence for `k >= j`,
`m(k) = 1 + sup_{v <= theta}[2kv - phi(v)] <= 1 + 2(k-j) theta`, so
`m(k)/(2k) <= theta + (1 - 2 j theta)/(2k)`; and `m(k) = 1` for `k <= j` gives `m(k)/(2k) = 1/(2k)`,
minimised at `k = j`. If `2 j theta < 1` the `k >= j` branch decreases to `theta` but never below it,
and the `k <= j` branch bottoms out at `1/(2j) > theta`; the infimum is `theta`. If `2 j theta > 1`
the `k >= j` branch increases from its value `1/(2j)` at `k = j`; the infimum is `1/(2j) < theta`.
Both cases are `min(1/(2j), theta)`. ∎

**Corollary (the sixth moment is subconvexity-neutral, sharp form).** With `theta = 13/84` and
`j = 3`: `2 j theta = 13/14 < 1`, so `inf_k m(k)/(2k) = 13/84`. **Proving
`int_0^T|zeta(1/2+it)|^6 dt <<_eps T^{1+eps}` — the flagship open problem of the moment literature —
cannot improve the subconvexity exponent by any amount whatsoever, even when combined with
Bourgain's bound and with Heath-Brown's twelfth moment.** The optimised bound it yields is
`13/84 + 1/(28k) -> 13/84`, approaching the known value from above and never reaching below it.

**Corollary (where to aim).** The threshold is `j > 1/(2 theta) = 42/13 = 3.2308...`. The eighth
moment (`j = 4`, `2 j theta = 26/21 > 1`) gives `mu(1/2) <= 1/8`. Everything below `j = 42/13` is
neutral. This is the campaign's selection rule for moment targets.

*Novelty note.* The individual implication "`m(j)=1` gives `mu <= 1/(2j)`" is classical (Ivić).
The *neutrality law* — that a perfect moment is worthless against a record `theta` unless
`j > 1/(2 theta)`, with the exact `min(1/(2j), theta)` formula — is the new statement, and it is
what makes the sixth moment's neutrality visible. Search of the 2026 survey literature
(arXiv:2509.20335, Florea JLMS 2026) found no such statement.

**(C5) formalized.** Lean module `GaloisForLFunctions.HTGeometry.MomentNeutralityLaw`; capstone
`HTGeometry.isGLB_momentBound`, threshold `HTGeometry.momentBound_improves_iff`, instances
`sixth_moment_neutral`, `eighth_moment_improves`, `sixth_below_eighth_above`, convexity bridge
`eq_one_of_convexOn_of_one_le`. Axioms `[propext, Classical.choice, Quot.sound]` only;
`scripts/formal_tools.py lint` passes. Card: `../3-formalized/moment-neutrality-law-subconvexity.md`.

---

## 6. Cycle 3 (2026-07-25) — the eighth moment `m(4)`

**Target.** `m(4) < 26/21 = 1.2381` (known `<= 3/2`, from Cauchy–Schwarz between the 4th and 12th
moments; this is the *only* known route to `m(4)` — there is no direct eighth-moment argument in
the literature). By (C5) this yields `mu(1/2) <= m(4)/8 < 13/84`.

**What the current bound actually is.** `m(4) <= (m(2)+m(6))/2 = (1+2)/2 = 3/2` is pure
interpolation: it uses **no** eighth-moment information at all. So the eighth moment has never been
attacked on its own terms. Ng–Shen–Wong (arXiv:2204.13891) give an *asymptotic* for the eighth
moment only under RH **and** the quaternary additive divisor conjecture; unconditionally nothing
beyond interpolation is known. This is a genuinely unworked target, unlike the sixth moment.

**Reduction to the block form.** By (B3), `m(4) = max_{0<alpha<=1/2} [beta_4(alpha) - 4 alpha]`.
Unconditionally `beta_4(alpha) = 1 + 4 alpha` for `alpha <= 1/4` (B2: the diagonal dominates when
`k alpha <= 1`). So

  **`m(4) = max_{1/4 < alpha <= 1/2} [ beta_4(alpha) - 4 alpha ]`,**

i.e. the entire eighth-moment problem lives on block lengths `N in (T^{1/4}, T^{1/2}]` — a single
dyadic octave of scales. Everything shorter is unconditionally perfect.

At `alpha = 1/2`: need `beta_4(1/2) < 26/21 + 2 = 68/21 = 3.2381`, floor `3`, known `7/2`.

**(C6) The eighth moment localises to a single octave of scales.** `[PROVED HERE]`
Write `P = N^4 ≍ T^{4 alpha}` and `S_4(h) = sum_A r_4(A) r_4(A+h)`, `r_4(A) = #{A = n_1n_2n_3n_4,
all n_i ~ N}` (the *balanced* quaternary divisor function). Then
`int_T^{2T}|D_N|^8 dt = T E_4^x(N) + sum_{h != 0} S_4(h) K_T(h)`, `K_T(h) = int_T^{2T}(A/B)^{-it}dt`,
`|K_T(h)| <= min(T, 2P/|h|)`. Trivially
`sum_{h!=0} S_4(h)|K_T(h)| << P^2 log T = T^{8 alpha + eps}` (split at `|h| = P/T`; both pieces give
`P^2`). Hence `beta_4(alpha) <= max(1 + 4 alpha, 8 alpha)` unconditionally, so

  `beta_4(alpha) - 4 alpha <= max(1, 4 alpha) <= 26/21`  **whenever `alpha <= 13/42 = 0.30952...`.**

Combined with (B2) (`beta_4(alpha) = 1+4alpha` for `alpha <= 1/4`), the eighth-moment target
`m(4) < 26/21` therefore needs new input **only** on

  **`alpha in (13/42, 1/2]`** — one octave of block lengths, `N in (T^{13/42}, T^{1/2}]`.

For comparison, the *currently known* `m(4) <= 3/2` is nontrivial only on `alpha in (3/8, 1/2]`
(`8 alpha <= 4 alpha + 3/2 <=> alpha <= 3/8`), and it is obtained purely by Cauchy–Schwarz
interpolation `m(4) <= (m(2)+m(6))/2`; **no direct eighth-moment argument exists in the literature**
(Ng–Shen–Wong arXiv:2204.13891 give an asymptotic only under RH plus the quaternary additive
divisor conjecture). The eighth moment is therefore an unworked target, unlike the sixth.

**(C7) Cancellation calibration at `alpha = 1/2`.** The off-diagonal must cancel below its trivial
size `P^2 = T^4`:
- known (`beta_4(1/2) <= 7/2`, from `m(4) <= 3/2` through (B3)): cancellation `>= T^{1/2}`;
- needed (`beta_4(1/2) < 68/21`): cancellation `> T^{16/21} = T^{0.7619}`;
- absolute floor (diagonal `T^3`): cancellation `T^1`.
So the balanced quaternary shifted-divisor sums are *already known* to cancel by `T^{1/2}` against
the kernel `K_T`; the task is to raise that to `T^{16/21}`, i.e. to reach 76% of the maximum
possible cancellation where 50% is currently forced.

**D10 (recorded).** Positivity/test-function lower bounds on the near-diagonal do **not** obstruct
this. The near-diagonal group `|h| <= P/T` carries kernel `≍ T e^{-iT log(A/B)}`, whose phase
`-Th/B` sweeps only `[-1,1]`, so that group is `≍ P^2 = T^4` in magnitude and near-coherent — but it
is *not* a lower bound for the whole integral, since the far group `|h| > P/T` has comparable
magnitude `P^2` with oscillating sign. Any nonnegative test function supported in `[T,2T]` inherits
the phase `e^{-i t_0 log(A/B)}` from its centre `t_0 ≍ T` and so cannot isolate the near-diagonal.
Do not attempt to derive a contradiction (or an `Omega`-result) from near-diagonal positivity.

### (C8) The eighth moment through Ivić's shift-average transfer — exact requirement

Located the right machinery: Ivić, *On the general additive divisor problem* (with Wu,
arXiv:1106.4744), which contains the general-`k` transfer and the best averaged bound. This
supersedes my hand-built (B1)–(B6) off-diagonal analysis, which reproduces it. Notation:
`D_k(N,h) = sum_{N<n<=2N} d_k(n) d_k(n+h)`, `Delta_k(N;h)` its error against the Conrey–Gonek main
term, `beta_k` the mean-square exponent of the ordinary divisor error
(`int_1^X |Delta_k(x)|^2 dx << X^{1+2 beta_k}`).

**Two classical facts imported into the campaign:**
- `alpha_k >= beta_k >= (k-1)/(2k)`, and **LH is equivalent to `alpha_k = beta_k = (k-1)/(2k)` for
  every `k`** — the generalized divisor problem. A fourth equivalent formulation for the ledger.
- Ivić's transfer: `int_0^T |zeta(1/2+it)|^{2k} dt << T^{1+eps} (1 + sup_{T^{1+eps}<M<<T^{k/2}}
  G_k(M;T)/M)`, `G_k(M;T) = sup_{x≍M, t <= M^{1+eps}/T} |sum_{h<=t} Delta_k(x,h)|`.

**Reduced transfer formula.** If `sum_{h<=H} Delta_k(N;h) << H^a N^{b+eps}` for `H <= N^{1+eps}/T`,
then taking the sup at `M = T^{k/2}`,
  **`m(k) <= 1 + max(0, k(a+b-1)/2 - a)`.**
(For `k=3` this is exactly Ivić's `(1.11)` exponent `(a+3b-1)/2`.)

**Exact criticality, again — twice over, at `k = 4`:**
- **No cancellation** in the shift sum (`a = 1`) with Vinogradov's conjectured `Delta_4(x,h) <<
  x^{3/4+eps}` (`b = 3/4`) gives `m(4) <= 1 + (2·(3/4) - 1) = 3/2` — **exactly the currently known
  bound**, which was obtained by a completely different route (Cauchy–Schwarz between the 4th and
  12th moments). The additive-divisor route and the interpolation route land on the same number.
- **Square-root cancellation** in the shift sum (`a = 1/2`, `b = 3/4`) gives
  `m(4) <= 1 + max(0, 2·(1/4) - 1/2) = 1` — **exactly the perfect eighth moment**, i.e. `mu(1/2) <= 1/8`.

So the whole eighth-moment problem sits *strictly between* no cancellation and square-root
cancellation in `sum_{h<=H} Delta_4`, and the target is explicit:

> **[TARGET Λ-8h]** `sum_{h<=H} Delta_4(N;h) << H^{a} N^{3/4+eps}` with **`a < 31/42 = 0.73809...`**
> at `H ≍ N^{1/2}` gives `m(4) < 26/21` and hence `mu(1/2) < 13/84`.
> `a = 1` is no cancellation, `a = 1/2` is square-root cancellation: the target is **52.4% of the
> way** from one to the other (`(1 - 31/42)/(1 - 1/2) = 11/21`).

**Known status of Λ-8h.** Ivić–Wu Theorem 1: `sum_{h<=H} Delta_k(N;h) <<_eps N^eps (H^2 + N^{1+beta_k})`
for `1 <= H <= N`, with `beta_3 = 1/3`, **`beta_4 = 3/8`**, `beta_5 <= 9/20`, `beta_6 <= 1/2`.
Note `beta_4 = 3/8 = (4-1)/(2·4)` is already the *conjecturally optimal* value, so their `k=4` bound
is not improvable through `beta_4`. At `H = N^{1/2}` it gives `N^{11/8} = H^{5/4} N^{3/4}`, i.e.
`a = 5/4` — **worse than no cancellation**, and it yields only `m(4) <= 7/4`.

**The structural opening.** Ivić–Wu's second term `N^{1+beta_k}` is **independent of `H`**: it comes
from Cauchy–Schwarz against the mean square of `Delta_k(x)`, which discards the `H`-average entirely.
The needed bound `H^{a} N^{3/4}` *does* decay with `H`. At the relevant `H ≍ N^{1/2}` their bound is
therefore lossy by construction. Any estimate that retains `H`-dependence below `H = N^{(1+beta_4)/2}
= N^{11/16}` is new territory — and `N^{1/2} < N^{11/16}`, so the range that matters is exactly the
range their method throws away.

**Cycle-3 target for cycle 4:** an `H`-sensitive bound for `sum_{h<=H} Delta_4(N;h)` in the range
`H <= N^{1/2}`, where the Ivić–Wu Cauchy–Schwarz step is provably lossy.

---

## 7. Cycle 4 (2026-07-25) — the exact-criticality phenomenon, and the duality-breaking opening

### (C9) Seven independent instances of exact criticality  `[PROVED HERE, each]`

Every assembled estimate examined in this campaign lands **exactly** on the bound already known,
with zero slack — never below it. Collected:

1. **Mean value / large sieve, every `k` and every `sigma`.** `int_0^T|zeta(sigma+it)|^{2k} << T^{1+eps}`
   holds exactly for `sigma >= 1 - 1/k`, and the resulting pointwise bound `1/(2k)` equals
   `(1-sigma)/2` at `sigma = 1-1/k` — the Phragmén–Lindelöf line, traced with no slack. (D8)
2. **Block moments.** `beta_k(alpha) <= max(1+k alpha, 2k alpha)`; diagonal = trivial off-diagonal
   exactly at `N^k = T`, and the bound there is exactly `1/4`. (B2)
3. **Sixth moment + Heath-Brown.** `m(3)=1, m(6)<=2` give `m(k)/(2k) = 1/6` for *every* `k in [3,6]`,
   because the chord from `(3,1)` to `(6,2)` is the ray `m = k/3` through the origin. (C2)
4. **Sixth moment + Bourgain.** Yields `13/84 + 1/(28k) -> 13/84`: exact neutrality. (C5)
5. **Additive divisor, no cancellation, `k=4`.** `a=1, b=3/4` gives `m(4) <= 3/2` — exactly the
   known bound, reached by a completely different route (Cauchy–Schwarz of the 4th and 12th). (C8)
6. **Optimal short-interval mean square + Cauchy–Schwarz, `k=4`.** Even with the best conceivable
   `int_X^{2X}(Delta_4(x+H)-Delta_4(x))^2 dx ≍ XH (log X)^c`, Cauchy–Schwarz gives
   `R_4 << N H^{1/2} = N^{5/4}` at `H = N^{1/2}`, i.e. `a = 1` again — exactly `m(4) <= 3/2`.
7. **Exponent pairs.** The `B`-process acts as the **identity** on the self-dual line
   `l = k + 1/2` (`B(k,l) = (l-1/2, k+1/2) = (k, k+1/2)` there), and `mu(1/2) <= k` on that line.
   The defect `d = l-k-1/2` transforms as `d -> -d` under `B` and `d -> (d+1/2)/(2k+2)` under `A`.

**[CONJECTURE DUAL] (duality-invariance barrier).** Every estimate built only from the approximate
functional equation, Hölder/Cauchy–Schwarz, mean-value theorems, and divisor-correlation bounds is
*invariant* under the functional-equation duality `s <-> 1-s` in the sense that it depends on the
parameters only through the self-dual combination; consequently its optimum is attained at the
self-dual parameter and it cannot beat the value there. Strict improvement requires a
**duality-breaking** input — one that uses the smooth structure of the phase `-t log n` in `n`.
This is why van der Corput / Bombieri–Iwaniec / decoupling are the only methods that have ever moved
`mu(1/2)`, and why every hybrid above returns the input value unchanged.
Falsifiable: exhibit a duality-invariant assembly that beats its self-dual value.

### (C10) `k = 4` is the self-dual index of the shift-average transfer  `[PROVED HERE]`

In Ivić's transfer the sup is taken at `M = T^{k/2}` and the shift range is `H <= M/T = T^{k/2-1}`.
The self-dual shift scale for the divisor error at length `N = M` is `H = N^{1/2} = T^{k/4}`. These
coincide **exactly when `k = 4`**:
  `k/2 - 1 = k/4  <=>  k = 4`.
For `k = 3` the transfer only needs `H <= T^{1/2} < N^{1/2} = T^{3/4}` (short regime); for `k = 6`
it needs `H <= T^2 > N^{1/2} = T^{3/2}` (long regime). So the eighth moment is precisely the
self-dual case — the same index the neutrality law (C5) singles out as the first useful one.

### (C11) The duality-breaking opening: Voronoi at the self-dual shift

Ivić–Wu bound `R_k(N,H) = sum_{N<n<=2N} d_k(n)[Delta_k(n+H) - Delta_k(n)]` by Cauchy–Schwarz, which
discards both the `H`-dependence and all oscillation. Replace it by the Voronoi/Oppenheim expansion
  `Delta_k(x) = x^{(k-1)/(2k)} sum_{m<=Y} d_k(m) m^{-(k+1)/(2k)} C_k(2 pi k (mx)^{1/k}) + ...`
The short-interval difference `Delta_k(x+H) - Delta_k(x)` damps the dual terms with
`H (m/x^{k-1})^{1/k} << 1`, i.e. it localises the dual sum to
  **`m ≍ x^{k-1}/H^k`.**
At `k = 4`, `x ≍ N`, `H ≍ N^{1/2}`: the dual length is `N^3/N^2 = N` — **exactly the length of the
original sum**. This is the analytic content of (C10): the `k=4` shift average at `H = sqrt N` is a
genuinely self-dual problem, and `R_4` becomes a bilinear exponential sum

  `R_4 ≍ N^{3/8} sum_{n ~ N} d_4(n) sum_{m ~ N} d_4(m) m^{-5/8} e( 4 (mn)^{1/4} ) x (damping)`,

with phase `(mn)^{1/4}`. Bilinear forms with a `(mn)^{1/4}` phase are exactly the objects that
van der Corput / Bombieri–Iwaniec spacing methods and `l^2`-decoupling address — i.e. this is a
**duality-breaking** input in the sense of `[CONJECTURE DUAL]`, and by (C9.6) it is the *only* way
past `m(4) <= 3/2`.

**Required saving.** The Cauchy–Schwarz-optimal bound is `R_4 << N^{5/4}`; the target Λ-8h needs
  `R_4 << N^{47/42} = N^{1.11904...}`,
so **a saving of `N^{5/4 - 47/42} = N^{11/84} = N^{0.13095...}` over the best possible
Cauchy–Schwarz bound** suffices to give `mu(1/2) < 13/84`. This is a modest power saving in a
bilinear exponential sum of dimensions `N x N` — the first target in this campaign that is
quantitatively within reach of existing exponential-sum technology.

**Cycle 5 task:** make the `k=4` Voronoi expansion and the damping factor explicit, verify the
localisation `m ≍ x^3/H^4` rigorously, and estimate the resulting bilinear form
`sum_{n~N} sum_{m~N} d_4(n) d_4(m) m^{-5/8} e(4(mn)^{1/4})` — needed saving `N^{11/84}` over trivial.

### (C12) Numerical pre-certification of the `k = 4` Voronoi expansion  `[NUMERICAL]`

Before building on the expansion used in (C11) it was tested directly.
`sum_{n<=x} d_4(n)` computed exactly for `x <= 4 x 10^6` by three divisor convolutions; the main
term `x p_3(log x) = Res_{s=1} zeta(s)^4 x^s/s` evaluated from the Stieltjes constants
(`A(u)^4 · x^u/(1+u)`, coefficient of `u^3`). Then `Delta_4(x)/x^{3/8}` was resampled in the
variable `u = x^{1/4}` on `x in [2,4] x 10^6` and its periodogram computed.

Predicted by `Delta_4(x) = c x^{3/8} sum_m d_4(m) m^{-5/8} cos(8 pi (m x)^{1/4} + c_4) + ...`:
peaks at frequency `4 m^{1/4}` cycles per unit `u`, with amplitude proportional to `d_4(m) m^{-5/8}`.

Measured (amplitude at the predicted frequency, versus predicted weight):

| `m` | `4m^{1/4}` | predicted `d_4(m) m^{-5/8}` | measured | ratio |
|---|---|---|---|---|
| 1 | 4.0000 | 1.000 | 0.1197 | 0.120 |
| 2 | 4.7568 | 2.594 | 0.2205 | 0.085 |
| 3 | 5.2643 | 2.013 | 0.1688 | 0.084 |
| 4 | 5.6569 | 4.204 | 0.3004 | 0.071 |
| 5 | 5.9814 | 1.463 | 0.1292 | 0.088 |
| 6 | 6.2603 | 5.221 | 0.4433 | 0.085 |
| 7 | 6.5063 | 1.185 | 0.1066 | 0.090 |
| 8 | 6.7272 | 5.453 | 0.4713 | 0.086 |
| 9 | 6.9282 | 2.533 | 0.2449 | 0.097 |
| 10 | 7.1131 | 3.794 | 0.3211 | 0.085 |
| 12 | 7.4448 | 8.464 | 0.6911 | 0.082 |

The ratio is constant to a few percent across `m` (the `m=11` row is contaminated by leakage from
the strong `m=12` peak at `7.4448` and is omitted). The unconstrained periodogram maxima occur at
`f` with `(f/4)^4 = 11.87, 7.90, 5.97, 15.29, 10.12, 3.92, 9.11` — integers `12, 8, 6, 15, 10, 4, 9`,
exactly the `m` with the largest `d_4(m) m^{-5/8}`.

**Certified:** the amplitude exponent `x^{3/8}`, the dual coefficients `d_4(m) m^{-5/8}`, and the
phase `8 pi (m x)^{1/4}`. This is the expansion (C11) rests on.

**Not certified (honest limitation).** The short-interval mean square
`<(Delta_4(x+H) - Delta_4(x))^2>` was also measured, for `H` from `10` to `10^5` at `x ≍ 3 x 10^6`.
It grows like `H^{0.7}` and saturates at `2<Delta_4^2> ≍ 1.3 x 10^9` already at `H ≈ 10^3`, whereas
the asymptotic heuristic predicts growth linear in `H` with saturation at `H ≍ x^{3/4} ≍ 7 x 10^4`.
The discrepancy is explained: at `x ≍ 3 x 10^6` the sum is dominated by the individual variance of
`d_4(n)` (empirically `E[d_4^2] ≈ 10^7`, consistent with `x(log x)^{15}` moments), not by the
Voronoi regime. **The asymptotic short-interval regime for `d_4` is numerically inaccessible at any
feasible `x`** — the `(log x)^{15}` moments would need astronomically large `x`. Criticality
instance (C9.6) therefore stands on the analytic argument only; do not attempt to certify it
numerically again.

---

## 8. Cycle 5 (2026-07-25) — the pivot mechanism, and a proof that Guth–Maynard cannot reach `mu(1/2)`

**D11 (correction, recorded).** Radziwiłł's `4.36`-th moment (IMRN 2012, arXiv:1106.4806) is
**conditional on RH** (`M_k(T) << T(log T)^{k^2}` for `0 < k < 2 + 2/11`, assuming RH). It therefore
cannot be fed into the neutrality law: the largest `j` with `m(j) = 1` *unconditionally* is still
`j = 2`, and `min(1/4, 13/84) = 13/84` — neutral. An earlier draft of this log briefly used it
unconditionally to claim `m(4) <= 1.4764 < 3/2`; **that claim is withdrawn.** Under RH the
Lindelöf hypothesis is a theorem anyway, so RH-conditional moment bounds are worthless here.
Unconditionally `m(4) <= 3/2` stands.

### (C13) Why `v = 1/8` is the pivot: `V^4 = sqrt N` at the self-dual block  `[PROVED HERE]`

Take the self-dual Dirichlet polynomial for `zeta^2`: the approximate functional equation for
`zeta(s)^2` has conductor `(t/2pi)^2`, so its balanced length is `N ≍ T`, with coefficients
`d(n) n^{-1/2}`. Largeness `|zeta(1/2+it)| >= V` forces some block to satisfy `|sum_{n~N} d(n)
n^{-1/2-it}| >= V^2 / log T`. In the Halász–Montgomery inequality

  `sum_r |<a, phi_r>|^2 <= ||a||^2 max_r sum_{r'} |<phi_r, phi_{r'}>|`,   `<phi_r,phi_{r'}> = sum_{n~N} n^{-i(t_r - t_{r'})}`,

the left side is `≍ R V^4` and the Gram off-diagonal is an exponential sum whose **square-root
cancellation size is `N^{1/2} = T^{1/2}`**. The method is non-vacuous exactly when `V^4 > N^{1/2}`:

  `T^{4v} > T^{1/2}  <=>  v > 1/8.`

**So `v = 1/8` is precisely the point at which the largeness of the `zeta^2` polynomial equals the
square-root-cancellation barrier of its own Gram matrix.** Below it, no large-value method whose
off-diagonal input is an exponential-sum bound for `sum_{n~N} n^{-iu}` can say anything at all —
*even granted perfect square-root cancellation*. This is the mechanism behind every criticality
instance at `v = 1/8` recorded in (C3).

**(C14) Halász–Montgomery is capped at the fourth moment.** `[PROVED HERE]` Grant perfect
square-root cancellation `sum_{n~N} n^{-iu} << N^{1/2+eps}` for all `1 <= u <= T`. For `v > 1/8` the
off-diagonal is then absorbed and the diagonal term `||a||^2 · N ≍ T^{1+eps}` gives
`R << T^{1+eps} V^{-4} = T^{1-4v+eps}` — **exactly the fourth-moment bound**. So the entire
Halász–Montgomery family, with the best conceivable exponential-sum input, reproduces `phi(v) >= 4v`
and nothing more. Criticality instance #12.

### (C15) THEOREM — Guth–Maynard's large-value estimate is inert at the self-dual block

Guth–Maynard (arXiv:2405.20552) Theorem 1.1: for `|b_n| <= 1`, `R` well-separated `t_r in [0,T]`
with `|sum_{n~N} b_n n^{it_r}| >= V`,

  `R <= T^{o(1)} ( N^2 V^{-2} + N^{18/5} V^{-4} + T N^{12/5} V^{-4} )`,

against the previous best `R <= T^{o(1)} ( N^2 V^{-2} + T min(N V^{-2}, N^4 V^{-6}) )`.

Parametrise the `zeta^2` blocks by `N = T^beta` (`beta <= 1`, `beta = 1` self-dual) and
`|zeta| >= T^v`, so the block largeness is `V = T^{beta/2 + 2v}`. Then

| term | exponent of `T` |
|---|---|
| `N^2 V^{-2}` | `beta - 4v` |
| `T N V^{-2}` | `1 - 4v` |
| `T N^4 V^{-6}` | `1 + beta - 12v` |
| GM `N^{18/5} V^{-4}` | `8beta/5 - 8v` |
| GM `T N^{12/5} V^{-4}` | `1 + 2beta/5 - 8v` |

**At `beta = 1`:** the previous bound is `max(T^{1-4v}, min(T^{1-4v}, T^{2-12v})) = T^{1-4v}`, and the
two Guth–Maynard terms are `T^{8/5-8v}` and `T^{7/5-8v}`. These fall below `T^{1-4v}` only when
`v > 3/20` and `v > 1/10` respectively; on that range the surviving maximum is still `T^{1-4v}`, and
for `v <= 3/20` the GM terms are strictly *larger*. Hence

  **at the self-dual block `beta = 1`, the Guth–Maynard bound is identically equal to the classical
  bound for every `v`; it never improves it.**

Since the binding block for `phi(v)` is always `beta = 1` (the previous-bound exponent `beta - 4v`
and `1 - 4v` are both maximised there), Guth–Maynard **cannot improve `phi(v)` for any `v`, hence
cannot improve any moment bound and cannot affect `mu(1/2)`.** Their improvement is real but lives
strictly at `beta ≈ 5/6` (their critical case `T = N^{6/5}`, which on our curve is `v = 5/48`, where
they do beat the classical `T^{0.5833}` with `T^{0.5}`) — a subcritical block that zero-density
estimates care about and `mu(1/2)` does not. This is a *proof* of the observation recorded as D9,
and it explains why the paper claims a zero-density and short-interval-primes consequence and no
subconvexity consequence.

**Consequence for the campaign.** At the self-dual block, generic large-value theory — mean value,
Halász–Montgomery, Huxley, Guth–Maynard — gives exactly `phi(v) >= 4v` and nothing else. The *only*
non-generic input anywhere in the subject at `beta = 1` is Heath-Brown's twelfth-moment argument,
which supplies `phi(v) >= 12v - 1`. Everything in the window `[1/8, 13/84]` therefore rests on that
single 1978 argument, and improving `phi` there means improving it. That is the next object of study.

---

## 9. Cycle 6 (2026-07-25) — the frontier collapses to one number, and the `E(T)` identification

### (C16) Heath-Brown's mechanism, recovered

Milićević–White (arXiv:1908.04833, §1 "Overview") transcribe Heath-Brown's t-aspect argument into
the `q`-aspect and state its skeleton explicitly. Translating back:

- The object is the **short second moment** `int_{t_0}^{t_0+G} |zeta(1/2+it)|^2 dt` at scale
  `G ≍ V^2`, chosen so that the sharp bound `<< G T^eps` exactly matches the contribution of one
  large value `|zeta| ≍ V` (a spike of height `V` occupies length `≍ 1/log T`).
- The sharp bound holds for individual `t_0` when `G >= T^{1/3}`, and this **alone** yields the Weyl
  bound. Below `G = T^{1/3}` it fails for individual `t_0`.
- Heath-Brown's actual content is a **large-sieve / approximate-orthogonality argument over the set
  of large-value points**: the relevant vectors attached to different points are nearly orthogonal,
  so few of them can simultaneously avoid cancellation. This recovers the sharp short second moment
  *on average over the large-value set* down to `G = T^{1/4}`.
- Milićević–White state the range of interest as `q^{1/8-eps} <= V <= q^{1/6+eps}` — an **independent
  confirmation of the window `[1/8, 13/84]`** found in (C4).

**(C17) The window is the `E(T)` gap.** `[PROVED HERE]` Under `G = T^{2v}`, the Heath-Brown window
`G in [T^{1/4}, T^{1/3}]` is exactly `v in [1/8, 1/6]`. And:
`int_T^{T+G}|zeta|^2 = G log(T/2pi) + 2 gamma G + O(G^2/T) + (E(T+G) - E(T))`, so the sharp short
second moment holds precisely for `G >> T^{theta_E}` where `E(T) << T^{theta_E}`. Hence

  **`mu(1/2) <= theta_E / 2`**   (Sobolev: `max_I |zeta|^2 << log T · int_I |zeta|^2 << G T^eps`).

- `theta_E = 1/3` (classical) gives `mu <= 1/6` — the Weyl bound, exactly.
- `theta_E = 1/4` — the **conjectured optimum**, sharp because `E(T) = Omega(T^{1/4})` — gives
  **`mu(1/2) <= 1/8`**, i.e. exactly the pivot.

> **The Lindelöf window `[1/8, 13/84]` is the image, under `v = (log_T G)/2`, of the gap
> `[T^{1/4}, T^{1/3}]` between the `Omega`-result and the known upper bound for the error term in
> the second moment of zeta.** The pivot `v = 1/8` is not an artefact: it is the subconvexity
> exponent that the *optimal* second-moment error term would deliver.

**(C18) The `E(T)` race — the narrowest gap in the subject.** Best known
`theta_E = 517/1648 = 0.3137136...` (Bourgain–Watt 2017, simultaneously for `E(T)`, the divisor
problem `Delta(x)` and the circle problem), giving `mu <= 517/3296 = 0.1568568`, just behind
Bourgain's direct `13/84 = 0.1547619`. To beat the record through this route one needs

  **`theta_E < 13/42 = 0.3095238...`,  versus the known `517/1648 = 0.3137136...`  — a gap of `0.00419`, i.e. `1.3%` of the distance to the conjectured optimum `1/4`.**

Both routes already use Bourgain's decoupling, so this is a genuine efficiency race between two
applications of the same technology, not a free lunch — but it is the closest any independent route
stands to the record.

### (C19) The frontier collapses to `phi(1/8)`  `[PROVED HERE]`

With `phi` the large-deviation exponent (`meas{t in [T,2T] : |zeta| > T^v} = T^{1-phi(v)+o(1)}`),

  `m(4) >= 1 + [8·(1/8) - phi(1/8)] = 2 - phi(1/8)`,   `m(6) >= 1 + [12·(1/8) - phi(1/8)] = 5/2 - phi(1/8)`.

Since `phi(1/8) >= 1/2` is what the fourth moment gives, and *every* known method gives exactly
`1/2` there (C13, C14, C15), this yields `m(4) >= 3/2` and `m(6) >= 2` — **the known bounds are
forced, and both are improvable if and only if `phi(1/8) > 1/2`.**

> **[TARGET Λ-1/8] — the single-number frontier.**
> `meas{ t in [T,2T] : |zeta(1/2+it)| > T^{1/8} } << T^{1/2 - delta}` for some `delta > 0`.
> - any `delta > 0` gives the **first improvement of Heath-Brown's twelfth moment since 1978** and
>   simultaneously the first direct improvement of the eighth moment;
> - `delta > 1/7` (i.e. `phi(1/8) > 9/14 = 0.6429`) starts the bootstrap `mu <= (1+c)/12` toward
>   beating `13/84`;
> - `delta > 11/42` (i.e. `phi(1/8) > 16/21 = 0.7619`) gives `m(4) < 26/21` directly.
>
> Equivalently: **the fourth moment of zeta must be shown not to be saturated by values of size
> `T^{1/8}`.** A set of measure `T^{1/2}` carrying `|zeta| ≍ T^{1/8}` contributes exactly `T` to
> `int_T^{2T}|zeta|^4 ≍ T log^4 T` — a `1/log^4 T` fraction. So the scenario to exclude is a
> *log-thin* saturation of the fourth moment; it is not excluded by the fourth-moment asymptotic,
> nor by its error term `O(T^{2/3})`, nor by any large-value estimate now known.

**Necessary conditions recorded.** `m(6) < 13/7` requires `phi(v) > 12v - 6/7` on `[3/28, 13/84]`:
`phi(1/8) > 9/14`, `phi(13/84) > 1`. The top-end condition `phi(13/84) > 1` is implied by the
conclusion itself (if `mu < 13/84` then `phi = infinity` there), so the argument must run as a
**bootstrap**: `mu <= (1 + sup_{v<=mu} min(8v - g(v), 1))/12` with `g = phi - 4v`, iterated downward.

---

## 10. Cycle 7 (2026-07-25) — `Λ-1/8` in its sharpest form: the moment curve must leave the chord

### (C20) THEOREM — `Λ-1/8` is exactly "the moment curve dips below the chord"  `[PROVED HERE]`

`phi` and `m` are Legendre-dual: `m(k) - 1 = sup_v [2kv - phi(v)]`, equivalently
`phi(v) >= sup_k [2kv - (m(k)-1)]`. Evaluating at `v = 1/8`:

  **`phi(1/8) >= sup_{k} [ k/4 - (m(k) - 1) ]`.**

Convexity with `m(2) = 1` and `m(6) <= 2` gives `m(k) <= 1 + (k-2)/4` on `[2,6]`, for which
`k/4 - (m(k)-1) = 1/2` **identically** — a plateau across the whole interval. Hence

  **`phi(1/8) > 1/2`  <=>  `m(k) < 1 + (k-2)/4` for some `k in (2,6)`,**

i.e. **the moment exponent function must be shown to lie strictly below the chord joining `(2,1)`
to `(6,2)` at some interior point.** Since `phi(1/8) > 1/2` is *necessary* for improving either
`m(4)` or `m(6)` (from `m(4) >= 2 - phi(1/8)`, `m(6) >= 5/2 - phi(1/8)`), the entire frontier turns
on one qualitative statement: **the known moment data is exactly the chord, and nothing is known to
be off it.**

The most accessible interior point is `k = 3`: the chord gives `m(3) <= 5/4`, which Ivić confirms is
the best known exponent for `int_0^T |zeta(1/2+it)|^6 dt`. So:

> **`Λ-1/8` follows from ANY improvement of the sixth moment below `T^{5/4}`.**
> Note this does *not* contradict the neutrality law (C5): `m(3) = 1` is subconvexity-neutral, but
> `m(3) < 5/4` is not vacuous — it forces `phi(1/8) > 1/2` and hence `m(4) <= 3/2 - 2delta/3`, the
> first direct improvement of the eighth moment. Neutrality concerns `mu(1/2)`; the chord statement
> concerns the moments themselves.

**(C21) What a sixth-moment improvement needs, exactly.** Through Ivić's transfer
(`int_0^T|zeta|^6 << T^{1+eps} + T^{(a+3b-1)/2+eps}` given `sum_{h<=H} Delta_3(x,h) << H^a x^{b+eps}`
for `H <= x^{1/3+delta}`), the condition `m(3) < 5/4` is

  **`a + 3b < 7/2`.**

| input | `(a,b)` | `a+3b` | verdict |
|---|---|---|---|
| trivial (`Delta_3 << x`, no shift cancellation) | `(1,1)` | `4` | fails |
| Ivić–Wu Cor. 1 in this range (`<< x^{4/3}`, `H`-free) | `(0,4/3)` | `4` | fails — it is trivial for `H <= x^{1/3}` |
| pointwise `Delta_3(x,h) << x^{5/6-delta}` | `(1, 5/6^-)` | `< 7/2` | **suffices** |
| square-root cancellation in `h` | `(1/2, 2/3)` | `5/2` | suffices with huge room |
| Vinogradov's conjecture `Delta_3 << x^{2/3+eps}` | `(1,2/3)` | `3` | gives the full `m(3)=1` |

**The gap is stark:** Ivić–Wu's bound is *trivial* in the range `H <= x^{1/3}` that the sixth moment
needs (their improvement begins at `H >= x^{1/2}`), and `Delta_3(x,h) = o(x)` is **not known for any
`k >= 3`, even for fixed `h`**. So `[3/28, 13/84]`-window progress needs the first nontrivial
ternary additive divisor estimate of any kind.

### (C22) THEOREM — the classical error-term programmes are capped at exactly `1/8`

For `k = 1, 2` the `2k`-th moment of `zeta` has a genuine asymptotic with error `E_k(T)`, and
`int_T^{T+G}|zeta|^{2k} << G T^eps` holds for `G >> T^{theta_{E_k}}`; Sobolev then gives

  **`mu(1/2) <= theta_{E_k} / (2k)`.**

- `k=1`: `theta_{E_1} = 1/3` gives `mu <= 1/6` (the Weyl bound, exactly). The **conjectured optimum
  is `1/4`, sharp because `E(T) = Omega(T^{1/4})`**, and it gives `mu <= 1/8`.
- `k=2`: `theta_{E_2} = 2/3` gives `mu <= 1/6` (the Weyl bound again, exactly). The **conjectured
  optimum is `1/2`, sharp because `E_2(T) = Omega(T^{1/2})** (Ivić–Motohashi), and it gives `mu <= 1/8`.

> **Both error-term programmes — the only two where an asymptotic formula is actually known — are
> capped at exactly `mu(1/2) <= 1/8`, and the cap cannot be lowered because both conjectural optima
> are attained by `Omega`-results.** Solving both famous error-term conjectures optimally yields the
> pivot and never Lindelöf. For `k >= 3` there is no asymptotic, so "`E_k << T^{theta}`, `theta<1`"
> is simply `m(k)=1` and falls under the neutrality law.

This is the fifteenth instance of exact criticality and the sharpest barrier statement so far: the
pivot `v = 1/8` is simultaneously (i) the crossing of the 4th- and 12th-moment constraints,
(ii) the point where `V^4` meets the square-root-cancellation size of the Gram matrix,
(iii) the Guth–Maynard `N^{3/4}` threshold, (iv) the plateau value of `k/4 - (m(k)-1)` on `[2,6]`,
and (v) the ceiling of both classical error-term programmes.

**New dead route.**
- **D12. Selberg-moment / large-deviation route.** `Chebyshev` against Selberg's unconditional
  moments of `log|zeta|` (`int_T^{2T}(log|zeta|)^{2k} ~ T c_k ((1/2)loglog T)^k`) would give
  `meas{|zeta| > T^{1/8}} <= T^{1/2-delta}` — but only if the moment asymptotic holds at
  `k ≍ (1/4) log T / loglog T`. At `k` bounded by any power of `loglog T` the bound degrades to
  `T exp(-c (loglog T)^2)`, which is `T^{1-o(1)}` and gives nothing. Equivalently one needs Gaussian
  tail behaviour out to `lambda ≍ log T / sqrt(loglog T)` deviations, versus the `(loglog T)^{O(1)}`
  range where Selberg-type CLTs are proved — an exponential gap. This regime is governed by prime
  resonance (branch A of S1), not by the CLT.
- **D13. Log-thin invisibility (structural, recorded once).** The scenario to exclude at the pivot
  is a set of measure `T^{1/2}` carrying `|zeta| ≍ T^{1/8}`, which contributes exactly `T` to
  `int|zeta|^4 ≍ T log^4 T` — a `1/log^4 T` fraction. Every short-interval variant reproduces the
  same `T^{1/2}`: with the sharp short fourth moment at scale `G`, `meas(S) << (T/G)(G T^eps/V^4) =
  T^{1+eps}V^{-4}`, **independent of `G`**. Short-interval refinements of the fourth moment can never
  help; only a genuinely larger moment exponent can.

**(C20) formalized.** Lean module `GaloisForLFunctions.HTGeometry.MomentChordPivot`
(`momentChord_upper`, `pivotGain_momentChord`, `pivotGain_gt_half_iff_below_chord`,
`pivotGain_le_half`, `pivotGain_at_four`, `chord_values`). Axioms `[propext, Classical.choice,
Quot.sound]`; lint green. Card `../3-formalized/moment-chord-pivot-law.md`.

**(C23) ANTEDB confirmation (Phase-2 audit, cycle 7).** The Tao–Trudgian–Yang exponent database has
a chapter "Moment growth for the zeta function" defining exactly `M(sigma,A)` with
`int_T^{2T}|zeta(sigma+it)|^A dt << T^{M(sigma,A)+o(1)}`. Recorded: `M(1/2,A)=1` for `0<=A<=4`
(Hardy 1916, Hardy–Littlewood 1923); `M(1/2,12)<=2` (Heath-Brown 1978); Trudgian–Yang piecewise
bounds for `A >= 866/65 ≈ 13.32` (`M(1/2,13)<=2.1340`, ..., `M(1/2,18)<=2.8466`); and the
interpolation `M(1/2,12+delta) <= 2 + delta/8 + (3 sqrt 510/7568) delta^{3/2}` for `0<delta<=86/65`.
**Nothing is recorded on `4 < A < 12`** — confirming that the chord is the entire known envelope
there. Two further observations:
- The linear coefficient of the Trudgian–Yang interpolation is exactly `1/8`, i.e. **the newest
  systematic optimization in the field reproduces the chord slope exactly at `A=12`.** Criticality
  instance #16.
- Their `M(1/2,A)/A` decreases through `0.16415` (`A=13`) to `0.15814` (`A=18`), still above
  `13/84 = 0.154762`, with slopes increasing `0.1380 -> 0.1450`; consistent, no contradiction.

---

## 11. Cycle 8 (2026-07-25) — the chord is the image of one input, and that input is neutral

### (C24) THEOREM — the whole known moment envelope is the image of `(a,b) = (1/2,1)`  `[PROVED HERE]`

Optimising Ivić's transfer over the block length: if `sum_{h<=H} Delta_k(x,h) << H^a x^{b+eps}` for
`H <= x^{1+eps}/T`, then

  **`m(k) <= 1 + max(0, k(a+b-1)/2 - a) =: transferBound k a b`.**

(Verified against Ivić's published `k=3` case `(a+3b-1)/2`; the two agree identically.)

The input `(a,b) = (1/2, 1)` gives, for **every** `k >= 2`,

  `transferBound k (1/2) 1 = 1 + (k-2)/4 = momentChord(2k)`.

Specialising: `m(2) <= 1` (the fourth moment), `m(3) <= 5/4`, `m(4) <= 3/2`, `m(6) <= 2`
(Heath-Brown). **The entire known unconditional moment envelope for zeta is the image of the single
point `(a,b) = (1/2,1)` under the shift-average transfer.** Heath-Brown's 1978 twelfth moment,
proved by a completely different route (short second moments plus an approximate-orthogonality
argument, C16), lands on exactly the same point. Criticality instance #17.

**Where `(1/2,1)` comes from.** It is precisely Cauchy–Schwarz applied to
`R_k(x,H) = sum_{n<=x} d_k(n) [Delta_k(n+H) - Delta_k(n)]`, using `sum_n d_k(n)^2 << x^{1+eps}` and
the *sharp* short-interval mean square `sum_n |Delta_k(n+H) - Delta_k(n)|^2 << x H^{1+eps}`.

**(C25) THEOREM — the short-interval mean square is neutral even at its conjectural optimum.**
Ivić (arXiv:0708.1601, Remark 2) writes of exactly the bound `X^{1+eps} h` for `k > 2`: *"this seems
unattainable at present"*; his Theorem 1 gives only `X^{1+eps} h^{4/3}`, and **that only under
`sigma(k) = 1/2`, i.e. under the Lindelöf hypothesis itself.** By (C24):

- the conjecturally optimal input `x h^{1+eps}` yields exactly the chord — **it would improve
  nothing**;
- the currently available input `x h^{4/3}` yields `(a,b) = (2/3,1)` and hence
  `m(k) <= 1 + max(0, k/3 - 2/3)`: `m(3) <= 4/3`, `m(6) <= 7/3` — strictly *worse* than the chord.

> **Do not chase the short-interval mean square of `Delta_k`.** Solved optimally it is neutral;
> solved as well as is currently conceivable it is worse than what is already known. Recorded as
> **D14**.

### (C26) The breaking criterion  `[PROVED HERE]`

For `k > 2`, `transferBound k a b < momentChord(2k)` **iff** `k(2a+2b-3) < 4a-2`. At `(1/2,1)` both
sides vanish — simultaneously for every `k`, which is why the criticality is exact rather than
coincidental at one index. The criterion holds for every `k > 2` as soon as

- **`b < 1`** at `a = 1/2`: any pointwise saving on the additive-divisor error beyond the trivial
  `Delta_k(x,h) << x^{1+eps}`; or
- **`a < 1/2`** at `b = 1`: better than square-root cancellation in the shift average (not expected).

With Vinogradov's conjectural `Delta_k(x,h) << x^{1-1/k+eps}` and square-root shift cancellation,
`(a,b) = (1/2, 1-1/k)` gives `transferBound = 1 + max(0, k/4 - 1)`: **`m(k) = 1` for `k <= 4`** (the
sixth *and* eighth moments perfect) and `m(6) <= 3/2`.

> **Consequence for the campaign.** Breaking the chord — equivalently `phi(1/8) > 1/2`, equivalently
> the first improvement of the eighth and twelfth moments since 1978 — is **exactly the statement
> that Cauchy–Schwarz is lossy in `R_k(x,H) = sum_n d_k(n)[Delta_k(n+H) - Delta_k(n)]`**, i.e. that
> there is cancellation between `d_k(n)` and the short-interval divisor error. Every other route
> examined in this campaign reduces to this one.

**Lean.** `GaloisForLFunctions.HTGeometry.ShiftAverageTransfer`: `transferBound_half_one`,
`transferBound_envelope`, `transferBound_lt_chord_iff`, `critical_input_equality`,
`breaks_of_b_lt_one`, `transferBound_vinogradov`. Axioms `[propext, Classical.choice, Quot.sound]`;
`lake build GaloisForLFunctions.HTGeometry` green.

**Note on the lint gate.** A concurrent session is adding `RHTower.SmoothAFE*` modules; one of them
(`SmoothAFEDualFactorization`) does not compile, so the repo-wide gate currently reports orphans not
attributable to this campaign. `SmoothAFEZetaResidueDecomposition` built and was wired; the broken
ones were left alone. This campaign's own area builds clean.
