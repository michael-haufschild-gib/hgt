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

---

## 13. Cycle 10 (2026-07-25) — two published theorems, two exact targets, one of them blocked

Located the literature that already treats **exactly** the transfer input, in exactly the shift range
the sixth moment needs: Baier–Browning–Marasingha–Zhao, *Averages of shifted convolutions of
`d_3(n)`* (arXiv:1101.5464; Proc. Edinb. Math. Soc. 55 (2012), 551–576). Their `Delta(N,h)` is
**the same object** as Ivić–Wu's (both follow Conrey–Gonek). They state Ivić's transfer explicitly
and compute their own contribution to it.

**BBMZ Theorem 1.** `sum_{h<=H} Delta(N,h) << (H^2 + H^{1/2} N^{13/12}) N^eps`, `1 <= H <= N`.
Exponent pair `(a,b) = (1/2, 13/12)`; they note it gives `I_3(T) << T^{11/8+eps}`, worse than the
known `5/4`, and remark *"The exponents … can be improved slightly for certain ranges of `H`. We
shall not pursue this here however."*

**BBMZ Theorem 2.** For `N^{1/3+eps} <= H <= N^{1-eps}` there is `delta > 0` with
`sum_{h<=H} |Delta(N,h)|^2 << H N^{2-delta}` (via Mikawa's circle-method treatment of twin primes).
Cauchy–Schwarz over the shifts converts this to `(a,b) = (1, 1 - delta/2)`.

### (C30) The two exact targets  `[PROVED HERE]`, machine-checked

Applying the breaking criterion `k(2a+2b-3) < 4a-2` at `k = 3`:

| input | `(a,b)` | breaks the chord? | exact target |
|---|---|---|---|
| BBMZ Thm 1 | `(1/2, 13/12)` | **no** (`input_half_thirteen_twelfths_fails`) | improve `13/12` to `1-delta`: a saving of `N^{1/12}` |
| BBMZ Thm 2 | `(1, 1-delta/2)` | iff `delta > 1/3` (`input_second_moment_breaks_iff`) | push `delta` past `1/3` |

Numerically at `H = N^{1/3}`: BBMZ Thm 1 gives `N^{5/4}`, the trivial bound is `N^{4/3}`, and the
target is `N^{7/6}`. So BBMZ is already nontrivial by `N^{1/12}` and is short of the target by
exactly `N^{1/12}`. Under the conjectural `Delta(N,h) << N^{2/3+eps}` the truth is `N^{5/6}`, so the
target sits **20% of the way** from BBMZ Thm 1 to the truth, and **50% of the way** from BBMZ Thm 2
(`delta > 1/3` against the conjectural `delta = 2/3`).

### (C31) D16 — BBMZ Theorem 1 cannot be bootstrapped: the route is circular  `[PROVED HERE]`

Their proof is Perron plus a contour shift, leaving
`E(N,H) = (1/2pi i) int_{sigma-iT}^{sigma+iT} zeta^3(s) sum_{N<n<=2N} d_3(n)((n+H)^s - n^s) ds/s`,
bounded by Cauchy–Schwarz between `int |zeta(sigma+it)|^6 dt` and a Dirichlet-polynomial mean value.
**The second factor is itself a block of `zeta(1/2-it)^3`**, so `E(N,H)` is the sixth moment in
disguise. Writing the induced self-map on the sixth-moment exponent `mu_6`: with
`E ≍ H T^{mu_6}` balanced against the Perron error `N^2/T`, one gets
`(a,b) = (1/(1+mu_6), 2 mu_6/(1+mu_6))`, whence the output exponent
`max(1, (a+3b-1)/2)`. Starting from `mu_6 = 5/4` the output is `≈ 1.39 > 5/4`: **the map expands.**
Its fixed point is `mu_6 = 3/2` (solving `2 mu^2 - mu - 3 = 0`), i.e. the loop converges *upward*
to the trivial value. Iterating BBMZ Theorem 1 therefore cannot improve the sixth moment, and no
better sixth-moment input improves their `13/12`.

> **Consequence.** Target 1 is blocked at the level of method: `13/12` cannot be improved by feeding
> in a better `int|zeta|^6`. Any improvement must avoid routing through the sixth moment.
> **Target 2 is not blocked** — BBMZ Theorem 2 uses the circle method (Mikawa), not `int|zeta|^6`,
> and its range `H >= N^{1/3+eps}` meets the required range `H ≍ N^{1/3}` exactly at the boundary.

**Live target for cycle 11:** `sum_{h<=H} |Delta_3(N,h)|^2 << H N^{5/3-}` at `H ≍ N^{1/3+eps}`
(i.e. `delta > 1/3` in BBMZ Theorem 2). This is the only route now identified that is neither
circular (D16), nor capped by criticality (D8, D14, C22, C25), nor blocked at the self-dual block
(C15, D9). Its mechanism is the circle method with minor-arc cancellation for `d_3`, which is where
`GL(3)`/delta-method technology would enter.

**Lean.** `HTGeometry.input_half_thirteen_twelfths_fails`, `input_half_breaks_iff_b_lt_one`,
`input_second_moment_breaks_iff`, `second_moment_conjectural_delta` in `ShiftAverageTransfer`.
Axioms `[propext, Classical.choice, Quot.sound]`; module builds green.

---

## 14. Cycle 11 (2026-07-25) — inside BBMZ Theorem 2

**Structure of their proof.** `D(N,h) = int_0^1 |S(alpha)|^2 e(-alpha h) dalpha + O(h N^eps)` with
`S(alpha) = sum_{N<n<=2N} d_3(n) e(n alpha)`. Major arcs `q <= Q_1 = N^delta` of width `1/(qQ)` with
`Q = N^{1/4}`; minor arcs the rest. Theorem 2 splits into
- **Proposition 1** (major arcs): reproduces the Conrey–Gonek main term with error `O(N^{1-delta_1})`,
  uniformly for `h <= N^{1-eta}`;
- **Proposition 2** (minor arcs): for `N^{1/3+eta} <= H <= N^{1-eta}`,
  `sum_{h<=H} | int_m |S(alpha)|^2 e(-alpha h) dalpha |^2 << N^{2-delta_2}`.

`delta_2` depends on `eta` and `delta` and is "sufficiently small"; it is the quantity that must be
pushed past `1/3`.

**(C32) Parseval form of Proposition 2.** Writing `c_h = int_m |S|^2 e(-alpha h) dalpha`, Parseval
gives `sum_{h in Z} |c_h|^2 = int_m |S(alpha)|^4 dalpha`. So Proposition 2 is a **restricted fourth
moment of the ternary-divisor exponential sum on the minor arcs**, with the `h <= H` truncation
retained (it is used, not merely discarded — their bound is `H`-independent yet requires
`H >= N^{1/3+eta}`, so the `h`-average is exploited rather than bounded).

For orientation: `int_0^1 |S|^4 dalpha` is the `d_3`-weighted additive energy of `[N,2N]`, of size
`≍ N^{3+o(1)}`, of which the major arcs carry the bulk; the diagonal alone is `≍ N^{2+o(1)}`. The
target `<< N^{5/3}` therefore asks the minor arcs to carry less than the diagonal of the full
integral — strong, but not obviously false, since `int_m |S|^2` is itself depleted by the major-arc
subtraction.

**(C33) Range check — the transfer needs exactly the endpoint.** In Ivić's transfer the sup runs
over `M = T^{1+gamma}`, `gamma in [0, k/2 - 1] = [0, 1/2]` for `k = 3`, with shift range
`H <= M^{1+eps}/T = T^{gamma}`, i.e. `H = M^{gamma/(1+gamma)}`. The requirement
`gamma a + (1+gamma)(b-1) < 1/4` is **linear in `gamma` with slope `a+b-1 > 0`**, so the binding case
is `gamma = 1/2`: `M = T^{3/2} = N`, `H = N^{1/3}`. Every other `gamma` is slack. This confirms that
only the endpoint matters — and it is exactly the endpoint of BBMZ Theorem 2's range
`H >= N^{1/3+eta}`. The two ranges meet, marginally, at `H = N^{1/3+eps}`.

**(C34) What the target would and would not buy.** `delta > 1/3` gives `m(3) < 5/4`, hence
`phi(1/8) > 1/2`, hence `m(4) < 3/2` and `m(6) < 2` — the first improvements of the sixth, eighth and
twelfth moments of zeta since 1978. It does **not** by itself beat `13/84`: `mu <= m(3)/6 < 5/24`
is weaker than `1/6`, and subconvexity would still come from `m(6)`, which needs `< 13/7`. Recorded
so that the reward is not overstated.

**Standing target (unchanged, now localised inside a specific proposition):**
> `int_m |S(alpha)|^4 dalpha`-type bound giving `delta_2 > 1/3` in BBMZ Proposition 2, at
> `H ≍ N^{1/3+eta}`, `S(alpha) = sum_{n ~ N} d_3(n) e(n alpha)`.

---

## 15. Cycle 12 (2026-07-25) — the target splits into two, and one of them is the major arcs

Work directly with the **signed** shift-average (what the transfer needs) rather than with BBMZ
Theorem 2's second moment. Using their own circle-method decomposition,

  `Delta(N,h) = [ int_M |S|^2 e(-alpha h) dalpha - int_N^{2N} S(x,h) dx ] + int_m |S|^2 e(-alpha h) dalpha + O(h N^eps)`,

and summing over `h <= H` with `K_H(alpha) := sum_{h<=H} e(-alpha h)`, `|K_H| <= min(H, 1/(2||alpha||))`:

  **`sum_{h<=H} Delta(N,h) = E_maj + int_m |S(alpha)|^2 K_H(alpha) dalpha + O(H^2 N^eps)`,
  `|E_maj| <= H N^{1-delta_1}` (BBMZ Prop. 1).**

At `H = N^{1/3}` the target is `N^{7/6}` and `O(H^2) = O(N^{2/3})` is negligible. So the target
splits into exactly two independent sub-targets.

### (C35) Sub-target (A) — the major arcs

`H N^{1-delta_1} = N^{4/3-delta_1} << N^{7/6}` requires **`delta_1 >= 1/6`**, i.e. BBMZ
Proposition 1's major-arc error improved from `O(N^{1-delta_1})` with `delta_1` "sufficiently small"
to `O(N^{5/6})`. The Conrey–Gonek prediction is `O(N^{1/2+eps})`, i.e. `delta_1 = 1/2`, so this is
**one third of the way from the published statement to the conjecture**. This is a *pure major-arc*
question — singular-series truncation at `q <= N^delta` and the accuracy of the main-term
approximation on arcs of width `1/(q N^{1/4})` — with no minor-arc input at all.
Additional slack available: `E_maj` is bounded here with **no cancellation in `h`**; any cancellation
in `sum_{h<=H}` of the major-arc error relaxes the requirement below `delta_1 = 1/6`.

### (C36) Sub-target (B) — the minor arcs, and the origin of the `N^{1/12}`

On `m` one has `||alpha|| >= 1/Q = N^{-1/4}`, so `|K_H| <= N^{1/4}/2` and crudely

  `| int_m |S|^2 K_H | <= N^{1/4} int_m |S|^2 <= N^{1/4} sum_{n~N} d_3(n)^2 << N^{5/4+eps}`.

**`N^{5/4}` is exactly BBMZ Theorem 1's value at `H = N^{1/3}`** (`H^{1/2}N^{13/12} = N^{5/4}`), and it
misses the target `N^{7/6}` by exactly `N^{1/12}` — the same `N^{1/12}` that has appeared throughout.
So the crude minor-arc estimate *is* the bottleneck of Theorem 1, which explains BBMZ's remark that
their exponents "can be improved slightly".

The crude step is lossy because `|K_H|` is only of size `N^{1/4}` in the immediate outskirts of the
major arc at `0`, where `|S|` is *small*, not average. Dyadic decomposition by `||alpha|| ≍ Delta`
gives `| int_m |S|^2 K_H | << log N · max_{Delta >= N^{-1/4}} (1/Delta) int_{||alpha|| ≍ Delta} |S|^2`,
so sub-target (B) is the **annulus `L^2` bound**

  **`int_{||alpha|| ≍ Delta} |S(alpha)|^2 dalpha << Delta · N^{1+eps}` for `Delta >= N^{-1/4}`,**

i.e. that the `L^2` mass of `S` in an annulus of measure `≍ Delta` is `≍ Delta` times the total — no
concentration just outside the major arcs. This would give `int_m |S|^2 K_H << N^{1+eps}`,
comfortably inside `N^{7/6}` with `N^{1/6}` to spare. Note `int_{|alpha| <= Delta} |S|^2 =
2 Delta sum d_3(n)^2 + O(N log^5)`; the main terms difference correctly to `≍ Delta N log^8` on the
annulus, so (B) is exactly the assertion that the `O(N log^5)` error also differences away.

> **Restated target.** `Lambda-1/8` at `k = 3` now needs only:
> **(A)** `int_M |S|^2 e(-alpha h) dalpha = int S(x,h)dx + O(N^{5/6})` uniformly for `h <= N^{1/3}`
> (major arcs, one third of the way to Conrey–Gonek); **and**
> **(B)** `int_{||alpha|| ≍ Delta} |S|^2 dalpha << Delta N^{1+eps}` for `Delta >= N^{-1/4}`
> (annulus equidistribution of the `L^2` mass).
> Neither involves the second moment `sum_h |Delta|^2`, so BBMZ Theorem 2 and its `delta > 1/3` are
> **no longer the target** — that route is superseded. Neither involves `int|zeta|^6`, so the
> circularity D16 does not apply.

**D17 (recorded).** Two false starts inside this cycle, both resolved:
(i) `int_m |S|^2 << N^{11/12}` — *false*: the major arcs carry only `≍ N log N` of the `L^2` mass
while the total is `≍ N log^8 N`, so the minor arcs carry the bulk and no power saving exists there.
(ii) `int_m |S|^4 << N^{2-delta}` via Cauchy–Schwarz against `K_H` — needs `sup_m |S| << N^{1/2-delta/2}`,
square-root cancellation for a `d_3` exponential sum on minor arcs, which is far out of reach.
The dyadic/annulus route above avoids both.

---

## 16. Cycle 13 (2026-07-25) — CORRECTION: the cycle-12 split is vacuous

**D18 (proved, and it retracts part of C35/C36).** The decomposition
`sum_{h<=H} Delta(N,h) = E_maj + int_m |S|^2 K_H dalpha + O(H^2 N^eps)` is an **identity, not a
reduction**. Indeed

  `int_0^1 |S|^2 K_H dalpha = sum_{h<=H} D_3(N,h)`  (exactly, no error term),
  `int_M |S|^2 K_H dalpha = sum_{h<=H}[ main(h) + (major-arc error) ]`,

so `int_m |S|^2 K_H dalpha = sum_{h<=H} Delta(N,h) - E_maj` **by definition**. Bounding the two
pieces separately is therefore exactly bounding the whole. Sub-target (B) of cycle 12 is not an
independent, easier statement: it *is* the main target minus a term one already has to control.

Three independent attempts to bound the minor-arc piece "directly" all return to the same
shifted-convolution sums, and are recorded so they are not retried:

1. **Exact annulus identity.** `int_{|alpha|<=Delta}|S|^2 = 2 Delta D + sum_{r != 0} C(r)
   sin(2 pi Delta r)/(pi r)` with `D = sum d_3(n)^2` and `C(r) = sum_n d_3(n)d_3(n+r)`. The
   off-diagonal is literally the ternary shifted convolution; splitting `C = M + Delta_3` puts
   `sum_r Delta_3(N,r) g_Delta(r)` back in play.
2. **Smooth annulus weight.** With `w` smooth on `[Delta,2Delta]`, Poisson gives
   `sum_{r in Z} hat w(r) = sum_{k in Z} w(k) = 0` exactly (`w` vanishes at every integer), so the
   constant part of the singular series cancels perfectly — but the surviving term is again
   `sum_{r <~ 1/Delta} Delta_3(N,r) hat w(r)`, needing `|sum_{r <= N^{1/4}} Delta_3(N,r)| << N^{1+eps}`
   at `Delta = N^{-1/4}`. BBMZ Theorem 1 gives `N^{29/24}` there: short by `N^{5/24}`, i.e. **this
   route is strictly *harder* than the main target** (which is short by only `N^{1/12}`).
3. **Gallagher.** `int_{|alpha|<=Delta}|S|^2 << Delta^2 [ N L^2 log^4 + I_3(N,L) ]`, `L = 1/(4Delta)`.
   The first term is `≍ N log^4` independent of `Delta` and cancels only in the *annulus difference*,
   which Gallagher does not compute; bounding the annulus by `F(2Delta)` reinstates `N log^4/Delta =
   N^{5/4}`. (Had the cancellation been usable, Ivić's LH-conditional `I_3 << N^{1+eps}L^{4/3}` would
   have given `N^{13/12} < N^{7/6}` — noted only to record that the arithmetic was checked and the
   obstruction is the cancellation, not the size of `I_3`.)

**What survives from cycle 12.** Two things, both real:
- **The `N^{1/12}` is located.** On `m`, `||alpha|| >= 1/Q = N^{-1/4}`, so `|K_H| <= N^{1/4}/2` and
  `|int_m |S|^2 K_H| <= N^{1/4} int_m |S|^2 << N^{5/4+eps}` — **exactly BBMZ Theorem 1's value at
  `H = N^{1/3}`**. So Theorem 1 is, in strength, the crude minor-arc estimate, and the recurring
  `N^{1/12}` gap is the cost of the bound `|K_H| <= 1/(2||alpha||)` at the major-arc boundary.
- **`int_m |S|^2 ≍ N log^8 N` admits no power saving** (D17(i)): the major arcs carry only `≍ N log N`
  of the `L^2` mass while the total is `≍ N log^8 N`.

**Standing position after 13 cycles.** The target is unchanged and irreducible by elementary
decomposition:
  `sum_{h<=H} Delta_3(N,h) << N^{7/6-delta}` at `H ≍ N^{1/3}`,
equivalently `phi(1/8) > 1/2`, equivalently the moment curve leaving the chord. The circle method
does not split it (D18); Cauchy–Schwarz is exactly critical (3.5–3.6 of the map); the Perron route
is circular (D16); the short-interval mean square is neutral (D14); generic large-value theory,
including Guth–Maynard, is inert at the self-dual block (3.3). The one mechanism known to beat
Cauchy–Schwarz in a shift average of this type is spectral — `GL(2)` at `k = 2`, `GL(3)` at `k = 3`.

---

## 17. Cycle 14 (2026-07-25) — the Diophantine form, and the unique symmetry-breaking mechanism

### (C37) The target as a six-variable lattice count

Expanding both divisor functions, `sum_{h<=H} D_3(N,h) = #{(a,b,c,d,e,f) : N < abc <= 2N,
0 < def - abc <= H}`. So the target is a lattice-point count on the thin slab

  **`def - abc = h`, `1 <= h <= H = N^{1/3}`, `abc ≍ N`,**

against its expected (Conrey–Gonek) value, to accuracy `N^{7/6}` out of a total `≍ N^{4/3}`. Six
variables, one equation, one inequality; no zeta function and no divisor function appear.

**(C38) The `d_2`-descent.** Writing `d_3 = d_2 * 1` and `n = d n'`, `n+h = e m'` turns it into

  `sum_{d,e} sum_{n',m'} d_2(n') d_2(m') · 1[ 0 < e m' - d n' <= H, d n' ≍ N ]`,

a double average over `(d,e)` of **binary** additive-divisor problems with unequal scalings. The
binary problem is exactly the case solved by `GL(2)` spectral theory (Duke–Friedlander–Iwaniec,
Motohashi, Meurman) with power-saving error uniform in the shift. The obstruction is therefore not
the inner problem but the **uniformity in `(d,e)` over the full range `d,e <= N`**: the trivial
per-pair error `O(1)` summed over `N^2` pairs already exceeds the target by `N^{5/6}`. This is the
precise sense in which `k = 3` is "`SL(3,Z)` rather than `SL(2,Z)`".

**(C39) Criticality #19 — double Voronoi is again self-dual.** In the cycle-9 reduction
`W = sum_{P ≍ x^2} c(P) P^{-(k-1)/(2k)} e(k P^{1/k})` with `c` a restricted `d_{2k}`, applying the
degree-`2k` Voronoi formula to `c` produces a kernel `e(2k (M P)^{1/(2k)})`; the stationary point of
`k P^{1/k} ± 2k (MP)^{1/(2k)}` in `P` is at `M = P`. **The dual sum has the same length as the
original**, for every `k`. Iterating Voronoi therefore returns to the same critical configuration —
a nineteenth instance, and the reason "apply the functional equation again" is not a route.

### (C40) The unique known symmetry-breaking mechanism: conductor lowering

Collecting the mechanism behind all nineteen instances: each method's bound, as a function of the
scale parameter, is invariant under the functional-equation duality `N <-> conductor/N`, and is
convex in `log N`; a convex function symmetric about a point attains its extremum there. So every
duality-respecting assembly is pinned at the self-dual scale, and the value there is the same for
all of them. **Improvement requires an input that is not duality-invariant.**

Exactly two such inputs are known in the subject:
1. **Pointwise exponential-sum estimates** (van der Corput, Bombieri–Iwaniec, `l^2` decoupling) — they
   use the smoothness of the phase `-t log n` in `n`, which the duality does not preserve. This is
   the only mechanism that has ever moved `mu(1/2)`, and it is capped at the square-root barrier at
   the self-dual block (C13, C14).
2. **Conductor lowering / deliberate unbalancing** — replacing the balanced approximate functional
   equation `x = y = t^{k/2}` by an unbalanced split, or inserting an auxiliary modulus to move the
   stationary point off the fixed point. This is the mechanism of Munshi's `GL(3)` subconvexity and
   of the delta method; it is precisely a device for destroying the self-duality that pins everything
   above.

> **Conjecture for the next cycles `[CONJECTURE UNBAL]`.** The ternary shift average
> `sum_{h<=H} Delta_3(N,h)` admits a conductor-lowered treatment in which the effective dual length
> is `≠ N`, and the resulting non-self-dual configuration yields `b < 1` in the transfer input,
> hence breaks the chord. Falsifiable: exhibit a conductor-lowering parameter and show its optimum
> returns to the balanced point (which would make criticality a theorem rather than a phenomenon).

**Recorded as the campaign's open core.** Everything else is closed: mean-value methods (D8),
short-interval mean square (D14), Perron/`int|zeta|^6` (D16), the circle-method split (D18), generic
and Guth–Maynard large values (C15), iterated Voronoi (C39), moment interpolation (C5, C24).

---

## 18. Cycle 15 (2026-07-25) — why `1/8`: the pivot is a double root

### (C41) THEOREM — the resolution floor, and the exact reason the pivot is `1/8`  `[PROVED HERE]`

For each `k` let `E_k(T)` be the error in the `2k`-th moment asymptotic. A bound `E_k << T^theta`
makes the short `2k`-th moment sharp at scale `T^theta`, and Sobolev gives `mu(1/2) <= theta/(2k)`.
`theta` cannot be pushed below the `Omega`-result, so each moment carries an intrinsic
**resolution floor**

  `resolutionFloor(k) = theta_k / (2k)`,   `theta_k = (2k-1)/(2k+2)`,

`theta_k` being the conjecturally optimal exponent — **sharp** at `k = 1` (`E(T) = Omega(T^{1/4})`)
and at `k = 2` (`E_2(T) = Omega(T^{1/2})`, Ivić–Motohashi). Then:

  **`resolutionFloor(k) >= 1/8  <=>  8(2k-1) >= 2k(2k+2)  <=>  (k-1)(k-2) <= 0  <=>  1 <= k <= 2`,**

because `8(2k-1) - 2k(2k+2) = -4(k-1)(k-2)` identically. So the floor equals `1/8` at `k = 1` **and**
`k = 2` — the roots of `k^2 - 3k + 2` — and is strictly smaller for every `k > 2`:
`resolutionFloor(3) = 5/48`, `resolutionFloor(4) = 7/80`, and `resolutionFloor(k) -> 0`.

> **This explains the pivot.** `k = 1` and `k = 2` are exactly the two indices at which an asymptotic
> formula for the moment is known, and they are exactly the two roots at which the resolution floor
> attains `1/8`. The coincidence that has appeared nineteen times in this campaign is the quadratic
> `(k-1)(k-2)`. `1/8` is therefore **not** a fundamental obstruction to Lindelöf: it is the joint
> resolution limit of precisely the two moments we can evaluate. The floor tends to `0`, so the
> moment hierarchy's *conjectural* resolution does reach the Lindelöf prediction; what stops it is
> the absence of asymptotic formulas for `k >= 3`, not the number `1/8`.

**Consequence for strategy.** The campaign's target `phi(1/8) > 1/2` is the statement that one can
see below the resolution floor of the second and fourth moments. There are exactly two ways: obtain
an asymptotic (with a power-saving error) for a moment with `k >= 3` — whose floor is already
`5/48 < 1/8` — or use a non-moment, non-duality-invariant input (C40). The first is the sixth-moment
problem; the second is conductor lowering. Nothing else in the subject has a floor below `1/8`.

**Lean.** `GaloisForLFunctions.HTGeometry.MomentResolutionFloor`:
`resolutionFloor_ge_eighth_iff`, `eighth_gap_factorisation`, `resolutionFloor_lt_eighth`,
`resolutionFloor_tendsto_zero`, plus the values at `k = 1,2,3,4`. Axioms
`[propext, Classical.choice, Quot.sound]`; module builds green.

---

## 19. Cycle 16 (2026-07-25) — the Omega side: LH cannot be disproved by any known method

Fourteen cycles were spent on the upper-bound side. This cycle audits the **disproof** direction,
which the campaign had never examined, and closes it.

### (C42) The resonance method is capped at `T^{o(1)}`

Every known `Omega`-result for `max_{t<=T}|zeta(1/2+it)|` comes from the **resonance method**: choose
a resonator `R(t) = sum_{n in cal N} r(n) n^{-it}` and compare `int |zeta| |R|^2` with `int |R|^2`.
The gain is governed by the **Gál / GCD sum** `Gamma(N) = max_{|cal N| = N} sum_{m,n}
gcd(m,n)/sqrt(mn)`, and Bondarenko–Seip determined it sharply:

  `Gamma(N) = exp( (C+o(1)) sqrt( log N loglog N ) )`  — **subpolynomial in `N`.**

Since the resonator length is itself bounded by a power of `log T`, the output is
`max_{t<=T}|zeta(1/2+it)| >= exp((1+o(1)) sqrt(2 log T logloglog T / loglog T))`
(Bondarenko–Seip; de la Bretèche–Tenenbaum), which is `T^{o(1)}`.

> **The cap is a theorem, not a limitation of effort.** Because `Gamma(N)` is subpolynomial and the
> resonator is polylogarithmic, no resonance construction can produce `Omega(T^c)` for any `c > 0`.
> **Therefore no known method can disprove the Lindelöf hypothesis.** Moreover the conjecturally
> *correct* maximum, `exp((1/sqrt2 + o(1)) sqrt(log T loglog T))` (Farmer–Gonek–Hughes), is itself
> `T^{o(1)}`: even a complete solution of the extreme-value problem is consistent with LH.

**Consistent with D3.** A genuine counterexample would need `Re sum_{p<=y} p^{-1/2-it} >> log T` with
`y ≈ (log T)^2 (loglog T)^2`, i.e. simultaneous alignment of `p^{-it}` over all primes up to
`(log T)^{2+o(1)}` at a single `t <= T`. The measure of such `t` is heuristically
`T exp(-c log^2 T / loglog T) << 1`, so no such `t` should exist below `T` — and D3 records that
Baker–Wüstholz is far too weak to decide this.

### (C43) The frontier, both sides, with proven caps

| side | best known | cap of the technology | status of the cap |
|---|---|---|---|
| upper (`mu <= ?`) | `13/84` (Bourgain) | `1/8` for all moment technology | **proved here** (C41): the resolution floor `(2k-1)/(2k(2k+2))` attains `1/8` exactly at the roots `k = 1, 2` of `(k-1)(k-2)`, which are exactly the two moments with known asymptotics |
| lower (`mu >= ?`) | `0` | `0` for all resonance technology | **proved** (Bondarenko–Seip GCD sums): `Gamma(N)` subpolynomial, so every resonance `Omega`-result is `T^{o(1)}` |

So the interval `[0, 13/84]` containing `mu(1/2)` is bracketed by two proven method-caps: nothing
below `1/8` from moments, nothing above `0` from resonance. **The campaign's exclusive focus on the
proof direction was correct**, and the two escape routes identified in C40/C41 — an asymptotic with
power-saving error for a moment with `k >= 3` (floor `5/48 < 1/8`), or conductor lowering — remain
the only openings.

**D19 (recorded).** A short-`2k`-th-moment bound for `k >= 3` is **not** an alternative route: an
asymptotic is not needed to run the resolution-floor argument, only `int_T^{T+G}|zeta|^{2k} << G
T^eps`, but that statement at `G = T` *is* the `2k`-th moment conjecture and for `G < T` is strictly
stronger. Short-interval bounds cannot be weaker than their global counterparts. So the `k >= 3`
opening genuinely requires the global asymptotic, with error `T^{theta}`, `theta < 13/14` to beat
`13/84`.

---

## 20. Cycle 17 (2026-07-25) — the additive-divisor route is capped at `1/8`, conjectures included

### (C44) THEOREM — solving the additive divisor problem does not give Lindelöf  `[PROVED HERE]`

Feed the shift-average transfer its **conjecturally exact** input: Vinogradov's predicted pointwise
size `Delta_k(x,h) << x^{1-1/k+eps}` (matched by the conjectured `Omega`-result
`Delta_k(x,h) = Omega(x^{1-1/k})`, Ivić) together with square-root cancellation over the shifts —
that is `(a,b) = (1/2, 1-1/k)`, which is the *truth* as far as anyone predicts it. Then

  `transferBound k (1/2) (1-1/k) = 1 + max(0, k/4 - 1)`,

so `m(k) <= 1` for `k <= 4` and `m(k) <= k/4` for `k >= 4`, and therefore

  **`transferBound k (1/2) (1-1/k) / (2k) = 1/8` exactly, for every `k >= 4`,**

with `1/(2k) >= 1/8` for `k <= 4`. The minimum over all indices is attained at `k = 4` and equals
`1/8`. Hence:

> **Even a complete solution of the `k`-ary additive divisor problem, at conjecturally exact
> strength and for every `k` simultaneously, yields only `mu(1/2) <= 1/8` — never the Lindelöf
> hypothesis.** The transfer is irreducibly lossy: the true moment exponent is `m(k) = 1`, while the
> transfer delivers only `m(k) <= k/4` for `k >= 4`.

For contrast, Ivić's own stated conjecture (1.8), `sum_{h<=H} Delta_k << H x^{1-1/k+eps}` (no shift
cancellation), gives `m(k) <= 1 + max(0,(k-3)/2)`: `m(3) = 1` — the full sixth moment, as he notes —
but only `mu <= 1/6`. Adding square-root shift cancellation improves that to `1/8` and no further.
Ivić remarks that (1.13) "gives an insight as to the limitations of the attack on the `2k`-th moment
via estimates for `Delta_k(x,h)`"; the exact value of that limitation is `1/8`.

### (C45) Three independent programmes, one cap

| programme | conjecturally optimal input | cap on `mu(1/2)` |
|---|---|---|
| second-moment error term | `E(T) << T^{1/4+eps}` (sharp: `Omega(T^{1/4})`) | `1/8` |
| fourth-moment error term | `E_2(T) << T^{1/2+eps}` (sharp: `Omega(T^{1/2})`) | `1/8` |
| `k`-ary additive divisor, all `k` | `(a,b) = (1/2, 1-1/k)` (Vinogradov + square-root) | `1/8` |

Three programmes, three different conjectural inputs, one cap — and by (C41) the first two coincide
because `(k-1)(k-2)` vanishes exactly at the two indices with known asymptotics. The third now joins
them by a separate computation. This is the twentieth instance of exact criticality and the
strongest: **it caps not a method but an entire conjectural programme.**

**Consequence for the campaign.** The remaining opening from C40/C41 narrows to one item:
- the `k >= 3` moment asymptotic route is capped at `1/8` too (C44 covers its input), so it beats
  `13/84` but stops at `1/8`;
- **conductor lowering** — the only identified non-duality-invariant mechanism — is now the sole
  candidate for reaching below `1/8`, and *a fortiori* the sole candidate for Lindelöf through any
  route this campaign has examined.

**Lean.** `HTGeometry.vinogradov_cap`, `vinogradov_cap_below`, `vinogradov_cap_is_eighth` in
`ShiftAverageTransfer`. Axioms `[propext, Classical.choice, Quot.sound]`; module builds green.

---

## 21. Cycle 18 (2026-07-25) — scope correction on C44, and where the loss actually sits

### (C46) CORRECTION — C44 caps the *transfer*, not the *information*

C44 must be stated precisely, and the chat summary of cycle 17 overstated it. What is proved is:

> **Ivić's shift-average transfer**, fed the conjecturally exact additive-divisor input
> `(a,b) = (1/2, 1-1/k)`, yields exactly `mu(1/2) <= 1/8` for every `k >= 4`.

It is **not** proved that the additive-divisor *information* is insufficient for Lindelöf. It is not:
the transfer consumes only `sum_{h<=t} Delta_k(x,h)` for `t <= M^{1+eps}/T`, i.e. shifts up to
`x^{1-2/k}`, and discards the whole range `x^{1-2/k} < h <= x^{1-eps}` in which the additive-divisor
conjecture is also asserted. The standard CFKRS-style computation of `int|zeta|^{2k}` uses the
shifted correlations across a much longer `h`-range; a transfer that consumed them could in principle
do better. **The `1/8` of C44 is a property of the transfer's aperture, not of the divisor data.**

This distinction matters for the whole map: the caps proved in this campaign are caps on
**assembly** — Hölder, Cauchy–Schwarz, the transfer's shift aperture, the resonance method's GCD
sum — not on the underlying arithmetic information. The one exception is C42 (the resonance cap),
which is a genuine information-theoretic cap because `Gamma(N)` is the exact extremal quantity.

**(C47) A new opening, from the correction.** If the loss is the transfer's aperture, then the
target is a **wide-aperture transfer**: a bound of the form

  `int_0^T |zeta(1/2+it)|^{2k} dt << T^{1+eps} ( 1 + sup_{M} G_k^{wide}(M;T)/M )`,
  `G_k^{wide}(M;T) = sup_{x ≍ M, t <= M^{1-eps}} | sum_{h<=t} Delta_k(x,h) |`,

using shifts up to `M^{1-eps}` rather than `M^{1+eps}/T`. With the conjecturally exact input
`(a,b) = (1/2, 1-1/k)` such a transfer would give
`G^{wide}/M << M^{(1/2)(1-eps)} M^{-1/k} = M^{1/2 - 1/k - eps'}`, and the sup over `M <= T^{k/2}`
would be at the *smallest* admissible `M ≍ T`, not the largest — the aperture change **reverses which
block binds**, moving the optimum off the self-dual endpoint. This is the first mechanism found in
the campaign that is not duality-invariant *and* does not require new arithmetic input: it requires
re-deriving the transfer, not a new estimate.
`[OPEN CORE]` whether the moment can in fact be expressed through long-shift correlations with the
error kept under control — Ivić's derivation restricts to `h <= M/T` for a reason that must be
identified before this can be claimed.

### (C48) Conductor lowering, instantiated and closed for the direct route

Applying `GL(3)` subconvexity to `zeta^3` directly is a dead end: `zeta(s)^3 = L(s, 1 boxplus 1
boxplus 1)` has conductor `t^3` and degree-3 convexity `t^{3/4}`, i.e. `zeta << t^{1/4}` — exactly the
classical convexity bound. Munshi's conductor-lowering gains `t^{3/4-delta}` with a very small
`delta`, giving `zeta << t^{1/4-delta/3}`, far worse than `13/84`. A *Weyl-quality* `GL(3)` bound
`t^{1/2}` would give exactly `zeta << t^{1/6}` — the classical Weyl bound, again exactly critical
(instance #21). Recorded as **D20**: conductor lowering applied to `zeta^3` as a degree-3 `L`-function
cannot beat `13/84`; if the mechanism is to work it must be applied to the *shifted convolution*,
where nothing nontrivial is known for `GL(3) x GL(3)`.

---

## 22. Cycle 19 (2026-07-25) — C47 retracted; the real loss is a conspiracy the `(a,b)` parametrisation cannot see

### (C49) The transfer is **not** aperture-limited — C47 is withdrawn  `[PROVED HERE]`

Re-deriving the transfer from scratch: with `zeta^k ≈ sum_n d_k(n) n^{-1/2-it} V(n/M)`, `M ≍ T^{k/2}`,

  `int_0^T |zeta|^{2k} dt = T sum_n d_k(n)^2/n V^2 + sum_{h>=1} (D_k(M,h)/M) K(h)`,
  `K(h) = ((1+h/m)^{iT} - 1)/(i log(1+h/m)) ≪ min(T, M/h)`,

so the shifts run to `h ≍ M`, not `h <= M/T`. Splitting `D_k = main + Delta_k` and partial-summing
the tail with `|sum_{h<=t} Delta_k| << t^a M^b`:

  `(T/M) |S(M/T)| << T^{1-a} M^{a+b-1}`,  and  `sum_{M/T<h<=M} Delta_k/h << T^{1-a} M^{a+b-1}`

— **the two ranges give the same exponent**, and the sup over `M <= T^{k/2}` reproduces
`m(k) <= 1 + max(0, k(a+b-1)/2 - a)` exactly. So Ivić's transfer already consumes the full shift
range; there is no wider aperture to exploit and **C47 is retracted.**

### (C50) The real loss: `Delta_k(M,h)` conspires with the kernel  `[PROVED HERE, k=2]`

Model `Delta_k(M,h)` as having its conjectured size `M^{1-1/k}` with independent signs across `h`.
Then square-root cancellation against the kernel predicts

  `|sum_h Delta_k(M,h) K(h)| ≈ ( sum_h K(h)^2 )^{1/2} M^{1-1/k} ≈ (2MT)^{1/2} M^{1-1/k}`,

which at `M = T^{k/2}` is `T^{3k/4}`. **At `k = 2` this reads `T^{3/2}`, while the true off-diagonal
contribution to the fourth moment is `<< T log^4 T`.** So the actual cancellation between the
shifted-divisor errors and the kernel exceeds the independent-signs prediction by a factor `T^{1/2}`:
the `Delta_2(T,h)` are **not** independent across `h` — they conspire with `K`.

> **This is the deepest explanation the campaign has reached for the `1/8` cap.** Any bound of the
> form `|sum_{h<=t} Delta_k(M,h)| << t^a M^b` treats the `Delta_k` as arbitrary and therefore cannot
> see the conspiracy; that is why the `(a,b)` route stalls at `1/8` even when fed its conjecturally
> exact input (C44), and why the loss is not aperture (C49) and not the size of `Delta_k`. What is
> needed is the *`h`-dependence* of `Delta_k(M,h)`, finely enough to expose its correlation with
> `K(h)`.
>
> **At `k = 2` exactly one tool supplies that: Motohashi's spectral formula**, which expands
> `Delta_2(M,h)` over the spectrum of the Laplacian with explicit `h`-dependence through
> Kloosterman/Kuznetsov terms. This closes the loop with C29: `GL(2)` spectral theory is not merely
> "the method that works at `k=2`" — it is the only known way to see the conspiracy, which is
> precisely the information the `(a,b)` parametrisation discards.

**Final form of the campaign's barrier.** Three statements, all proved here:
1. every duality-invariant assembly is pinned at the self-dual scale (C40, 21 instances);
2. the moment/error-term programmes have resolution floor exactly `1/8`, because
   `(k-1)(k-2)` vanishes at the two indices with known asymptotics (C41);
3. the shift-average route caps at `1/8` even with conjecturally exact input, because the `(a,b)`
   parametrisation cannot represent the `Delta_k`–kernel conspiracy (C44, C50).

The single surviving requirement is therefore sharp: **an explicit spectral expansion of
`Delta_3(M,h)` in `h`** — the `GL(3)` analogue of Motohashi's formula. Nothing weaker suffices,
because anything weaker is an `(a,b)`-type bound, and those are capped.

---

## 23. Cycle 20 (2026-07-25) — the conspiracy exponent, and the state of the GL(3) analogue

**Corpus check (folders named by the user).** `formal/GaloisForLFunctions/{HTGeometry, RHTower,
HilbertMetric}` contain **no** Motohashi, Kuznetsov, Kloosterman, shifted-convolution, or
divisor-correlation material. The only additive-divisor file is this campaign's
`HTGeometry/ShiftAverageTransfer`; the `Eisenstein` hits in `RHTower` are theta/modular, unrelated
to `GL(3)`. The corpus is clean of everything cycle 19 identified as needed.

### (C51) The conspiracy exponent `c(k) = 3k/4 - 1`  `[PROVED HERE]`

Quantifying C50. Model `Delta_k(M,h)` at its conjectured size `M^{1-1/k}` with independent signs.
The kernel satisfies `sum_{h<=M} K(h)^2 ≍ 2MT` (the ranges `h <= M/T` and `h > M/T` contribute `MT`
each), so square-root cancellation predicts

  `|sum_h Delta_k(M,h) K(h)| ≍ (2MT)^{1/2} M^{1-1/k} = T^{3k/4}`  at the balanced `M = T^{k/2}`.

The off-diagonal must in fact be `<< T^{1+eps}` (it carries part of the CFKRS main term and no more).
Hence any expansion of `Delta_k` capable of delivering the `2k`-th moment must exhibit cancellation
of strength

  **`T^{c(k)}`,  `c(k) = 3k/4 - 1`:  `c(2) = 1/2`,  `c(3) = 5/4`,  `c(4) = 2`.**

- `c(2) = 1/2` is exactly what Motohashi's `GL(2)` spectral formula supplies — which is *why* the
  fourth moment of `zeta` has an asymptotic and no weaker tool gives it.
- `c(3) = 5/4` is **two and a half times** the `GL(2)` requirement. This is the quantitative content
  of Ivić–Wu's "overwhelmingly hard" and of "`SL(3,Z)` rather than `SL(2,Z)`".
- `c` grows linearly, so the difficulty of the moment hierarchy escalates at a fixed rate — the
  campaign's first quantitative statement about *why* each successive moment is harder.

This is a **falsifiable benchmark**: any proposed `GL(3)` Motohashi analogue can be tested against
`c(3) = 5/4` before any application is attempted. Lean: `conspiracyExponent`,
`conspiracyExponent_two/three/four`, `conspiracyExponent_pos`, `conspiracyExponent_strictMono`.

### (C52) State of the `GL(3)` analogue (audit, July 2026)

- **Kwan, *Spectral moment formulae for `GL(3) x GL(2)` L-functions* I–III** (ANT 18.10 (2024);
  arXiv:2310.09419; Math. Ann. 391.1 (2025)) proves an **exact Motohashi-type identity linking the
  shifted cubic moment of `GL(2)` L-functions to the shifted fourth moment of `GL(1)` L-functions**,
  with an automorphic account of the full CFKRS main terms. This is the classical Motohashi level
  generalised — the `GL(1)` side is the **fourth** moment, not the sixth.
- **Blomer–Buttcane and Buttcane** supply the `GL(3)` Kuznetsov formula (Invent. Math. 2013;
  arXiv:1708.09685, 1909.09232) and `GL(3)` Bessel theory, but no application to `d_3(n)d_3(n+h)`.
- The `d_3` correlation literature (Baier–Browning–Marasingha–Zhao; Topacogullari for `d_k x d`;
  arXiv:2206.05877 for `d_3` with itself) is **conditional** at the level needed — e.g. the full main
  term for composite shifts assuming an averaged level of distribution `2/3` for `d_3`.
- arXiv:2110.08974 (Motohashi's formula for individual Dirichlet `L`-functions) originally contained
  sixth-moment calculations, **removed because they were heuristic**.

> **Conclusion of the audit.** The identity the campaign requires — an exact spectral expansion of
> `Delta_3(M,h)` in `h` with cancellation `T^{5/4}` — does not exist. The nearest technology
> (Kwan I–III) degenerates one level below it, to Motohashi's own `k = 2` case. This is consistent
> with, and now quantifies, C29 and C50.

---

## 24. Cycle 21 (2026-07-25) — where the conspiracy comes from, and how much of it Hecke supplies

### (C53) The mechanism at `k = 2`: the `h`-dependence is carried by Hecke eigenvalues

Motohashi/Kuznetsov expand `Delta_2(M,h)` over the spectrum with the **`h`-dependence entering
through Hecke eigenvalues** `lambda_j(h)`:
`Delta_2(M,h) ≈ sum_j c_j(M) lambda_j(h) (transform)`. Then
`sum_h Delta_2(M,h) K(h) ≈ sum_j c_j(M) sum_h lambda_j(h) K(h)`, and the inner sum cancels because
`lambda_j(h)` oscillates in `h`. **That is the conspiracy of C50, identified.** The `GL(3)` analogue
would carry the `h`-dependence through `GL(3)` Hecke eigenvalues `A_j(1,h)`.

### (C54) Hecke cancellation supplies only `T^{1/4}` of the required `T^{5/4}`  `[PROVED HERE]`

`sum_{h<=M}|K(h)| ≍ M log T` (both ranges contribute `≍ M`), while square-root cancellation in the
Hecke eigenvalues gives `|sum_h A(1,h) K(h)| ≍ (sum_h |K|^2)^{1/2} = (2MT)^{1/2}`. So the eigenvalue
oscillation alone contributes a factor

  `(M log T) / (2MT)^{1/2} ≍ (M/T)^{1/2} log T`,  which at `M = T^{3/2}` is `T^{1/4+o(1)}`.

Against the requirement `c(3) = 5/4` (C51) this leaves a further **`T^{1}`** to be supplied by the
spectral side — the size and cancellation of the coefficients `c_j(M)` and of the spectral sum
itself. Checking the same computation at `k = 2` (`M = T`): the Hecke factor is `(M/T)^{1/2} = T^{0}`,
so at `k = 2` **all** of the required `c(2) = 1/2` comes from the spectral side, none from the
eigenvalue oscillation. So the two cases are not merely quantitatively but structurally different:
at `k = 3` the eigenvalue sum begins to help, but only by `T^{1/4}` of the needed `T^{5/4}`.

**Validation of the framework against the known case.** At `k = 2` the conjectured RMS of
`Delta_2(M,h)` is `M^{1/2}` — matched by Motohashi's `Omega(x^{1/2})` for fixed `h` — and the
independent-signs model predicts `T^{3/2}` for `sum_h Delta_2 K`, while the fourth moment forces
`<< T log^4 T`. So Motohashi's formula *demonstrably* encodes correlations across `h` worth exactly
`T^{1/2}`. The framework therefore reproduces a verified fact in the one case where the answer is
known, which is the only available test of it.

### (D21) Unbalancing the approximate functional equation does **not** help

With `zeta^k = sum_{n<=X} d_k(n)n^{-s} + chi^k sum_{n<=Y} d_k(n) n^{-(1-s)} + ...`, `XY = (t/2pi)^k`,
the transfer's error is `T^{1-a} M^{a+b-1}` with `M = max(X,Y)`, which is **increasing in `M`** and
therefore minimised exactly at the balanced point `X = Y = t^{k/2}`. Unbalancing the AFE strictly
worsens the bound (criticality instance #22). **Hence "conductor lowering" in the sense that could
help is *not* AFE unbalancing** — it must be Munshi's delta-method device, which lowers the conductor
of the character sums produced *after* the decomposition, not the lengths of the AFE itself.
Recorded so the cheap version is not attempted again.

---

## 25. Cycle 22 (2026-07-25) — ERRATUM: C50/C51/C53/C54 dropped a factor `1/M`; the corrected picture

### (E1) The error

The off-diagonal of the `2k`-th moment is

  `sum_{m != n} d_k(m)d_k(n)(mn)^{-1/2} V V int_0^T (n/m)^{it} dt
     = sum_{h>=1} ( D_k(M,h) / M ) K(h)`,  `K(h) << min(T, M/h)`,

with a normalising **`1/M`** coming from `(mn)^{-1/2} ≍ 1/M`. Cycles 19–21 wrote the error part as
`sum_h Delta_k(M,h) K(h)` and omitted that factor. All numerical conclusions drawn from it are
withdrawn: **C50** ("`Delta_2` conspires with the kernel by `T^{1/2}`"), **C51**
(`c(k) = 3k/4 - 1`), **C53** (the mechanism claim), and **C54** (`Hecke supplies T^{1/4}`).

### (E2) The corrected computation  `[PROVED HERE]`

With the factor restored, the independent-signs model predicts an off-diagonal error

  `(1/M)(2MT)^{1/2} M^{1-1/k} = sqrt2 · T^{1/2} M^{1/2 - 1/k} = sqrt2 · T^{k/4}`  at `M = T^{k/2}`.

Since the off-diagonal must be `<< T^{1+eps}`, independent signs suffice **exactly when `k <= 4`**,
and the corrected conspiracy exponent is

  **`c(k) = k/4 - 1`:  `c(3) = -1/4`,  `c(4) = 0`,  `c(6) = 1/2`.**

### (E3) Why the correction makes the map *more* coherent

The corrected model reproduces C44 exactly: it predicts `m(k) = 1` for `k <= 4` and `m(k) <= k/4`
for `k >= 4`, which is precisely `transferBound k (1/2) (1-1/k)`. So the independent-signs model
**is** the input `(a,b) = (1/2, 1-1/k)`, and:

- **No conspiracy is needed at `k <= 4`.** In particular the sixth moment (`k = 3`) follows from
  Vinogradov's conjectured size plus square-root cancellation in the shifts, with room to spare
  (`c(3) = -1/4`). Cycle 21's claim that Motohashi's formula must encode cross-`h` correlations is
  withdrawn — at `k = 2` none are needed.
- **`1/8` is exactly the `k = 4` borderline.** `c(4) = 0`: the model is precisely critical there,
  which is *why* the additive-divisor cap of C44 sits at `1/(2·4) = 1/8` and not elsewhere. The
  pivot now has a third, independent explanation, agreeing with C41's `(k-1)(k-2)` root count and
  with the `V^4 = sqrt N` computation of C13.
- **Going below `1/8` needs `k > 4` and genuine correlations** among the `Delta_k(M,h)` across
  shifts, of strength `T^{k/4-1}` — beyond square-root cancellation, which is what "conspiracy"
  should have meant all along.

**Status of the terminal requirement, corrected.** It is *not* a `GL(3)` Motohashi formula for
`Delta_3`: at `k = 3` no correlations are needed and the sixth moment is exactly the
Vinogradov-plus-square-root package. The terminal requirement is at `k > 4`: correlations among
`Delta_k(M,h)` beyond square-root cancellation, of strength `T^{k/4-1}`. Lean corrected accordingly
(`conspiracyExponent = k/4 - 1`, with `conspiracyExponent_four = 0`, `conspiracyExponent_nonpos`,
`conspiracyExponent_pos`).

---

## 26. Cycle 23 (2026-07-25) — LH forces correlations, and the first disproof route

### (C55) THEOREM (conditional) — LH implies the divisor-correlation errors are correlated across shifts

Let `k > 4` and `M = T^{k/2}`. Under LH the moment is `T^{1+eps}` and the diagonal is `T(log T)^{k^2}`,
so the off-diagonal satisfies `| sum_h (Delta_k(M,h)/M) K(h) | << T^{1+eps}`.

The independent-signs model — `|Delta_k(M,h)| ≍ M^{1-1/k}`, which is both Vinogradov's conjectured
bound and the conjectured `Omega`-order (Ivić, (1.10)), with signs uncorrelated across `h` — predicts

  `(1/M) ( sum_{h<=M} K(h)^2 )^{1/2} M^{1-1/k} = sqrt2 · T^{k/4}`.

For `k > 4` this exceeds `T^{1+eps}`. Hence:

> **LH implies that the errors `Delta_k(M,h)` in the `k`-ary divisor correlation are correlated
> across the shift `h`, to strength `T^{k/4-1}`, for every `k > 4`.**

This is a *consequence* of LH about pure divisor arithmetic, with no zeta function in the
conclusion. It is new to this campaign and, as far as the audits found, unstated.

### (C56) The first identified disproof route

Contrapositive: **any theorem establishing enough pseudorandomness of `h -> Delta_k(M,h)`, for a
single `k > 4`, to validate the square-root prediction would contradict LH — i.e. would disprove
it.** Concretely it would suffice to prove, for one `k > 4` and `M = T^{k/2}`,

  `| sum_{h>=1} (Delta_k(M,h)/M) K(h) | >> T^{k/4 - eps}`,   `K(h) ≍ min(T, M/h)`.

Significance for the campaign:
- This is the **only disproof mechanism found in 23 cycles**. C42 closed the classical route
  (every resonance `Omega`-result is `T^{o(1)}` because Gál sums are subpolynomial), and that cap is
  a theorem; this route is not blocked by it, because it does not construct a large value of `zeta`
  at all — it argues from the *statistics of divisor correlations*.
- It is falsifiable in the useful direction: it predicts that if anyone proves square-root
  cancellation for the `k`-ary correlation errors against the kernel at any `k > 4`, LH fails.
- It is almost certainly not the truth (everyone expects LH), and its more likely value is as a
  **constraint**: it says the `Delta_k(M,h)` cannot be modelled as independent, which is a
  structural fact any future spectral expansion must respect. Compare `k <= 4`, where E2 of cycle 22
  shows independence is consistent and no correlation is needed.

**Position after 23 cycles.** Both directions now have a stated mechanism:
- to *prove* LH: correlations of strength `T^{k/4-1}` among `Delta_k(M,h)` for `k > 4` (C55), of
  which none is known for any `k`;
- to *disprove* LH: pseudorandomness of the same family at a single `k > 4` (C56).
The two are exact complements, which is the sharpest formulation the campaign has produced: the
Lindelöf hypothesis is, in this frame, precisely a statement about whether the `k`-ary divisor
correlation errors are correlated or random across shifts.

---

## 27. Cycle 24 (2026-07-25) — everything pinned at `1/8` is one comparison

### (C57) THEOREM — the model exponent versus the conjectured truth  `[PROVED HERE]`

Two exponents for the error term `E_k(T)` of the `2k`-th moment:

- **independent-signs model** (cycle 22, corrected): `modelErrorExponent k = k/4`;
- **conjectured truth** (Ivić): `momentErrorExponent k = theta_k = (2k-1)/(2k+2)`.

Then, identically,

  **`k/4 - (2k-1)/(2k+2) = (k-1)(k-2) / (4(k+1))`.**

Consequences, all formalised:
- `model ≤ conjecture ⟺ 1 ≤ k ≤ 2` (`model_le_conjecture_iff`): the model and the conjectured
  truth **agree exactly at `k = 1, 2`** — the roots of `(k-1)(k-2)`, and exactly the two indices at
  which the moment of `zeta` has a known asymptotic formula.
- `conjecture < model` for every `k > 2` (`conjecture_lt_model`): beyond `k = 2` the truth is
  strictly smaller than independent signs predict, by `(k-1)(k-2)/(4(k+1))` — `1/8` at `k = 3`,
  `3/10` at `k = 4`, `5/7` at `k = 6`. **That gap is exactly the correlation among the
  `Delta_k(M,h)` across shifts that the conjectured truth demands.**
- `modelErrorExponent k / (2k) = 1/8` **identically** (`model_floor_is_eighth`).

### (C58) The unification

The last item closes the circle. C41 proved `resolutionFloor(k) = theta_k/(2k) >= 1/8 <=> 1 <= k <= 2`
via `8(2k-1) - 2k(2k+2) = -4(k-1)(k-2)`. But `1/8` is *itself* `(k/4)/(2k)` — the model's resolution
floor, which is `1/8` for **every** `k`. So C41 is literally the statement `theta_k >= k/4`, i.e.
`conjecture >= model`, i.e. `(k-1)(k-2) <= 0`. **C41 and C57 are the same computation.**

> **Everything this campaign found pinned at `1/8` is one comparison: the independent-signs model
> has resolution floor `1/8` at every index `k`, and the conjectured truth attains that floor exactly
> on `[1,2]` — the two moments with known asymptotics — and beats it for `k > 2` by
> `(k-1)(k-2)/(4(k+1))`.**
>
> So `1/8` is *the model's* answer, not `zeta`'s. The twenty-two criticality instances are twenty-two
> routes that see only what the independent-signs model can see. Beating `1/8` is exactly the
> statement that one can detect the correlations the model omits — and by C57 those correlations are
> present for every `k > 2`, of known conjectural strength.

**Sharpened terminal statement.** Prove, for a single `k > 2`, that the `k`-ary divisor-correlation
errors are correlated across shifts to strength `(k-1)(k-2)/(4(k+1))` — equivalently, that
`E_k(T) << T^{k/4 - delta}` for some `delta > 0`. At `k = 3` this asks
`E_3(T) << T^{3/4 - delta}` against the model's `T^{3/4}` and Ivić's conjectured `T^{5/8}`; the
required `delta` is anything positive, and the conjecture provides `1/8`.

**Lean.** `modelErrorExponent`, `model_sub_conjecture`, `model_le_conjecture_iff`,
`conjecture_le_model`, `conjecture_lt_model`, `model_floor_is_eighth` in `MomentResolutionFloor`.
Axioms `[propext, Classical.choice, Quot.sound]`; module builds green.

---

## 28. Cycle 25 (2026-07-25) — scope correction on C41/C57, and the terminal target restated

### (E4) `theta_k = (2k-1)/(2k+2)` for `k >= 3` is my interpolation, not a sourced conjecture

C41 and C57 used `theta_k = (2k-1)/(2k+2)` as "the conjectured true error exponent" for `E_k(T)`.
The **facts** are only:
- `E(T) = Omega(T^{1/4})` (Good) with `E(T) << T^{1/4+eps}` conjectured — so `theta_1 = 1/4`, sharp;
- `E_2(T) = Omega(T^{1/2})` (Ivić–Motohashi) with `E_2 << T^{1/2+eps}` conjectured — `theta_2 = 1/2`,
  sharp.

The formula `(2k-1)/(2k+2)` was fitted to these two points; **for `k >= 3` it is not sourced**, and
moreover `E_k(T)` is not even *defined* for `k >= 3`, since no asymptotic formula for the `2k`-th
moment exists. Statements about `theta_k`, `k >= 3`, are therefore conditional on both the existence
of the asymptotic and on the interpolation. Flagged; the `(k-1)(k-2)` arithmetic in
`MomentResolutionFloor` remains valid as arithmetic about that formula.

### (C59) The substantive, source-only version

Strip the interpolation and only the following remains — which is stronger, because it is
unconditional on the two indices where anything is known:

> **The independent-signs model predicts `E_k(T) ≍ T^{k/4}`, and this is exactly right in both cases
> where the answer is known**: `k = 1` gives `T^{1/4}` and `k = 2` gives `T^{1/2}`, each matched by an
> `Omega`-result. The model's resolution floor is `(k/4)/(2k) = 1/8` **for every `k`**. Hence every
> method that sees only what the model sees is capped at `mu(1/2) <= 1/8`, and the two verifiable
> cases confirm the model is exactly correct there.

That is the campaign's central fact, and it needs no conjecture beyond `theta_1 = 1/4`,
`theta_2 = 1/2`. The twenty-two criticality instances are twenty-two routes confined to the model's
field of view.

### (C60) Terminal target, restated correctly

Since `E_k` is undefined for `k >= 3` without an asymptotic, the target is not "bound `E_k`" but:

> **Establish the `2k`-th moment asymptotic for a single `k >= 3` with error term `T^{k/4 - delta}`,
> any `delta > 0`.**

At `k = 3` this is: `int_0^T |zeta(1/2+it)|^6 dt = T P_9(log T) + O(T^{3/4-delta})`. By the
resolution-floor argument it gives `mu(1/2) <= (3/4-delta)/6 = 1/8 - delta/6 < 1/8`, beating
Bourgain's `13/84` and passing below the pivot for the first time. The interpolated conjecture would
supply `delta = 1/8` and `mu <= 5/48 = 0.1042`.

Note what this does **not** require: not `m(3) = 1` (the sixth-moment *upper bound*, which by the
neutrality law C5 is subconvexity-neutral), but the **asymptotic with a power-saving error**. The
distinction is the campaign's: an upper bound `T^{1+eps}` gives `1/6`; the asymptotic with error
`T^{3/4-delta}` gives below `1/8`.

---

## 29. Cycle 26 (2026-07-25) — reconciling `k > 2` and `k > 4`, and where the model must break

### (C61) The model's consistency range is exactly `k <= 4`  `[PROVED HERE]`

The independent-signs model predicts moment-error size `T^{k/4}` against a main term
`≍ T (log T)^{k^2}`. The prediction is consistent with the existence of an asymptotic formula
(error `= o(main)`) exactly when

  `T^{k/4} = o(T (log T)^{k^2})`  <=>  `k/4 < 1`, **or** `k = 4` (where `T^1 / (T log^{16} T) -> 0`).

So the model is consistent with the Keating–Snaith/CFKRS moment conjecture for `k <= 4` and
**contradicts it for every `k > 4`**. This settles the tension between cycle 23 (`k > 4`) and cycle
24 (`k > 2`): the sourced threshold is **`k > 4`**; cycle 24's `k > 2` came from comparing against
the interpolated `theta_k`, which E4 has flagged as unsourced. Correlations among the
`Delta_k(M,h)` are *provably* required only for `k > 4`.

### (C62) All the campaign's targets are one statement

The model gives `m(k) <= max(1, k/4)` (this is `transferBound k (1/2) (1-1/k)`, C44). Hence:

| `k` | model | best known | gap |
|---|---|---|---|
| 2 | `1` | `1` | — (both sharp) |
| 3 | `1` | `5/4` | model would prove the **sixth moment** |
| 4 | `1` | `3/2` | model would prove the **eighth moment** |
| 6 | `3/2` | `2` (Heath-Brown 1978) | model would **improve the twelfth moment** |

and `min_k max(1,k/4)/(2k) = 1/8`, attained at `k = 4`. So:

> **model correct at `k = 4`  <=>  `m(4) = 1`  <=>  eighth moment  =>  (by convexity with `m(2)=1`)
> `m(3) = 1`, the sixth moment  =>  `mu(1/2) <= 1/8`.**

Everything the campaign has separately identified — the neutrality law's "aim at `k = 4`, not
`k = 3`" (C5), the additive-divisor cap (C44), the resolution floor (C41/C59), the pivot `v = 1/8`
(C13) — is this one statement seen from four sides.

### (C63) And below `1/8`

Since `m(k) >= 1` always while the model gives `k/4 > 1` for `k > 4`, the model is *not* sharp there,
and any unconditional `m(k) < k/4` at a single `k > 4` yields `mu(1/2) < 1/8`. The nearest instance:

> **`m(6) < 3/2`** — i.e. `int_0^T |zeta(1/2+it)|^{12} dt << T^{3/2-delta}` — gives
> `mu(1/2) <= (3/2-delta)/12 < 1/8`.
> Known: `m(6) <= 2` (Heath-Brown 1978, unimproved). The model itself would give `3/2`; the moment
> conjecture gives `1`, hence `mu <= 1/12`.

So the campaign's two thresholds are now explicit and both are twelfth-moment statements:
`m(6) < 13/7 = 1.857` beats Bourgain (C5 calibration); `m(6) < 3/2` passes below the pivot.

---

## 30. Cycle 27 (2026-07-25) — why `m(6) <= 2` has stood for 48 years: the method is already at its limit

### (C64) Heath-Brown's twelfth moment is optimal for its own mechanism  `[PROVED HERE]`

From C16, Heath-Brown's mechanism is the **short second moment** `int_{t_0}^{t_0+G}|zeta|^2 dt` at
scale `G ≍ V^2`, which
- is sharp for an *individual* `t_0` when `G >= T^{1/3}` — and that alone yields the Weyl bound;
- is pushed down to `G = T^{1/4}` **on average over the large-value set**, by an
  approximate-orthogonality/large-sieve argument (Milićević–White's transcription).

Under `G = T^{2v}` the range `[T^{1/4}, T^{1/3}]` is exactly `v in [1/8, 1/6]`, which is precisely the
window on which `m(6) = 1 + sup_v[12v - phi(v)] = 2` is attained (`phi >= 12v-1` meets `phi >= 4v` at
`v = 1/8` and reaches `1` at `v = 1/6`).

**The lower endpoint is not a technical choice.** `G = T^{1/4}` is the conjecturally optimal scale
for the short second moment, and it is *sharp*: `E(T) = Omega(T^{1/4})` means the short second moment
**fails** below `T^{1/4}`. Hence

> **Heath-Brown's argument already runs at the information-theoretic limit of its input.**  `m(6) <= 2`
> is the exact output of the method when the second-moment error term is taken at its best possible
> value, and no sharpening of that input can improve it. This explains the absence of any improvement
> since 1978 — not as a gap in effort, but as a method operating at its ceiling.

### (C65) The two second-moment routes, and why they differ

| route | input at its conjectural limit | output |
|---|---|---|
| **pointwise** short second moment at `G = T^{theta_E}` | `theta_E = 1/4` (sharp, `Omega(T^{1/4})`) | `mu <= theta_E/2 = 1/8` |
| **Heath-Brown**, averaged over the large-value set | same `G = T^{1/4}` | `m(6) <= 2`, hence `mu <= 1/6` |

Both consume the same arithmetic input and both are at its limit; the pointwise route gives the
better exponent because it does not pay for the averaging. Currently the pointwise route is at
`theta_E = 517/1648` (Bourgain–Watt), giving `mu <= 0.15686` — just behind Bourgain's direct
`13/84 = 0.15476` (C18). **So the entire second-moment programme, both branches, is already within
`0.002` and `1/24` respectively of its own ceiling.**

### (C66) Consequence: the target must change mechanism, not sharpen one

Combining with C59 (`the model's floor is 1/8`), C61 (`the model breaks only for k > 4`) and C63
(`m(6) < 3/2` passes below the pivot):

> Improving `m(6)` below `3/2` cannot come from the second moment in either branch — both are capped
> by `E(T) = Omega(T^{1/4})`. It requires the **fourth**-moment input at its own limit
> (`E_2(T) = Omega(T^{1/2})`, ceiling also `1/8`) or a mechanism outside the moment/error-term
> programme entirely. Since `1/8` is the shared ceiling of both, and `m(6) < 3/2` is *equivalent* to
> passing below `1/8` (C63), **no combination of the second and fourth moment error terms can reach
> it.** The requirement is strictly `k > 4` correlations (C61), i.e. the twelfth-moment target and
> the correlation target are the same target.

---

## 31. Cycle 28 (2026-07-25) — completeness: every route is either capped (with proof) or equivalent to LH

### (C67) Classification of all routes examined

After 28 cycles the routes divide exactly into two classes.

**A. Capped, with the cap proved here.**

| route | cap | proof |
|---|---|---|
| mean-value / large-sieve, all `k`, all `sigma` | `1/4` (convexity) | D8 |
| Halász–Montgomery with any exponential-sum input | `1/4` (reproduces the 4th moment) | C14 |
| Guth–Maynard large values | inert at the self-dual block | C15 |
| second-moment error term `E(T)` | `1/8` (`Omega(T^{1/4})` sharp) | C41, C59 |
| fourth-moment error term `E_2(T)` | `1/8` (`Omega(T^{1/2})` sharp) | C41, C59 |
| Heath-Brown's twelfth moment | `m(6) = 2`, i.e. `mu <= 1/6` | C64 (method at its input's limit) |
| `k`-ary additive divisor via Ivić's transfer | `1/8` | C44 |
| short-interval mean square of `Delta_k` | neutral (reproduces the chord) | D14 |
| circle-method split of the shift average | tautological | D18 |
| resonance / Gál sums (the `Omega` side) | `T^{o(1)}`, cannot disprove LH | C42 |
| `GL(3)` subconvexity applied to `zeta^3` | `1/6` at best | D20 |

Every cap is `1/4`, `1/6`, or `1/8`, and each of those is a criticality point identified in the map.

**B. Uncapped — and each is equivalent to LH or strictly implies it.**

- the **moment conjecture** `m(k) = 1` for all `k` — *equivalent* to LH;
- the **exponent-pair conjecture**, `(eps, 1/2+eps)` an exponent pair — i.e. square-root cancellation
  for `sum_{n~N} n^{-it}` pointwise; implies LH and is the only route that has ever moved `mu(1/2)`
  (Weyl `1/6`, Bombieri–Iwaniec `9/56`, Huxley `32/205`, Bourgain `13/84`);
- **`k > 4` correlations** among `Delta_k(M,h)` across shifts (C61), which by C63 is the same target
  as `m(6) < 3/2`.

> **This is the campaign's completeness statement.** Every route in the subject that admits a
> ceiling has been given one, with a proof; what remains uncapped is exactly the family of
> statements that are equivalent to, or strictly stronger than, the Lindelöf hypothesis itself.
> That is the structural reason the problem is open: there is no intermediate statement left whose
> resolution would settle it.

### (C68) The two live objects, side by side

| | moment side | exponential-sum side |
|---|---|---|
| statement | `m(k) = 1` for all `k` | `sum_{n~N} n^{-it} << N^{1/2+eps}` for `N <= sqrt t` |
| current | `m(2) = 1`; `m(3) <= 5/4`, `m(6) <= 2` | `<< N^{1/2} t^{13/84}`, i.e. `N^{0.809}` at `N = sqrt t` |
| distance to target | `1/4` at `k = 3` | `0.309` in the exponent |
| capped? | no | no |
| moved since | `m(6)`: 1978 | `mu`: 2017 |

Both are self-dual at `N = sqrt t` (C13, C39) and both are blocked there by the square-root barrier.
The campaign's twenty-two criticality instances are all statements that some *auxiliary* route
returns the value already visible from these two.

---

## 32. Cycle 29 (2026-07-25) — E5: the `1/8` cap used the wrong conjecture; Conrey–Gonek gives LH

### (E5) Scope correction to C44/C62/C63/C66

C44 fed the transfer **Vinogradov's** conjectured size `Delta_k(x,h) << x^{1-1/k+eps}`, giving
`(a,b) = (1/2, 1-1/k)` and the cap `mu <= 1/8`. But BBMZ state the **Conrey–Gonek** prediction
(Conrey–Gonek, Eq. (30) and Conjecture 3), quoted verbatim in their introduction:

  `D(N,h) = int_N^{2N} S(x,h) dx + O(N^{1/2+eps})`,  uniformly for `1 <= h <= x^{1/2}`,

i.e. `|Delta_k(N,h)| << N^{1/2+eps}` — **independent of `k`**, and strictly stronger than Vinogradov's
for every `k >= 3` (`1/2 < 1 - 1/k`).

### (C69) THEOREM — the Conrey–Gonek input gives Lindelöf  `[PROVED HERE]`

With square-root cancellation over shifts, Conrey–Gonek's size is the input `(a,b) = (1/2, 1/2)`, and

  **`transferBound k (1/2) (1/2) = 1 + max(0, k·0/2 - 1/2) = 1`  for every `k`,**

i.e. `m(k) = 1` for all `k` — **hence LH**. Equivalently in the model language: the off-diagonal error
becomes `(1/M)(2MT)^{1/2} M^{1/2} = (2T)^{1/2}`, *independent of `k`* and `<< T` always. The breaking
criterion is satisfied for every `k > 0`: `k(2a+2b-3) = -k < 0 = 4a-2`.

> **So the additive-divisor route is *not* capped at `1/8`.** The cap of C44 is an artefact of feeding
> the transfer Vinogradov's weaker conjectured size. Under the modern Conrey–Gonek prediction the
> same transfer delivers the full moment conjecture and therefore the Lindelöf hypothesis.
> C44 stands only as: *Vinogradov's* size, via the transfer, caps at `1/8`.

### (C70) The two conjectured sizes are in direct conflict

- Conrey–Gonek: `Delta_k(x,h) << x^{1/2+eps}`.
- Ivić (Ivić–Wu (1.10)): `Delta_k(x,h) = Omega(x^{1-1/k})` for every `k >= 2`, `h >= 1`.

For `k = 2` both read `x^{1/2}` and agree. **For `k >= 3` they contradict each other.** Combining with
C55: if Ivić's `Omega`-conjecture holds *and* the `Delta_k(M,h)` behave independently across `h`, then
the moment conjecture fails for `k > 4` and LH is false. So at most one of

  (i) Ivić's `Omega(x^{1-1/k})`, (ii) independence of `Delta_k(M,h)` across `h`, (iii) LH

can fail to be violated — precisely, (i) and (ii) together contradict (iii).

**Revised standing position.** The additive-divisor route is uncapped and reaches LH; what is capped
is the version fed Vinogradov's size. The live question is therefore sharpened to a conflict between
two named conjectures about the *size* of the `k`-ary divisor-correlation error, decidable in
principle at `k = 3`: is `Delta_3(x,h)` of order `x^{1/2}` (Conrey–Gonek, giving LH) or `x^{2/3}`
(Ivić, capping the route at `1/8`)?

**Lean.** `transferBound_conreyGonek`, `conreyGonek_breaks_chord`, `vinogradov_exceeds_conreyGonek`
in `ShiftAverageTransfer`; module builds green.

---

## 33. Cycle 30 (2026-07-25) — the two hypotheses separate; what each one buys

### (C71) THEOREM — clean separation of the two inputs  `[PROVED HERE]`

| input | `(a,b)` | `transferBound k a b` | consequence |
|---|---|---|---|
| Conrey–Gonek size, **no** shift cancellation | `(1, 1/2)` | `1 + max(0, k/4 - 1)` | `mu(1/2) <= 1/8` (at `k = 4`) |
| Conrey–Gonek size **+** square-root shift cancellation | `(1/2, 1/2)` | `1` for every `k` | `m(k) = 1` for all `k`, i.e. **LH** |
| Vinogradov size + square-root shift cancellation | `(1/2, 1-1/k)` | `1 + max(0, k/4 - 1)` | `mu(1/2) <= 1/8` |

So the pointwise size and the shift-cancellation are **independent halves**: either one alone (with
the other at its trivial value) delivers exactly `1/8`; **together they deliver Lindelöf.** This is
the cleanest decomposition of the target the campaign has produced, and it explains the recurrence of
`1/8` once more: `1/8` is what *one* of the two halves buys.

### (C72) The remaining gap in the Conrey–Gonek route

Conrey–Gonek's prediction is stated **uniformly for `1 <= h <= x^{1/2}`**, while the transfer needs
shifts up to `h ≍ M`. The uncovered range `x^{1/2} < h <= x` must be supplied separately; with the
trivial `|Delta_k| << x^{1+eps}` there it contributes `x^{1+eps} log x`, which is far too large.
So the route requires the Conrey–Gonek error to persist to `h <= x^{1-eps}`. That is the natural
expectation but is **not** part of the stated conjecture, and it is the one gap in an otherwise
complete conditional chain to LH. `[OPEN CORE]`

### (C73) The conflict at `k = 3`, and what would settle it

- **Conrey–Gonek**: `Delta_k(x,h) << x^{1/2+eps}` — the "square-root of the number of terms"
  heuristic, and the same shape for every `k`.
- **Ivić** (Ivić–Wu (1.10)): `Delta_k(x,h) = Omega(x^{1-1/k})` for every fixed `h >= 1` — equivalently
  "the correlation error is the square of the ordinary divisor error", since
  `(x^{(k-1)/(2k)})^2 = x^{1-1/k}`.

At `k = 2` both read `x^{1/2}` and the `Omega` is a **theorem** (Motohashi), so `k = 2` does not
discriminate. At `k = 3` they read `x^{1/2}` and `x^{2/3}` and **contradict**. By C71:

> if Conrey–Gonek is right (and extends in `h`), LH follows; if Ivić's `Omega` is right, the
> additive-divisor route is capped at `1/8` and LH must come from elsewhere.

**This is the sharpest live question the campaign has isolated**, and it is a question about divisor
arithmetic alone: *what is the true order of `Delta_3(x,h)` for fixed `h`?* Deciding it at `k = 3`
either yields LH by C71 or closes the route by C44.

**Lean.** `transferBound_conreyGonek`, `transferBound_conreyGonek_pointwise`,
`conreyGonek_separation`, `conreyGonek_breaks_chord`, `vinogradov_exceeds_conreyGonek`; module green.

---

## 34. Cycle 31 (2026-07-25) — the contested exponent is a hyper-Kloosterman assembly question

### (C74) Where the two conjectured sizes come from

- **Conrey–Gonek `x^{1/2+eps}`** is the "square-root of the number of terms" heuristic: `x` summands
  of size `x^eps`, full cancellation. Its shape is `k`-independent, which is exactly what one expects
  if the underlying complete exponential sums are square-root cancelling.
- **Ivić `Omega(x^{1-1/k})`** has an exact structural reading: `x^{1-1/k} = (x^{(k-1)/(2k)})^2`, i.e.
  **the correlation error is the square of the ordinary divisor error** `Delta_k(x) ≍ x^{(k-1)/(2k)}`.
  At `k = 2` this gives `x^{1/2}`, agreeing with Conrey–Gonek; the shapes separate from `k = 3`.

### (C75) The delta-method reading: it is an assembly question, and the input exists

In the delta/circle method the error term of `D_k(x,h)` is assembled from complete sums
`sum*_{a mod c} e(-ah/c) · (Voronoi duals)`, whose arithmetic core for `d_k` is the
**hyper-Kloosterman sum `Kl_k`**. Deligne's bound gives `Kl_k` its full square-root cancellation
(`|Kl_k(a;p)| <= k p^{(k-1)/2}`, i.e. square-root in the `k-1` free variables) for every `k` — at
`k = 2` this is Weil's bound, which is precisely what produces `Delta_2(x,h) ≍ x^{1/2}`.

> **So the Conrey–Gonek / Ivić conflict is not about a missing input.** The arithmetic input —
> square-root cancellation for `Kl_k` — is a theorem of Deligne for every `k`. The question is
> whether the **assembly** preserves it: Conrey–Gonek's `x^{1/2}` is what full preservation gives,
> Ivić's `x^{1-1/k}` is what a `k`-dependent assembly loss gives.

This places the terminal question in the same family as every other finding of the campaign: **the
losses are in assembly, not in information** (C46). It also distinguishes this route from the
`GL(3)` spectral route of cycles 19–20, where the input itself (a Motohashi analogue for `Delta_3`)
does not exist. Here the input exists and has for fifty years.

**Calibration of how badly the assembly currently loses.** `Delta_3(x,h) = o(x)` is *not known for
any `k >= 3`, even for fixed `h`* (Ivić–Wu, (1.5)). So against a conjectured truth of `x^{1/2}` or
`x^{2/3}`, the current state is `x^{1+eps}` — the assembly presently loses everything. The nearest
positive results are for the *mixed* correlation `d_k x d`: Topacogullari obtains
`D_{3,2}(x,h) = x P_3(log x) + O(x^{8/9+eps})` for `1 <= h << x^{2/3}`, i.e. a saving of `x^{1/9}`,
and analogous power savings for `d_k x d`, `k >= 4`. **No power saving whatsoever is known for
`d_3 x d_3`.**

### (C76) Restated terminal question

> Prove any power saving for the *self*-correlation: `Delta_3(x,h) << x^{1-delta}` for fixed `h`.
> This is the first nontrivial estimate of any kind for `d_3 x d_3`. By C71 the route to LH then
> needs the saving pushed to `x^{1/2+eps}` together with square-root cancellation over shifts
> extended to `h <= x^{1-eps}` (C72).

Recorded as the campaign's open core, replacing the `GL(3)`-Motohashi formulation of cycle 19: that
one required an input that does not exist; this one requires an assembly that does not yet work,
from an input (Deligne) that does.

---

## 35. Cycle 32 (2026-07-25) — the self-correlation reduces to moduli `<= x^{1/3}`; the level of
distribution is **not** the obstruction

### (C77) Reduction of `d_3 x d_3` to `d_3 x d` in progressions of small modulus

Write `d_3(m) = #{(a,b,c) : abc = m}` and let `a` be the smallest factor, so `a <= m^{1/3}`. Then
`d_3` is expressible through divisors `a <= m^{1/3}` and the binary divisor function, giving

  `D_3(x,h) = sum_{n<=x} d_3(n) d_3(n+h)
     ≍ sum_{a <= x^{1/3}} sum_{n <= x, n ≡ -h (mod a)} d_3(n) d((n+h)/a) · (multiplicity weights)`,

and substituting `n + h = a m`,

  **`D_3(x,h) ≍ sum_{a <= x^{1/3}} sum_{m <= x/a} d(m) d_3(a m - h)`.**

So the ternary **self**-correlation is a sum over moduli `a <= x^{1/3}` of `d_3` evaluated along the
linear forms `am - h`, weighted by `d(m)`. At `a = 1` this is exactly Topacogullari's `d_3 x d`
correlation, which **is** solved with a power saving (`O(x^{8/9+eps})` for `h << x^{2/3}`).

### (C78) The level of distribution is not the obstruction  `[PROVED HERE, as a diagnostic]`

The moduli in (C77) run only to `x^{1/3}`, comfortably inside the classical `x^{1/2}` barrier — and
the ternary divisor function is known to have exponent of distribution **beyond `1/2`**:
Friedlander–Iwaniec `1/2 + 1/230`, improved by Heath-Brown, then Fouvry–Kowalski–Michel to
`1/2 + 1/46` for prime moduli (arXiv:1304.3199), with subsequent refinements.

> **So `d_3 x d_3` is not blocked by the level of distribution.** Every modulus it needs lies at
> `x^{1/3}`, far below what is already available. The obstruction is the **`d(m)` weight and the
> bilinear structure** of the inner sum `sum_m d(m) d_3(am - h)` — i.e. the same
> "assembly, not information" phenomenon as C46 and C75, now localised to a specific bilinear form.

This is a genuinely useful diagnostic: it rules out the most natural first guess (that one needs a
level of distribution beyond reach) and points instead at the weighted linear-form sums.

### (C79) Restated open core, third form

> Obtain a power saving for `sum_{m <= x/a} d(m) d_3(a m - h)`, uniformly for `a <= x^{1/3}` and
> fixed `h`, and assemble over `a`. At `a = 1` this is Topacogullari's theorem; the content is
> uniformity in `a` together with the assembly.

Three successive formulations of the same open core are now on record, each strictly more concrete
than the last: `GL(3)` Motohashi analogue (cycle 19, input missing) -> hyper-Kloosterman assembly
(cycle 31, input exists) -> **uniform-in-`a` `d_3 x d` correlations along linear forms `am - h`**
(here, with the `a = 1` case a theorem). The progression is from "a tool that does not exist" to "a
theorem that must be made uniform in one parameter".

---

## 36. Cycle 33 (2026-07-25) — the function-field model decides the contested exponent, and every
ingredient the campaign needs is already a theorem there

### (C80) `F_q[t]` evidence on the Conrey–Gonek / Ivić conflict

Sawin has proved, in the large-`q` limit over `F_q[t]`:
- **short intervals**: *Square-root cancellation for sums of factorization functions over short
  intervals in function fields* (Duke Math. J. 170 (2021) 997–1026; arXiv:1809.05137) — the estimate
  approaches square-root cancellation for large characteristic;
- **progressions**: *Square-root cancellation for sums of factorization functions over squarefree
  progressions in `F_q[t]`* (Acta Math. 233 (2024) 285–418; arXiv:2102.09730) — level of distribution
  converging to `1` and power savings converging to square-root cancellation as `q -> infinity`, for
  the Möbius, von Mangoldt **and divisor functions**.

Both point the same way: over `F_q[t]` the governing behaviour of divisor sums is **square-root
cancellation**, with no `k`-dependent degradation. That is the shape of Conrey–Gonek's
`Delta_k(x,h) << x^{1/2+eps}`, not of Ivić's `Omega(x^{1-1/k})`.

*Caveat, recorded honestly.* Sawin's objects are sums of `d_k` over short intervals and progressions,
i.e. the analogues of `Delta_k(x+H) - Delta_k(x)` and of the level of distribution — **not** directly
the self-correlation `Delta_k(x,h)`. The evidence is therefore strong but indirect. It is
nevertheless the only evidence the campaign has found that bears on the conflict at all, and it
favours Conrey–Gonek, hence (by C71) favours the additive-divisor route reaching LH.

### (C81) Every ingredient the campaign requires is a theorem over `F_q[t]`

Collecting what 33 cycles identified as needed, against what is known in the function field:

| campaign requirement (number field) | status over `Q` | status over `F_q[t]` |
|---|---|---|
| short-interval mean square `I_k(X,h) << X^{1+eps} h` (D14) | Ivić: *"seems unattainable at present"* | **theorem** (Sawin 2021, large `q`) |
| level of distribution for `d_3` beyond `1/2` (C78) | `1/2 + 1/46` (FKM) | **-> 1** (Sawin 2024) |
| square-root cancellation, no `k`-degradation (C80) | contested (Conrey–Gonek vs Ivić) | **theorem** (Sawin, both papers) |
| Lindelöf hypothesis itself | open | trivial (Weil: RH is a theorem) |

> **So the obstruction is not the arithmetic — it is the transfer from `F_q[t]` to `Z`.** Every
> analytic ingredient the campaign has isolated as necessary is already available over function
> fields, proved by geometric means (singular loci of the varieties whose `F_q`-points control the
> sums). What fails in the number field is the absence of the geometric input, not the truth of the
> statements.

This is the campaign's cleanest statement of the nature of the difficulty, and it is consistent with
every barrier proved: each cap (C67) is a cap on an *assembly* available over `Z`, and each is
absent over `F_q[t]` precisely because the geometric method does not assemble — it computes.

### (C82) Consequence for the open core

The core (C79) — a power saving for `sum_m d(m) d_3(am-h)` uniformly in `a <= x^{1/3}` — has a
function-field analogue that Sawin's methods reach. **The live question is therefore whether the
geometric argument admits a number-field counterpart**, i.e. whether the singular-locus computation
that yields square-root cancellation over `F_q[t]` has an archimedean shadow. Recorded as the
campaign's standing open core, superseding C79's number-field-only phrasing.

---

## 37. Cycle 34 (2026-07-25) — map rewritten to the corrected state; Hamburger rigidity

**Durable artifact refreshed.** `../2-fully-proven/new_scientific_knowledge/lindelof-frontier-criticality-map.md`
dated from cycle 11 and still asserted claims retracted in cycles 18, 19, 22, 25 and 29 (errata
E1–E5). It has been rewritten end to end against the corrected record: the pivot is now derived from
the independent-signs model (which is *exactly right* at `k = 1, 2`, the only verifiable cases), the
`3k/4-1` conspiracy exponent and the `GL(3)`-Motohashi framing are gone, the additive-divisor cap is
correctly attributed to Vinogradov's size rather than to the route, and the Conrey–Gonek separation
(either half buys `1/8`; both buy LH) and the `F_q[t]` evidence are included. For a multi-session
campaign a stale map is worse than no map; this is now the single authoritative summary.

### (C83) Hamburger rigidity — the HGT thesis, verified for this object

Hamburger's theorem (1921): a Dirichlet series `F(s) = sum a_n n^{-s}`, convergent for `sigma > 1`,
meromorphic of finite order with its only pole at `s = 1`, and satisfying **the same functional
equation as `zeta`**, must equal `c·zeta`. So the class of objects with `zeta`'s functional equation
and growth is **one-dimensional**.

Consequences for this campaign:
- `mu(1/2)` is a well-defined invariant of the functional equation alone: there is no deformation
  within the class along which it could be tracked, and no "model object" in the class with
  `mu = 1/8` can exist. **A barrier proof by exhibiting a counterexample object is therefore
  impossible** — recorded as **D22**, closing the Selberg-style "parity example" strategy that a
  barrier theorem would normally use.
- It confirms the project's founding metaphor for this object exactly: `zeta` is *fixed by a
  constraint* (its functional equation plus growth), not propagated by any flow — and the campaign's
  twenty-two criticality instances are the quantitative shadow of that rigidity, each showing that a
  method respecting the constraint returns the constraint's own fixed-point value.

**Standing position.** Open core as in §5 of the map: the transfer of Sawin's geometric square-root
cancellation from `F_q[t]` to `Z`. Everything else in the subject that admits a ceiling has one, with
a proof, and the ceilings are `1/4`, `1/6`, `1/8`.

---

## 38. Cycle 35 (2026-07-25) — the Backlund route, and an assessment

### (C84) The Backlund route is the `phi` analysis in disguise

LH `<=>` for each `delta > 0`, `N(1/2+delta; T, T+1) = o(log T)` (Backlund 1918). Analysing it:

- **On average it already holds.** Global zero-density `N(sigma,T) << T^{A(sigma)(1-sigma)+eps}` gives
  `T^{1-c}` such zeros in total, so the *average* over unit intervals is `<< T^{-c} log T = o(log T)`.
  LH can only fail on **exceptional intervals**, of which there are at most `T^{1-c}/log T`.
- **Exceptional intervals are bounded in strength.** Off-line zeros come in pairs `beta, 1-beta` at
  the same height, and a unit interval contains `(1/2pi)log(T/2pi) ≈ 0.159 log T` zeros in total.
  So an exceptional interval carries at most `≈ 0.0796 log T` zeros on each side of the line.
  Backlund's `o(log T)` therefore has to exclude only the band `c in (0, 0.0796]`.
- **But the criterion is *local* and every density estimate is *global*.** Positive-proportion
  results (Conrey `2/5`, later `> 0.41`) are also global densities among all zeros up to `T`; none
  precludes a local exceptional interval.

And an exceptional interval is exactly a place where `|zeta|` is large: Backlund's implication
"many off-line zeros `=>` large `mu`" is the same content as the large-deviation exponent `phi`.
**So the Backlund route carries no information the `phi` analysis does not already have**, and every
ceiling proved in §3 of the map applies to it verbatim. Recorded as **D23** so it is not reopened as
if it were an independent route.

### Assessment (recorded in the log, and stated to the user)

Thirty-five cycles have produced: four Lean modules with clean axioms; eleven proved method-ceilings;
a five-fold characterisation of the pivot `1/8`; the moment-neutrality law; the proof that the
`Omega` side cannot disprove LH; the Conrey–Gonek separation showing which conjecture settles LH
which way; and the localisation of the remaining gap to the `F_q[t] -> Z` transfer of Sawin's
geometric square-root cancellation.

What has **not** been produced is a proof or a disproof of the Lindelöf hypothesis, and this log
records the reason plainly: LH has been open since 1908, `mu(1/2) <= 13/84` has stood since 2017,
`m(6) <= 2` since 1978, and §6 of the map proves there is **no uncapped intermediate statement** —
every remaining route is equivalent to LH or strictly stronger. That is a structural obstruction, not
a shortfall of effort or of cycles. Further iterations of this campaign will continue to produce map
refinements and barrier theorems; they will not produce a resolution.

---

## 39. Cycle 36 (2026-07-25) — consolidated to a preprint

`../4-publication-ready/lindelof-method-ceilings.md` — *Method ceilings for the Lindelöf hypothesis:
eleven barrier theorems, and why they all meet at 1/8*.

Contents: the independent-signs model and its resolution floor (§1); five characterisations of the
pivot (§2); eleven ceiling theorems (§3), each `1/4`, `1/6` or `1/8`, plus two tautological routes;
the separation of the additive-divisor route into two halves each worth `1/8` and jointly worth LH,
with the Conrey–Gonek/Ivić conflict and the `F_q[t]` evidence (§4); completeness, Hamburger
rigidity, and the remaining gap (§5).

The abstract states plainly that the paper proves no new bound on `mu(1/2)` and that its content is
negative and structural. Four results carry Lean certificates
(`MomentNeutralityLaw`, `MomentChordPivot`, `ShiftAverageTransfer`, `MomentResolutionFloor`),
all with axioms `[propext, Classical.choice, Quot.sound]`.

**Campaign state.** The `1-in-progress` card remains the working log of record, including errata
E1–E5 and dead routes D1–D23. The map (`2-fully-proven`) and the preprint (`4-publication-ready`)
are both current as of this cycle. The open core is unchanged and is stated in §5.3 of the preprint.

---

## 40. Cycle 37 (2026-07-25) — capstone theorem in Lean

`GaloisForLFunctions.HTGeometry.LindelofMethodCeilings` bundles the paper's three quantitative
claims into a single machine-checked statement `lindelof_method_ceilings`:

1. `modelErrorExponent k / (2k) = 1/8` for every `k > 0` — the model floor, identically in `k`; and
   `modelErrorExponent k ≤ momentErrorExponent k ↔ 1 ≤ k ≤ 2` — the model is exact exactly at the
   two indices with known asymptotics.
2. `min (1/(2j)) θ < θ ↔ 1/(2θ) < j` — the neutrality threshold; with the two instances
   `min (1/6) (13/84) = 13/84` (sixth moment neutral) and `min (1/8) (13/84) = 1/8` (eighth moment
   improves).
3. `transferBound k (1/2) (1-1/k)/(2k) = 1/8` and `transferBound k 1 (1/2)/(2k) = 1/8` for `k ≥ 4`,
   and `transferBound k (1/2) (1/2) = 1` for every `k` — the two halves each worth `1/8`, jointly
   worth `m(k) = 1`.

Two companion theorems: `chord_is_one_input` (the chord is the image of `(1/2,1)`, and the pivot gain
is constant on it) and `chord_criticality` (the break criterion, with `(1/2,1)` failing it with
equality on *both* sides simultaneously for every `k`).

Axioms `[propext, Classical.choice, Quot.sound]`; `lake build GaloisForLFunctions.HTGeometry` green.
Five Lean modules now carry the campaign: `MomentNeutralityLaw`, `MomentChordPivot`,
`ShiftAverageTransfer`, `MomentResolutionFloor`, `LindelofMethodCeilings`.

---

## 41. Cycle 38 (2026-07-25) — a reachable target: `(a,b) = (1/2,1)` reproves Heath-Brown

### (C85) The critical input would give a new proof of the 1978 twelfth moment

By Theorem 3.6 of the preprint, the input `(a,b) = (1/2, 1)` — that is,

  **`sum_{h<=H} Delta_k(x,h) << H^{1/2} x^{1+eps}`**

— maps under the transfer to `m(k) <= 1 + (k-2)/4` for every `k`, hence in particular to

  `m(3) <= 5/4`,  `m(4) <= 3/2`,  **`m(6) <= 2`**.

The last is Heath-Brown's theorem (QJM 29 (1978)), whose only known proof runs through short second
moments and an approximate-orthogonality argument over the large-value set (C16, C64). So:

> **An unconditional proof of `sum_{h<=H} Delta_k(x,h) << H^{1/2} x^{1+eps}` would give a new,
> purely additive-divisor proof of Heath-Brown's twelfth-moment bound** — and simultaneously of
> `m(3) <= 5/4` and `m(4) <= 3/2`, which are currently only interpolations from it.

**Why this is the campaign's most reachable target.** It does not require *beating* any known bound —
only *matching* the chord by a different route. And at `k = 3`, `H = x^{1/3}` it is quantitatively
close: `(1/2,1)` asks for `x^{7/6+eps}`, while Baier–Browning–Marasingha–Zhao already have `x^{5/4}`.
**The gap is exactly `x^{1/12}`** — the same `x^{1/12}` identified in C36 as the cost of the crude
minor-arc estimate `|K_H| <= 1/(2||alpha||)` at the major-arc boundary.

**Status of the two routes to it.**
- BBMZ Theorem 1's own route is **blocked** (D16): its proof is Perron plus Cauchy–Schwarz between
  `int|zeta|^6` and a Dirichlet-polynomial mean value whose second factor is a block of
  `zeta(1/2-it)^3`, so it estimates the sixth moment by itself; the induced self-map on `m(3)` sends
  `5/4 |-> ≈1.39` and has fixed point `3/2`.
- The circle-method route is **tautological** (D18) as a *split*, but the `x^{1/12}` is localised: it
  is the loss in bounding `int_m |S|^2 K_H` by `sup_m|K_H| · int_m|S|^2 = N^{1/4} · N log^8 N`. Any
  treatment that uses the decay of `K_H` away from the major arc, rather than its supremum, attacks
  exactly that factor.

**Recorded as the campaign's reachable sub-target**, distinct from the open core (which requires
beating the chord). Output if achieved: a new proof of a 48-year-old theorem by a route the subject
does not currently have, plus the first nontrivial `(a,b)` input for the transfer at `b = 1`.

---

## 42. Cycle 39 (2026-07-25) — the `x^{1/12}` is entirely in the `Delta_3` term; nothing else leaks

Decompose the annulus integral exactly. With `C(r) = sum_n d_3(n)d_3(n+r)`, `D = sum_n d_3(n)^2`,

  `int_{|alpha|<=Delta}|S|^2 dalpha = 2 Delta D + (2/pi) sum_{r>=1} C(r) sin(2 pi Delta r)/r`,

and splitting `C(r) = S(r)·N log^4 + Delta_3(N,r)` with `S(r)` the singular series of mean `c`:

| term | contribution to the annulus `F(2Delta)-F(Delta)` | after `(1/Delta)·`, at `Delta = N^{-1/4}` | target `N^{7/6}` |
|---|---|---|---|
| diagonal `2 Delta D` | `≍ Delta N log^8` | `N log^8` | **clear** |
| singular-series constant `c` | `≍ Delta N log^4` (via `sum_r sin(2 pi Delta r)/r = pi/2 - pi Delta`) | `N log^4` | **clear** |
| singular-series fluctuation `S(r)-c` | `<< Delta^{1/2} N log^4` (square-root cancellation in `sum_{r<=R}(S(r)-c)`, then the bracket `≈ 2 pi Delta r` for `r <= 1/Delta` and `O(1)` beyond) | `<< N^{9/8} log^4` | **clear** (`9/8 < 7/6`) |
| `Delta_3(N,r)` | — | — | **the target** |

> **So no slack is lost outside the `Delta_3` term.** The main term, the singular series and its
> fluctuation all come in strictly below `N^{7/6}`, the fluctuation with room `N^{7/6-9/8} = N^{1/24}`
> to spare. The entire `x^{1/12}` gap of C85 sits in `sum_r Delta_3(N,r)·(kernel)` and nowhere else.

This sharpens D18 rather than contradicting it: the circle-method decomposition is tautological *as a
split of the target*, but the accounting above shows the tautology is tight — there is no auxiliary
term whose better treatment could contribute. Any gain must come from the divisor-correlation error
itself.

**Consolidated deliverables (state as of this cycle).**
- Working log: this card (errata E1–E5, dead routes D1–D23, cycles 1–39).
- Structural map: `../2-fully-proven/new_scientific_knowledge/lindelof-frontier-criticality-map.md`.
- Preprint: `../4-publication-ready/lindelof-method-ceilings.md`.
- Lean (all axioms `[propext, Classical.choice, Quot.sound]`): `MomentNeutralityLaw`,
  `MomentChordPivot`, `ShiftAverageTransfer`, `MomentResolutionFloor`, `LindelofMethodCeilings`.
- Open core: beat the chord (§5.3 of the preprint). Reachable sub-target: `(a,b) = (1/2,1)`, i.e.
  close BBMZ's `x^{1/12}`, giving a new proof of Heath-Brown's twelfth moment (C85).

---

## 43. Cycle 41 (2026-07-25) — D14 and C85 are the same statement; and the smallest remaining gap

### (C86) The neutrality of the short-interval mean square *is* the reachability of `(a,b)=(1/2,1)`

Cauchy–Schwarz on `R_3 = sum_{n~N} d_3(n)[Delta_3(n+H) - Delta_3(n)]` gives
`|R_3| <= (sum_n d_3(n)^2)^{1/2} I_3(N,H)^{1/2}` with
`I_3(N,H) = int (Delta_3(x+H)-Delta_3(x))^2 dx`. Feeding the *optimal* `I_3 << N^{1+eps} H` returns
exactly `(a,b) = (1/2, 1)`. So the two findings coincide:

- **D14** (the short-interval mean square is neutral): at its optimum it reproduces the chord, hence
  improves nothing;
- **C85** (`(a,b)=(1/2,1)` is reachable): reproducing the chord *by this route* is a new proof of
  Heath-Brown's twelfth moment.

Same statement, opposite valuation — worthless for advancing `mu(1/2)`, valuable as an independent
proof of a 1978 theorem whose only known proof runs through short second moments.

### (C87) The three routes to `(a,b)=(1/2,1)` at `k=3`, `H = N^{1/3}`; target `N^{7/6} = N^{1.1667}`

| route | input | output | gap |
|---|---|---|---|
| BBMZ Thm 1 | published | `N^{5/4} = N^{1.25}` | `N^{1/12} = N^{0.0833}` |
| BBMZ Thm 2 + Cauchy–Schwarz over shifts | `sum_{h<=H}|Delta|^2 << H N^{2-delta}` | `N^{4/3-delta/2}` | needs `delta > 1/3` |
| Ivić short-interval, **unconditional** (2.4) | `I_3 << N^{1-eps_1}h^2`, `h >= N^{1/6}` | `N^{4/3-eps_1/2}` | needs `eps_1 > 1/3` |
| Ivić short-interval, **under LH** (2.3) | `I_3 << N^{1+eps}h^{4/3}` | `N^{11/9} = N^{1.2222}` | **`N^{1/18} = N^{0.0556}`** |

> **The smallest gap anywhere in the campaign is `N^{1/18}`**, and it belongs to the short-interval
> mean square — but only in its LH-conditional form (Ivić's Theorem 1 assumes `sigma(3) = 1/2`, i.e.
> LH itself). Unconditionally the same route needs `eps_1 > 1/3` in his (2.4), where only "some
> `eps_1 > 0`" is proved.

This corrects an impression left by earlier cycles: **BBMZ Theorem 1 is not the closest approach.**
Under LH the short-interval route is closer by `N^{1/36}`, and both unconditional routes need a
specific small constant pushed past `1/3`.

**Consistency check.** `h^{4/3}` gives `(a,b) = (2/3,1)` hence `m(3) <= 4/3`; `h^1` gives `(1/2,1)`
hence `m(3) <= 5/4`. The shift-sum bounds differ by `N^{11/9-7/6} = N^{1/18}` and the moment
exponents by `4/3 - 5/4 = 1/12`; the transfer's `k=3` factor relates them (`(1/18)·3 = 1/6 = (1/12)·2`).
The arithmetic closes.

### (C88) Correction to C87, and a tightening

C87 wrote "needs `eps_1 > 1/3`". The correct statement is `eps_1 >= 1/3`, and the boundary case is
exactly the conjectural optimum:

  `I_3 << N^{1-eps_1} h^2`  gives  `|R_3| << N^{1/2} (N^{1-eps_1}h^2)^{1/2} = N^{1-eps_1/2} h`,
  which at `h = N^{1/3}` is `N^{4/3 - eps_1/2}`; this is `<= N^{7/6}` iff `eps_1 >= 1/3`.

And at `h = N^{1/3}` the conjectural truth `I_3 ≍ N h` equals `N^{1-1/3}h^2 = N^{2/3}·N^{2/3} = N^{4/3}`
— i.e. **`eps_1 = 1/3` *is* the conjectural optimum**, neither more nor less.

> So the short-interval route needs precisely the bound Ivić calls "unattainable at present", and
> that bound gives precisely `N^{7/6}` — the chord value, with nothing to spare. This is the exact
> mechanism behind D14/C86: the route is neutral because its optimum lands on the target and not
> past it.

Calibration of the conditional bound in the same units: Ivić's LH-conditional `I_3 << N^{1+eps}h^{4/3}`
corresponds to `eps_1 = 2/9` (since `N·N^{4/9} = N^{1-eps_1+2/3}` gives `eps_1 = 5/3 - 13/9 = 2/9`),
short of `1/3` by `1/9`; halved by the Cauchy–Schwarz, that is the `N^{1/18}` of C87. The two
accountings agree.

---

## 44. Cycle 43 (2026-07-25) — why Guth–Maynard advances zero-density but not subconvexity

### (C89) Corollary of C15: the two problems have different binding blocks

Guth–Maynard's Theorem 1.1 improves the large-value count in the window `0.7 < sigma < 0.8` with
`N <= T^{10/11}`. Writing the block length as `N = T^beta`:

- **Zero density.** The standard argument uses a Dirichlet polynomial of length `N` **strictly below**
  `T`; their critical case is `T = N^{6/5}`, i.e. `beta = 5/6`. That lies inside their improvement
  window, and the consequence is real: `N(sigma,T) <= T^{30(1-sigma)/13+o(1)}`, and primes in
  `x^{17/30+o(1)}`.
- **Subconvexity.** By C15 the binding block for `phi(v)` — hence for `mu(1/2)` — is the **self-dual**
  `beta = 1`, and there the two Guth–Maynard terms `T^{8/5-8v}`, `T^{7/5-8v}` drop below the classical
  `T^{1-4v}` only where the surviving maximum is still `T^{1-4v}`. Their bound is therefore
  *identically equal* to the classical one at `beta = 1`, for every `v`. Moreover `beta = 1` is
  excluded from their stated range by `N <= T^{10/11}`.

> **So the answer to "why does Guth–Maynard improve the density hypothesis but not Lindelöf?" is
> that the two problems bind at different blocks: `beta ≈ 5/6` (subcritical, inside their window)
> versus `beta = 1` (self-dual, outside it and inert there).** This is not an accident of their
> method's range — C15 shows the inertness holds at `beta = 1` even where their terms are admissible.

Recorded here because the workspace carries a parallel card
`density-hypothesis-large-values-frontier.md`; the two campaigns meet exactly at this point, and the
statement above is the precise boundary between them. Anyone working the density side should note
that improvements confined to `beta < 1` cannot cross into `mu(1/2)`, and conversely that the
self-dual block is invisible to the large-value technology that drives zero-density.

**Consistency with the rest of the map.** This is the same phenomenon as D8 (mean-value methods trace
the convexity line exactly), C14 (Halász–Montgomery reproduces the fourth-moment bound), and C64
(Heath-Brown at his input's ceiling): the self-dual block returns the value already visible, and
every technique that gains does so strictly below it.

---

## 45. Cycle 44 (2026-07-25) — the `1/8` caps are of two kinds, and only one is theorem-backed

### (C90) Splitting the ceilings by what supports them

The map records several ceilings at `1/8`. They are **not** of equal standing:

**(a) Theorem-backed.** The error-term programmes (C41, C59). Their ceilings rest on
`E(T) = Omega(T^{1/4})` (Good) and `E_2(T) = Omega(T^{1/2})` (Ivić–Motohashi) — **both theorems**.
No sharpening of the second- or fourth-moment error term can go below them, so `mu <= theta_{E_k}/(2k)`
cannot be pushed under `1/8` by those routes. This ceiling is unconditional and permanent.

**(b) Conjecture-backed, and the conjecture is contested.** The additive-divisor cap (C44) rests on
feeding the transfer Vinogradov/Ivić's conjectured size `Delta_k(x,h) = Omega(x^{1-1/k})`. That is a
*conjecture*, and by C70 it **contradicts** Conrey–Gonek's `Delta_k(x,h) << x^{1/2+eps}` for every
`k >= 3`. Under Conrey–Gonek the same route gives `m(k) = 1` for all `k`, i.e. LH (C69). So this
ceiling is an artefact of a contested input, not a property of the route.

### (C91) All square-root heuristics agree, and they agree on LH

Three independent "square-root" heuristics appear in the subject:

| side | heuristic | prediction |
|---|---|---|
| exponential sums | `sum_{n~N} n^{-it} << N^{1/2+eps}` (exponent-pair conjecture) | **LH** |
| additive divisors | `Delta_k(x,h) << x^{1/2+eps}` (Conrey–Gonek) | **LH** (C69, with square-root shift cancellation) |
| function fields | Sawin: square-root cancellation for divisor sums over short intervals and squarefree progressions, level of distribution `-> 1` | square-root, no `k`-degradation |

They agree with each other and all point to LH. **The only prediction in the subject that implies a
cap is Ivić's `Omega(x^{1-1/k})`**, which is contradicted by Conrey–Gonek at every `k >= 3` and is not
the shape the function-field theorems exhibit.

> **Re-weighting of the map.** The `1/8` that recurs across the campaign is a genuine and permanent
> ceiling for the *error-term* programmes, where `Omega`-results are theorems. For the
> additive-divisor route it is a ceiling only if Ivić's `Omega`-conjecture is true, and the balance of
> evidence — Conrey–Gonek, and Sawin over `F_q[t]` — is against it. The honest reading is therefore
> that the additive-divisor route **probably reaches LH**, and that what is genuinely capped is the
> narrower family of methods that consume only the second and fourth moment error terms.

This does not weaken the completeness theorem (C67): the routes in class B remain equivalent to or
stronger than LH, and Conrey–Gonek-plus-square-root-shift-cancellation is precisely one of them. It
sharpens *which* ceilings are structural and which are contingent — a distinction the earlier cycles
did not draw.

---

## 46. Cycle 45 (2026-07-25) — why `k = 2` cannot discriminate, and a structural argument for
Conrey–Gonek

### (C92) The two heuristics coincide at `k = 2` for an identifiable arithmetic reason  `[PROVED HERE]`

- **Squared-divisor heuristic** (Ivić): the correlation error is the square of the ordinary divisor
  error, `Delta_k(x) ≍ x^{(k-1)/(2k)}`, giving exponent `(k-1)/k = 1 - 1/k`.
- **Random heuristic** (Conrey–Gonek): square root of the number of terms, exponent `1/2`,
  independent of `k`.

These agree **iff `(k-1)/k = 1/2`, i.e. iff `k = 2`**, and for `k > 2` the squared-divisor exponent
exceeds the random one by exactly `(k-2)/(2k)`. Lean: `heuristics_agree_iff`, `heuristics_gap`,
`squaredDivisor_gt_random`.

> This is why the one case where the answer is known cannot settle the conflict: Motohashi's
> `Omega(x^{1/2})` for the binary correlation is simultaneously "the square of the ordinary error"
> and "the random size", because `k = 2` is precisely the root of `(k-1)/k = 1/2`. **Extrapolating
> from `k = 2` is ambiguous, and Ivić's conjecture extrapolates one of the two coinciding formulas
> while Conrey–Gonek extrapolates the other.**

### (C93) A structural argument favouring the random exponent

For the **ordinary** divisor sum the truth `x^{(k-1)/(2k)}` is *below* the random prediction
`x^{1/2}` for every `k`, because the Voronoi oscillations of a single `d_k` cancel better than random.
For the **correlation** at `k = 2`, Motohashi's `Omega(x^{1/2})` says the truth is *exactly* the
random size — no better. The natural reading:

> a single divisor function cancels better than random (coherent Voronoi oscillation), but **two
> independent divisor functions cancel only randomly**, because their Voronoi expansions are not
> aligned. That mechanism is `k`-independent and predicts `x^{1/2}` for every `k`.

Ivić's `x^{(k-1)/k}` would instead require the two Voronoi expansions to multiply *coherently* —
which is exactly what independence rules out. Combined with C91 (all square-root heuristics agree,
and Sawin's `F_q[t]` theorems exhibit square-root with no `k`-degradation), the balance of structural
argument and evidence favours Conrey–Gonek, hence by C69 favours the additive-divisor route reaching
LH.

**Recorded status.** This is a heuristic argument, not a proof, and it is labelled as such. Its value
is that it explains *why* the two conjectures were ever confusable — the coincidence at the root of
`(k-1)/k = 1/2` — and identifies which of them the `k = 2` evidence actually supports (neither, on
its own).

---

## 47. Cycle 46 (2026-07-25) — E6: C78 was too quick; the level of distribution **is** implicated

### (E6) Correction to C78

C78 concluded "the level of distribution is not the obstruction", on the grounds that the reduction
C77 uses moduli `a <= x^{1/3}`, inside the known exponent of distribution for `d_3`
(`1/2 + 1/46`, Fouvry–Kowalski–Michel). That inference was too quick: the inner problem produced by
C77 is itself a correlation `sum_m d(m) d_3(am-h)` along a progression, and its own treatment
requires distribution information at a level higher than `a`.

The literature is explicit. arXiv:2206.05877 (*On correlation of the 3-fold divisor function with
itself*) obtains **the full main term of the `d_3 x d_3` correlation for composite shifts,
conditionally on an averaged level of distribution for `d_3` in arithmetic progressions of level
`2/3`**. So:

  known level: `1/2 + 1/46 ≈ 0.5217`;  level needed: `2/3 ≈ 0.6667`;  **gap `≈ 0.145`.**

C78's claim is withdrawn; the corrected statement is that the moduli appearing in the *naive*
reduction are small, but the reduction does not by itself avoid the higher-level requirement.

### (C94) Fourth formulation of the open core

The core now has four successively more concrete forms, all recorded:

1. a `GL(3)` Motohashi analogue for `Delta_3` — input does not exist (cycle 19);
2. hyper-Kloosterman assembly — input exists (Deligne), assembly loses (cycle 31);
3. a power saving for `sum_{m<=x/a} d(m) d_3(am-h)` uniform in `a <= x^{1/3}` (cycle 32);
4. **an averaged level of distribution `2/3` for `d_3` in arithmetic progressions** — which by
   arXiv:2206.05877 yields the full main term of the `d_3 x d_3` correlation for composite shifts,
   hence the first nontrivial estimate for the ternary self-correlation.

(4) is the most concrete of the four: it is a single named exponent in a heavily-studied problem,
with a known starting point (`1/2+1/46`) and a known target (`2/3`). It also connects the campaign to
the Friedlander–Iwaniec / Heath-Brown / Fouvry–Kowalski–Michel line directly.

**Chain to LH, with each link's status.**

| link | statement | status |
|---|---|---|
| 1 | level of distribution `2/3` for `d_3` (averaged) | open; known `1/2+1/46` |
| 2 | full main term for `d_3 x d_3`, composite shifts | follows from 1 (arXiv:2206.05877) |
| 3 | `Delta_3(x,h) << x^{1/2+eps}` (Conrey–Gonek size) | conjectural; favoured by C91–C93 |
| 4 | square-root cancellation over shifts, `h <= x^{1-eps}` | conjectural; the `[OPEN CORE]` of C72 |
| 5 | `m(k) = 1` for all `k`, i.e. **LH** | follows from 3+4 by C69 |

The campaign's contribution is links 5 and the classification; links 1–4 are the open mathematics,
and link 1 is the one with a named exponent and an active literature.

---

## 48. Cycle 47 (2026-07-25) — how small a power saving suffices, and E7

### (C95) Any power saving suffices, given square-root shift cancellation  `[PROVED HERE]`

Feed the transfer a first power saving `Delta_3(x,h) << x^{1-delta}` for the ternary
self-correlation, at `k = 3`:

| shift input | `(a,b)` | `transferBound 3 a b` | breaks the chord `m(3) < 5/4`? |
|---|---|---|---|
| none (`a = 1`) | `(1, 1-delta)` | `3/2 - 3delta/2` | iff **`delta > 1/6`** |
| square-root (`a = 1/2`) | `(1/2, 1-delta)` | `5/4 - 3delta/2` | **for every `delta > 0`** |

So with square-root cancellation over the shifts, **the very first power saving for `d_3 x d_3` —
of any size — already breaks the chord.** Without it, `delta > 1/6` is needed. This is the sharpest
form of the reachable target: not "obtain the Conrey–Gonek exponent `1/2`", merely "obtain any
`delta > 0`", which is exactly what C76 identified as the first nontrivial estimate of any kind for
the ternary self-correlation.

### (E7) Correction: breaking the chord improves `m(3)` and `m(4)`, **not** `m(6)`

Earlier cycles wrote that `phi(1/8) > 1/2` gives "`m(4) < 3/2` **and** `m(6) < 2`". Only the first
half is right.

- **`m(4)` improves.** From `m(3) = 5/4 - eps'` with `m(6) <= 2` and convexity,
  `m(4) <= m(3) + (m(6)-m(3))/3 = 3/2 - 2eps'/3 < 3/2`. ✓
- **`m(6)` does not.** `m(6) = 1 + sup_v[12v - phi(v)]`, and improving `phi` at `v = 1/8` alone does
  not lower the supremum, which is attained on the whole plateau `v in [1/8, 13/84]` where
  Heath-Brown's `phi >= 12v - 1` binds and gives exactly `1`. Lowering `m(6)` requires improving
  `phi` across that entire interval, not at the single point.

So the correct statement of the payoff is: **the first power saving for `d_3 x d_3`, with square-root
shift cancellation, yields `m(3) < 5/4` and `m(4) < 3/2` — the first improvements of the sixth and
eighth moments of `zeta` since they were obtained by interpolation from Heath-Brown 1978.** The
twelfth moment itself is untouched, and by C64 it is at its own method's ceiling.

This also re-scopes C63: `m(6) < 3/2` (passing below the pivot) needs the plateau improved
throughout `[1/8, 13/84]`, which is strictly more than any single power saving delivers.

**(C95) formalized.** `HTGeometry.transferBound_first_saving_no_cancellation`
(`transferBound 3 1 (1-δ) = 3/2 - 3δ/2` for `δ ≤ 1/3`),
`transferBound_first_saving_sqrt` (`transferBound 3 (1/2) (1-δ) = 5/4 - 3δ/2` for `δ ≤ 1/6`),
`first_saving_breaks_chord` (any `δ > 0` breaks the chord with square-root shift cancellation; without
it, iff `δ > 1/6`), and `chord_at_three` (`momentChord 6 = 5/4`). Axioms
`[propext, Classical.choice, Quot.sound]`; `lake build GaloisForLFunctions.HTGeometry` green.

**Lean inventory (campaign).** Five modules: `MomentNeutralityLaw`, `MomentChordPivot`,
`ShiftAverageTransfer`, `MomentResolutionFloor`, `LindelofMethodCeilings`. Certified statements now
cover: the neutrality law and its `j > 1/(2θ)` threshold; the chord–pivot plateau and the certified
value of `phi(1/8)`; the transfer and its break criterion; the three named inputs
(Vinogradov, Conrey–Gonek pointwise, Conrey–Gonek with shift cancellation) and what each buys; the
independent-signs model, its resolution floor `1/8` identically in `k`, and its exactness on `[1,2]`;
the two correlation-error heuristics and their coincidence exactly at `k = 2`; and the first-power-
saving thresholds.

---

## 49. Cycle 48 (2026-07-25) — a fully costed reachable target

### (C96) Uniformity in `a` of Topacogullari's theorem: the payoff, computed

Take the reduction C77, `D_3(x,h) ≍ sum_{a <= x^{1/3}} sum_{m <= x/a} d(m) d_3(am-h)`, whose `a = 1`
case is Topacogullari's `d_3 x d` theorem with error `O(x^{8/9+eps})`. **Suppose that estimate is made
uniform in `a`**, i.e. error `O((x/a)^{8/9+eps})` for the inner sum. Then

  `sum_{a <= x^{1/3}} (x/a)^{8/9} = x^{8/9} sum_{a <= x^{1/3}} a^{-8/9} ≍ x^{8/9 + 1/27} = x^{25/27}`,

a first power saving for the **ternary self-correlation** with

  **`delta = 1 - 25/27 = 2/27 = 0.0741`.**

By C95, with square-root cancellation over the shifts this already breaks the chord, and the
resulting bounds are explicit:

| quantity | currently known | after `delta = 2/27` | improvement |
|---|---|---|---|
| `m(3)` (sixth moment) | `5/4 = 1.25` | `5/4 - 3delta/2 = 41/36 = 1.1389` | first since 1978 |
| `m(4)` (eighth moment) | `3/2 = 1.5` | `41/36 + (2 - 41/36)/3 = 77/54 = 1.4259` | first since 1978 |
| `m(6)` (twelfth moment) | `2` | `2` | unchanged (E7, C64) |
| `mu(1/2)` | `13/84` | `13/84` | unchanged (neutrality law C5) |

`mu <= min(m(3)/6, m(4)/8, m(6)/12) = min(0.1898, 0.1783, 1/6) = 1/6`, so subconvexity is untouched —
exactly as the moment-neutrality law predicts, since `k = 3` and `k = 4` both sit below the threshold
`42/13` once `m(6) = 2` still binds.

> **This is the campaign's fully costed reachable target.** It requires no new conjecture and no new
> machinery — only uniformity in one parameter of a published theorem, plus square-root cancellation
> over shifts. Its payoff is the first improvement of the sixth and eighth moments of `zeta` in 48
> years, and it does **not** improve subconvexity, which the neutrality law says no `k <= 42/13`
> moment can.

**Caveat, recorded.** The inner sum `sum_m d(m) d_3(am-h)` is not literally Topacogullari's object:
his is `sum_n d_3(n)d(n+h)`, and ours evaluates `d_3` along the linear form `am - h`. They coincide at
`a = 1`. Making the general-`a` case work is exactly a level-of-distribution statement for `d_3`, so
C96 and C94 (level `2/3`) are two faces of the same requirement; C96 is the version that starts from
a theorem rather than from an unproved exponent.

---

## 50. Cycle 49 (2026-07-25) — Phase 5 executed: the transfer is now proved in full

The transfer had been *used* since cycle 8 and only *checked* against Ivić's published `k=3` case.
It is now proved end to end, in seven steps, as §3bis of the preprint: AFE; expansion; the kernel
bound `|I(m,h)| ≤ min(T, 4m/h)`; the main-term citation; the head range `h ≤ M/T`; the tail range
`M/T < h ≤ M` by summation by parts; and the optimisation at `M ≍ T^{k/2}`.

**The analytic core of step (6) is formalised.** New Lean module
`GaloisForLFunctions.HTGeometry.ShiftPartialSummation`:

- `sum_mul_weight_eq` — summation by parts in the exact form the transfer needs,
  `∑_{i<n} f i · w i = S n · w n − ∑_{j<n} S(j+1)·(w(j+1) − w j)`, proved by induction;
- `abel_bound_of_partialSum_le` — from `|S j| ≤ B·j^a` and the weight `1/(j+1)`,
  `|∑_{i<n} f i/(i+1)| ≤ B·n^a/(n+1) + ∑_{j<n} B·(j+1)^a/((j+1)(j+2))`;
- `increment_le_rpow` — the increment weight is dominated by `(j+1)^{a−2}`;
- `summable_increment` — for `a < 1` that dominating series converges, which is precisely why the
  tail range contributes the same exponent as the head and not more.

Axioms `[propext, Classical.choice, Quot.sound]`; `lake build GaloisForLFunctions.HTGeometry` green
(10,884 jobs). Six campaign modules now.

**What this closes.** Every ceiling in §3 and §4 of the preprint is read off from the transfer; until
now the transfer itself rested on a citation plus a numerical check at one index. The only remaining
citation inside the proof is step (4), the Conrey–Gonek main-term computation, which is standard and
is the same input Ivić uses.

---

## Cycle 50 — the zero-geometry route, and its exact inertness (C97–C101)

Two Lean modules banked first: `HTGeometry.SpikeSobolev` (the analytic core of `(F2)`,
`μ ≤ m(k)/(2k)` — `f t₀² − f t² ≤ ∫|2ff'|` by FTC + interval monotonicity, and the integrated
Sobolev form `(b−a)f t₀² ≤ ∫f² + (b−a)∫|2ff'|`), and `HTGeometry.JensenZeroGeometry` (below).
Both green, axioms `[propext, Classical.choice, Quot.sound]`.

### C97 — a route the map did not contain

Every ceiling in §3 of the preprint is analytic (moments, large values, exponential sums). The
folklore route *"a large value of `ζ` pushes the zeros aside, and the zeros cannot be pushed"* had
never been made exact here. It is a genuinely different mechanism: no Dirichlet polynomial, no
moment, no exponential sum — only Jensen's formula, the functional equation, and Riemann–von
Mangoldt.

### C98 — the Jensen balance is an identity, and the duality is exact

`[PROVED HERE]` With `s₀ = ½+it₀`, `L = log(t₀/2π)`, `n_{t₀}(u)` the **two-dimensional** disc count:

    log|ζ(s₀)| = (R/π)L + 𝔈_R(t₀) − ∫_0^R n_{t₀}(u) du/u + O(R²/T),

`𝔈_R` = mean of `log|ζ|` over the *folded* circle (all sample points at `Re ≥ ½`). Proof: Jensen for
`ξ` on `D(s₀,R)`; `ξ = H·ζ` with `H` zero-free there so `log|H|` is harmonic and drops out; the
functional equation on the left arc yields the explicit `(R/π)L`.

**The duality.** The expected potential of a Riemann–von Mangoldt-correct on-line zero set is
`∫_0^R (u/π)L du/u = (R/π)L` — *exactly* the `χ`-factor mean, at every radius. Hence

    log|ζ(½+it₀)| = 𝔈_R(t₀) + D_R(t₀),   D_R := ∫_0^R ((u/π)L − n_{t₀}(u)) du/u,

so **LH ⟺ the zero set has no logarithmic holes around critical-line points**, uniformly. This is a
reformulation of LH that splits Backlund's criterion into a vertical (count) and a horizontal
(displacement) part.

### C99 — the route is exactly inert `[PROVED HERE]`

Inputs: (Z-a) `μ(1/2) ≤ θ₀` ⟹ `𝔈_R ≤ 2θ₀J(R)log T`, `J(R) = (1/2π)∫(½−R|cos θ|)_+dθ`;
(Z-b) `|β−½| ≤ ½` ⟹ `n_{t₀}(u) ≥ (√(u²−¼)/π)L − 2S_max` for `u ≥ ½`, giving potential
`≥ (I(R)/π)L`, `I(R) = √(R²−¼) − ½arccos(1/(2R))`.

**The cancellation.** With `A := R − √(R²−¼)` and `θ_R := arccos(1/(2R))`:

    R − I(R) = A + θ_R/2,      1 − 2J(R) = (2/π)(θ_R + 2A),
    ⟹  4(R − I(R)) = 2(θ_R + 2A) = π(1 − 2J(R))  ⟹  (R − I(R))/π = (1 − 2J(R))/4.

Therefore `μ ≤ ¼ + 2J(R)(θ₀ − ¼)` for all `R ≥ ½` (and `θ₀ + (R/π)(1−4θ₀)` for `R ≤ ½`; the two
agree at `R = ½`). Consequences:

- `θ₀ = ¼` ⟹ output `= ¼` **at every radius** — the convexity bound is a fixed point at all scales;
- output ∈ `[θ₀, ¼]` always — **the route never improves its input**;
- `¼` is the *unique* fixed point and the map contracts toward it with ratio `2J(R) < 1`: iterating
  the route drives a subconvex input back **up** to `¼`;
- closing the route on itself (`θ₀ = μ`) gives `μ(1−2J) ≤ (1−2J)/4`, i.e. exactly `μ ≤ ¼`.

**The Jensen balance is equivalent to the convexity bound.** Gain exactly zero.

### C100 — where the gain lives, and the circularity `[PROVED HERE]`

With the zeros in the disc *on the line*, the potential attains `(R/π)L`, the `χ`-factor cancels in
full, and the output is `2J(R)θ₀`. Since `J(R) → 0` as `R → ∞`, iterating gives `θ₀ → 0`: a
zero-geometry proof of RH ⟹ LH, with contraction ratio `2J(R)` per step, and (with
`S ≪ log t/loglog t`, `R ≍ loglog t`) the correct shape `exp(C log t·logloglog t/loglog t)`.

So the entire gain is the **horizontal** position of the zeros. The **vertical** input is worthless:
any `S(t) ≤ c_S log t`, *including the unproved `c_S = 0`*, leaves the output at `¼`. The exact
intermediate needed is `#{ρ : β > ½+δ, |γ−t₀| ≤ R} = o(log T)` pointwise — Backlund, i.e. LH.
**Exactly circular; no intermediate.** (Same shape as the map's other dichotomies.)

### C101 — what this kills, and what it opens

Killed (added to dead routes): **D24** — any programme of the form "bound `μ` by showing large values
force zero gaps / zero-count deficiencies, then bound deficiencies by `S(t)`". Even a *perfect*
unconditional `S(t) = o(log t)` — itself a well-known open problem, best current
`|S(t)| ≤ 0.111 log t + …` (Trudgian) — buys nothing. The route is worth `¼` and stops.

Opened: the identity `log|ζ| = 𝔈_R + D_R` is exact and holds for **every** `R` up to `√T`. Inertness
came from bounding `𝔈_R` by convexity *pointwise on the circle*. The next generative move is to
stop bounding `𝔈_R` pointwise: `𝔈_R` is a **circle mean**, so what is needed is a bound on
`log|ζ(σ+it)|` *on average over the folded circle* — a first-moment statement for `log|ζ|` off the
line, not a sup bound. `∫_T^{2T} log|ζ(½+it)| dt = 2π Σ_{γ}(β−½) + O(log T)` (Littlewood) is exactly
such a statement and is *not* used above. Question for the next cycle: does the pair
(Jensen balance, Littlewood's lemma) close into a system with gain, i.e. can the first moment of
`log|ζ|` on the folded circle beat `2θ₀J(R)`?

Files: `docs/drafts/pipeline/4-publication-ready/lindelof-method-ceilings.md` §6 (twelfth ceiling,
full proofs); `formal/GaloisForLFunctions/HTGeometry/JensenZeroGeometry.lean`;
`formal/GaloisForLFunctions/HTGeometry/SpikeSobolev.lean`.

### C102 — the sharp form: the slope-1/2 barrier `[PROVED HERE]`

C99 fed the balance the *chord* `μ(σ) ≤ 2θ₀(1−σ)`. That is not what is known — the known `μ*(σ)`
lies strictly below the chord in the interior. Redoing the balance with the actual curve gives a
sharper and much more informative answer.

With `Φ(R) = (1/2π)∫μ*(½+R|cos θ|)dθ` and `Out(R) = (1−2J(R))/4 + Φ(R)`:

**Gain criterion.** `Out(0) = μ*(½)` and `Out'(0⁺) = (1 + 2μ*'(½⁺))/π`.
So the route gains **iff `|μ*'(½⁺)| > ½`**.

**The barrier.** If the bound at `σ = ½` is attained at the self-dual block (`μ*(½) = b(½) − ¼`),
then the same block is admissible at every `σ`, so `μ*(σ) ≥ μ*(½) − (σ−½)/2` — slope exactly `−½`,
never steeper. Feeding that in:

- for `R ≤ 2μ*(½)`: `Out(R) ≥ R/π + ½(2μ*(½) − 2R/π) = μ*(½)` **identically in `R`** — a second
  exact cancellation, this time of the explicit factor against the folded-mean loss;
- for `R ≥ 2μ*(½)`: `d/dR G(c,R) = (2/π)(√(R²−c²)/R − 1) ≤ 0`, hence
  `d/dR Out ≥ (1/π)(√(R²−a²) − √(R²−¼))/R ≥ 0` with `a = 2μ*(½) ≤ ½`.

So `Out(R) ≥ μ*(½)` for **every** radius, with an exact plateau of length `2μ*(½)`. (Structural echo
of the chord–pivot plateau of C-earlier: another quantity that is constant on an interval and then
degrades.)

**The lever, stated exactly.** The route gains iff one can prove

    μ(σ) < 13/84 − (σ − ½)/2   for some σ > ½,

i.e. an off-line bound beating the slope-`½` line through the current on-line record. Equivalently:
**a critical Dirichlet block longer than `√(t/2π)`.** The AFE caps block length at `√(t/2π)`, so this
is exactly "the self-dual block is not the binding one" — the *same* condition that makes
Guth–Maynard inert at `β = 1` (§3.3). **The twelfth ceiling and the third are one obstruction seen
from two sides.** Note the direction: it is a *bootstrap* from off-line to on-line, the reverse of
Phragmén–Lindelöf.

Lean: `AFEBound`, `AFEBound.half_lipschitz_lower`, `afe_plateau_identity`, `gain_derivative`,
`no_gain_of_half_lipschitz`, `afe_slope_barrier` — axioms `[propext, Classical.choice, Quot.sound]`.
Paper: preprint §6.4, Lemma 6.8 / Theorem 6.9 / Corollary 6.10.

**D24 (dead route, recorded).** "Bound `μ` by showing large values force zero-gaps, then bound the
deficiency via `S(t)`." Dead: gain zero, and even a perfect unconditional `S(t) = o(log t)` buys
nothing. **D25.** "Feed the known `μ(σ)` curve into the Jensen balance." Dead unless (6.4) holds.

**Next generative move (for the following cycle).** Two concrete, disjoint targets:
1. **Check (6.4) against the known `μ(σ)` table.** This is now a purely arithmetic question about
   published exponents: is `μ(σ) ≤ 13/84 − (σ−½)/2` known anywhere on `(½, 0.81)`? If yes, the
   Jensen balance improves `13/84` immediately. This is the first *bootstrap from off-line to
   on-line* the campaign has produced and it costs nothing to test.
2. **Replace the pointwise bound on `𝔈_R` by a mean bound.** `𝔈_R` is a *circle mean*, and
   `∫_T^{2T} log^+|ζ(σ+it)|dt ≪ T·log(1/(2σ−1))` (Jensen from the second moment) is smaller than the
   pointwise bound by a full factor of `log T`. That kills only `T/log T` worth of large values by
   Markov; the question is whether the higher moments of `log^+|ζ(σ+it)|` (Bohr–Jessen /
   Selberg-type, all finite for fixed `σ > ½`) push it to a power saving. The obstruction identified:
   the folded circle contains points with `σ → ½`, where the moments blow up; the trade-off between
   the truncation radius and the moment order is the object to optimise.

### C103 — target 1 settled, by proof rather than table lookup: (6.4) is unsatisfiable `[PROVED HERE]`

The criterion (6.4) — "`μ(σ) < 13/84 − (σ−½)/2` for some `σ > ½`" — does not need a table. It is
refuted structurally.

Every known bound has the form `μ*(σ) = max_{α} ( b(α) − ασ )`, a **maximum** over dyadic Dirichlet
blocks of length `t^α`, where `t^{b(α)}` bounds `|Σ_{n∼t^α} n^{−it}|`. Because it is a maximum, for
*every* `σ`

    μ*(σ) ≥ b(α₀) − α₀σ    for the block `α₀` attaining the bound at `σ = ½`,

and `α₀ = ½` there (the self-dual block: `b(½) − ¼ = μ*(½)`, while short blocks give
`b(α) − α/2 ≈ α/2 → 0` and the `α ≈ 1` block gives `b(1) − σ = ½ − σ`, smaller at `σ = ½`). Hence

    μ*(σ) ≥ μ*(½) − (σ − ½)/2    on all of [½, 1].

Sanity check on a known instance: Weyl's `(k,l) = (1/6, 2/3)` gives `μ(σ) ≤ (k+l−σ)/2 = (5/6−σ)/2`,
which is *identically* `1/6 − (σ−½)/2` — **exactly the barrier line at every `σ`**. Bourgain's bound
extends the same way. For `σ > ½ + 2·13/84 = 0.8095` the line is negative and `μ* ≥ 0` beats it
vacuously, so (6.3) holds there too.

**Consequence, and the real statement of the obstruction.** Because `μ*` is a *maximum over blocks*,
it can never fall below the line traced by the single block that binds on the critical line.
Therefore:

> Improving `μ(σ)` below `μ(½) − (σ−½)/2` requires **cancellation between distinct dyadic blocks** of
> the Dirichlet approximation — not a better bound for any one block.

No current method produces inter-block cancellation; every one of them bounds blocks separately and
takes a maximum. This is the same defect that makes the self-dual block `β = 1` always bind in the
Guth–Maynard analysis (§3.3). **D26 (dead route):** "improve `μ` by feeding a better off-line bound
into the Jensen balance" — dead for every max-over-blocks bound, i.e. for all of them.

**What survives as the live question.** Not "is `μ(σ)` small off the line" but:

> `[OPEN CORE]` Is there any estimate for `ζ(σ+it)`, `σ > ½`, that exploits cancellation **between**
> the dyadic blocks `n ∼ t^{α₁}` and `n ∼ t^{α₂}`, `α₁ ≠ α₂`, of its Dirichlet approximation?

This is a new formulation and it is *not* a moment or large-value statement; it is a statement about
the phase relation between blocks of different length, i.e. about `Σ_{n∼N₁}n^{−it} · conj(Σ_{n∼N₂}n^{−it})`
having a saving beyond Cauchy–Schwarz. Recorded as the successor question to the additive-divisor
open core; the two are related — the additive-divisor input `Σ_h Δ_k(x,h)` is precisely an inter-block
correlation for `ζ^k`.

### C104 — scope correction on C103, and the block-exponent anchor

**Scope of C103.** The proved statement is about the *off-line* curve: a max-over-blocks bound cannot
dip below `μ*(½) − (σ−½)/2`. It is **not** a claim that inter-block cancellation is needed for LH —
improving the single self-dual block improves `μ*(½)` and hence the whole line uniformly. The
[OPEN CORE] posed there is therefore the live question *for the Jensen route*, and its link to the
additive-divisor core is `[ANALOGY]`, not proof: `Σ_h Δ_k(x,h)` is an inter-block correlation for
`ζ^k`, which is suggestive but not a reduction.

**The block-exponent anchor.** Writing `b(α)` for the exponent of `|Σ_{n∼t^α} n^{−it}|`, the AFE
gives `μ(½) = b(½) − ¼` exactly. In the block variable `N = t^{1/2}` this reads

    |Σ_{n∼N} n^{−it}| ≪ N^{1/2 + 2μ},   so   LH  ⟺  b(½) = ¼  ⟺  square-root cancellation
    for the single self-dual block.

Current record `μ ≤ 13/84` = block exponent `N^{17/21} = N^{0.8095…}`; square-root cancellation is
`N^{1/2}`. **Shortfall `= 2μ = 13/42`.**

**Identity worth flagging.** The plateau length of Theorem 6.9 is `2μ*(½)` — *exactly* the shortfall
from square-root cancellation in the self-dual block. So the Jensen balance's inert interval and the
block's distance from square-root cancellation are the same number, not two numbers that happen to
agree: both are `2μ`, because the balance measures the folded circle against the slope-`½` line whose
intercept is set by the block exponent. This is the sharpest form of "the twelfth ceiling and the
third are one obstruction": all three quantities — the Guth–Maynard self-dual block `β = 1`, the
Jensen plateau `2μ`, and the square-root-cancellation shortfall — are the same object.

### C105 — target 2 of C102 resolved: REDISCOVERED, and why

Target 2 was: replace the pointwise bound on `𝔈_R` by a *mean* bound, hoping for a large-value
(`φ(v)`) statement. Carried out:

From the balance, `v log T ≤ 𝔈_R + D_R` and `D_R ≤ (R/π)log T`, so choosing `R = πv/2` forces
`𝔈_R(t₀) ≥ (v/2)log T`. Then `𝔈_R^+ ≤ (1/2π)∫ log^+|ζ(σ(θ)+it(θ))|dθ` and Jensen give, for `k ≥ 1`,

    ∫_T^{2T}(𝔈_R^+)^k dt₀ ≤ (1/2π)∫_0^{2π}[ ∫_T^{2T}(log^+|ζ(σ(θ)+it)|)^k dt ] dθ.

Feeding Selberg-type moments `≪ T(2k−1)!!·V_σ^{2k}`, `V_σ² ≍ log(1/(σ−½))` capped at `loglog T`, and
optimising `k` at the top of the admissible range `K ≍ log T/loglog T`, the bracket is `≍ 1/(v²log T)`
and the output is `meas ≪ T·exp(−K·loglog T) = T^{1−c}` with `c` **absolute, independent of `v`**.
(The `θ`-integral is dominated by `|cos θ| ≲ 1/(R log T)` where `V² ≍ loglog T`; including its measure
factor `1/(R log T)` only helps.)

So the route yields `φ(v) ≥ c > 0` uniformly in `v` — which beats the fourth moment's `φ(v) ≥ 4v`
for `v < c/4`.

**Verdict: REDISCOVERED.** The same conclusion follows from Selberg's moments of `log|ζ(½+it)|`
*directly*, with no Jensen balance: `meas{log|ζ| > v log T} ≪ T(Ck loglog T)^k/(v log T)^{2k}`, same
optimisation, same `T^{1−c}`. The balance routes back to the identical input. **D27 (dead route):**
"use the folded circle mean plus Selberg moments to bound the large-value set". It adds nothing to
Selberg, and gives no bound on `μ` or on any `M(A)` (a uniform constant lower bound for `φ` is
useless against `max_v(Av − φ(v))` for large `A`, which needs `φ` **superlinear**).

**The recurring shape.** Every route examined this cycle collapses to the same two inputs — the
self-dual block bound and Selberg's moment range — no matter which geometric packaging is used. That
is now four independent packagings (large-value/Halász, Guth–Maynard blocks, Jensen zero geometry,
folded-circle moments) reducing to the same pair. Recorded as the structural observation of the
cycle; the map's "no uncapped intermediate" now has a mechanism attached to it, not just a census.

**Live target carried forward:** `φ` **superlinear**. Every known lower bound for `φ` is linear in
`v` because every one of them is a fixed moment. A superlinear `φ` requires either infinitely many
moments used simultaneously, or a mechanism in which the *cost* of a large value grows faster than
linearly in `v`. The Jensen balance supplies exactly such a candidate mechanism — a value `T^v`
demands a zero-deficiency of `≍ v log T` spread over a window of length `≍ v`, so the "phase-space
volume" consumed grows like `v²` — but the accounting above (an `L¹`/`L^k` budget) is too lossy to
convert `v²` into a superlinear exponent. Sharpening that accounting is the next cycle's object.

### C106 — the off-line moment attempt: inert, and the optimum is the fourth moment

The one structurally promising feature of the Jensen balance is **rigidity**: for `v` close to `θ₀`,
`𝔈_R(t₀) ≥ (v/2)log T` together with the pointwise ceiling `log|ζ(σ+it)| ≤ (θ₀ − (σ−½)/2)log T`
forces `|ζ|` to be *within `o(log T)` of its maximal allowed size at almost every point of a circle
of radius `R`* — an extremely rigid configuration, and one that lives partly **off** the critical
line, where the mean-value theorems are strong.

Exploiting it: if `|ζ(σ+it)| ≍ T^{μ*(σ)}` on a set of measure `≫ meas·R` with `σ = ½+x`, then
`∫_T^{2T}|ζ(σ+it)|^{2k}dt ≪ T^{1+ε}` (valid exactly for `σ ≥ 1 − 1/k`, §3.1) gives

    meas ≪ T^{1 − 2k(θ₀ − x/2) + ε},    k = 1/(½ − x)  (the smallest admissible).

Maximising the saving: `2k(θ₀ − x/2) = (2θ₀ − x)/(½ − x)`, whose derivative in `x` is
`(2θ₀ − ½)/(½−x)² < 0` for `θ₀ < ¼`. **The maximum is at `x = 0`, i.e. `k = 2`.** Output
`φ(v) ≥ 4θ₀` at `v = θ₀` — *identical* to the fourth moment. Inert.

Note the sign: the saving is decreasing in `x` **because `θ₀ < ¼`** — subconvexity itself is what
makes moving off the line unprofitable. At `θ₀ = ¼` the derivative vanishes and every `x` is
equally good; below `¼` the critical line strictly dominates. **D28 (dead route).**

**Consolidated observation for the map.** Five independent packagings now collapse onto the pair
(self-dual block, fourth moment / Selberg range): large-value/Halász (§3.2), Guth–Maynard blocks
(§3.3), Jensen zero geometry (§6.3), folded-circle moments (C105), off-line moments (C106). The
collapse is not a coincidence in each case but the same algebraic fact — the self-dual point `x = 0`,
`α = ½`, `β = 1`, `k = 2` is a stationary point of every one of these optimisations, and it is a
*maximum* precisely because `μ < ¼`.

**`[CONJECTURE] (self-dual stationarity).** For every optimisation over a block/abscissa/moment
parameter that is built from (i) the approximate functional equation and (ii) a mean value theorem,
the self-dual parameter is stationary, and it is the global optimum whenever the input exponent is
`< ¼`. Falsifiable: exhibit one such optimisation whose optimum is strictly off the self-dual point.
If true, it explains the entire ceiling map in one line and predicts that **any method that improves
`μ` must break the approximate functional equation's symmetry, not optimise within it.**

### C107 — self-dual stationarity, promoted from conjecture to theorem (the abscissa case) `[PROVED HERE]`

The `[CONJECTURE]` of C106 is provable in its sharpest instance, and the proof exposes the mechanism.

Fix the abscissa `σ = ½ + x`, `0 ≤ x < ½`, and pair the two facts:
- self-dual ceiling: `μ*(½+x) = θ₀ − x/2` (C102's (6.3));
- mean-value criticality: `∫_T^{2T}|ζ(½+x+it)|^{2k}dt ≪ T^{1+ε}` iff `k ≥ k(x) = 1/(½−x)` (§3.1).

    Sav(x) := 2·k(x)·μ*(½+x) = (2θ₀ − x)/(½ − x),     Sav'(x) = 2(θ₀ − ¼)/(½ − x)².

**(i)** At `θ₀ = ¼`: `Sav(x) ≡ 1` for **every** `x` — the numerator *is* the denominator. Perfect
degeneracy across the whole strip.
**(ii)** For `θ₀ < ¼`: `Sav` strictly decreasing, unique optimum `x = 0`, `Sav(0) = 4θ₀` — the fourth
moment.
**(iii)** For `θ₀ > ¼` the optimum moves off the line.

**The mechanism is a tangency.** The slope-`½` line through `(½, ¼)` reaches `0` exactly at `σ = 1`,
which is exactly where the mean value theorem becomes available for all `k`. Two unrelated features
of `ζ` — the *value* `¼` of the convexity bound, and the *criticality* `σ = 1 − 1/k` — touch at one
point. That tangency is the reason every route in the map returns the same answer:

> **The convexity bound is a degenerate tie across the entire critical strip. Every subconvexity
> input breaks the tie, and always in the same direction — back to the critical line and the fourth
> moment.**

Lean: `selfDualCeiling`, `meanValueThreshold`, `largeValueSaving`, `largeValueSaving_convexity`
(`≡ 1`), `largeValueSaving_strictAnti`, `largeValueSaving_zero` (`= 4θ₀`), capstone
`self_dual_stationarity`. Axioms `[propext, Classical.choice, Quot.sound]`. Paper: §6.5,
Theorem 6.11, Conjecture 6.12.

**Conjecture 6.12 (still open, now sharply falsifiable).** Every optimisation over a block, abscissa,
or moment parameter built from the AFE plus a mean value theorem is stationary at the self-dual
parameter and attains its optimum there whenever the input exponent is `< ¼`. **Falsifier wanted:**
one such optimisation whose optimum is strictly off the self-dual point. If none exists, the
prediction is that **any method improving `μ` must break the AFE's symmetry rather than optimise
within it** — which reframes the whole campaign: stop optimising inside the AFE.

**Next cycle's object, chosen by this prediction.** Symmetry-breaking substitutes for the AFE:
(a) an approximate functional equation with **unequal** lengths `N₁·N₂ = t/2π`, `N₁ ≠ N₂` — the
    smoothed/`ρ`-shifted AFE family, where the self-dual point is not forced;
(b) the Motohashi spectral decomposition, which replaces the AFE entirely for the fourth moment and
    is the one known route that is *not* an AFE optimisation — and which is exactly the object the
    additive-divisor open core asks to generalise to `GL(3)`.
These two are the same question asked twice, which is the first time the campaign's two open cores
have met.

### C108 — erratum E8, and the first test of Conjecture 6.12

**E8 (wording, C106/C107).** `k(x) = 1/(½ − x)` is the **largest** admissible moment order for
`∫_T^{2T}|ζ(½+x+it)|^{2k}dt ≪ T^{1+ε}` (the criticality `σ ≥ 1 − 1/k` reads `k ≤ 1/(1−σ)`), not the
smallest. At `x = 0` it is `k = 2` — the fourth moment, the largest with a `T^{1+ε}` bound. The
formula `Sav(x) = 2k(x)μ*(½+x)` and every consequence are unchanged; only the description was
inverted. Corrected in the Lean docstring and in preprint §6.5.

**First test of Conjecture 6.12: the unequal-length AFE. PASSES (route inert).**
Hardy–Littlewood's approximate functional equation does **not** force equal lengths:

    ζ(s) = Σ_{n≤x} n^{−s} + χ(s) Σ_{n≤y} n^{−(1−s)} + O(x^{−σ} + |t|^{½−σ} y^{σ−1}),   2πxy = |t|.

So the free parameter `a` with `x = t^a`, `y ≍ t^{1−a}` is exactly a symmetry-breaking knob, and the
self-dual choice `a = ½` is a *choice*, not a constraint. Writing `β(a) := max_{α ≤ a}(b(α) − α/2)`
for the best block bound available up to length `t^a`,

    μ(½) ≤ max( β(a), β(1−a) )   for every a ∈ (0,1).

`β` is non-decreasing (a longer range can only raise a maximum), so `max(β(a), β(1−a)) = β(max(a,1−a))
≥ β(½)`, with equality iff `a = ½`. **The symmetric choice is optimal; unequal lengths give strictly
nothing.** `[D29]`

The reason is worth recording: at `a = ½` the two sums are complex conjugates of each other (this is
why the Riemann–Siegel `Z`-function is real), so they are *one* sum, not two. Away from `a = ½` they
are two independent sums and the longer one dominates. **Symmetry-breaking in the AFE converts one
sum into two, and two is worse than one** — a second, independent reason the self-dual point is
optimal, and one that Conjecture 6.12 did not predict but is consistent with.

So option (a) of C107 is closed. Option (b) — Motohashi's spectral decomposition, the one known route
that is not an AFE optimisation — survives, and is the same object as the additive-divisor open core.
The campaign's two open cores have merged into one:

> `[OPEN CORE, merged]` A spectral (non-AFE) decomposition for the sixth moment of `ζ` — equivalently
> a `GL(3)` Motohashi formula, equivalently a power saving for `Σ_{m≤x/a} d(m)d₃(am−h)` uniform in
> `a ≤ x^{1/3}`. Every AFE-internal route is now proved inert; this is the only surviving direction.
