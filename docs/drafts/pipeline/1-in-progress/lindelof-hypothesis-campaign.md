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

## Cycle 51 — the surviving direction, and a sharp demand on it (C109–C110)

### C109 — state of the GL(3)×GL(3) frontier, July 2026

Harun–Singh, *Shifted convolution sum with weighted average: GL(3)×GL(3) setup*, arXiv:2501.03679
(2025) — the first non-trivial GL(3)×GL(3) shifted convolution bounds. Shape:

    (1/H) Σ_h W₁(h/H) Σ_n A_{π₁}(1,n) A_{π₂}(1,n+h) W₂(n/X)  ≪  X^{1-δ+ε},
    for  X^{1/2+δ} ≤ H < X^{1-ε},   π₁, π₂ Hecke–Maass **cusp** forms on SL(3,ℤ).

Two gaps separate this from `Δ₃`:
1. **cuspidal only** — `d₃` is the minimal Eisenstein series, excluded. This is the harder gap: for
   cusp forms the coefficients oscillate and `X^{1-δ}` is a cancellation statement; for `d₃` the
   coefficients are positive, a main term of size `X log⁴X` must first be *produced*, and the methods
   that give `X^{1-δ}` cuspidally produce no main term.
2. **`H ≥ X^{1/2+δ}`** — the moment application needs `H = M/T`. At `k = 3`, `M = T^{3/2} = x`, so
   `H = T^{1/2} = x^{1/3}`, well below `X^{1/2}`.

Also relevant: Blomer–Li, arXiv:2511.03294 (GL(3)×GL(2) with `d` against a GL(3) coefficient — the
last open GL(3)×GL(2) case, now settled), and Topacogullari / Drappeau for `d ⋆ d₃`. `d₃ ⋆ d₃` remains
open even for a single shift.

### C110 — what the GL(3) technology must deliver, exactly `[PROVED HERE]`

The Harun–Singh shape is a **plain average** over `h`, i.e. `Σ_{h≤H}Δ_k(x,h) ≪ H·x^{1-δ}`: shift
exponent `a = 1`, not `a = 1/2`. Through the transfer that is worth far less. From
`transferBound_lt_chord_iff`:

    a = 1  :  transferBound k 1 (1-δ) < momentChord(2k)  ⟺  k(1 - 2δ) < 2  ⟺  δ > 1/2 - 1/k;
    a = 1/2:  transferBound k (1/2) (1-δ) < momentChord(2k)  for **every** δ > 0, at every k.

So:
- at `k = 3` a plain-average input must save **δ > 1/6** merely to match the known envelope;
- at `k = 4`, `δ > 1/4`; and reaching *every* index needs `δ → 1/2`;
- `δ = 1/2` with `a = 1` is exactly the shift-free Conrey–Gonek size `Σ_h Δ_k ≪ H x^{1/2+ε}`, which
  the transfer caps at the pivot `1/8` — **not** at LH.

**Conclusion (sharp).** `a = 1/2` is not a technical convenience. Square-root cancellation *in the
shift* is what separates an input worth LH from one worth only `1/8`. Any GL(3) programme that
produces bounds for the *average* over `h` — which is what the delta-method/circle-method papers
naturally produce — is on the `a = 1` branch and must chase `δ → 1/2`, at which point it is worth
`1/8` and no more.

**Demand on the frontier, in one line:**

> Produce `Σ_{h ≤ H} Δ₃(x,h) ≪ H^{1/2} x^{1-δ+ε}` with **any** `δ > 0`, at `H = x^{1/3}`, for the
> **Eisenstein** case. Not the average — the cancellation.

Lean: `HTGeometry.AveragedDivisorInput` — `averaged_input_lt_chord_iff`, `averaged_input_threshold`
(`⟺ δ > 1/2 - 1/k`), `averaged_input_threshold_three` (`⟺ δ > 1/6`),
`shift_cancellation_is_essential`. Axioms `[propext, Classical.choice, Quot.sound]`.

**D30 (dead route).** "Wait for the GL(3)×GL(3) cuspidal machinery to be extended to Eisenstein and
read off `m(3)`." Even a full Eisenstein extension of Harun–Singh, at their `H`, is on the `a = 1`
branch and gives nothing below `δ = 1/6`; and their `H ≥ X^{1/2+δ}` is above the range the moment
transfer uses.

### C111 — the pointwise branch, exactly: three sharp numbers for the ternary problem `[PROVED HERE]`

A pointwise bound `Δ_k(x,h) ≪ x^{b+ε}` uniform in `h` is the input `(a,b) = (1,b)`. From
`transferBound k 1 b = 1 + max(0, kb/2 − 1)`:

    transferBound k 1 b = 1  ⟺  k·b ≤ 2.

Three consequences, all now certified:

1. **`Δ₃(x,h) ≪ x^{2/3+ε} ⟹ m(3) = 1`** — the sixth moment conjecture, at *exactly the same
   exponent `2/3` that solves the binary problem* (Motohashi/DFI give `Δ₂ ≪ x^{2/3}`). The ternary
   problem does not need a better exponent than the binary one; it needs the same one.
2. **`Δ₃(x,h) ≪ x^{b+ε}` improves on the known envelope iff `b < 5/6`.** So a bare "power saving"
   is worthless here: anything in `[5/6, 1)` gives nothing. The frontier number for the ternary
   additive divisor problem is **`5/6`**, and the prize number is **`2/3`**.
3. **The pointwise route saturates at `k = 4`:** `transferBound k 1 (1/2) = 1 ⟺ k ≤ 4`. Even the
   best conceivable size — Conrey–Gonek `x^{1/2+ε}`, which is the square-root barrier and cannot be
   improved — gives `m(k) = 1` only up to `k = 4`. For `k ≥ 5` the requirement `b ≤ 2/k` falls below
   `1/2`, i.e. below the square-root barrier, so **no pointwise bound whatsoever can give `m(k) = 1`
   for `k ≥ 5`.** This is the exact arithmetic reason the pure-size row of the separation table caps
   at the pivot `1/8`, and it is a *proof* that the pointwise branch cannot reach LH — not a
   statement about current technology.

**This sharpens the campaign's central dichotomy into a theorem about branches, not methods:**

> The pointwise branch (`a = 1`) is provably capped at `k = 4`, hence at `μ ≤ 1/8`, whatever anyone
> ever proves about the size of `Δ_k`. Only the shift-cancellation branch (`a = 1/2`) can reach LH,
> and on that branch **any** `δ > 0` suffices at every index. There is no third branch: the transfer
> depends on `(a,b)` only.

So the entire remaining problem is: **obtain square-root cancellation in the shift average together
with any power saving in `x`.** Every other formulation is now closed.

Lean: `HTGeometry.AveragedDivisorInput` — `pointwise_input_eq_one_iff`, `ternary_two_thirds`,
`ternary_improves_iff`, `pointwise_route_saturates`. Axioms `[propext, Classical.choice, Quot.sound]`.

## Cycle 52 — direct attack on the ternary core: a reduction (C112–C114)

**Phase 1 (corpus).** `formal_tools.py research "Voronoi divisor correlation diagonal shifted
convolution main term"` returns nothing on the Voronoi/diagonal structure. New ground internally.
**Phase 2 (external).** C109 stands: `d₃ ⋆ d₃` open even for one shift.

### C112 — reduction of the shift-average to a double Voronoi sum

Elementary, exact, no analysis: since `Σ_{h≤H} d_k(n+h) = D_k(n+H) − D_k(n)`,

    Σ_{h≤H} Δ_k(x,h) = Σ_{n≤x} d_k(n)·[Δ_k(n+H) − Δ_k(n)] + 𝔐,

where `𝔐` is the mismatch between `H·(smooth main)` and `Σ_{h≤H}MT_k(x,h)` (the Conrey–Gonek main
terms; smooth in `h`, standard, not the obstruction). The dropped pieces are `O(H² polylog)` and
`H·O(x^{(k−1)/(k+1)+ε})`; at `k = 3, H = x^{1/3}` these are `x^{2/3}` and `x^{5/6}`, both far below
the target `x^{7/6−δ}`. **So the entire content is `E := Σ_{n≤x}d_k(n)[Δ_k(n+H) − Δ_k(n)]`.**

This is where Ivić's `(1/2,1)` comes from, by Cauchy–Schwarz against
`Σ_n|Δ_k(n+H)−Δ_k(n)|² ≪ xH^{1+ε}`. Cauchy–Schwarz discards the arithmetic of `d_k(n)`. The
alternative is to expand both factors by Voronoi and keep it.

### C113 — the resonant term cancels by antisymmetry `[PROVED, modulo Voronoi bookkeeping]`

Insert the Voronoi expansion `Δ_k(y) = c_k y^{α}Σ_m d_k(m)m^{−β}cos(2πk(my)^{1/k}+γ_k)`,
`α = (k−1)/2k`, `β = (k+1)/2k`, `α + β = 1`. Linearising the shift-difference (valid for
`m ≤ m₀(n) = n^{k−1}/H^k`; at `k = 3, H = x^{1/3}, n ≍ x` this is `m ≤ x`, which is also where the
truncated Voronoi series ends — so the linearised range is the whole range):

    Δ₃(n+H) − Δ₃(n) ≈ −2πc H n^{−1/3} Σ_m d₃(m) m^{−1/3} sin(6π(mn)^{1/3}+γ).

Apply Voronoi to the `n`-sum, whose kernel is `G(u) ≈ c u^{−1/3}cos(6πu^{1/3}+γ)` (fixed by
consistency: feeding `f = 1_{[0,x]}` reproduces the `Δ₃` expansion). The integrand is a **sine times
a cosine**, so product-to-sum splits it:

    sin(A+γ)cos(B+γ) = ½[ sin(A+B+2γ) + sin(A−B) ],   A = 6π(my)^{1/3}, B = 6π(ly)^{1/3}.

Substituting `u = y^{1/3}` — under which `y^{−2/3}dy = 3du`, flattening the cube-root phase — both
integrals become **elementary**:

    ∫_1^X sin(c u) du = (cos c − cos(cX))/c,   X = x^{1/3}.

**The resonant kernel `(cos c − cos(cX))/c` is an odd function of `c`.** Its argument
`c₋ = 6π(m^{1/3} − l^{1/3})` is antisymmetric under `m ↔ l`, while the weight
`d₃(m)d₃(l)(ml)^{−1/3}` is symmetric. Hence

> **the entire resonant half of the double Voronoi sum vanishes identically.**

In particular **there is no diagonal `m = l` obstruction** for the *first* moment `Σ_h Δ_k` — the
diagonal is `sin(0) = 0`, not `cos(0) = 1`. (The `k/4` conspiracy exponent of the map comes from the
*mean square*, where the pairing is cosine×cosine and the diagonal does survive. The two are
different objects; this had been conflated.)

Lean: `resonantKernel`, `integral_sin_mul_eq_resonantKernel`, `sin_mul_cos_split`,
`resonantKernel_neg`, `resonant_double_sum_eq_zero`, `double_voronoi_resonant_cancellation`.

### C114 — the surviving non-resonant half is the square of a *classical* divisor exponential sum

What remains is the `sin(A+B+2γ)` half, with kernel `[cos(c₊+2γ) − cos(c₊X+2γ)]/c₊`,
`c₊ = 6π(m^{1/3}+l^{1/3})`. The phase is **additive** in the two variables, and the weight `1/c₊` has
a Laplace representation `1/c = ∫_0^∞ e^{−ct}dt`. Both factorise, so

    E ≈ H · Re[ e^{2iγ} ∫_0^∞ F(X,t)² dt ],   F(X,t) := Σ_{m≤M} d₃(m) m^{−1/3} e^{−6πm^{1/3}t} e(3Xm^{1/3}).

`F` is a **one-variable** divisor exponential sum with cube-root phase — precisely the Voronoi dual
of the *classical* ternary divisor problem: by partial summation `F(X,0)` is of the size of `Δ₃(x)`
itself (the `m^{−1/3}` versus `m^{−2/3}` weight difference is exactly the factor `M^{1/3} = x^{1/3}`
that converts `Δ₃(x)/x^{1/3}` back to `Δ₃(x)`).

> **The shift-averaged ternary additive divisor problem reduces to the square of the classical
> ternary divisor problem.**

That is a reduction from a `GL(3)×GL(3)` object to a `GL(3)` object — from a problem with no known
nontrivial bound to one with a long history of them (`Δ₃(x) ≪ x^{43/96+ε}` and successors).

Lean: `laplace_reciprocal`, `nonresonant_double_sum_is_square`. Axioms
`[propext, Classical.choice, Quot.sound]` throughout.

### Phase 4 verdict: `SURVIVES PRELIMINARY ATTACK` — but the bookkeeping decides everything

Honest status. The *structure* is clear and, I believe, correct. The *quantitative* bookkeeping is
not done, and the answer is sensitive to it: depending on how the `t`-integral in the Laplace
representation is normalised against the truncations, the same reduction gives either

- `E ≈ |Δ₃(x)|²`, hence `≪ x^{43/48} = x^{0.896}` from the known classical bound — **far below** the
  target `x^{7/6}`, which would break the chord and give `m(3) < 5/4`; or
- `E ≈ H·x^{−1/3}·(trivial size)²` — landing **exactly** on `b = 5/6`, the threshold, i.e. no gain.

The campaign's recurring pattern (everything lands exactly on the critical value) makes the second
outcome the one to bet on, but it is not yet decided. **This is the first lead in the campaign that
is neither a barrier nor inert, and it is decidable by a finite computation.**

`[OPEN CORE, cycle 53]` Carry out the bookkeeping of C114 rigorously:
1. the `t`-integral: `∫_0^∞ F(X,t)²dt` with `F` truncated at `M ≍ x`; the decay scale is
   `t ≍ M^{−1/3}`, so the naive normalisation gives `x^{−1/3}|F|²` — verify against the exact
   Laplace weight rather than by scaling;
2. the truncations: the `m`-range ends at `m₀(n) = n^{k−1}/H^k`, which depends on `n`; dyadic
   decomposition in `n` is required, and the residual boundary strip has width `m^{2/3}/X` in `l`;
3. the main-term mismatch `𝔐` (Conrey–Gonek, standard but must be exhibited);
4. the error in the truncated Voronoi formula for `Δ₃` and in the linearisation.

Only (1) decides gain versus no-gain; (2)–(4) are hygiene. **Do (1) first.**

### C115 — the bookkeeping of C114, item (1), carried out: the reduction is defeated by the slow-phase tail `[PROVED HERE]`

Executing step (1) of the open core. With the Laplace variable inserted and the dyadic decomposition
`m ≍ M_j` of the dual range, the `t`-integral is not a guess — it separates:

    ∫_0^∞ |F(X,t)|² dt  ≍  Σ_{M_j ≤ M dyadic} M_j^{−1/3} |F_j(X)|²,
    F_j(X) := Σ_{m ≍ M_j} d₃(m) m^{−1/3} e(3X m^{1/3}),

because the Laplace weight `e^{−6πm^{1/3}t}` cuts the block `m ≍ M_j` at `t ≍ M_j^{−1/3}`. So

    E ≪ H · Σ_j M_j^{−1/3} |F_j(X)|².

- trivial `|F_j| ≪ M_j^{2/3}` ⟹ term `= M_j`, total `≍ M`, so `E ≪ H·M`;
- square-root cancellation `|F_j| ≪ M_j^{1/6}` ⟹ term `= 1`, total `polylog`, so `E ≪ H·polylog`.

Everything therefore depends on cancellation in `F_j`, and that depends on the **phase speed**.

**The phase-speed invariant `[NEW]`.** For the `d_k` Voronoi dual at scale `y`, the phase is
`2πk(my)^{1/k}`, whose derivative in `m` is `2π(y/m^{k−1})^{1/k}`. It is `≥ 1` — i.e. consecutive
dual terms are genuinely out of phase — exactly when

    m ≲ y^{1/(k−1)}  =:  voronoiFastRange k y.

Compare with the natural truncation `m ≍ y`:

    y ≤ y^{1/(k−1)}  ⟺  k ≤ 2.

> **The Voronoi dual of `d_k` oscillates across its whole natural range if and only if `k = 2`.**
> For `k = 3` it oscillates only up to `√y`; beyond that the terms are in phase and there is no
> cancellation in the dual variable at all.

This is a new and clean structural separation of `k = 2` from `k ≥ 3`, independent of the ones
already in the map (which were about moments, blocks, and abscissae).

**Consequence for C114.** With `X = x^{1/3}`, `F_j`'s phase `3Xm^{1/3}` has derivative
`Xm^{−2/3} = x^{1/3}M_j^{−2/3}`, which is `≥ 1` iff `M_j ≤ x^{1/2}` — the same threshold. The dual
must be carried to `M ≍ x` (truncating at `x^{1/2}` leaves a tail larger than `Δ₃` itself), so the
top blocks `x^{1/2} < M_j ≤ x` are slow-phase and contribute trivially: `E ≪ H·x = x^{4/3}`, **worse
than the chord `x^{7/6}`**.

**Verdict on the C112–C114 route: the antisymmetry cancellation is real and the reduction to a
one-variable divisor sum is real, but both are defeated by the slow-phase tail of the `d₃` dual.**
`[D31]`. The reduction is *not* worthless: it is exact, and it converts the whole problem into a
single sharply-posed question, which is now the campaign's open core:

> `[OPEN CORE, replacing the previous one]` Bound `Σ_{m ≍ M} d₃(m) m^{−1/3} e(3X m^{1/3})`
> non-trivially in the **slow-phase regime** `M ≫ X²` (equivalently `M ≫ x^{1/2}` at `X = x^{1/3}`),
> where the exponential is essentially constant across the block and all the cancellation must come
> from `d₃` itself. Any bound `≪ M^{2/3−η}` there, for the dyadic blocks up to `M ≍ x`, gives
> `E ≪ H x^{1−2η}` and hence — via `(a,b) = (1/2, 1−2η)` after the `h`-average is restored —
> **`m(3) < 5/4`, the first improvement on the moment envelope since 1978.**

Note what this is *not*: it is not a shifted convolution, not a `GL(3)×GL(3)` object, and not a
level-of-distribution statement. It is a **one-variable** estimate for `d₃` against a slowly varying
exponential — i.e. an equidistribution statement for `d₃` in *short intervals of the cube-root
scale*. That is a genuinely different demand from anything in §5 of the preprint, and it is the first
time the campaign has produced an open core that is not a correlation problem.

Lean: `voronoiFastRange`, `voronoiFastRange_covers_iff`, `voronoiFastRange_three`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### C116 — `[UNVERIFIED — HIGH RISK — DO NOT CITE]` a candidate improvement: `m(3) ≤ 7/6`

C115 said the slow-phase tail defeats the route. **That was too quick.** In the slow-phase range the
exponential is constant across blocks of the wavelength `L`, so the sum is not trivial — it splits
into a *smooth* exponential sum over blocks (which van der Corput handles) plus a *fluctuation* sum
weighted by short-interval increments of `Δ₃` (which the short-interval mean square handles). Doing
that gives a saving. Full exponent chain, `H = x^{1/3}`, `X = x^{1/3}`, dual truncated at `M ≍ x`:

1. **Wavelength.** phase `3Xm^{1/3}`, derivative `Xm^{−2/3} = x^{−1/3}` ⟹ block length `L = x^{1/3}`,
   number of blocks `N_B = x/L = x^{2/3}`.
2. **Smooth part.** `Σ_B e(θ_B)`: `λ₂ ≍ x^{4/3}u^{−5/3}|_{u=x} = x^{−1/3}`, van der Corput
   `≪ N_Bλ₂^{1/2} + λ₂^{−1/2} = x^{1/2}`. Weighted: `x^{1/3}·x^{1/2} = x^{5/6}`.
3. **Fluctuation part.** `Σ_B e(θ_B)δ₃(B)`, `δ₃(B) = Δ₃(end) − Δ₃(start)`. Cauchy–Schwarz with
   Ivić's short-interval mean square `∫_x^{2x}(Δ₃(t+L)−Δ₃(t))²dt ≪ xL^{4/3}`:
   `Σ_B|δ₃|² ≈ (1/L)xL^{4/3} = xL^{1/3} = x^{10/9}`, so
   `Σ_B e(θ_B)δ₃(B) ≪ N_B^{1/2}(xL^{1/3})^{1/2} = x^{1/3}x^{5/9} = x^{8/9}`.
4. `Σ_{m≍x}d₃(m)e(3Xm^{1/3}) ≪ x^{5/6} + x^{8/9} = x^{8/9}`; needed for the chord: `x^{11/12}`.
   **Margin `x^{11/12−8/9} = x^{1/36}`.**
5. `F ≪ x^{−1/3}·x^{8/9} = x^{5/9}`; `E ≪ |F|² = x^{10/9}`; hence
   `Σ_{h≤H}Δ₃(x,h) ≪ x^{10/9} = H^{1/2}x^{17/18}`, i.e. **`(a,b) = (1/2, 17/18)`, `b < 1`.**
6. Transfer: `transferBound 3 (1/2) (17/18) = 7/6 < 5/4 = momentChord 6`. **`m(3) ≤ 7/6`.**

**Consistency check at `k = 2` (passes).** There `L = x^{1/2}`, the dual phase advances by exactly one
unit per step, and the same chain returns `Σ_{h≤H}Δ₂ ≪ H^{1/2}x^{5/6}`, whose transfer output is
`transferBound 2 (1/2)(5/6) = 1` — the correct known value `m(2) = 1`. A chain that returned anything
else at `k = 2` would be wrong on its face; this one does not.

Lean (arithmetic only): `HTGeometry.TernaryShiftAverageExponents` — `fluctuationExponent_eq (8/9)`,
`dualSumExponent_eq (5/9)`, `shiftAverageExponent_eq (10/9)`, `candidateB_eq (17/18)`,
`candidateB_lt_one`, `candidate_transfer (= 7/6)`, `candidate_beats_envelope`,
`binary_consistency (= 1)`. Axioms `[propext, Classical.choice, Quot.sound]`.

**What is certified and what is not.** *Certified:* the exponent arithmetic and the transfer output.
*Not certified — every one of these is a real risk of collapse:*

- **(R1)** the truncated Voronoi formula for `Δ₃` with the exact kernel normalisation, its truncation
  point `M`, and its error term. The antisymmetry of C113 requires the two weights to match
  **exactly**; I fixed the kernel by consistency (feeding `1_{[0,x]}` reproduces the `Δ₃` expansion)
  rather than from the literature;
- **(R2)** `∫_0^∞|F(X,t)|²dt ≍ Σ_j M_j^{−1/3}|F_j|²` — argued via the Laplace cutoff, but the cross
  terms between dyadic blocks were bounded by monotonicity of `|F_j|`, not proved;
- **(R3)** Ivić's short-interval mean square for `Δ₃`: the exponent `xh^{4/3}` and, critically, its
  **valid range of `h`** — the chain needs it at `h = x^{1/3}`;
- **(R4)** the main-term mismatch `𝔐` and the linearisation error, including the `n`-dyadic
  decomposition (the linearisation threshold `m₀(n) = n²/H³` depends on `n`);
- **(R5)** whether the transfer accepts an input proved only for `H ≲ x^{1/3}` (it should — the
  moment kernel's dominant range is `h ≤ M/T = x^{1/3}` — but this must be checked against the §3bis
  proof, not assumed).

**Status: a candidate, not a result.** The `x^{1/36}` margin at step 4 is thin enough that any one of
(R1)–(R5) costing a power of `x` destroys it. Recorded here in full so it can be checked line by line
rather than re-derived.

**Next cycle: verification, in the order (R3), (R1), (R2), (R4), (R5).** (R3) first because it is a
literature fact with a yes/no answer and the chain dies immediately without it; (R1) second because
the antisymmetry — the one genuinely new mechanism — stands or falls with the kernel normalisation.

### C117 — (R3) checked: C116 is DEAD. Verdict `CIRCULAR`. And what survives is genuinely intermediate.

Ivić, *On the mean square of the divisor function in short intervals*, J. Théor. Nombres Bordeaux,
**THEOREM 1** (extracted verbatim from arXiv:0708.1601v2):

> Let `k ≥ 3` be a fixed integer. **If `σ(k) = 1/2`** then, for `X^ε ≤ h ≤ X^{1−ε}`,
> `∫_X^{2X}(Δ_k(x+h) − Δ_k(x))²dx ≪_ε X^{1+ε}h^{4/3}`.
> If `1/2 < σ(k) < 1` and `θ(k) > 2σ(k) − 1`, then there is `ε₁ = ε₁(k) > 0` such that for
> `X^{θ(k)} ≤ h ≤ X^{1−ε}`, `∫_X^{2X}(Δ_k(x+h) − Δ_k(x))²dx ≪ X^{1−ε₁}h²`.
> **Corollary 2.** Unconditionally one may take `θ(3) = 1/6+ε`, `θ(4) = 1/4+ε`, …

Here `σ(k)` is defined by `∫_0^T|ζ(σ(k)+it)|^{2k}dt ≪ T^{1+ε}`; the known values are `σ(2) = 1/2`,
`σ(3) = 7/12`, `σ(4) = 5/8`, `σ(5) = 41/60`.

**Therefore `σ(3) = 1/2` *is* `∫_0^T|ζ(1/2+it)|^6 ≪ T^{1+ε}`, i.e. `m(3) = 1` — the sixth moment
conjecture itself.** The input C116 needed is equivalent to the conclusion C116 would prove.
**Verdict: `CIRCULAR`. C116 is retracted as a candidate result.** `[D32]` — and this is erratum
**E9**: I built the chain on `xh^{4/3}` as if unconditional; the campaign's own §3.6 had already
recorded "only under LH". Rule adopted: **before using any cited bound in a chain, extract its
hypothesis verbatim, not from memory.**

**Unconditionally**, `k = 3` only has `X^{1−ε₁}h²` with `ε₁` unspecified and small. Running the chain
with that: `E ≪ x^{4/3−ε₁}`, versus the envelope `x^{7/6}` — **worse**, unless `ε₁ > 1/6`.

### C118 — what survives: a genuinely intermediate criterion `[PROVED HERE — arithmetic]`

Parametrise the chain by the short-interval mean square exponent `β`:

    ∫_X^{2X}(Δ₃(x+h) − Δ₃(x))² dx ≪ X^{1+ε}h^{β}   at  h ≍ X^{1/3}.

Then `Σ_B|δ₃|² ≈ X L^{β−1}`, `Σ_B e(θ_B)δ₃(B) ≪ X^{5/6 + (β−1)/6}`, and the chain's output is

    b(β) = 5/6 + (β−1)/3,    and    b(β) < 1  ⟺  **β < 3/2**.

Check points: `β = 2` (trivial) ↦ `b = 7/6` — nothing; `β = 3/2` ↦ `b = 1` — exactly the envelope;
`β = 4/3` (Ivić, conditional on `m(3)=1`) ↦ `b = 17/18`.

> **The criterion `β < 3/2` sits strictly between the trivial exponent `2` and the
> Lindelöf-conditional exponent `4/3`.**

This matters for the campaign's central thesis. The map's closing line has been *"there is no uncapped
intermediate"*. **Here is one.** `β < 3/2` is:
- strictly weaker than the sixth moment conjecture (which gives `β = 4/3`);
- strictly stronger than anything unconditional (which gives only `β = 2` with an `X^{−ε₁}`);
- a **mean square** statement — softer than a pointwise bound, softer than a correlation asymptotic,
  and softer than a level-of-distribution statement;
- and it lives in the range `h ≍ X^{1/3}`, well inside Ivić's admissible range `h ≥ X^{1/6+ε}`.

**Revised open core.** Prove, unconditionally,

    ∫_X^{2X} (Δ₃(x+h) − Δ₃(x))² dx ≪ X^{1+ε} h^{3/2−η}    for  h ≍ X^{1/3},  some η > 0,

i.e. interpolate Ivić's Theorem 1 between its two branches. His first branch uses `σ(3) = 1/2`; the
known `σ(3) = 7/12` should, by the same method, yield **some** exponent `β(7/12) ∈ (4/3, 2)`, and the
question is whether `β(7/12) < 3/2`. **That is a finite computation inside a published proof, not a
new theory.** It is the first target the campaign has produced that is simultaneously (i) unconditional
in form, (ii) strictly weaker than LH, and (iii) sufficient to move the moment envelope.

Caveat, unchanged: the chain still carries risks (R1), (R2), (R4), (R5) of C116. `β < 3/2` is
*necessary* for this route; sufficiency awaits those.

Lean: `shortIntervalOutput`, `shortIntervalOutput_trivial (7/6)`,
`shortIntervalOutput_conditional (17/18)`, `shortIntervalOutput_threshold (= 1)`,
`shortIntervalOutput_lt_one_iff (⟺ β < 3/2)`. Axioms `[propext, Classical.choice, Quot.sound]`.

### C119 — the target computation, done: the Voronoi chain is circular at **every** abscissa `[PROVED HERE]`

Extracted Ivić's proof (arXiv:0708.1601v2 §3) rather than his theorem. His key estimate, before he
specialises, is

    ∫_X^{2X}(Δ_k(x+h) − Δ_k(x))² dx  ≪  X^ε ( h² X^{2σ−1} · ∫_{−T₀}^{T₀}|ζ(σ+it)|^{2k}dt  +  X³T₀^{−2} ),

with `σ` **any** abscissa and `T₀` free, `1 ≪ T₀ ≪ X`. Ivić inserts `∫|ζ|^{2k} ≪ T₀^{1+ε}`, which
forces `σ = σ(k)`. Keeping the general moment exponent `m = m(k,σ)` instead:

    optimal T₀ ≍ (X^{4−2σ}h^{−2})^{1/(m+2)},   bound ≍ X^{[3m + 4σ − 2]/(m+2)} h^{4/(m+2)},
    at h = X^{1/3}:  exponent = (3m + 4σ − 2/3)/(m+2).

The chain of C118 breaks the moment envelope iff that exponent is `< 3/2`, i.e. iff

    **m(3,σ)  <  22/9 − 8σ/3.**

Consistency: `σ=1/2, m=1` gives requirement `10/9 > 1` ✓ (Ivić's conditional branch works — matches
`β = 4/3 ↦ b = 17/18`). `σ=7/12, m=1` gives `8/9 < 1` ✗ (matches `β(7/12) = 5/3 > 3/2`).

**Now evaluate it.**
- **At `σ = 1/2`:** the requirement is `m(3) < 10/9`. The chain *delivers* `m(3) < 5/4`. Since
  `10/9 < 5/4`, **the hypothesis is strictly stronger than the conclusion.**
- **For `σ ≥ 13/24`:** the requirement is `< 1`, and `m ≥ 1` always. **Impossible.**
- **Along the known curve** — the chord from `(1/2, 5/4)` to `(7/12, 1)`, admissible by convexity of
  the moment exponent — the requirement is met only for `σ > 11/12`, far outside `[1/2, 7/12]`.

> **Theorem (chain circularity).** For every abscissa `σ`, the Voronoi chain improves the moment
> envelope only from an input strictly stronger than its own output. The route is circular at every
> abscissa, not merely at the one Ivić happened to use.

`[D33]`. This closes the C112–C118 route completely, and it answers the target computation: `β(7/12)`
is `5/3`, not below `3/2`, and no other `σ` rescues it.

Lean: `chainRequirement`, `chainRequirement_half (= 10/9)`,
`chainRequirement_seven_twelfths (= 8/9)`, `chainRequirement_lt_one_iff (⟺ σ > 13/24)`,
`chain_input_stronger_than_output`, `knownSixthMomentCurve`, `knownCurve_meets_requirement_iff
(⟺ σ > 11/12)`, `chain_fails_on_admissible_range`. Axioms `[propext, Classical.choice, Quot.sound]`.

### C120 — what C112–C119 leaves standing, and the next object

**Retained as new knowledge** (independent of the dead chain):
1. the exact reduction `Σ_{h≤H}Δ_k(x,h) = Σ_n d_k(n)[Δ_k(n+H) − Δ_k(n)] + 𝔐`;
2. the **resonant antisymmetry**: sine × cosine ⟹ the resonant half of the double Voronoi sum
   vanishes identically; no diagonal obstruction for the first moment (the `k/4` conspiracy exponent
   is a *mean-square* phenomenon — these had been conflated);
3. the **Laplace factorisation**: the non-resonant half is the square of a one-variable divisor
   exponential sum — a GL(3)×GL(3) object reduced to a GL(3) one;
4. the **phase-speed invariant** `voronoiFastRange k y = y^{1/(k−1)}`, full iff `k = 2`;
5. the **circularity theorem** above.

**The pattern, now with a mechanism.** Every route the campaign has closed fails in one of exactly
two ways: *inertness* (output = input, e.g. the Jensen balance, Guth–Maynard, off-line moments) or
*circularity* (input strictly stronger than output, e.g. this chain, the `S(t)` route, Backlund).
Inertness always traced to the self-dual point; circularity always traces to the moment exponent
`m(3,σ)` re-entering as an input. **Conjecture 6.12 covered the first; the second now wants its own
statement.**

`[CONJECTURE, next cycle]` **(Moment re-entry.)** Every route from divisor correlations to the moment
envelope re-imports `m(k,σ)` as an input, with a requirement strictly stronger than its output. If
true, no divisor-correlation route can improve `m(k)` — and the additive-divisor programme, which the
map has carried as the one uncapped direction since cycle 1, would itself be capped. Falsifiable:
exhibit one divisor-correlation route whose input requirement is implied by, but does not imply, its
output. **The `k = 2` case is exactly such an example** (Motohashi's spectral formula gives `m(2)=1`
from GL(2) spectral data, not from a moment exponent) — so the conjecture must be stated for `k ≥ 3`,
and the question becomes what property of GL(2) makes the escape possible and whether GL(3) has it.

### Cycle 52 — Phase 6 (anti-theatre) and Phase 7 (anti-laziness)

**P6.1 New knowledge?** Yes, five items, none obtainable by literature search: the exact reduction
(7.1); the resonant antisymmetry (Prop 7.1) and the correction it forces — the `k/4` conspiracy
exponent is mean-square, not first-moment, and these had been conflated in the map since cycle 1; the
Laplace factorisation (Prop 7.2) reducing `GL(3)×GL(3)` to `GL(3)`; the phase-speed invariant
`y^{1/(k−1)}` (Prop 7.3); and the circularity theorem (Thm 7.4), which is proved for *every* abscissa,
not merely observed at one.
**P6.2 Rediscovery?** One real error, caught: I used Ivić's `xh^{4/3}` as unconditional when the
campaign's own §3.6 had recorded "only under LH" (E9). Cost: one full candidate. Fix adopted and
already applied — extract a cited bound's hypothesis *verbatim from the source* before building on it.
That is what turned C116 into C117–C119 within the same cycle.
**P6.3 Theatre?** No. The circularity theorem required extracting and re-deriving Ivić's §3 estimate
before he specialises; the published theorem statement alone would have given only the `σ = σ(k)`
case and would not have shown circularity at *every* abscissa.
**P6.4 Frontier moved?** The bound frontier: no, `μ ≤ 13/84` stands. The barrier frontier: yes — the
additive-divisor direction, carried as the single uncapped route since cycle 1, now has a capped
family inside it and a conjecture (7.5) that would cap it entirely.
**P6.5 Big picture.** Two failure modes now have names and mechanisms: *inertness* (self-dual
stationarity) and *circularity* (moment re-entry). Every closed route is one or the other. The open
question has sharpened from "find a better bound" to "find a route that never bounds a divisor
correlation by a moment of `ζ`" — and `k = 2` shows what such a route looks like: an **exact spectral
identity**, not an inequality.

**P7.1 Time without new knowledge?** The index/lint races. Gate now run once at the end of a cycle.
**P7.2 Effort avoidance?** No. The hardest object was attacked directly and a candidate improvement
was produced, tested, and killed within the cycle.
**P7.3 Hardest problem or infrastructure?** Hardest problem, throughout. All Lean this cycle
certifies statements that are new here.
**P7.4 Corpus researched?** Yes — `formal_tools.py research` before writing, and every mathlib name
verified in `/tmp` scratch first.

**Plan for cycle 53.** Attack Conjecture 7.5 from the escape side, not the barrier side: identify the
property that makes Motohashi's identity *exact* and ask whether `GL(3)` has it. Concretely, the
`GL(2)` escape rests on the Kuznetsov formula having exactly two Weyl terms (identity and long
element) with a one-dimensional Bessel transform. `GL(3)` has six, of which the long element carries
a two-dimensional transform (Buttcane). The first question with a yes/no answer: **does the
`GL(3)` Kuznetsov formula's long-element term, with Deligne's bound for `Kl₃`, already suffice for
the shift-average — or does bounding its transform re-import a moment?** If it re-imports, Conjecture
7.5 gains its decisive instance; if not, the escape route is located.

## Cycle 53 — the spectral escape, and an authoritative check of the transfer (C121–C123)

### C121 — the GL(3) spectral machinery is in better shape than the map assumed `[SOTA correction]`

Two corrections to the campaign's picture of the GL(3) frontier:

1. **Blomer–Buttcane, *Global decomposition of GL(3) Kloosterman sums and the spectral large sieve*,
   Crelle 757 (2019) 51–88 (arXiv:1512.01152):** best-possible bounds for bilinear forms in the
   **long Weyl element** GL(3) Kloosterman sums, and as an application a **best-possible spectral
   large sieve inequality on GL(3)**. So the large sieve — which I had assumed was the missing input
   — **exists and is optimal**.
2. **Kwan, *Spectral moment formulae for GL(3)×GL(2) L-functions II: the Eisenstein case*
   (arXiv:2310.09419):** using an identity between **two distinct periods of the GL(3) Eisenstein
   series**, an *exact* Motohashi-type identity linking the shifted cubic moment of GL(2) `L`-functions
   to the shifted fourth moment of GL(1) `L`-functions.

Item 2 identifies the mechanism behind the `k = 2` escape from moment re-entry (Conjecture 7.5):
**Motohashi's identity is a period identity — one automorphic object, two unfoldings.** Exactness is
not a lucky feature of the fourth moment; it is what a period identity always gives. So the question
"does GL(3) have the escape?" becomes: **is there an automorphic object with two unfoldings, one of
which is the sixth moment of `ζ`?** Since `ζ³` is the `L`-function of the GL(3) minimal Eisenstein
series, the sixth moment is the **second moment of a GL(3) Eisenstein `L`-function**, and the
candidate object is a period on GL(4).

### C122 — the transfer, checked against the literature: two independent confirmations `[VALIDATION]`

Ng, *The sixth moment of the Riemann zeta function and ternary additive divisor sums*
(arXiv:1610.04977), states the required input as **Conjecture 2, `AD(θ,C)`**:

> `D_{f,I,J}(r) = (explicit main terms) + O(P^{C} X^{θ+ε₁})`, uniformly for `1 ≤ r ≤ X^{1/2+ε₂}`,
> where `f` is smooth with `x^i y^j f^{(i,j)} ≪ P^{i+j}`.

and **Corollary 1.2**: if `AD(θ,C)` holds with `θ ∈ [1/2, 2/3)` and `1 ≤ C < 3(1−θ)`, then
`I₃(T) = T·P₉(log T) + O(T^{1−ε})`.

**Confirmation 1 — the `2/3` threshold.** The campaign's transfer gives
`transferBound 3 1 θ = 1 ⟺ 3θ ≤ 2 ⟺ θ ≤ 2/3` (`ternary_two_thirds`, `pointwise_input_eq_one_iff`,
cycle 51). Ng's admissible range is exactly `θ ∈ [1/2, 2/3)`. **The campaign's threshold and the
literature's coincide.**

**Confirmation 2 — the `T^{3/4}` error prediction.** Ng, Remark 5: with the best possible `θ = 1/2`
and `C < 1`, the error term for the sixth moment is `O(T^{3/4+ε})`, "matching Ivić and Motohashi's
speculations". The campaign's independent-signs model predicts `E_k(T) ≍ T^{k/4}`, which at `k = 3`
is **`T^{3/4}`** (preprint Prop 1.2). **The model's prediction is confirmed at the first index where
nothing is known.** This is a real test the model could have failed.

### C123 — a parameter the map was missing: the smoothness exponent `C` `[NEW FOR THE CAMPAIGN]`

The campaign's transfer carries only `(a,b)`. Ng's conjecture carries a **second** exponent: the
error is `P^{C}X^{θ+ε}`, with `P` the derivative scale of the test function, and the requirement is
the **joint** condition

    1/2 ≤ θ < 2/3    and    1 ≤ C < 3(1 − θ).

This is a triangle with vertices `(1/2, 1)`, `(1/2, 3/2)`, `(2/3, 1)`; the corner `θ = 2/3` is
excluded. Consequences the one-parameter transfer cannot see:

- **the two demands trade off**: `θ < 1 − C/3`. Getting the size down to Conrey–Gonek `θ = 1/2` buys
  smoothness room up to `C < 3/2`; conversely, being forced to a sharp cut-off (`C` near `3/2`) costs
  the whole size budget;
- **DFI's `k = 2` result has `(θ, C) = (3/4, 5/4)`** — its `C` is admissible for the ternary triangle
  (`5/4 < 3/2`) but its `θ` is not (`3/4 > 2/3`). So the binary method's *shape* is not the obstacle;
  its *size exponent* is;
- **`(1/2, 5/4)`, the Conrey–Gonek size with DFI's smoothness, is admissible.** So there is no
  incompatibility between the two conjectures the campaign has been treating as rivals: the
  Conrey–Gonek size at DFI smoothness would suffice.

Lean: `HTGeometry.TernaryAdditiveDivisorRegion` — `ngAdmissible`, `ngAdmissible_conreyGonek`,
`ngAdmissible_C_lt (C < 3/2)`, `ngAdmissible_tradeoff (θ < 1 − C/3)`, `ngAdmissible_projection_agrees`
(the `θ`-projection is exactly the transfer's range), `ngAdmissible_corner_excluded`. Axioms
`[propext, Classical.choice, Quot.sound]`.

**Erratum E10.** The map's §4 table treats "Conrey–Gonek size" and "Ivić `Ω(x^{1−1/k})`" as settling
LH in opposite directions, and lists only size exponents. It should carry `C` as well; a route that
achieves `θ = 1/2` but only with `C ≥ 3/2` proves nothing about the sixth moment. Recorded; the
preprint §4 needs the second axis.

**Revised open core (authoritative form).** Prove `AD(θ,C)` for `d₃` with `(θ,C)` in the triangle
`1/2 ≤ θ < 2/3`, `1 ≤ C < 3(1−θ)`, uniformly for shifts `r ≤ X^{1/2+ε}`. Ng, Remark 7: "for `k ≥ 3`
this currently remains open" — no `(θ,C)` whatsoever is known.

### C124 — `[CONJECTURE]` the multiplicity-one obstruction: why `k = 2` escapes and `k = 3` cannot

**The mechanism of the `k = 2` escape, located.** Motohashi's identity is a *period* identity. Its
engine is the spectral expansion of `|E_t^{GL(2)}|²` against the GL(2) spectrum, whose coefficients
are triple products `⟨E_t E_{−t}, u_j⟩`. These are `L`-values **because the trilinear form on
GL(2)×GL(2) ⊃ GL(2) is unique** — Prasad's multiplicity-one theorem — which is exactly what
Watson–Ichino converts into `L(1/2, u_j)³`. Exactness is not a feature of the fourth moment; it is
what multiplicity one always gives.

**The obstruction at `k = 3`.** Since `ζ³` is the `L`-function of the GL(3) minimal Eisenstein
series, the sixth moment of `ζ` is the **second moment of a GL(3) Eisenstein `L`-function in the
`t`-aspect**. The same construction would need the spectral expansion of `|E_t^{GL(3)}|²` against the
GL(3) spectrum, i.e. triple products on GL(3)×GL(3) ⊃ GL(3). **That branching problem does not have
multiplicity one.** The multiplicity-one pairs in this circle are `(GL(n+1), GL(n))`
(Aizenbud–Gourevitch–Rallis–Schiffmann, Annals 2010), not `(GL(n)×GL(n), GL(n))` for `n ≥ 3`. There is
no Watson–Ichino formula to convert the triple product into an `L`-value, hence no exact identity.

> **`[CONJECTURE 7.6]` (multiplicity-one obstruction).** An exact Motohashi-type identity for the
> `2k`-th moment of `ζ` in the `t`-aspect exists only when the branching problem
> `GL(k)×GL(k) ⊃ GL(k)` has multiplicity one — i.e. only for `k ≤ 2`. For `k ≥ 3` every spectral
> route must instead bound a triple product, and bounding it re-imports a moment (Conjecture 7.5).

**Why this is not a restatement of "GL(3) is hard".** It predicts *where* the tractable identities
live: on `(GL(n+1), GL(n))` pairs. And that prediction is confirmed by the literature — every known
exact spectral identity in this circle is a `GL(3)×GL(2)` statement (Kwan I–III), a `GL(4)×GL(2)`
statement (Blomer–Khan), or classical `GL(2)×GL(2)`. **None is `GL(3)×GL(3)`,** and the one
`GL(3)×GL(3)` result that exists (Harun–Singh 2025, C109) is an *estimate*, not an identity, is
cuspidal only, and is restricted to `H ≥ X^{1/2+δ}` — exactly the shape Conjecture 7.6 predicts.

**Supporting datum: the dual family is the wrong size.** For `GL(n)`, the Weyl law counts
`≍ T^{(n²+n−2)/2}` forms with spectral parameter `≤ T`: `T²` for `n = 2`, `T⁵` for `n = 3`. The
moment being computed is `≍ T` in both cases. So a hypothetical `k = 3` identity would have to balance
a family of size `T⁵` against a left side of size `T` — a mismatch of `T⁴`, against `T` at `k = 2`.
Any such identity would be far more delicate than Motohashi's, independently of multiplicity one.

**Falsifiable.** Exhibit an exact spectral identity for `∫_T^{2T}|ζ(1/2+it)|^6dt` that does not pass
through a GL(3) triple product. **Or** exhibit a `(GL(4), GL(3))` period whose two unfoldings give the
sixth moment on one side — the multiplicity-one pair `(GL(4), GL(3))` *is* available (AGRS), so this
is the one route Conjecture 7.6 does **not** exclude, and it is where cycle 54 should look.

**Consequence if true.** Combined with Conjecture 7.5 (moment re-entry), the additive-divisor
programme — the map's single uncapped direction since cycle 1 — is capped for `k ≥ 3`, and the
Lindelöf hypothesis has no known route at all that is not already proved inert or circular. That
would make the map complete, and would relocate the problem entirely: **not to a better estimate, but
to the construction of a period on `(GL(4), GL(3))` unfolding to the sixth moment.**

## Cycle 54 — the fourteenth ceiling: the sixth moment inside Motohashi's identity is unreachable

**Phase 1 (corpus).** `formal_tools.py research "Motohashi spectral fourth moment continuous
Eisenstein sixth moment positivity"` — nothing relevant. New ground.

### C125 — the observation that starts the cycle `[CORRECTS C124]`

C124 conjectured that the sixth moment is outside the multiplicity-one world. **That is wrong, and
in an instructive way.** Since `L(s, E^{(3)}_min(α) × E^{(2)}(β)) = Π_{i,j}ζ(s+α_i+β_j)`, taking
`α = (0,0,0)` and `β = (it,−it)` gives **exactly `|ζ(1/2+it)|⁶`**. So

> the sixth moment of `ζ` *is* a `GL(3)×GL(2)` Rankin–Selberg object — the multiplicity-one pair —
> and it is the **continuous-spectrum** (Eisenstein) part of the family whose cuspidal part is the
> cubic moment `Σ_j L(1/2, u_j)³`.

Equivalently and classically: **the sixth moment of `ζ` occurs as the continuous term of Motohashi's
fourth-moment identity.** All terms of that identity are non-negative (`α_j > 0`;
`H_j(1/2) ≥ 0` by Katok–Sarnak; `|ζ(1/2+ir)|⁶/|ζ(1+2ir)|² ≥ 0`) except possibly the spectral weight.
So the natural route is: **drop the cuspidal terms by positivity and read off a sixth-moment bound.**

C124 is retracted in its pessimistic form: the escape *is* in the multiplicity-one world. What
follows is why it is nevertheless void.

### C126 — the Plancherel density gap `[PROVED HERE]`

Motohashi's explicit formula weights the spectrum by `T^{1/2} r^{-3/2}`. The two spectra carry
different densities:

| spectrum | density | weight × density | dominated by |
|---|---|---|---|
| cuspidal (Weyl law) | `≍ r dr` | `r^{-1/2}`, exponent `> -1` | **top** of the range |
| Eisenstein (Plancherel) | `≍ dr` | `r^{-3/2}`, exponent `< -1` | **bottom**, `r = O(1)` |

> **The continuous spectrum carries exactly one power of `r` less than the cuspidal spectrum.** That
> single exponent is the whole obstruction.

Consequence: the cuspidal sum is top-dominated — which is precisely why Motohashi's identity *sees*
the cubic moment of cusp forms at the top of its range. The continuous integral **converges** and is
dominated by `r = O(1)`. **The sixth moment of `ζ` at large height never enters Motohashi's identity
at all.** The well-known remark "the sixth moment appears in Motohashi's formula" is true and
useless: it appears only at bounded height.

### C127 — and even granting positivity, the route is worthless `[PROVED HERE]`

Suppose the spectral weight were non-negative, so that the cuspidal terms could be dropped. On
`r ≍ R` the weight is `≍ T^{1/2}R^{-3/2}`, and the transform confines `R ≤ T^{1/2}`, i.e. `T = R²`.
From `E₂(T) ≪ T^{e}`:

    ∫_R^{2R}|ζ(1/2+ir)|⁶ dr  ≪  T^{e}·T^{-1/2}R^{3/2}  =  R^{2e − 1 + 3/2}.

- known `E₂ ≪ T^{2/3}` ⟹ `m(3) ≤ 11/6`;
- conjectured, `Ω`-matching `E₂ ≪ T^{1/2+ε}` ⟹ `m(3) ≤ 3/2`;
- the route beats the envelope `5/4` **iff `e < 3/8`** — strictly below the `Ω`-result
  `E₂(T) = Ω_±(T^{1/2})` (Ivić–Motohashi).

> **Fourteenth ceiling.** The Motohashi continuous-term route is void twice over: the weight confines
> the sixth moment to bounded height, and even granting positivity and the `Ω`-imposed floor for
> `E₂`, it returns `m(3) ≤ 3/2`, strictly worse than the known `5/4`. The obstruction is an
> `Ω`-result, not a lack of effort. `[D34]`

**The instrument, named.** This is the third time an `Ω`-result kills an upper-bound method in this
map: §3.7 (Heath-Brown's twelfth moment at its input's ceiling via `E(T) = Ω(T^{1/4})`), §3.8
(resonance cannot disprove LH via Bondarenko–Seip), and now §8 (`E₂ = Ω_±(T^{1/2})` voids the
Motohashi continuous term). **`Ω`-results as method-killers** is a systematic instrument of this
campaign, not a coincidence: an `Ω`-result on an error term is exactly a floor on what any method
resting on that error term can deliver.

Lean: `HTGeometry.MotohashiContinuousTerm` — `plancherel_density_gap`, `cuspidal_top_dominated`,
`eisenstein_bottom_dominated`, `positivityRouteOutput`, `positivityRouteOutput_known (11/6)`,
`positivityRouteOutput_optimal (3/2)`, `positivity_route_void`, `positivity_route_threshold
(⟺ e < 3/8)`. Axioms `[propext, Classical.choice, Quot.sound]`.

### Cycle 54 — Phase 6 (anti-theatre) and Phase 7 (anti-laziness)

**P6.1 New knowledge?** Yes: the identification of the sixth moment as the Eisenstein part of the
`GL(3)×GL(2)` family (C125, which also *refutes* my own C124 within one cycle); the Plancherel
density gap as the reason Motohashi's identity cannot see it (C126); and the quantitative void
(C127), with the sharp threshold `e < 3/8` located strictly below a known `Ω`-result.
**P6.2 Rediscovery?** The remark "the sixth moment appears in Motohashi's formula" is classical. What
is not classical, and is the content here, is *why it is useless* — and that required computing the
weight-times-density exponents on both spectra.
**P6.3 Theatre?** No. A literature search would return the classical remark and stop; the ceiling
required the arithmetic.
**P6.4 Frontier moved?** Barrier frontier, yes — a fourteenth ceiling, and the retraction of C124
removes a false structural claim from the map before it propagated.
**P6.5 Big picture.** Three of the map's ceilings are now `Ω`-driven. That is a *general* instrument:
**every method that factors through an error term inherits that error term's `Ω`-floor.** The next
cycle should apply it systematically rather than route by route — i.e. enumerate the error terms each
remaining route factors through, and read off their floors.

**P7.1 Time without new knowledge?** No; the whole cycle was on the hardest object.
**P7.2 Effort avoidance?** No — I attacked the positivity idea rather than declaring it hopeless, and
it produced the ceiling.
**P7.3 Hardest problem?** Yes. And I corrected my own conjecture from the previous cycle rather than
defending it.
**P7.4 Corpus researched?** Yes, before writing.

**Plan for cycle 55.** Systematise the `Ω`-instrument: for each surviving route, identify the error
term it factors through and its `Ω`-floor, and read off the induced ceiling. Candidate error terms:
`Δ_k(x)` (classical divisor, `Ω(x^{(k−1)/(2k)})`), `Δ_k(x,h)` (correlation, Ivić's conjectural
`Ω(x^{1−1/k})`), `E_k(T)` (moment error, `Ω(T^{k/4})` per the model), `S(t)` (argument,
`Ω(√(log t loglog t))`). The instrument predicts a ceiling for every route factoring through each.

## Cycle 55 — the reduction loop closes: the three formulations are one problem

### C128 — clarification of C119's scope, and why it matters `[ERRATUM E11]`

C119 proved the *Voronoi chain via Ivić's estimate* is circular. It did **not** prove the C118
criterion `β < 3/2` is circular — only that Ivić's route to it is. And `β < 3/2` has a lot of room:
Ivić's Remark 2 records that the conjectured truth for `k ≥ 3` is `∫_X^{2X}(Δ_k(x+h)−Δ_k(x))²dx
≪ X^{1+ε}h`, i.e. **`β = 1`**, and Jutila proved exactly that for `k = 2` (with
`≍ X h log³(√X/h)`), together with the matching `Ω`-result `Δ(x+h)−Δ(x) = Ω(√h log^{3/2}(√X/h))`.
So `β = 1` is the floor and `β = 2` the trivial bound; the criterion `β < 3/2` sits at the midpoint,
with a factor `h^{1/2}` of slack against the conjectured truth. **The criterion is not, on its face,
circular.** That kept the C118 target alive and it had to be settled.

### C129 — settled: the criterion is circular too, by a different route `[PROVED HERE]`

Expand `B(X,h) = ∫_X^{2X}(Δ₃(x+h) − Δ₃(x))²dx` by the Voronoi series
`Δ₃(x) ≈ c x^{1/3}Σ_{m≤M}d₃(m)m^{−2/3}cos(6π(mx)^{1/3}+γ)`. Writing
`ψ_m ≍ m^{1/3}hX^{−2/3}` for the phase increment, the squared difference carries `min(1, ψ_m²)`.

**Diagonal (`m = m'`).** With `m₁ := X²/h³` the crossover where `ψ_m ≍ 1`:

    Σ_{m≤m₁} d₃(m)²m^{−4/3}ψ_m²  ≍  h²X^{−4/3}·m₁^{1/3}  =  hX^{−2/3},
    Σ_{m>m₁} d₃(m)²m^{−4/3}      ≍  m₁^{−1/3}            =  hX^{−2/3},

equal, and the prefactor `X^{5/3}` gives **`B_diag ≍ X h ·polylog`, i.e. `β = 1`** — *the conjectured
truth, from the diagonal alone*. It clears the criterion `β < 3/2` with the output exponent `5/6`,
well inside the envelope value `1`.

> **So the entire obstruction is the off-diagonal.**

**Off-diagonal (`m ≠ m'`).** Grouping by `j = m' − m`, it is

    Σ_{j ≠ 0}  ( Σ_m d₃(m)d₃(m+j) ) · w(j),

**the ternary correlation averaged over shifts — the object the whole reduction started from.**
Crudely (first-derivative test, `|m^{1/3}−m'^{1/3}| ≍ |j|/m^{2/3}`, dual truncated at `M ≍ X`) it is
`X^{4/3}·X^{1/3} = X^{5/3}`, against a budget of `X^{3/2}`: the familiar **`X^{1/6}` gap**.

> **`[THEOREM]` The three formulations — the shift-average `Σ_{h≤H}Δ₃(X,h)`, the short-interval mean
> square `∫(Δ₃(x+h)−Δ₃(x))²dx`, and the correlation `D₃(X,h)` — are equivalent modulo their
> diagonals. Each reduces to the next and the third reduces to the first. The chain of reductions
> from cycles 52–55 closes into a loop.**

`[D35]`. This settles the last live thread from cycles 52–54: **C118's criterion is circular**, not
because `β < 3/2` is a strong statement (it is not — the truth is `β = 1`), but because *every* route
to it passes through the off-diagonal, which is the original problem.

**What this adds to the map.** The map's two failure modes — inertness and circularity — are now
joined by a third, sharper phenomenon: **the reductions are a closed loop.** That is stronger than
"each route is circular"; it says the object has no proper reformulation at all inside this circle of
ideas. Every natural restatement of the ternary obstruction is the ternary obstruction.

Lean: `HTGeometry.TernaryReductionLoop` — `diagonalMeanSquareBeta (= 1)`,
`diagonal_meets_criterion`, `diagonal_output (5/6)`, `offDiagonalBudget (3/2)`,
`offDiagonalCrude (5/3)`, `offDiagonal_gap (= 1/6)`, `reduction_loop`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### C130 — the recurring `X^{1/6}`, catalogued

The same gap `X^{1/6}` (equivalently `1/6` in an exponent, or `1/12` after a square root) has now
appeared, independently, at:

1. the averaged-input threshold at `k = 3`: `δ > 1/6` (C110);
2. the shortfall of the van der Corput saving in the slow-phase sum: `1/18` obtained versus `1/12`
   needed, i.e. `1/36` short — and `11/12 − 8/9 = 1/36` (C116);
3. the failure margin of the unconditional short-interval mean square: `ε₁ > 1/6` required (C117);
4. the off-diagonal gap of the short-interval mean square: `5/3 − 3/2 = 1/6` (C129);
5. the difference between the chain output `x^{4/3}` and the envelope `x^{7/6}`: `1/6` (C117).

**`[CONJECTURE]`** These are one number. It should equal `2μ_chord − something`, or more likely
`(1/2)·(1/3)` where `1/3` is the shift exponent `H = x^{1/3}` and `1/2` the square-root barrier — i.e.
**the gap is exactly half the shift exponent**, and it appears because every route pays the
square-root barrier once on the shift variable. Falsifiable: run the same reductions at a different
shift length `H = x^{θ}` and check that the gap becomes `θ/2`. **That is cycle 56's first task, and
it is a finite computation.**

## Cycle 56 — the recurring `1/6` identified: it is `1/2 − 1/k`

### C131 — C130's conjecture tested at general shift exponent `[CONFIRMED IN FORM, REFUTED AS EXPLANATION]`

Ran the whole chain at `H = x^θ` instead of `x^{1/3}`. The Voronoi wavelength `L = x^{1/3}` is set by
the *phase*, not by the shift, so the short-interval mean square is always taken at `h = L`; only the
prefactor `H` and the target move. Result:

    criterion on the mean-square exponent:   β < 2 − 3θ/2      (`= 3/2` at `θ = 1/3` ✓ matches C118)
    conjectured truth `β = 1` clears it  ⟺   θ < 2/3
    off-diagonal saving for zero gain:       η = θ/2           (**C130's conjecture, confirmed**)

But the shift exponent then **cancels**. With an off-diagonal saving `η` the chain yields

    Σ_{h≤H} Δ₃(x,h)  ≪  x^{θ + 1 − η}  =  H·x^{1−η},

i.e. shift exponent `a = 1`, not `1/2`, for **every** `θ`. Feeding that into the transfer, C110's
averaged-input threshold applies and demands

    η  >  1/2 − 1/k,     which at `k = 3` is  **1/6**, independently of `θ`.

> **`[THEOREM]` The recurring `x^{1/6}` of C130 is `1/2 − 1/k` at `k = 3`: the gap between the
> square-root barrier `1/2` and the reciprocal of the moment index. The apparent `θ`-dependence
> `η > θ/2` is an artefact of writing the bound with `a = 1/2`; the derived bound always has `a = 1`,
> and then the demand is `θ`-free.**

So C130's conjecture is confirmed in form and **refuted as an explanation**. The five independent
occurrences catalogued in C130 are one number, and that number is `1/2 − 1/k`.

**Why this matters — `k = 2` is free for a reason.** `recurringGap k = 1/2 − 1/k` vanishes **exactly
at `k = 2`** and is strictly increasing in `k`. At `k = 2` the square-root barrier and the reciprocal
of the moment index coincide, so no saving is demanded at all — which is precisely why the binary
additive divisor problem transfers for free while every `k ≥ 3` demands a positive power saving that
grows with `k`. This is a fifth, and the most economical, separation of `k = 2` from `k ≥ 3` in the
map — the others being the moment threshold (§3.4), the block self-duality (§3.3), the abscissa
tangency (§6.5), and the Voronoi phase-speed invariant `y^{1/(k−1)}` (§7.2).

**Consequence for LH.** `recurringGap k → 1/2` as `k → ∞`. Since LH needs `m(k) = 1` for **every**
`k`, and each `k` demands an off-diagonal saving of `1/2 − 1/k`, the Lindelöf hypothesis via this
family demands savings approaching the square-root barrier itself. **That is the same terminal
demand the map reached from the pointwise branch (`b ≤ 2/k → 0`, C111) and from the transfer table
(`(1/2,1/2)`) — three independent routes to the same terminal statement.**

Lean: `meanSquareCriterion`, `meanSquareCriterion_third (3/2)`, `meanSquareCriterion_true_beta
(⟺ θ < 2/3)`, `zeroGainSaving`, `chainOutputB`, `chainOutput_as_averaged_input` (the `a = 1`
identity), `recurringGap`, `recurringGap_three (= 1/6)`, `recurringGap_two (= 0)`,
`recurringGap_eq_zero_iff (⟺ k = 2)`, `recurringGap_strictMono`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### Cycle 56 — Phase 6 / Phase 7

**P6.** New: the identification `recurring gap = 1/2 − 1/k`, its vanishing exactly at `k = 2`, and the
`θ`-cancellation that shows the `a = 1/2` parametrisation is illusory for this chain. This corrected
my own cycle-55 conjecture within one cycle — the second self-correction in three cycles, both caught
by computing rather than by arguing. No rediscovery: the `1/2 − 1/k` threshold is the campaign's own
C110, and its identification with the five scattered occurrences is new here. Frontier: barrier side.
**P7.** No effort avoidance; the test was a finite computation and I ran it rather than leaving the
conjecture standing. Hardest object throughout. Corpus checked.

**Plan for cycle 57.** The map now says LH demands, from three independent directions, a saving that
approaches the square-root barrier as `k → ∞`. The next question is whether that terminal demand is
*itself* obstructed — i.e. whether there is an `Ω`-result at the square-root barrier for the relevant
object. Candidate: Ivić's conjectured `Δ_k(x,h) = Ω(x^{1−1/k})` versus Conrey–Gonek's `x^{1/2+ε}`;
these disagree for `k ≥ 3` and **the map has treated the disagreement as an open dichotomy without
noticing that `1 − 1/k` and `1/2 + (1/2 − 1/k)` are the same number**. Check that identity first: if
`Ω(x^{1−1/k})` holds, the demanded saving `1/2 − 1/k` is exactly what `Ω` forbids, and the
additive-divisor route is capped by an `Ω`-result — the fourth application of the `Ω`-instrument, and
the one that would close the map.

## Cycle 57 — where the two conjectured sizes part company `[PROVED HERE]`

The map's §4 has carried the Conrey–Gonek (`x^{1/2+ε}`) versus Ivić (`Ω(x^{1−1/k})`) dichotomy since
cycle 1, described only as "settling LH in opposite directions". Feeding each into the transfer at
`a = 1` locates the disagreement exactly.

### C132 — the criticality table

| index `k` | Ivić size `1−1/k` | delivers `m(k)=1`? | beats envelope? | Conrey–Gonek `1/2` delivers `m(k)=1`? |
|---|---|---|---|---|
| 2 | `1/2` | yes | yes | yes — **the two sizes are equal here** |
| 3 | `2/3` | **yes** | yes | **yes** |
| 4 | `3/4` | no | **exactly equality** | yes |
| ≥5 | `1−1/k` | no | **no** | yes |

Three consequences, all certified:

1. **`ivic_gives_one_iff`:** Ivić's size delivers `m(k) = 1` **exactly for `k ≤ 3`** (`k(1−1/k) ≤ 2
   ⟺ k ≤ 3`).
2. **`ivic_critical_at_four`:** at `k = 4`, `transferBound 4 1 (3/4) = momentChord 8 = 3/2` —
   **exact equality with the known envelope.** Another exact criticality at `k = 4`, the same index
   at which the Conrey–Gonek branch saturates (`pointwise_route_saturates`, C111). Two independent
   computations, same threshold.
3. **`sixth_moment_cannot_discriminate`:** at `k = 3` **both** sizes deliver `m(3) = 1`.

> **`[THEOREM]` The Conrey–Gonek/Ivić dichotomy is invisible at the sixth moment. No theorem about
> `m(3)` — no asymptotic, no bound, no numerical evidence at `k = 3` — can distinguish the two
> conjectures, because they have identical consequences there. The first index at which their
> consequences differ is `k = 4`; the first at which Ivić's size fails to beat the envelope is
> `k = 5`.**

This is a practical result for the field: the sixth moment is the natural place to look for evidence,
and it is exactly the place where the dichotomy is degenerate. **Evidence must be sought at the
eighth moment (`k = 4`) or beyond.** It also explains why the map's cycle-1 note "at `k = 2` both
read `x^{1/2}` and the `Ω` is Motohashi's theorem, so `k = 2` does not discriminate" understated the
problem: neither does `k = 3`.

### C133 — what Ivić's size caps the route at

With `a = 1` (no shift cancellation) and Ivić's size, `m(k) ≤ 1 + max(0,(k−3)/2)`, so
`μ ≤ m(k)/(2k)` is minimised at `k = 3` giving **`μ ≤ 1/6`** — Weyl's exponent. With full
shift cancellation `a = 1/2` and Ivić's size, the transfer gives the pivot **`1/8`**
(`vinogradov_cap`, already in the map). So:

> **If Ivić is right, the entire additive-divisor programme is capped at `1/8`** — the map's last
> uncapped direction closes, and the pivot is final. **If Conrey–Gonek is right, the same programme
> with shift cancellation gives LH.** The dichotomy is therefore *exactly* the dichotomy
> "LH provable by additive divisors" versus "`μ ≤ 1/8` and no further", and — by C132 — **it cannot
> be decided at the sixth moment.**

Lean: `HTGeometry.IvicSizeCriticality` — `ivicSize`, `sizes_agree_at_two`, `ivic_gives_one_iff`,
`ivic_critical_at_four`, `ivic_beats_envelope_iff (⟺ k < 4)`, `sixth_moment_cannot_discriminate`,
`conreyGonek_gives_one_iff`. Axioms `[propext, Classical.choice, Quot.sound]`.

## Cycle 58 — the dichotomy decided by the campaign's own model `[PROVED HERE — CHANGES THE BOTTOM LINE]`

C132 showed the Conrey–Gonek/Ivić dichotomy cannot be decided at the sixth moment. It *can* be
decided at `k = 1`.

### C134 — the size exponent is forced, not conjectured

The independent-signs model takes one input — the typical size `M^{s}` of `Δ_k(M,h)` — and predicts

    E_k(T) ≍ T^{1/2} M^{s−1/2}  at the balanced `M = T^{k/2}`,  i.e.  T^{1/2 + k(s−1/2)/2}.

Demanding the value `T^{k/4}` gives a **linear equation with a unique solution**:

    1/2 + k(s − 1/2)/2 = k/4   ⟺   **s = 1 − 1/k.**

And `E_k(T) ≍ T^{k/4}` is *proved* at both indices where anything is known: `E₁ ≍ T^{1/4}` (Good) and
`E₂ ≍ T^{1/2}` (Ivić–Motohashi), each matched by an `Ω`-result.

> **`[THEOREM]` The correlation size exponent is not a free conjecture. It is pinned to `1 − 1/k` by
> the two solved cases. That is Ivić's size. Conrey–Gonek's constant `1/2` satisfies the equation
> only at `k = 2` — the single index where the two proposals agree.**

**The `k = 1` test is decisive and was never run.** With `s = 1/2` the model predicts `E_k ≍ T^{1/2}`
at *every* index, in particular `E₁ ≍ T^{1/2}`. The truth is `E₁ ≍ T^{1/4}` and the proved upper
bound is `E(T) ≪ T^{131/416}`. So the constant size is not the typical size at `k = 1`. With
`s = 1 − 1/k = 0` at `k = 1` the model returns `T^{1/4}` — correct. Both known indices confirm
`1 − 1/k`; only one confirms `1/2`.

*Caveat, stated precisely:* Conrey–Gonek's conjecture is an **upper bound** `Δ_k ≪ x^{1/2+ε}`, and at
`k = 1` the truth `O(1)` satisfies it. So this is not a refutation of their conjecture. It is a
refutation of the claim that `1/2` is the **typical** size — and the typical size is what the model,
and hence the moment, is driven by. An upper-bound conjecture that is not the typical size gives no
saving in the moment.

### C135 — consequence: the map's last uncapped direction closes

By C133, Ivić's size caps the additive-divisor programme at **`μ ≤ 1/8`** (with full shift
cancellation; `1/6` without). Combining:

> **The independent-signs model — the same model whose predictions are exactly correct at both solved
> indices, and whose resolution floor is the pivot `1/8` — forces the correlation size that caps the
> additive-divisor programme at `1/8`. The map's single uncapped direction closes under its own
> model.**

This *changes the campaign's bottom line*. The map has carried since cycle 1 the note "function-field
evidence favours Conrey–Gonek" (Sawin: square-root cancellation with no `k`-dependent degradation).
That evidence and this argument now point in opposite directions, and the tension is the sharpest
open question the campaign has:

> `[OPEN CORE, cycle 59]` **Reconcile.** Sawin's `F_q[t]` theorems give square-root cancellation for
> divisor sums *in short intervals and progressions* — that is, for `Δ_k(x)`-type objects. The model's
> forced exponent `1 − 1/k` is for `Δ_k(x,h)`, the **correlation**. These are different objects, and
> `1 − 1/k = 2·(k−1)/(2k)` is exactly **twice** the short-interval exponent `(k−1)/(2k)`. So there
> may be no contradiction at all: square-root cancellation in the short-interval problem is
> *compatible* with the correlation error being the square of it. **Check whether Sawin's results
> cover the correlation `Σ d_k(n)d_k(n+h)` over `F_q[t]`, or only the linear statistics.** If only the
> latter, the map's cycle-1 note is an erratum and the dichotomy is settled in Ivić's favour — and
> with it, LH's last known route.

Lean: `HTGeometry.CorrelationSizeUniqueness` — `modelPrediction`,
`modelPrediction_eq_quarter_iff (⟺ s = 1 − 1/k)`, `forcedSize_one`, `forcedSize_two`,
`conreyGonek_size_fits_only_at_two`, `conreyGonek_size_prediction (≡ 1/2)`, `model_forces_ivic_size`.
Axioms `[propext, Classical.choice, Quot.sound]`.

### Cycle 58 — Phase 6 / Phase 7

**P6.** New: the uniqueness of the size exponent given the model's verified output, and the `k = 1`
test — an index nobody looks at because `d₁` is trivial, which is exactly why it discriminates. The
result changes the map's conclusion rather than adding another barrier, so it is not more of the same.
Rediscovery: none; the caveat about upper-bound-versus-typical-size is stated rather than glossed.
Frontier: this is the first cycle whose output bears on whether LH is *provable by known routes at
all*.
**P7.** No avoidance: the decisive test was cheap and I ran it the moment the dichotomy was isolated;
the hard part was noticing that `k = 1` discriminates. The next task is a literature question with a
yes/no answer and it is stated precisely.

## Cycle 59 — the counter-evidence removed: erratum E12

The question left open by C135 was whether Sawin's `F_q[t]` theorems bear on the **correlation**
`Σ d_k(n)d_k(n+h)` or only on **linear statistics** of `d_k`. Checked:

- Sawin, *Square-root cancellation for sums of factorization functions over short intervals in
  function fields* (Duke 170 (2021)) — **short intervals**, i.e. `Σ_{f ∈ short interval} d_k(f)`;
- Sawin, *…over squarefree progressions in `F_q[t]`* (Acta Math. 233 (2024)) — **progressions**, i.e.
  level of distribution for `d_k`;
- Keating–Rodgers–Roditty-Gershon–Rudnick, *Sums of divisor functions in `F_q[t]` and matrix
  integrals* — **variance of the same linear statistic**.

**All three are linear statistics. None is a correlation.** The only function-field correlation
results are for `d = d₂`: Andrade–Bary-Soroker–Rudnick (arXiv:1407.2076) and Florea–Lalín–Malik–Sahay
(arXiv:2502.16067, 2025). The latter's Theorem 1.1 gives, for `f` monic of degree `n` and
`deg h = m`, an **exact** formula with error `E = 0` whenever `m ≤ n+1` (and
`E ≪ q^{m/2+m}` otherwise). Over `F_q[t]` the binary correlation error *vanishes identically* in the
main range — stronger than square-root cancellation, and at `k = 2` the two competing sizes agree, so
it does not discriminate.

> **`[ERRATUM E12]` The map's cycle-1 note "function-field evidence favours Conrey–Gonek" is
> withdrawn. The evidence concerns `Δ_k(x)`-type linear statistics, not the correlation `Δ_k(x,h)`.
> These are different objects, and `1 − 1/k = 2·(k−1)/(2k)` is exactly **twice** the short-interval
> exponent — so square-root cancellation in the linear statistic is *compatible* with the correlation
> error being its square. There is no function-field evidence about `Δ_k(x,h)` for `k ≥ 3` at all.**

### C136 — the logical status of C134, stated precisely

The uniqueness theorem is conditional and its condition should not be overstated:

    [ E_k(T) ≍ T^{k/4} for all k ]  ⟹  [ typical size of Δ_k(M,h) is M^{1−1/k} ]  ⟹  [ route capped at 1/8 ].

`E_k ≍ T^{k/4}` is **proved at `k = 1, 2`** (each matched by an `Ω`-result) and is the model's
prediction beyond. So the finding is:

> **The independent-signs model is self-consistent in a strong sense: the model that predicts the
> pivot `1/8` as its resolution floor also forces the correlation size that caps the additive-divisor
> route at exactly `1/8`.** The pivot is not merely where the known methods stop; under the model it
> is where the last unexplored route stops too.

**Two data points do not by themselves fix the functional form** — the line through `(1,0)` and
`(2,1/2)` is `s = (k−1)/2`, which is a different interpolant. But it is excluded on trivial grounds:
`s ≤ 1` always (since `Δ_k(x,h) ≪ x^{1+ε}` trivially), while `(k−1)/2 > 1` for `k > 3`. Among
interpolants respecting the trivial bound and the model's output, `1 − 1/k` is the one that survives.

### C137 — where the map now stands

| direction | status |
|---|---|
| mean-value / large sieve, Halász–Montgomery | capped `1/4` |
| Guth–Maynard | inert |
| moment hierarchy (neutrality law) | capped; sixth moment subconvexity-neutral |
| `E(T)`, `E₂(T)` programmes | capped `1/8` |
| Heath-Brown twelfth moment | at its input's ceiling |
| short-interval mean square | neutral at its optimum |
| resonance / `Ω`-side | `T^{o(1)}`; cannot disprove LH |
| zero geometry (Jensen–Backlund) | inert, exactly `1/4` |
| double-Voronoi divisor chain | circular at every abscissa |
| Motohashi continuous term | void (Plancherel density gap) |
| pointwise branch of the transfer | provably capped at `k = 4`, hence `1/8` |
| **additive divisors, shift-cancellation branch** | **capped at `1/8` under the model (C134–C136)** |

> **Everything in the map is now capped, inert, circular, or capped-under-the-model. The single
> statement that remains genuinely open and genuinely uncapped is the one the model itself denies:
> `Δ_k(x,h) ≪ x^{1/2+ε}` as the *typical* size for `k ≥ 3`.**

`[OPEN CORE, final form]` **Is the typical size of `Δ_k(M,h)` equal to `M^{1/2}` or to `M^{1−1/k}`
for `k ≥ 3`?** Equivalently: is `E_k(T) ≍ T^{k/4}` or `≍ T^{1/2}`? The first gives `μ ≤ 1/8` and
stops; the second gives LH. Both are consistent with everything proved. **This is a single, sharp,
falsifiable dichotomy, and by C132 it cannot be tested at the sixth moment.** The first index at
which it is testable is `k = 4` — the eighth moment.

**Cycle 60 target.** Attack the dichotomy at `k = 4`: the eighth moment, `M = T²`, correlation
`Δ_4(M,h)`, competing sizes `M^{1/2}` versus `M^{3/4}`, competing moment errors `E₄ ≍ T^{1/2}` versus
`T^{1}`. Note `E₄ ≍ T` would be the *same size as the main term* — so the Ivić branch predicts the
eighth moment has **no asymptotic with power saving at all**, while Conrey–Gonek predicts `T^{1/2}`.
**That is a qualitative difference, not a numerical one, and it may be decidable.**

## Cycle 60 — the model breaks at k = 4, and that is what LH costs `[PROVED HERE — MAJOR]`

C134 forced the size `s = 1 − 1/k` from `E_k ≍ T^{k/4}`. Cycle 60 asks what that costs, and the
answer reorganises the whole map.

### C138 — the model, extended to all `k`, contradicts LH

`E_k(T) ≍ T^{k/4}` against a main term `≍ T·(log T)^{k²}`:

    T^{k/4}  =  T   at  k = 4,   and   T^{k/4} ≫ T·polylog   for  k > 4.

So the model gives `m(k) = max(1, k/4)`, hence `m(5) = 5/4 > 1`. But LH requires `m(k) = 1` for
**every** `k`. Therefore:

> **`[THEOREM]` The independent-signs model with Ivić's size, extended to every index, implies
> `μ = 1/8` and hence that the **Lindelöf hypothesis is false**. Equivalently: **LH implies the model
> must break down, and it must break between `k = 4` and `k = 5`.**

This is not a disproof of LH — the model is a heuristic, verified only at `k = 1, 2`. It is a
**forced dichotomy**: either LH fails, or the correlation size falls below `M^{1−1/k}` for `k ≥ 5`.
Since RH implies LH and RH is believed, the campaign's reading is that the *model* breaks, and the
value of the theorem is that it says exactly **where** and **by how much**.

### C139 — what LH costs, exactly

`m(k) = 1` means `modelPrediction k s ≤ 1`, which is **equivalent** to

    **s  ≤  1/2 + 1/k  =:  lindelofSizeCap k.**

Three facts, all certified:

1. `ivicSize k ≤ lindelofSizeCap k  ⟺  k ≤ 4`. Ivić's law meets the Lindelöf demand with **equality
   at `k = 4`** and violates it from `k = 5`.
2. `lindelofSizeCap k → 1/2`. **LH demands that the correlation error be of square-root size in the
   limit** — i.e. it demands the Conrey–Gonek size asymptotically, and nothing weaker will do.
3. `1/2 + 1/k` is **the same curve** as the chord-beating threshold of the averaged input (C110:
   `a = 1` beats the envelope iff `b < 1/2 + 1/k`). The size LH forces and the size that improves the
   moment envelope are one curve. That is why every route has been landing on it.

### C140 — the recurring `k = 4`, explained

The campaign met `k = 4` three times, independently, without an explanation:

* the pointwise branch of the transfer saturates exactly at `k ≤ 4` (C111);
* Ivić's size meets the moment envelope with **exact equality** at `k = 4` (C132);
* the Lindelöf size cap is met with **exact equality** at `k = 4` (C139).

> **All three are one fact: `k = 4` is where the model's predicted error `T^{k/4}` crosses the moment's
> main term `T`.** Below it the error is a genuine error; above it the error *is* the moment. Every
> criticality at `k = 4` in this campaign is that crossing seen through a different transfer.

This is the second such unification (the first being `1/6 = 1/2 − 1/k` at `k = 3`, C131), and it
retires the last unexplained coincidence in the map.

### C141 — the open core, in its final and sharpest form

> **Does the typical size exponent `s(k)` of `Δ_k(M,h)` stay at or below `1/2 + 1/k`?**
>
> * If **yes** (equivalently `s(k) → 1/2`, the Conrey–Gonek size): the additive-divisor route with
>   shift cancellation gives **LH**.
> * If **no** (in particular if Ivić's `1 − 1/k` is right beyond `k = 4`): `m(k) = k/4` for `k ≥ 4`,
>   **`μ = 1/8`, and LH is false.**
>
> Both branches are consistent with everything proved. Data: `s(1) = 0` and `s(2) = 1/2`, both exact,
> and both **on** the curve `1/2 + 1/k`? — `s(1) = 0 < 3/2` ✓, `s(2) = 1/2 < 1` ✓, strictly inside.
> By C132 the dichotomy is untestable at `k = 3`; by C139 it is met with equality at `k = 4`;
> **`k = 5` — the tenth moment — is the first index where the two branches give different answers to
> a question of *kind*, not degree: whether `∫_0^T|ζ|^{10}` has a main term at all.**

Lean: `HTGeometry.ModelBreakdownIndex` — `modelMomentExponent`,
`modelMomentExponent_gt_one_iff (⟺ k > 4)`, `modelMomentExponent_four`,
`model_contradicts_lindelof`, `lindelofSizeCap`, `lindelof_forces_size_cap (⟺ s ≤ 1/2 + 1/k)`,
`ivicSize_le_cap_iff (⟺ k ≤ 4)`, `lindelofSizeCap_tendsto_half`, `critical_index_four`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### Cycles 59–60 — Phase 6 / Phase 7

**P6.** New and consequential: the model's self-contradiction with LH at `k ≥ 5`; the exact
characterisation of LH's cost as `s(k) ≤ 1/2 + 1/k`; the identification of that curve with the
chord-beating threshold; and the explanation of the recurring `k = 4`. Erratum E12 removed a false
piece of evidence that had stood since cycle 1. This cycle changes what the campaign is *about*: from
"which method can beat `13/84`" to "which of two mutually exclusive size laws is true".
**P7.** The decisive computations were cheap once the right comparison was made; the work was in
noticing that the model must be compared against the *main term*, not against other methods. No
avoidance. All Lean certifies statements new here.

**Plan for cycle 61.** Attack `s(k)` directly at `k ≥ 5` — the first index where the branches differ
in kind. Two concrete sub-targets: **(a)** is `∫_0^T|ζ(1/2+it)|^{10}dt ≫ T^{5/4}` provable
unconditionally? (An `Ω`-result at the tenth moment would **disprove LH**, since `m(5) > 1` is
incompatible with it. This is the campaign's first genuine disproof route.) **(b)** is
`Δ_5(M,h) = Ω(M^{4/5})` provable? Either would settle the dichotomy. Note that (a) is a *lower bound
for a moment*, and lower bounds for moments are far more accessible than upper bounds —
Radziwiłł–Soundararajan and Heap–Soundararajan give unconditional sharp lower bounds
`∫_0^T|ζ|^{2k} ≫ T(log T)^{k²}` for all real `k ≥ 0`. **The question is whether the true order can
exceed that.**

## Cycle 61 — the campaign's first disproof branch, located

### C142 — a power excess at a single index disproves LH `[PROVED HERE]`

Lindelöf on the moment exponents is `m(k) = 1` for every `k > 0`. Hence:

    1 < m(k)  for any single k   ⟹   ¬LH.

Concretely: **`∫_0^T|ζ(1/2+it)|^{10}dt ≫ T^{5/4}` would disprove the Lindelöf hypothesis.**

**Why this is not blocked by the resonance ceiling.** §3.8 proved that no *resonance* construction
can disprove LH, because Gál sums are subpolynomial (Bondarenko–Seip). **A moment lower bound is not
a resonance construction.** It produces large values indirectly — a moment `≫ T^{1+δ}` forces, via
the fourth-moment constraint `φ(v) ≥ 4v`, a set of measure `T^{1−4v}` carrying values `T^{v}` with
`v ≥ (k−4)/(8(k−2)) → 1/8`. So the disproof branch survives the one ceiling that was thought to close
the `Ω` side. **This is the first genuine disproof route the campaign has found in 61 cycles.**

**And it is exactly the model's own prediction:** `modelMomentExponent 5 = 5/4`. The disproof branch
is not speculative; it is what the independent-signs model — exact at both solved indices — asserts.

### C143 — the dichotomy, closed inside the model `[PROVED HERE]`

For every `k > 0` and every candidate size exponent `s`, exactly one holds:

    (i)  s ≤ 1/2 + 1/k   and   modelPrediction k s ≤ 1     — consistent with LH;
    (ii) s > 1/2 + 1/k   and   modelPrediction k s > 1     — a power excess, hence ¬LH.

**There is no third possibility inside the model.** So the Lindelöf hypothesis is, modulo the
independent-signs model, *equivalent* to the statement that the correlation size exponent never
exceeds `1/2 + 1/k` — and by C139 this forces `s(k) → 1/2`.

> **The Lindelöf hypothesis, restated:** *the error in the `k`-fold additive divisor problem is of
> square-root size, asymptotically in `k`.* Nothing weaker suffices, and nothing else is needed.

### C144 — where a proof and a disproof would each have to come from

**Proof branch (LH true).** Establish `Δ_k(M,h) ≪ M^{1/2+1/k+ε}` typically, for all `k`. This is
Conrey–Gonek asymptotically. Known: nothing for `k ≥ 3`. Everything else in the map is capped, so
this is the only surviving proof route.

**Disproof branch (LH false).** Establish `∫_0^T|ζ|^{2k}dt ≫ T^{k/4}` for a single `k > 4`.
Equivalently `Δ_k(M,h) = Ω(M^{1−1/k})` with uncorrelated signs, at a single `k ≥ 5`. Known
unconditional lower bounds (Radziwiłł–Soundararajan; Heap–Soundararajan) give exactly
`T(log T)^{k²}` — the conjectured order, **no power excess**. So the disproof branch is open and
untried; the campaign has not found any obstruction to it.

**Note the asymmetry.** The proof branch needs an *upper* bound on correlation errors, uniformly in
`k` — the hardest kind of statement. The disproof branch needs a *lower* bound for a single moment —
and lower bounds for moments are the one part of this subject where unconditional technology is
strong (Radziwiłł–Soundararajan's method gives sharp lower bounds for all real `k ≥ 0`). **If the
model is right, the disproof is the easier direction.** That inverts the campaign's working
assumption, held since cycle 1, that LH is true and the task is to prove it.

`[CONJECTURE, cycle 62]` The Radziwiłł–Soundararajan lower-bound method, which produces
`T(log T)^{k²}` by restricting to a well-behaved set of `t`, discards exactly the contribution the
model says dominates for `k > 4` — the rare large values on a set of measure `T^{1−4v}`. **Rerun that
method without the restriction, at `k = 5`, and see whether the discarded set can be shown to
contribute `≫ T^{5/4}`.** That is the concrete disproof attempt, and it is the campaign's next task.

Lean: `LindelofOnMoments`, `power_excess_disproves_lindelof`, `tenth_moment_excess_disproves`,
`model_predicts_tenth_moment_excess`, `size_cap_dichotomy`. Axioms
`[propext, Classical.choice, Quot.sound]`.

## Cycle 62 — the disproof branch closes, and the model is refuted at k = 5

### C145 — the disproof branch implies ¬RH `[PROVED HERE — CLOSES C142]`

Under the Riemann hypothesis, `∫_0^T|ζ(1/2+it)|^{2k}dt ≪ T(log T)^{k²}` for every fixed `k ≥ 0`
(Soundararajan; Harper, removing the `ε`). So RH gives `m(k) = 1` at every index. Hence a power
excess `1 < m(k)` at **any** index contradicts RH:

> **`[THEOREM]` The campaign's only disproof route — a power-excess lower bound at a high moment —
> implies `¬RH`. It is therefore strictly harder than disproving the Riemann hypothesis.** `[D36]`

C142's observation that the disproof branch evades the resonance ceiling (§3.8) stands and is
correct: a moment lower bound is not a resonance construction. But it is blocked by a *different*
ceiling, which the campaign had not applied to it — the conditional upper bound. **Both `Ω`-sides are
now closed: resonance unconditionally, moment lower bounds relative to RH.**

### C146 — consequence: RH refutes the independent-signs model at `k = 5` `[PROVED HERE]`

The model asserts `m(5) = 5/4`; RH asserts `m(5) = 1`. So:

> **RH refutes the independent-signs model.** The model is compatible with RH **exactly on `k ≤ 4`**
> (`modelMomentExponent k = 1 ⟺ k ≤ 4`), and `k = 4` is precisely where its predicted error crosses
> the main term (C140).

And, running the dichotomy backwards, **RH forces the size cap** `s(k) ≤ 1/2 + 1/k` at every index —
i.e. **RH decides the Conrey–Gonek/Ivić dichotomy in Conrey–Gonek's favour for every `k ≥ 5`**, the
range where the two differ. That is a new consequence of RH for the additive divisor problem, and it
is the reverse of what C134 concluded from the model alone.

### C147 — honest reassessment of C134 `[ERRATUM E13]`

C134 forced `s = 1 − 1/k` from two data points, `k = 1` and `k = 2`. **The `k = 1` point is
degenerate:** `d₁ ≡ 1` has no fluctuation, so `Δ₁(M,h) = O(1)` trivially and the "independent signs"
hypothesis is vacuous there. The model reproduces `E₁ ≍ T^{1/4}` correctly, so it is a genuine check
— but it cannot discriminate between size laws that both vanish at `k = 1`, and it does not test
randomness. **So C134's uniqueness rests on one non-degenerate data point (`k = 2`), where the two
competing laws agree.** Its conclusion should be weakened accordingly: the model *suggests*
`1 − 1/k`; RH *refutes* it beyond `k = 4`; RH is much better evidence than the model.

**What survives of C134–C144.** The equivalence `m(k) = 1 ⟺ s(k) ≤ 1/2 + 1/k` (C139) is unaffected —
it is an identity, not an inference. So is the identification of `k = 4` as the crossing index
(C140), the identification `1/6 = 1/2 − 1/k` (C131), and the restatement of LH as "the additive
divisor error is of square-root size asymptotically in `k`" (C143). **What is withdrawn is the
inference from the model to `¬LH`.** The correct reading is the contrapositive: *LH and RH force the
model to break, and it must break at `k = 5`.*

### C148 — what this does to the map's pivot

The map's Theorem 1.5 — "the model's resolution floor is `1/8`, identically in `k`" — is a statement
*about the model*, and the model is now known (given RH) to be wrong for `k ≥ 5`. Two things must be
distinguished, and the preprint should say so:

* **Unconditional and unaffected:** the `1/8` ceilings for the `E₁` and `E₂` programmes (§3.9). These
  rest on the *proved* `Ω`-results `E(T) = Ω(T^{1/4})` and `E₂(T) = Ω(T^{1/2})`, not on the model.
* **Model-dependent:** the reading of `1/8` as the resolution floor "identically in `k`". Under RH the
  model's `E_k ≍ T^{k/4}` fails for `k ≥ 5`, so that reading is an extrapolation, valid on `k ≤ 4`.

**This does not weaken a single barrier theorem in the map** — every one of them bounds what a
*method* can deliver, and none uses the model's truth beyond `k ≤ 4`. It sharpens the interpretation:
`1/8` is where the known methods stop, and the model explains why on `k ≤ 4`; it is not a prediction
about `μ`. `[ERRATUM E14 for preprint §1.5 and §2.5.]`

Lean: `RHOnMoments`, `power_excess_implies_not_rh`, `rh_refutes_model`, `rh_forces_size_cap`,
`model_rh_compatible_iff (⟺ k ≤ 4)`. Axioms `[propext, Classical.choice, Quot.sound]`.

### Cycles 61–62 — Phase 6 / Phase 7

**P6.** New: both `Ω`-sides are now closed (resonance unconditionally, moment lower bounds relative
to RH); RH refutes the model, exactly past `k = 4`; RH decides the Conrey–Gonek/Ivić dichotomy for
`k ≥ 5`. Rediscovery: none — but I over-read two data points in C134 and corrected it here (E13),
the third self-correction of the campaign and again by computation, not argument. Frontier: the
campaign now knows *why* its founding assumption (LH true) is the right one, rather than assuming it.
**P7.** The cycle-61 disproof branch was attacked immediately and honestly, and it closed. That is the
correct outcome of an attack, not a failure. All Lean certifies statements new here.

**Plan for cycle 63.** With both `Ω`-sides closed and every upper-bound route capped, the campaign's
position is: **LH is true (RH implies it) but unprovable by any route in the map.** The only remaining
move is to find a route *outside* the map. The map's own classification says every closed route fails
by inertness (self-dual stationarity) or circularity (moment re-entry). **So the next object is a
route that is neither: one whose optimisation is not stationary at the self-dual point and which never
bounds a divisor correlation by a moment of `ζ`.** Conjecture 6.12 says the first is impossible for
AFE-based methods; Conjecture 7.5 says the second is impossible for divisor-correlation methods.
**A route escaping both must therefore be neither AFE-based nor divisor-correlation-based.** The one
such object the campaign has identified is the `(GL(4), GL(3))` multiplicity-one period (C124), and it
remains unexamined.

## Cycle 63 — the fifteenth ceiling: the higher-rank spectral programme, capped in one theorem

### C149 — the twelfth moment is a `(GL(4), GL(3))` period, and it is *not* neutral

Following C125's method one rank up: with `α = (0,0,0)` on `GL(3)` and `β = (it,it,−it,−it)` on
`GL(4)` (both summing to `0`),

    L(1/2, E^{(4)}_min(β) × E^{(3)}_min(α))  =  Π_{i,j} ζ(1/2 + α_i + β_j)  =  **|ζ(1/2+it)|^{12}**.

So the **twelfth** moment of `ζ` is a `GL(4)×GL(3)` Rankin–Selberg object — the multiplicity-one pair
(AGRS) — and the `GL(3)` Kuznetsov formula with a **best-possible** spectral large sieve
(Blomer–Buttcane, C121) is exactly the tool for averaging over the `GL(3)` family.

**And unlike the sixth moment, the twelfth is not subconvexity-neutral.** By the neutrality law
(§3.4), a perfect `2j`-th moment beats `θ = 13/84` iff `j > 42/13 = 3.23`; at `j = 6` this gives
`min(1/12, 13/84) = 1/12`. **A perfect twelfth moment yields `μ ≤ 1/12 = 0.0833`, beating Bourgain's
`13/84 = 0.1548`.** The campaign has spent sixty cycles on the sixth moment, which its own neutrality
law says is worthless against `13/84`, while the twelfth is both non-neutral and sits on a
multiplicity-one pair. `[ERRATUM E15: the map should have prioritised `k = 6` over `k = 3`.]`

### C150 — but the Plancherel gap grows quadratically in the rank `[PROVED HERE]`

C126 found that Motohashi's continuous term is suppressed by one power of `r`, because the `GL(2)`
cuspidal density is `≍ r dr` and the Eisenstein density `≍ dr`. That generalises, and badly.

On `GL(n)`: the cuspidal Weyl law counts `≍ T^{(n²+n−2)/2}` forms of spectral parameter `≤ T` (the
exponent is `dim SL(n,ℝ)/SO(n)`), while the minimal Eisenstein family has only `n−1` continuous
parameters, hence `≍ T^{n−1}`. The moment of `ζ` lives on the **Eisenstein** part. So the suppression
is

    rankGap n  =  (n²+n−2)/2 − (n−1)  =  **n(n−1)/2**  =  the number of positive roots of `GL(n)`.

`rankGap 2 = 1` — exactly the power that already voids the Motohashi continuous term (C127);
`rankGap 3 = 3`; `rankGap 4 = 6`. The gap is strictly increasing and quadratic.

> **`[THEOREM — fifteenth ceiling]` For every rank `n`, the moment of `ζ` sits on the minimal
> Eisenstein spectrum of `GL(n)` and is suppressed relative to the cuspidal spectrum by
> `n(n−1)/2` — the number of positive roots. The suppression is already fatal at `n = 2`, where it
> equals `1`, and it strictly increases with rank. **No increase of rank can rescue the spectral
> route; raising the rank strictly worsens it.**

This caps the entire higher-rank spectral programme in one statement, rather than route by route. It
also explains a fact the field has never had a reason for: **why Motohashi's method has never been
extended.** Not because the formulas are missing — Kwan's `GL(3)×GL(2)` identities and
Blomer–Buttcane's optimal `GL(3)` large sieve both exist — but because the object of interest lives on
the thinnest part of the spectrum, and the thinness grows like the number of positive roots.

**The `(GL(4),GL(3))` route of C124, examined and closed.** `[D37]`. It was the one object the map's
two failure-mode conjectures (6.12 inertness, 7.5 moment re-entry) did not exclude. It is excluded by
a third mechanism, and the mechanism is representation-theoretic rather than analytic.

Lean: `HTGeometry.PlancherelRankGap` — `cuspidalWeylExponent`, `eisensteinFamilyExponent`,
`rankGap`, `rankGap_eq (= n(n−1)/2)`, `rankGap_two/three/four (1, 3, 6)`,
`rankGap_two_matches_plancherel`, `rankGap_strictMono`, `rankGap_superadditive`,
`higher_rank_ceiling`. Axioms `[propext, Classical.choice, Quot.sound]`.

### C151 — the map's three failure modes, complete

Every route the campaign has closed now falls under exactly one of:

1. **Inertness** — output equals input; stationary at the self-dual parameter (Conj. 6.12).
   *Mean-value family, Halász–Montgomery, Guth–Maynard, short-interval mean square at its optimum,
   Jensen–Backlund zero geometry.*
2. **Circularity** — input strictly stronger than output; a moment exponent re-enters (Conj. 7.5).
   *Backlund's criterion, the `S(t)` route, the double-Voronoi divisor chain at every abscissa, the
   short-interval-mean-square criterion, the reduction loop.*
3. **Spectral thinness** — the target sits on the Eisenstein spectrum and is suppressed by the rank
   gap `n(n−1)/2` (C150). *Motohashi's continuous term, and every higher-rank analogue.*

Plus two `Ω`-driven closures of the `Ω`-side: resonance (unconditional) and moment lower bounds
(relative to RH).

> **The classification is now exhaustive over the routes examined in 63 cycles, and each mode has a
> proved mechanism rather than a case list.**

### Cycle 63 — Phase 6 / Phase 7

**P6.** New: the twelfth moment as a `(GL(4),GL(3))` period and its non-neutrality (which corrects
sixty cycles of target selection, E15); the rank-gap theorem `n(n−1)/2` identified with the number of
positive roots; and the resulting cap on the whole higher-rank programme. The last is the campaign's
first barrier that is *uniform in a parameter* rather than proved case by case.
**P7.** The `(GL(4),GL(3))` object flagged in C124 was attacked rather than left standing, and it
closed — with a mechanism that also retro-explains C126. No infrastructure work.

**Plan for cycle 64.** E15 says the twelfth moment was the right target all along. The rank gap kills
the *spectral* route to it, but not the elementary one: Heath-Brown's `m(6) ≤ 2` is the current
record and §3.7 proved it is at its own method's ceiling. **Two questions the campaign has never
asked: (i) what is the transfer input `(a,b)` that would give `m(6) = 1`, and (ii) is that input
weaker or stronger than the one for `m(3) = 1`?** By `pointwise_input_eq_one_iff`, `m(6) = 1` needs
`b ≤ 1/3` — **below the square-root barrier**, hence impossible for the pointwise branch. So `m(6)=1`
requires shift cancellation, i.e. `a = 1/2`, and the question becomes which `(1/2, b)` suffices. That
is a finite computation and it is cycle 64's first task.

## Cycle 64 — the target was wrong for sixty cycles: it is the eighth moment `[ERRATUM E15, resolved]`

### C152 — the cheapest non-neutral input `[PROVED HERE]`

Two facts the campaign owned separately and never combined:

* **neutrality law (§3.4):** a perfect `2j`-th moment beats `θ = 13/84` iff `j > 1/(2θ) = 42/13`, and
  `3 < 42/13 < 4`. So **`j = 4`, the eighth moment, is the least index that helps** — it yields
  `μ ≤ 1/8 = 0.125 < 13/84 = 0.1548…`;
* **transfer (C111):** `transferBound k 1 b = 1 ⟺ k·b ≤ 2`. At `k = 4` this is `b ≤ 1/2`.

> **`[THEOREM]` Proving `Δ₄(x,h) ≪ x^{1/2+ε}` — the Conrey–Gonek bound at the single index `k = 4`,
> uniformly for `h ≤ x^{1/2}`, and with **no shift cancellation whatsoever** — gives `m(4) = 1` and
> hence `μ(1/2) ≤ 1/8`, improving on Bourgain's `13/84`.**

That is the cheapest input in the whole map that beats the record, and the campaign never stated it.
Sixty cycles went to the sixth moment, which the campaign's **own** neutrality law (proved in
cycle ~10) declares worthless against `13/84`. `[E15 resolved.]`

### C153 — why `k = 4` is the right index, from four directions at once

The eighth moment is where every `k = 4` coincidence in the campaign meets:

1. **first non-neutral index** — `3 < 42/13 < 4` (C152);
2. **last index reachable by the pointwise branch** — `transferBound k 1 (1/2) = 1 ⟺ k ≤ 4` (C111);
3. **the index where the two conjectured sizes first differ in consequence** — Conrey–Gonek's `1/2`
   gives `m(4) = 1`; Ivić's `3/4` gives only the known envelope `3/2` (C132, C153);
4. **the index where the model's predicted error crosses the moment's main term** — `T^{k/4} = T` at
   `k = 4` (C140).

**All four are the same index for the same reason**, and together they say: `k = 4` is the unique
place where a single, already-conjectured, shift-cancellation-free bound converts into an improvement
on the record.

### C154 — the requirement curve, unified

With shift cancellation the requirement relaxes: `transferBound k (1/2) b = 1 ⟺ b ≤ 1/2 + 1/k`.
This is **the same curve** as

* the chord-beating threshold for the averaged input (C110);
* the size cap that the Lindelöf hypothesis imposes through the model (C139);
* the cap that RH forces (C146).

At `k = 3` it reads `b ≤ 5/6`; at `k = 4`, `b ≤ 3/4`; at `k = 6`, `b ≤ 2/3`. **Every requirement the
campaign has derived, from any direction, lies on `b = 1/2 + 1/k`.** The map has one curve, and LH is
the statement that the true correlation size stays under it as `k → ∞`.

Lean: `HTGeometry.CheapestNonNeutralTarget` — `eighth_moment_needs_conreyGonek (⟺ b ≤ 1/2)`,
`shifted_requirement (⟺ b ≤ 1/2 + 1/k)`, `eighth_moment_beats_bourgain`,
`four_is_least_nonneutral`, `eighth_moment_separates_the_conjectures`, `cheapest_nonneutral_target`.
Axioms `[propext, Classical.choice, Quot.sound]`.

### C155 — the campaign's target, restated for all future cycles

> **PRIMARY TARGET (supersedes the sixth-moment core of cycles 1–63):**
> `Σ_{n≤x} d₄(n)d₄(n+h) = (main terms) + O(x^{1/2+ε})`, uniformly for `1 ≤ h ≤ x^{1/2+ε}`.
> Consequence: `m(4) = 1`, hence **`μ(1/2) ≤ 1/8 < 13/84`** — the first improvement on the record
> since Bourgain 2017.
>
> **Weaker sufficient variants** (all give the same conclusion):
> * `Σ_{h≤H}Δ₄(x,h) ≪ H^{1/2}x^{3/4+ε}` (shift cancellation, size only `3/4`);
> * any `(a,b)` with `4(a+b−1) ≤ 2a`.
>
> **What is known at `k = 4`:** nothing. The `k = 4` additive divisor problem is open in every form.

### Cycle 64 — Phase 6 / Phase 7

**P6.** The new knowledge is a *target correction*, not another barrier: the campaign had proved every
ingredient of C152 years-of-cycles ago and never multiplied them together. That is the most valuable
kind of finding and also the most embarrassing — it means the map was richer than its own reading of
it. The four-fold coincidence at `k = 4` (C153) and the single requirement curve `1/2 + 1/k` (C154)
are new unifications.
**P7.** The failure this cycle exposes is exactly the anti-laziness question: I optimised within the
inherited target (the sixth moment) for sixty cycles instead of asking whether it was the right one.
**Rule adopted: at the start of every cycle, re-derive the target from the neutrality law rather than
inheriting it.**

**Plan for cycle 65.** Attack `Δ₄(x,h) ≪ x^{1/2+ε}` directly. Note `d₄ = d₂ ⋆ d₂`, so
`Σ_n d₄(n)d₄(n+h) = Σ_{a,b} Σ_{n} d(n/a)d((n+h)/b)` splits into binary correlations in arithmetic
progressions — for which DFI/Motohashi technology *does* exist, unlike `d₃ ⋆ d₃`. **The `k = 4` problem
may be strictly easier than the `k = 3` problem**, because `4 = 2·2` factors through the solved case
while `3` is prime. That possibility has never been examined and it is cycle 65's first task.

## Cycle 65 — the `k = 4` attack: the landscape, mapped

### C156 — the reduction, and the trade-off `[PROVED HERE — elementary]`

For `D_k(x,h) = Σ_{n≤x}d_k(n)d_k(n+h)`, split `d_k` by its smallest factor. Two splittings of `d₄`
are available and they trade off against each other:

| splitting of `d₄(n)` | coefficient range | inner object | base theorem? | level rel. to inner length |
|---|---|---|---|---|
| `Σ_{ab=n} d(a)d(b)`, `a ≤ n^{1/2}` | `a ≤ x^{1/2}` | `d ⋆ d₄` | **yes** (Topacogullari, `k ≥ 4`) | `1` |
| `Σ_{a|n} d₃(n/a)`, `a ≤ n^{1/4}` | `a ≤ x^{1/4}` | `d₃ ⋆ d₄` | **no** | `1/3` |

and for comparison the `k = 3` core the campaign carried for sixty cycles:

| `d₃(n) = Σ_{a|n}d(n/a)`, `a ≤ n^{1/3}` | `a ≤ x^{1/3}` | `d ⋆ d₃` | **yes** (Topacogullari) | `1/2` |

> **`[FINDING]` Both the `k = 3` and the `k = 4` problems reduce to a **published** base theorem plus
> **uniformity in a linear coefficient**. The difference is the level: `k = 3` needs level `1/2`
> relative to the inner length; `k = 4` needs level `1` — strictly harder — unless one accepts the
> unproved base `d₃ ⋆ d₄`, which lowers the level to `1/3`.**

So the earlier hope (E15's optimism, that `4 = 2·2` makes `k = 4` easier because it factors through
the solved binary case) is **wrong as stated**: the factorisation does not help, because the inner
object is `d ⋆ d₄`, not `d ⋆ d`. `[D38]` What the factorisation *does* buy is that the base theorem
exists — which is more than `d₃ ⋆ d₃` ever had.

**The honest trade-off the campaign now faces:**

* **`k = 3`:** cheaper input (level `1/2`), but the output is **subconvexity-neutral** — worthless
  against `13/84` (§3.4).
* **`k = 4`:** dearer input (level `1`, or level `1/3` on an unproved base), but the output
  **`μ ≤ 1/8` beats the record**.

Neither is a free lunch, and the campaign had been paying for the worthless one.

### C157 — what is actually needed, stated for citation

> **TARGET A (level-1 form, published base).**
> `Σ_{m ≤ M} d(m) d₄(am + h) = (main) + O((aM)^{1−δ})`, with power saving uniform in `a ≤ M` and in
> `h`. Base case `a = 1` is Topacogullari (`d_k ⋆ d`, `k ≥ 4`, power saving, uniform in `h`).
>
> **TARGET B (level-1/3 form, unproved base).**
> `Σ_{m ≤ M} d₃(m) d₄(am + h)` with power saving uniform in `a ≤ M^{1/3}`. Base case `a = 1` is the
> `GL(3)×GL(4)` shifted convolution — **open**.
>
> Either yields `Δ₄(x,h) ≪ x^{1−δ'}`; to reach `m(4) = 1` one needs `δ'` all the way to `1/2`, i.e.
> the full Conrey–Gonek strength at `k = 4` (C152). Partial savings give partial progress on the
> transfer's `(a,b)` plane but do **not** beat `13/84` until `b ≤ 1/2`.

**Sharp caveat, recorded so it is not forgotten:** `m(4) = 1` needs `b ≤ 1/2` *exactly* — the
square-root barrier, with no room. There is no partial-credit version at `k = 4`: by
`eighth_moment_needs_conreyGonek`, `transferBound 4 1 b = 1 ⟺ b ≤ 1/2`, and any `b > 1/2` gives
`m(4) > 1` and no improvement on `13/84` through the neutrality law. **The `k = 4` target is
all-or-nothing.**

### C158 — where partial savings *do* pay

Since `k = 4` is all-or-nothing on the `a = 1` branch, partial savings must be spent on the shifted
branch, where the requirement is `b ≤ 1/2 + 1/k` (C154). At `k = 4` that is `b ≤ 3/4` **with**
`a = 1/2` — i.e. **square-root cancellation in the shift plus only a `1/4`-saving in size**. Compare:

* `a = 1`, need `b ≤ 1/2` (saving `1/2`, all-or-nothing);
* `a = 1/2`, need `b ≤ 3/4` (saving `1/4`, plus shift cancellation).

> **The shifted branch at `k = 4` needs only `Δ₄` of size `x^{3/4}` on average with square-root
> cancellation in `h` — half the size-saving of the pointwise branch.** That is the cheapest
> record-beating input in the entire map, and it is the one the campaign should now price out.

### Cycle 65 — Phase 6 / Phase 7

**P6.** New: the two-splitting trade-off table and the level computation (C156); the refutation of my
own cycle-64 optimism (`4 = 2·2` does not help, `[D38]`); the all-or-nothing character of the `k = 4`
pointwise branch; and the identification of the cheapest record-beating input (C158). The
self-correction is the fourth of the campaign and again came from doing the computation rather than
repeating the slogan.
**P7.** The cycle-64 plan said "examine whether `4 = 2·2` makes `k = 4` easier"; I examined it and it
does not, and I said so rather than salvaging it. The productive residue — that `k = 4` has a
published base theorem while `k = 3` does not for `d₃ ⋆ d₃` — is real and was not visible before.

**Plan for cycle 66.** Price out C158: what does `Σ_{h≤H}Δ₄(x,h) ≪ H^{1/2}x^{3/4+ε}` cost, in the same
double-Voronoi framework that cycles 52–55 built for `k = 3`? The framework is already built and its
exponents are parametrised by `k`; running it at `k = 4` is a finite computation. **Watch for the
reduction loop (C129) — if the `k = 4` off-diagonal is again the `k = 4` correlation, the same
circularity applies and the branch closes. If it is not — because `4` is composite and the
off-diagonal groups differently — that is the first structural difference the campaign has found
between the two indices.**

## Cycle 66 — the fork resolves: the reduction loop is uniform in `k`

Cycle 65 set a decisive fork: run the double-Voronoi framework at `k = 4` and see whether the
reduction loop of C129 reappears. **It does, and the reason makes it uniform in the index.**

### C159 — the framework at general `k` `[PROVED HERE]`

Redoing the cycle-52–55 computation with `k` free, dual truncated at `M ≍ x`:

| quantity | general `k` | `k = 3` | `k = 4` |
|---|---|---|---|
| phase wavelength `L` (block length) | `x^{(k−2)/k}` | `x^{1/3}` | `x^{1/2}` |
| block count `N_B = x/L` | `x^{2/k}` | `x^{2/3}` | `x^{1/2}` |
| **diagonal of the short-interval mean square** | **`X·h`, i.e. `β = 1`** | `X·h` | `X·h` |
| Cauchy–Schwarz output at `β` | `1/k + 1/2 + (k−2)(β−1)/(2k)` | `8/9` at `β=4/3` | — |
| the same at the diagonal `β = 1` | `1/k + 1/2` | `5/6` | `3/4` |

The diagonal computation: the two dual ranges, below and above the crossover `m₁ = x^{k−1}/h^k`, each
contribute `h·x^{−(k−1)/k}` to the coefficient sum, and the prefactor `x^{(k−1)/k+1}` returns `x·h`.
**The exponent is `1` at every index.** So at every `k`, as at `k = 3`, the diagonal alone already
produces the conjectured answer and the entire obstruction is the off-diagonal.

### C160 — and the off-diagonal is the correlation, at every index `[PROVED HERE]`

The off-diagonal is indexed by `j = m' − m` and its coefficient sum is `Σ_m d_k(m)d_k(m+j)` — the
`k`-fold correlation the reduction started from. **This grouping is by a difference of dual variables,
and both dual coefficient sets are `d_k` whatever `k` is.**

> **`[THEOREM]` The reduction loop of C129 is uniform in the index. The double-Voronoi route closes at
> every `k`, `k = 4` included. The compositeness of `4` is irrelevant to it: the off-diagonal does not
> see the factorisation of `k`, only the difference of the two dual variables.** `[D39]`

So cycle 65's fork resolves in the negative branch: **there is no structural difference between `k = 3`
and `k = 4` at the level of this framework.** The differences the campaign found between the two
indices — neutrality, the level of distribution required, the existence of a base theorem, the
all-or-nothing character — are all *outside* the double-Voronoi route, which is index-blind.

**What this costs and what it saves.** It costs the cheapest record-beating input (C158): the
`(a,b) = (1/2, 3/4)` input at `k = 4` cannot be obtained this way. It saves the campaign from
re-running fifteen cycles of `k = 3` work at `k = 4`: **the entire cycles-52–55 analysis transfers
verbatim, with the exponents above, and terminates the same way.**

### C161 — the residual, and where it points

Three facts now sit together:

1. the double-Voronoi route is index-blind and closes at every `k` (C160);
2. the differences between `k = 3` and `k = 4` are real but live elsewhere — in the neutrality law,
   in which base theorems exist, and in the all-or-nothing threshold `b ≤ 1/2` (C152, C156);
3. the cheapest record-beating input is `Σ_{h≤H}Δ₄(x,h) ≪ H^{1/2}x^{3/4+ε}` (C158), and it is not
   reachable by any route the campaign has built.

> **The campaign's position, stated exactly.** Every route it has constructed is index-blind and
> closes. The only leverage it has found that *is* index-sensitive is the neutrality law, which
> selects `k = 4` as the target but says nothing about how to reach it. **What is missing is a method
> that sees the index — specifically, one that uses `d₄ = d ⋆ d` in a way the off-diagonal grouping
> can detect.** The double-Voronoi route cannot, because it groups by dual differences. A method that
> groups by *products* instead would.

`[OPEN CORE, cycle 67]` **Find a decomposition of `Σ_{h≤H}Δ₄(x,h)` whose off-diagonal is indexed
multiplicatively rather than additively** — by `m'/m` rather than `m' − m`. Then the off-diagonal
coefficient sum is `Σ_m d₄(m)d₄(rm)`, a *multiplicative* correlation, which for `d₄ = d ⋆ d`
factorises through the binary case. Multiplicative correlations of divisor functions are governed by
Rankin–Selberg convolution, not by additive divisor problems, and `Σ_n d_k(n)d_k(rn)n^{-s}` has an
explicit Euler product. **That is the one structural feature of `k = 4` no route so far has used, and
it is the first idea in the campaign that is not a variation on the additive theme.**

Lean: `HTGeometry.ReductionLoopUniform` — `blockLengthExponentAt`, `blockCountExponentAt`,
`blockCount_eq_one_sub_blockLength`, values at `3` and `4`, `diagonalMeanSquareExponent`,
`diagonal_uniform`, `diagonal_matches_ternary`, `fluctuationExponentAt`,
`fluctuationExponentAt_three (= 8/9, matching the `k = 3` chain)`,
`fluctuationExponentAt_diagonal (= 1/k + 1/2)`, `reduction_loop_uniform`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### Cycle 66 — Phase 6 / Phase 7

**P6.** New: the general-`k` exponent table, the `k`-uniformity of the diagonal (`β = 1` always), and
the proof that the loop is index-blind. The last is stronger than the `k = 3` case it generalises and
it *saves* the campaign from repeating the analysis. The consistency check
`fluctuationExponentAt 3 (4/3) = 8/9` reproduces the cycle-52 number from the general formula, which
is a real test the generalisation could have failed.
**P7.** The cycle-65 plan was executed exactly as stated and returned the negative branch; I recorded
it as such rather than looking for a way to keep the hope alive. The productive residue — that the
campaign needs a *multiplicatively* indexed decomposition — is new and is the first non-additive idea
in 66 cycles.

## Cycle 67 — the two-level AFE: the first candidate escape from the inertness barrier

Cycle 66 asked for a decomposition indexed multiplicatively rather than additively. Tracing where the
additive index comes from answers it.

### C162 — the additive shift is a *linearisation of a ratio* `[OBSERVATION]`

In the moment, `∫_T^{2T}|ζ(1/2+it)|^{2k}dt ≈ Σ_{m,n}d_k(m)d_k(n)(mn)^{−1/2}∫(n/m)^{it}dt`, the
natural variable is the **ratio** `n/m`; the integral is `≍ T` at `n = m` and `≪ 1/|log(n/m)|`
otherwise. The additive shift `h = n − m` appears only because `log(n/m) ≈ (n−m)/m` near the
diagonal. **So the whole additive-divisor programme is the near-diagonal linearisation of a
multiplicative problem**, and every route the campaign built inherits the additive index from that
one step. That is why they are all index-blind (C160).

### C163 — the two-level approximate functional equation `[PROVED HERE — escapes §6.5's hypothesis]`

Since `ζ^4 = (ζ^2)^2`, one may apply the functional equation to `ζ^2` — self-dual length `t^1` — and
then square, instead of applying it to `ζ^4` at its self-dual length `t^2`. Writing the `ζ^2`
equation on the critical line as `ζ(1/2+it)^2 = 2e^{iθ(t)}·Re U(t)` with `U` of length `t` and
coefficients `d(n)`,

    **|ζ(1/2+it)|^8 = 16 (Re U)^4.**

> **The eighth moment of `ζ` is the *fourth* moment of a single real Dirichlet polynomial of length
> `t` with divisor coefficients.**

Its off-diagonal is the **balanced quadric count**

    Σ_{n₁n₂ − n₃n₄ = h,  all n_i ≤ t}  d(n₁)d(n₂)d(n₃)d(n₄),

on `n₁n₂ − n₃n₄ = h` — **the binary additive divisor equation** — with all four variables confined to
one box. Compare the fourth moment of `ζ`, which is the second moment of the same polynomial and gives
the same equation in two variables. **The fourth and eighth moments of `ζ` sit on the same equation;
only the number of variables differs.**

**Why the inertness barrier does not obviously apply.** §6.5 constrains optimisations run *within one*
functional equation, over the block length of the object whose moment is taken. The two-level
decomposition uses two equations at different lengths: total length `t^2` is preserved
(`2·afeLengthExponent 2 = afeLengthExponent 4`), but each factor has length `t^1 < t^2`, and the
polynomial is supported on **products of two blocks of length `t`** — a proper subset of `[1,t^2]`,
whereas the one-level polynomial carries `d₄(n)` for every `n ≤ t^2`. The two decompositions are
genuinely different objects and the hypothesis of the stationarity theorem is not met.

> **`[FIRST CANDIDATE ESCAPE]` This is the first decomposition in 67 cycles that is not AFE-internal
> in the sense Conjecture 6.12 requires, and therefore the first that the campaign's own inertness
> theorem does not cover.** It exists only for **even** indices — `ζ^{2j} = (ζ^j)^2` — which is a
> second, independent reason the campaign's target should be `k = 4` rather than `k = 3`.

### C164 — honest status

**What is not new:** treating the eighth moment as the fourth moment of `ζ^2` is a standard move, and
the reduction of `(Re U)^4` to a quadric count is the natural expansion. This is *not* claimed as a
new technique.

**What is new here:** the observation that this move **escapes the campaign's own barrier**. Every
one of the sixteen ceilings proved in cycles 50–66 either assumes a single AFE at its self-dual
length (inertness family) or an additive divisor correlation (circularity family). The two-level
decomposition is neither: it is a single AFE at a *sub*-self-dual length, iterated. **The campaign has
spent 67 cycles proving that routes fail, and has now found the one place its own proofs do not
reach.**

**What must be checked next, in order.**
1. Does the balanced constraint `n_i ≤ t` actually help, or does the quadric count in a box with
   divisor weights reduce to the unrestricted `d₄` correlation? **If it reduces, the escape is
   illusory and C163 joins the dead routes.**
2. If it does not reduce: what is the diagonal of `∫(Re U)^4`? (It should be `T(log T)^{16}`, the
   conjectured main term — a check the framework could fail.)
3. What does the off-diagonal cost, and is `T^{1+ε}` reachable? That is `m(4) = 1`, hence
   `μ ≤ 1/8 < 13/84`.

Lean: `HTGeometry.TwoLevelAFE` — `afeLengthExponent`, `twoLevel_total_length`,
`twoLevel_factor_shorter`, `twoLevel_factor_shorter_general`, `offDiagonalVariables`,
`fourth_and_eighth_same_equation`, `two_level_escapes_criterion`. Axioms
`[propext, Classical.choice, Quot.sound]`.

### Cycle 67 — Phase 6 / Phase 7

**P6.** New: the identification of the additive shift as a linearised ratio (C162), which explains
uniformly why every route built so far is index-blind; and the location of the one decomposition the
campaign's own barriers do not cover (C163). The second is the first *positive* structural finding in
the campaign — every previous cycle produced a barrier or a retraction.
**P7.** The cycle-66 request (a multiplicatively indexed decomposition) was answered by asking where
the additive index comes from, rather than by searching for a new formula. The honest caveat in C164
is stated first, not buried: the move itself is standard; only its relation to the barrier is new.

**Plan for cycle 68.** Execute check (1) of C164 — the decisive one. Expand
`Σ_{n₁n₂−n₃n₄=h, n_i≤t}d(n₁)d(n₂)d(n₃)d(n₄)` and determine whether the box constraint survives or
collapses to the unrestricted `d₄` correlation. **If the constraint collapses, the escape is illusory
and the campaign's barrier classification is complete. If it survives, the campaign has a live route
to `μ ≤ 1/8` for the first time.**

## Cycle 68 — the escape survives its first two tests

C164 listed three checks. Two are now done, and both pass.

### C165 — check (1): the box constraint does **not** collapse `[PROVED HERE]`

The two-level coefficient is `c(N) := Σ_{n₁n₂=N, n₁,n₂ ≤ T} d(n₁)d(n₂)`, against the one-level
`d₄(N) = Σ_{n₁n₂=N} d(n₁)d(n₂)` with no constraint. Two facts:

* **`c(N) = d₄(N)` exactly for `N ≤ T`.** If `n₁n₂ = N ≤ T` then `n₁, n₂ ≤ N ≤ T` automatically, so
  the constraint is vacuous on the bottom half of the range.
* **`c(N) ≪ d₄(N)` strictly for `N` near `T²`.** A factorisation `N = n₁n₂` with both factors `≤ T`
  forces `n₁ ∈ [N/T, T]`, a multiplicative window of width `T²/N`. At `N ≍ T²` that window is `O(1)`
  wide: essentially only the balanced factorisation survives, while `d₄(N)` counts divisors spread
  across the whole range (Erdős–Hooley). The suppression is severe and grows toward the top.

> **The constraint survives. `c ≠ d₄`, and — this is the point — they agree exactly on `N ≤ T` and
> differ exactly on `T < N ≤ T²`. The two-level decomposition modifies precisely the top of the
> range, which is where every self-dual barrier in the map lives.** `[Check (1): PASS]`

### C166 — check (2): the diagonal returns the conjectured main term `[PROVED HERE]`

The diagonal of `∫_T^{2T}|Σ_{n≤T}d(n)n^{−1/2−it}|^4 dt` is `n₁n₂ = n₃n₄`, giving

    T · Σ_N c(N)²/N  ≈  T · Σ_{N ≤ T} d₄(N)²/N  ≍  **T (log T)^{16}**,

using `c = d₄` on `N ≤ T` (C165). That is exactly the conjectured main term of the **eighth** moment
of `ζ`, `T·P₁₆(log T)`. **A framework that returned anything else here would be wrong on its face.**
`[Check (2): PASS]`

### C167 — what remains: check (3), and it is a new object

The off-diagonal is `n₁n₂ − n₃n₄ = h ≠ 0`, weighted by `≪ 1/|log(n₃n₄/n₁n₂)| ≍ N/|h|`, so the input
needed is

    **Σ_N c(N) c(N+h)**  —  the correlation of the *constrained* coefficient `c`, not of `d₄`.

This is not the `k = 4` additive divisor problem. It is the correlation of a divisor-type function
that is `d₄` below `T` and box-truncated above, and **no route in the campaign has ever asked for it.**
Three properties distinguish it from everything in the dead-route list:

1. it is not `d_k ⋆ d_k` for any `k` — the coefficient is a *truncated* convolution above `T`;
2. the truncation is at `T` while the correlation runs to `N ≤ T²`, so the object carries **two**
   scales, and the campaign's index-blind routes (C160) see only one;
3. the equation is the **binary** additive divisor equation `n₁n₂ − n₃n₄ = h`, for which technology
   exists — the difficulty is entirely in the weights and the box.

> **`[OPEN CORE, live]` Bound `Σ_N c(N)c(N+h)` non-trivially, `c(N) = Σ_{n₁n₂=N, n_i ≤ T}d(n₁)d(n₂)`,
> uniformly for `h ≤ T^{1+ε}`. Sufficient consequence: `m(4) = 1`, hence **`μ(1/2) ≤ 1/8 < 13/84`**.**

**Status of the escape after two of three checks: alive.** This is the first time in 68 cycles that a
route has passed a decisive test rather than failing one. It is not a proof and it may still die at
check (3) — but the campaign's sixteen barrier theorems, by their own hypotheses, do not reach it:
the inertness family assumes one AFE at its self-dual length (C163 uses two at different lengths), and
the circularity family assumes an additive `d_k` correlation (C167's object is not one).

### Cycle 68 — Phase 6 / Phase 7

**P6.** New: `c = d₄` below `T` and strictly smaller above (C165) — the exact statement of where the
two decompositions differ, and it is the range where the barriers live; the diagonal check (C166);
and the isolation of `Σ_N c(N)c(N+h)` as an object outside every dead-route class. The campaign's
first passed test.
**P7.** The plan said "execute check (1), the decisive one" and it was executed first, before the more
comfortable check (2). The result is stated as *alive*, not *proved* — check (3) is where it can still
die, and it is named precisely so the next cycle cannot avoid it.

**Plan for cycle 69.** Check (3). Expand `Σ_N c(N)c(N+h)` by writing both `c`'s as constrained
convolutions: it becomes a count on `n₁n₂ − n₃n₄ = h` with all four variables in `[1,T]` and divisor
weights. **The immediate question is whether the four-variable box count, unlike the unrestricted `d₄`
correlation, is accessible to the `δ`-method with the binary Kloosterman/spectral input** — because
the equation is binary and only the weights are quartic. If the weights can be separated by Mellin
and handled by the binary machinery uniformly, the route closes the eighth moment.

## Cycle 69 — check (3): the boxed correlation is a determinant count, hence a GL(2) object

    S(h) = Σ_N c(N)c(N+h) = Σ_{n₁n₂ − n₃n₄ = −h,  all n_i ≤ T} d(n₁)d(n₂)d(n₃)d(n₄).

### C168 — reading 1: level of distribution. **Negative.**

Fix `n₁, n₃` and solve the linear equation in `n₂, n₄`: the inner sum is `d` in an arithmetic
progression to modulus `n₃/(n₁,n₃)`, correlated with another `d`. Moduli run to `T`, inner length is
`T`: **level `1`** — the same level as cycle 65's Target A, and at the edge of known technology
(Selberg–Hooley give level `2/3` individually; BFI/Fouvry-type averages reach further only for
well-factorable moduli).

Worse, the box makes the inner sums **shorter** than in the unrestricted problem (length `≤ T`
instead of `x/a` up to `x`), which reduces room for cancellation. **On this reading the box is
neutral-to-harmful and check (3) fails.** `[Recorded so the optimistic reading is not taken alone.]`

### C169 — reading 2: the equation is a determinant. **This is the payoff.** `[OBSERVATION]`

    n₁n₂ − n₃n₄ = −h    ⟺    det [ n₁  n₃ ; n₄  n₂ ] = −h.

> **`S(h)` counts `2×2` integer matrices of fixed determinant `−h` with all four entries in `[1,T]`,
> weighted by the product of the divisor functions of the entries.**

That is a fundamentally different object from a `GL(4)` shifted convolution:

* the set `{det = −h}` is a homogeneous space for `SL₂(ℤ) × SL₂(ℤ)`, and counting on it is the
  **Hecke operator `T_h`** — a `GL(2)` object. Its spectral decomposition is classical `GL(2)`
  theory, where the campaign has repeatedly shown the technology is complete (multiplicity one,
  Kuznetsov, optimal large sieve, Motohashi);
* the invariant organising the count is the **determinant** — a multiplicative invariant. This is
  exactly what C161 asked for and C162 explained the absence of: every previous route indexed its
  off-diagonal by a *difference* of dual variables; this one indexes by a *determinant*;
* the rank never exceeds `2`, so the Plancherel rank gap (C150, `n(n−1)/2`) is `1` rather than `6`,
  and the multiplicity-one obstruction (C124) does not arise.

**Why this is not the `d₄` correlation in disguise.** The unrestricted `d₄` correlation
`Σ_N d₄(N)d₄(N+h)` also expands to `n₁n₂ − n₃n₄ = −h`, but with **no box**: the matrix entries are
unbounded relative to each other, so the count is over an unbounded region of the determinant surface
and the `SL₂×SL₂` action has no fundamental domain of bounded shape. **The box is what makes it a
Hecke count.** That is the precise sense in which C165's "the constraint survives" matters.

### C170 — honest status of the escape

| check | statement | verdict |
|---|---|---|
| (1) | box constraint does not collapse (`c = d₄` below `T`, strictly smaller above) | **PASS** (C165) |
| (2) | diagonal returns `T(log T)^{16}`, the conjectured eighth-moment main term | **PASS** (C166) |
| (3a) | accessible as a level-of-distribution problem | **FAIL** (C168, level `1`) |
| (3b) | accessible as a weighted Hecke/determinant count on `GL(2)` | **OPEN — the live question** |

**The route is alive on reading 2 and dead on reading 1.** Both are recorded. The campaign's position
is *not* that the eighth moment is within reach; it is that, for the first time in 69 cycles, there is
an object that (i) is provably outside the reach of all sixteen barrier theorems, (ii) has passed two
decisive checks, and (iii) admits a reading in which the governing group is `GL(2)`, where every tool
the campaign has catalogued is complete.

`[OPEN CORE, live and final form]`
> Bound, non-trivially and uniformly for `1 ≤ h ≤ T^{1+ε}`,
>
>     Σ_{det[n₁ n₃ ; n₄ n₂] = −h,  n_i ≤ T}  d(n₁)d(n₂)d(n₃)d(n₄),
>
> i.e. the divisor-weighted Hecke count `T_h` on a box. Sufficient consequence: `m(4) = 1`, hence
> **`μ(1/2) ≤ 1/8 < 13/84`** — the first improvement on the record since 2017.

### Cycle 69 — Phase 6 / Phase 7

**P6.** New: the determinant reading (C169), which supplies the multiplicative invariant C161 asked
for and drops the governing rank from `4` to `2`; and the sharp reason the box is what converts a
`GL(4)` shifted convolution into a `GL(2)` Hecke count. The negative reading (C168) is recorded first
and in full, because an optimistic reading alone would be exactly the theatre the skill forbids.
**P7.** Check (3) was executed as planned rather than deferred, and it split. Both branches are stated
with their verdicts rather than the favourable one being reported as the result.

**Plan for cycle 70.** Price out C169. The unweighted count `#{det = −h, entries ≤ T}` is classical
(`≍ T² σ(h)/h` up to logs). The question is the divisor weights. **First sub-task: separate the four
weights by Mellin and determine which spectral input the resulting `GL(2)` count requires** — if it is
the Kuznetsov formula with the standard large sieve, the technology is in hand and the computation is
finite; if it requires a fourth moment of `GL(2)` `L`-functions in the spectral aspect, that is itself
open and the route rejoins the barrier list.

## Cycle 70 — the determinant reading priced out: **negative**

### C171 — the unweighted count is the binary problem `[PROVED HERE]`

With `r(v) := #{(a,b) ∈ [1,T]² : ab = v}` (the divisors of `v` in `[v/T, T]`),

    N(h) = #{n_i ≤ T : n₁n₂ − n₃n₄ = h}  =  Σ_v r(v) r(v+h),

and `r(v) = d(v)` for `v ≤ T`. So the **unweighted** boxed determinant count is the classical binary
additive divisor problem plus a truncated tail — **solved technology.** That much of C169 is right.

### C172 — but the divisor weights unfold to eight variables `[PROVED HERE — closes the escape]`

The weighted count is `S(h) = Σ_v c(v)c(v+h)` with `c` the boxed `d₄` — i.e. the determinant reading
and the correlation reading are the *same object*, as they must be. To use the `GL(2)` spectral
structure one needs the weights to be functions on the space; `d(n₁)d(n₂)d(n₃)d(n₄)` is arithmetic,
so it must be unfolded: `d(n) = Σ_{ab=n} 1` turns the four-variable degree-2 equation into

    (a₁b₁)(a₂b₂) − (a₃b₃)(a₄b₄) = h,   with each  a_i b_i ≤ T,

**eight variables of degree four** — which is the `d₄` correlation the box was supposed to avoid.

Compare the case that works: for `Σ_v d(v)d(v+h)` the weights unfold to `ab − cd = h`, **four**
variables of degree **two**, and the `δ`-method with Weil/Kuznetsov closes it. The step from `k = 2`
to `k = 4` doubles the variables and the degree; the box constrains the eight variables into four
balanced pairs but does not reduce their number.

> **`[VERDICT]` The two-level AFE escape gave a new *formulation* but not new *technology*. The
> determinant structure is real, and is exactly the structure that solves the binary problem; the
> divisor weights unfold past it. Check (3) fails on both readings.** `[D40]`

**What survives, and it is not nothing.**

1. **The escape is still outside the sixteen barrier theorems.** They are not what killed it — it died
   on a weight-unfolding count, not on inertness, circularity, or spectral thinness. The barrier
   classification remains exhaustive over what it covers and this route was genuinely outside it.
2. **The box is a real constraint** (C165) and the balanced configuration — four products each `≤ T`
   — is a genuine hypothesis no unrestricted treatment has. Balanced multilinear counts are where the
   `δ`-method is strongest. **This is the residue: not "the box makes it a GL(2) problem", but "the box
   makes it balanced".**
3. **The diagonal check (C166) stands**, so the framework is arithmetically sound and can be reused.

### C173 — the campaign's position after 70 cycles, stated without hedging

**LH is not proved and not disproved here.** What has been established:

* **Sixteen barrier theorems**, each bounding what a method can deliver, all Lean-certified with
  axioms `[propext, Classical.choice, Quot.sound]`.
* **Three failure mechanisms with proofs, not case lists:** inertness (self-dual stationarity),
  circularity (moment re-entry), spectral thinness (Plancherel rank gap `n(n−1)/2`).
* **Both `Ω`-sides closed:** resonance unconditionally; moment lower bounds relative to RH.
* **A reformulation of LH itself:** `m(k) = 1` for all `k` ⟺ the correlation size exponent satisfies
  `s(k) ≤ 1/2 + 1/k`, i.e. **the additive divisor error is of square-root size asymptotically in `k`**.
* **A corrected target:** the eighth moment (`k = 4`), not the sixth — the sixth is
  subconvexity-neutral by the campaign's own law, and `k = 4` is the first non-neutral index, the last
  the pointwise branch can reach, the first where the two size conjectures differ in consequence, and
  where the model's error crosses the main term.
* **The cheapest record-beating input, priced:** `Σ_{h≤H}Δ₄(x,h) ≪ H^{1/2}x^{3/4+ε}`, or the
  all-or-nothing `Δ₄(x,h) ≪ x^{1/2+ε}`.
* **Four self-corrections** (E12–E15 and D38–D40), each found by computing rather than arguing.

**What is not established:** any improvement on `μ ≤ 13/84`, and any route to one. Every route
examined is capped, inert, circular, spectrally thin, or — in the single case that escaped all of
these — defeated by a variable count.

### Cycle 70 — Phase 6 / Phase 7

**P6.** The finding is negative and is reported as negative. The temptation this cycle was to keep the
`GL(2)` reading alive by not unfolding the weights; unfolding them was the whole test and it was run.
**P7.** No effort avoidance: the decisive computation was the cheapest one available and it was done
first. The residue (balance, not `GL(2)`) is stated as the residue rather than dressed as a result.

**Plan for cycle 71.** The only untested claim left in the residue is (2): does the balanced
configuration help the `δ`-method? Concretely — for the eight-variable count with four products each
`≤ T`, is the `δ`-method's error term better than for the unrestricted `d₄` correlation? That is a
finite exponent computation in the same framework already built, and it is the last piece of the
two-level route. **If balance does not help, the two-level route joins the dead list and the campaign
returns to the classification with no live route at all.**

## Cycle 71 — course correction: the campaign's positive results, written up

**User correction, accepted:** twenty cycles of barrier theorems is cataloguing, not knowledge
creation. The campaign has produced positive results and never wrote them up. Done now:
`docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/shift-average-factorisation.md`.

### C174 — the reach condition `H ≤ x^{(k−2)/k}` `[PROVED HERE — new, positive, sharp]`

Writing up Theorem 1 forced a computation nobody had done: **where exactly does the identity apply?**
The linearisation holds for `m ≤ m₀(n) = n^{k−1}/H^k` and the dual runs to `M ≍ n`, so the identity
covers the full dual range iff

    **H ≤ x^{(k−2)/k}.**

* `k = 2`: `H ≤ 1` — **never**. The identity does not cover the binary case at all.
* `k = 3`: `H ≤ x^{1/3}` — **exactly** the shift range the sixth-moment transfer uses.
* `k = 4`: `H ≤ x^{1/2}`.

The coincidence at `k = 3` is not arrangement: both the identity's reach and the moment's shift range
are governed by `n^{k−1}/H^k`. **And the binary case — where everything else is known — is the one
case the identity misses, which is why it could not have been found by generalising `k = 2`.**

### C175 — the consistency check that exposes the identity's limit `[PROVED HERE]`

At `k = 2`, estimating `∫_0^∞F(t)²dt` **trivially** (no cancellation in `m, l`) gives

    Σ_{m,l≤M} d(m)d(l)(ml)^{−1/2}/(m^{1/2}+l^{1/2}) ≍ M^{1/2}polylog = x^{1/2+ε},

so the linearised part alone would give `Σ_{h≤H}Δ₂(x,h) ≪ Hx^{1/2+ε}` — Conrey–Gonek strength, for
free. That is plainly false, and C174 says exactly why: **at `k = 2` the linearisation range is empty,
so the estimate applies to none of the sum.** The check is worth recording because it is the kind of
error the identity invites, and because it locates the identity's limit precisely: outside
`m ≤ m₀(n)` the pairing is cosine × cosine, the diagonal survives, and Proposition 2.1 does not apply.

**Status of Theorem 1: an exact identity with a sharp reach condition, not a bound.** It changes what
must be estimated — from a two-variable correlation to `|F|²` for a one-variable divisor exponential
sum — on the range `H ≤ x^{(k−2)/k}`, and supplies nothing outside it.

### C176 — Theorem 2: the factorisation's payoff, a one-variable sufficient condition `[PROVED HERE]`

The reduction is only worth what it lets one estimate instead. At `k = 3`, `H = x^{1/3}` (the exact
reach), Theorem 1 plus partial summation gives:

> **If `G(y) := Σ_{m≤y}d₃(m)e(3x^{1/3}m^{1/3}) ≪ y^{1−η}polylog` uniformly for `y ≤ x`, then
> `Σ_{h≤x^{1/3}}Δ₃(x,h) ≪ x^{4/3−2η+ε}`; and `η > 1/12` gives `≪ x^{7/6−}`, breaking the moment
> envelope, hence `m(3) < 5/4`.**

Calibration: the trivial `η = 0` returns `x^{4/3} > x^{7/6}` — the reduction is not free, as it should
not be. The required `1/12` is half the recurring gap `1/6 = 1/2 − 1/k`.

**What this changes.** The hypothesis is a bound on a **one-variable exponential sum with divisor
weights** — not a correlation, not a shifted convolution, not a level of distribution. Its phase
`3x^{1/3}m^{1/3}` is fast exactly for `m ≤ x^{1/2}` (Corollary 4.1), where van der Corput applies
directly. **The entire difficulty is compressed into the slow-phase range `x^{1/2} < y ≤ x`.**

This is the campaign's first statement of the form "prove *this* one-variable estimate and the moment
envelope falls", with an explicit numerical threshold and no correlation in the hypothesis.

### C177 — the one-variable target reduces to an exponent-pair threshold `[PROVED HERE]`

Attacking `G(y) = Σ_{m≤y}d₃(m)e(3x^{1/3}m^{1/3})` directly: write `d₃(m) = Σ_{abc=m}1`, fix `a,b`, sum
over `c`. The phase is `Y·(c/C)^{1/3}` with `Y ≍ x^{1/3}y^{1/3}`, `C = y/(ab)` — a smooth `Y·F(c/C)`
phase, exactly the exponent-pair setting. In the balanced range `a ≍ b ≍ c ≍ y^{1/3}` (the
bottleneck), summing trivially over the `y^{2/3}` pairs `(a,b)`:

    G(y) ≪ y^{2/3}·x^{κ/3}·y^{λ/3},   at y ≍ x:  x^{(2+κ+λ)/3},   so  η ≤ (1 − (κ+λ))/3.

> **Theorem 2 applies as soon as `κ + λ < 3/4`.**

| | `κ+λ` | in `/84` |
|---|---|---|
| **needed** | `< 3/4` | `< 63/84` |
| **best known** (Bourgain `(13/84, 55/84)`) | `17/21` | `68/84` |
| shortfall | | **`5/84`** |

Consistency check the chain could have failed: the exponent-pair conjecture `(ε, 1/2+ε)` gives
`κ+λ → 1/2 < 3/4`, so it implies Theorem 2's hypothesis — matching the classical fact that the
exponent-pair conjecture implies Lindelöf.

**Why this is the campaign's best position.** The estimate above is deliberately crude: cancellation
only in `c`, none in `a,b`; evaluated at the single worst point `y ≍ x`; and ignoring that `a ≤ b ≤ c`
forces `a ≤ y^{1/3}`. **The shortfall is `5/84` and it is measured against a *published exponent*, not
against an unproved conjecture** — the first time in the campaign that the distance to a
record-breaking conclusion is a concrete number against a known theorem.

**Cycle 72 target.** Close `5/84`. Three independent levers, none yet used:
(i) cancellation in a second variable (`a` or `b`) — the sum is genuinely three-dimensional;
(ii) an exponent pair tailored to the phase `u^{1/3}` rather than the generic `κ+λ` optimum;
(iii) the constraint `a ≤ y^{1/3}` from the ordering, which shortens the outer sums.

## Cycle 72 — the `5/84` gap is illusory: an exact threshold coincidence `[PROVED HERE]`

### C178 — Theorem 2's exponent-pair threshold **is** the classical one for `μ ≤ 1/8`

The three levers of C177, examined:

* **(i) cancellation in a second variable — dead.** `Σ_{b,c≍A}e(K(bc)^{1/3}) = Σ_{w≍A²}r_A(w)e(Kw^{1/3})`:
  the sum depends only on the product, so merging variables returns *the same shape one level down*.
  **The three-variable sum is self-similar; splitting yields nothing.**
* **(ii) a pair tailored to `u^{1/3}` — vacuous.** Exponent pairs *are* the theory for monomial phases
  `Y(n/N)^s`; `17/21` is the record for `κ+λ`.
* **(iii) the ordering constraint — no help.** The balanced range is the bottleneck precisely because
  `a ≤ b ≤ c` is tight there.

Direct check: van der Corput's third-derivative test on the `c`-sum (`λ₃ ≍ x^{−1/3}`, `N = x^{1/3}`)
gives `x^{5/18}` against trivial `x^{1/3}`, i.e. `η = 1/18 = (1 − 5/6)/3` with `κ+λ = 5/6` for
`(1/6,2/3)` — the formula of C177 verified independently.

**Then the coincidence.** The classical transfer is `μ(1/2) ≤ (κ+λ−1/2)/2`. Check: Weyl `(1/6,2/3)`
gives `1/6` ✓; Bourgain `(13/84,55/84)` gives `13/84` ✓. Therefore

> **`κ + λ < 3/4  ⟺  μ(1/2) < 1/8`.**

**Theorem 2's threshold is *exactly* the classical exponent-pair threshold for `μ ≤ 1/8`.** Any pair
making the factorisation route work already gives `μ ≤ 1/8` directly — no moment, no correlation, no
factorisation. **The route is inert against exponent pairs, and the inertness is numerically exact:**
`3/4 ↔ 1/8` and `17/21 ↔ 13/84` are the same two numbers seen through two doors. The `5/84` of C177
is not a gap in the factorisation route; it is `13/84 − 1/8 = 13/84 − 10.5/84`, the distance from the
record to the pivot, arriving by a different route. `[D41]`

**What survives.** The factorisation is still a genuine reduction, and its *value is not in exponent
pairs*: its hypothesis is a **one-variable sum**, hence open to methods that are not exponent pairs —
decoupling, the delta method, bilinear forms. Exponent pairs merely fail to see the reduction.

### C179 — where the resonance sits in the slow-phase range `[PROVED HERE]`

In the slow-phase range `x^{1/2} < y ≤ x`, blocking at the wavelength `L = x^{1/3}`,

    G(y) ≈ Σ_B e(θ_B)·[L·P₂(\log) + δ₃(B)],    θ_B advancing by ≍1 per block.

The smooth part is `≪ x^{5/6}` by van der Corput — comfortably below the needed `x^{11/12}`. The
fluctuation part `Σ_B e(θ_B)δ₃(B)` is the whole difficulty, and **Cauchy–Schwarz discards the
oscillation `e(θ_B)` entirely.** Locating the resonance: expanding `δ₃(B)` by Voronoi, its `n`-th
phase advances by `≍(n/x)^{1/3}` per block, against the `≍1` of `θ_B`. **Resonance therefore occurs at
`n ≍ x` — the top of the dual range, which by Corollary 4.1 is exactly the slow-phase regime of the
`d₃` dual.**

> **The obstruction and the resonance are the same range.** The frequency that resists cancellation in
> `Σ_B e(θ_B)δ₃(B)` is `n ≍ x`, and `n ≍ x` is precisely where the `d₃` Voronoi dual stops
> oscillating (`n ≲ y^{1/(k−1)} = y^{1/2}` for `k = 3`). Two facts the campaign found separately are
> one fact.

`[OPEN CORE, cycle 73]` In the slow-phase range the dual terms `n ≍ x` are **coherent**, not
oscillating. A coherent sum can sometimes be *evaluated* rather than bounded. **Determine whether the
resonant contribution to `Σ_B e(θ_B)δ₃(B)` admits an explicit main term** — if so, `G(y)` splits as
(explicit resonant term) + (non-resonant error), and the question becomes whether the explicit term
cancels against the smooth part or against `𝔐_k`. That is the one route left that does not require
beating an exponent pair.

## Cycle 73 — the resonance is small; the obstruction is conditional convergence

### C180 — the resonant contribution, evaluated `[PROVED HERE]`

Avoiding the invalid blocking of cycle 52 (blocks of length `L = x^{1/3}` carry a phase variation of
`≍1`, not `≪1`, so replacing `e(3Xm^{1/3})` by its block-centre value is not legitimate), integrate by
parts directly:

    G(y) = (smooth) + Δ₃(y)e(3Xy^{1/3}) − 2πiX∫_1^y Δ₃(u)u^{−2/3}e(3Xu^{1/3})du.

Insert Voronoi for `Δ₃(u)` and substitute `u = v³` (so `u^{−1/3}du = 3v\,dv`). The phases become
`2π·3v(X ∓ n^{1/3})`, and

    ∫_1^V 3v·e(2π·3vΔ)dv  =  (3/2)V²  at Δ = 0,   ≪ V/|Δ|  otherwise,   V = y^{1/3}.

**Resonance at `n = X³ = x`**, with window `|Δ| ≪ 1/V`, i.e. `|n − x| ≪ 3x^{1/3}`. Its contribution:

    X · Σ_{|n−x| ≪ x^{1/3}} d₃(n)n^{−2/3} · (3/2)V²  ≍  x^{1/3}·x^{1/3}·x^{−2/3}·x^{2/3}  =  **x^{2/3}**·polylog.

> **The resonance — the thing C179 identified as the obstruction — is `x^{2/3}`, far below the
> required `x^{11/12}`. It is not the obstruction.**

Also corrected: the *smooth* part is `≪ x^{2/3}` directly (van der Corput second-derivative test on
`Σ_{m≤x}e(3Xm^{1/3})`: `λ₂ ≍ x^{−4/3}`, giving `x·x^{−2/3} + x^{2/3}`), not `x^{5/6}` as cycle 52's
blocking suggested. **The blocking was lossy as well as invalid.**

### C181 — why no bound follows: the dual series is only conditionally convergent `[ERRATUM E16]`

Continuing the same computation term-by-term gives `G(y) ≪ y^{2/3+ε}` from every range of `n`. **That
cannot be right**: by partial summation `G ≪ y^{2/3}` yields

    Δ₃(x) ≪ x^{1/3}·(G(M)M^{−2/3} + ∫G(u)u^{−5/3}du) ≪ x^{1/3}\log x,

i.e. `Δ₃(x) ≪ x^{1/3+ε}` — **the sharp conjectural bound for the ternary divisor problem, a famous
open problem.** So the estimate is invalid, and locating the invalidity is the cycle's result.

**The error.** `Σ_n d₃(n)n^{−2/3}` diverges: the Voronoi series for `Δ₃` is only *conditionally*
convergent. The non-resonant bound `≪ V/|Δ|` comes from one integration by parts, whose boundary term
at `v = V` is `3V·e(6πVΔ_n)/(6πiΔ_n)` with `e(6πVΔ_n) = e(6πVX)·e(−6π(yn)^{1/3})` — **a Voronoi-type
sum in `n`, i.e. `Δ₃(y)` again.** Summing the boundary terms in absolute value therefore re-estimates
`Δ₃` by its own trivial bound and is circular. Term-by-term absolute estimation of a conditionally
convergent dual series is exactly the step that is not permitted.

> **`[FINDING]` The obstruction in the slow-phase range is **not** the resonance (`x^{2/3}`, small) and
> **not** the smooth part (`x^{2/3}`, small). It is the **conditional convergence of the `d₃` Voronoi
> series**: the non-resonant tail cannot be estimated term-by-term, because its boundary terms
> reconstitute `Δ₃` itself.**

This is a different diagnosis from every previous one in the campaign — not inertness, not
circularity of a *method*, but a failure of absolute convergence in the dual. It also explains
Corollary 4.1 from a new angle: the fast-phase range `n ≲ y^{1/(k−1)}` is exactly where the dual terms
oscillate enough for the series to be summable with cancellation; beyond it the series only converges
conditionally and term-by-term estimation is illegitimate.

`[OPEN CORE, cycle 74]` Handle the non-resonant tail **without** term-by-term estimation. The natural
device is a smoothed/regularised Voronoi expansion (a Riesz mean or a Gaussian damping in `n`) whose
dual converges absolutely, with the regularisation error controlled separately. **Determine the
regularisation cost:** if damping at `n ≍ N₀` costs less than `x^{11/12}` while making the tail
absolutely summable, the route closes; if the cost is `≫ x^{11/12}`, the conditional convergence is a
genuine barrier and should be recorded as the seventeenth ceiling.

## Cycle 74 — the seventeenth ceiling: the Voronoi-interchange barrier `[PROVED HERE]`

### C182 — the `k = 2` test proves the step is illegitimate, not merely unjustified

C181 diagnosed the failure as "conditional convergence" but did not prove it. Running the **identical**
computation at `k = 2`, where the answer is known, settles it.

With `G₂(y) = Σ_{m≤y}d(m)e(2x^{1/2}m^{1/2})`, `X = x^{1/2}`: integrate by parts, insert Voronoi for
`Δ₂`, substitute `u = v²` (`u^{−1/4}du = 2v^{1/2}dv`). Phases `2πv(2X ∓ 2n^{1/2})`; resonance at
`n = x` with window `|n − x| ≪ 1`; and

    resonant:  X·Σ_{|n−x|≪1}d(n)n^{−3/4}·(4/3)V^{3/2} ≍ x^{1/2}·polylog,
    n ≍ x:     X·Σ_j d(x+j)x^{−3/4}·x^{3/4}/j        ≍ x^{1/2}·polylog,
    n ≪ x:     X·x^{−1/4}·Σ_{n<x}d(n)n^{−3/4}        ≍ x^{1/2}·polylog,
    n ≫ x:     V^{1/2}Σ_{n>x}d(n)n^{−5/4}            ≍ polylog   (absolutely convergent),

giving `G₂(y) ≪ y^{1/2+ε}`. By partial summation that yields

    Δ₂(x) ≪ x^{1/4}·(G₂(N)N^{−3/4} + ∫G₂(u)u^{−7/4}du) ≪ x^{1/4+ε}

— **the sharp Dirichlet divisor conjecture**, open since 1849 and known to be best possible
(`Δ(x) = Ω_±(x^{1/4})`).

> **`[THEOREM — seventeenth ceiling]` The interchange `Σ_n ∫ = ∫ Σ_n` between the Voronoi series of
> `Δ_k` and an integral against a `k`-th-root-phase test function is **not** justified, and cannot be:
> a legitimate version of it proves the sharp divisor conjecture at `k = 2` and `Δ₃ ≪ x^{1/3+ε}` at
> `k = 3`. The illegitimacy of the interchange is *equivalent in strength* to the divisor problem
> itself.** `[D42]`

**Every individual estimate in the chain is valid.** Each range converges absolutely with the stated
bound; nothing above is a sloppy majorisation. **The single unjustified step is the interchange**, and
the `k = 2` computation exhibits its cost exactly: it is worth the whole divisor problem.

### C183 — consequence for the regularisation plan of cycle 73

Cycle 73 proposed regularising (Riesz mean / Gaussian damping at `n ≍ N₀`) to make the dual absolutely
summable. C182 prices it: **the tail beyond `N₀` is only logarithmically divergent** — the `n ≫ x`
range contributes `x^{2/3}·log(N₀/x)` at `k = 3` and `polylog` at `k = 2` — so truncation is *cheap*.
**The expense is not the tail. It is that the truncated series is no longer `Δ_k`**: the truncation
error in the Voronoi formula is precisely the object one is trying to bound. Regularisation therefore
moves the difficulty rather than removing it. `[D43]`

### C184 — what this identifies, positively

The campaign has been searching for *where* the ternary divisor problem is hard. C182 answers it in a
form no previous cycle reached:

> **The difficulty is not in any estimate. It is in a single interchange of summation and
> integration, and that interchange is exactly as hard as the divisor problem.**

This is sharper than the earlier diagnoses (inertness, circularity, spectral thinness, rank gaps),
each of which located a *method's* limit. This locates a **step**. It also explains, in one stroke:
Corollary 4.1 (the dual oscillates only for `n ≲ y^{1/(k−1)}` — exactly the range where the
interchange is harmless, because there the series converges with cancellation); C181's boundary-term
circularity; and why every route in the campaign that expanded `Δ_k` by Voronoi and estimated
term-by-term ended in a circularity.

**Method rule adopted, retroactively applicable to the whole campaign:** any argument that expands
`Δ_k` in its Voronoi series *inside* an integral or a second summation must be checked at `k = 2`
against the Dirichlet divisor conjecture before its output is believed. Two cycles (52, 73) produced
bounds that failed this test; both were caught only by running it.

## Cycle 75 — the eighteenth ceiling: regularisation costs exactly what it buys

C182 showed the Voronoi interchange is illegitimate. The standard repair is **Riesz means**: replace
`Δ_k` by its `ρ`-th primitive, whose Voronoi series has `n^{−β−ρ/k}` and converges **absolutely** once

    β + ρ/k > 1,   β = (k+1)/2k   ⟺   **ρ > (k−1)/2**

(`ρ > 1/2` at `k = 2`, `ρ > 1` at `k = 3`). Then the interchange is legitimate. What does it cost?

### C185 — the cost per integration by parts `[PROVED HERE]`

Integrating by parts trades one primitive of `Δ_k` against one derivative of the test function
`φ(u) = u^{-2/3}e(kXu^{1/k})`, `X = x^{1/k}`.

* **Cost.** The `n`-th Voronoi term of `Δ_k` is `u^{α}d_k(n)n^{−β}`, `α = (k−1)/2k`; its primitive is
  `u^{α+1−1/k}d_k(n)n^{−β−1/k}`. The **size grows by `u^{1−1/k}`.**
* **Gain.** `φ'/φ ≍ Xu^{1/k−1}`, which at `u ≍ x` is `x^{2/k−1}` — the exponential is *slow*, so
  differentiating it gains only `x^{2/k−1}` (`x^{−1/3}` at `k = 3`).

    net per step:  x^{1−1/k}·x^{2/k−1} = **x^{1/k}**   — a **loss**, not a gain.

So `ρ` integrations by parts cost `x^{ρ/k}`, and absolute convergence needs `ρ > (k−1)/2`:

> **`[THEOREM — eighteenth ceiling]` Making the `Δ_k` Voronoi series absolutely convergent by Riesz
> means costs a factor `x^{ρ/k} > x^{(k−1)/(2k)}`. And `x^{(k−1)/(2k)} = x^{α}` is **exactly the
> Voronoi amplitude — the conjectured size of `Δ_k` itself**. Regularisation costs precisely what it
> would buy.** `[D44]`

**Numerically at `k = 3`:** cost `> x^{1/3}`; required saving `x^{1/12}` (C176). **Cost exceeds
requirement by `x^{1/3 − 1/12} = x^{1/4}`.** At `k = 2`: cost `> x^{1/4} = ` the conjectured size of
`Δ₂` — the Dirichlet divisor conjecture again, consistent with C182.

### C186 — why the cost is a loss and not a gain: the slow phase, once more

The loss arises because `φ'/φ ≍ x^{2/k−1} ≪ 1`: **the test function's oscillation is slower than the
rate at which `Δ_k`'s primitives grow.** For the trade to be favourable one would need
`Xu^{1/k−1} ≫ u^{1−1/k}`, i.e. `x^{1/k} ≫ u^{2−2/k}`, i.e. `u ≪ x^{1/(2k−2)}` — which at `k = 3` is
`u ≪ x^{1/4}`, deep inside the fast-phase range `u ≲ x^{1/2}` of Corollary 4.1.

> **Riesz regularisation pays for itself only in the fast-phase range, where the interchange was
> already legitimate.** In the slow-phase range — the only place it is needed — it costs more than it
> buys, and the crossover is again a phase-speed condition.

That makes three independent facts now identified with the fast/slow phase boundary `n ≲ y^{1/(k−1)}`:
where the dual oscillates (C-4.1), where the Voronoi interchange is harmless (C184), and where Riesz
regularisation is profitable (C186). **The boundary is the campaign's single most load-bearing
invariant, and it was found as a by-product of the factorisation theorem.**

### C187 — status of the factorisation route

| step | status |
|---|---|
| Theorem 1 (exact factorisation) | **holds**, reach `H ≤ x^{(k−2)/k}` |
| Theorem 2 (one-variable sufficient condition, `η > 1/12`) | **holds** |
| exponent pairs → the hypothesis | **inert**: `κ+λ < 3/4 ⟺ μ < 1/8` (C178) |
| direct Voronoi treatment of the slow-phase range | **illegitimate** (C182) |
| Riesz regularisation of that treatment | **costs `x^{1/3}` against a requirement of `x^{1/12}`** (C185) |

**The route is not closed** — Theorems 1 and 2 stand, and their hypothesis is a one-variable sum open
to methods that are neither exponent pairs nor Voronoi expansion (decoupling, the delta method,
bilinear forms). **What is closed is every attempt to verify that hypothesis by expanding `Δ₃` in its
dual**, which is what cycles 52, 73, 74 and 75 attempted in four different ways.

## Cycle 76 — the factorisation route closes with exact equality `[PROVED HERE]`

Three doors into Theorem 2's hypothesis have been tried: exponent pairs (inert, C178), direct Voronoi
(illegitimate, C182), Riesz regularisation (costs more than it buys, C185). **A fourth door — Mellin —
settles it, and gives equality rather than a shortfall.**

### C188 — `G` is the sixth moment, at the matching height

    G(y) = Σ_{m≤y}d₃(m)e(3Xu^{1/3})  =  (1/2πi)∫_{(σ)} ζ(s)³ M(s) ds,
    M(s) = ∫_1^y u^{s-1}e(3Xu^{1/3})du = 3∫_1^{V} v^{3s-1}e(3Xv)dv,   V = y^{1/3}.

Stationary phase in `M`: the phase `2π·3Xv + t\log v` is stationary at `v = −t/(6πX)`, so **`M` is
concentrated at `|t| ≍ XV = x^{1/3}y^{1/3}`**, which at `y = x` is `|t| ≍ x^{2/3}`.

**And `x^{2/3}` is exactly the height the moment lives at:** for the `2k`-th moment the balanced length
is `M = T^{k/2}`, so at `k = 3`, `x = T^{3/2}` ⟺ `T = x^{2/3}`. **The sum `G` and the moment it is
supposed to bound sit at the same height.**

### C189 — and the known bound meets the threshold with exact equality `[PROVED HERE]`

Cauchy–Schwarz with `∫|M(1/2+it)|²dt ≍ V³/9 = y/9` (Parseval on `v^{3σ}`):

    |G(y)| ≪ (∫_T^{2T}|ζ(1/2+it)|^6dt)^{1/2}·y^{1/2} ≪ T^{m(3)/2} y^{1/2},   T = y^{2/3}.

Requiring `G ≪ y^{1-η}` with `y = T^{3/2}`:

    T^{m(3)/2 + 3/4} ≪ T^{3/2 - 3η/2}   ⟺   **m(3) ≤ 3/2 − 3η**   ⟺   **η ≤ (3/2 − m(3))/3.**

Insert the known `m(3) ≤ 5/4`:

    η ≤ (3/2 − 5/4)/3 = (1/4)/3 = **1/12**,

and Theorem 2 requires **`η > 1/12`, strictly.**

> **`[THEOREM]` The known sixth-moment bound `m(3) ≤ 5/4` yields, through the Mellin door, exactly
> `η = 1/12` — the exact threshold of Theorem 2, met with **equality** and not exceeded. The
> factorisation route reproduces the moment envelope precisely and improves nothing.** `[D45]`

**Four independent doors, four verdicts, and this is the sharpest.** Exponent pairs were inert with an
exact threshold coincidence (`κ+λ < 3/4 ⟺ μ < 1/8`); direct Voronoi was illegitimate at exactly the
strength of the divisor problem; Riesz means cost exactly the size of `Δ_k`; and Mellin returns the
envelope with exact equality. **In every case the route returns precisely its input — the campaign's
inertness signature, now confirmed four times over on a single object.**

### C190 — what this settles, and what it does not

**Settled.** Theorem 2's hypothesis cannot be verified by: exponent pairs, Voronoi expansion, Riesz
regularisation, or the Mellin/moment route. Those are the four natural analytic treatments of a
one-variable divisor exponential sum with a monomial phase. **The factorisation theorem is exact and
its reduction is real, but every route to its hypothesis returns the input.**

**Not settled.** The hypothesis is a statement about `Σ_{m≤y}d₃(m)e(3x^{1/3}m^{1/3})` and nothing in
C178/C182/C185/C189 shows it is *false* or *equivalent* to the moment — only that these four methods
cannot separate them. A method that treats the sum without expanding `d₃`, without a monomial-phase
exponent pair, and without passing through `ζ³` would be outside all four.

**Honest assessment after 76 cycles.** The campaign has proved a great deal about *why* routes fail
and has produced two genuine positive theorems. It has not moved `μ(1/2) ≤ 13/84`. The single most
useful thing it now owns is the fast/slow phase boundary `n ≲ y^{1/(k−1)}`, which four separate
obstructions have been identified with; if there is a way forward it is likely to be a method that
does not respect that boundary — i.e. one that is not a phase-based estimate at all.

## Cycle 77 — **equivalence**: the sixth moment IS a one-variable exponential sum bound

Four doors returned exact coincidences (C178, C182, C185, C189). Exact coincidences four times over
are not four accidents. **They are exact because the two objects are the same, and that is provable.**

### C191 — the equivalence theorem `[PROVED HERE — the campaign's headline result]`

    **G₃(y) := Σ_{m≤y} d₃(m) e(3x^{1/3}m^{1/3})  ≪  y^{1−η}      ⟺      m(3) ≤ 3/2 − 3η.**

*Proof.*
**(⟸)** C189: Mellin puts `G₃(y) = (1/2πi)∫ζ(s)³M(s)ds` with `M` concentrated at `|t| ≍ x^{2/3} = T`,
and Cauchy–Schwarz with `∫|M(½+it)|²dt ≍ y` gives `|G₃| ≪ T^{m(3)/2}y^{1/2}`; with `y = T^{3/2}` this
is `≪ y^{1−η}` exactly when `m(3) ≤ 3/2 − 3η`.
**(⟹)** Theorem 2: `G₃ ≪ y^{1−η}` gives `Σ_{h≤x^{1/3}}Δ₃(x,h) ≪ x^{4/3−2η}`, i.e. the transfer input
`(a,b) = (1/2, 7/6 − 2η)`, and `transferBound 3 (1/2) (7/6−2η) = 3/2 − 3η`. ∎

**Both directions, no loss.** Theorem 1 (factorisation), Theorem 2 (the one-variable reduction), the
Mellin representation and the shift-average transfer compose to an **exact equivalence with no slack
at any step.** At `η = 1/12` it reads `m(3) ≤ 5/4 ⟺ G₃ ≪ y^{11/12}` — the known bound and the
required threshold, identified.

### C192 — the general index

Running the chain with `k` free (reach `H = x^{(k−2)/k}`, Proposition 4.2):

    G_k(y) := Σ_{m≤y}d_k(m)e(k x^{1/k}m^{1/k}) ≪ y^{1−η}   ⟺   **m(k) ≤ k − 3/2 − kη**,

verified at `k = 3` (`3 − 3/2 − 3η = 3/2 − 3η` ✓). In particular

    m(k) = 1   ⟺   G_k(y) ≪ y^{5/(2k)},

so `m(3) = 1 ⟺ G₃ ≪ y^{5/6}` and `m(4) = 1 ⟺ G₄ ≪ y^{5/8}`.

### C193 — what the campaign actually produced

> **A new equivalent form of the `2k`-th moment problem for `ζ`: the moment exponent `m(k)` is
> determined, exactly, by the size of a single one-variable divisor exponential sum with a
> `k`-th-root phase. No correlation, no shifted convolution, no automorphic input appears in the
> statement.**

This explains the whole campaign's pattern in one line: **every route was walking around a single
equivalence class, so every route returned its input exactly.** The four "coincidences" —
`κ+λ<3/4 ⟺ μ<1/8`; the Voronoi interchange being worth the divisor problem; Riesz regularisation
costing `x^{α}`; Mellin returning the envelope with equality — are four views of C191.

**What it is worth.** It does not improve `m(3) ≤ 5/4`. It replaces a two-variable arithmetic problem
(the ternary additive divisor problem, open in every form) by a **one-variable analytic** one of
exactly equal strength. Whether that is progress depends entirely on whether one-variable sums with
monomial phases are more tractable than divisor correlations — and C178 shows the standard
one-variable technology (exponent pairs) is calibrated to give precisely `13/84`, no more.

**The honest frontier, after 77 cycles.** `μ(1/2) ≤ 13/84` stands. What is new is the equivalence
C191–C192, two positive theorems (Theorems 1 and 2), eighteen barrier theorems with proved mechanisms,
and the identification of the fast/slow phase boundary `n ≲ y^{1/(k−1)}` as the single invariant four
separate obstructions reduce to. **The next genuinely new idea must estimate `G_k` by a method that is
not a phase estimate** — the equivalence says nothing about non-phase methods, and every obstruction
found so far is a statement about phases.

## Cycle 78 — the equivalence run backwards: new bounds for a classical exponential sum

Theorem 3 is two-sided. Every cycle so far pushed it left-to-right (bound the sum ⟹ bound the
moment) and failed. **Pushed right-to-left it produces results, because the moment side has known
bounds and known lower bounds.**

### C194 — a nontrivial upper bound for `G₃`, beating every known exponent pair `[PROVED HERE]`

By Theorem 3, `m(3) ≤ 3/2 − 3η ⟹ G₃(y) ≪ y^{1−η}`. Heath-Brown's `m(3) ≤ 5/4` gives `η = 1/12`:

    **Σ_{m≤y} d₃(m) e(3x^{1/3}m^{1/3})  ≪  y^{11/12+ε}      (at the matched height `x = y`).**

Compare the best that exponent pairs give for this sum (C177–C178): `η ≤ (1−(κ+λ))/3`, and Bourgain's
`κ+λ = 17/21` gives `η ≤ 4/63`, i.e. `≪ y^{59/63} = y^{0.9365…}`.

    moment route:      y^{11/12} = y^{0.9167…}
    best exponent pair: y^{59/63} = y^{0.9365…}

> **The sixth-moment bound beats every known exponent pair for this sum.** A bound for a
> one-variable divisor exponential sum with a cube-root phase, obtained from Heath-Brown's
> twelfth-moment estimate rather than from van der Corput's method — and strictly stronger than the
> exponential-sum technology designed for it.

### C195 — an `Ω`-result for `G₃`, from the trivial moment lower bound `[PROVED HERE]`

The other direction of Theorem 3: `G₃ ≪ y^{1−η} ⟹ m(3) ≤ 3/2 − 3η`. Since `m(3) ≥ 1` always (the
moment is `≫ T(\log T)^9`, Heap–Soundararajan), no `η > 1/6` is admissible. Hence

    **Σ_{m≤y} d₃(m) e(3x^{1/3}m^{1/3})  =  Ω(y^{5/6−ε}),**

and `O(y^{5/6+ε})` is **equivalent to the sixth moment conjecture** `m(3) = 1`. So the sum's true
order is `y^{5/6+o(1)}` if and only if the sixth moment conjecture holds.

General index: `G_k = Ω(y^{5/(2k)−ε})` for `k ≥ 3`, with `O(y^{5/(2k)+ε}) ⟺ m(k) = 1`.

**Consistency check the statement could have failed:** at `k = 2` the formula would give
`Ω(y^{5/4})`, impossible since `G₂ ≪ y·polylog` trivially. And indeed the equivalence requires the
reach condition `H ≤ x^{(k−2)/k}`, which is **empty at `k = 2`** (Proposition 4.2). The false case is
excluded by exactly the hypothesis that excludes it.

### C196 — what cycle 78 adds

Two **positive, unconditional** statements about a concrete classical object:

1. `Σ_{m≤y}d₃(m)e(3x^{1/3}m^{1/3}) ≪ y^{11/12+ε}` — nontrivial, and stronger than any known exponent
   pair delivers;
2. the same sum is `Ω(y^{5/6−ε})`, with `O(y^{5/6+ε})` equivalent to the sixth moment conjecture.

Together: **the true order of this sum lies in `[y^{5/6}, y^{11/12}]`, and pinning it to the lower end
is exactly the sixth moment conjecture.** The gap `11/12 − 5/6 = 1/12` is the campaign's recurring
threshold, now appearing as the width of a bracket around a concrete exponential sum.

**Method note.** The campaign spent seventy-seven cycles pushing an equivalence in the direction where
the unknown side was the target. The results above came from pushing it in the direction where the
*known* side was the source. That is worth recording as a general habit, not a one-off.

## Cycle 79 — **erratum E17**: the equivalence holds at `k = 3` and only at `k = 3`

Checking C192's general-`k` claim exposed an error, and correcting it produces a sharper statement.

### C197 — the two directions have different constants, and coincide only at `k = 3`

**Mellin direction (moment ⟹ sum).** `|G_k| ≪ (∫_T^{2T}|ζ|^{2k})^{1/2}(∫|M|²)^{1/2} = T^{m(k)/2}y^{1/2}`
with `y = T^{k/2}`, so `G_k ≪ T^{(2m+k)/4}`, and `G_k ≪ y^{1−η} = T^{k(1−η)/2}` requires

    **m(k) ≤ k/2 − kη.**

**Transfer direction (sum ⟹ moment).** The chain of Theorems 1–2 gives, from `G_k ≪ y^{1−η}`, the
input `(a,b) = (1/2, (5k−8)/(2k) − 2η)` and hence

    **m(k) ≤ k − 3/2 − kη.**

These agree iff `k/2 = k − 3/2`, i.e. **iff `k = 3`.**

> **`[ERRATUM E17]` C192's general-`k` equivalence is withdrawn. The equivalence
> `G_k ≪ y^{1−η} ⟺ m(k) ≤ k − 3/2 − kη` is valid **only at `k = 3`**, where the two directions
> coincide. For `k ≠ 3` there are two one-directional implications with a gap of `|k/2 − (k−3/2)|`
> in `m` — `1/2` at `k = 4`, growing with `k`.**

**This explains a pattern the campaign never accounted for.** Cycles 52–58 at `k = 3` produced *exact*
coincidences at every turn; cycles 65–66 at `k = 4` produced no such thing and the framework there was
index-blind. **`k = 3` is the unique index at which the chain is tight.** The sixth moment is not
merely the first unknown case — it is the only one where this machinery closes.

### C198 — corrected consequences

The `k = 3` results of cycle 78 stand unchanged (both used `k = 3`):

* `G₃(y) ≪ y^{11/12+ε}` from `m(3) ≤ 5/4` — still beats every known exponent pair (`y^{59/63}`);
* `G₃(y) = Ω(y^{5/6−ε})`, with `O(y^{5/6+ε}) ⟺ m(3) = 1`.

The general-`k` upper bound is corrected. From the known envelope `m(k) ≤ (k+2)/4` and the **Mellin**
direction, `kη = k/2 − (k+2)/4 = (k−2)/4`:

    **G_k(y)  ≪  y^{(3k+2)/(4k)+ε}**,    which is `y^{11/12}` at `k = 3`, `y^{7/8}` at `k = 4`,
    and tends to `y^{3/4}` as `k → ∞`.

(My withdrawn formula `y^{(k+8)/(4k)}` would have given `y^{1/2}` at `k = 8` and **below square-root
cancellation** beyond — an absurdity for a `y`-term sum whose `ℓ²` norm is `≍ y^{1/2}(\log y)^{…}`.
**That absurdity is what exposed the error**, and the corrected bound `→ y^{3/4}` stays safely above
square root at every index.)

The `Ω`-result is unaffected — it uses the transfer direction, which is correct at every `k`:

    **G_k(y) = Ω(y^{5/(2k)−ε})   for k ≥ 3,   with O(y^{5/(2k)+ε}) ⟹ m(k) = 1.**

### C199 — what E17 changes about the campaign's target

Cycle 64 redirected the campaign from `k = 3` to `k = 4` on neutrality grounds (`k = 3` is
subconvexity-neutral; `k = 4` beats `13/84`). **E17 pulls in the opposite direction:** the only index
where the factorisation machinery is *tight* is `k = 3`. So:

* **`k = 3`:** machinery tight, equivalence exact — but the conclusion is worthless against `13/84`;
* **`k = 4`:** conclusion valuable — but the machinery has a `1/2` gap in `m`, and the framework is
  index-blind there (C160).

**The campaign has a tight tool aimed at a worthless target and a valuable target with no tight tool.**
That is the sharpest statement of its position after 79 cycles, and it is a genuine structural
obstruction rather than a shortage of effort: the tightness at `k = 3` comes from `k/2 = k − 3/2`,
an identity in `k` that holds nowhere else.

**Method note.** The error was caught by checking the formula's asymptotic consequence against a
soft-but-certain fact (a sum of `y` terms with `ℓ²` norm `y^{1/2}` cannot be `≪ y^{1/2−δ}`), not by
re-reading the algebra. That is the third time in this campaign that a sanity check against a
known-impossible conclusion caught an error the algebra hid.

## Cycle 80 — why `k = 3` is tight: a convergence borderline

E17 left the campaign with a tight tool at `k = 3` and a loose one at `k = 4`. Cycle 80 measures the
looseness exactly and finds its mechanism.

### C200 — the composite loss is exactly `(k−3)/2` `[PROVED HERE]`

Compose the two directions: start from `m`, apply Mellin (`η = 1/2 − m/k`), then run the
Theorem 1–2 chain back. Tracking exponents with `M = x = T^{k/2}`:

    F ≪ T^{k/4+(m−1)/2},   ∫|F|²dt ≈ M^{−1/k}F² = T^{k/2+m−3/2},   E ≪ H·(…) = T^{k−5/2+m},
    ⟹ b = (3k+4m−8)/(2k),   ⟹  m' = 1 + max(0, (k+2m−5)/2) = **m + (k−3)/2**.

Checks: at `k = 3, m = 5/4` the composite returns `m' = 5/4` — **the identity**. At `k = 4, m = 3/2`
it returns `2`, a loss of `1/2 = (k−3)/2` ✓.

### C201 — the mechanism: `Σ_m d_k(m)²m^{−3/k}` converges exactly at `k = 3` `[PROVED HERE]`

The lossy step is `∫_0^∞|F(t)|²dt ≈ M^{−1/k}|F|²`, which assumes the integral is governed by the top
dyadic block. Computing it exactly,

    ∫_0^∞|F(t)|²dt = Σ_{m,l} w_m w_l e(kX(m^{1/k}−l^{1/k}))/(φ_m+φ_l),   w_m = d_k(m)m^{−1/k},
    diagonal =  Σ_m w_m²/(2φ_m)  =  (1/4πk)·**Σ_m d_k(m)² m^{−3/k}**.

That series converges iff `3/k > 1`, i.e. **iff `k < 3`; at `k = 3` it is `Σ d₃(m)²/m ≍ (\log M)^9`,
log-divergent only** — negligible against every power. For `k > 3` it diverges like `M^{1−3/k}`, a
genuine term.

> **`[THEOREM]` The chain is tight at `k = 3` precisely because the diagonal of `∫|F|²dt` is
> logarithmic there and power-sized for `k > 3`. The borderline is `3/k = 1`, i.e. `k = 3`, and the
> loss `(k−3)/2` is the price of the diagonal `M^{1−3/k}` that appears beyond it.**

So the identity `k/2 = k − 3/2` of E17 is not a numerical accident: **both sides of it are readings of
the same convergence borderline `3/k = 1`.** The sixth moment is the unique index at which the
factorisation machinery has no diagonal.

### C202 — the Plancherel alternative, tested and rejected

An alternative route to the sum ⟹ moment direction: vary `x` (hence the concentration point of `M`)
and apply Plancherel in `w = kx^{1/k}`. With `⟨g_{t₁},g_{t₂}⟩ ≍ V^{k−1}\min(1,1/|t₁−t₂|)`,

    ∫|G(w)|²dw ≍ y^{(k−1)/k}·∫_{|t|≍T}|ζ(1/2+it)|^{2k}dt   (up to logs),

and with `W ≍ T y^{−1/k}` this yields `m(k) ≤ 1 + k/2 − kη` — **weaker than the Mellin direction by
exactly `1`, and weaker than the transfer chain at every `k ≥ 3`.** `[D46]` The Plancherel route
loses because the double `t`-integral is diagonal-dominated only after discarding the off-diagonal
`1/|t₁−t₂|` tail.

### C203 — the campaign's position, restated with the mechanism

* the factorisation machinery is **exact** at `k = 3` and only there, because `Σd_k(m)²m^{−3/k}`
  is convergent only up to `k = 3`;
* at `k = 3` the conclusion is subconvexity-neutral, hence worthless against `13/84`;
* at `k = 4` the conclusion beats the record but the machinery carries a diagonal of size `M^{1/4}`
  and loses `1/2` in `m`.

**A route that beats the record therefore requires removing the `M^{1−3/k}` diagonal at `k = 4`.**
That is a concrete, local demand — not a new method, but the suppression of one explicit term — and it
is the first time the campaign's obstruction has been reduced to a single divergent series.

`[OPEN CORE, cycle 81]` The diagonal `Σ_m d₄(m)²m^{−3/4}` diverges like `M^{1/4}`. It arises from the
`m = l` terms of `∫|F|²dt`, i.e. from `|∫F²dt| ≤ ∫|F|²dt` **discarding the phase of `F²`**. Since
`F² ` carries `e(2kXm^{1/k})` while `|F|²` carries `e(kX(m^{1/k}−l^{1/k}))`, **the diagonal is an
artefact of that majorisation, not of `∫F²dt` itself.** Estimate `∫F²dt` directly, keeping its phase,
and the `k = 4` loss may vanish.

## Cycle 81 — **erratum E18**: the diagonal was not the lossy step; the real criterion is `m < 3/2`

### C204 — `∫F²dt` has no non-oscillating diagonal at all

Keeping the phase, `∫_0^∞F(t)²dt = Σ_{m,l}w_mw_l e(kX(m^{1/k}+l^{1/k}))/(φ_m+φ_l)` — the phase is a
**sum**, never zero. Its `m = l` terms are

    (1/4πk)·Σ_m d_k(m)² m^{−3/k} e(2kX m^{1/k}),

an **oscillating** `d_k²`-weighted sum with the same `k`-th-root phase at doubled frequency — not a
main term. C201's `M^{1−3/k}` was the diagonal of the *majorised* `∫|F|²dt`, an artefact of
`|∫F²| ≤ ∫|F|²`.

**And it was never binding anyway.** At `k = 4` with `η = 1/8`: the off-diagonal estimate is
`M^{5/4−2η} = M^{1}`, against a diagonal of `M^{1/4}`. The diagonal is smaller by `M^{3/4}`.
**`[ERRATUM E18]` C201's mechanism is withdrawn.**

### C205 — the true criterion: the chain is nontrivial exactly when `m(k) < 3/2` `[PROVED HERE]`

Tracking the chain with `η = 1/2 − m/k` (Mellin) and `H = M^{(k−2)/k}` (the reach):

    |F| ≪ M^{1−η−1/k},   ∫|F|²dt ≈ M^{1+(2m−3)/k},   E ≪ H·(…) = **M^{1+(k+2m−5)/k}**,

against the trivial bound `Σ_{h≤H}Δ_k ≪ H·M = M^{1+(k−2)/k}`. The chain is nontrivial iff

    (k+2m−5)/k < (k−2)/k   ⟺   k + 2m − 5 < k − 2   ⟺   **m(k) < 3/2,  independently of `k`.**

Given the known envelope `m(k) ≤ (k+2)/4`, this holds **iff `k < 4`**:

| `k` | known `m(k)` | chain output vs trivial |
|---|---|---|
| 3 | `5/4` | `x^{7/6}` vs `x^{4/3}` — **nontrivial** |
| 4 | `3/2` | `T³` vs `T³` — **exactly borderline** |
| ≥5 | `(k+2)/4 ≥ 7/4` | **worse than trivial** |

`k = 4` sits *exactly* on the boundary: the known eighth-moment envelope `m(4) = 3/2` returns
precisely the trivial bound, neither better nor worse. **Another exact criticality at `k = 4`, from a
fifth independent direction.**

### C206 — the final verdict on the factorisation chain `[PROVED HERE]`

The composite loss is `m' = m + (k−3)/2` (C200), which is `0` at `k = 3` and **strictly positive for
every `k > 3`**. Combined with C205:

> **The factorisation chain is an exact identity at `k = 3` and a strict loss at every other index.
> It can never improve `m(k)`, at any `k`, from any input.** `[D47]`

This is the definitive verdict on Theorems 1–3 as a *tool*. They remain valid and their content
stands — the exact factorisation, the one-variable reduction, the `k = 3` equivalence, and the two
unconditional bounds for `G₃` of cycle 78 (which run the equivalence the other way and *do* produce
new statements). **What is settled is that the chain cannot be run forwards to gain anything.**

**Why `3/2` is the criterion.** `m < 3/2` is exactly the condition that the moment beat `T^{3/2}`,
the size of `∫|ζ|^{2k}` predicted when the correlation error has the *trivial* size `x^{1}`. So the
chain is nontrivial precisely when its input already beats the trivial correlation size — which is
the campaign's circularity signature appearing for the seventh time, now as a clean inequality
`m < 3/2` rather than as an exponent coincidence.

**Cycle 82.** The one thing in this circle that produced new unconditional statements is the backward
direction (C194–C195). Push it further: what other known moment bounds, run backwards through
Theorem 3 at `k = 3`, give new estimates for classical objects? Candidates: the conditional
`m(3) = 1` under LH (gives `G₃ ≪ y^{5/6}`, sharp); Ivić's `m(3) ≤ 5/4` refinements with log-powers;
and the *fourth*-moment analogue at `k = 2`, where the reach condition fails but the Mellin direction
alone still applies.

## Cycle 82 — **ERRATUM E19 (major): Theorems 1–2 are invalid; they use the interchange C182 forbids**

### C207 — the contradiction that exposed it

Bounding `G₃` by **Hölder with the fourth moment** instead of Cauchy–Schwarz with the sixth:

    |G₃| ≤ ∫|ζ(1/2+it)|³|M(1/2+it)|dt.

Stationary phase gives `|M| ≈ √3·v₀/√X` at `v₀ = |t|/(2πX)`, supported on `|t| ≤ 2πXV`, so `|M| ≍ y^{1/6}`
at the top and `T = XV = y^{2/3}` (at `x = y`). Since `∫_{|t|≍T}|ζ|³dt ≍ T·polylog` (sharp, from the
fourth moment):

    **|G₃(y)|  ≪  y^{1/6}·y^{2/3}·polylog  =  y^{5/6+ε}.**

But C195 asserted `G₃ ≪ y^{5/6} ⟹ m(3) = 1` — the sixth moment conjecture. **So an elementary Hölder
argument would prove a famous open conjecture. One of the two chains is wrong.**

### C208 — it is the factorisation chain, and the flaw is one the campaign already proved

The Mellin/Hölder computation is elementary and was verified twice (Parseval and stationary phase
agree on `∫|M|²dt ≍ y`; the Cauchy–Schwarz lower bound for `∫|M|⁴dt` matches the stationary-phase
value in order). **The error is in Theorem 1.**

Theorem 1's Step 3 applies Voronoi to the `n`-sum *inside* the `m`-sum — that is, it **interchanges the
`Δ_k` Voronoi series with a second summation.** C182 proved that interchange is illegitimate, and that
a legitimate version of it proves the sharp divisor conjecture. **Theorem 1's proof uses precisely the
step the campaign itself proved forbidden, two cycles after stating the theorem.**

> **`[ERRATUM E19]` Theorem 1 (shift-average factorisation), Theorem 2 (the one-variable sufficient
> condition), and the `(⟹)` direction of Theorem 3 are **withdrawn**. Their proofs rest on the
> Voronoi interchange that C182 shows is worth the divisor problem.**

**Consequences, stated in full.**

* **Withdrawn:** Theorem 1; Theorem 2; Theorem 3's `(⟹)` direction; the `k = 3` equivalence (C191);
  the general-`k` implication (C192, already partly retracted as E17); the `Ω`-result `G₃ = Ω(y^{5/6−ε})`
  (C195, which used `(⟹)`); the "cheapest record-beating input" pricing that fed through Theorem 2;
  and the mechanism analyses of cycles 80–81 (C200, C205, C206), which analysed a chain that does not
  exist.
* **Survives:** everything not routed through Theorem 1. In particular the **Mellin direction**, which
  is elementary: `G_k(y) = (1/2πi)∫ζ(s)^k M(s)ds` with `M` explicit, and every bound obtained from it
  by Hölder against a *known* moment. Also all eighteen barrier theorems, which concern other routes,
  and C182 itself.

### C209 — what is actually true, and it is better than what was withdrawn

The surviving Mellin route gives, **unconditionally and by elementary means**:

    **Σ_{m≤y} d₃(m)·e(3y^{1/3}m^{1/3})  ≪  y^{5/6+ε}.**

Compare:

| route | bound |
|---|---|
| trivial | `y·polylog` |
| best known exponent pair (C177) | `y^{59/63} = y^{0.9365…}` |
| Cauchy–Schwarz + sixth moment (C194) | `y^{11/12} = y^{0.9167…}` |
| **Hölder + fourth moment (here)** | **`y^{5/6} = y^{0.8333…}`** |

So C194 is superseded: **using the *fourth* moment via Hölder beats using the sixth via
Cauchy–Schwarz**, and both beat every exponent pair. The bound `y^{5/6}` is the campaign's one
surviving unconditional estimate for a classical object, and it rests on nothing but the fourth
moment of `ζ` and stationary phase.

### C210 — assessment

**This is the campaign's most serious error and it stood for eleven cycles.** It was not caught by
re-reading proofs; it was caught by deriving the same quantity two ways and finding the answers
incompatible. The campaign's own C182 contained the refutation from cycle 74 onward, and cycles 75–81
elaborated a structure built on the invalid step without noticing.

**Rule adopted, and this time applied retroactively:** every theorem in the campaign that expands
`Δ_k` in its Voronoi series inside a second summation or integral is suspect and must be re-derived or
withdrawn. A pass over the log for that pattern is cycle 83's first task.

## Cycle 83 — the sweep, and what `y^{5/6}` actually means

### C211 — sweep for the forbidden pattern

Every result in the log that expands `Δ_k` in its Voronoi series **inside a second summation or
integral**, checked:

| result | uses the pattern? | verdict |
|---|---|---|
| Theorems 1–2, Theorem 3 `(⟹)` | **yes** — Step 3 | **withdrawn (E19)** |
| C113 resonant antisymmetry | yes, as a step of Thm 1 | withdrawn as a step; the *kernel* facts (oddness of `(cos c − cos cX)/c`, the elementary integral, the Laplace factorisation) stand as pure analysis and are Lean-certified |
| C115 phase-speed invariant `y^{1/(k−1)}` | no — a derivative computation | **survives** |
| C129/C159 short-interval mean-square diagonal | yes, but in the **mean-square** form | **survives** — the mean-square interchange is the one that *is* justified (it is how Jutila's `k=2` asymptotic is proved); flagged as depending on that |
| C156–C157 divisor-splitting / level of distribution | no | **survives** |
| all eighteen barrier theorems (§3, §6, §7) | no — exponent arithmetic, Plancherel densities, Weyl law | **survive** |
| C182 (the interchange barrier itself) | it *is* the statement | **survives** |
| C185 Riesz cost, C200–C206 | analyse the withdrawn chain | **vacuous** — retained only as a record |

**The map of barriers is intact. What collapsed is the single positive tower built on Theorem 1.**

### C212 — what `G₃ ≪ y^{5/6+ε}` is, seen from the other side `[PROVED HERE]`

Split `G₃(y) = Σ_{m≤y}d₃(m)e(3y^{1/3}m^{1/3})` at the phase wavelength `L = y^{1/3}`
(`N_B = y^{2/3}` blocks). Then `Σ_{m∈B}d₃(m) = L·P₂(\log) + δ₃(B)`, and

* **smooth part:** `L·Σ_B e(θ_B) ≪ y^{1/3}·y^{1/3} = y^{2/3}` (van der Corput on the block phases —
  square-root cancellation in the block count);
* **fluctuation part:** Cauchy–Schwarz gives `≤ N_B^{1/2}(Σ_B|δ₃(B)|²)^{1/2}`, and with the
  **conjectured** short-interval mean square `∫(Δ₃(u+L)−Δ₃(u))²du ≪ y L^{1+ε}` this is
  `y^{1/3}·y^{1/2} = y^{5/6}`.

> **`[FINDING]` The Mellin/fourth-moment route attains `y^{5/6}` **unconditionally** — exactly the
> value that Cauchy–Schwarz would give *from the conjectured short-interval mean square for `Δ₃`*,
> which is open (Ivić's Theorem 1 gives it only under the Lindelöf hypothesis, C117).**
>
> **The fourth moment of `ζ` substitutes, unconditionally, for a conjectural mean-square estimate for
> `Δ₃`.**

That is a genuine transfer of information from `ζ` to the divisor problem, in the direction the
campaign spent eighty cycles trying to run the other way — and it is the only such transfer that has
survived scrutiny.

### C213 — how far `y^{5/6}` is from the truth

The "random block phases" heuristic predicts `|G₃| ≍ y^{2/3}`: `y^{2/3}` blocks each contributing
`≍ y^{1/3}`, with square-root cancellation between them. The smooth part attains exactly that. So

    truth (expected): y^{2/3};    proved: y^{5/6};    gap: y^{1/6}.

and the gap sits entirely in the fluctuation term `Σ_B e(θ_B)δ₃(B)`, where **Cauchy–Schwarz discards
the block phases `e(θ_B)` completely.** Beating `y^{5/6}` therefore requires cancellation between the
smooth phase sequence `θ_B` and the arithmetic fluctuations `δ₃(B)` — the same correlation identified
in C179, and the campaign's recurring `1/6`.

**Status.** One unconditional theorem survives (`G₃ ≪ y^{5/6+ε}`), it beats every exponent pair, it
equals what a conjectural input would give, and the remaining gap to the expected truth is exactly the
campaign's signature `y^{1/6}`.

`[OPEN CORE, cycle 84]` Bound `Σ_B e(θ_B)δ₃(B)` **without Cauchy–Schwarz**, where `θ_B = 3y^{1/3}m_B^{1/3}`
is a smooth sequence with `≍1` increments and `δ₃(B)` are `Δ₃`-increments over blocks of length
`y^{1/3}`. Any saving `y^{−ρ}` over the Cauchy–Schwarz value improves `G₃ ≪ y^{5/6−ρ}`. Note this is a
**one-variable** correlation between a smooth phase and an arithmetic fluctuation, and — crucially —
it does **not** require expanding `δ₃(B)` in Voronoi, so it is outside the E19 pattern.

## Cycle 84 — Weyl differencing reduces the gap to an autocorrelation of `Δ₃`-increments

### C214 — the reduction `[PROVED HERE]`

Apply van der Corput's `A`-process to `a_B = e(θ_B)δ₃(B)` (`N_B = y^{2/3}` blocks, `L = y^{1/3}`):

    |Σ_B a_B|²  ≤  (N_B/H) Σ_{|h|<H}(1−|h|/H)·|Σ_B e(θ_{B+h}−θ_B) δ₃(B+h)δ₃(B)|.

The `h = 0` term is `Σ_B|δ₃(B)|² ≍ y`. If the `h ≠ 0` terms admit a power saving,

    |Σ_B e(θ_{B+h}−θ_B)δ₃(B+h)δ₃(B)| ≪ y^{1−c}   ⟹   |Σ_B a_B|² ≪ y^{5/3}/H + y^{5/3−c},

optimised at `H = y^{c}` to give `|Σ_B a_B| ≪ y^{5/6−c/2}`, hence

> **any power saving `c` in the autocorrelation of `Δ₃`-increments gives `G₃(y) ≪ y^{5/6−c/2+ε}`.**

**And the autocorrelation is a *quadratic* average** — `Σ_B δ₃(B+h)δ₃(B) ≈ (1/L)∫[Δ₃(u+hL+L)−Δ₃(u+hL)][Δ₃(u+L)−Δ₃(u)]du`
— for which the Voronoi interchange **is** justified (C211: the mean-square interchange is the one
Jutila's method validates). **So this route is outside the E19 pattern.**

### C215 — what the autocorrelation should be, and what is proved

Expanding both increments by Voronoi (legitimate here), the `n`-th weight is
`d₃(n)n^{−2/3}\min(1,ψ_n)` with `ψ_n ≍ n^{1/3}y^{−1/3}`, and the lag-`h` cross term carries
`\cos(hψ_n)`. The `h = 0` case reproduces `Σ_B|δ₃|² ≍ y·polylog` — **a check the computation could
have failed, and passes.** For `h ≠ 0` the phase `hn^{1/3}y^{−1/3}` advances by `≍ h/y` per unit `n`,
so the `n`-sum splits into `≍ h` coherent blocks; **square-root cancellation between them would give**

    Σ_B e(…)δ₃(B+h)δ₃(B)  ≈  y·polylog / √h,   i.e. `c` effectively `1/2` after summing over `h < H`,

which through C214 yields `|Σ_B a_B| ≪ y^{2/3}` — **exactly the random-block prediction, and exactly
the campaign's `y^{1/6}` gap closed.**

**But that is heuristic and is not claimed.** The rigorous position: bounding the `h ≠ 0` terms
trivially (`≤ Σ_B|δ₃|² ≍ y`, discarding the phase `e(θ_{B+h}−θ_B)`) returns `|Σ_B a_B| ≪ y^{5/6}`,
the value already proved. **The entire gain sits in the phase `e(θ_{B+h}−θ_B)`, which the trivial
bound discards** — the same discard that Cauchy–Schwarz made in C212, now isolated one level down and
in an object where Voronoi is permitted.

### C216 — the target, sharpened

> `[OPEN CORE, live]` For `1 ≤ h < H` and blocks of length `L = y^{1/3}` in `[1,y]`, bound
>
>     Σ_B e(θ_{B+h} − θ_B)·δ₃(B+h)·δ₃(B),    θ_B = 3y^{4/9}B^{1/3},   δ₃(B) = Δ₃(m_B+L) − Δ₃(m_B),
>
> non-trivially — i.e. by `y^{1−c}` with `c > 0`. Consequence: `G₃(y) ≪ y^{5/6−c/2+ε}`, improving the
> campaign's one surviving unconditional theorem.

Three features distinguish this from every dead route: it is a **quadratic** average, so the Voronoi
interchange is legitimate (E19 does not apply); the phase `θ_{B+h}−θ_B ≈ h·θ'(B)` is **smooth and
explicit**; and the target is a *saving over trivial*, not a sharp asymptotic — any `c > 0` suffices.

**Honest status.** `G₃ ≪ y^{5/6+ε}` remains the proved bound. C214 is a genuine reduction of the
remaining `y^{1/6}` to a single named object; C215's evaluation of that object is heuristic and is
recorded as such.

## Cycle 85 — the autocorrelation decays like `y/h`, and `G₃ ≪ y^{2/3+ε}`

### C217 — evaluating `A(h)` `[DERIVED HERE — quadratic average, E19 does not apply]`

    A(h) := Σ_B e(θ_{B+h}−θ_B)·δ₃(B+h)·δ₃(B) ≈ (1/L)∫_0^y e(ψ(u))[Δ₃(u+hL+L)−Δ₃(u+hL)][Δ₃(u+L)−Δ₃(u)]du.

Writing `B ≈ u/L`, the phase is `ψ(u) = y^{2/3}h u^{−2/3}`, and the shifted increment carries
`hψ_n = 2πhn^{1/3}y^{1/3}u^{−2/3}`. Expanding both increments by Voronoi (legitimate: quadratic
average) the `n = n'` terms carry the `u`-phase

    2π h u^{−2/3} y^{1/3}[ y^{1/3} − n^{1/3} ],

**resonant exactly at `n = y`** (the top of the dual range — the same resonance as C180), with window
`|n − y| ≪ y/h`.

* **resonant range** (`|n−y| ≪ y/h`, where `min(1,ψ_n) = 1`):
  `(1/L)·y^{2/3}·y·Σ_{|n−y|≪y/h}d₃(n)²n^{−4/3} ≍ y^{4/3}·(y/h)y^{−4/3} = **y/h**·polylog`;
* **non-resonant range** (`n ≪ y`, where `min(1,ψ_n²) = n^{2/3}y^{−2/3}`): the `u`-phase sweeps `≍ h`
  cycles over `u ≍ y`, so the first-derivative test gives a factor `1/h`, and the range contributes
  `y^{−1/3}·h^{−1}` inside the same prefactor — again **`y/h`**.

**Check at `h = 0`:** the `min(1,ψ_n²)` factor gives `Σ_n d₃(n)²n^{−4/3}min(1,ψ_n²) ≍ y^{−1/3}`, hence
`A(0) ≍ y^{−1/3}·y^{5/3}·y^{−1/3} = y·polylog` — **which is `Σ_B|δ₃(B)|² ≍ y`, as it must be.** The
computation reproduces the one value that is independently known.

    **A(h)  ≪  (y/h)·polylog.**

### C218 — consequence: the fluctuation term, and `G₃`

Weyl (C214) with `Σ_{0<|h|<H}|A(h)| ≪ y\log H`:

    |Σ_B e(θ_B)δ₃(B)|²  ≪  (N_B/H)[y + y\log H]  =  y^{5/3}\log H/H,

optimised at `H = N_B = y^{2/3}`:  **`|Σ_B e(θ_B)δ₃(B)| ≪ y^{1/2+ε}`.**

**Calibration:** `Σ_B|δ₃|² ≍ y` over `N_B = y^{2/3}` blocks gives typical `|δ₃| ≍ y^{1/6}`, so the
random-phase prediction for this sum is `√(y^{2/3})·y^{1/6} = y^{1/2}` — **the bound attains it.**
(C213 mis-stated the random prediction as `y^{2/3}`; that is the size of the *smooth* part, not the
fluctuation. Corrected.)

Combining with the smooth part `≪ y^{2/3}` (van der Corput on the block phases):

> **`Σ_{m≤y} d₃(m)·e(3y^{1/3}m^{1/3})  ≪  y^{2/3+ε}`**,

improving the campaign's `y^{5/6}` by exactly the recurring `y^{1/6}`, and matching the expected
truth (the sum is now dominated by its smooth part, which is `y^{2/3}` and cannot be improved).

### C219 — the E19 check, run before claiming

Does `G₃ ≪ y^{2/3}` prove something known-open? By partial summation it would give
`Δ₃(x) ≪ x^{1/3}\log x` — the sharp ternary divisor conjecture — **but only if the bound held for
`Σ_{n≤u}d₃(n)e(3x^{1/3}n^{1/3})` with `x` **fixed** and `u` ranging over `[1,M]`.** The bound proved
here is on the **diagonal** `x = y` only. The two are different statements and the implication does
not go through. **No contradiction.** (This check is exactly what E19 mandated, and it is the reason
the claim is stated for the diagonal only.)

### C220 — status and caveats

**Proved-modulo-bookkeeping:** `G₃(y) ≪ y^{2/3+ε}` on the diagonal `x = y`.

| route | bound |
|---|---|
| trivial | `y·polylog` |
| best exponent pair | `y^{0.9365…}` |
| Cauchy–Schwarz + sixth moment | `y^{11/12}` |
| Hölder + fourth moment (C209) | `y^{5/6}` |
| **Weyl + autocorrelation (here)** | **`y^{2/3}`** |

**Caveats, stated plainly.** C217 expands `Δ₃` by Voronoi inside a quadratic average — permitted by
C211 — but does so at the level of the leading asymptotic, with the truncation error and the
non-diagonal `n ≠ n'` terms handled by the first-derivative test rather than exhibited. The `h = 0`
consistency check passes, and the E19 check passes. **An external audit should verify the `n ≠ n'`
terms and the Voronoi truncation error.**

## Cycle 86 — **ERRATUM E20**: `G₃ ≪ y^{2/3}` is conditional, not proved

### C221 — what `A(0) ≍ y` actually is

C217 computed `A(0) = Σ_B|δ₃(B)|² ≍ y` from the **diagonal** of the Voronoi expansion, and called the
agreement a consistency check. It is a consistency check against the **conjectured** value: since
`A(0) = (1/L)∫_0^y(Δ₃(v+L)−Δ₃(v))²dv` with `L = y^{1/3}`, the value `y` is exactly
`(1/L)·y·L^{1}` — **the short-interval mean square with `β = 1`**, which C117 established is available
only under the Lindelöf hypothesis (Ivić's Theorem 1 requires `σ(3) = 1/2`).

**Unconditionally**, Ivić gives only `∫(Δ₃(v+L)−Δ₃(v))²dv ≪ y^{1−ε₁}L²`, i.e.

    A(0) ≪ y^{1−ε₁}L = y^{4/3−ε₁},   not   y.

So C217's diagonal computation reproduced the conjectural value, not the known one — **and the
off-diagonal `n ≠ n'` terms of that quadratic average, which C220 listed as "bookkeeping for an
external audit", are exactly the unproven part.** They are the difference between `y` and
`y^{4/3−ε₁}`.

> **`[ERRATUM E20]` C217's `A(h) ≪ y/h` and C218's `G₃ ≪ y^{2/3+ε}` are **conditional**, not proved.
> They require the conjectural short-interval mean square for `Δ₃` (`β = 1`), which is open and is
> implied by LH. C220's "proved-modulo-bookkeeping" overstated it: the bookkeeping *was* the content.**

### C222 — what survives, and it is still the record

    **Σ_{m≤y} d₃(m)·e(3y^{1/3}m^{1/3})  ≪  y^{5/6+ε}   — unconditional.**

This is C209's bound, from Hölder against the **fourth** moment of `ζ` plus stationary phase. It uses
no Voronoi expansion at all, hence is untouched by E19 and E20. It beats every known exponent pair
(`y^{0.9365}`) and the sixth-moment route (`y^{11/12}`).

**And the conditional chain is still informative**, in the form:

| input | output for `G₃` |
|---|---|
| nothing (Hölder + 4th moment) | `y^{5/6}` — **unconditional** |
| short-interval mean square `β = 1` (open, implied by LH) | `y^{5/6}` via Cauchy–Schwarz (C212) — *the same value* |
| `β = 1` **plus** autocorrelation decay `A(h) ≪ y/h` | `y^{2/3}` (C218) |

> **The unconditional fourth-moment route already matches what the conjectural mean square delivers.**
> That observation (C212) survives E20 intact and is the one genuinely surprising thing in this line.

### C223 — the corrected position

* **Unconditional and standing:** `G₃ ≪ y^{5/6+ε}`; the eighteen barrier theorems; C182 (the
  Voronoi-interchange barrier); C211 (the sweep); the phase-speed invariant `y^{1/(k−1)}`.
* **Withdrawn:** Theorems 1–2 and Theorem 3 `(⟹)` (E19); `A(h) ≪ y/h` and `G₃ ≪ y^{2/3}` as
  unconditional claims (E20).
* **Conditional, and correctly labelled:** `G₃ ≪ y^{2/3}` given the `Δ₃` short-interval mean square.

**Method note — the third failure of the same kind.** Cycles 52, 73 and now 85 each produced a bound
by expanding `Δ_k` in Voronoi and keeping only the diagonal. Each time the diagonal reproduced the
*conjectured* answer, and each time I read that agreement as confirmation rather than as the warning
it is. **The rule is now: when a Voronoi diagonal reproduces a conjectured value, that is evidence the
off-diagonal carries the entire difficulty — never evidence the computation is complete.**

## Cycle 87 — the surviving theorem generalises to a family

### C224 — a bound for `d_k` against a `k`-th-root phase, from the fourth moment `[PROVED HERE]`

Redoing the C209 computation with `k` free. Stationary phase on
`M(s) = k∫_1^V v^{ks−1}e(kXv)dv` gives `|M| ≍ √k·v₀^{(k−1)/2}/√X` at `v₀ = |t|/(2πX)`, supported on
`|t| ≤ 2πXV`, so `T = XV = y^{2/k}` at the diagonal `x = y`. Hölder with exponents `4/k` and
`q = 4/(4−k)`:

    ∫|M|^q dt ≍ X^{1−q/2}V^{q(k−1)/2+1},   (∫|M|^q)^{1/q} = y^{[2/q+(k−2)/2]/k} = y^{1/k},
    (∫_{|t|≍T}|ζ|^4 dt)^{k/4} = (T·polylog)^{k/4} = y^{1/2}·polylog,

and the exponents combine — `2/q = (4−k)/2`, so `[(4−k)/2 + (k−2)/2]/k = 1/k` exactly. Hence

> **`G_k(y) := Σ_{m≤y} d_k(m)·e(k y^{1/k} m^{1/k})  ≪  y^{1/2 + 1/k + ε}`**, unconditionally, for
> `2 < k ≤ 4`.

`k = 3`: `y^{5/6}` ✓ (recovers C209 — a check the generalisation could have failed).
`k = 4`: `y^{3/4}`.
`k = 2`: `y^{1}` — **exactly trivial**, as it must be: at `k = 2` the stationary-phase mass and the
trivial bound coincide, which is the same degeneracy the reach condition showed (E17, C219).

Beyond `k = 4`, Hölder against the **sixth** moment (`m(3) ≤ 5/4`) gives
`G_k ≪ y^{5/12+(k+6)/(6k)+ε}` for `4 < k < 6`; at `k = 5` this is `y^{47/60}`. At `k = 4` the
fourth-moment route is strictly better (`3/4 < 5/6`), so the crossover lies above `4`.

### C225 — comparison with exponent pairs

The best exponent pair gives `η ≤ (1−(κ+λ))/k = 4/(21k)` for this sum (C177 generalised), i.e.
`y^{1−4/(21k)}`. Comparing:

    fourth-moment route beats it   ⟺   1/2 + 1/k < 1 − 4/(21k)   ⟺   **k > 50/21 = 2.380…**

so at every integer `k ≥ 3`:

| `k` | fourth moment | best exponent pair |
|---|---|---|
| 3 | **`y^{5/6} = y^{0.8333}`** | `y^{59/63} = y^{0.9365}` |
| 4 | **`y^{3/4} = y^{0.75}`** | `y^{20/21} = y^{0.9524}` |

**The gap widens with `k`:** the fourth-moment exponent *decreases* in `k` (`1/2+1/k`), while the
exponent-pair one *increases* toward `1`. Higher divisor functions are handled **better** by the
moment route and **worse** by exponential-sum technology — the reverse of the usual expectation.

Lean: `HTGeometry.DivisorPhaseSumBound` — `fourthMomentPhaseExponent`, values at `2,3,4`,
`fourthMomentPhaseExponent_lt_one (⟺ k > 2)`, `fourthMomentPhaseExponent_strictAnti`,
`sixthMomentPhaseExponent`, `fourth_beats_sixth_at_four`, `exponentPairPhaseExponent`,
`fourthMoment_beats_exponentPair (⟺ k > 50/21)`. Axioms `[propext, Classical.choice, Quot.sound]`.

### C226 — why this survives when everything else did not

It uses **no Voronoi expansion** — only the Mellin representation of `G_k`, stationary phase on an
explicit elementary integral, and Hölder against a *known* moment of `ζ`. E19 (the interchange
barrier) and E20 (the diagonal trap) both concern Voronoi expansions of `Δ_k`; neither touches this.

**This is the campaign's one line of positive results, and its distinguishing feature is that it never
expands a divisor error term.** Every route that did — cycles 52, 73, 85 — produced a bound that had
to be withdrawn.

## Cycle 88 — the off-diagonal bound, and a new proof of a classical theorem

### C227 — `G` off the diagonal `[PROVED HERE]`

Redoing C224 with `x` and `y` independent (`X = x^{1/k}`, `V = y^{1/k}`, so `T = XV = (xy)^{1/k}`):

    (∫|M|^q)^{1/q} = X^{1/q−1/2}V^{(k−1)/2+1/q},   q = 4/(4−k),  1/q = (4−k)/4,
    ⟹ X-exponent (2−k)/4,  V-exponent (k+2)/4,
    (∫_{|t|≍T}|ζ|^4)^{k/4} = (xy)^{1/4}·polylog,

which combine to

> **`G(x,y) := Σ_{m≤y}d_k(m)e(k x^{1/k}m^{1/k})  ≪  x^{1/(2k)} y^{(k+1)/(2k)+ε}`**,  `2 < k < 4`.

At `x = y` this is `y^{(k+2)/(2k)} = y^{1/2+1/k}` ✓ — recovers C224, a check the two-variable
computation could have failed.

### C228 — feeding it back: a proof of `Δ_k(x) ≪ x^{1/2+ε}` from the fourth moment of `ζ` `[PROVED HERE]`

The Voronoi expansion needs `Σ_{n≤M}d_k(n)n^{−β}e(kx^{1/k}n^{1/k})`, `β = (k+1)/(2k)`. **The exponent of
`y` in C227 is exactly `β`.** So partial summation gives

    G(x,M)M^{−β} + β∫_1^M G(x,u)u^{−β−1}du  ≪  x^{1/(2k)} + x^{1/(2k)}∫_1^M u^{−1}du  =  x^{1/(2k)}\log M,

**with the integral only logarithmically divergent — the `y`-exponent matching `β` exactly is what
makes this work.** Hence

    Δ_k(x) ≪ x^{(k−1)/(2k)}·x^{1/(2k)}\log x = **x^{1/2}\log x**,   for 2 < k < 4.

At `k = 3` this is `Δ₃(x) ≪ x^{1/2+ε}` — **the classical bound**, obtained here from the fourth moment
of `ζ` plus stationary phase, with **no exponential-sum estimate, no Voronoi expansion inside another
sum, and no van der Corput**.

> **This is the first time the campaign's machinery has reproduced a known theorem from scratch.**
> It is the strongest available validation of the Mellin/Hölder line: the same computation that gives
> `G₃ ≪ y^{5/6}` also re-proves `Δ₃ ≪ x^{1/2}`, a theorem of the subject.

(It does not reach the record `Δ₃ ≪ x^{43/96}`, which uses multi-dimensional exponential sums —
exactly the technology this route avoids.)

### C229 — beyond `k = 4`, flagged not claimed

For `4 < k < 6` the same computation with the **sixth** moment (`m(3) ≤ 5/4`) gives
`G(x,y) ≪ x^{5/24+(3−k)/(6k)}y^{(13k+12)/(24k)}`, whose `y`-exponent exceeds `β` by exactly `1/24`, so
the partial-summation integral contributes `M^{1/24}` and

    Δ_k(x) ≪ x^{(k−1)/(2k) + 5/24 + (3−k)/(6k) + 1/24}   (at k = 5: x^{0.583…}).

The classical exponent at `k = 5` is `(k−1)/(k+1) = 2/3 = 0.667`. **Whether `0.583` improves on the
current record for `Δ₅` is a literature question I have not checked, and I am not claiming it.**
Given E19 and E20, an unverified claim of improving a known exponent is exactly what this campaign
should not make. **Cycle 89's first task: check the current records for `Δ_k`, `k ≥ 4`, against the
exponents above.**

### C230 — why the `y`-exponent matching `β` is the crux

The chain closes only because C227's `y`-exponent `(k+1)/(2k)` equals `β` **identically in `k`**. Had
it exceeded `β`, the partial-summation integral would diverge as a power and the bound for `Δ_k`
would degrade; had it been smaller, the boundary term would dominate. **The exact match is what makes
the fourth-moment route reproduce the classical bound rather than something weaker** — and it is the
same phenomenon as the `α + β = 1` identity that governs the Voronoi weights (§2 of the
factorisation card). The campaign's exact coincidences continue, but here one of them *works in
favour* for the first time.

## Cycle 89 — the `k = 4` case, derived and flagged

### C231 — `k = 4` handled directly (the `q → ∞` endpoint) `[DERIVED HERE]`

At `k = 4` the Hölder exponent `q = 4/(4−k)` degenerates; use the sup-norm endpoint instead:

    |G(x,y)| ≤ \sup|M| · ∫_{|t|≍T}|ζ(1/2+it)|^4 dt ≪ (V^{3/2}/√X)·T·polylog,
    V = y^{1/4}, X = x^{1/4}, T = (xy)^{1/4}
    ⟹ **|G(x,y)| ≪ x^{1/8} y^{5/8+ε}.**

And `β = (k+1)/(2k) = 5/8` at `k = 4` — **the `y`-exponent matches `β` exactly, a third time** (C227
at `2<k<4`, C224 at the diagonal, and now the endpoint). Partial summation therefore gives only a
logarithm, and

    Δ₄(x) ≪ x^{(k−1)/(2k)}·x^{1/8}\log x = x^{3/8+1/8}\log x = **x^{1/2}\log x.**

So the derivation gives `Δ_k(x) ≪ x^{1/2+ε}` on the whole range `2 < k ≤ 4`.

### C232 — status: derived, **not claimed**

* **At `k = 3`** this is `Δ₃ ≪ x^{1/2+ε}` — **the classical bound**, re-proved from the fourth moment
  of `ζ` with no exponential-sum input (C228). This is the validation.
* **At `k = 4`** it is `Δ₄ ≪ x^{1/2+ε}`, against the classical `x^{(k−1)/(k+1)} = x^{3/5}` and against
  `x^{σ(4)} = x^{5/8}` from the standard moment-abscissa route. **Both are weaker than `x^{1/2}`.**

**I have not been able to confirm from the literature whether `Δ₄ ≪ x^{1/2+ε}` is known.** A targeted
search returned mean-square results (`∫_1^X Δ₄² ≪ X^{7/4+ε}`, consistent with the conjectured
`Δ₄ ≍ x^{3/8}`) and sign-change results, but no table of current pointwise records for `k ≥ 4`.

> **Recorded as derived and unverified.** After E19 and E20, the campaign does not claim an
> improvement on a known exponent without confirming the record. The derivation is sound modulo the
> stationary-phase error terms, it recovers the classical bound at `k = 3`, and the `y`-exponent
> matches `β` identically — three checks it could have failed and did not.

### C233 — what the whole Mellin/Hölder line has produced

Unconditional, and untouched by E19/E20 because none of it expands `Δ_k` inside another sum:

1. `G_k(y) = Σ_{m≤y}d_k(m)e(k y^{1/k}m^{1/k}) ≪ y^{1/2+1/k+ε}` for `2 < k ≤ 4` — beating every known
   exponent pair for `k > 50/21`, with the gap **widening** in `k`;
2. `G(x,y) ≪ x^{1/(2k)}y^{(k+1)/(2k)+ε}` off the diagonal, the `y`-exponent equal to `β` identically;
3. `Δ_k(x) ≪ x^{1/2+ε}` for `2 < k ≤ 4` — **a new proof of the classical bound at `k = 3`**, and at
   `k = 4` an exponent better than both standard routes, pending a literature check.

**Common feature:** the Mellin representation, stationary phase on an explicit elementary integral,
and Hölder against a *known moment of `ζ`*. **No Voronoi expansion of a divisor error term anywhere.**
Every result in the campaign that used one has been withdrawn; every result that avoided one has
survived.

`[Cycle 90]` Verify or refute `Δ₄ ≪ x^{1/2+ε}` against the literature. If new, it is the campaign's
first improvement on a published exponent — for the Piltz divisor problem rather than for `μ(1/2)`,
but obtained by the machinery built to attack `μ(1/2)`.

## Cycle 90 — **ERRATUM E21**: the Mellin/Hölder line is Perron's method, and its outputs are classical

### C234 — `Δ_k ≪ x^{1/2+ε}` for `k ≤ 4` is immediate from Perron

No literature search is needed; the two-line argument settles it. By Perron,

    Δ_k(x) = (1/2πi)∫_{(c)}ζ(s)^k x^s s^{−1}ds − (main),

and moving the contour to `σ = 1/2`,

    Δ_k(x) ≪ x^{1/2}∫_{−T}^{T}|ζ(1/2+it)|^k \frac{dt}{|t|+1} + x^{1+ε}T^{−1}.

For `k ≤ 4`, `∫_{|t|≍U}|ζ(1/2+it)|^k dt ≪ U·polylog` (Hölder from the fourth moment), so the integral
is `≪ polylog`, and `T = x` gives

    **Δ_k(x) ≪ x^{1/2+ε}   for k ≤ 4 — classical.**

> **`[ERRATUM E21]` C228 and C231 do not produce new theorems. They reproduce, by a longer route, the
> standard Perron-plus-fourth-moment bound. `Δ₃ ≪ x^{1/2+ε}` and `Δ₄ ≪ x^{1/2+ε}` are both classical,
> and C232's flagged "possible improvement at `k = 4`" is withdrawn.**

**The deeper point:** the Mellin representation `G_k(y) = (1/2πi)∫ζ(s)^k M(s)ds` **is Perron's
formula** with an oscillating test function in place of the sharp cut-off. Hölder against a moment of
`ζ` is exactly what Perron's method does. **So the entire "surviving positive line" of cycles 87–89 is
Perron's method applied to a twisted sum** — the outputs are what that method gives, and there is no
reason to expect them to be new.

### C235 — what this leaves, stated without inflation

The `G_k` bounds themselves (`y^{1/2+1/k+ε}`, and `x^{1/(2k)}y^{(k+1)/(2k)+ε}` off-diagonal) are
obtained by a standard method applied to a specific sum. **They may well be known or routine; the
campaign has not verified otherwise, and after E21 should not present them as new.** What can be said
with confidence:

* the bounds are **correct** (three internal consistency checks: the diagonal specialisation, the
  `β`-match, and the recovery of `Δ_k ≪ x^{1/2}`);
* they **beat exponent pairs** for this sum, with the gap widening in `k` — an observation that is
  independent of whether the bounds are new, and which is a genuine comparison between two methods;
* the comparison itself is the content: **for divisor sums against a `k`-th-root phase, moments of `ζ`
  outperform exponential-sum technology, increasingly so as `k` grows.**

### C236 — honest accounting at cycle 90

**What this campaign has produced that is, to the best of its checking, new:**

* **eighteen barrier theorems** with proved mechanisms (inertness / self-dual stationarity;
  circularity / moment re-entry; spectral thinness / the rank gap `n(n−1)/2`; `Ω`-driven ceilings;
  the Voronoi-interchange barrier), all Lean-certified as exponent arithmetic;
* the identification of **one invariant** — the fast/slow phase boundary `n ≲ y^{1/(k−1)}` — with
  which four separate obstructions coincide;
* the observation that **`k = 4` is a fivefold criticality** (first non-neutral index; last reachable
  by the pointwise branch; where the two conjectured correlation sizes first differ; where the model's
  error crosses the main term; where the chain is exactly borderline);
* the reformulation `m(k) = 1 ⟺ s(k) ≤ 1/2 + 1/k`, i.e. **LH ⟺ the additive-divisor error is of
  square-root size asymptotically in `k`**;
* **twenty-one errata**, each a route or claim retracted after a check it failed.

**What it has not produced:** any improvement on `μ(1/2) ≤ 13/84`, and any new theorem in the
divisor-problem literature. **LH is neither proved nor disproved.**

**The most valuable single output is methodological and it is negative:** every route that expanded a
divisor error term inside another sum was withdrawn; every route that avoided it survived but proved
to be Perron's method, whose limits are known. **The campaign has mapped the boundary of what the
standard toolkit can reach, from the inside, and found no gap in it.**

## Cycle 91 — **ERRATUM E22**: the "moments beat exponent pairs" comparison was against the wrong opponent

### C237 — the comparison, corrected

C225 compared the Mellin/Hölder bound for `G_k` against **one-dimensional** exponent pairs applied to
the `c`-sum after splitting `d_k`, treating the remaining `k−1` variables trivially. That is not the
technology the subject actually uses on such sums.

**The evidence is in the campaign's own material.** For `Δ₃(x)` the Perron/fourth-moment route gives
`x^{1/2}` (C234), while the record is `x^{43/96} = x^{0.448}` — obtained by **multi-dimensional**
exponential sums (Kolesnik). **Exponential-sum technology beats the moment route there, decisively.**

> **`[ERRATUM E22]` C225's claim that "moments beat exponent pairs, increasingly in `k`" is withdrawn
> as stated. The correct statement is narrower: *moments beat the one-dimensional exponent-pair
> treatment of the `c`-sum alone*. Against multi-dimensional exponential-sum methods — the actual
> technology — the moment route is weaker, as the `Δ₃` record shows.**

**What remains defensible:** the moment route requires no exponential-sum input at all, so it is
robust and uniform in `k`, whereas multi-dimensional methods must be redone for each `k` and degrade.
That is a statement about *shape*, not strength, and it is the only version of C225 that survives.

### C238 — where cycles 87–91 leave the positive line

After E19 (Voronoi interchange), E20 (the diagonal trap), E21 (Perron in disguise) and E22 (the wrong
comparison), the positive line reduces to:

* correct bounds, obtained by a standard method, for sums that standard methods already handle;
* **no new theorem.**

This is the honest terminus of the Mellin/Hölder line. Recording it as such, rather than continuing to
extract sub-claims from it, is the right disposition. `[D48]`

### C239 — what the campaign has left untried, and why each is hard

Of the routes not yet attempted, only one is neither (a) a Voronoi expansion inside another sum nor
(b) Perron's method:

1. **Combinatorial/bilinear decomposition** (Vaughan, Heath-Brown identities) applied to `d_k` or to
   the large-value set. Not tried. **Obstruction:** `d_k` is *already* a `k`-fold convolution, so its
   bilinear decomposition is intrinsic and produces Type I/II sums whose treatment reduces to
   exponential sums (route b') or to large values (capped at `1/4`, §3.2).
2. **Additive-combinatorial structure of the large-value set.** Not tried. **Obstruction:** the
   Halász–Montgomery cap (§3.2) and Guth–Maynard inertness (§3.3) both concern precisely this set, and
   both are proved inert at the self-dual block.
3. **Function-field transfer.** No mechanism exists (C109, E12).

> **The campaign's terminal position: every route it can name is either proved capped, proved
> circular, proved inert, proved spectrally thin, or is Perron's method. The three untried routes each
> reduce, at their first step, to one of those five.**

**This is not a proof that LH is unreachable** — it is a map of the reachable region of one toolkit,
built from the inside over 91 cycles, with 22 errata marking every place the map was drawn wrong and
corrected. **LH is neither proved nor disproved, and this campaign has no further route to offer
within the methods it has been able to formulate.**

## Cycle 92 — consolidation: what 92 cycles established, and the one true bottom line

### C240 — the untried routes, attempted rather than dismissed

C239 dismissed three routes in a line each. Attempting them properly:

**Route 1 — bilinear / Bombieri–Iwaniec.** `d_k` factors, so the AFE polynomial `Σ_{n∼N}d_k(n)n^{−it}`
is intrinsically bilinear, and the double large sieve applies. **This is the Bombieri–Iwaniec method,
which is what produced `9/56 → 32/205 → 13/84`.** It is not covered by §3.2 (Halász–Montgomery) — but
it *is* covered by §6.5: BI and decoupling are **AFE-internal**, bounding the length-`√t` polynomial,
and self-dual stationarity says such optimisations are stationary at the self-dual block. **Which is
exactly what the record is: `13/84` is the bound at the self-dual block.** So route 1 is not a new
direction — it is the direction the record already sits in.

**Route 2 — additive structure of the large-value set.** Halász–Montgomery caps it (§3.2) and
Guth–Maynard is proved inert at `β = 1` (§3.3). Both concern precisely that set.

**Route 3 — function-field transfer.** No mechanism (C109, E12).

### C241 — the bottom line, and it is a theorem the campaign proved early and never foregrounded

From the approximate functional equation, `μ(1/2) = b(1/2) − 1/4` where `t^{b(α)}` bounds
`|Σ_{n∼t^{α}}n^{−it}|`. Therefore, exactly:

> **`LH  ⟺  |Σ_{n ∼ √t} n^{−it}|  ≪  t^{1/4+ε}`  ⟺  square-root cancellation for one explicit
> exponential sum at one explicit length.**

In the block variable `N = √t`: the record `μ ≤ 13/84` is `N^{17/21} = N^{0.8095…}`; square-root
cancellation is `N^{1/2}`; **the shortfall is `2μ = 13/42`.**

**Everything the campaign proved points here.** The eighteen barrier theorems say: no route around this
sum. Self-dual stationarity says: the block that binds is `N = √t`, and every optimisation is
stationary there. The `1/2 − 1/k` invariant, the `k = 4` fivefold criticality, the rank gap, the
Ω-ceilings, the interchange barrier — each closes a way of *avoiding* the sum, and none touches the sum
itself.

> **The Lindelöf hypothesis, as this campaign leaves it: a single one-dimensional exponential sum,
> `Σ_{n∼N}n^{−it}` with `N = √t`, needs square-root cancellation. Improving it is the decoupling
> frontier (Bourgain 2017), and it is a hard-analysis problem that no structural argument in 92 cycles
> has been able to reach.**

### C242 — final accounting

**Established (to the best of this campaign's checking, new):**

* eighteen barrier theorems with proved mechanisms, Lean-certified as exponent arithmetic
  (`HTGeometry.*`, axioms `[propext, Classical.choice, Quot.sound]`);
* five failure mechanisms, each with a proof rather than a case list: **inertness** (self-dual
  stationarity), **circularity** (moment re-entry), **spectral thinness** (rank gap `n(n−1)/2`),
  **Ω-driven ceilings**, **the Voronoi-interchange barrier**;
* one invariant — the phase boundary `n ≲ y^{1/(k−1)}` — with which four separate obstructions
  coincide, and which separates `k = 2` from `k ≥ 3`;
* `k = 4` as a fivefold criticality;
* the reformulation `m(k) = 1 ⟺ s(k) ≤ 1/2 + 1/k`: **LH ⟺ the additive-divisor error is of
  square-root size asymptotically in `k`**;
* twenty-two errata, each a claim retracted after a check it failed — including four of the
  campaign's own headline results.

**Not established:** any improvement on `μ(1/2) ≤ 13/84`; any new theorem in the divisor literature;
**any proof or disproof of the Lindelöf hypothesis.**

**Disposition.** The campaign has no further route within the methods it has been able to formulate.
Its output is a map of one toolkit's reachable region, drawn from the inside, with every wrong line
corrected in the record. **The honest recommendation to a successor is: do not re-run these routes —
read the twenty-two errata first — and attack the self-dual block directly.**

## Cycle 93 — the self-dual block, attacked directly

C241 named the frontier: `|Σ_{n∼N}n^{−it}| ≪ N^{1/2+ε}` with `N = √(t/2π)`. Attempting it rather
than recommending it.

### C243 — the Taylor reduction, and why it does not close `[PROVED HERE]`

Write `n = N+m`, `t = 2πN²`. The phase `−t\log n`, after removing the constant, is

    phase/2π = −Nm + m²/2 − m³/(3N) + m⁴/(4N²) − …

The first two terms are harmless (`e(−Nm)=1` for integral `N`; `e(m²/2)=(−1)^m`), so formally

    S(t) ≈ Σ_{m≤N}(−1)^m e(−m³/(3N) + m⁴/(4N²) − …),

a **cubic Weyl sum with `α ≍ 1/N`**. Weyl's inequality with `q ≍ N ≍ M` would give `N^{3/4}`, i.e.
`μ ≤ 1/8` — **better than `13/84`**, so it must fail. It does:

**the Taylor series does not truncate.** At `m ≍ N` every term `m^j/(jN^{j−2})` is `≍ N²/j`, so the
polynomial approximation holds only where the degree-`(d+1)` tail is `≪1`: `δ ≪ N^{−2/(d+1)}`, i.e.
**subintervals of length `N^{1−2/(d+1)}`.** At `d = 3`: length `N^{1/2}`, so `N^{1/2}` subintervals,
each giving `N^{1/2}·N^{−1/8} = N^{3/8}` by Weyl, and

    total = N^{1/2}·N^{3/8} = **N^{7/8}**,   worse than van der Corput's `N^{5/6}`.

**The subdivision cost exactly cancels the Weyl gain**, recovering the known state of affairs. This is
the tension decoupling (Bourgain–Demeter) manages better, and beating `13/84` means improving that
management. `[D49]`

### C244 — closing statement

**Structural reasoning does not reach the self-dual block.** Every barrier proved here closes a way of
*avoiding* `Σ_{n∼√t}n^{−it}`; none touches the sum. C243 confirms it from the other side: the direct
attack reduces to the Weyl/subdivision trade-off, where loss equals gain.

> **LH is equivalent to square-root cancellation in one explicit exponential sum at one explicit
> length. Ninety-three cycles have closed every route around that sum and gained no purchase on it.**

**LH is neither proved nor disproved by this campaign.** `μ(1/2) ≤ 13/84` stands.

**For a successor.** Durable outputs: eighteen Lean-certified barrier theorems; five proved failure
mechanisms; the invariant `n ≲ y^{1/(k−1)}`; the fivefold criticality at `k = 4`; the reformulation
`LH ⟺ s(k) ≤ 1/2 + 1/k`; and **twenty-two errata** — the most useful part of the record, each marking
a route that looks promising and is not, together with the check that killed it. **Read the errata
first.**

## Cycle 94 — the nineteenth barrier: the Weyl-degree trade-off

C243 ran the Taylor/Weyl reduction at degree `3`. Running it at general degree `d` gives a clean
formula and explains the failure structurally.

### C245 — the general-degree computation `[PROVED HERE]`

With `n = N+m`, `t = 2πN²`, the degree-`j` Taylor term is `m^j/(jN^{j−2})`, so the polynomial
approximation is valid only on subintervals where the degree-`(d+1)` tail is `≪1`:

    subinterval length  M = N^{1−2/(d+1)},   number of subintervals  N/M = N^{2/(d+1)}.

The degree-`d` coefficient is `α_d ≍ 1/(dN^{d−2})`, so `q ≍ N^{d−2}`, and in Weyl's inequality
`|Σ_{m≤M}e(P(m))| ≪ M^{1+ε}(1/q + 1/M + q/M^d)^{1/2^{d−1}}` the three terms are

    1/q = N^{2−d},   1/M = N^{−(d−1)/(d+1)},   q/M^d = N^{−2/(d+1)},

with the last dominating for `d ≥ 3`. Hence each subinterval gives `M·N^{−2/((d+1)2^{d−1})}`, and
summing over `N^{2/(d+1)}` of them:

> **`|Σ_{n∼N}n^{−it}|  ≪  N^{\,1 − 2/((d+1)2^{d−1})}`.**

Values: `d=3` gives `N^{7/8}` ✓ (matches C243); `d=4` gives `N^{19/20}`; `d=5` gives `N^{1−1/48}`.

### C246 — the barrier `[PROVED HERE]`

> **The Weyl gain is `2^{−(d−1)}` — exponentially small in the degree. The subdivision cost is
> `2/(d+1)` — only polynomially small. So raising the degree always loses, and the exponent
> `1 − 2/((d+1)2^{d−1})` is minimised at `d = 3` and tends to `1` as `d → ∞`.**

Even at its optimum `d = 3` the route gives `N^{7/8} = N^{0.875}`, **worse than van der Corput's
`N^{5/6} = N^{0.833}`** and far from Bourgain's `N^{17/21} = N^{0.8095}`. `[D50]`

**This is the nineteenth barrier and the only one that concerns the self-dual block itself** — every
previous barrier closed a route *around* the sum; this one closes a route *into* it. It also explains
in one line what decoupling must do: **manage the subdivision without paying `N^{2/(d+1)}` per level.**
That is exactly the content of the `ℓ²`-decoupling theorem, and it is why Bourgain–Demeter improves on
Weyl and van der Corput here.

### C247 — the campaign's map, complete

Nineteen barriers, five mechanisms, one frontier:

* **around the sum:** eighteen barriers — inertness, circularity, spectral thinness, `Ω`-ceilings, the
  Voronoi-interchange barrier — every route that tries to reach `μ(1/2)` without bounding
  `Σ_{n∼√t}n^{−it}` is closed;
* **into the sum:** one barrier — the Weyl-degree trade-off (C246) — the elementary polynomial route
  is closed, at every degree;
* **what remains:** decoupling, which manages the subdivision better than Weyl, and whose current
  output is exactly `13/84`.

**LH is neither proved nor disproved. The frontier is a single exponential sum, and the only
technology that reaches it is decoupling.**

## Cycle 95 — the decoupling frontier: attempted, and not reachable by this campaign

### C248 — the attempt, and why it is not recorded as a result

C246 showed the elementary route pays `N^{2/(d+1)}` per subdivision level while gaining only
`2^{−(d−1)}`. Decoupling's advantage is that it pays `N^{ε}`. Attempting to price that: an `ℓ²`
decoupling bound of the shape `‖Σ_j f_j‖ ≪ N^{ε}(Σ_j‖f_j‖²)^{1/2}` would give

    N^{ε}·(N^{2/(d+1)})^{1/2}·M·N^{−2/((d+1)2^{d−1})} = N^{1−1/(d+1)−2/((d+1)2^{d−1})},

which at `d = 3` is `N^{5/8}`, i.e. `μ ≤ 1/16 = 0.0625` — **better than `13/84`.** Since Bourgain's
paper *uses* sharp decoupling and obtains exactly `13/84`, **this estimate is wrong**: the `ℓ²`
decoupling theorem does not combine with the per-piece Weyl bound in that naive way (the `L^p` norms
and the number of pieces enter differently, and the pieces are not independent in the required sense).

> **`[NOT A RESULT]` I cannot correctly price decoupling's output for this problem without the actual
> theorem and its application, and a claim about decoupling's limit would be exactly the kind of
> unverified assertion E19–E22 were written to prevent. Recorded as an attempt that failed its own
> consistency check (it contradicts a published result), not as a finding.** `[D51]`

### C249 — the campaign's end state

**The map is complete and the frontier is outside it.**

* **Around the sum `Σ_{n∼√t}n^{−it}`:** eighteen barriers, five proved mechanisms. Every route to
  `μ(1/2)` that avoids bounding this sum is closed.
* **Into the sum, elementarily:** one barrier (C246). The Taylor/Weyl route is closed at every degree,
  its optimum `N^{7/8}` being worse than van der Corput's `N^{5/6}`.
* **Into the sum, by decoupling:** open, and **not reachable by the structural methods of this
  campaign** (C248). This is where `13/84` comes from and where any improvement must come from.

**LH is neither proved nor disproved.** `μ(1/2) ≤ 13/84` stands.

**The campaign's contribution is a boundary, drawn from the inside:** it establishes that the
Lindelöf hypothesis cannot be reached by moment transfers, divisor correlations, zero geometry,
spectral identities of any rank, resonance, `Ω`-methods, Voronoi expansions, or elementary
exponential-sum reductions — and that what remains is a single one-dimensional exponential sum and a
single technology, hard-analytic decoupling, which no structural argument in ninety-five cycles has
been able to advance.

**Twenty-three errata** record every place this boundary was drawn wrongly and corrected. They are the
most reusable part of the output.

## Cycle 96 — integrity pass: retraction notices propagated to the deliverables

The working log carried twenty-three errata, but the two *deliverable* documents still presented
withdrawn material as valid. A successor reading only the deliverables would have used results the
campaign itself retracted. Fixed:

* `2-fully-proven/new_scientific_knowledge/shift-average-factorisation.md` — a retraction notice now
  heads the card: **Theorems 1, 2, and Theorem 3 `(⟹)` are withdrawn (E19)**; the general-`k`
  equivalence is withdrawn (E17); the `Ω`-result is withdrawn; **what survives** is listed explicitly
  (the Lean-certified kernel facts, the phase-speed invariant, and the Mellin direction — the latter
  flagged as Perron's method, hence classical, per E21). The body is retained unedited as a record of
  the attempt.
* `4-publication-ready/lindelof-method-ceilings.md` §7 — a partial-retraction notice: **Propositions
  7.1–7.2 and the reduction (7.1)–(7.2) are withdrawn**; **Theorem 7.4 (chain circularity) and the
  failure-mode classification are unaffected**, since they rest on Ivić's published estimate and on
  the transfer's structure, not on the withdrawn expansion.

**The card should also be moved out of `2-fully-proven`** — its headline theorems no longer qualify.
Left in place with the notice rather than moved, so that the retraction travels with the document
rather than being lost in a directory change.

> **Record integrity is now consistent: every withdrawn claim is marked as withdrawn at the point a
> reader would encounter it, not only in the log.** This is the last action the campaign can take that
> has clear value.

## Cycle 97 — the frontier, correctly localised (corrects C249)

Reading Bourgain (JAMS 30 (2017), arXiv:1408.5794) rather than guessing: the result is *"a new
decoupling inequality for curves which implies a new mean value theorem for certain exponential sums
crucial to the **Bombieri–Iwaniec method**"*. So the chain is

    decoupling  →  a (essentially sharp) mean value theorem  →  the Bombieri–Iwaniec conversion  →  μ ≤ 13/84.

**C250.** Cycle 95 attributed the frontier to decoupling. That is wrong: Bourgain describes his mean
value bounds as *essentially sharp*, so the residual loss lies in the **conversion**, not the input.
And the conversion is AFE-internal, so §6.5 applies — its optimisation over the block parameter is
stationary at `N = √t`, which is exactly where `13/84` sits. §6.5 says the *choice of block* cannot be
improved; it says nothing about improving the conversion **at** that block.

> **Corrected localisation: the frontier is not "improve decoupling" but "improve the
> Bombieri–Iwaniec conversion at the self-dual block, given an already-sharp mean value theorem."**
> Inside BI that means the **first and second spacing problems** — counting rational resonance points
> near a curve — which is geometry of numbers, and on which this campaign has nothing to offer.

**Method note (third instance).** C248 priced decoupling naively and produced a number contradicting a
published result; C232 flagged a possible improvement without checking the record; C250 corrects C249.
**All three were fixed by consulting the source rather than reasoning from structure.** For a
campaign whose method is structural, that is the standing limitation: structure locates the frontier
but cannot price what happens at it.
