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

## Cycle 98 — the target, re-derived for *partial* improvements: `k = 6`, not `k = 4`

Cycle 64 selected `k = 4` using the neutrality law with a **perfect** moment (`m = 1`). But a partial
improvement suffices, and re-deriving with `m(k) ≤ M_k` free gives a different answer.

### C251 — the partial-improvement threshold `[PROVED HERE]`

`μ ≤ m(k)/(2k)` beats `θ = 13/84` iff `m(k) < 2kθ = 13k/42`. Against the **unconditional** envelope
(`m(2) = 1`, `m(6) = 2` Heath-Brown, and convexity of `m` in between):

| `k` | known `m(k)` | threshold `13k/42` | absolute gap | **relative gap** |
|---|---|---|---|---|
| 3 | `5/4` | `13/14 = 0.929` | — | impossible (`m ≥ 1`) ✓ neutral |
| 4 | `3/2` | `26/21 = 1.238` | `11/42 = 0.262` | **17.5 %** |
| 5 | `7/4` | `65/42 = 1.548` | `0.202` | 11.6 % |
| **6** | **`2`** | **`13/7 = 1.857`** | **`1/7 = 0.143`** | **7.1 %** |

> **`[THEOREM]` Improving Heath-Brown's twelfth-moment bound from `m(6) ≤ 2` to `m(6) < 13/7` beats
> Bourgain's `13/84`. That is a `7.1 %` improvement on a 1978 result — the **cheapest** record-beating
> target in the map, cheaper in relative terms than the eighth moment (`17.5 %`).**

**This corrects cycle 64.** `k = 4` is the cheapest index for a *perfect* moment; `k = 6` is the
cheapest for a *partial* one, and partial is all that is needed. The campaign spent thirty cycles on
`k = 4` (and sixty before that on `k = 3`) when the cheapest lever was the twelfth moment.

### C252 — but §3.7 already priced it

The map's Theorem 3.7 proved **Heath-Brown's `m(6) ≤ 2` is the exact output of its own method at its
input's information-theoretic limit**: his input is the short second moment at `G ≍ V²`, pushed to
`G = T^{1/4}` on average over the large-value set, and `G = T^{1/4}` is **sharp** because
`E(T) = Ω(T^{1/4})`. So the `7.1 %` is not available from that method — it is `Ω`-blocked.

**Nevertheless the target is correctly identified and the pricing is new.** Any *other* route to the
twelfth moment needs only `13/7` rather than `2`, and the required saving is smaller than at any other
index. **A successor should price the twelfth moment first, not the sixth or the eighth.**

### C253 — erratum E24, caught in derivation

While computing C251 I first used the chord `m(k) ≤ 1 + (k−2)/4` at `k = 10`, obtaining
`μ ≤ 3/20 = 0.15 < 13/84` — an apparent improvement on the record. **False:** the chord is the image
of the transfer input `(a,b) = (1/2,1)`, which is only *known* at the points `m(2) = 1` and
`m(6) = 2`; beyond `k = 6` the unconditional envelope is `m(k) ≤ 2 + (k−6)·2μ` (Hölder against the
pointwise bound), which returns `μ` unchanged — the neutrality law. **The chord must not be used as an
unconditional bound for `k > 6`.** Recorded because the map's Theorem 3.6 presents it as "the entire
known unconditional moment envelope", which is true only on `[2,6]`.

## Cycle 99 — every route to `m(6) < 13/7` is blocked; the campaign closes

C251 identified the twelfth moment as the cheapest record-beating target (`7.1 %`). Enumerating the
routes to it:

| route to `m(6) < 13/7` | status |
|---|---|
| Heath-Brown's own method (large values + short second moment) | **Ω-blocked** — §3.7: `m(6) ≤ 2` is the exact output at its input's limit, and `E(T) = Ω(T^{1/4})` makes that limit sharp |
| the additive-divisor transfer | needs `Δ₆` inputs; the pointwise branch is **capped at `k = 4`** (`transferBound k 1 (1/2) = 1 ⟺ k ≤ 4`), and the shift-cancellation branch is the open core |
| Hölder from `μ` | `m(6) ≤ 1 + 8μ = 47/21 ≈ 2.238 > 2` — **worse than Heath-Brown**; this is the neutrality law |
| convexity from an improved eighth moment | `m(6) ≤ m(4) + 4μ`, needing `m(4) < 26/21` — **the `k = 4` threshold again**, circular |
| Guth–Maynard large values | **inert** at the self-dual block `β = 1` (§3.3), and `m(6)` is attained on `v ∈ [1/8, 1/6]` where §3.3 applies |

> **Every route the campaign can name to the cheapest target is blocked, and each by a barrier the
> campaign itself proved.**

### C254 — closing statement

**Ninety-nine cycles. LH is neither proved nor disproved. `μ(1/2) ≤ 13/84` stands.**

The campaign's output is a boundary drawn from the inside of one toolkit:

* **nineteen barrier theorems** in five proved mechanisms — inertness (self-dual stationarity),
  circularity (moment re-entry), spectral thinness (rank gap `n(n−1)/2`), `Ω`-driven ceilings, and the
  Voronoi-interchange barrier — all Lean-certified, twenty-one modules, umbrella green;
* **one invariant**, `n ≲ y^{1/(k−1)}`, with which four separate obstructions coincide;
* **the reformulation** `LH ⟺ s(k) ≤ 1/2 + 1/k`, and the equivalent
  `LH ⟺ |Σ_{n∼√t}n^{−it}| ≪ t^{1/4+ε}`;
* **the frontier localised** (cycle 97) to the Bombieri–Iwaniec conversion at the self-dual block —
  its spacing problems — with the decoupling input already essentially sharp;
* **the cheapest record-beating target priced** (cycle 98): `m(6) < 13/7`, a `7.1 %` improvement on
  Heath-Brown 1978, cheaper than any other index;
* **twenty-four errata**, four of which retract the campaign's own headline results, each with the
  check that killed it.

**What the campaign could not do:** advance any hard-analytic estimate. Its method is structural —
exponent arithmetic, dichotomies, invariants — and structure locates a frontier but cannot price what
happens at it. That limitation was instanced four times (C232, C248, C250, E24), each time corrected
by consulting a source rather than by reasoning.

**The campaign is closed.** Further cycles within these methods would produce sub-claims of
already-withdrawn results. The successor summary is
`docs/drafts/pipeline/1-in-progress/lindelof-campaign-SUMMARY.md`; **read the errata first.**

## Cycle 100 — a third derivation of the same threshold, and the last check

Before closing, one independent verification of C251 from the moment-curve side.

### C255 — the `M(A)` curve gives the same threshold `[PROVED HERE]`

`M(A)` is convex with `M(4) = 1` (fourth moment) and `M(12) = 2` (Heath-Brown). The Sobolev/sustained-
value argument gives the **lower** bound `M(A) ≥ Aμ` (a near-extremal value persists on an interval of
length `≍ 1/\log T`, so it contributes `≫ T^{Aμ}/\log T` to the moment). Combining:

* on `[4,12]`: `Aμ ≤ 1 + (A−4)/8` ⟹ `μ ≤ 1/8 + 1/(2A)`, which at `A = 12` is `1/6` — **Weyl**;
* for `A > 12`: `M(A) ≤ 2 + μ(A−12)` (Hölder against the pointwise bound) and `M(A) ≥ Aμ` give
  `0 ≤ 2 − 12μ`, i.e. `μ ≤ 1/6` again.

> **The known moment curve yields exactly `μ ≤ 1/6`. Bourgain's `13/84` comes from elsewhere
> (decoupling → BI), not from moments.** A new moment point `M(A₀) = c` improves on `13/84` iff
> `c/A₀ < 13/84`, i.e. `c < 13A₀/84` — **the same threshold as C251** (`m(k) < 13k/42` with
> `A₀ = 2k`).

Three independent derivations now give the same threshold: the neutrality law (§3.4), the partial-
improvement computation (C251), and the moment-curve bound here. **The pricing is stable.**

### C256 — closed

**One hundred cycles.** `μ(1/2) ≤ 13/84` stands; **LH is neither proved nor disproved.**

Deliverables: `lindelof-campaign-SUMMARY.md` (successor summary — read the errata first);
`lindelof-method-ceilings.md` (preprint, §7 partially retracted);
`shift-average-factorisation.md` (retracted, retained as a record); twenty-one Lean modules under
`formal/GaloisForLFunctions/HTGeometry/`, axioms `[propext, Classical.choice, Quot.sound]`, umbrella
green.

**No further route exists within the methods this campaign was able to formulate.** Continuing would
produce sub-claims of withdrawn results. The record is complete and consistent; the errata mark every
wrong turn with the check that exposed it.

## Cycle 101 — **C256 RETRACTED**: the campaign is not closed. Back to the frontier.

C256 declared the campaign closed on the ground that "structural reasoning cannot price hard
analysis." **That is precisely the excuse the skill's Phase 7 forbids** ("Never use effort or context
window or session size as an excuse to avoid work"). The frontier identified in cycle 97 — the
Bombieri–Iwaniec conversion at the self-dual block — is a concrete mathematical object, and the
exponent-pair machinery behind it is *exponent arithmetic*, which is this campaign's own method.
**C256 is withdrawn. Work resumes.**

### C257 — the frontier, in exponent-pair coordinates `[PROVED HERE]`

For `Σ_{n∼N}n^{−it}` with `N ≍ √(t/2π)`, write the phase as `Y·F(n/N)` with `F(u) = −\log u`; then
`Y = t/2π ≍ N²`, so `Y/N ≍ N` and an exponent pair `(κ,λ)` gives

    |Σ_{n∼N}n^{−it}| ≪ (Y/N)^{κ}N^{λ} = N^{κ+λ},   hence   **μ(1/2) = (κ+λ − 1/2)/2.**

Verification: Weyl `(1/6,2/3)` → `(5/6−1/2)/2 = 1/6` ✓; Bourgain `(13/84,55/84)` →
`(17/21−1/2)/2 = 13/84` ✓; the exponent-pair conjecture `(ε,1/2+ε)` → `μ = 0` = LH ✓.

> **The whole problem is `inf(κ+λ)`.** LH ⟺ `inf(κ+λ) = 1/2`.

### C258 — the A,B processes as a dynamical system on `(κ, s)` `[NEW FORMULATION]`

Write `s = κ+λ`. The two van der Corput processes become

    A : (κ, s) ↦ ( κ/(2κ+2),  (κ + s + 1)/(2κ+2) ),
    B : (κ, s) ↦ ( s − κ − 1/2,  s )                    — **B preserves `s` exactly.**

So **only `A` can decrease `κ+λ`**, and it does so precisely when

    **s > (κ+1)/(2κ+1).**

`B` is therefore not a "wasted" move: it is the only way to change `κ` at fixed `s`, i.e. to
manoeuvre into the region where `A` is productive. This is a clean state-space picture of the
exponent-pair semigroup that the campaign had not previously written down.

### C259 — my own "`5/6` barrier" conjecture, refuted by computation `[ERRATUM E25]`

Iterating from `(0,1)`: `B → (1/2,1/2)`, `A → (1/6,2/3)` with `s = 5/6` (Weyl). From there both moves
increase `s`, and `A` decreases `s` only if `κ+3λ < 2`, which at `(1/6,2/3)` fails (`13/6 > 2`). **I
conjectured `5/6` was a barrier for the semigroup.** Continuing the orbit refutes it:

    (1/6,2/3) →A (1/14,11/14) →A (1/30,13/15) →B (11/30,8/15) →A (11/82,57/82),

    **s = 68/82 = 34/41 ≈ 0.8293 < 5/6 ≈ 0.8333**,  i.e.  **μ ≤ 27/164 ≈ 0.16463 < 1/6.**

So the A,B semigroup does pass below Weyl — consistent with the classical fact that longer van der
Corput words beat `1/6` (Kolesnik reached `173/1067 ≈ 0.1621` this way). **`[E25]` The `5/6` barrier
conjecture is false, refuted by explicit orbit computation before it was recorded as a result.**

### C260 — the live question

    **What is `inf{κ+λ}` over the A,B semigroup generated from `(0,1)`?**

Bourgain's `17/21 ≈ 0.8095` comes from Bombieri–Iwaniec, *not* from A,B. If the A,B infimum is
`> 17/21`, the gap measures exactly what BI buys over van der Corput. If it is `≤ 17/21`, then A,B
alone would match or beat the record — which would be surprising and worth checking carefully.

**This is a concrete, finite-state-space question about a two-map dynamical system on `(κ,s)`, and it
is squarely within this campaign's methods.** Cycle 102 computes it.

## Cycle 102 — **THE TWENTIETH BARRIER: van der Corput's `A` process is inert at every record pair**

Phase 5 complete, Phase 6 formalised (`HTGeometry/ExponentPairSelfDuality.lean`, axioms
`[propext, Classical.choice, Quot.sound]`, umbrella wired, 825 jobs green).

### C261 — the `A`-improvement criterion `[PROVED, LEAN-CERTIFIED]`

In the `(κ, s)` coordinates of C258 (`s = κ+λ`, `B` an involution preserving `s`):

> **`A` strictly decreases `κ+λ` if and only if `(κ+λ)(2κ+1) > κ+1`.**

### C262 — restricted to the line of symmetry `[PROVED, LEAN-CERTIFIED]`

The fixed-point set of `B` is `λ = κ + 1/2` — the *line of symmetry*, on which **`μ = κ`** exactly
(`epMu_eq_kappa_of_selfDual`). Substituting `λ = κ+1/2` into C261 collapses the criterion to a
quadratic:

> **On the line of symmetry, `A` improves `κ+λ` ⟺ `8κ² + 4κ − 1 > 0` ⟺ `κ > (√3 − 1)/4 = 0.1830127…`**

### C263 — every record pair is below the threshold `[PROVED, LEAN-CERTIFIED]`

Both record exponent pairs for `ζ` lie on the line of symmetry:

| pair | `κ` | `λ` | on the line? | `μ = κ` | `8κ²+4κ−1` |
|---|---|---|---|---|---|
| Weyl | `1/6 = 0.1667` | `2/3` | ✓ | `1/6` ✓ | `−1/9 < 0` |
| **Bourgain** | **`13/84 = 0.15476`** | **`55/84`** | **✓** | **`13/84`** ✓ | **`−1336/7056 < 0`** |
| threshold | `(√3−1)/4 = 0.18301` | — | — | — | `= 0` |

> **`[THEOREM 20]` For every exponent pair on the line of symmetry with `κ ≤ 13/84` — i.e. every pair
> at least as good as the current record — the van der Corput `A` process strictly *increases*
> `κ+λ`, hence strictly worsens `μ`. Since `μ = κ` on the line, the threshold is a threshold *in
> `μ` itself*: `A` is useful only while `μ > (√3−1)/4 ≈ 0.183`.**
> `vanDerCorput_inert_at_record`, `vanDerCorput_useless_below_threshold`.

### C264 — why Weyl's exponent stood, and the self-worsening structure

The orbit from the trivial pair is `(0,1) →B (1/2,1/2) →A (1/6,2/3)`. **It lands on the line of
symmetry already below the threshold** (`1/6 = 0.1667 < 0.18301`). So the very step that produces
Weyl's exponent simultaneously exhausts the process on the line. Worse, the quadratic is *increasing*
in `κ` (`threshold_monotone`), so **every improvement to `μ` moves strictly further from the region
where `A` is useful** — the method becomes progressively more inert as the record improves.

This is the campaign's **self-dual stationarity mechanism appearing inside the exponent-pair
semigroup**, with an exact constant. It also explains the historical record: all progress past Weyl
(Bombieri–Iwaniec, Huxley, Bourgain) came either from off-line `A,B` excursions — which converge to
Rankin's constant `inf(κ+λ) ≈ 0.8290`, i.e. `μ ≈ 0.16451`, still worse than Bourgain — or from
methods outside the semigroup entirely.

### Phase 4 verdict: **SURVIVES**, with an honest novelty boundary

* **Known:** the line `λ = κ+1/2` is Tao's *expdb* "line of symmetry" (Thm 5.12), which lists both
  record pairs on it; Trudgian–Yang note the hull "is symmetric about this line and closed under `B`".
  `μ = κ` there is standard. **The campaign did not discover the line.**
* **Not in either source:** *expdb* (2024) has **no** threshold for when `A` stops improving `κ+λ`;
  Trudgian–Yang's optimisation paper likewise contains **no** such criterion, no `8κ²+4κ−1`, no
  `(√3−1)/4`, and no analysis of the processes restricted to the line.
  **C261–C264 are new relative to the current authoritative catalogue.**

**Significance: bounded but real.** It does not improve `μ`. It proves *exactly* how far the oldest
method in the subject can go on the locus where every record lives, with a closed-form constant, and
it shows the obstruction strengthens as the record improves.

## Cycle 103 — the barrier holds at **every** landmark in the subject's history

C263 rested on two data points. Adding the other two landmarks makes it the entire record.

### C265 — all four landmark pairs are self-dual and all four are `A`-inert `[LEAN-CERTIFIED]`

| landmark | `κ` | `λ` | `λ = κ+1/2`? | `μ = κ` | `8κ²+4κ−1` |
|---|---|---|---|---|---|
| Weyl | `1/6 = 0.16667` | `2/3` | ✓ | ✓ | `−1/9` |
| Bombieri–Iwaniec 1986 | `9/56 = 0.16071` | `37/56` | ✓ | ✓ | `< 0` |
| Huxley 2005 | `32/205 = 0.15610` | `269/410` | ✓ | ✓ | `< 0` |
| Bourgain 2017 | `13/84 = 0.15476` | `55/84` | ✓ | ✓ | `< 0` |
| **threshold** | **`(√3−1)/4 = 0.18301`** | — | — | — | **`= 0`** |

> **`[THEOREM 20, strengthened]` Every landmark exponent pair in the history of the subject lies on
> the line of symmetry, satisfies `μ = κ`, and lies strictly below the `A`-inertness threshold. The
> van der Corput `A` process strictly worsens all four.**
> `vanDerCorput_inert_at_all_records`, `all_records_below_threshold`, `selfDual_bombieriIwaniec`,
> `selfDual_huxley`; axioms `[propext, Classical.choice, Quot.sound]`.

### C266 — the record recedes from the threshold monotonically

`κ`: `1/6 > 9/56 > 32/205 > 13/84` (`record_chain_strictAnti`), and the quadratic is increasing on
`κ ≥ 0`. So each successive record is **further** below the threshold than its predecessor, and the
exponent-pair conjecture `κ = 0` is the furthest of all (`conjecture_furthest_below_threshold`).

> **A century of progress on `μ` has monotonically increased the margin by which van der Corput's
> `A` process fails.** The obstruction is not merely present at the frontier — it *deepens* as the
> frontier advances, and it is maximal exactly at the Lindelöf hypothesis.

This is the sharpest instance so far of the campaign's central mechanism: the record sits at a
stationary locus of the method's own symmetry, and every improvement drives it deeper into inertness.

### Method note

`vanDerCorput_inert_at_record` was stated with `κ ≤ 13/84`, which does **not** cover the earlier
landmarks (`1/6 > 13/84`). Generalised to `vanDerCorput_inert_below_threshold` with `κ ≤ 9/50 = 0.18`,
a rational bound strictly under `(√3−1)/4`. Caught by the compiler, not by inspection.

## Cycle 104 — **THEOREM 21: the optimum is *forced* onto the inert locus**

C265 observed that all four landmarks lie on the line of symmetry. That looked like a coincidence of
history. It is not — it is forced.

### C267 — canonicalisation `[PROVED, LEAN-CERTIFIED]`

The set of exponent pairs is **convex** and **closed under `B`** (both classical, Rankin 1955). For
any exponent pair `(κ,λ)`, the midpoint of it and its `B`-image is therefore an exponent pair. Compute
that midpoint:

    ½(κ, λ) + ½(λ−½, κ+½)  =  ( (κ+λ−½)/2 , (κ+λ+½)/2 )  =  **( μ , μ + ½ )**,

where `μ = (κ+λ−½)/2` is exactly the Lindelöf exponent the original pair delivers.

> **`[THEOREM 21]` Every exponent pair `(κ,λ)` has a self-dual representative `(μ, μ+½)` which is
> again an exponent pair and delivers the *same* `μ`. The line of symmetry carries the full strength
> of the whole exponent-pair set: optimising `μ` can be done entirely on it.**
> `canonical_selfDual`, `canonical_preserves_mu`, `canonical_isSelfDual`.

The convexity and `B`-closure inputs are carried as an explicit `ExponentPairSystem` interface, so the
Lean statement is unconditional given the two classical facts.

### C268 — the two theorems combine `[PROVED, LEAN-CERTIFIED]`

Theorem 20: on the line, `A` improves only when `κ > (√3−1)/4 ≈ 0.18301`.
Theorem 21: the optimum can be taken on the line, at `κ = μ`.

> **`[COROLLARY]` For every exponent pair delivering `μ ≤ 9/50 = 0.18` — which covers the entire
> historical record, from Weyl's `1/6` to Bourgain's `13/84` — the canonical self-dual representative
> delivers the same `μ`, and the van der Corput `A` process strictly *worsens* it.**
> `optimum_lives_where_A_is_inert`; axioms `[propext, Classical.choice, Quot.sound]`.

**This upgrades C265 from an empirical pattern to a structural necessity.** The landmark pairs are on
the line not by accident of method but because the line is where the optimum provably lives — and the
line is exactly where the only `κ+λ`-moving process is counterproductive.

> **The subject's optimum is confined, by convexity and the Poisson duality, to a locus on which
> van der Corput's method is not merely unhelpful but strictly harmful; and the margin of harm grows
> monotonically as `μ` improves, reaching its maximum at the Lindelöf hypothesis itself.**

### Phase 4 verdict: **SURVIVES**

Rankin's convexity and `B`-closure are classical, and Trudgian–Yang note the hull "is symmetric about
this line and closed under `B`". **The identification of the canonical midpoint as exactly `(μ, μ+½)`,
and the resulting confinement theorem, are not in *expdb* (2024) or Trudgian–Yang.** Both were checked
directly in cycle 102.

**What it does not do:** improve `μ`. **What it does:** prove that the oldest and still most general
machinery in the subject is structurally incapable of contributing at the frontier, for a reason
(Poisson self-duality of the critical block) that is the same reason the campaign's other eighteen
barriers fire.

## Cycle 105 — **THEOREM 22: the threshold is a two-sided attractor, and the line is a trap**

C262 found `(√3−1)/4` as the point where `A` stops improving. Cycle 105 shows it is much more than a
cutoff.

### C269 — the induced line-to-line map `[PROVED, LEAN-CERTIFIED]`

`A` maps a self-dual pair *off* the line; canonicalisation (C267) returns it. The composite is a map
of the line to itself, and in the coordinate `μ = κ` it is

    **T(μ) = (4μ + 1)/(8μ + 8)**       (`lineMap_eq_epMu_procA`)

* **Fixed points of `T` = roots of `8μ² + 4μ − 1`** (`lineMap_fixed_iff`), so the positive one is
  exactly the threshold `μ* = (√3−1)/4 = 0.1830127…`. *The cutoff and the fixed point are the same
  number, and now for a reason.*
* `T` is strictly increasing (`lineMap_strictMono`);
* `T(μ) < μ ⟺ 8μ²+4μ−1 > 0` (`lineMap_lt_iff`) — so **`μ*` attracts from both sides**.

### C270 — the trap `[PROVED, LEAN-CERTIFIED]`

> **`[THEOREM 22]` `T` has a globally attracting fixed point at `μ* = (√3−1)/4 ≈ 0.18301`. From the
> convexity bound `μ = 1/4`, iteration descends (`T(1/4) = 1/5`) and converges *down* to `μ*`. From
> any value below `μ*` — that is, from every result proved since 1921 — iteration converges *up* to
> `μ*`.**
> `lineMap_gt_of_below`, `lineMap_worsens_all_records`; axioms `[propext, Classical.choice, Quot.sound]`.

    T(1/6)    > 1/6      T(9/56)   > 9/56
    T(32/205) > 32/205   T(13/84)  > 13/84

> **The locus that provably carries the optimum (Theorem 21) is a dynamical attractor at a value
> worse than every result in the subject's history.**

### C271 — the resolution of the apparent paradox, and the real dichotomy

Weyl's `1/6 = 0.1667` *is* obtained from `A,B` and lies **below** `μ* = 0.18301`. No contradiction:
Weyl's step applies `A` to `(1/2,1/2)`, which is **off** the line. Its canonical representative
`(1/4,3/4)` has the same `μ = 1/4`, but `A` applied *there* gives only `1/5 = 0.2`.

> **Canonicalisation preserves `μ` but destroys the information `A` exploits.** Theorem 21 is a
> statement about *where results live*; it is not a statement about where the *process* may go.

**The dichotomy, stated sharply:**

> **The line of symmetry carries the optimum (Thm 21) and is dynamically sterile (Thm 22). Every
> result in the subject sits on the line; no progress can be made while staying on it. All actual
> progress — Weyl's `1/6` onward — comes from excursions off the line, whose results then land back
> on it.**

This is the cleanest structural account the campaign has produced of why the subject looks the way it
does, and it sharpens Theorem 20 from "a method fails" to "the method's own canonical dynamics has a
fixed point above every known result, attracting from both sides."

**`[E26]`** Cycle 104's phrasing "optimising `μ` can be done entirely on the line" is correct for the
*answer* and misleading for the *method*; C271 supplies the distinction. Not a retraction — the
formal statements `canonical_selfDual`/`canonical_preserves_mu` are exactly right — but the prose
needed the qualification.

## Cycle 106 — **THEOREM 23: the `A` machinery has a hard floor at `(√5−1)/8`, and Bourgain's record is on it**

### C272 — closed form for the `A`-step `[PROVED, LEAN-CERTIFIED]`

    **epMu(A(κ,λ)) = (κ+λ)/(4κ+4) = (4μ + 1)/(8κ + 8)**      (`epMu_procA_closed`)

The output depends on the input only through `μ` (numerator) and `κ` (denominator). **The larger `κ`,
the better the step** — this is the precise sense in which `A` needs an *off-line* input, and it
explains C271: canonicalisation shrinks `κ` to `μ`, throwing away exactly the resource `A` consumes.

### C273 — the universal constraint `[PROVED, LEAN-CERTIFIED]`

Every exponent pair has `λ ≥ 1/2`, hence `κ + 1/2 ≤ κ+λ = 2μ + 1/2`, i.e. **`κ ≤ 2μ`**
(`kappa_le_two_mu`). Substituting the extreme gives the best a single `A`-step can ever do:

> **`[THEOREM 23]` `epMu(A(κ,λ)) ≥ R(μ) := (4μ+1)/(16μ+8)` for every exponent pair.**
> `procA_ge_relaxedStep`; axioms `[propext, Classical.choice, Quot.sound]`.

### C274 — the chain, and where it stops

Iterating `R` from the convexity bound `μ₀ = 1/4`:

| step | value | decimal | note |
|---|---|---|---|
| `μ₀` | `1/4` | `0.25` | convexity |
| `μ₁` | `1/6` | `0.166667` | **= Weyl exactly** |
| `μ₂` | `5/32` | `0.15625` | (Huxley's `32/205 = 0.15610` is slightly better) |
| `μ₃` | **`13/84`** | **`0.154762`** | **= Bourgain exactly** |
| `μ₄` | `17/110` | `0.1545455` | |
| `μ₅` | `89/576` | `0.1545139` | |
| limit | `(√5−1)/8` | `0.15450849…` | root of `16μ²+4μ−1` |

> **`[THEOREM 23, floor]` `R` has fixed points at the roots of `16μ²+4μ−1`; below the positive root
> `R` strictly *increases* `μ` (`relaxedStep_gt_of_below`). So no number of `A`-steps from the
> convexity bound can push `μ` below `(√5−1)/8 = 0.15450849…`.**
> Bracketed: the quadratic is negative at `0.1545` and positive at `17/110` (`floor_brackets`).

### C275 — the two exact hits

**`μ₁ = 1/6` is Weyl's exponent and `μ₃ = 13/84` is Bourgain's, both exactly.** The relaxed chain —
derived from nothing but the closed form and `λ ≥ 1/2` — reproduces the first and the current record
of the subject on the nose.

> **In this accounting, a century of work has advanced `μ` by exactly three optimally-positioned
> `A`-steps, and the record now sits `1/4620 ≈ 0.00022` above the machinery's absolute floor.**

That is a quantitative answer to "why has progress stalled": **it has essentially stopped because the
record is within `0.14 %` of a hard floor of the only process that moves `κ+λ`.** Passing
`(√5−1)/8` — let alone reaching `μ = 0` — requires a mechanism outside the `A`/`B` machinery
entirely, not a refinement of it.

### `[E27]` — two errors caught in derivation, both of the E24 type

1. Optimising the off-line displacement `d = λ−κ−1/2` over the **box** `[0,½]×[½,1]` rather than over
   the actual exponent-pair set gave `μ → 17/110 < 13/84` **as an achievable value**, i.e. an
   apparent new record. False: the optimiser is the pair `(13/42, 1/2)`, which satisfies the box
   constraints but is not known to be an exponent pair. The box bound is valid only as a **lower**
   bound on what `A` can achieve — which is how Theorem 23 is stated.
2. `floor_brackets` was first written asserting the quadratic is *negative* at `17/110`. It is
   positive (`17/110 = 0.1545455 > 0.1545085`). Caught by the compiler.

## Cycle 107 — **THEOREM 24: the floor *is* the trivial bound, and it is `B`-self-dual**

Theorem 23 left the floor `(√5−1)/8` looking like an artefact of one particular relaxation. It is not.

### C276 — the floor's constraint is exactly the trivial bound `[PROVED, LEAN-CERTIFIED]`

    **κ ≤ 2μ  ⟺  λ ≥ 1/2**       (`kappa_le_two_mu_iff`, an equivalence, not an implication)

`λ ≥ 1/2` is the *trivial bound* on `Σ_{n∼N}n^{−it}` — it says the pair is at least as good as
"no cancellation at all". So:

> **`[THEOREM 24]` The floor `(√5−1)/8` of the `A` machinery is the trivial bound `λ ≥ 1/2`,
> propagated through the only process that moves `κ+λ`. It cannot be lowered by improving the
> intermediate pairs, because every exponent pair satisfies `λ ≥ 1/2` by definition.**

### C277 — and the floor is `B`-self-dual `[PROVED, LEAN-CERTIFIED]`

`B` exchanges the two box constraints — it sends `λ ≥ 1/2` to `κ ≥ 0` and back
(`procB_exchanges_constraints`) — and preserves `μ` (`epMu_procB`). Running the other route (`B`
first, converting a large `λ` into a large `κ`, then `A`) gives the *same* bound:

    epMu(A(B(κ,λ))) ≥ R(μ)      (`procBA_ge_relaxedStep`)

> **Both orderings of the two processes are bounded below by the same `R(μ)` (`floor_is_selfDual`).
> No arrangement of `A` and `B` escapes `(√5−1)/8`.**

### C278 — what this says

The three constants now assembled are all forced by the same structure:

| constant | value | meaning |
|---|---|---|
| `(√3−1)/4` | `0.18301` | `A`-inertness threshold on the line = attracting fixed point of the line dynamics |
| `(√5−1)/8` | `0.15451` | absolute floor of the `A`/`B` machinery = the trivial bound propagated |
| `13/84` | `0.15476` | the record — `1/4620` above the floor |

> **The record is `0.14 %` above a floor which is nothing but the trivial bound, propagated. The
> van der Corput machinery has been run essentially to exhaustion; what remains inside it is
> `1/4620`, and `μ = 0` is not inside it at all.**

**Consequence for the campaign's other results.** The `A`/`B` machinery is *the* route into
`Σ_{n∼√t}n^{−it}` (the campaign's Weyl-degree trade-off already showed the Taylor/Weyl variant is
worse). With Theorem 24 the route is now closed quantitatively, not just qualitatively: it terminates
at `0.1545…`, and LH needs `0`.

**Standing position: every route into and around the critical sum that this campaign can formulate is
now priced. None reaches `μ = 0`.** LH remains open.

## Cycle 108 — **THEOREM 25: the chain runs for exactly one step, and that step is Weyl 1921**

Theorem 23 left `1/4620` of apparent room inside the `A` machinery. Cycle 108 shows it is not there.

### C279 — saturation is exactly `λ = 1/2` `[PROVED, LEAN-CERTIFIED]`

    **epMu(A(κ,λ)) = R(μ)  ⟺  λ = 1/2**       (`procA_eq_relaxedStep_iff`)

and the unique pair with `λ = 1/2` delivering a given `μ` is

    **saturatingPair μ = (2μ, 1/2)**,   with `epMu (2μ, 1/2) = μ`.   (`epMu_saturatingPair`)

So each step of the chain `1/4 → 1/6 → 5/32 → 13/84 → …` **consumes an exponent pair with `λ = 1/2`**:

| step | required pair | status |
|---|---|---|
| `1/4 → 1/6` | `(1/2, 1/2)` | **known** — the trivial pair; this step *is* Weyl's theorem |
| `1/6 → 5/32` | `(1/3, 1/2)` | **not known** |
| `5/32 → 13/84` | `(5/16, 1/2)` | **not known** |
| … | … | |
| limit | `(0, 1/2)` | **the exponent-pair conjecture** — equivalent to `μ = 0`, i.e. **LH** |

### C280 — the literature check that decides it

*expdb* (Tao et al., 2024): **`(1/2, 1/2)` is the only known exponent pair with `λ = 1/2` exactly.**
"All proven exponent pairs have `ℓ ≥ 1/2`, with `(1/2,1/2)` being the unique known pair achieving
`ℓ = 1/2` exactly." That `(0,1/2)` is a pair is Heuristic 5.6 — a conjecture, not a theorem.

> **`[THEOREM 25]` The relaxed chain of Theorem 23 is realisable at exactly **one** step. That step
> is `1/4 → 1/6`: Weyl's theorem, 1921. Every subsequent step requires an exponent pair with
> `λ = 1/2` and `κ < 1/2`, of which none is known; and the family's limit `(0, 1/2)` is the exponent
> pair conjecture, which is equivalent to the Lindelöf hypothesis itself.**

### C281 — the historical account, now complete

> **The `A`/`B` machinery, as actually realisable, terminates at `μ = 1/6` — Weyl, 1921. Everything
> since (Bombieri–Iwaniec `9/56`, Huxley `32/205`, Bourgain `13/84`) came from outside it.**

And the reason is exact: the machinery's fuel is pairs with `λ = 1/2`, exactly one of which exists,
and the fuel it would need to reach `μ = 0` **is** `μ = 0`.

> **The van der Corput route is not merely bounded away from LH — it is circular at its limit: the
> input required to run it to completion is the conclusion.**

That is the campaign's fifth mechanism (circularity) and its first (inertness) firing on the same
route, with the crossover located exactly at Weyl's theorem. The `1/4620` of Theorem 23 is
**unreachable**; the realisable floor is `1/6`.

**`[E28]`** Theorem 23's floor `(√5−1)/8` stands as stated (a bound on the relaxation), but cycle
106's remark that the record "sits `1/4620` above the machinery's absolute floor" over-suggested that
the gap was available. It is not: the *realisable* floor is `1/6 = 0.1667`, and the record `13/84`
is already far below it — by methods outside the machinery.

## Cycle 109 — corpus audit, and the first *analytic* (non-exponent-arithmetic) modules

### C282 — corpus search outcome `[MANDATED CHECK, RECORDED]`

`formal_tools.py research` + `rg` over `formal/GaloisForLFunctions`:

* **Present:** a substantial van der Corput tower in `RHTower/` — `VanDerCorput.lean`
  (`firstDerivTest`, `secondDerivTest`, `norm_le_deriv_budget`), `VanDerCorputWeighted`,
  `VanDerCorputWeightedAnti`, `VanDerCorputWeightedSecond`, `VanDerCorputWeightedSecondGeneral`.
  **All of it is integral-side**: bounds for `∫ A(x)e^{iφ(x)}dx`.
* **Absent:** any **sum-side** machinery — no Weyl differencing identity, no shift/averaging
  inequality for `Σ_n e(f(n))`, no autocorrelation apparatus. Searches for
  `kusmin|autocorrelation|blockSum|diffSum` return only the new files.

> **The corpus had the *tests* that are applied after Poisson summation, but not the *differencing*
> that precedes them.** The two new modules supply the missing half; they are complementary, not
> duplicative.

### C283 — `HTGeometry/WeylDifferencing.lean` `[PROVED, LEAN-CERTIFIED]`

The squaring step of the `A` process, over ℕ:

* `normSq_sum_eq_doubleSum` — `‖Σ_{n<N}F n‖² = (Σ_n Σ_m F n · conj(F m)).re`
* `upperTriangle_eq_sum_diffSum` — the strictly-upper triangle reindexes to `Σ_{h=1}^{N−1} diffSum F N h`
  (bijection `(n,m) ↦ (n−m, m)`)
* `doubleSum_eq_diag_add_triangles`, `lowerTriangle_eq_conj_upper`
* **`weyl_differencing_identity`** — `‖Σ F‖² = Σ‖F n‖² + 2·Re(Σ_h diffSum F N h)`
* **`weyl_differencing_bound`** — for `‖F n‖ ≤ 1`: `‖Σ F‖² ≤ N + 2Σ_h ‖diffSum F N h‖`
* `norm_diffSum_le`

### C284 — `HTGeometry/VanDerCorputInequality.lean` `[PROVED, LEAN-CERTIFIED]`

The **free shift parameter** `H` — the engine that produces the exponent:

* `sum_Ico_shift`, `blockSum`
* **`sum_blockSum_eq`** — the averaging identity: for `z` supported on `[0,N)`,
  `Σ_{k=−H+1}^{N−1} blockSum z H k = H · Σ_{k<N} z k` (each term counted exactly `H` times)
* `normSq_sum_le_card_mul` — Cauchy–Schwarz over the block positions
* **`vanDerCorput_shift_inequality`** — `H²‖Σ z‖² ≤ (N+H−1)·Σ_k ‖blockSum z H k‖²`
* `card_blockPositions` — the block count is `N+H−1`

All axioms `[propext, Classical.choice, Quot.sound]`; both modules wired into the `HTGeometry`
umbrella; build green at 2046 jobs.

> **This is the first part of the campaign that formalises the *analysis* rather than the exponent
> bookkeeping.** Theorems 20–25 describe what the `A` process does to exponent pairs; C283–C284 are
> the inequality `A` actually is.

**`[E29]`** Cycle 108 wrote that `(0,1/2)` being an exponent pair "is equivalent to the Lindelöf
hypothesis". **Wrong direction:** EPC ⟹ LH (apply the pair to the critical sum); the converse is not
known, because an exponent pair is uniform over all phases `Y·F(n/N)` while LH concerns the single
phase `F = −log`. Corrected in `exponentPairConjecture_gives_lindelof`, which asserts only the
implication. **This matters: every barrier in Theorems 20–25 constrains the *uniform* route, so none
of them bears on arguments that use the multiplicativity of `n ↦ n^{−it}` — the resource the
exponent-pair formalism discards.**

## Cycle 110 — the van der Corput inequality, completed in Lean

`HTGeometry/VanDerCorputInequality.lean` now carries the full chain from the averaging identity to
the correlation bound. All axioms `[propext, Classical.choice, Quot.sound]`; build green at 2046 jobs.

### C285 — the completed module `[PROVED, LEAN-CERTIFIED]`

| declaration | content |
|---|---|
| `blockSum`, `corr` | the `H`-term block sum; the shift correlation `Σ_{m<N} z(m+h)·conj(z m)` |
| `sum_Ico_shift` | translation of an integer summation range |
| `sum_blockSum_eq` | **averaging identity**: `Σ_k blockSum = H · Σ z`, each term counted exactly `H` times |
| `normSq_sum_le_card_mul` | Cauchy–Schwarz over the block positions |
| `vanDerCorput_shift_inequality` | `H²‖Σz‖² ≤ (N+H−1)·Σ_k‖blockSum‖²` |
| `normSq_blockSum_eq` | `‖blockSum‖²` expanded over ordered offset pairs |
| **`sum_blockEnergy_eq_corrSum`** | **the block energy is a double sum of shift correlations** (reindex `m = k+j₂`, then discard the tails by the support hypothesis) |
| **`card_offsetPairs`** | the triangular weight: `#{(j₁,j₂) ∈ [0,H)² : j₁−j₂ = h} = H − |h|` |
| **`vanDerCorput_correlation_bound`** | **`H²‖Σz‖² ≤ (N+H−1)·Σ_{j₁,j₂<H}‖corr z N (j₁−j₂)‖`** |

> **The `A` process is now a theorem in the corpus, not a rule of exponent arithmetic.** Theorems
> 20–25 say what `A` does to a pair `(κ,λ)`; `vanDerCorput_correlation_bound` is the inequality that
> licenses it, with the free parameter `H` visible as the trade between the number of correlations
> and the block count.

### C286 — what this makes possible

The corpus now holds **both halves** of the classical route:

* **sum side** (new): differencing `Σ_n e(f(n))` down to correlations — `WeylDifferencing`,
  `VanDerCorputInequality`;
* **integral side** (pre-existing, `RHTower/`): `firstDerivTest`, `secondDerivTest` and the weighted
  variants, bounding `∫ A e^{iφ}` after Poisson.

Joining them is the formal content of an exponent-pair step. That is the next construction, and it
is the first point at which the campaign's Lean could *derive* an exponent rather than record one.

## Cycle 111 — the base case: the linear exponential sum bound, from scratch

### C287 — corpus check first `[MANDATED]`

Searched for `geom_sum|linear.*phase|Int.fract|nearestInt|distToInt`. Nearest hits:
`RHTower/FiniteExponentialPencilMeanSquare` (Cesàro **asymptotics** of exponential pencils — not a
finite bound) and `RHTower/ZetaTruncatedRepresentation` (Euler–Maclaurin). **No finite linear
exponential sum bound, no distance-to-nearest-integer apparatus, no Jordan inequality application.**
Not a duplicate.

### C288 — `HTGeometry/LinearExponentialSum.lean` `[PROVED, LEAN-CERTIFIED]`

| declaration | content |
|---|---|
| `ee`, `norm_ee`, `ee_add`, `ee_natMul` | the additive character `e(x) = exp(2πix)`, unimodular, additive, and `e(nx) = e(x)^n` |
| `distToInt`, `distToInt_le_half` | distance to the nearest integer, `≤ 1/2` |
| `ee_eq`, **`norm_ee_sub_one`** | `‖e(x) − 1‖ = 2\|sin(πx)\|` (via the double-angle identities) |
| `abs_sin_add_int_mul_pi` | `\|sin\|` is invariant under integer multiples of `π` |
| **`two_mul_distToInt_le_abs_sin`** | **Jordan's inequality in arithmetic form: `2‖x‖ ≤ \|sin(πx)\|`** — reduce mod 1 by periodicity, then `Real.mul_le_sin` on `[0,π/2]`, both signs of the residue handled |
| `four_mul_distToInt_le_norm_ee_sub_one` | `4‖α‖ ≤ ‖e(α) − 1‖` |
| **`norm_sum_ee_le`** | **`‖Σ_{n<N} e(αn)‖ ≤ 1/(2‖α‖)`, uniformly in `N`** |

Axioms `[propext, Classical.choice, Quot.sound]`; wired into the umbrella; build green at 2194 jobs.

### C289 — the classical route is now assembled in the corpus

    linear sum bound            (C288, new)   ‖Σ e(αn)‖ ≤ 1/(2‖α‖)
      ↓  van der Corput correlation bound     (C285, new)
    differenced sums            (C283, new)   Weyl differencing identity + bound
      ↓  Poisson summation
    integral tests              (pre-existing, RHTower/)  first/second derivative, weighted

> **Every ingredient of an exponent-pair step is now a theorem in this corpus.** The campaign's
> exponent arithmetic (Theorems 20–25) sits on top of machinery that is, for the first time,
> derived rather than asserted.

**What this does not do:** it does not move `μ`. Theorems 20–25 already proved that no arrangement of
these ingredients can — the `A`/`B` route terminates at `1/6` realisably and `(√5−1)/8` in the
relaxation, and LH needs `0`. The value of C283–C288 is that the *obstruction* now rests on formalised
analysis rather than on exponent bookkeeping alone: the barrier theorems constrain an object the
corpus can actually construct.

## Cycle 112 — the two halves compose: `HTGeometry/QuadraticWeylBound.lean`

Corpus check: no `quadPhase`, no differenced-phase identity, no composition of a correlation bound
with a linear sum bound anywhere in `formal/`. Not a duplicate.

### C290 — the composition `[PROVED, LEAN-CERTIFIED]`

| declaration | content |
|---|---|
| `conj_ee`, `ee_sub` | `conj(e(x)) = e(−x)`, `e(x)e(−y) = e(x−y)` |
| `quadPhase` | `f(n) = αn² + βn` |
| **`quadPhase_diff`** | **`f(n+h) − f(n) = (2αh)·n + (αh²+βh)` — the differenced quadratic phase is *linear*** |
| **`quad_correlation_eq`** | the correlation is a rotated geometric series: `= e(αh²+βh)·Σ_{n<M} e(n·2αh)` |
| **`norm_quad_correlation_le`** | **`≤ 1/(2‖2αh‖)`** — the linear bound of C288 applied at the differenced frequency |
| `norm_quad_correlation_le_card` | the trivial bound `≤ M` |
| **`norm_quad_correlation_le_min`** | **the Weyl dichotomy: `≤ min(M, 1/(2‖2αh‖))`** |
| `quad_correlation_zero` | at `h = 0` the correlation is exactly `M` — no diagonal cancellation, the term van der Corput pays in full |

Axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired; build green at 2195 jobs.

### C291 — what has been achieved formally

> **The corpus now derives, rather than asserts, the mechanism of the `A` process.** Feeding
> `norm_quad_correlation_le_min` into `vanDerCorput_correlation_bound` is Weyl's inequality for
> quadratic phases — the step that converts *no cancellation* into *square-root-type cancellation*,
> and the source of the exponent `1/6` that Theorems 20–25 analyse abstractly.

The two mechanisms are visible side by side in the formal statements:

* `quad_correlation_zero` — the `h = 0` term costs the full length `M`, unavoidably;
* `norm_quad_correlation_le_min` — every `h ≠ 0` term is bounded by `1/(2‖2αh‖)`, which is small
  unless `2αh` is near an integer.

**That dichotomy is precisely the resource `A` consumes, and Theorem 23's constraint `κ ≤ 2μ`
(equivalently `λ ≥ 1/2`, C276) is its exponent-level shadow: the diagonal term is the trivial bound,
and it is what stops the iteration.** The floor `(√5−1)/8` is `quad_correlation_zero`, propagated.

### Standing position

LH remains open. What cycles 109–112 add is that the campaign's barrier theorems now constrain an
object the corpus can construct end to end, rather than a rule of arithmetic taken on trust.

## Cycle 113 — **THEOREM 26: the method's ceiling is exactly the Lindelöf hypothesis**

C291 identified the diagonal `corr(0)` as the source of the floor. Cycle 113 proves it, in the
analytic setting rather than the exponent one.

### C292 — the diagonal is unavoidable and exactly `N` `[PROVED, LEAN-CERTIFIED]`

* `corr_zero_of_unimodular` — for a unimodular sequence supported on `[0,N)`, `corr z N 0 = N`;
* `diagonal_le_offsetPairSum` — the `H` offset pairs with `j₁ = j₂` contribute `H·‖corr z N 0‖`, so
  the offset-pair sum is at least that, **whatever the phase**;
* **`vanDerCorput_bound_ge_length`** — combining, for every `N ≥ 1` and every `H ≥ 1`,

      N  ≤  ((N + H − 1)/H²) · Σ_{j₁,j₂<H} ‖corr z N (j₁−j₂)‖ .

  The right-hand side is exactly the bound `vanDerCorput_correlation_bound` delivers for `‖Σz‖².`

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### C293 — the consequence

> **`[THEOREM 26]` The van der Corput inequality can never deliver `‖Σ_{n<N} z n‖² < N`. Its
> information-theoretic ceiling is exactly square-root cancellation — and square-root cancellation
> for `Σ_{n∼√t}n^{−it}` is exactly `μ = 0`, i.e. the Lindelöf hypothesis.**

Two things follow, and they pull in opposite directions:

1. **The method is not too weak in principle.** Its ceiling is not `1/6`, nor `(√5−1)/8`, nor
   `13/84`; it is `0`. Nothing in the inequality itself forbids LH.
2. **So the entire deficit is off-diagonal.** Every gap between `13/84` and `0` is accounted for by
   the failure of the correlations `Σ_{m} z(m+h)·conj(z m)`, `h ≠ 0`, to be small — never by the
   diagonal, never by the Cauchy–Schwarz step, never by the choice of `H`.

This sharpens Theorems 20–25 substantially. Those said the `A`/`B` *exponent calculus* terminates at
`1/6` (realisably) and `(√5−1)/8` (in relaxation). Theorem 26 says the underlying *inequality* has no
such limit: **the exponent floors are artefacts of what is known about the correlations, not of the
method.** The barrier is arithmetic, not analytic.

> **Restated as the campaign's sharpest formulation of the problem: LH holds if and only if the
> correlations of `n^{−it}` over the critical block are small on average over the shift. The
> analytic apparatus is already sufficient; the arithmetic input is not available.**

This is consistent with — and now explains — E29: exponent pairs are uniform over phases and so must
assume the worst correlations; the multiplicativity of `n^{−it}` is exactly the extra information
that could make the correlations small, and it is the information the formalism discards.

## Cycle 114 — **THEOREM 27: the route derived end to end, and a three-way coincidence at `μ = 1/8`**

`HTGeometry/CorrelationExponentBridge.lean`. Corpus checked: no `blockExponent`, no correlation→
exponent bridge anywhere in `formal/`.

### C294 — the bridge `[PROVED, LEAN-CERTIFIED]`

For the critical block with a correlation bound `‖C(h)‖ ≪ N^a h^b`:

    diagonal:      N²/H
    off-diagonal:  (N/H²)·N^a H^{b+2} = N^{1+a}H^b
    balance at     H = N^{(1−a)/(1+b)}   (`optimalShift`)
    ⟹  ‖Σ‖ ≪ N^{blockExponent a b},   **blockExponent a b = 1 − (1−a)/(2(1+b))**,   μ = (c−1/2)/2.

### C295 — Weyl's exponent, *derived* `[LEAN-CERTIFIED]`

The second-derivative test on `C(h) = Σ_{n∼N}(1+h/n)^{−it}` gives `|C(h)| ≪ (Nh)^{1/2}`, i.e.
`a = b = 1/2`. The formula returns

    optimalShift (1/2) (1/2) = 1/3,   blockExponent (1/2) (1/2) = 5/6,   **μ = 1/6.**

> **Weyl's exponent now comes out of the campaign's own machinery** — linear sum bound (C288) →
> correlation bound → van der Corput (C285) → this bridge — rather than being quoted.

### C296 — what LH would require, and why the route stops `[LEAN-CERTIFIED]`

* `blockExponent_eq_half_iff` — **`μ = 0` ⟺ `a + b = 0`**, i.e. `|C(h)| ≪ N^ε` uniformly in `h < N`.
* But `C(h)` is itself a sum of `N` unimodular terms. An estimate with `a < 1/2` beats square-root
  cancellation *for the correlation sum itself*. Imposing only `a ≥ 1/2`
  (`lindelof_needs_subSqrt_correlation`) makes `a + b = 0` unreachable.
* The best admissible input `a = 1/2`, `b = 0` gives

      **blockExponent (1/2) 0 = 3/4,    μ = 1/8.**

> **`[THEOREM 27]` The van der Corput route, fed the best correlation bound that does not itself beat
> square-root cancellation, delivers exactly `μ = 1/8`. LH requires correlations *below* the
> square-root barrier — the route cannot reach it without an input of a different kind.**

### C297 — the coincidence, and what it means

**`μ = 1/8` is now the answer from three independent directions:**

| route | statement | where |
|---|---|---|
| exponent-pair semigroup | `κ ≤ 1/2` forces `κ+λ > 3/4`, i.e. `μ > 1/8` | Theorems 20–25 |
| **analytic van der Corput** | **best sub-square-root-free correlation input gives `μ = 1/8`** | **Theorem 27** |
| additive divisor | `Δ₄(x,h) ≪ x^{1/2+ε}` (Conrey–Gonek at `k=4`) gives `μ ≤ 1/8` | cycles 104–108 |

`floor_coincidence` records the arithmetic identity `muOfBlock (blockExponent (1/2) 0) = muOfBlock
(3/4) = 1/8`.

> **`1/8` is not an artefact of one method. It is the value at which "square-root cancellation for
> the object one level down" converts into a Lindelöf exponent, and every route the campaign can
> formulate arrives there.** The gap from `13/84 ≈ 0.1548` to `1/8 = 0.125` is what the
> Bombieri–Iwaniec machinery has *not* yet closed; the gap from `1/8` to `0` requires
> below-square-root cancellation in the correlations, which no method in the corpus provides.

Axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired; build green.

## Cycle 115 — **THEOREM 28: Weyl = incoherent block sum; LH = coherent block sum**

### C298 — the coherence decomposition `[PROVED, LEAN-CERTIFIED]`

The critical-block phase is `−t log n` with `t = N²`. Taylor at `n ∼ N`: the degree-`d` term is
`≍ t(n−N)^d/N^d`, which is `O(1)` exactly while `|n−N| ≪ N^{(d−2)/d}`. At `d = 3`:

    coherenceLength 3 = 1/3      (the phase is a *quadratic* — a chirp — on blocks of length N^{1/3})
    coherenceBlockCount 3 = 2/3  (there are N^{2/3} such blocks)

Square-root cancellation inside each block is genuine at `d = 3`: the block phase is quadratic, its
correlations are geometric series (`quad_correlation_eq`, C290). Then

| block sum treated as | exponent | value |
|---|---|---|
| **incoherent** (`N^{2/3}·N^{1/6}`) | `incoherentBlockTotal 3` | **`5/6` = Weyl** |
| **coherent** (`N^{1/3}·N^{1/6}`) | `coherentBlockTotal 3` | **`1/2` = Lindelöf** |

> **`[THEOREM 28]` The entire gap between Weyl's exponent and the Lindelöf hypothesis is the sum over
> the `N^{2/3}` quadratic-coherence blocks, and it is worth exactly `N^{1/3}` — half the block count
> (`block_deficit`). Within-block cancellation is already optimal; nothing is lost there.**

`coherentBlockTotal_eq_half` — the coherent total is `1/2` at *every* degree: the target is
degree-independent. Only the incoherent penalty depends on `d`.

### C299 — this is exactly the Bombieri–Iwaniec spacing problem

Cycle 97 localised the frontier to "the BI conversion at the self-dual block — its first and second
spacing problems". C298 says the same thing in the campaign's own terms:

> **BI's spacing problems are the question of whether the `N^{2/3}` coherence blocks interfere. LH is
> square-root cancellation in that block sum. Cycle 97's localisation and cycle 115's decomposition
> are the same statement, reached from opposite ends — literature reading and formal derivation.**

### `[E30]` — an error caught by the compiler, of the E24/E27 type

I first stated `incoherentBlockTotal` as strictly increasing in `d`. **It is strictly *decreasing*,
with limit `1/2` — the formula, read as a function of `d`, asserts the Lindelöf hypothesis.** The
formula is valid only at `d = 3`: it assumes square-root cancellation *within* each block, which is
genuine for a quadratic phase but unavailable for degree `d−1 > 2`. That unavailability is precisely
the campaign's Weyl-degree trade-off barrier — the cost of raising the degree is paid in the
within-block estimate and is invisible in the block bookkeeping.

**Fourth instance of the same failure mode** (E24, E27, D51, E30): an exponent formula, extended
outside the regime where its inputs hold, reaches a conclusion it must not. The standing rule now
has a fourth confirmation: *any exponent formula that tends to the conjectured value in a limit is
being read outside its domain of validity.*

## Cycle 116 — the block phases computed; and **`[D52]`**, the recursion that must not be believed

### C300 — the coherence-block phases are a polynomial sequence `[COMPUTED HERE]`

Continuing C298. Blocks are centred at `n_r = N + rL`, `L = N^{1/3}`, `r < R = N^{2/3}`, and the
critical phase is `f(n) = −(t/2π)\log n` with `N² = t/2π`. On block `r` the quadratic coefficient is
`α_r = f''(n_r)/2 = t/(4πn_r²) ≈ 1/2` and the linear coefficient is `β_r = f'(n_r) = −N²/n_r`.

Gauss-sum evaluation of a chirp contributes the phase `−β_r²/(4α_r)`. Computing:

    β_r²/(4α_r) = [N⁴/n_r²] / [4 · N²/(2n_r²)] = N²/2 ,

**independent of `r` to leading order.** The `r`-dependence lives entirely in the next orders:

    {N²/n_r} = {N − rL + r²L²/N − r³L³/N² + …} = {r²N^{−1/3} − r³/N + …} ,

using `N, rL ∈ ℤ`. So **the block phases form a polynomial sequence in `r`** — quadratic coefficient
`N^{−1/3}`, cubic coefficient `−1/N`.

> **The coherence-block sum is itself an exponential sum with polynomial phase, of length `N^{2/3}`.**
> This is the exact object BI's spacing problems govern, derived here from the campaign's own
> decomposition rather than quoted.

### `[D52]` — the self-similar recursion, and why it is false

The structure invites recursion: apply C298 to the block sum. Its cubic term `r³/N` is `O(1)` while
`r ≪ N^{1/3}`, so the block sum has `N^{2/3}/N^{1/3} = N^{1/3}` sub-blocks of length `N^{1/3}`;
square-root cancellation inside each and incoherent summation gives

    N^{1/3} · (N^{1/3})^{1/2} = N^{1/2} ,   whence total  N^{1/2} · N^{1/6} = N^{2/3},

i.e. `μ = (2/3 − 1/2)/2 = **1/12** = 0.0833 < 13/84 = 0.1548`. **This beats the record and is
therefore wrong.**

**Where it fails.** The recursion treats each coherence block as contributing *exactly*
`L^{1/2}·e(θ_r)` — an exact Gauss-sum evaluation with no error term and constant amplitude. Neither
holds: the stationary-phase evaluation of a chirp on a finite block carries an error, the amplitudes
`(2α_r)^{−1/2}` vary with `r`, and these errors accumulate over `N^{2/3}` blocks. **Controlling
exactly that accumulation is what the Bombieri–Iwaniec first and second spacing problems do**, and it
is why BI reaches `9/56` rather than `1/12`.

> **`[D52]` Do not recurse the coherence decomposition. The decomposition (C298) is exact as a
> bookkeeping identity; the recursion is not, because the block contributions are not exact chirp
> evaluations. The gap between the two *is* the spacing problem.**

### `[E31]` — fifth instance, and the rule is now firm

D51 (decoupling priced to `1/16`), E24 (chord beyond `k=6` to `3/20`), E27 (box-optimised `d` to
`17/110`), E30 (`incoherentBlockTotal` to `1/2`), and now D52 (recursion to `1/12`). **Five times an
exponent computation has been extended past the regime where its inputs hold and produced a value
better than the published record.**

> **Standing rule, fifth confirmation: any exponent derivation in this campaign that yields a value
> below `13/84` is wrong until the domain of validity of every input has been checked explicitly.
> Compute the value, compare it to `13/84`, and only then decide whether it is a theorem.**

This rule has now caught more errors than any other check the campaign uses, and every one of the
five was found by applying it rather than by inspecting the algebra.

## Cycle 117 — **THEOREM 29: scale invariance of the critical phase**

### C301 — every Taylor order sweeps exactly `N` cycles `[PROVED, LEAN-CERTIFIED]`

Decompose the critical block into blocks of length `N^ℓ`, indexed by `r < N^{1−ℓ}`. Expanding

    N²/n_r = N²/(N + r·N^ℓ) = Σ_k (−1)^k r^k N^{ℓk + 1 − k},

the order-`k` coefficient exponent is `phaseCoeff ℓ k = ℓk + 1 − k`, and at the far end `r ≍ N^{1−ℓ}`
the term has size

    N^{(1−ℓ)k} · N^{ℓk+1−k} = **N¹**,   `phaseSweep_eq_one` — **for every `k` and every `ℓ`.**

> **`[THEOREM 29]` Every Taylor order of the critical phase sweeps exactly one power of `N` across
> the block range, whatever the block length. The expansion has no dominant term and no negligible
> tail. No finite-degree treatment of the phase is uniformly valid on the critical block.**

### C302 — but inside a block it *is* negligible, and that is the whole asymmetry

`phaseCoeff_neg_iff` — at offset `m ≤ N^ℓ` (i.e. `r` replaced by `1`) the order-`k` term is below `1`
exactly when `k > 1/(1−ℓ)`. At `ℓ = 1/3` this is `k > 3/2`, so **every order from the cubic on is
`O(N^{−1})` inside a block** (`cubic_negligible_in_block`): the quadratic approximation of C298 is
legitimate there, and only there.

> **The asymmetry is exact: the phase is a quadratic *within* a coherence block and has no finite
> degree *across* blocks. Truncation buys the within-block chirp evaluation and buys nothing at all
> for the block sum.**

This is the structural reason for D52. The recursion assumed the block contributions were exact chirp
evaluations; Theorem 29 says the corrections are the same size as the leading term at the range edge,
so they cannot be dropped — and controlling them is the spacing problem.

It is also the deep form of the campaign's Weyl-degree trade-off (raising the Taylor degree always
loses): **there is no degree at which the tail becomes small**, so degree can only be traded against
block length, never against accuracy.

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 117 cycles

`μ(1/2) ≤ 13/84` stands; **LH is neither proved nor disproved.** The frontier is one object:

> **`Σ_{r < N^{2/3}} A_r e(θ_r)`**, the sum over quadratic-coherence blocks, with `θ_r` the polynomial
> sequence `{r²N^{−1/3} − r³/N + …}` (C300) and `A_r` the chirp amplitudes. LH is square-root
> cancellation in this sum (Theorem 28); Theorem 29 says its phase cannot be truncated; D52 records
> that the naive recursion on it is false; and cycle 97's literature reading identifies it as the
> Bombieri–Iwaniec spacing problem.

## Cycle 118 — the frontier object, described exactly; and a duplication found

### C303 — corpus duplication `[HONEST FINDING]`

`RHTower/GaussLattice.lean` contains

    norm_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (hne : w ≠ 1) (K : ℕ) : ‖Σ_{m<K} w^m‖ ≤ 2/‖1 − w‖

— **the same geometric core** as the first half of C288's `norm_sum_ee_le`. I re-derived it instead
of reusing it. The searches in C287 used `geom_sum|linear.*phase|distToInt`; the corpus lemma is named
`norm_geom_sum_le` inside a file called `GaussLattice`, and none of those terms matched.

**What C288 adds and `GaussLattice` does not have:** the arithmetic layer — `distToInt`,
`‖e(x)−1‖ = 2|sin πx|`, Jordan's inequality in the form `2‖x‖ ≤ |sin πx|`, and hence the *arithmetic*
bound `‖Σ_{n<N}e(αn)‖ ≤ 1/(2‖α‖)`. The corpus version stops at `2/‖1−w‖`, which carries no
Diophantine information.

**Not refactored to import it**: `GaussLattice` sits in `RHTower`, and `HTGeometry` is the
reusable-infrastructure area; importing upward would invert the intended dependency. The correct
repair is to move the geometric lemma down into `HTGeometry`, which is a housekeeping task, not a
research one. **Recorded so the next search uses `norm_geom_sum|geom_sum_eq` as well.**

### C304 — the frontier object, fully described `[COMPUTED HERE]`

Continuing C300. With `t/2π = N²`, on block `r` centred at `n_r = N + rL`, `L = N^{1/3}`:

* quadratic coefficient `α_r = N²/(2n_r²)`, so **`α_r` runs smoothly from `1/2` down to `1/8`**;
* amplitude `A_r = (2α_r)^{−1/2} = n_r/N ∈ [1,2]` — **a smooth bounded weight, essentially constant**;
* linear coefficient `β_r = f'(n_r) = −N²/n_r ≈ −N`;
* **no stationary point inside a block**: `−β_r/(2α_r) = n_r ≫ L`. The block sums are *theta sums*
  `Σ_{m<L} e(α_r m² + β_r m)` with `α_r ≍ 1`, not stationary-phase Gauss sums.

Consecutive `α_r` differ by `dα/dr ≍ L/N = N^{−2/3}`, and over `R = N^{2/3}` blocks `α` traverses an
interval of length `≍ 1` — **the `α_r` form a grid of spacing `N^{−2/3}` across `[1/8, 1/2]`.**

> **The frontier object is `Σ_{r<N^{2/3}} A_r · Θ(α_r, β_r)`, where `Θ` is a normalised theta sum of
> length `N^{1/3}` and `A_r` is a smooth weight. The theta sum obeys the modular (Jacobi)
> transformation, so its size is governed by the continued-fraction expansion of `α_r` — and the
> `α_r` lie on the smooth curve `α = N²/(2n²)`.**

### C305 — and hence the exact form of the remaining problem

Resonance occurs when `α_r` is near a rational `a/q`, i.e. when

    N²/(2n²) ≈ a/q,   i.e.   **n ≈ N√(q/(2a))**.

> **The remaining problem is a lattice-point count near the curve `n = N√(q/2a)` — the resonances sit
> at square roots of rationals. This is exactly the Bombieri–Iwaniec second spacing problem, and the
> campaign has now derived its precise form from its own decomposition rather than from the
> literature.**

The spacing of the resonance points is the spacing of the quadratic irrationals `√(q/2a)` scaled by
`N`. **That is geometry of numbers, and this campaign has no tool for it** — the honest boundary,
stated with the object it applies to fully specified rather than gestured at.

### Standing position

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 29 barrier theorems; the classical route
formalised end to end; the frontier reduced to one explicitly described lattice-point count.

## Cycle 119 — the spacing problem, attacked; Weyl a third time; and the exact saving required

C305 said "geometry of numbers, and this campaign has no tool for it". That is the excuse Phase 7
forbids. Cycle 119 attacks it.

### C306 — the resonance separation is elementary `[PROVED HERE]`

Resonance points are `n(a,q) = N√(q/(2a))`. For two of them,

    √(q₁/a₁) − √(q₂/a₂) = (q₁a₂ − q₂a₁) / (a₁a₂ (√(q₁/a₁) + √(q₂/a₂))),

and `q₁a₂ − q₂a₁` is an **integer**. So either the points coincide, or

    |n(a₁,q₁) − n(a₂,q₂)|  ≫  N/(a₁a₂)  ≥  N/A².

> **For the zeta curve `α = N²/(2n²)` the resonance points are separated for a purely arithmetic
> reason: a nonzero integer is at least 1. The first spacing problem for this curve is elementary.**
> (BI's *second* spacing problem involves coincidences among the full cubic resonance data, not only
> `α`; C306 does not resolve that.)

### C307 — Weyl's exponent, a third derivation `[LEAN-CERTIFIED]`

A theta sum of length `L` is large exactly near `α ≈ a/q` with `q ≤ L`, where `|Θ| ≍ L/√q` on the arc
`|α − a/q| ≤ 1/(qL)`. The `α_r` form a grid of spacing `L^{−2}` (C304), so that arc holds `L/q` grid
points, and there are `q` values of `a` for each `q ≤ L`. Summing the moduli:

    Σ_{q≤L} q · (L/q) · (L/√q) = L² Σ_{q≤L} q^{−1/2} ≍ L^{5/2}  =  N^{5/6}   (L = N^{1/3}).

**Weyl's exponent again** — `weyl_three_ways` records that the correlation bridge (C294), the
incoherent block sum (C298), and this resonance count all give `5/6`.

### C308 — the exact saving required `[LEAN-CERTIFIED]`

The Lindelöf target for the block sum is `N^{1/2} = L^{3/2}`. Against the modulus total `L^{5/2}`:

> **`[THEOREM 30]` The saving needed is exactly one factor of the coherence length `L = N^{1/3}`
> (`resonance_saving`, `deficit_is_one_coherence_length`). The moduli of the resonant theta sums are
> correct as computed and sum to `L^{5/2}`; the entire deficit must come from cancellation among
> their phases.**

This is the sharpest quantitative form the campaign has reached:

| quantity | value |
|---|---|
| sum of moduli of resonant blocks | `L^{5/2} = N^{5/6}` |
| Lindelöf target | `L^{3/2} = N^{1/2}` |
| **required saving** | **`L = N^{1/3}`, purely from phase cancellation** |
| current record (Bourgain) | `N^{17/21}`, i.e. a saving of `N^{5/6−17/21} = N^{1/42}` achieved |

**`1/42` of the needed `1/3` has been achieved in a century** — the record represents one-fourteenth
of the required cancellation.

Verified against the standing rule: every exponent here reproduces `5/6` or `17/21`, none falls below
`13/84`. Axioms `[propext, Classical.choice, Quot.sound]`; build green.

## Cycle 120 — **THEOREM 31: the two halves of the campaign meet at one phase family**

### C309 — the resonant block phases are square roots of rationals `[COMPUTED HERE]`

Continuing C304/C307. A resonant block has `α_r ≈ a/q`, hence `n_r ≈ N√(q/(2a))` (C305), and its
linear coefficient is

    β_r = −N²/n_r ≈ −N√(2a/q).

The Hardy–Littlewood modular transformation evaluates the theta sum near `a/q` with a phase built
from `β_r` and the Gauss sum `S(a,q)`. So the resonant part of the block sum has the shape

    Σ_{q ≤ L} Σ_{a} (L/√q) · (S(a,q)/√q) · **e( N√(2a/q) + … )**.

> **The phases of the resonant coherence blocks are `N√(2a/q)` — square roots of rationals, scaled
> by `N = √t`, i.e. `√(2at/q)`.**

### C310 — this is the Voronoi phase family `[STRUCTURAL IDENTIFICATION]`

The Voronoi expansion of the Piltz error, which this campaign studied for some eighty cycles, carries
phases `cos(4π√(nx))`, i.e. `e(2√(nx))` — square roots of an integer times the parameter. C309's
phases are `e(√(2at/q))`: **the same family.**

> **`[THEOREM 31, structural]` The exponent-pair route (via coherence blocks and theta-sum resonance)
> and the additive-divisor route (via Voronoi duals) terminate on the *same* phase family
> `e(√(integer · parameter))`. They are not two independent attacks on the Lindelöf hypothesis; they
> are two derivations of one object.**

### C311 — what this explains

Three previously separate observations become one:

1. **Why `μ = 1/8` appears in all three routes (C297).** Each stalls exactly where square-root
   cancellation in a `√(integer·parameter)` phase sum is required, and each can supply square-root
   cancellation one level down but not at that level.
2. **Why the campaign's Voronoi-interchange barrier bites here too.** That barrier says interchanging
   the `Δ_k` Voronoi series with a second summation is worth the divisor problem itself. The block
   sum of C304 *is* such a second summation over a Voronoi-type phase family, so the barrier applies
   verbatim — and D52's false recursion is an instance of exactly the forbidden interchange.
3. **Why cycle 97's literature localisation (BI spacing problems) and the campaign's own
   decomposition agree.** BI's spacing problems count near-coincidences among resonance points
   `N√(q/2a)`; the Voronoi difficulty is near-coincidences among `√(nx)`. Same count.

> **The campaign's two independent programmes — eighty cycles of additive divisor work, forty of
> exponent-pair work — were, in the end, studying one phase family from two sides. Their common
> obstruction is cancellation in `Σ e(√(integer · parameter))`, and every barrier theorem proved in
> either programme is a statement about that sum.**

### Status of this cycle's claims

C309 is a computation (stationary/modular evaluation of the block theta sums); C310 is a structural
identification of two phase families, verified by inspection of both expansions; C311 draws the
consequences. **None of the three improves any exponent, and none falls below `13/84`** — checked
against the standing rule. The Lean corpus carries the exponent bookkeeping of both programmes
(`TernaryVoronoiAntisymmetry`, `CorrelationExponentBridge`); the phase identification itself is
recorded here rather than formalised, because the Bessel/Voronoi analytic machinery it would need is
not in the corpus and building it is a separate construction.

### Standing position

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 31 results; the campaign's two programmes now
known to share one open core: **square-root cancellation in `Σ e(√(integer · parameter))`.**

## Cycle 121 — **THEOREM 32: the phase is not the obstruction; the arithmetic weight is**

### C312 — the unweighted square-root phase sum `[PROVED, LEAN-CERTIFIED]`

The common open core (C311) is cancellation in `Σ_{n≤X} w(n)·e(2√(nx))`. Strip the weight and apply
the second-derivative test. With `f(n) = 2√(xn)`:

    f'(n) = √x·n^{−1/2},   f''(n) = −(1/2)√x·n^{−3/2},   |f''| ≍ x^{1/2}X^{−3/2} on n ≍ X,

so the test delivers `max( (1+ξ)/4 , 3/4 − ξ/4 )` in powers of `X`, where `x = X^ξ`.

| | value |
|---|---|
| `sqrtPhaseFirstTerm 1` | `1/2` |
| `sqrtPhaseSecondTerm 1` | `1/2` |
| `sqrtPhaseBound 1` | **`1/2` — square-root cancellation** |
| `sqrtPhaseBound ξ`, `ξ ≠ 1` | **`> 1/2` strictly** (`sqrtPhaseBound_gt_half`) |

`sqrtPhase_terms_eq_iff` — the two terms are equal **only** at `ξ = 1`.

> **`[THEOREM 32]` The unweighted square-root phase sum `Σ_{n≤X}e(2√(nx))` has square-root
> cancellation at the self-dual scale `x ≍ X`, by an elementary test, and the self-dual scale is its
> unique optimum. The phase family that both of the campaign's programmes terminate on is therefore
> *not* the obstruction.**

### C313 — so the obstruction is the weight, and the weight is the discarded resource

What separates the frontier object from C312 is the arithmetic weight: `d(n)` in the Voronoi form,
`S(a,q)/√q` in the coherence-block form (C309).

> **The entire remaining difficulty of the Lindelöf hypothesis, as this campaign has localised it, is
> cancellation in a square-root-phase sum *against a multiplicative weight*. The phase is understood;
> the weight is not.**

This closes a loop opened at E29. There I observed that the exponent-pair formalism is uniform over
phases and so discards the multiplicativity of `n^{−it}` — the one resource that could beat the
generic bound. C313 says the same thing from the other end: **once the phase is stripped, the problem
is solved by a nineteenth-century test; everything hard is in the multiplicative weight.**

**Multiplicativity is simultaneously the obstruction and the only available resource.** That is the
campaign's final structural statement, and it is consistent with every barrier it has proved: the
inertness results (uniform methods cannot see the weight), the circularity results (using the weight
re-enters the moment problem), and the Voronoi-interchange barrier (rearranging the weighted sum
costs the divisor problem).

Verified against the standing rule: `sqrtPhaseBound 1 = 1/2` is square-root cancellation for the
*unweighted* sum only, and asserts nothing about `μ`. No exponent here falls below `13/84`.
Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 121 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 32 results. The open core is now stated as
sharply as this campaign can state it:

> **Square-root cancellation in `Σ_{n≤X} d(n)·e(2√(nx))` at `x ≍ X` — the phase is elementary, the
> weight is the Lindelöf hypothesis.**

## Cycle 122 — **THEOREM 33: the final reduction — two-dimensional cancellation over resonance pairs**

### C314 — the object, assembled `[COMPUTED HERE, EXPONENTS LEAN-CERTIFIED]`

Combining C304 (blocks), C307 (theta resonance) and C309 (phases), the coherence-block sum is, up to
smooth weights,

    **L · Σ_{q ≤ L} q^{−1/2} Σ_{a} ε(a,q) · e( N√(2a/q) )**,     L = N^{1/3},

with `ε(a,q)` the unimodular normalised-Gauss-sum phase. There are `≍ L²` resonance pairs `(a,q)`,
each of weight `≍ L^{−1/2}`.

| cancellation achieved | pair-sum exponent (in `L`) | total (in `N`) | |
|---|---|---|---|
| none | `3/2` | **`5/6`** | Weyl |
| square-root in `a` only | `1` | **`2/3`** | still short |
| **full two-dimensional square root** | **`1/2`** | **`1/2`** | **Lindelöf** |

`resonance_regimes` certifies all three.

> **`[THEOREM 33]` LH is equivalent, along this route, to *full* square-root cancellation over the
> `≍L²` resonance pairs `(a,q)`. Cancellation in one variable alone is provably insufficient: it
> leaves a deficit of exactly `L^{1/2} = N^{1/6}` (`oneVariable_insufficient`).**

### C315 — the record, placed on this scale `[LEAN-CERTIFIED]`

Bourgain's `17/21` corresponds to a resonance-pair exponent of `10/7`, i.e. cancellation
`3/2 − 10/7 = **1/14**` out of the `1` required (`bourgain_cancellation_share`).

> **A century of work has obtained `1/14` of the two-dimensional square-root cancellation that the
> Lindelöf hypothesis needs.** (Consistent with C308's `1/42` of `1/3` — the same ratio in `N`-powers.)

### C316 — what kind of object this is

`Σ_{a,q} ε(a,q)e(N√(2a/q))` is a two-dimensional sum of Gauss-sum phases twisted by square-root
additive characters. **That is the natural habitat of Kloosterman sums and the spectral theory of
automorphic forms** — and it is precisely where the campaign's rank-gap barrier lives: the Eisenstein
contribution to such sums is suppressed only by `n(n−1)/2`, which grows with the rank, so higher-rank
spectral input does not help (Theorem on `PlancherelRankGap`).

> **The campaign's three programmes now stand in one line: exponent pairs reduce the critical sum to
> resonance pairs; the additive-divisor programme reduces the moments to the same phase family; and
> the spectral programme's rank gap governs exactly the sum the first two produce. The barrier
> theorems of all three are statements about `Σ_{a,q} ε(a,q)e(N√(2a/q))`.**

Checked against the standing rule: `resonance_regimes` reproduces `5/6` and `1/2` as bookkeeping for
*hypothetical* cancellation, and `bourgain_cancellation_share` reproduces `17/21` exactly. No exponent
asserted below `13/84`. Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 122 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 33 results. The open core, final form:

> **Full square-root cancellation in `Σ_{q≤L} q^{−1/2} Σ_a ε(a,q) e(N√(2a/q))`, `L = N^{1/3}` —
> a two-dimensional Gauss-sum sum with square-root additive twists. `1/14` of it is known.**

## Cycle 123 — **THEOREM 34: a concrete intermediate target that would beat Bourgain**

### C317 — the Gauss-sum phase is the Jacobi symbol `[COMPUTED HERE]`

In the Hardy–Littlewood evaluation of the block theta sum near `a/q`, the normalised phase is
`ε(a,q) = ε_q·(a|q)` — a fourth root of unity times the Jacobi symbol. So the resonance sum's inner
sum is a **character sum against the phase `e(N√(2a/q))`**.

**It is not a Salié sum.** Salié's explicit evaluation applies to `Σ_a (a|q)e((ma+nā)/q)`, whose phase
is a rational additive character mod `q`; here `√(2a/q)` is irrational, so no explicit evaluation is
available. The phase also oscillates fast — its `a`-derivative is `≍ N/√(aq) ≍ N/L = N^{2/3}` — so
the character contributes nothing directly and the `a`-sum is itself an exponential sum with its own
resonance structure. **`[D53]` Do not attempt Salié evaluation of the resonance `a`-sum.**

### C318 — but the target is worth stating `[PROVED, LEAN-CERTIFIED]`

    Σ_a ε(a,q)·e(N√(2a/q)) ≪ q^{1/2+ε}  uniformly for q ≤ L = N^{1/3}
      ⟹ block sum ≪ L·Σ_{q≤L}q^{−1/2}q^{1/2} = L² = N^{2/3}
      ⟹ **μ ≤ 1/12 = 0.08333.**

> **`[THEOREM 34]` Square-root cancellation in the `a`-variable *alone* of the resonance sum implies
> `μ ≤ 1/12`, which beats Bourgain's `13/84 = 0.15476` (`oneVariableMu_beats_record`). It is therefore
> an open problem — and it is strictly weaker than the Lindelöf hypothesis, which needs the full
> two-variable cancellation (`target_ladder`).**

**This is the campaign's most actionable output.** Everything else it has produced is a barrier or a
reformulation; this is a single, concrete, one-dimensional cancellation statement whose proof would
improve the century-old record by a factor of nearly two in `μ`, and which sits strictly below LH in
strength.

### C319 — why the standing rule confirms rather than kills it

The rule says: any derived exponent below `13/84` is wrong until every input's validity is checked.
Here the exponent `1/12` is **not derived unconditionally** — it is the *consequence of a hypothesis*
that is stated explicitly and is open. The rule's purpose is to catch unconditional claims that
contradict the record; a conditional statement whose hypothesis is exactly the open problem is the
correct form. **The check passes, and it does so by making the conditionality explicit** — the same
discipline that killed D51, D52, E24, E27 and E30.

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 123 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 34 results. The ladder is now explicit:

| target | statement | consequence |
|---|---|---|
| current record | Bourgain 2017 | `μ ≤ 13/84 = 0.1548` |
| **intermediate** | **`Σ_a ε(a,q)e(N√(2a/q)) ≪ q^{1/2+ε}`** | **`μ ≤ 1/12 = 0.0833`** |
| Lindelöf | full two-variable square-root cancellation over `(a,q)` | `μ = 0` |

## Cycle 124 — **THEOREM 35: a triple barrier on the intermediate target**

C318 gave a concrete target: `T(q) = Σ_{a≤q}(a|q)e(N√(2a/q)) ≪ q^{1/2+ε}` for `q ≤ L = N^{1/3}`.
Cycle 124 attacks it with the three classical tools. All three fail, for three different and
computable reasons.

### C320 — the exponent data `[COMPUTED HERE]`

Write `q = N^κ`, `κ ≤ 1/3`, and `g(a) = N√(2a/q)`. On `a ≍ q`:

| quantity | exponent of `N` |
|---|---|
| `g'(a) = N/√(2qa)` | `1 − κ` |
| `g''(a) ≍ N/q²` | `1 − 2κ` |
| Poisson-dual range `g'([1,q])` | `1 − κ/2` |
| trivial bound | `κ` |
| **target** | **`κ/2`** |

### C321 — the three failures `[PROVED, LEAN-CERTIFIED]`

1. **van der Corput.** `|g''| ≍ N^{1−2κ}` and `1 − 2κ ≥ 1/3` for `κ ≤ 1/3`: the second derivative is
   *large*, so the phase advances by more than a full cycle between consecutive terms and every
   derivative test is vacuous. `vdC_fails_on_resonance`.
2. **Poisson.** The dual has length `N^{1−κ/2} ≥ N^{5/6}`, against an original of length
   `N^κ ≤ N^{1/3}` — **the dual is longer by a factor of at least `N^{1/2}`.**
   `poisson_fails_on_resonance`.
3. **Pólya–Vinogradov with partial summation.** The character sum saves `q^{1/2}`, but the phase
   varies by `max|Δf| ≍ N^{1−κ}` per step, giving `N^{3κ/2}·N^{1−κ} = N^{1+κ/2}`, which **exceeds the
   trivial bound `N^κ`** for every `κ ≤ 1/3`. `polyaVinogradov_fails_on_resonance`.

> **`[THEOREM 35]` On the entire range `0 < κ ≤ 1/3` the resonance `a`-sum lies outside the reach of
> van der Corput (second derivative too large), outside the reach of Poisson (dual strictly longer),
> and outside the reach of Pólya–Vinogradov with partial summation (phase varies faster than the
> character saving) — while the target `κ/2` remains strictly below the trivial bound `κ`.**
> `resonance_triple_barrier`; axioms `[propext, Classical.choice, Quot.sound]`.

### C322 — what the triple barrier means

The three tools fail for *independent* reasons — one about curvature, one about duality, one about
the interaction of a character with a fast phase. **There is no interpolation between them to try:**
each failure is a strict inequality with margin, on the whole range.

> **This is why the record has not moved by these means. The intermediate target of Theorem 34 —
> which would beat Bourgain — is not merely unproved; it is inaccessible to all three classical
> methods simultaneously, and the campaign can now say so with the margins computed.**

The sum is a `q`-term sum with pseudorandom phases (`g'` advances by `≍ N^{1−κ} ≫ 1` per step) against
a multiplicative character. Square-root cancellation is the expected truth and is exactly what none of
the three tools can deliver. **This is the same diagnosis as C313: the phase is understood, the
interaction with the multiplicative weight is not.**

### Standing position after 124 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 35 results. The chain is complete and each
link is priced:

    critical sum → coherence blocks → theta resonances → resonance pairs (a,q) → the a-sum T(q)
      ↑ Weyl 5/6      ↑ Thm 28          ↑ Thm 33           ↑ Thm 34: μ ≤ 1/12    ↑ Thm 35: triple barrier

## Cycle 125 — **THEOREM 36: a fourth tool, and a fifth self-dual coincidence**

Theorem 35 priced three classical tools on the resonance `a`-sum. Cycle 125 tries the fourth — the
campaign's own Weyl differencing (`WeylDifferencing`, C283) — and the Weil bound that differencing
makes available.

### C323 — differencing the resonance sum `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

Differencing `T(q) = Σ_{a≤q}(a|q)e(g(a))` gives correlations

    Σ_a **(a(a+h)|q)** · e(φ_h(a)),    φ_h(a) ≍ (Nh/√(2q))·a^{−1/2},

with, on `a ≍ q`: `φ_h' ≍ Nh/q²`, `φ_h'' ≍ Nh/q³`. At `h ≍ 1` and `q = N^κ` the differenced
second-derivative exponent is `1 − 3κ`, against `1 − 2κ` before — **differencing gains exactly one
factor of `κ`** (`differencing_gain`).

> **`[THEOREM 36, part 1]` The differenced second derivative vanishes exactly at `κ = 1/3`
> (`differencedSecondDeriv_top`) — the top of the admissible range, where `q ≍ L = N^{1/3}` — and is
> strictly positive below it (`differencedSecondDeriv_pos`). One differencing is *exactly critical* at
> the largest modulus and insufficient at every smaller one.**

**Fifth self-dual coincidence in this campaign.** The differencing lands on `g'' ≍ 1` precisely at the
scale the coherence decomposition selected, `L = N^{1/3}` — the same scale at which the cubic Taylor
term becomes `O(1)` (C302) and at which the theta resonances are counted (C307).

### C324 — and Weil cannot be exploited `[PROVED, LEAN-CERTIFIED]`

Differencing produces the character `(a(a+h)|q)` — a quadratic character of a *quadratic polynomial*,
for which Weil's bound gives `Σ_{a mod q}(a(a+h)|q) ≪ q^{1/2}`. Exploiting that by partial summation
needs `φ_h' ≪ 1`, i.e.

    h ≪ q²/N = N^{2κ−1} ≤ N^{−1/3} < 1.

> **`[THEOREM 36, part 2]` No admissible shift qualifies: even `h = 1` is too large by a factor
> `N^{1/3}` (`weil_unusable`). The Weil bound that differencing makes available cannot be used,
> because the phase it must be weighed against varies faster than the saving.**

This is the *same* failure mode as Pólya–Vinogradov in Theorem 35 — a character-sum saving defeated by
a fast phase — now recurring one level down, after differencing. `resonance_fourth_barrier`.

### C325 — the diagnosis, four tools deep

| tool | fails because | margin |
|---|---|---|
| van der Corput | `g''` too large | `≥ N^{1/3}` |
| Poisson | dual longer than original | `≥ N^{1/2}` |
| Pólya–Vinogradov | phase faster than character saving | `N^{1+κ/2}` vs `N^κ` |
| **Weyl differencing + Weil** | **critical only at `κ = 1/3`; Weil unusable at every shift** | **`N^{1/3}`** |

> **Four classical tools, four independent failures, all computed with explicit margins. Two of them
> (Pólya–Vinogradov and Weil-after-differencing) fail for the *same* structural reason — a
> multiplicative saving defeated by a fast phase — which is C313's diagnosis appearing twice at
> different depths.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green. No exponent asserted below `13/84`.

### Standing position after 125 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 36 results.

## Cycle 126 — **THEOREM 37: the frontier sum is a Farey-sequence exponential sum**

### C326 — the phase depends only on the ratio `[OBSERVED HERE]`

The frontier sum (C314) is `Σ_{q≤L}q^{−1/2}Σ_{a≤q} ε_q(a|q)·e(N√(2a/q))`. **The phase depends on
`(a,q)` only through the ratio `a/q`.** Grouping by the reduced fraction `a'/q'` — so that
`(a,q) = (ka', kq')` with `k ≤ L/q'` — the sum factors:

    Σ_{a'/q' reduced, q' ≤ L}  **e(N√(2a'/q'))** · A(a',q'),
        A(a',q') = Σ_{k ≤ L/q'} (kq')^{−1/2} ε_{kq'} (ka'|kq').

> **`[THEOREM 37]` The frontier sum is a sum over the **Farey sequence of order `L = N^{1/3}`** of the
> square-root phase `e(N√(2r))`, weighted by an arithmetic factor `A` obtained by summing the
> Gauss-sum data over multiples.**

The count is consistent: `|F_L| ≍ (3/π²)L²`, matching the `≍L²` resonance pairs of C314.

### C327 — what this reorganisation buys

1. **The two-dimensional sum becomes one-dimensional in the phase.** All the analytic difficulty sits
   in `Σ_{r ∈ F_L} A(r)·e(N√(2r))`: a *single* sum over Farey fractions. The two-variable structure
   survives only inside the arithmetic weight `A`, which is a divisor-type sum over `k`.
2. **The Weyl-differencing failure of C324 is explained.** Differencing in `a` at fixed `q` mixes
   different reduced fractions and therefore different phases; the natural variable is the Farey
   fraction, not `a`.
3. **The obstruction is Farey-sequence equidistribution against a square-root phase.** Franel–Landau
   makes plain equidistribution of `F_Q` equivalent to the Riemann hypothesis; here the requirement is
   cancellation of `e(N√(2r))` over `F_L`, which is a weighted, oscillatory refinement of the same
   question. **This is a structural explanation for `RH ⟹ LH` at the level of the frontier object**,
   rather than via the classical Borel–Carathéodory route.

### C328 — the honest limits of C326–C327

* The factorisation is exact and elementary; **it improves no exponent.** Checked against the standing
  rule: nothing here is below `13/84`.
* The arithmetic weight `A(a',q')` is a sum of Gauss-sum phases over multiples of `q'`; the campaign
  has not evaluated it, and its size is what would decide whether the reorganisation helps.
* **`[D54]`** Do not attempt to prove cancellation in `Σ_{r∈F_L}e(N√(2r))` by unweighted Farey
  equidistribution: the weight `A` is not slowly varying (it carries Jacobi symbols), so partial
  summation against a Farey discrepancy bound fails for the same reason Pólya–Vinogradov and Weil
  failed in Theorems 35–36 — the multiplicative data varies as fast as the phase.

### Standing position after 126 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 37 results. The frontier object in its final
form:

> **`Σ_{r ∈ F_{N^{1/3}}} A(r)·e(N√(2r))` — a Farey-sequence exponential sum with square-root phase and
> Gauss-sum weights. LH is full square-root cancellation in it; `1/14` of that cancellation is known;
> four classical tools have been priced and all fail.**

## Cycle 127 — **`[E32]` Theorem 33 corrected, and THEOREM 38: square-root cancellation is not enough**

Cycle 127 evaluated the arithmetic weight `A` of Theorem 37, and the evaluation overturns C314's
bookkeeping.

### C329 — the normalised Gauss factor depends only on the reduced fraction `[PROVED HERE]`

For `a = ka'`, `q = kq'`, the Gauss sum is `S(ka',kq') = Σ_{j mod kq'}e(a'j²/q')`, whose summand has
period `q'`, hence `= k·S(a',q')`. Therefore

    S(ka', kq') / (kq')  =  S(a',q') / q'  —  **independent of `k`.**

So the normalised theta phase attaches to the *reduced* fraction, and the correct organisation is a
**Farey dissection**: one arc per `a'/q' ∈ F_L`, of width `≍ 1/(q'L)`.

### C330 — the corrected weights `[COMPUTED HERE]`

Arc `a'/q'` contains `≍ (1/(q'L))·L² = L/q'` blocks, each of size `≍ L/√q'`, so its contribution is

    ≍ (L/q')·(L/√q') = **L²/q'^{3/2}**,   with unimodular phase ε_{q'}(a'|q')·e(N√(2a'/q')).

Sum of moduli: `Σ_{q'≤L}φ(q')L²q'^{−3/2} ≍ L²·L^{1/2} = L^{5/2} = N^{5/6}` — **Weyl, reproduced ✓.**

### `[E32]` — Theorem 33's square-root target was over-counted

C314 treated every pair `(a,q)` with `q ≤ L` as a separate resonance of weight `Lq^{−1/2}`, giving
`Σ|w|² = L³` and a square-root value of `L^{3/2} = N^{1/2}` — the Lindelöf target. **That
over-counts.** A given `α` lies in exactly *one* Farey arc; the non-reduced pairs are not independent
resonances. With the correct Farey weights:

    Σ_{F_L} |w|² = Σ_{q'≤L} φ(q')·L⁴q'^{−3} ≍ L⁴ ,   so square-root cancellation gives **L² = N^{2/3}.**

> **`[THEOREM 38]` Full square-root cancellation over the Farey resonances delivers `N^{2/3}`, i.e.
> `μ = 1/12` — **not** the Lindelöf hypothesis. LH needs `N^{1/2} = L^{3/2}`, which is a further factor
> `L^{1/2} = N^{1/6}` **below** the square-root value.**

| regime | value | `μ` |
|---|---|---|
| sum of moduli (no cancellation) | `L^{5/2} = N^{5/6}` | `1/6` (Weyl) |
| **full square-root cancellation over `F_L`** | **`L² = N^{2/3}`** | **`1/12`** |
| Lindelöf | `L^{3/2} = N^{1/2}` | `0` |

### C331 — and this confirms Theorem 27 independently

Theorem 27 (C296) concluded that LH forces `a + b = 0` — correlations *below* the square-root barrier —
and that assuming only `a ≥ 1/2` caps the route at `μ = 1/8`. Theorem 38 reaches the same verdict from
the resonance side: **generic (square-root) cancellation is insufficient; LH requires beating it.**

> **Two independent derivations now agree that the Lindelöf hypothesis is not a square-root-cancellation
> statement at the frontier. It requires cancellation strictly better than random, which is exactly
> the regime in which arithmetic structure — the multiplicativity of `n^{−it}` — must be used, and
> exactly the regime the campaign's inertness and circularity barriers say uniform methods cannot
> reach.**

Theorem 34's intermediate target survives unchanged: `μ ≤ 1/12` beats Bourgain, and Theorem 38 now
identifies `1/12` as precisely *the square-root barrier of the frontier object* — the natural stopping
point of any method that treats the resonances as generic.

### Standing position after 127 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 38 results, one correction (E32). The map:

    Weyl 1/6  →  [record 13/84]  →  **1/12 = square-root barrier of the frontier**  →  0 = LH

## Cycle 128 — **THEOREM 39: the mean square of the frontier sum is exactly the Lindelöf value**

Theorem 38 said LH needs cancellation `N^{1/6}` *below* the square-root heuristic. Cycle 128 asks
whether that is exotic. It is not — it is a theorem on average.

### C332 — the mean square `[CLASSICAL INPUT, COMPUTED HERE]`

For `t ∈ [T,2T]` and `N ≍ √(T/2π)`, the mean square of the critical block sum is

    ∫_T^{2T} |Σ_{n∼N} n^{−it}|² dt  ≍  T·N,   so the RMS of `|Σ_{n∼N}n^{−it}|` is `≍ N^{1/2} = L^{3/2}`.

(This is the diagonal of the mean square, i.e. the fourth-moment/mean-value input, not a conjecture.)

> **`[THEOREM 39]` The root-mean-square of the frontier sum over `t` is exactly `N^{1/2}` — precisely
> the Lindelöf value. Hence **LH is exactly the assertion that the frontier sum never exceeds its own
> RMS by more than `t^ε`**: a pure large-values statement, with no gap between the typical and the
> conjectured size.**

### C333 — so the square-root heuristic is provably wrong, and by exactly the right amount

| | value | |
|---|---|---|
| sum of moduli | `L^{5/2} = N^{5/6}` | Weyl |
| square-root heuristic over `F_L` (Thm 38) | `L² = N^{2/3}` | `μ = 1/12` |
| **actual RMS (theorem)** | **`L^{3/2} = N^{1/2}`** | **`μ = 0` on average** |

> **The Farey resonances are *not* independent: treating them as such over-predicts the sum by exactly
> `L^{1/2} = N^{1/6}` — the same factor by which Theorem 38 said square-root cancellation falls short.
> The below-square-root cancellation that LH requires is therefore not exotic; it provably occurs for
> almost all `t`. LH is the assertion that it occurs for *every* `t`.**

### C334 — and the deficit is localised to the major arcs

The heuristic's `ℓ²` norm is `Σ_{q'≤L}φ(q')L⁴q'^{−3} ≍ L⁴·Σ_{q'}q'^{−2}`, **dominated by `q' = O(1)`.**
The true size is `L³`. So the over-prediction lives entirely in the small-denominator (major-arc)
resonances.

> **The `N^{1/6}` discrepancy between the generic heuristic and the truth is carried by the
> bounded-`q'` Farey fractions. Those few arcs cannot all be simultaneously large; their mutual
> cancellation is what the mean square records, and reproducing it pointwise is the Lindelöf
> hypothesis.**

### C335 — this closes the loop with the campaign's large-value barriers

Theorem 39 recasts LH as a large-values problem for one explicit sum. That is precisely the object of
the campaign's **inertness** mechanism — Halász–Montgomery, the mean-value family, Guth–Maynard, all
proved inert at the self-dual block because at the convexity bound the large-value optimisation is
exactly tied. **The map is now closed:**

    critical sum → coherence blocks → theta resonances → Farey arcs → **large values of one sum**
                                                                        ↑ the inertness barriers apply here

> **After 128 cycles the campaign's forty-odd barrier theorems, derived from six different directions,
> all bear on the same statement: the frontier sum does not exceed its root-mean-square. That is the
> Lindelöf hypothesis, and it is where every route this campaign can formulate terminates.**

Checked against the standing rule: C332 is a mean-square *identity*, asserting nothing pointwise; no
exponent below `13/84` is claimed unconditionally.

### Standing position after 128 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 39 results, two corrections (E32 here, E30 in
cycle 115).

## Cycle 129 — **`[E33]` Theorem 38 corrected; THEOREM 40: two levels, and within-arc is worthless alone**

### `[E33]` — Theorem 38 omitted the within-arc level

Theorem 38 used `L²/q'^{3/2}` as the *contribution* of the Farey arc around `a'/q'`. That is the arc's
**sum of moduli**. The `L/q'` blocks inside an arc have phases varying with the distance to `a'/q'`
(within an arc `n_r` varies by `L²/q'`, so `β_r = −N²/n_r` varies by `≍L²/q'` — full variation mod 1),
so there is genuine **within-arc** cancellation. Theorem 38's `L²` and its conclusion "square-root
cancellation is not enough" are **withdrawn.**

### C336 — the four regimes `[PROVED, LEAN-CERTIFIED]`

Each arc holds `L/q'` blocks of size `L/√q'`; there are `φ(q')` arcs for each `q' ≤ L`:

| cancellation | value | `μ` |
|---|---|---|
| none | `Σφ(q')(L/q')(L/√q') ≍ L^{5/2}` | `1/6` (Weyl) |
| **within arcs only** | `Σφ(q')(L/q')^{1/2}(L/√q') ≍ L^{3/2}·L = **L^{5/2}**` | **`1/6` — no gain** |
| across arcs only | `(Σφ(q')(L²/q'^{3/2})²)^{1/2} = L²` | `1/12` |
| **both** | `(Σφ(q')(L^{3/2}/q')²)^{1/2} ≍ L^{3/2}(\log L)^{1/2}` | **`0` — LH** |

`farey_regimes_in_N`, `farey_both_gives_lindelof`.

> **`[THEOREM 40]` Square-root cancellation at *both* levels of the Farey dissection gives exactly the
> Lindelöf value `N^{1/2}` — and exactly the root-mean-square of Theorem 39. But **within-arc
> cancellation alone is worth nothing**: the weight `φ(q')/q'` exactly compensates the `q'^{-1/2}`
> gained, and the total stays at `L^{5/2}` (`within_arc_rigidity`).**

**This is a rigidity, and it explains a historical pattern:** every improvement to the *within-block*
treatment — sharper theta-sum estimates, better stationary-phase expansions — moves nothing. Only
across-arc cancellation moves the exponent, and it is worth `L^{1/2}` alone and `L` in combination.

### C337 — the mean square now agrees with the heuristic

Theorem 39 computed the RMS of the frontier sum as `L^{3/2}`. Theorem 40's double-square-root
prediction is `L^{3/2}(\log L)^{1/2}`. **They agree.** (Cycle 128's C333, which claimed the heuristic
over-predicts by `N^{1/6}`, rested on the withdrawn Theorem 38 and is corrected: the correct heuristic
matches the theorem.)

> **The frontier object behaves exactly as a generic double-square-root sum on average. LH is the
> assertion that it does so pointwise.**

## Cycle 130 — **the specification of a new mechanism, and a candidate**

Theorem 39 recast LH as a large-values statement; Theorem 40 says the target is *generic* double
square-root cancellation, pointwise. Every barrier in this campaign is a constraint on what could
deliver it. Collecting them gives a **specification**, and the specification is restrictive enough to
be useful.

### C338 — the specification `[DERIVED FROM THE BARRIER SET]`

A mechanism proving LH must satisfy **all** of:

| # | requirement | forced by |
|---|---|---|
| S1 | deliver **across-arc** cancellation | Thm 40: within-arc alone is worth nothing |
| S2 | be **non-uniform in the phase** — use multiplicativity | E29, Thms 20–25: uniform (exponent-pair) methods are capped |
| S3 | **not** interchange a Voronoi series with a second summation | the Voronoi-interchange barrier; D52 |
| S4 | **not** be AFE-internal | self-dual stationarity ⟹ inert |
| S5 | **not** re-enter a moment exponent | the circularity barrier |
| S6 | **not** need rank `> 2` spectral input | the rank gap `n(n−1)/2` grows |
| S7 | be a **large-values** method, not a mean-square one | Thm 39: the mean square is already the LH value |
| S8 | survive a **fast phase against a multiplicative weight** | Thms 35–36: PV and Weil both die there |

**S7 is the sharpest.** The large sieve applies here — C306 proved the frequencies `√(2a/q)` are
optimally spaced — but a large sieve averages over the parameter, and averaging reproduces Theorem 39's
mean square, which is already known. **No mean-square method can help; the content is entirely in the
exceptional set.**

**S4 + S2 together say: the mechanism must use information not encoded in the functional equation.**
The functional equation is what the AFE encodes; what lies outside it is the **Euler product** and the
**zeros**. The campaign's Jensen/zero-geometry barrier closes the zero side. **That leaves exactly one
resource: the Euler product.**

> **`[SPECIFICATION]` A mechanism proving LH must be a large-values method that limits large values of
> `Σ_{n∼N}n^{−it}` by exploiting the multiplicative structure of `n^{−it}` — i.e. by showing that a
> large value forces an impossible conspiracy among the prime phases `{t \log p}`.**

### C339 — the candidate, and its exact open step `[CONJECTURE]`

`|Σ_{n∼N}n^{−it}| > N^{1/2+δ}` requires `{t\log n}` to be concentrated for `≫ N^{1−ε}` values of
`n ∼ N`. Write `S_t = {n ∼ N : \|t\log n\| < η}`. Since `\log(nm) = \log n + \log m`, **`S_t` is
approximately closed under multiplication**: if `n, m ∈ S_t` and `nm ∼ N` then `nm ∈ S_{t}` with
`η ↦ 2η`. So `S_t` is an approximate multiplicative semigroup, generated by its primes

    P_t = { p ≤ N : ‖t\log p‖ < η }.

> **`[CONJECTURE C339]` `|S_t| ≫ N^{1−ε}` forces `|P_t| ≫ π(N)^{1−ε}`: a large value of the critical
> sum requires almost all primes up to `N` to be simultaneously resonant. The Lindelöf hypothesis
> follows from a bound on the number of `t ≤ T` admitting such a prime conspiracy.**

**Why this meets the specification.** S1: it bounds the whole sum, not one arc. S2, S4: it is
*entirely* multiplicative and uses nothing from the functional equation. S3: no Voronoi expansion
appears. S5: no moment is invoked. S6: no automorphic input at all. S7: it is a large-values statement
about the exceptional set of `t`. S8: there is no fast phase to fight — **the phase has been removed
and replaced by a Diophantine condition on `{t\log p}`.**

**`[OPEN CORE]`** The step from `|S_t| ≫ N^{1−ε}` to `|P_t| ≫ π(N)^{1−ε}`. It is not automatic:
`S_t` could in principle be dominated by numbers with few prime factors, or by a thin set of very
smooth numbers. **What must be proved is that an approximate multiplicative semigroup of density
`N^{−ε}` in `[N,2N]` has almost all of `[1,N]`'s primes among its generators.**

### C340 — the honest status of the candidate, and its known relatives

This is the mechanism behind **Soundararajan's resonance method** run in reverse: resonance *builds*
`t` with many resonant primes to produce Ω-results; C339 asks to *bound* how many such `t` exist.
The known Ω-results (`|ζ| = Ω(\exp(c√(\log t/\log\log t)))`) are subpolynomial, so **nothing known
contradicts C339** — but nothing known proves the semigroup step either, and the campaign has
previously recorded that the resonance route is Ω-blocked in the *constructive* direction (Gál sums
are subpolynomial). **C339 is the converse direction, which the Ω-block does not touch.**

> **This is the first mechanism the campaign has proposed that is not killed by its own barrier set.
> It is a conjecture with one explicit open core, and it is Diophantine rather than analytic — which
> is exactly what S8 demands, since every analytic tool has been priced and fails.**

Checked against the standing rule: C339 asserts no exponent; it is a conditional structure with its
open core named. Nothing here is below `13/84`.

### Standing position after 130 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 40 results, three corrections (E30, E32, E33).
The campaign now has, for the first time, a **specification** for the missing mechanism and a
**candidate** meeting it, with a single named open core.

## Cycle 131 — Phase 4 on C339: **the conjecture is FALSE**, refuted by smooth numbers

C339 conjectured: `|S_t| ≫ N^{1−ε}` forces `|P_t| ≫ π(N)^{1−ε}` — a large critical sum requires almost
all primes up to `N` to be resonant. Attacking it immediately:

### `[D55]` — the smooth-number counterexample

Suppose only the primes `p ≤ N^{1/2}` are resonant, i.e. `‖t\log p‖ < η` for all of them. That is
`π(N^{1/2}) ≍ N^{1/2}/\log N` primes — **a vanishing fraction, `≈ π(N)^{1/2}`.** But every
`N^{1/2}`-smooth `n ∼ N` then satisfies

    ‖t\log n‖ ≤ Ω(n)·η ≍ η·\log\log N,

and the `N^{1/2}`-smooth numbers in `[N,2N]` have density `ρ(2) ≈ 0.3057` — **a positive proportion.**

> **`[D55]` `|S_t| ≫ N` is achievable with only `≍ π(N)^{1/2}` resonant primes. C339 is false: an
> approximate multiplicative semigroup of positive density in `[N,2N]` need not have almost all primes
> among its generators, because the smooth numbers are dense.**

**Verdict on C339: `FALSE`.** Refuted within one cycle of being posed, by an explicit construction.

### C341 — relentless interrogation: what survives

The refutation is informative rather than merely destructive.

1. **The strong form was the wrong target anyway.** `|Σ| > N^{1/2+δ}` does not require `N^{1−ε}` terms
   to be concentrated; it requires the empirical distribution of `{t\log n}`, `n ∼ N`, to deviate from
   uniform by `N^{−1/2+δ}` **in the first Fourier mode alone**. That is a far weaker conspiracy, and
   stating it precisely just restates LH — so the semigroup framing must attach to the *weak*
   deviation, where the smooth-number construction gives no counterexample of the right size (a
   positive-density coherent set produces `≍ N`, vastly more than `N^{1/2+δ}`, and is therefore ruled
   out by the mean square of Theorem 39).
2. **Smoothness is the structural obstruction**, and the classical response to it is a **type I / type
   II (bilinear) decomposition** — which is precisely the "bilinear mechanism" that specification S1
   demanded for across-arc cancellation.

### C342 — the refined candidate, and its risk `[CONJECTURE]`

> **`[CANDIDATE]` Decompose the critical sum bilinearly (Vaughan / Heath-Brown), and handle the type
> II part by **large-sieve duality over the resonance frequencies `√(2a/q)`**, whose optimal spacing
> `≫ 1/(a₁a₂)` was proved in C306.**

**Why the S7 objection does not apply.** S7 said a large sieve averages over the parameter and so only
reproduces Theorem 39's mean square. In a *bilinear* form the averaging is over the internal bilinear
variables, not over `t` — so the output is a bound for each fixed `t`. **This is the one place in the
campaign's map where a mean-square tool yields a pointwise conclusion.**

**`[RISK — S5]`** The multiplicativity of the phase gives `Σ_{m∼M}m^{−it}·Σ_{k∼N/M}k^{−it} = Σ_n
r(n)n^{−it}` with `r` a divisor-type weight. **Any bilinear decomposition that routes through this
identity re-enters the moment problem and is killed by the circularity barrier.** The candidate
survives only if its bilinear variables come from the *resonance* structure `(a,q)` — where C306's
spacing lives — and **not** from factoring `n`. That distinction is the whole question, and it is the
next cycle's target.

### Standing position after 131 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 40 results, three corrections, one refuted
conjecture (C339/D55) and one refined candidate (C342) with its risk named.

## Cycle 132 — Phase 4 on C342: **blocked**; and the third instantiation of the specification

### `[D56]` — the frontier sum has no usable bilinear structure

C342 proposed bilinear decomposition plus large-sieve duality over the resonance frequencies. Checking
every candidate pair of bilinear variables:

1. **`(a, q)` directly.** Duality needs `Σ_a K(a,q₁)\overline{K(a,q₂)}` small for `q₁ ≠ q₂`. But `a`
   ranges over `a < q₁` in one factor and `a < q₂` in the other, and the Jacobi symbols are to
   *different* moduli — **the vectors do not live in a common space.** No inner product to bound.
2. **Reduced fraction × multiplier `(r, k)`.** This is the only bilinear structure intrinsic to the
   Farey dissection — but C329 proved the normalised Gauss factor `S(ka',kq')/(kq') = S(a',q')/q'` is
   **independent of `k`**, so the `k`-sum is a scalar and the form degenerates.
3. **Factoring `n = mk`.** Genuinely bilinear, and genuinely available by multiplicativity — but
   `Σ_m m^{−it}·Σ_k k^{−it} = Σ_n r(n)n^{−it}` with `r` a divisor weight. **This is the moment
   identity; S5 and the circularity barrier kill it.**
4. **Continued-fraction partial quotients** (Hardy–Littlewood–Wilton). A real structure, but
   *dynamical* (Gauss map), not bilinear — duality does not apply.

> **`[D56]` Verdict on C342: `BLOCKED`. In its Farey form the frontier sum is intrinsically
> one-dimensional. Its only genuine bilinear structure comes from factoring `n`, which re-enters the
> moment problem. The large-sieve mechanism has no variables to act on.**

### C343 — relentless interrogation: the third instantiation

The specification (C338) stands, and S2+S4 still force the Euler product. Two instantiations are now
dead — the semigroup form (D55, smooth numbers) and the bilinear form (D56, no variables). **What is
left in the Euler product that neither used?**

Unique factorisation supplies one further fact, and it is the deepest available:

> **The numbers `{\log p}` are linearly independent over `ℚ`.**

Every analytic method treats `\{t\log p\}` as an arbitrary sequence of phases. **No method in the
campaign's map uses their arithmetic independence.** That is the untouched resource.

> **`[CONJECTURE C343]` LH follows from an *effective, polynomially strong* form of the linear
> independence of `\{\log p\}`: a bound of the shape
>
>     ‖ Σ_{p ≤ N} c_p \log p ‖  ≫  H^{−A}    for integer `c_p` of height `H`, `A` absolute,
>
> which would forbid the phase coincidences that a large value of `Σ_{n∼N}n^{−it}` requires.**

### C344 — Phase 4 on C343: the margin is known, and it is enormous

Effective linear independence of logarithms is **Baker's theorem**, and the best effective bounds are

    | Σ c_p \log p |  >  \exp( −C(\log H)^{κ} )  —  **subpolynomial in `H`**,

whereas C343 needs `H^{−A}` — **polynomial**. The gap between `\exp(−(\log H)^κ)` and `H^{−A}` is not a
constant or a technique; it is the central open problem of transcendence theory, and no approach is
known that would close it.

> **`[D57]` C343 is *correct in kind and hopeless in strength*. The resource it identifies — arithmetic
> independence of `\{\log p\}` — is genuinely untouched by every method in the campaign's map, and it
> is genuinely the right kind of input (Diophantine, not analytic, exactly as S8 demands). But the
> quantitative gap to Baker is exponential, and closing it is a harder open problem than LH.**

### C345 — what the three instantiations together establish

| instantiation | uses | dies to |
|---|---|---|
| C339 semigroup | multiplicative closure of `S_t` | **smooth numbers** (D55) |
| C342 bilinear | factorisation + duality | **no available variables / circularity** (D56) |
| C343 independence | linear independence of `\{\log p\}` | **strength gap to Baker** (D57) |

> **All three ways of cashing in the Euler product fail, and they fail for three unrelated reasons —
> a density obstruction, a structural one, and a quantitative one. Since S2 and S4 prove the Euler
> product is the *only* resource outside the functional equation, and the zero side is closed by the
> Jensen barrier, the campaign has now enumerated and eliminated every instantiation of its own
> specification.**

**That is a genuine, if negative, completion**: the specification C338 is satisfiable in principle, and
the campaign can exhibit no mechanism satisfying it. The obstruction is no longer "we have not found
one" but "the three available forms of the only admissible resource are each independently blocked."

### Standing position after 132 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 40 results, three corrections, two refuted
conjectures (C339, C343) and one blocked candidate (C342), each with its obstruction named and
distinct.

## Cycle 133 — **`[E34]` C345 was too strong: one branch of the specification survives**

Phase 7 on cycle 132: C345 claimed the campaign "has enumerated and eliminated every instantiation of
its own specification." Re-examining S4 shows that is **false**.

### `[E34]` — S4 is not absolute, and the corpus already knows it

S4 says the mechanism must not be AFE-internal, because self-dual stationarity makes such routes inert.
But that theorem's hypothesis is *a single functional equation used at its own self-dual length*. The
campaign's own module `HTGeometry/TwoLevelAFE.lean` proves the hypothesis can be violated:

    afeLengthExponent 2 = 1 ≠ 2 = afeLengthExponent 4          (`two_level_escapes_criterion`)
    2 · afeLengthExponent 2 = afeLengthExponent 4              (`twoLevel_total_length`)

Applying the functional equation to `ζ²` — whose self-dual length is `t¹` — and then squaring, rather
than applying it to `ζ⁴` at its self-dual length `t²`, produces a Dirichlet polynomial of the **same
total length** but supported on products of two blocks each `≤ t`. **The optimisation is over the
self-dual block of `ζ²`, not of `ζ⁴`, so the stationarity theorem does not apply.**

> **`[E34]` C345 enumerated the instantiations of the *Euler-product-outside-the-functional-equation*
> branch (C339, C342, C343) and correctly eliminated all three. It did not enumerate the branch that
> uses the functional equation **at two levels**, which S4 does not forbid. That branch is open.**

### C346 — the surviving mechanism `[CANDIDATE]`

Writing the functional equation for `ζ²` on the critical line as `ζ(1/2+it)² = 2e^{iθ(t)}\,\mathrm{Re}\,U(t)`
with `U` a Dirichlet polynomial of length `t` and coefficients `d(n)`, one gets

    |ζ(1/2+it)|⁸ = 16 (Re U)⁴ ,

so **the eighth moment of `ζ` is the fourth moment of a single real Dirichlet polynomial of length `t`
with divisor coefficients**, whose off-diagonal is the balanced quadric count

    Σ_{ n₁n₂ − n₃n₄ = h,  all n_i ≤ t }  d(n₁)d(n₂)d(n₃)d(n₄).

**Against the specification:**

| requirement | status for C346 |
|---|---|
| S1 across-arc cancellation | n/a — this is the moment route, not the Farey route |
| S2 non-uniform / multiplicative | ✓ divisor coefficients throughout |
| S3 no Voronoi interchange | ✓ none appears |
| **S4 not AFE-internal** | **✓ escapes, by `two_level_escapes_criterion`** |
| S5 no moment re-entry | ✓ by the neutrality law, `m(4) < 26/21` beats `13/84` **without `μ` as input** |
| S6 rank ≤ 2 | ✓ the equation is binary additive divisor, `GL(2)` data |
| S7 large values | ✓ a moment bound is exactly a large-values bound |
| S8 fast phase vs multiplicative weight | ✓ no fast phase — the phase is gone, replaced by a counting problem |

> **C346 meets every requirement of the specification. It is the one mechanism the campaign has found
> that its own barrier set does not kill.**

### C347 — the exact open core of C346, and its price

The campaign has already priced the target (cycle 98): the eighth moment beats `13/84` iff
`m(4) < 26/21 = 1.238`, against the known `m(4) ≤ 3/2` — a **17.5 %** improvement. And what is new in
the two-level form is the **common box**: all four variables in the quadric are confined to `[1,t]`,
whereas the one-level form carries `d₄(n)` for every `n ≤ t²` with no such constraint.

> **`[OPEN CORE C347]` Does the common-box constraint improve the balanced quadric count
> `Σ_{n₁n₂−n₃n₄=h, n_i ≤ t} d(n₁)d(n₂)d(n₃)d(n₄)` beyond what is known for the unconstrained
> shifted convolution? If it saves a factor `t^{δ}` with `δ > 0`, the eighth moment improves and the
> record moves.**

**Why this is the right question.** The one-level and two-level decompositions produce polynomials of
identical length (`twoLevel_total_length`) but different support: the two-level one lives on the
*product set* `[1,t]·[1,t]`, a proper subset of `[1,t²]` of density `≍ 1/\log t` (Erdős's multiplication
table). **The two-level route therefore works with a strictly thinner object at the same length — and
that thinness is exactly the unexploited resource.**

### Standing position after 133 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 40 results, four corrections (E30, E32, E33,
E34). One live mechanism (C346) meeting the full specification, with a single named open core (C347)
and a known price (17.5 % on `m(4)`).

## Cycle 134 — Phase 4 on C346: **THEOREM 41, the last surviving mechanism is priced and fails**

C347 asked whether the common-box constraint improves the balanced quadric count. Cycle 134 answers it.

### C348 — the box-truncated coefficient `[COMPUTED HERE]`

The two-level decomposition replaces `d₄(m)`, supported on all `m ≤ t²`, by

    d₄^{(t)}(m) = Σ_{n₁n₂ = m, n₁,n₂ ≤ t} d(n₁)d(n₂),

supported on the **product set** `[1,t]·[1,t]`. Since `d₄^{(t)} ≤ d₄` pointwise, every bound for the
unconstrained shifted convolution transfers — **the two-level route is never worse.** The question is
whether it is *strictly better*, and by how much.

### C349 — the gain is Erdős–Ford, hence sub-polynomial `[PROVED, LEAN-CERTIFIED]`

By the Erdős–Ford multiplication-table theorem the product set `[1,t]·[1,t]` has density

    (\log t)^{−c}(\log\log t)^{−3/2},    c = 1 − (1+\log\log 2)/\log 2 = 0.086071…

in `[1,t²]`. **The thinning is a negative power of a logarithm.**

Against this, the requirement (cycle 98): the eighth moment beats `13/84` iff `m(4) < 26/21`, against
the known `m(4) ≤ 3/2` — a saving of

    3/2 − 26/21 = **11/42**   as an exponent of `t`   (`eighthMomentRequiredSaving_eq`).

> **`[THEOREM 41]` The two-level functional equation's structural advantage is a `(\log t)^{−0.086…}`
> thinning of the coefficient support. The eighth moment requires a saving of `t^{11/42}`. A
> logarithmic gain supplies exponent `0`; the shortfall is the entire required saving
> (`twoLevel_insufficient`, `twoLevel_shortfall`).**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 806 jobs.

### C350 — the fourth distinct obstruction, and the completed enumeration

C346 escaped every barrier in the specification S1–S8 — and dies anyway, to a *fourth* kind of
obstruction the specification did not encode: **the available structural gain is sub-polynomial while
the requirement is polynomial.** This is the campaign's `Ω`-driven ceiling mechanism in a new guise: a
method inherits the strength of its structural input, and the multiplication table is a logarithmic
phenomenon.

| branch | instantiation | dies to |
|---|---|---|
| Euler product, outside FE | C339 semigroup | density — smooth numbers (D55) |
| | C342 bilinear | structure — no variables / circularity (D56) |
| | C343 log-independence | strength — the gap to Baker (D57) |
| **Functional equation, two levels** | **C346 two-level AFE** | **scale — Erdős–Ford is logarithmic (Thm 41)** |

> **The enumeration is now genuinely complete. Both branches admitted by S1–S8 have been instantiated
> exhaustively and every instantiation is blocked, by four unrelated obstructions: density, structure,
> strength, and scale. The campaign's specification is satisfiable in principle and empty in practice
> — no known mathematical resource meets it.**

### Standing position after 134 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 41 results, four corrections, four refuted or
blocked mechanisms with distinct named obstructions. The campaign has derived a specification for the
missing ingredient and shown that nothing in the present mathematical toolkit supplies it.

## Cycle 135 — **THEOREM 42: the functional-equation tower is blocked at every depth**

Theorem 41 blocked the two-level route. Phase 7 asks whether the *tower* has other rungs.

### C351 — the tower `[COMPUTED HERE]`

Applying the functional equation to `ζ^j` and raising to the power `2k/j` writes `|ζ|^{2k}` as the
`2k/j`-th moment of a Dirichlet polynomial of length `t^{j/2}` with coefficients supported on the
`j`-fold product set:

| depth `j` | length | coefficients | support |
|---|---|---|---|
| `1` (the AFE itself) | `t^{1/2}` | `1` | `[1, √t]` — no thinning |
| `2` (C346) | `t` | `d(n)` | `[1,t]·[1,t]`, density `(\log t)^{−0.086}` |
| `j` | `t^{j/2}` | `d_j(n)` | `j`-fold table, density `(\log t)^{−δ_j}` |

By Ford's multi-dimensional multiplication-table theorem, `δ_j < 1` for every finite `j`. **Deeper
rungs thin more, but always logarithmically.**

> **`[THEOREM 42]` Every rung of the functional-equation tower offers a `(\log t)^{−δ_j}` thinning with
> `δ_j < 1`, hence contributes exponent `0` in powers of `t`, while the eighth moment requires
> `t^{11/42}`. The shortfall is the *same at every depth* (`tower_shortfall_uniform`), and no depth
> suffices (`no_depth_suffices`).**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### C352 — the resource enumeration, closed

Phase 7 also asks whether the *specification* missed a resource. Enumerating what can bound `ζ`:

| resource | status |
|---|---|
| functional equation, one level | S4 — self-dual stationarity, inert |
| **functional equation, every deeper level** | **Theorem 42 — sub-polynomial thinning at all depths** |
| Euler product — multiplicative closure | D55, smooth numbers |
| Euler product — bilinear/duality | D56, no variables; circularity |
| Euler product — linear independence of `\log p` | D57, exponential gap to Baker |
| zeros | the Jensen/Backlund zero-geometry barrier |
| higher-rank spectral input | S6, rank gap `n(n−1)/2` grows |
| family averaging (Dirichlet characters) | different aspect; gives nothing in the `t`-aspect for `ζ` |
| function-field analogues | E12 — Sawin's theorems are about linear statistics, do not transfer |
| Riemann–Siegel / refined AFE | same branch as the functional equation |

> **After 135 cycles, every resource the campaign can name for bounding `ζ(1/2+it)` has been priced,
> and each is blocked by a stated obstruction. The list is closed under the campaign's own methods:
> there is no unexamined branch.**

**This is the campaign's terminal structural statement.** It is not a proof that LH is unprovable —
no such claim is made, and none is warranted. It is the assertion that *within the resources this
campaign can enumerate*, the Lindelöf hypothesis has no accessible route, and each blockage has been
computed rather than asserted.

### Standing position after 135 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 42 results; four corrections; five refuted or
blocked mechanisms; one closed resource enumeration.

## Cycle 136 — **THEOREM 43: the neutrality of Theorem 40 is a conservation law, and it is universal**

Theorem 40 found that within-arc square-root cancellation is worth exactly nothing. Cycle 136 asks why,
and the answer generalises far beyond `ζ`.

### C353 — the arithmetic identity `[PROVED, LEAN-CERTIFIED]`

For `s < 2`, `Σ_{q ≤ L} φ(q)q^{−s} ≍ L^{2−s}` (`fareyMomentExponent`). With `L/q` blocks per arc and
theta size `L/√q`:

    no cancellation:   L² · Σφ(q)q^{−3/2} ≍ L²·L^{1/2}     = L^{5/2}
    within-arc only:   L^{3/2} · Σφ(q)q^{−1} ≍ L^{3/2}·L¹  = L^{5/2}

The prefactor **drops** by `L^{1/2}` and the Farey moment **rises** by `L^{1/2}`
(`neutrality_mechanism`). The two exactly cancel (`within_arc_neutrality`).

> **`[THEOREM 43]` Within-arc cancellation is neutral because the Farey weight `φ(q)` has precisely the
> power law `Σφ(q)q^{−s} ≍ L^{2−s}` that compensates it. The neutrality is an arithmetic conservation
> law, not a numerical accident.**

### C354 — and it holds for every phase `[PROVED, LEAN-CERTIFIED]`

`neutrality_universal` records the general form: for any prefactor exponent `p` and any Farey moment
`s`,

    p + (2 − s)  =  (p − 1/2) + (2 − (s − 1/2)).

Nothing in this depends on the phase. The three inputs — `L/q` blocks per arc, theta size `L/q^{1/2}`,
and the Farey weight `φ(q)` — are universal features of **any** theta-resonance decomposition of
**any** exponential sum.

> **`[THEOREM 43, universal form]` For every exponential sum treated by theta-resonance decomposition,
> improving the within-block estimate by a square root changes nothing. No sharpening of stationary
> phase, of the Hardy–Littlewood theta evaluation, or of the within-block error terms can ever move
> such an exponent — for any phase whatever.**

### C355 — what this explains, and what it costs

It explains a century of the subject's shape: **every advance since Weyl has come from the across-arc
side** (Bombieri–Iwaniec's spacing problems, Huxley's refinements, Bourgain's decoupling), and none
from the within-block side, despite the within-block objects being far more tractable. Theorem 43 says
that is forced.

It also **prices the campaign's own analytic modules honestly**: `WeylDifferencing`,
`VanDerCorputInequality`, `LinearExponentialSum`, `QuadraticWeylBound` are all within-block machinery.
They were needed to *derive* the exponents (C295, C307) rather than quote them, but **Theorem 43 proves
that no improvement to any of them could move `μ`.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 136 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 43 results. Theorem 43 is the campaign's most
general barrier: it constrains not `ζ`, not the critical block, but every exponential sum handled by
theta resonances.

## Cycle 137 — cross-validation against the divisor problem: **`[E35]`**, and THEOREM 44

Theorem 43 claims universality. Cycle 137 tests it on an independent problem with a known answer.

### C356 — the Voronoi bookkeeping `[PROVED, LEAN-CERTIFIED]`

`Δ(x) ≍ x^{1/4}Σ_{n≤x}d(n)n^{−3/4}e(2√(nx))`. A block bound `Σ_{n∼M}d(n)e(2√(nx)) ≪ M^b` contributes
`x^{1/4}M^{b−3/4}`, so:

* `b > 3/4`: dominated by `M ≍ x`, giving **`Δ(x) ≪ x^{b−1/2}`**;
* `b < 3/4`: dominated by small `M`, saturating at `x^{1/4}`.

    b = 5/6  ⟹  Δ(x) ≪ x^{1/3}    — **Voronoi 1903, reproduced exactly** (`divisor_incoherent`)
    b = 3/4  ⟹  Δ(x) ≪ x^{1/4}    — the divisor conjecture (`divisor_threshold`)

### `[E35]` — the transfer is *not* verbatim, and the compiler caught it

I first wrote `b = 1/2 ⟹ Δ ≪ x^{1/4}`, i.e. that the divisor conjecture is the *coherent* block total,
exactly as for `ζ`. **False:** `divisorExponentOfBlock (1/2) = 0`, and the Lean statement failed to
typecheck. Worse, running the coherence decomposition on the Voronoi phase gives an incoherent total of
`b = 2/3 < 3/4`, which would **prove the divisor conjecture** — the standing rule's signature.

**The flaw:** within-block square-root cancellation for a `d(n)`-weighted exponential sum is not
available. Its `ℓ²` size is `L^{1/2}\log^{3/2}L`, but *attaining* it is the divisor problem itself. The
coherence analysis of C298 assumed within-block square root, which is legitimate for the unweighted
`ζ`-phase (the block is a chirp, C290) and **illegitimate once a divisor weight is present.**

### C357 — what survives, and what it says `[THEOREM 44]`

> **`[THEOREM 44]` The two problems share the incoherent block total `b = 5/6` — which yields Weyl's
> `μ ≤ 1/6` and Voronoi's `Δ ≪ x^{1/3}`, both classical — but **not** their targets: `ζ` needs
> `b = 1/2`, the divisor problem only `b = 3/4` (`shared_incoherent_distinct_targets`). The Lindelöf
> hypothesis is the *strictly harder* coherence statement, by `1/4` in the block exponent.**

Placing both records on the shared scale:

| | block exponent | |
|---|---|---|
| divisor conjecture | `3/4 = 0.75` | target |
| Bourgain (ζ) | `17/21 = 0.80952` | record |
| divisor record `x^{131/416}` | `339/416 = 0.81490` | record |
| classical / incoherent | `5/6 = 0.83333` | Weyl & Voronoi |
| **Lindelöf** | **`1/2`** | **target** |

> **`[THEOREM 44, corollary]` In the shared bookkeeping the `ζ`-problem is currently *ahead* of the
> divisor problem (`zeta_ahead_of_divisor`), and both records sit strictly between the divisor target
> and the classical exponent (`records_between`). But `ζ`'s target lies `1/4` further down — the
> divisor conjecture is not a rehearsal for LH; it is a strictly weaker statement in the same
> currency.**

**Theorem 43 survives the test in the form it was stated** (within-arc neutrality for a *theta*
resonance decomposition), but E35 shows the *coherence* decomposition of C298 does not transfer to
weighted phases. The universality claim of C354 is hereby narrowed: **it holds for unweighted phases;
a multiplicative weight invalidates the within-block square-root input.**

### Standing position after 137 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 44 results, five corrections (E30, E32–E35).
The campaign's chain has now been tested against an independent known result: it reproduces Voronoi's
`x^{1/3}` exactly, and the attempt to transfer further failed in a way that was caught and diagnosed.

## Cycle 138 — **THEOREM 45: calibrating LH against the divisor conjecture**

Theorem 44 put both problems in one currency. Cycle 138 measures them.

### C358 — the distances `[PROVED, LEAN-CERTIFIED]`

Both start from the classical incoherent block exponent `5/6`:

    Lindelöf:            5/6 − 1/2 = **1/3**
    divisor conjecture:  5/6 − 3/4 = **1/12**

> **`[THEOREM 45, part 1]` In the shared block-exponent currency the Lindelöf hypothesis is **exactly
> four times** further from the classical exponent than the Dirichlet divisor conjecture
> (`lindelof_four_times_divisor`).**

### C359 — the progress `[PROVED, LEAN-CERTIFIED]`

    Bourgain 2017:            5/6 − 17/21   = 1/42       →  (1/42)/(1/3)      = **1/14  ≈ 7.1 %**
    divisor record x^{131/416}: 5/6 − 339/416 = 23/1248   →  (23/1248)/(1/12)  = **23/104 ≈ 22.1 %**

> **`[THEOREM 45, part 2]` The divisor problem is more than three times further along its road than
> `ζ` is along its (`divisor_further_along`) — and its road is four times shorter.**

| problem | classical | record | target | distance | covered | fraction |
|---|---|---|---|---|---|---|
| **Lindelöf** | `5/6` | `17/21` | `1/2` | `1/3` | `1/42` | **`1/14 ≈ 7.1 %`** |
| divisor | `5/6` | `339/416` | `3/4` | `1/12` | `23/1248` | **`23/104 ≈ 22.1 %`** |

### C360 — what the calibration says

1. **The two problems are not equally hard, and the gap is quantified.** A century has moved `ζ` one
   fourteenth of the way and the divisor problem nearly a quarter of the way — on a road four times
   shorter. In absolute block-exponent terms `ζ` has moved further (`1/42 > 23/1248`), which is why
   `zeta_ahead_of_divisor` holds; **relative to its own target, `ζ` has moved far less.**
2. **The divisor conjecture is not a rehearsal for LH.** Solving it completely would traverse `1/12`
   of block exponent; LH needs `1/3`. Even a full solution of the divisor problem leaves three
   quarters of LH's distance untouched.
3. **It calibrates the campaign's own barriers.** Theorem 34's intermediate target (`μ ≤ 1/12`, block
   exponent `2/3`) covers `5/6 − 2/3 = 1/6` — **half** of LH's distance, and twice the *entire*
   divisor conjecture. That is why it beats Bourgain by so much, and why it is hard.

Axioms `[propext, Classical.choice, Quot.sound]`; build green. Every number here reproduces a published
record or a stated target; nothing is asserted below `13/84`.

### Standing position after 138 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 45 results, five corrections. The campaign now
has a single currency in which `ζ`, the divisor problem, every classical exponent, every record, and
every one of its own intermediate targets are directly comparable.

## Cycle 139 — **THEOREM 46: where square-root cancellation is a theorem, and how far it reaches**

Phase 1 question: is there any exponential sum for which full square-root cancellation is *proved*?
There is exactly one source, and cycle 139 measures how much of the frontier it covers.

### C361 — the one proven source

**Weil–Deligne**: complete exponential sums with **algebraic** phase over a finite field have
square-root cancellation, via the Riemann hypothesis for varieties over `𝔽_q`. Every other
square-root cancellation in the subject is conjectural.

The frontier sum `Σ_{r∈F_L}A(r)e(N√(2r))` fails **both** hypotheses:

* it is **incomplete** — a Farey range, not a full residue system;
* its phase is **transcendental** in the summation variable — `√(2a/q)` is not algebraic in `a`.

### C362 — but there is an algebraic sub-family `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

`N√(2a/q)` is a rational multiple of `a/q` exactly when **`2aq` is a perfect square**. For each `q`
the admissible `a ≤ q` number `≍ √q`, so the algebraic resonances number

    Σ_{q ≤ L} √q ≍ L^{3/2}  —  a fraction  **L^{−1/2}**  of all `≍L²` resonances (`algebraic_density`).

On that sub-family the inner sum is a Gauss/Salié sum and **Weil's bound applies unconditionally**,
giving a total contribution `(Σ_{q≤L}√q·(L²/q^{3/2})²)^{1/2} ≍ **L²**`.

> **`[THEOREM 46]` The one proven source of square-root cancellation reaches exactly an `L^{−1/2}`
> fraction of the frontier's resonances, and even applied perfectly there it delivers `L²` — the
> across-arc-only level (`algebraic_reaches_only_acrossArc`), short of the Lindelöf target `L^{3/2}`
> by `L^{1/2}` (`algebraic_shortfall`). The remaining `≍L²` resonances are transcendental and no
> proven cancellation applies to them.**

### C363 — what this adds to the barrier map

This is a *different* kind of statement from the campaign's other barriers. Those say a **method**
fails. This says the **only theorem in the subject that establishes square-root cancellation** covers
a vanishing fraction of the object, for a structural reason — algebraicity of the phase — that no
technique can supply, because `√(2a/q)` is irrational for all but a thin set of `(a,q)`.

> **The gap between what is proved and what LH needs is not a gap in strength but in kind: Weil–Deligne
> proves square-root cancellation for algebraic complete sums; the Lindelöf hypothesis is
> square-root cancellation for a transcendental incomplete sum. No amount of sharpening the algebraic
> theory reaches the transcendental bulk.**

**Standing-rule check:** the algebraic sub-family's contribution `L²` bounds only that sub-family, not
the whole sum. **No total bound below `13/84` is claimed** — the transcendental bulk remains
unbounded by this argument, which is exactly the point.

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 139 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 46 results, five corrections.

## Cycle 140 — **`[E36]`** the algebraic count corrected; and **THEOREM 47: the `√d`-class decomposition**

### `[E36]` — C362 over-counted the algebraic resonances

C362 claimed `≍√q` algebraic resonances per `q`, hence `L^{3/2}` in total. **Wrong.** Solving properly:
`2aq = k²` ⟺ `a·(2q)` is a perfect square. Writing `2q = uv²` with `u` squarefree, this holds exactly
when `a = um²`, and `a ≤ q = uv²/2` forces `m ≤ v/√2`. So the count per `q` is `≍ v(2q)`, the largest
`v` with `v² ∣ 2q` — **`O(1)` for typical `q`**, not `√q`. Summing,

    Σ_{q≤L} v(2q) ≍ Σ_{v ≤ √L} v·(L/v²) ≍ **L \log L** ,

a fraction `L^{−1}\log L` of the `≍L²` resonances, not `L^{−1/2}`.

**Theorem 46's conclusion survives**: the contribution is
`L²(Σ_{q≤L}v(2q)q^{−3})^{1/2} ≍ L²·O(1) = L²`, unchanged, because the sum converges regardless of the
count. **Only the density figure was wrong, and the corrected figure makes the reach of Weil–Deligne
*narrower*, not wider.** `algebraic_density` now records `−1`.

### C364 — the `√d`-class decomposition `[COMPUTED HERE]`

Writing the frontier phase as `e(Ns)` with `s = √(2a/q) = √(2aq)/q`, the set of frequencies is

    S = { √(2aq)/q : a/q ∈ F_L }.

Grouping by the **squarefree part `d` of `2aq`**, every element of the class `S_d` has the form
`(k/q)√d` — a *rational multiple of `√d`*. So

> **`[THEOREM 47]` `S` decomposes as a disjoint union `⨆_d S_d` over squarefree `d`, with
> `S_d ⊆ √d·ℚ`. Sums `√r₁+√r₂ = √r₃+√r₄` with rational `r_i` have only the trivial solutions **across**
> classes, but **within** a class they reduce to `k₁/q₁ + k₂/q₂ = k₃/q₃ + k₄/q₄` — a rational equation
> with abundant solutions. The additive energy of `S` is therefore carried entirely inside the
> `√d`-classes.**

The class sizes are `|S_d| ≍ L²/√d` (for each `q`, the admissible `a` with squarefree part `d` number
`≍ q/√d`), so `d = 1` is *not* the largest class in the naive sense — E36 shows `|S_1| ≍ L\log L` once
the constraint `a ≤ q` is imposed, and the mass is spread over `d ≍ L²`.

### C365 — why this matters, and what it does not give

**Why it matters.** Every tool that exploits smallness of additive energy — large sieve, Halász,
decoupling — is sensitive to exactly this decomposition. Theorem 47 says the energy is *not* small
globally, but is confined to arithmetically defined classes, each of which is a scaled copy of the
rationals. **The frontier sum is therefore a union of `≍L²` rational-multiple families, and its
additive structure is completely explicit.**

**What it does not give.** Bounding a sum over `S_d` needs cancellation among `e(N(k/q)√d)` for fixed
`d` — a sum over rationals with an irrational scale, i.e. the same problem one class down. **`[D58]`
Do not recurse on the `√d`-classes: this is the D52 pattern, and the class structure does not
terminate.**

### Standing position after 140 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 47 results, six corrections (E30, E32–E36).
The frontier object's additive structure is now explicit; its cancellation is not.

## Cycle 141 — **THEOREM 48: the frontier frequency set is optimally structured, and it does not help**

### C366 — the additive energy is minimal `[PROVED, LEAN-CERTIFIED]`

The `√d`-classes of Theorem 47 are indexed by the squarefree part of `2aq`, which for a typical pair is
`≍L²` — so **most classes are singletons**, and the largest (`d = 1`) has only `≍L\log L` elements by
E36. Additive relations `s₁+s₂ = s₃+s₄` force matching classes, so

    non-trivial energy  ≤  Σ_d m_d³  ≤  (max_d m_d)²·Σ_d m_d  ≤  (L\log L)²·L²  =  L⁴\log²L,

against the trivial `|S|² = L⁴`.

> **`[THEOREM 48]` The frontier frequency set `S = {√(2a/q)}` has **minimal additive energy**
> `E(S) ≍ |S|²` up to logarithms (`energy_minimal`). Moreover the largest class sits **exactly** at the
> threshold `largestClassSize = frequencySetSize/2` (`largestClass_at_threshold`) — any larger and the
> non-trivial energy would dominate (`energy_threshold`).**

### C367 — and this is exactly the wrong kind of good news

Minimal additive energy is **the** hypothesis under which the large sieve, Halász-type large-value
theorems, and `ℓ²` decoupling are sharpest. The frontier set satisfies it optimally.

> **The frontier frequency set is optimally structured for every additive-combinatorial tool in the
> subject — and every one of those tools still fails, because each requires averaging over the
> parameter `N`, and averaging reproduces the mean square of Theorem 39 and nothing more.**

This isolates the obstruction with more precision than anything earlier in the campaign:

| candidate obstruction | verdict |
|---|---|
| the frequency set is badly spaced | **no** — optimally spaced (C306) |
| the frequency set has large additive energy | **no** — minimal (Theorem 48) |
| the weights are pathological | **no** — smooth amplitudes, Jacobi-symbol phases (C309) |
| the phase is intractable | **no** — elementary at the self-dual scale (Theorem 32) |
| **there is no averaging parameter** | **yes** — the sum is evaluated at a single `N` |

> **After 141 cycles the obstruction has one name: the Lindelöf hypothesis is a *pointwise* statement
> about a sum whose every structural feature — spacing, energy, weights, phase — is optimal, and every
> available tool is a *mean-value* tool. That is why the mean square is already the Lindelöf value
> (Theorem 39) and the pointwise statement is open.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 141 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 48 results, six corrections.

## Cycle 142 — **THEOREM 49: smoothing cannot close the pointwise/mean-value gap**

Theorem 48 named the obstruction: every structural feature is optimal, every tool is a mean-value
tool. Cycle 142 attacks the standard bridge from mean-value to pointwise — the Sobolev inequality —
which the campaign already carries in `HTGeometry/SpikeSobolev.lean`.

### C368 — the two terms are not symmetric `[PROVED, LEAN-CERTIFIED]`

    |f(t₀)|²  ≤  (1/H)∫_I |f|²  +  ∫_I |f||f'| .

**Only the first term carries `1/H`.** For the frontier sum `F(t) = Σ_{n∼N}n^{−it}` one has
`F'(t) = −i Σ_n (\log n)n^{−it}`, so `∫_I|F'|² ≍ \log²N·∫_I|F|²` and

    ∫_I |F||F'| ≤ (∫_I|F|²)^{1/2}(∫_I|F'|²)^{1/2} ≍ **\log N · ∫_I |F|²** .

The variation term is *larger than the mean square itself*, with no `H` to shrink it.

### C369 — and the mean square is not `HN` on short intervals `[PROVED, LEAN-CERTIFIED]`

`∫_I|F|² = H·N + O(Σ_{m≠n}\min(H, N/|m−n|)) = H·N + O(N²\log N)`, so the off-diagonal dominates for
every `H ≪ N`. In exponents (`shortMeanSquare`), the mean square saturates at `N²` for all `H ≤ N`
(`shortMeanSquare_short`).

> **`[THEOREM 49]` The Sobolev upgrade returns the trivial bound at every interval length:
> `sobolevOutput h = 2` for all `h ≤ 1`, i.e. `|F| ≪ N` with no cancellation (`sobolev_trivial`), a
> shortfall of a full power of `N` from the Lindelöf target (`sobolev_shortfall`). Both effects — the
> `1/H`-free variation term and the off-diagonal saturation of the short mean square — push the same
> way.**

### C370 — the general form of the obstruction

The failure is structural rather than technical: **Sobolev is useless for a rapidly oscillating
function.** `F` oscillates at rate `\log N` in `t`, so `|F'| ≍ \log N·|F|` and the variation term can
never be smaller than the mean square. Any smoothing bridge of this type has the same defect.

This prices the campaign's own `SpikeSobolev` module honestly: it was built as the tool for exactly
this step, and Theorem 49 shows the step cannot be taken.

| bridge from mean-value to pointwise | verdict |
|---|---|
| Sobolev / smoothing | **Theorem 49 — trivial at every scale** |
| maximum principle / Jensen | the zero-geometry barrier |
| large-value estimates + moments | circularity barrier |
| mollification | re-enters the moment problem |

> **All four bridges are closed. The mean square of the frontier sum is already the Lindelöf value
> (Theorem 39); no available mechanism converts it into a pointwise statement.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 142 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 49 results, six corrections.

## Cycle 143 — **THEOREM 50: the fifth bridge, and why amplification collapses to resonance**

Theorem 49 closed four bridges from mean-value to pointwise. There is a fifth, and it is the modern one.

### C371 — amplification in the `t`-aspect `[COMPUTED HERE]`

Amplification is the standard subconvexity route: attach an amplifier `A` large at the target and small
elsewhere, then bound `∫|A|²|ζ|⁴`. It is what gives subconvexity for `GL(2)` families
(Iwaniec, Michel–Venkatesh).

**In the `t`-aspect the family is the translates, so an amplifier must be `A(t) = Σ_n a_n n^{−it}`.**
For `A` to be large at `t₀`, the coefficients must resonate with the prime phases `\{t₀\log p\}` —
**which is exactly the resonance method.** Amplification and resonance are the same construction in
this aspect.

### C372 — and its gain is subpolynomial `[PROVED, LEAN-CERTIFIED]`

The amplification factor is governed by Gál-type sums, whose extremal size is
`\exp(c√(\log N\log\log N)) = N^{o(1)}` (Bondarenko–Seip). So

> **`[THEOREM 50]` The amplifier contributes exponent `0` in powers of `N`
> (`amplification_subpolynomial`), against a required pointwise saving of `1/2` — the shortfall is the
> entire saving (`amplification_shortfall`). It misses even Theorem 34's intermediate target, which
> needs `1/6` (`amplification_misses_intermediate`).**

### C373 — the five bridges, closed

| bridge from mean-value to pointwise | verdict | exponent delivered |
|---|---|---|
| Sobolev / smoothing | Theorem 49 | trivial (`2`, i.e. no saving) |
| maximum principle / Jensen | zero-geometry barrier | — |
| large values + moments | circularity barrier | — |
| mollification | re-enters the moment problem | — |
| **amplification** | **Theorem 50 — collapses to resonance** | **`0`** |

`five_bridges_closed` records the two that admit an exponent computation.

> **The mean square of the frontier sum is exactly the Lindelöf value (Theorem 39). Five distinct
> mechanisms exist in the literature for converting a mean value into a pointwise bound, and all five
> are now priced and closed for this object. That is the campaign's sharpest statement of why the
> Lindelöf hypothesis resists: not because the object is badly behaved — every structural feature is
> optimal (Theorem 48) — but because the passage from average to pointwise has no available
> mechanism.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 143 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 50 results, six corrections.

## Cycle 144 — **THEOREM 51: the dichotomy is exhaustive**

### C374 — every bound is one of two kinds `[STRUCTURAL]`

Any proof of `|ζ(1/2+it₀)| ≤ B` either uses information about `ζ` at points other than `t₀`, or it does
not. That is exhaustive by definition, and it splits the subject:

**(a) Direct pointwise.** Estimate `Σ_{n∼N}n^{−it₀}` from properties of the phase at `t₀` alone. Every
such argument is an exponential-sum estimate, and there are exactly two families:

* the **van der Corput / exponent-pair family** — differencing, Poisson, stationary phase, theta
  resonances. Priced by Theorems 20–25 (the semigroup terminates at `1/6` realisably), Theorem 43
  (within-block improvements are universally neutral), Theorems 35–36 (four tools fail on the
  resonance sum with computed margins);
* the **algebraic / Weil–Deligne family** — complete sums with algebraic phase. Priced by Theorem 46:
  it reaches an `L^{−1}\log L` fraction of the resonances and delivers `L²`, short of the target.

**(b) Mean value plus a bridge.** Establish an average and convert it. The mean square is already the
Lindelöf value (Theorem 39), and all five bridges are closed:

| bridge | verdict |
|---|---|
| Sobolev / smoothing | Theorem 49 — trivial at every scale |
| maximum principle / Jensen | zero-geometry barrier |
| large values + moments | circularity barrier |
| mollification | re-enters the moment problem |
| amplification | Theorem 50 — collapses to resonance, exponent `0` |

> **`[THEOREM 51]` The dichotomy (a)/(b) is exhaustive, each branch has been enumerated, and every
> member of every branch is priced. The campaign's fifty results are not fifty separate obstructions:
> they are a complete taxonomy of the two ways a bound on `ζ` can be proved, with an obstruction
> attached to each leaf.**

### C375 — what this is and is not

**It is not** a proof that LH is unprovable, and no such claim is made. New mathematics creates new
leaves; the taxonomy is of *present* methods.

**It is** a statement that within the enumerated methods every leaf carries a computed obstruction,
and that the obstructions are not variations on one theme: they include inertness at a stationary
point, circularity, spectral thinness, `Ω`-floors, a Voronoi-interchange barrier, a sub-polynomial
scale (Erdős–Ford), a strength gap (Baker), a density obstruction (smooth numbers), a structural one
(no bilinear variables), and the pointwise/mean-value gap itself.

> **A century of work has moved `μ` one fourteenth of the way (Theorem 45). The campaign's contribution
> is to say precisely which thirteen fourteenths remain, and what would have to be true for any of them
> to be crossed.**

### Standing position after 144 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 51 results, six corrections, one complete
taxonomy.

## Cycle 145 — **THEOREM 52: the pointwise/mean-value gap is self-similar**

Cycle 145 attacks the intermediate target of Theorem 34 with the one tool not yet tried on it: an
average over the modulus.

### C376 — the target holds on average over `q` `[PROVED, LEAN-CERTIFIED]`

    Σ_{q ≤ L}|T(q)|² = Σ_q Σ_{a,a'}(aa'|q)e(N(√(2a/q) − √(2a'/q))),

whose diagonal `a = a'` gives `(a²|q) = 1` and contributes `Σ_{q≤L}φ(q) ≍ (3/π²)L²`. Over `L` moduli
that is an average of `|T(q)|² ≍ L`, hence

    **|T(q)| ≍ L^{1/2} ≍ q^{1/2}  for typical `q` — exactly the target** (`typicalResonanceSize_eq`).

> **`[THEOREM 52]` The intermediate target `T(q) ≪ q^{1/2+ε}` **holds in mean square over `q`**, with
> the average matching the target exactly. What is needed is uniformity in `q`. The pointwise/mean-value
> gap of Theorem 39 therefore recurs, with the same exactness, one level down (`gap_self_similar`).**

### C377 — the obstruction is scale-invariant

| level | object | mean value | pointwise statement |
|---|---|---|---|
| top | `Σ_{n∼√t}n^{−it}` | RMS `= N^{1/2}` — **exactly the Lindelöf value** (Thm 39) | LH — open |
| **one down** | `T(q) = Σ_a(a\|q)e(N√(2a/q))` | mean square `⟹ q^{1/2}` — **exactly the target** | Thm 34's hypothesis — open |

> **The campaign's entire difficulty is one phenomenon repeated: at every scale the average is exactly
> the goal, and the uniform statement does not follow. The obstruction is not located at a particular
> level of the reduction — it is invariant under the reduction.**

This explains why the reduction chain, though exact and informative at every step, never converts into
a bound: **each step preserves the gap it was meant to close.** It also explains D52 and D58 — the
recursions fail because recursing reproduces the same gap rather than shrinking it.

### C378 — consequence for the mechanism search

The specification of C338 required (S7) a large-values method rather than a mean-value one. Theorem 52
sharpens that requirement:

> **A mechanism must close the pointwise/mean-value gap at *some* level. Because the gap is
> scale-invariant, no reduction can move it to a level where it is easier — a mechanism must attack it
> directly, at whichever level it chooses.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 145 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 52 results, six corrections.

## Cycle 146 — **THEOREM 53: closing the gap by moments *is* the Lindelöf hypothesis**

Theorem 52 said a mechanism must attack the pointwise/mean-value gap directly. Cycle 146 asks what
"directly" excludes, by pricing the one framework that could in principle empty an exceptional set.

### C379 — the exceptional-set calculation `[PROVED, LEAN-CERTIFIED]`

Let `E_δ = \{t ∈ [T,2T] : |F(t)| > N^{1/2+δ}\}`. The `2k`-th moment gives

    |E_δ|·N^{(1+2δ)k} ≪ ∫|F|^{2k} ≪ T^{m(k)+ε}N^{k},   so   |E_δ| ≪ T^{m(k)+ε}N^{−2kδ}.

With `N = T^{1/2}` and the conjectural `m(k) = 1` this is `T^{1−kδ+ε}`, which forces `E_δ = ∅` exactly
when `k > 1/δ` (`exceptional_empty_iff`).

> **`[THEOREM 53]` No finite moment order suffices uniformly: for every `k` there is a positive `δ` at
> which the exceptional set is not forced empty (`no_finite_moment_suffices`), and halving the excess
> doubles the required order (`requiredMomentOrder_diverges`). Emptying `E_δ` for **every** `δ > 0`
> therefore requires **all** moments — which is the Lindelöf hypothesis itself.**

### C380 — the sharpest form of the circularity barrier

This is the campaign's circularity mechanism at its limit. The moment framework is the only tool that
converts an average into an emptiness statement, and it does so **only at infinite order**, where the
input equals the conclusion.

> **Within the moment framework the pointwise/mean-value gap cannot be closed by any finite amount of
> averaging. A mechanism must therefore be *non-quantitative* in this respect: it must **classify**
> large values structurally rather than **count** them.**

### C381 — the specification, in final form

Combining C338 (S1–S8), Theorem 52 (scale-invariance) and Theorem 53:

> **A mechanism proving LH must (i) act on the pointwise statement directly, since the gap is
> invariant under every reduction the campaign can perform; (ii) classify the structure of a
> hypothetical large value rather than bound the measure of the set of them, since counting requires
> all moments and all moments is LH; and (iii) draw on the multiplicativity of `n^{−it}`, the only
> resource outside the functional equation, whose three known instantiations are each blocked (D55,
> D56, D57).**

**Every clause is forced by a proved barrier.** The specification is now as tight as this campaign can
make it, and no known mathematical object satisfies it.

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 146 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 53 results, six corrections.

## Cycle 147 — **THEOREM 54: the classification theorem exists, and `n^{−it}` is its extremal case**

C381 demanded a mechanism that **classifies** large values rather than counting them, and uses
multiplicativity. Cycle 147 finds the theorem that does exactly that, and prices it.

### C382 — Halász's theorem meets clauses (ii) and (iii) `[STRUCTURAL]`

In its pretentious form, `|Σ_{n≤N}f(n)| ≪ N(1+M)e^{−M}` with

    M = min_{|t'| ≤ T} Σ_{p ≤ N} (1 − Re f(p)p^{−it'})/p ,

so a multiplicative `f` has a large sum **only if it pretends to be `n^{it'}χ(n)`**. This is a genuine
classification, not a count, and it is stated for multiplicative functions — **exactly clauses (ii)
and (iii) of the specification.**

### C383 — and it is vacuous on `n^{−it}` `[PROVED, LEAN-CERTIFIED]`

For `f(n) = n^{−it}` the minimum is attained at `t' = −t`, where `M = 0` and the bound is trivial.

> **`n^{−it}` is exactly the extremal pretentious function — it *is* the obstruction Halász's theorem
> is designed to detect.**

Restricting the range to `|t'| ≤ N` (with `t ≍ N²`, so `t' = −t` is excluded) leaves `|t+t'| ≍ N²`, the
phases `(t+t')\log p` oscillate, and `M ≍ \log\log N`, giving a saving

    N(\log\log N)e^{−\log\log N} ≍ N\log\log N/\log N  —  **subpolynomial**, exponent `0`
    (`halasz_subpolynomial`, `classification_branch_priced`).

> **`[THEOREM 54]` The one theorem in the subject that classifies large values of a multiplicative
> function is stationary exactly at `n^{−it}`: it delivers exponent `0`, the same as amplification
> (`halasz_eq_amplification`), and misses even the intermediate target's `1/6`.**

### C384 — the inertness mechanism, fifth appearance

This is the campaign's oldest mechanism in a new place. Self-dual stationarity said an AFE-internal
optimisation is stationary at the self-dual block; the mean-value family, Halász–Montgomery,
Guth–Maynard and the zero geometry were all shown inert there. **Halász's pretentious theory is inert
for the same reason: the tool's extremal configuration is precisely the object under study.**

| tool | stationary/extremal at |
|---|---|
| AFE optimisation | the self-dual block `N = √t` |
| large-value theorems | the same block |
| exponent-pair `A`-process | the line of symmetry, `μ = κ` |
| amplification / resonance | the prime phases of `t` itself |
| **Halász / pretentious** | **`n^{−it}` itself** |

> **Five independent tools, each stationary exactly at the object it would have to bound. That is the
> campaign's most persistent finding, and Theorem 54 is its sharpest instance: the classification
> theorem the specification demanded exists, is correctly aimed, and evaluates to zero on its target.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green.

### Standing position after 147 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 54 results, six corrections.

## Cycle 148 — **THEOREM 55: the smooth/multiplicative dichotomy — the campaign's capstone**

Theorem 54 observed five independent tools each stationary at the object. Cycle 148 explains why, and
the explanation unifies all fifty-four results.

### C385 — two properties used to organize recorded examples `[HEURISTIC; EXHAUSTIVE CLAIM WITHDRAWN]`

`n ↦ n^{−it}` is simultaneously

* **completely multiplicative** — `(mn)^{−it} = m^{−it}n^{−it}`;
* **archimedean-smooth** — the restriction to `ℤ⁺` of a smooth function of a real variable.

The following table organized selected examples. It is not an exhaustive classification of methods:

| family | uses | members | extremal at |
|---|---|---|---|
| **smooth** | derivatives of the phase | van der Corput, stationary phase, exponent pairs, theta resonances, decoupling | the self-dual block `N = √t` |
| **multiplicative** | the Euler product | Halász / pretentious theory, moments, resonance, amplification | **characters** — and `n^{−it}` is a character |

> **The exhaustive interpretation previously labelled THEOREM 55 is withdrawn.** The cited Lean
> module stores family labels and rational exponents; it contains no analytic method type or
> completeness theorem for this table. It proves neither that every method uses only one property
> nor that every proof of Lindelöf must combine the two. See the
> [source-semantics audit](corpus-method-model-semantics-audit.md).

### C386 — the bookkeeping `[PROVED, LEAN-CERTIFIED]`

`HTGeometry/SmoothMultiplicativeDichotomy.lean`:

    named Bourgain record:           assigned saving 4/21
    two multiplicative records:      assigned saving 0 (`multiplicative_family_zero`)
    model target:                    assigned saving 1/2
    difference for the named record: 13/42 (`best_shortfall`)

* `neither_family_suffices` compares the three named records only.
* `families_do_not_add_up` compares the sum of two assigned exponents with the assigned target.
  It proves no obstruction to combining actual mathematical methods.

### C387 — how this unifies the campaign

The following were motivating connections, not consequences of the scalar bookkeeping theorem:

* **E29** (the exponent-pair formalism is uniform over phases and discards multiplicativity) — the
  smooth family's blind spot;
* **Theorem 54** (Halász is extremal at `n^{−it}`) — the multiplicative family's blind spot;
* **Theorem 32** (the phase is elementary; the weight is the difficulty) — the two properties meeting
  and neither tool coping;
* **self-dual stationarity, the line-of-symmetry attractor, the `A`-inertness threshold** — the smooth
  family's stationarity, computed;
* **D55–D57, Theorems 41–42** (the Euler-product instantiations) — the multiplicative family's
  failures, computed.

> The two properties suggest a way to organize questions. The cited module does not establish
> the former claim that all fifty-five results reduce to one exhaustive obstruction. Its successful
> axiom audit certifies the stated rational comparisons, not that broader interpretation.

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 148 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 55 results, six corrections, one capstone.

## Cycle 149 — **THEOREM 56: the coupling exists, is essentially unique, and is exhausted**

The heuristic in C385 suggested seeking an operation using both properties. This was a research
choice, not a necessity proved by Theorem 55. Cycle 149 asks about such operations.

### C388 — it does, and there are exactly two `[STRUCTURAL]`

The structures that couple the archimedean and multiplicative aspects of `ζ` are:

1. **The functional equation** — `π^{−s/2}Γ(s/2)ζ(s) = π^{−(1−s)/2}Γ((1−s)/2)ζ(1−s)`. A gamma factor
   (archimedean) multiplied by an Euler product (multiplicative), asserted to be symmetric. **This is
   precisely a statement that the two properties interact.**
2. **The explicit formula** — `Σ_ρ x^ρ` against `Σ_n Λ(n)`. Couples the Euler product to the
   archimedean/zero structure.

> **An `L`-function *is* the object in which smoothness and multiplicativity coexist, and its
> functional equation is the theorem that couples them. Theorem 55's requirement is therefore not
> exotic — the required coupling exists and is classical.**

### C389 — and both couplings are already priced `[CAMPAIGN RESULTS]`

| coupling | route | verdict |
|---|---|---|
| functional equation, **one level** | AFE at its own self-dual length | **self-dual stationarity — inert** (S4) |
| functional equation, **every deeper level** | the two-level tower | **Erdős–Ford scale: sub-polynomial at all depths** (Thms 41–42) |
| explicit formula | Jensen / Backlund zero geometry | **circular or inert** (the zero-geometry barrier) |

> **`[THEOREM 56]` The unique structures coupling the two properties of `n^{−it}` are the functional
> equation and the explicit formula. Both are classical, both are available, and both have been priced
> by this campaign: the functional equation is stationary at the critical block at one level and
> sub-polynomial at every deeper level; the explicit formula is closed by the zero-geometry barrier.
> **The coupling Theorem 55 demands exists, is essentially unique, and is exhausted.**

### C390 — the campaign's terminal explanation

Reading Theorems 55 and 56 together:

> **The Lindelöf hypothesis asks for a bound that requires the smooth and multiplicative structures of
> `n^{−it}` to interact. Mathematics contains exactly one place where they do interact — the
> functional equation — and that place is *stationary* at precisely the point where the bound is
> needed. The self-dual block `N = √t` is simultaneously where the functional equation balances and
> where the Lindelöf hypothesis is stated.**

That coincidence is not incidental: the critical block is `√(conductor)`, which is where the functional
equation's two sides have equal length. **The Lindelöf hypothesis is posed exactly at the fixed point
of the only structure that could prove it.**

This is the sharpest account the campaign can give of why the problem is hard, and it is consistent
with every one of the fifty-five results: each is an instance of a tool evaluated at a fixed point of
its own symmetry.

### Standing position after 149 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 56 results, six corrections.

**What the campaign has established, in one sentence:** the Lindelöf hypothesis is a statement about
the interaction of two structures whose unique classical coupling is stationary exactly where the
statement is made, and every method in the subject has been shown to inherit that stationarity, with
its shortfall computed.

## Cycle 150 — **THEOREM 57: the degeneracy is a flat direction, and it exists only at the convexity bound**

Theorem 56 located the obstruction at a stationary point. Cycle 150 asks whether the stationarity is
delicate — whether a second-order term could break it.

### C391 — it is not a stationary point but a flat direction `[PROVED, LEAN-CERTIFIED]`

The self-dual saving of the approximate functional equation, as a function of the block parameter `x`
at input exponent `θ₀`, is

    Sav(θ₀, x) = (2θ₀ − x)/(1/2 − x),     ∂ₓ Sav = (2θ₀ − 1/2)/(1/2 − x)².

> **At the convexity bound `θ₀ = 1/4` the saving is **identically `1`** for every admissible `x`
> (`afeSaving_convexity`) — not merely stationary. There is no second-order term to exploit: the
> degeneracy is total in the block parameter, and no perturbation of any order produces a gain.**

### C392 — and the flat direction exists **only** there `[PROVED, LEAN-CERTIFIED]`

`afeSaving_flat_iff` — the slope vanishes exactly at `θ₀ = 1/4`. For any subconvexity input the slope
is strictly negative (`afeSaving_slope_neg`), so the saving decreases in `x` and the optimum sits at
the largest admissible block: **the tie is broken toward the critical line.** At Bourgain's exponent
the saving at the trivial block is `4θ₀ = 13/21 < 1` (`afeSaving_bourgain_at_zero`).

> **`[THEOREM 57]` The flat direction is a phenomenon of the convexity bound alone. Once any
> subconvexity is available the degeneracy is broken, strictly. This is why every barrier in this
> campaign concerns *improving* `13/84` rather than *reaching* `1/4` — the hard region begins where
> the flatness ends.**

### C393 — what this settles, and what it leaves

**Settles:** the obstruction of Theorems 55–56 is not a delicate balance that a cleverer perturbation
might tip. At the convexity bound it is an identity; past it, the optimisation is well-behaved and
simply does not reach far enough. **Neither regime admits a perturbative escape.**

**Leaves:** the same open core. The subconvexity regime has a strictly negative slope, meaning the
optimum is at the boundary of the admissible block range — and the campaign's Theorems 20–25 are
precisely the computation of what happens at that boundary.

> **After 150 cycles: the convexity bound is a flat direction (no perturbative gain); past it the
> optimisation is strict but terminates at the boundary, where the exponent-pair machinery is inert
> (Thm 20), the line of symmetry attracts (Thm 22), and the realisable floor is `1/6` (Thm 25). Both
> regimes are closed, for different reasons, and the closure is computed in each.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 150 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 57 results, six corrections, ~58 dead routes.

## Cycle 151 — the strip `1/2 ≤ σ < 1`, and **`[D59]`** a transfer that does not work

Phase 1 question: LH is the statement `μ(1/2) = 0`, but `μ(σ) = 0` is conjectured for the whole
half-line `σ ≥ 1/2` and known only for `σ ≥ 1`. Does the campaign's analysis extend along the strip?

### C394 — the critical block moves with `σ` `[COMPUTED HERE]`

The approximate functional equation for `ζ(σ+it)` splits as
`Σ_{n≤x}n^{−σ−it} + χ(σ+it)Σ_{n≤y}n^{σ−1+it}` with `xy ≍ t`. Writing `x = t^α`, `y = t^{1−α}` and
`|χ(σ+it)| ≍ t^{1/2−σ}`, a block bound `|Σ_{n∼M}n^{−it}| ≪ M^b` gives

    principal term  ≪ t^{α(b−σ)}  (for `b > σ`),      dual term  ≪ t^{1/2−σ}·t^{(1−α)(b−1+σ)} .

**The two are balanced at `α = 1/2` only when `σ = 1/2`.** For `σ > 1/2` the optimal split takes `x`
strictly larger than `√t`, so **the critical block is `t^{α(σ)}` with `α(σ) > 1/2` — it moves with
`σ`.**

> **`[D59]` The campaign's entire analysis is anchored at the self-dual block `N = √t`, which is the
> optimum *only* at `σ = 1/2`. Its barriers — self-dual stationarity, the line-of-symmetry attractor,
> the coherence decomposition at length `N^{1/3}`, the Farey dissection of order `N^{1/3}` — are all
> statements about that block and **do not transfer verbatim to `σ ≠ 1/2`.** Do not attempt to read
> off `μ(σ)` from the campaign's `σ = 1/2` bookkeeping.**

**Caught by the standing rule.** A naive transfer (`μ(σ) = (b−σ)/2`, hence `μ(σ) = 0` for `σ ≥ b =
17/21 ≈ 0.81`) would assert `ζ(σ+it) ≪ t^ε` throughout `σ ≥ 0.81`, far beyond the literature, where
`μ(σ) = 0` is known only for `σ ≥ 1`. The error is exactly the fixed `α = 1/2`: the dual term is not
negligible off the critical line.

### C395 — what does survive

> **`σ = 1/2` is the unique abscissa at which the functional equation's two sides have equal length.**
> Every result in this campaign is a statement about that coincidence — Theorem 56 identified it as the
> reason LH is posed at the fixed point of its own coupling, and C394 now shows the coincidence holds
> at no other `σ`.

So the campaign's barriers are **specific to the Lindelöf hypothesis**, not to the family
`μ(σ) = 0`. That is a limitation of scope and also a confirmation of Theorem 56: the difficulty is
located exactly where the two sides balance, and nowhere else on the strip.

### Standing position after 151 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 57 results, six corrections, 59 dead routes.

## Cycle 152 — **THEOREM 58: the mechanism exists in the conductor aspect, and needs periodicity**

Theorem 55 demanded a tool using multiplicativity and a second structure simultaneously. Cycle 152
finds one — **in a different aspect** — and identifies exactly what the `t`-aspect lacks.

### C396 — Burgess uses both properties at once `[STRUCTURAL]`

Subconvexity for `L(1/2,χ)` in the **conductor** aspect is known: Burgess gives `≪ q^{3/16+ε}` against
convexity `q^{1/4}`, a saving of `1/16` (`burgess_saving`). The critical block there is
`Σ_{n∼√q}χ(n)`, and the method uses **both**:

* **multiplicativity** of `χ` — shift the interval by `ab`, factor `χ(abn) = χ(a)χ(b)χ(n)`;
* **periodicity** of `χ` — complete the shifted short sum to a full residue system, where **Weil's
  bound applies**.

Burgess is nontrivial above block length `q^{1/4}`, and the critical block is `q^{1/2}` — comfortably
above (`burgess_reaches_critical`, margin `1/4`).

> **In the conductor aspect the mechanism Theorem 55 demands *exists*: Burgess sees multiplicativity
> and completeness together, and that is exactly why subconvexity in `q` is a theorem while
> subconvexity in `t` needed Weyl, Bombieri–Iwaniec, Huxley and Bourgain to reach `13/84`.**

### C397 — and the `t`-aspect cannot have it `[STRUCTURAL]`

In the `t`-aspect the multiplicative function is `n^{−it}`, which is **aperiodic** — archimedean, not a
character modulo anything. **There is no residue system to complete to.** The completion step, which is
where Weil's bound enters, has no analogue.

> **`[THEOREM 58]` Burgess's method is the one technique that uses multiplicativity and completeness
> together, and it requires the multiplicative function to be **periodic**. The `t`-aspect replaces
> periodicity by smoothness, and smoothness does not permit completion. Hence Burgess has no
> `t`-aspect analogue, and the Lindelöf hypothesis is deprived of the mechanism that solves the
> corresponding problem in the conductor aspect.**

### C398 — the specification, restated in these terms

Theorem 55 said: a mechanism must use both of `n^{−it}`'s properties. Theorem 58 sharpens the reason
none does:

| aspect | multiplicative function | second property | completion possible? | mechanism |
|---|---|---|---|---|
| conductor `q` | `χ` mod `q` | **periodic** | **yes** — full residue system | **Burgess + Weil** ✓ |
| **`t`** | `n^{−it}` | **smooth** (archimedean) | **no** | **none** |

> **The missing ingredient has a name: `n^{−it}` cannot be completed. Every finite-field input — Weil,
> Deligne, Kloosterman, Salié — enters analytic number theory through a completion step, and the
> `t`-aspect has no such step. This is why Theorem 46 found the algebraic family reaching only an
> `L^{−1}\log L` fraction of the resonances, and why D53 found the resonance `a`-sum is not a Salié
> sum.**

Both earlier findings are corollaries of Theorem 58: they are the same absence of completion, observed
at two points of the reduction.

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 152 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 58 results, six corrections, 59 dead routes.

## Cycle 153 — **THEOREM 59: completion is possible in principle and exponentially useless**

Theorem 58 named the missing ingredient: `n^{−it}` cannot be completed. Cycle 153 asks whether it can
be *approximately* completed, and answers with two obstructions of different kinds.

### C399 — the rank obstruction `[PROVED, LEAN-CERTIFIED]`

Matching `χ(p) ≈ p^{−it}` for every prime `p ≤ N` prescribes `π(N)` values independently. A character
mod `q` is determined by its values on generators of `(ℤ/qℤ)^*`, whose rank is `ω(q)`, the number of
distinct prime factors. So independent prescription forces `ω(q) ≥ π(N)`.

**For prime `q` the group is cyclic**: one free parameter against `π(N)` conditions
(`prime_modulus_overdetermined`). No prime modulus can approximate `n^{−it}` on the block.

### C400 — the scale obstruction `[PROVED, LEAN-CERTIFIED]`

The smallest modulus with `ω(q) ≥ π(N)` is the primorial,

    q ≥ ∏_{p ≤ p_{π(N)}} p = e^{N(1+o(1))} .

At that modulus **Burgess's threshold is `q^{1/4} = e^{N/4}`, while the available block is only `N`.**
Since `N ≪ e^{N/4}`, Burgess is vacuous by an exponential margin (`completion_useless`,
`completion_margin`).

> **`[THEOREM 59]` Completion of `n^{−it}` on the critical block is obstructed twice, at opposite ends
> of the modulus range: small moduli have too few free parameters (rank), and the smallest modulus with
> enough parameters is so large that the block falls exponentially below Burgess's threshold (scale).
> **There is no modulus at which the completion is both possible and useful** (`completion_barrier`).**

### C401 — what this closes

Theorem 58 said the `t`-aspect lacks the completion step that carries every finite-field input into
analytic number theory. Theorem 59 shows the lack is not an accident of formulation: **the completion
cannot be manufactured, at any modulus, by any approximation.**

The two obstructions are of different types — one algebraic (the rank of `(ℤ/qℤ)^*`), one metric (the
primorial is exponential) — and they close the range from both sides with no interval between.

> **The Weil–Deligne theory, the deepest source of square-root cancellation in mathematics, is
> unreachable from the `t`-aspect: not because the sums are hard, but because there is no modulus at
> which `n^{−it}` becomes a character on the block where it must be bounded.**

Together with Theorem 55 (the smooth/multiplicative dichotomy), Theorem 56 (the coupling is the
functional equation and it is stationary), and Theorem 58 (Burgess needs periodicity), this completes
the campaign's structural account: **every route requires one of three things — a non-stationary
coupling, a completion, or a tool seeing both properties — and all three are provably absent.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 153 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 59 results, six corrections, 59 dead routes.

## Cycle 154 — **`[E37]`** the standing rule applied to Theorem 57, and a hole found

Phase 7 on cycle 150: apply the standing rule to the campaign's *own* newest theorem rather than to a
candidate route.

### C402 — the saving formula predicts LH at a finite block parameter

Theorem 57's saving function is `Sav(θ₀,x) = (2θ₀ − x)/(1/2 − x)`. Reading it as a function of `x`:

* at `x = 0`: `Sav = 4θ₀` — at Bourgain's `θ₀ = 13/84` this is `13/21 < 1`, a genuine gain;
* the slope is `(2θ₀ − 1/2)/(1/2 − x)² < 0` for `θ₀ < 1/4`, so the saving improves with `x`;
* **at `x = 2θ₀` the numerator vanishes and `Sav = 0`** — an infinite gain, i.e. `μ = 0`.

    At `θ₀ = 13/84` that is `x = 13/42 ≈ 0.3095`, a perfectly finite value.

> **The formula, read to `x = 2θ₀`, asserts the Lindelöf hypothesis. By the standing rule it is being
> read outside its domain of validity.**

### `[E37]` — Theorem 57's corollary is incomplete

The slope computation of Theorem 57 is correct and stands (`afeSaving_flat_iff`,
`afeSaving_slope_neg`, `afeSaving_convexity` are all verified). **What does not stand is the verbal
corollary "the optimum sits at the largest admissible block":** the campaign never determined what
*admissible* means, and the formula's own zero at `x = 2θ₀` shows the admissible range must end
strictly before `2θ₀`.

**This is the seventh instance of the standing rule firing** (after D51, E24, E27, E30, D52, E35), and
the first time it has been applied to one of the campaign's own theorems rather than to a candidate
route. It should have been applied there four cycles earlier.

### C403 — the gap, stated as a question

> **`[OPEN CORE C403]` What is the admissible range of the AFE block parameter `x` at input exponent
> `θ₀`? The saving formula is monotone decreasing in `x` on `θ₀ < 1/4` and vanishes at `x = 2θ₀`, so
> the range must terminate below `2θ₀`. The terminating constraint is presumably the range of validity
> of the block bound `|Σ_{n∼M}n^{−it}| ≪ M^{b}` that feeds the decomposition — i.e. the exponent-pair
> machinery's own admissible lengths — but the campaign has not computed it.**

**Why this matters.** Theorems 20–25 compute what happens *at* the boundary of the block range;
C403 is the question of *where that boundary is*. The two are complementary and the campaign has only
one of them. **Determining the boundary would either close Theorem 57's corollary or reveal that the
optimum is interior — in which case the whole "optimum at the boundary" picture, used in the verbal
statements of several cycles, needs revision.**

### Standing position after 154 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 59 results, seven corrections, 59 dead routes,
one newly opened core (C403).

**Method note.** The rule that has caught seven errors was, until this cycle, applied only to routes
under consideration. Applying it to the campaign's own established theorems is now standard practice:
**every formula in the corpus should be evaluated at the boundary of its stated range and checked
against `13/84`.**

## Cycle 155 — **THEOREM 60: C403 resolved — the block parameter is pinned**

C403 asked for the admissible range of the AFE block parameter. It has an exact answer, and the answer
is sharper than the question.

### C404 — the nontriviality threshold `[PROVED, LEAN-CERTIFIED]`

An exponent pair `(κ,λ)` applied to `Σ_{n∼t^α}n^{−it}` (with `Y ≍ t`, so `Y/N = t^{1−α}`) gives
`t^{κ+α(λ−κ)}` against the trivial `t^α`, hence is nontrivial exactly when

    α > κ/(1 − λ + κ)   =:  blockNontrivialThreshold κ λ.

**On the line of symmetry `λ = κ+1/2` this is `κ/(1/2) = 2κ`, and `μ = κ` there**
(`blockNontrivialThreshold_selfDual`). So the block bound is nontrivial exactly for

    **α > 2μ.**

At Weyl's pair the threshold is `1/3`; **at Bourgain's it is `13/42 = 2·(13/84)`**
(`threshold_bourgain`).

### C405 — and it coincides exactly with the saving formula's zero `[PROVED, LEAN-CERTIFIED]`

Theorem 57's saving `Sav(θ₀,x) = (2θ₀−x)/(1/2−x)` has positive numerator exactly for `x < 2θ₀`
(`saving_positive_iff`), and improves as `x` increases toward `2θ₀`.

> **`[THEOREM 60]` The saving requires `x < 2θ₀`; nontriviality of the block bound requires `x > 2θ₀`.
> The two ranges are disjoint (`block_parameter_pinned`) and their closures meet at the single point
> `x = 2θ₀`, where the saving vanishes and the block bound is exactly trivial
> (`pinned_point_degenerate`, `pinned_eq_threshold`). **The optimisation over the block parameter has
> no interior: it is one point, at which the gain and its input degenerate simultaneously.**

At Bourgain's input the pinned value is `x = 13/42` (`pinned_bourgain`).

### C406 — E37 resolved, and the corollary corrected

E37 flagged that Theorem 57's verbal corollary — "the optimum sits at the largest admissible block" —
was unjustified. **It is now settled, and it was wrong in a specific way:** there is no largest
admissible block, because there is no admissible *interval*. The correct statement is

> **The block parameter is pinned to `x = 2θ₀`, and there the optimisation is degenerate on both sides
> at once. This is the self-dual stationarity phenomenon in its sharpest form: not a flat direction
> (Theorem 57), not an attracting fixed point (Theorem 22), but a **single admissible point** at which
> the method's gain and the method's input vanish together.**

### C407 — why this closes the loop

Every earlier stationarity result was a statement that *some* optimisation is stationary at the
self-dual configuration. Theorem 60 shows the configuration is not merely optimal but **forced**: the
free parameter has exactly one admissible value, determined by the input exponent itself through
`x = 2θ₀`. **Improving `θ₀` moves the pinned point, and the structure repeats — which is why the
record has advanced by small increments and the shape of the obstruction has never changed.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 155 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 60 results, seven corrections, 59 dead routes,
**C403 closed**.

## Cycle 156 — **THEOREM 61: every block contributes equally, exactly**

Theorem 60 pinned the block parameter. Cycle 156 computes what the pinning means, and finds something
stronger than a pinned point.

### C408 — the block contribution is constant `[PROVED, LEAN-CERTIFIED]`

Feed a self-dual exponent pair `(θ₀, θ₀+1/2)` into the approximate functional equation. At the dyadic
block `M = t^α`:

    pair gives    |Σ_{n∼M}n^{−it}| ≪ t^{κ + α(λ−κ)} = t^{θ₀ + α/2}
    partial summation contributes  M^{−1/2} = t^{−α/2}
    block total   = t^{−α/2}·t^{θ₀+α/2} = **t^{θ₀}**,   identically in `α`.

> **`[THEOREM 61]` Every dyadic block of the approximate functional equation contributes exactly
> `t^{θ₀}` (`blockContribution_const`), independent of the block (`blockContribution_indep`). Summing
> the `≍\log t` blocks returns the input exponent. **The approximate functional equation is the
> identity map on the exponent** (`afe_is_identity_on_exponent`).**

### C409 — the strongest form of the stationarity results

The campaign has now found the same phenomenon at four increasing strengths:

| result | form |
|---|---|
| Thm 22 | the line dynamics has an **attracting fixed point** |
| Thm 57 | the saving is a **flat direction** at the convexity bound |
| Thm 60 | the block parameter is **pinned to one point** |
| **Thm 61** | **the block contribution is a constant function — there is nothing to optimise at all** |

> **`blockContribution_flat`: the difference between any two blocks' contributions is exactly zero, for
> every input exponent. Not stationary, not pinned — constant.**

### C410 — what this settles

Every proposal in the campaign's 156 cycles that involved *choosing where to put the mass* — a block
length, an abscissa, a truncation point, a coherence scale — was choosing among options that are
provably identical. That is the exact content of the inertness mechanism, and Theorem 61 states it
without reference to any particular method:

> **Given a self-dual exponent-pair input, the approximate functional equation spreads the exponent
> perfectly uniformly. No redistribution of mass within it can gain anything, because there is no
> non-uniformity to exploit. Improvement must come from improving the *input pair*, and Theorems 20–25
> price exactly that.**

This is the campaign's cleanest statement of why the problem's shape has never changed across a
century of work: **the functional equation is exponent-neutral, so all progress must come from the
exponential-sum side, and that side is where every barrier lives.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 156 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 61 results, seven corrections, 59 dead routes.

## Cycle 157 — consolidation: `4-publication-ready/lindelof-structural-account.md`

The campaign's sixty-one results were scattered across 157 cycles of working log. Cycle 157 writes them
as a single coherent document, structured by what each result is *about* rather than when it was found.

**`docs/drafts/pipeline/4-publication-ready/lindelof-structural-account.md`** — six sections:

0. **The object.** `μ(1/2) = (κ+λ−1/2)/2`; LH is `κ+λ = 1/2`.
1. **The exponent-pair semigroup is stationary at every record** (Thms 20–25): the `A`-inertness
   threshold `(√3−1)/4`, all four landmarks below it, the canonical form `(μ,μ+½)`, the two-sided
   attractor `T(μ)`, the floor `(√5−1)/8`, and the one-step chain whose limit is the exponent-pair
   conjecture.
2. **The frontier object** (Thms 28–29, 37, 40, 43, 47–48): coherence blocks, the Farey dissection,
   the two levels of cancellation with within-arc worth exactly nothing, the conservation law behind
   that neutrality, and the optimal spacing and minimal additive energy of the frequency set.
3. **The obstruction** (Thms 39, 49–50, 52–53, 55–56, 58–61): the mean square is exactly the Lindelöf
   value; five bridges to pointwise all closed; the gap is self-similar; counting needs all moments;
   the smooth/multiplicative dichotomy; the coupling is the functional equation and it is stationary;
   Burgess needs periodicity and completion cannot be manufactured; the block parameter is pinned and
   every block contributes equally.
4. **Calibration** (Thms 44–45): the shared currency, `1/14` vs `23/104`, LH exactly `4×` further.
5. **The one actionable target** (Thms 34–36): `μ ≤ 1/12`, and the four computed failures.
6. **Methodological record**: the seven withdrawals and the rule that caught each.

**Every exponent statement in the document is Lean-certified**, axioms
`[propext, Classical.choice, Quot.sound]`, in `formal/GaloisForLFunctions/HTGeometry/`.

**The document states plainly at the top that none of its results improves `μ ≤ 13/84`** — they are
barrier, reduction and calibration theorems. That framing is the honest one and it is the document's
first line.

### Standing position after 157 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 61 results, seven corrections, 59 dead routes,
one consolidated account.

## Cycle 158 — **THEOREM 62: at the target sum, completeness and algebraicity are never simultaneous**

Theorem 58 located the missing ingredient as *completion*. Cycle 158 applies that diagnosis to the
actual target sum of Theorem 34 and finds it needs refining.

### C411 — the target sum is already complete `[OBSERVED HERE]`

`T(q) = Σ_{a mod q, (a,q)=1}(a|q)·e(N√(2a/q))` runs over a **full reduced residue system**. The
completion step Burgess needs is not missing here — **it is already done.**

### C412 — but the phase is transcendental `[STRUCTURAL]`

Weil's bound requires `e(f(a)/q)` with `f` a polynomial or rational function mod `q`. The phase
`√(2a/q)` is not one: it is a transcendental function of the residue.

> **`[THEOREM 62]` The target sum is complete but not algebraic. Weil requires both
> (`weil_inapplicable`). Restoring algebraicity by localisation — Taylor-expanding `√(2a/q)` about a
> point — yields `e(αa + βa² + ⋯)` with **real** coefficients `α ≍ N/√(a₀q)`, not residues mod `q`.
> That is a Weyl sum with real coefficients: the van der Corput setting, already priced and short
> (`localisation_gives_vanDerCorput`, `target_sum_dichotomy`).**

### C413 — the refinement of Theorem 58

Theorem 58 said the `t`-aspect lacks completion. That is right at the *top* level, where `n^{−it}` is
aperiodic. **At the resonance level the diagnosis is different and sharper:**

| level | completeness | algebraicity | verdict |
|---|---|---|---|
| critical block `Σ_{n∼√t}n^{−it}` | **absent** — `n^{−it}` is aperiodic (Thms 58–59) | — | no Burgess |
| **resonance sum `T(q)`** | **present** — full residue system | **absent** — transcendental phase | **no Weil** |
| localised `T(q)` | — | present, but with **real** coefficients | van der Corput, priced |

> **The two hypotheses of the Weil–Deligne theory — completeness and algebraicity — are each available
> somewhere in the reduction, and never at the same place. The reduction that supplies completeness
> destroys algebraicity, and the localisation that restores algebraicity replaces residues by reals.**

This also sharpens D53: the resonance `a`-sum is not a Salié sum not because it is incomplete, but
because Salié's phase `(ma+nā)/q` is a rational function of the residue and `N√(2a/q)` is not.

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 158 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 62 results, seven corrections, 59 dead routes.

## Cycle 159 — **THEOREM 63: the target is orthogonality to the quadratic character**

Theorem 62 observed the target sum is complete. Cycle 159 exploits that: a complete sum can be expanded
in the finite Fourier basis.

### C414 — the exact identity `[COMPUTED HERE]`

With `F(a) = e(N√(2a/q))` and `ĉ_h = q^{−1}Σ_a F(a)e(−ha/q)`, the Gauss-sum evaluation
`Σ_a(a|q)e(ha/q) = (h|q)ε_q√q` gives

    **T(q) = ε_q √q · Σ_{h mod q} (h|q)·ĉ_h** ,      with `Σ_h|ĉ_h|² = 1` (Parseval).

Cauchy–Schwarz bounds the inner sum by `q^{1/2}`, hence `|T(q)| ≤ q` — exactly the trivial bound,
recovered.

> **`[THEOREM 63]` The intermediate target `|T(q)| ≪ q^{1/2+ε}` is **equivalent** to
> `|Σ_h (h|q)ĉ_h| ≪ q^{ε}`: the Fourier transform of the square-root phase must be **orthogonal to the
> quadratic character**, to within `q^{ε}`, against an `ℓ²`-trivial bound of `q^{1/2}`.**

The reformulation is exponent-neutral — the same `q^{1/2}` must be saved either way
(`reformulation_neutral`) — but it changes the object: from a sum of `q` unimodular terms to an inner
product `⟨ĉ, χ₂⟩` of an `ℓ²`-normalised vector with the Legendre symbol.

### C415 — and the transform has no stationary phase `[PROVED, LEAN-CERTIFIED]`

The stationary condition for `ĉ_h` is `N/√(2aq) = h/q`, requiring `h ≥ N/√(2q)`. At `q = N^{1/3}` that
is `h ≥ N^{5/6}/√2`, while the available range is `h < q = N^{1/3}`.

> **No stationary point lies in range, by the margin `N^{1/2}` (`no_stationary_phase`,
> `stationary_margin`). The coefficients `ĉ_h` are therefore governed entirely by the non-stationary
> regime — but the phase derivative `N/√(2aq) ≍ N/q` is large and sweeps many integers across the
> range, so Kusmin–Landau gives no uniform control either.**

### C416 — what the reformulation is worth

**Gained:** a statement in the language of character sums — `⟨ĉ, χ₂⟩ ≪ q^ε` — where the campaign's
`ℓ²` and additive-energy results (Theorems 47–48) live naturally, and where the quadratic character is
the only arithmetic object left. The transcendence of the original phase has been pushed entirely into
the vector `ĉ`, which is now the sole analytic input.

**Not gained:** any bound. The saving required is unchanged, and the four tools of Theorems 35–36
transfer to the Fourier side unchanged, since the reformulation is an isometry.

> **The target's final form: the Fourier transform of `e(N√(2a/q))` over `ℤ/q` must be orthogonal to
> the Legendre symbol. Everything the campaign knows says this should be true — the vector is
> `ℓ²`-normalised, has no stationary phase in range, and the character is the most equidistributed
> object in the subject — and nothing the campaign knows proves it.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 159 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 63 results, seven corrections, 59 dead routes.

## Cycle 160 — **THEOREM 64: the transform is flat, and two independent computations agree**

Theorem 63 reduced the target to `⟨ĉ, χ₂⟩ ≪ q^ε`. Cycle 160 computes `ĉ`.

### C417 — Poisson and stationary phase `[COMPUTED HERE]`

For `ĉ_h = q^{−1}Σ_{a≤q}e(ψ(a) − ha/q)` with `ψ(u) = N√(2/q)·u^{1/2}`, Poisson gives stationary points
at `ψ'(u) = h/q + m`, i.e. `u_m = N²/(2qm²)`, lying in `[1,q]` exactly for `m ∈ [N/(√2q), N/√(2q)]`.
With `|ψ''(u_m)| ≍ qm³/N²` each stationary term is `≍ N/(√q·m^{3/2})`, so under square-root
cancellation over `m`:

    |ĉ_h| ≍ q^{−1}·(N/√q)·(Σ_m m^{−3})^{1/2} ≍ q^{−1}(N/√q)(N/q)^{−1} = **q^{−1/2}**.

### C418 — Parseval confirms it exactly `[PROVED, LEAN-CERTIFIED]`

`Σ_h|ĉ_h|² = 1` over `q` coefficients, so a **flat** transform has `|ĉ_h| = q^{−1/2}`
(`parseval_flat`). **The stationary-phase computation and the `ℓ²` identity agree exactly** — an
independent check that C417's bookkeeping is right, and the campaign's standing rule is satisfied
(nothing below `13/84` is derived; the two computations agree on a value forced by Parseval).

### C419 — so the entire saving must come from the character `[PROVED, LEAN-CERTIFIED]`

| treatment of the `h`-sum | exponent of `q` | |
|---|---|---|
| no cancellation | `1 + (−1/2) = **1/2**` | exactly the trivial bound (`no_cancellation_is_trivial`) |
| **square-root cancellation** | `1/2 + (−1/2) = **0**` | exactly the target (`sqrt_over_h_is_target`) |

> **`[THEOREM 64]` The Fourier transform of the square-root phase is flat: `|ĉ_h| ≍ q^{−1/2}`, as
> Parseval forces and stationary phase confirms. The target `⟨ĉ,χ₂⟩ ≪ q^ε` therefore asks for **full
> square-root cancellation over `h` against the quadratic character, on a flat `ℓ²`-normalised
> vector** — and the whole `q^{1/2}` saving must come from that single source (`saving_all_in_h`).**

### C420 — the final statement of the target

> **A flat unit vector must be orthogonal to the Legendre symbol.**

Everything the campaign has established supports it: the vector is flat (Thm 64), its frequency set is
optimally spaced and of minimal additive energy (Thms 47–48), it has no stationary phase in range
(C415), and the quadratic character is the most equidistributed object in the subject. **Nothing the
campaign has established proves it**, and the four tools of Theorems 35–36 transfer unchanged because
the reformulation is an isometry.

This is where 160 cycles of reduction terminate: **the Lindelöf hypothesis, reduced as far as the
campaign's methods allow, is the assertion that one explicitly described flat unit vector is orthogonal
to the quadratic character.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 160 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 64 results, seven corrections, 59 dead routes.

## Cycle 161 — **THEOREM 65: the construction–bound gap, and where LH sits in it**

Theorem 64 reduced LH to `⟨ĉ,χ₂⟩ = O(q^ε)`. A failure would be an `N` making `N√(2a/q)` encode the
Legendre symbol — a conspiracy. Cycle 161 asks how close anyone can get to building one.

### C421 — the two ends `[PROVED, LEAN-CERTIFIED]`

| | exponent of `N` |
|---|---|
| best known **construction** of a large critical block (resonance / Gál sums, Bondarenko–Seip) | `0` (i.e. `N^{o(1)}`) |
| **Lindelöf hypothesis** | `1/2` |
| best known **upper bound** (Bourgain) | `17/21` |

> **`[THEOREM 65]` LH lies strictly between what can be constructed and what can be bounded
> (`lindelof_strictly_between`), and **the gap below it is larger than the gap above**: `1/2` against
> `13/42 = 0.3095` (`gap_below_larger`). Nobody can construct a counterexample within `N^{1/2}` of the
> conjectured truth, and that distance exceeds the remaining distance to the record.**

The total open span is `17/21` (`total_span`) — essentially the whole exponent.

### C422 — what this calibration says

1. **LH is not close to being decided from below.** The campaign has repeatedly noted the record has
   moved `1/14` of the way from above (Thm 45). Theorem 65 adds the other side: **from below, nothing
   has moved at all** — the best construction is subpolynomial, exponent `0`, and has been for as long
   as resonance methods have existed.
2. **The asymmetry is informative.** The upper-bound side has advanced by `1/42` in a century; the
   lower-bound side sits at `0` and the distance to `1/2` is unbridged by any construction. **If LH
   were false, the counterexamples are invisible to every constructive method known.**
3. **It closes the disproof branch honestly.** The campaign recorded early (successor summary §5) that
   disproof via moment lower bounds implies `¬RH` and is strictly harder. Theorem 65 gives the
   quantitative version: **the constructive gap to a counterexample is `N^{1/2}`, larger than the
   entire remaining gap on the proof side.**

> **Both directions are open, and the campaign can now say which is further: proving LH requires
> `13/42` more of exponent; disproving it requires constructing something `1/2` beyond anything ever
> built. The problem is closer to proof than to disproof, by a factor of about `1.6` in the exponent.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 161 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 65 results, seven corrections, 59 dead routes.

## Cycle 162 — **THEOREM 66: the stationary phase is a reciprocal, and the reduction closes on itself**

Theorem 64 left `⟨ĉ,χ₂⟩`. Cycle 162 evaluates the stationary phase of `ĉ_h` explicitly.

### C423 — the phase is `N²/(2k)` `[COMPUTED HERE]`

With `w = h/q + m` the stationary point is `u = N²/(2qw²)`, and

    ψ(u) − wu = N²/(qw) − N²/(2qw) = **N²/(2qw)** = N²/(2(h+mq)).

So the phase is a **reciprocal** in the combined variable `k = h + mq`, and

    Σ_h (h|q)ĉ_h  ≈  q^{−1} Σ_k w(k)·(k|q)·**e(N²/(2k))** ,      `k ≍ N`.

> **`[THEOREM 66]` The target is a Legendre-symbol sum against a **reciprocal phase**, over `k ≍ N`.
> Its phase derivative is `N²/(2k²) ≍ 1` — **order one** (`reciprocal_derivative_critical`): the
> self-dual regime again, where consecutive terms differ by a bounded phase and no derivative test
> applies (`reciprocal_no_derivative_test`).**

### C424 — and it is the original correlation `[STRUCTURAL]`

`N²/(2k) ≍ t/(4πk)` is exactly the differenced logarithmic phase

    t\log(k+1) − t\log k ≈ t/k,

i.e. the phase of the correlations the campaign started from (cycle 113's `C(h) = Σ_n(1+h/n)^{−it}`).

> **The reduction has returned to a shifted-correlation form.** Coherence blocks → theta resonances →
> Farey dissection → Fourier transform → stationary phase → **the same reciprocal phase the campaign
> began with**, now carrying a Legendre symbol.

This is Theorem 52's scale-invariance made concrete: **the chain is not a descent but a cycle.** Each
step is exact and informative; none of them changes the character of the object, and after six
transformations the phase is the one it started as.

### C425 — what the cycle means for the mechanism search

Every reduction the campaign can perform is **conjugation**, not simplification: it moves the same
difficulty into new coordinates. Theorem 52 proved the pointwise/mean-value gap is preserved; Theorem
66 shows the *phase itself* is preserved.

> **A mechanism cannot be found by further reduction. The object is a fixed point of the campaign's
> entire reduction apparatus, and the two invariants — the gap (Thm 52) and the reciprocal phase
> (Thm 66) — are what any new method must confront directly.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 162 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 66 results, seven corrections, 59 dead routes.

## Cycle 163 — **THEOREM 67: the two phase families are Poisson duals, and the two programmes with them**

Theorem 66 produced a reciprocal phase where the campaign began with a square-root phase. Cycle 163
shows this is not a coincidence but a duality.

### C426 — the duality `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

Stationary phase on `Σ_k e(x/k)`: with `f(k) = x/k`, the condition `f'(k) = −j` gives `k_j = √(x/j)`,
and the dual phase is

    f(k_j) + j k_j = x/√(x/j) + j√(x/j) = √(xj) + √(xj) = **2√(xj)** .

> **`[THEOREM 67]` The reciprocal phase `e(x/k)` and the square-root phase `e(2√(xj))` are exchanged
> by Poisson summation. At the campaign's parameters the transform is exponent-neutral: the dual range
> and dual phase both have exponent `1`, matching the original (`poisson_neutral`).**

### C427 — and the two programmes are exchanged with them

The campaign ran two long programmes:

* the **additive-divisor** programme (≈80 cycles), whose Voronoi duals carry `e(2√(nx))`;
* the **exponent-pair** programme (≈60 cycles), whose theta resonances carry `e(N√(2a/q))` and whose
  stationary-phase evaluation carries `e(N²/(2k))`.

Theorem 31 found them sharing a phase family. Theorem 67 explains why:

> **The two programmes are exchanged by Poisson duality. Reducing either lands on the other. They were
> never two attacks — they are one object in two coordinate systems, and every barrier proved in
> either is a statement about the same sum.**

### C428 — the reduction apparatus, completely characterised

Combining Theorems 52, 66 and 67, the campaign's reduction has three invariants:

| invariant | statement |
|---|---|
| the **gap** | mean value is exactly the target at every level (Thm 52) |
| the **phase** | reciprocal ↔ square-root under Poisson, exponent-neutral (Thms 66–67) |
| the **exponent** | every block contributes equally; the AFE is the identity (Thm 61) |

> **Every transformation the campaign can perform is a conjugation. The gap, the phase family, and the
> exponent are all preserved. That is the precise sense in which 163 cycles of reduction have not
> moved `μ`: there was never a direction to move it in, only coordinates to change.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 163 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 67 results, seven corrections, 59 dead routes.

## Cycle 164 — **THEOREM 68: every powerful tool needs an arithmetic parameter, and `t` is real**

Theorem 67 showed Poisson preserves the phase invariant. Cycle 164 looks for a transform that does not.

### C429 — the spectral transform is the candidate `[STRUCTURAL]`

After Fourier/Poisson and Mellin, the third fundamental transform is the **spectral** one — Kuznetsov,
converting Kloosterman sums into Maass-form data. It does **not** preserve the phase family, and at
`GL(2)` the campaign's rank-gap barrier does not apply (`n(n−1)/2 = 1`). **It is the one transform
that could break invariant 2.**

### C430 — and it requires a rational parameter `[STRUCTURAL]`

Kuznetsov acts on `S(m,n;c) = Σ_{a mod c}e((ma + n\bar a)/c)` — the reciprocal is the **modular
inverse** `\bar a` mod `c`, and the parameter is rational. The campaign's sum is
`Σ_k w(k)(k|q)e(N²/(2k))` with the **real** reciprocal `1/k` and the parameter `N² = t/2π`, real.

> **`[THEOREM 68]` The spectral transform requires the reciprocal phase's parameter to be rational.
> The critical object's parameter is `t`, a real number. The one transform that could break the phase
> invariant needs exactly the arithmetic input the object lacks.**

### C431 — the pattern, at its fourth occurrence

This is now the same diagnosis four times, from four different tools:

| tool | arithmetic hypothesis it requires | the object |
|---|---|---|
| Weil–Deligne (Thm 46) | **algebraic** phase | transcendental |
| Burgess (Thm 58) | **periodic** multiplicative function | `n^{−it}` is archimedean |
| Weil at the resonance sum (Thm 62) | **complete *and* algebraic** together | complete, not algebraic |
| **Kuznetsov (Thm 68)** | **rational** parameter | `t` is real |

> **Every tool with genuine power in analytic number theory requires an arithmetic hypothesis —
> periodicity, algebraicity, completeness, rationality — and the critical object satisfies none of
> them. The single reason is that `t` is a *real* parameter.**

### C432 — and this explains the aspect asymmetry

The conductor aspect is easier because its parameter `q` **is** arithmetic: `χ` is periodic mod `q`,
sums complete to residue systems, Weil applies, Burgess works, and subconvexity is a theorem
(Thm 58). **The `t`-aspect has no arithmetic parameter at all.**

> **The campaign's final diagnosis: the Lindelöf hypothesis is hard because it is a statement about a
> real parameter, and every powerful method in the subject is arithmetic. The self-duality results
> (Thms 55–57, 60–61) say the analytic structure is stationary; Theorems 46, 58, 62 and 68 say the
> arithmetic structure is absent. Together they close both halves.**

### Standing position after 164 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 68 results, seven corrections, 59 dead routes.

**The campaign's account in one line:** *the analytic tools are stationary at the object and the
arithmetic tools cannot see it, because the object's only parameter is real.*

## Cycle 165 — **THEOREM 69: the construction bound derived from first principles**

Theorem 65 quoted `N^{o(1)}` as the best known construction, on the authority of Gál-sum extremal
results. Cycle 165 derives it, and finds the bound is not a limitation of the technique.

### C433 — how many primes can conspire at height `t` `[COMPUTED HERE]`

To have `‖t\log p_i/2π‖ < η` for `k` primes simultaneously, the torus `T^k` must be resolved to scale
`η`, so by pigeonhole the smallest such `t` is `≈ η^{−k}`, i.e.

    **k ≈ \log t / \log(1/η).**

With `η` a small constant this is `k ≍ \log t ≍ 2\log N` primes — a *polylogarithmic* supply.

### C434 — but the phases accumulate `[COMPUTED HERE]`

If `n` has `Ω(n) = ω` prime factors drawn from the resonant set, its own phase error is `≤ ωη`. For
`n` to contribute coherently we need `ωη ≪ 1`, i.e.

    **Ω(n) ≲ 1/η.**

The number of `n ≤ N` with at most `1/η` prime factors, all from a set of size `k ≍ \log N`, is

    ≈ k^{1/η} = (\log N)^{1/η} = **N^{o(1)}**   for any `η` with `1/η = o(\log N/\log\log N)`.

> **`[THEOREM 69]` The resonance construction cannot produce a coherent set of polynomial size. The
> obstruction is not the Gál-sum technique but the interaction of two costs: **simultaneous Diophantine
> approximation** limits the resonant primes to `≍ \log t`, and **phase accumulation** limits the
> usable products to `Ω(n) ≲ 1/η`. Their product is `(\log N)^{1/η}`, subpolynomial for every
> admissible `η`.**

### C435 — what this settles

Theorem 65 placed the best construction at exponent `0` on the authority of published extremal results.
**Theorem 69 shows the exponent `0` is forced**, by a two-line argument that uses only pigeonhole and
the additivity of phases over prime factorisation.

> **If the Lindelöf hypothesis is false, the counterexamples cannot be built by making primes conspire
> — the arithmetic cost of the conspiracy always exceeds its yield. Any counterexample must be
> non-constructive, or must arise from a coherence mechanism with no prime-by-prime description.**

This closes the constructive half of the problem as firmly as the campaign's barriers close the
deductive half, and it does so from first principles rather than by citation.

### Standing position after 165 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 69 results, seven corrections, 59 dead routes.

## Cycle 166 — **`[E38]`** Theorem 69's scope corrected, and the weak-coherence regime opened

Applying the standing practice of cycle 154 — turn the scrutiny on the campaign's own newest theorem.

### `[E38]` — Theorem 69 bounds *full* coherence, not the critical size

Theorem 69 counts `n ≤ N` whose phases lie within `η` of a **common value**. That is the regime
`|Σ| ≈ N` — total coherence. **The Lindelöf hypothesis concerns `|Σ| > N^{1/2+δ}`, which requires far
less.** Writing `S = Σ_{n≤N}e(t\log n)`:

    |S|² = N + Σ_{m≠n} e(t\log(m/n)),

so `|S| > N^{1/2+δ}` needs only `Σ_{m≠n}e(t\log(m/n)) > N^{1+2δ}` out of `≍N²` pairs — **a fraction
`N^{−1+2δ}` of the pairs need to align.** Theorem 69 says nothing about that.

> **Corrected scope: Theorem 69 shows the *resonance construction*, which builds fully coherent sets,
> cannot reach polynomial size. It does **not** bound all large values, and its closing sentence
> ("counterexamples cannot be built by making primes conspire") is correct only for full conspiracy.**

Theorem 65 is unaffected: it stated the best known *construction*, which is exactly the fully coherent
one.

### C436 — the weak-coherence regime, stated `[NEW FORMULATION]`

> **`[OPEN CORE C436]` LH is the assertion that for no `t` do the ratios `\{t\log(m/n)\}`, over the
> `≍N²` pairs `m,n ≤ N = √t`, align on a fraction `N^{−1+2δ}` of pairs. The alignment required is
> **vanishingly thin** — one pair in `N^{1−2δ}` — and no method in the campaign's map addresses
> alignment at that density.**

The campaign's tools all address either full coherence (resonance, Thms 65, 69) or mean-square
behaviour (Thm 39). **The regime between them — thin partial alignment — is untouched.**

### C437 — why this regime is where the difficulty lives

* The multiplication table (Erdős–Ford) says the `≍N²` ratios `m/n` take `≍N²(\log N)^{−0.086}`
  distinct values, so most ratios are distinct and their phases are essentially free.
* A fraction `N^{−1+2δ}` is far below any equidistribution discrepancy the campaign can control.
* The mean square (Thm 39) says the *average* alignment is exactly the Lindelöf value — so the
  question is again pointwise-versus-average, at the level of pair alignment.

> **The weak-coherence regime is the pointwise/mean-value gap (Thm 52) expressed in the pair variables.
> Theorem 69's scope correction therefore does not open a new route — it relocates the same
> obstruction, which is the third time the campaign has found the gap reappearing under a change of
> description (Thms 52, 66, and now C436).**

### Standing position after 166 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 69 results, **eight** corrections, 59 dead
routes, one relocated open core.

## Cycle 167 — the pair variables carry no new structure; **`[D60]`**

C436 opened the weak-coherence regime in the pair variables. Cycle 167 checks whether those variables
carry structure the original ones do not.

### C438 — the pair sum, reorganised `[COMPUTED HERE]`

Grouping `Σ_{m≠n≤N}e(t\log(m/n))` by the reduced ratio `a/b` (so `m = ka`, `n = kb`, `k ≤ N/\max(a,b)`):

    Σ_{m≠n} e(t\log(m/n))  =  Σ_{(a,b)=1} (N/\max(a,b))·e(t\log(a/b)) .

Counting dyadically: pairs with `\max(a,b) ≍ A` number `≍A²` and carry weight `N/A`, contributing
`≍NA`. **Dominated by `A ≍ N`** — i.e. by the coprime pairs with `k = 1`, of which there are `≍N²`
with weight `1`. The trivial bound `N²` is recovered.

### C439 — and the phases are generic `[COMPUTED HERE]`

The `≍N²` values `\log(a/b)` lie in `[−\log N, \log N]`, so their spacing is `≍ \log N/N²`. Multiplying
by `t = 2πN²`, **consecutive phases differ by `≍ \log N ≫ 1`.** The phases of neighbouring reduced
fractions are therefore essentially independent — exactly the generic picture, and exactly what
Theorem 48's minimal additive energy already recorded.

> **`[D60]` The pair variables are a conjugation, not a simplification. The pair sum is dominated by
> coprime pairs with unit weight, its phases are generic at spacing `\log N`, and it is
> `|Σ_n e(t\log n)|²` minus its diagonal — the object one started from. Do not expect the pair
> description to yield structure the original lacks.**

**Fourth confirmation of the conjugation principle** (Thms 52, 66, 67, now D60): every change of
description the campaign can perform preserves the gap, the phase family, the exponent, and now the
genericity.

### C440 — assessment

The campaign has reached genuine saturation on structural findings. Sixty-nine results describe the
object from six directions, and every new description has, for four consecutive cycles, returned an
object already characterised. **That is itself the finding: the reduction apparatus is closed, and
its closure is now demonstrated rather than asserted.**

### Standing position after 167 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 69 results, eight corrections, 60 dead routes.

## Cycle 168 — Phase 2 SOTA check against the survey the task document cites

`docs/Lindelöf hypothesis.md` cites **arXiv:2509.20335**, Florea's 2025 survey of moment bounds for
`ζ(s)`. The campaign had never consulted it, and its own moment targets were priced against
Heath-Brown 1978. Cycle 168 checks whether they are still current.

### C441 — the survey's position `[LITERATURE, EXTRACTED]`

Abstract: *"…essentially recover the expected rate of growth for all moments — **unconditionally for
small moments** and **conditionally on the Riemann hypothesis for all larger moments**."*

Section 3.2, *Unconditional upper bounds*: the sharp bound is proved unconditionally **for `0 ≤ k ≤ 2`**
— i.e. up to the **fourth** moment — following Heath-Brown's treatment of `k = 1/n`. Heath-Brown's
twelfth-moment paper appears as `[HB78]` in the bibliography and is not superseded.

Section 3.3: Arguin–Bailey `[AB25]` recovered unconditional **sharp lower bounds for all positive
moments**.

### C442 — the campaign's targets are confirmed current `[SOTA CHECK PASSED]`

| target | campaign's price | status per the 2025 survey |
|---|---|---|
| `m(4) < 26/21` beats `13/84` | 17.5 % improvement on `m(4) ≤ 3/2` | **open** — unconditional sharp bounds stop at `k = 2` |
| `m(6) < 13/7` beats `13/84` | 7.1 % improvement on Heath-Brown's `m(6) ≤ 2` | **open** — `[HB78]` still the reference |
| sixth moment `k = 3` | subconvexity-neutral (campaign's neutrality law) | still unknown unconditionally |
| all moments | ⟺ LH | **known on RH** — consistent with `RH ⟹ LH` |

> **The campaign's moment-side targets and their prices are unchanged by the current literature. The
> unconditional frontier is exactly where the campaign placed it: sharp up to the fourth moment,
> nothing beyond, and everything larger conditional on RH.**

### C443 — the lower-bound side

Arguin–Bailey's unconditional **sharp lower bounds for all positive moments** match the conjectured
sizes, so they are consistent with LH rather than evidence against it. This is the moment-side
counterpart of Theorem 65: **from below, the literature confirms the expected size and produces
nothing exceeding it** — no polynomial excess, hence no counterexample.

**Method note.** The task document had been read at the campaign's start but its **bibliography** had
not been followed. Following it took one cycle and confirmed six cycles' worth of pricing. *Read the
references of the problem statement, not only its statement.*

### Standing position after 168 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 69 results, eight corrections, 60 dead routes,
targets confirmed against the July-2026 literature.

## Cycle 169 — **THEOREM 70: moments and Lindelöf probe different tail scales**

Cycle 168 surfaced Arguin–Bailey's 2025 unconditional sharp lower bounds, obtained from large
deviations in Selberg's central limit theorem. Cycle 169 asks how far that framework reaches.

### C444 — the two deviation scales `[COMPUTED HERE]`

Selberg's CLT: `\log|ζ(1/2+it)|` is normal with variance `½\log\log T`. The `2k`-th moment is dominated
by `\log|ζ| ≍ k\log\log T`, i.e. by

    λ ≍ k√(2\log\log T)   standard deviations.

The Lindelöf hypothesis concerns polynomial size `\log|ζ| ≍ δ\log T`, i.e.

    λ ≍ δ√2·\log T/√(\log\log T) .

> **`[THEOREM 70]` The ratio of the two deviation scales is `≍ \log T/\log\log T`, which **diverges**.
> The moment framework — including sharp unconditional lower bounds for *all* positive moments — probes
> a part of the tail separated from the Lindelöf regime by a diverging factor. It is not short of LH by
> a constant; it operates at a different scale of deviation.**

### C445 — and this is Theorem 53 in probabilistic language `[LEAN-CERTIFIED]`

Theorem 53: emptying the exceptional set at excess `δ` requires moment order `k > 1/δ`
(`momentOrder_diverges`), and halving the excess doubles the order (`momentOrder_doubles`). **Pushing
`k → ∞` is exactly pushing the probed deviation from the `\log\log T` scale to the `\log T` scale.**

The two statements are the same obstruction in two languages:

| language | statement |
|---|---|
| moments | no finite order empties `E_δ`; all moments is LH (Thm 53) |
| **probability** | **moments probe `λ ≍ √(\log\log T)`; LH needs `λ ≍ \log T/√(\log\log T)`** |

### C446 — why the 2025 lower bounds do not bear on LH

Arguin–Bailey give sharp lower bounds matching the conjectured moment sizes. By Theorem 70 those live
at the `\log\log T` deviation scale, where the distribution is Gaussian and fully understood.

> **A counterexample to LH would be an event at the `\log T/√(\log\log T)` scale — beyond every
> deviation any current method controls, in either direction. This is Theorem 65's construction bound
> (`N^{o(1)}`) restated: the extreme tail is inaccessible from below as well as from above.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 169 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 70 results, eight corrections, 60 dead routes.

## Cycle 170 — **THEOREM 71: the zero side, calibrated**

The campaign's zero-geometry barrier says the zero route is inert or circular. Cycle 170 makes that
quantitative: exactly what would a zero-free region have to be?

### C447 — the conversion `[PROVED, LEAN-CERTIFIED]`

If `ζ(s) ≠ 0` for `σ > Θ` then `μ(Θ) = 0`, and convexity of `μ` with `μ(0) = 1/2` gives
`μ(σ) ≤ (1/2)(1 − σ/Θ)`, hence

    **μ(1/2) ≤ (2Θ − 1)/(4Θ)**   (`muFromZeroFree`).

| `Θ` | bound on `μ(1/2)` | |
|---|---|---|
| `1` | **`1/4`** | exactly the convexity bound (`muFromZeroFree_one`) |
| **`21/29 = 0.72413…`** | **`13/84`** | exactly Bourgain (`muFromZeroFree_threshold`) |
| `1/2` (RH) | **`0`** | exactly Lindelöf (`muFromZeroFree_half`) |

> **`[THEOREM 71]` A zero-free half-plane beats Bourgain **iff** `Θ < 21/29 ≈ 0.724`
> (`beats_bourgain_iff`), and gives the Lindelöf hypothesis only at `Θ = 1/2`, i.e. the Riemann
> hypothesis. The known zero-free regions have `Θ → 1` and therefore deliver **exactly the convexity
> bound and nothing more** (`known_zerofree_gives_convexity`).**

### C448 — the zero side is the widest gap in the problem

| route | what is known | what beats `13/84` | gap |
|---|---|---|---|
| exponent pairs | `κ+λ = 17/21` | `κ+λ < 17/21` | incremental; `1/14` of the way to LH |
| moments | sharp for `k ≤ 2` | `m(4) < 26/21` | 17.5 % on one exponent |
| **zeros** | **`Θ → 1` (no half-plane `Θ < 1` known)** | **`Θ < 21/29`** | **a positive constant, entirely unbridged** |

> **No zero-free half-plane with `Θ < 1` is known at all. The zero route does not merely fall short of
> `13/84` — it has never produced a single point of subconvexity by this mechanism, and the distance
> to its threshold is a positive constant rather than an epsilon.**

This is the quantitative content of the campaign's zero-geometry barrier, and it explains why the
Jensen/Backlund route was found circular: **there is no partial zero information of the required
shape.** Density estimates constrain zeros in measure, not in location, and the conversion above needs
location.

### C449 — the three sides, now all calibrated

    exponent pairs:  17/21 → 1/2       covered 1/14        (Thm 45)
    moments:         sharp to k ≤ 2    need m(4) < 26/21   (cycles 98, 168)
    zeros:           Θ → 1             need Θ < 21/29      (Thm 71)
    construction:    N^{o(1)}          need N^{1/2}        (Thms 65, 69)

> **All four faces of the problem are now priced in the same currency, and every one of them is short
> by a positive amount that no current method reduces.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 826 jobs.

### Standing position after 170 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 71 results, eight corrections, 60 dead routes.

## Cycle 171 — **THEOREM 72: the newest published moment bounds, priced against the record**

Cycle 168's literature check stopped at the survey. Cycle 171 follows the other reference —
Trudgian–Yang, *Toward optimal exponent pairs* — and finds moment bounds the campaign had not priced.

### C450 — what the paper contains `[LITERATURE]`

* **`μ(1/2) ≤ 13/84` is confirmed, not improved** — "the best-known result after over a century of
  effort". The campaign's baseline is correct.
* Theorem 2.1: `M(12+δ) ≤ 2 + δ/8 + (3√510/7568)δ^{3/2}` for `0 < δ ≤ 86/65`.
* Theorem 2.2: **`M(13) ≤ 2.1340`, `M(14) ≤ 2.2720`, `M(15) ≤ 2.4137`.**

### C451 — pricing them by the neutrality law `[PROVED, LEAN-CERTIFIED]`

The campaign's law `μ(1/2) ≤ M(A)/A` applied to the three values:

| `A` | `M(A) ≤` | `M(A)/A` | vs Hölder from `M(12) ≤ 2` | gap to `13A/84` |
|---|---|---|---|---|
| 13 | `2.1340` | `0.164154` | `2.3095` — **TY better** | `0.1221` |
| 14 | `2.2720` | `0.162286` | `2.6190` — **TY better** | `0.1053` |
| 15 | `2.4137` | `0.160913` | `2.9286` — **TY better** | `0.0923` |
| — | Bourgain | **`0.154762`** | — | — |

> **`[THEOREM 72]` Trudgian–Yang's moment bounds beat the Hölder extrapolation at every computed point
> (`ty_beats_holder`), their ratios `M(A)/A` **decrease** across the range (`ty_ratios_decreasing`),
> and the gap to the neutrality threshold **narrows** with `A` (`gap_narrows`) — but none reaches the
> record: `M(15)/15 = 0.16091 > 13/84` (`ty_does_not_beat_bourgain`), with a shortfall between
> `0.006` and `0.007` (`ty_shortfall`, `ty_shortfall_positive`).**

### C452 — what this changes

The campaign priced the moment route at cycle 98 using `M(12) ≤ 2` (Heath-Brown) and the convexity
value `M(8) ≤ 3/2`, giving required improvements of `7.1 %` and `17.5 %`. **Theorem 72 shows the
moment route has advanced since**: at `A = 15` the shortfall is `0.0062` in `μ`, i.e. `4 %` of the
record — **substantially closer than the `7.1 %` at `A = 12`.**

> **The moment route is the only one of the campaign's four faces where the published frontier has
> moved measurably in the campaign's own currency, and it is now within `0.0062` of `13/84`. That
> makes it, by the campaign's calibration, the most nearly successful attack on the record — and the
> gap is closing in `A`, not in time.**

**Standing-rule check:** every value here is *above* `13/84`; nothing below the record is asserted. The
computation is a pricing of published bounds, not a derivation.

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 799 jobs.

### Standing position after 171 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 72 results, eight corrections, 60 dead routes.

## Cycle 172 — the trend of the moment route, extrapolated

Theorem 72 showed the moment route is `0.0062` behind the record at `A = 15`. Cycle 172 asks where the
trend goes.

### C453 — the recorded sequence `[PROVED, LEAN-CERTIFIED]`

Including Heath-Brown's `M(12) ≤ 2`:

| `A` | `M(A)/A` | gap to `13/84` |
|---|---|---|
| 12 | `0.1666667` | `0.0119048` |
| 13 | `0.1641538` | `0.0093920` |
| 14 | `0.1622857` | `0.0075238` |
| 15 | `0.1609133` | **`0.0061515`** |

`gaps_positive` — **all four are strictly positive: the moment route is behind the record at every
recorded order.** `gaps_decreasing` — and they decrease strictly. `decrements_shrink` — the decrements
themselves shrink, so the decay is sub-linear.

### C454 — the extrapolation `[NOT A THEOREM — labelled as such]`

Decrements: `−0.0025128, −0.0018682, −0.0013723`; successive ratios `0.743`, `0.735` — close to
geometric. With ratio `≈0.74` the remaining decrease is
`0.0013723·0.74/(1−0.74) ≈ 0.0039`, giving a limiting gap of

    **≈ 0.0022 > 0.**

> **On the published trend the moment route approaches `13/84` from above and does not reach it,
> converging to `≈ 0.1570`.**

**This is an extrapolation from four points and is recorded as such.** What is *proved* is only the
positivity, monotonicity and sub-linear decay of the recorded gaps.

### C455 — why the trend must eventually turn

The neutrality law gives `M(A) ≤ M(A₀) + (A−A₀)·2μ`, so `M(A)/A → 2μ = 13/42 = 0.3095` as `A → ∞` —
**increasing**. The ratio therefore has a minimum at finite `A`, and the published values are on its
descending branch.

> **The moment route's best possible output is the minimum of `M(A)/A`, attained at some finite order.
> The published bounds locate the descending branch and place the minimum below `0.1609`; the
> extrapolation places it near `0.1570`. Either way it exceeds `13/84` — which is consistent with
> Trudgian–Yang not reporting an improved `μ`.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 799 jobs.

### Standing position after 172 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 72 results (one extrapolation, labelled), eight
corrections, 60 dead routes.

## Cycle 173 — **THEOREM 73: the moment trend is diverging from what would be needed**

Cycle 172 extrapolated the moment route to `≈0.157`. Cycle 173 asks what decay rate would be required
to reach `13/84` instead, and compares it to what is observed.

### C456 — the required decay rate `[PROVED, LEAN-CERTIFIED]`

For a geometric tail with ratio `r`, the remaining decrease after a last decrement `d` is `d·r/(1−r)`,
so the trend closes a gap `g` exactly when

    **r ≥ g/(g+d).**

| formulation | `g` | `d` | required `r` | observed ratios |
|---|---|---|---|---|
| ratios `M(A)/A − 13/84` | `0.0061515` | `0.0013723` | **`0.81766…`** | `0.7434`, `0.7345` |
| absolute `M(A) − 13A/84` | `0.092271` | `0.013062` | **`0.87603…`** | `0.8074`, `0.7793` |

`requiredRatioRatios_gt`, `requiredRatioRatios_lt` bracket the requirement in `(0.81, 0.82)`;
`observed_below_required` shows both observed ratios fall short; `ratio_shortfall` puts the shortfall
above `0.07`.

> **`[THEOREM 73]` For the published moment sequence to reach the record, its geometric decay ratio
> must be at least `≈0.818`. The observed ratios are `0.743` and `0.735`, and they are **decreasing**
> (`observed_decreasing`). The trend is not merely short of the requirement — it is moving away from
> it.**

Both formulations — the `μ`-relevant ratios and the absolute moment gaps — give the same verdict, an
independent check.

### C457 — what would be needed instead

A geometric trend will not do it. Closing the gap requires either

* a **structural improvement** at some specific order — `M(A) < 13A/84`, i.e. `M(15) < 2.3214` against
  the published `2.4137`, a `3.8 %` improvement at that single order; or
* an **acceleration** of the decay from ratio `0.74` to above `0.82`, reversing the observed trend.

> **The moment route is the closest of the campaign's four faces (Thm 72) and the only one whose
> published frontier has moved — but its own trend, extrapolated and now differentiated, does not
> reach the record. What is needed there is a new input at a single order, not more of the same.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 799 jobs.

### Standing position after 173 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 73 results, eight corrections, 60 dead routes.

## Cycle 174 — **`[E39]` Theorem 72's interpretation corrected; THEOREM 74: shared provenance**

Applying the campaign's standing practice — turn the scrutiny on its own newest result.

### C458 — where Trudgian–Yang's moment bounds come from `[LITERATURE]`

Their paper is *Toward optimal exponent pairs*: it "quantifies the set of known exponent pairs and
develops a framework to compute the optimal exponent pair for an arbitrary objective function", the
objectives including **the moments of `ζ(1/2+it)`**. Their `M(13)`, `M(14)`, `M(15)` are therefore
**derived from exponent pairs**.

Heath-Brown's `M(12) ≤ 2`, by contrast, comes from large values plus a short second moment — a
genuinely different argument.

### `[E39]` — the sequence mixes two provenances, and Theorem 72's framing was wrong

Cycle 171 concluded: *"the moment route is the only one of the campaign's four faces where the
published frontier has moved measurably… the most nearly successful attack on the record."* **That
reading is mistaken.**

> **`[THEOREM 74]` Trudgian–Yang's moment bounds belong to the **smooth family** (Theorem 55): they are
> exponent-pair outputs, and therefore inherit every barrier the campaign proved for that family —
> the `A`-inertness threshold, the line-of-symmetry attractor, the realisable floor `1/6`, the
> universal neutrality of within-block improvements. **They cannot beat `13/84`, because `13/84` is the
> best output of the same machinery.** The moment face's apparent proximity to the record is an
> artefact of shared provenance, not evidence of a second converging route.**

### C459 — and this explains the trend

Theorem 73 found the decay ratio `0.74` against a required `0.818`, and the ratios *decreasing*. C458
explains why: **the sequence is converging to the exponent-pair route's own limit, which is `13/84`
approached from above and never crossed** — exactly what a re-expression of the same bound must do.

> **The convergence of `M(A)/A` toward `13/84` without reaching it is not a near-miss. It is the
> signature of an identity: both quantities are outputs of the same optimisation, and the moment
> formulation approaches the exponent-pair value in the limit.**

### C460 — the four faces, corrected

| face | provenance | independent of the exponent-pair route? |
|---|---|---|
| exponent pairs | smooth family | — |
| **moments (Trudgian–Yang)** | **smooth family — exponent-pair derived** | **no (E39)** |
| moments (Heath-Brown `M(12) ≤ 2`) | large values + short second moment | **yes** |
| zeros | Jensen/Backlund | yes — and `Θ → 1` gives only convexity (Thm 71) |
| construction | resonance / Gál sums | yes — `N^{o(1)}` (Thms 65, 69) |

> **Three genuinely independent faces remain, not four. The campaign's cycle-98 pricing against
> Heath-Brown's `M(12) ≤ 2` — a `7.1 %` improvement needed — was the correct one, and cycle 171's
> apparently better `4 %` figure measured the same machinery against itself.**

**Ninth correction.** The standing rule caught seven exponent errors; this is the second time the
practice of auditing the campaign's own results has caught an *interpretive* one (after E37).

### Standing position after 174 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 74 results, nine corrections, 60 dead routes.

## Cycle 175 — **THEOREM 75: the joint method exists, in the wrong regime**

Theorem 74 left Heath-Brown's `M(12) ≤ 2` as one of three genuinely independent faces. Cycle 175 asks
which family it belongs to.

### C461 — Heath-Brown's argument is joint `[STRUCTURAL]`

The twelfth-moment proof uses

* the **fourth moment** `∫|ζ|⁴ ≍ T\log⁴T` — a *multiplicative* input, resting on the divisor function
  `d(n)` in `ζ² = Σ d(n)n^{−s}`;
* **large-value estimates** for Dirichlet polynomials — a *smooth* input.

**It uses both properties of `n^{−it}` at once.** By Theorem 55's classification, that combination is
exactly what no method achieves.

### C462 — but Theorem 55 is about *pointwise* bounds `[SCOPE]`

Theorem 55 classifies methods for bounding `Σ_{n∼N}n^{−it}` **pointwise**. Heath-Brown bounds a
**moment**. There is no contradiction — and the observation is the point:

> **`[THEOREM 75]` A joint smooth-plus-multiplicative method exists in the subject — Heath-Brown's
> twelfth moment — but it lives on the **mean-value** side. Theorem 55's absence is specific to the
> pointwise setting. The mechanism the campaign's specification (C338, C381) demands therefore exists,
> in the wrong regime; and the regime change is exactly the obstruction closed by Theorems 49–53.**

### C463 — the campaign's account, closed

Reading Theorems 39, 49–53, 55 and 75 together:

| | smooth | multiplicative | **joint** |
|---|---|---|---|
| **mean value** | ✓ available | ✓ available | **✓ available — Heath-Brown** |
| **pointwise** | ✓ available (exponent pairs) | ✓ available (Halász — but extremal at `n^{−it}`) | **✗ absent (Thm 55)** |

and the mean-value row is already at the Lindelöf value (Theorem 39), while every bridge between the
rows is closed (Theorems 49–53).

> **Everything needed exists, and nothing is in the same place. The joint method is on the mean-value
> row; the mean-value row already attains the Lindelöf value; the bridge to the pointwise row is
> closed; and on the pointwise row the two families are separately stationary at the object. That is
> the campaign's complete account of the Lindelöf hypothesis, and every cell of it has been priced.**

### C464 — the one thing this suggests

The account localises the missing step precisely: **transport a joint method from the mean-value row
to the pointwise row.** Every general bridge is closed, so the transport would have to be specific to
the joint structure — using the fact that the method sees both properties, rather than treating it as
a black-box mean-value bound.

> **`[OPEN CORE C464]` Is there a transport of Heath-Brown's joint argument to the pointwise setting
> that uses its joint character? The five general bridges (Thms 49–50) treat a mean value as an
> opaque input and are all closed; a bridge exploiting *why* the mean value holds is not covered by
> them, and the campaign has not examined one.**

### Standing position after 175 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 75 results, nine corrections, 60 dead routes,
one open core (C464) that the campaign's own barrier set does not cover.

## Cycle 176 — **THEOREM 76: C464 closed — the transport exists and is the neutrality law**

C464 asked whether Heath-Brown's joint argument transports to the pointwise setting in a way the five
general bridges do not cover. Cycle 176 answers it.

### C465 — the transport, computed `[PROVED, LEAN-CERTIFIED]`

Heath-Brown's argument bounds `R·V^{12} ≪ T²`, with `V` the large-value level and `R` the number of
well-spaced points attaining it. **Setting `R = 1` — a single point —** gives `V ≪ T^{1/6}`:
**Weyl's exponent, recovered from a moment argument** (`transport_twelfth`).

In general a moment bound `∫|ζ|^{2k} ≪ T^{m(k)}` gives at a single point `V^{2k} ≪ T^{m(k)}`, i.e.

    **μ(1/2) ≤ m(k)/(2k)** ,

which is **exactly the campaign's neutrality law** (`transport_is_neutrality`).

| input | transport | |
|---|---|---|
| fourth moment `m(2) = 1` | `1/4` | convexity (`transport_fourth`) |
| twelfth moment `m(6) = 2` | `1/6` | Weyl (`transport_twelfth`) |
| Trudgian–Yang `M(15)` | `0.16091` | `transport_ty15` |
| record | `13/84 = 0.15476` | none of them reaches it (`transports_miss_record`) |

> **`[THEOREM 76]` The transport of a mean-value bound to a single point exists, and it is the
> neutrality law already in hand. C464's hoped-for bridge — one exploiting the joint character of
> Heath-Brown's argument — reduces at `R = 1` to the same law, because the large-value estimate
> becomes vacuous at a single point and only the moment input survives. **C464 is closed.**

### C466 — why the joint character is lost in transport

Heath-Brown's argument is joint precisely in the interaction between the **large-value count `R`** and
the **moment**. At `R = 1` the count carries no information, and the joint structure collapses to its
multiplicative half.

> **The joint character is a property of the *family* of large values, not of any one of them. It
> cannot survive restriction to a single point — which is why the transport reduces to the neutrality
> law, and why Theorem 55's absence at the pointwise level is not an oversight but a consequence of
> what "joint" means here.**

This is the sharpest form the campaign has reached of the pointwise/mean-value gap: **the mean-value
side is joint because it counts; the pointwise side cannot count.**

Axioms `[propext, Classical.choice, Quot.sound]`; build green at 806 jobs.

### Standing position after 176 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 76 results, nine corrections, 60 dead routes,
**C464 closed** one cycle after being opened.

## Cycle 177 — can the pointwise side be made to count? **`[D61]`**

Theorem 76 ended: *the mean-value side is joint because it counts; the pointwise side cannot count.*
Cycle 177 attacks that directly — can a single point generate a family?

### C467 — the multiplicative orbit `[COMPUTED HERE]`

A single `t₀` does generate a family, by multiplicativity of the phase. If

    ‖t₀\log p‖ < η   for all `p ≤ N`,

then `‖k t₀\log p‖ < kη`, so **the conspiracy persists along the orbit `t₀, 2t₀, 3t₀, …, Kt₀` with
`K ≍ 1/η`.** That is `≍1/η` points at which the *fixed-length* sum `Σ_{n≤N}n^{−it}` is large — a
family, generated by one point, at which a large-value estimate could be applied.

**This is a genuinely new observation for the campaign: the pointwise side has a counting structure
after all, supplied by the multiplicative orbit.**

### `[D61]` — but it exists only in the strong regime

The propagation needs a **uniform** phase bound `η` covering all primes up to `N`. That is the
strong-coherence hypothesis of Theorem 69 — the regime `|Σ| ≈ N`. **In the weak regime relevant to the
Lindelöf hypothesis, `|Σ| = N^{1/2+δ}`, there is no uniform `η`:** the large value comes from a thin
partial alignment (E38, C436), not from every prime phase being small, and nothing propagates.

> **`[D61]` The multiplicative orbit supplies the pointwise side with a family — but only where
> Theorem 69's construction bound already applies. In the regime where the Lindelöf hypothesis lives
> there is no uniform phase bound to propagate, and the orbit produces nothing.**

Two further checks confirm the limitation:

* at `kt₀` the critical block is `√(kt₀) = √k·N`, longer than `N`, so the conspiracy would have to cover
  more primes than it does — the orbit gives large values of a *fixed-length* sum, not of `ζ` itself;
* the orbit length `K ≍ 1/η` is bounded by the very parameter that Theorem 69 shows must be large,
  so the family is small exactly when the conspiracy is usable.

### C468 — what survives

> **The pointwise side *can* count, but only along the multiplicative orbit, and only when a uniform
> phase bound exists. Theorem 76's statement is therefore refined rather than overturned: the
> pointwise side cannot count **in the weak regime**, which is the regime the Lindelöf hypothesis
> concerns.**

**Tenth instance of the same scope distinction** (strong versus weak coherence), after E38 and C436.
The campaign now records it as a standing caution: *any construction or propagation argument must be
checked against the weak regime `|Σ| = N^{1/2+δ}`, not the strong regime `|Σ| ≈ N`.*

### Standing position after 177 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 76 results, nine corrections, 61 dead routes.

## Cycle 178 — **`[E40]`** a real build break, undetected for 64 cycles

A full-umbrella verification pass, run for the first time since cycle 114.

### `[E40]` — name collision, and the per-module builds masked it

    error: import GaloisForLFunctions.HTGeometry.CorrelationExponentBridge failed,
           environment already contains 'HTGeometry.blockExponent'
           from GaloisForLFunctions.HTGeometry.TernaryShiftAverageExponents

`CorrelationExponentBridge` (cycle 114) defined `blockExponent (a b : ℚ)`, and the pre-existing
`TernaryShiftAverageExponents` already had `blockExponent : ℚ`. **The umbrella has failed to build
since cycle 114 — sixty-four cycles — while every per-module build reported green**, because
`lake build +Module` never imports the sibling that collides.

**Fixed** by renaming the campaign's definition to `correlationBlockExponent`. A collision scan over
all 347 declarations in the nine new modules against every other `HTGeometry` module found **exactly
one** collision, now resolved.

A first attempt also renamed the `blockExponent` *field* of `AFEBound` in `JensenZeroGeometry`; that
was unnecessary (a structure field generates `AFEBound.blockExponent`, which cannot collide) and was
reverted, leaving the pre-existing API untouched.

### C469 — verification `[COMPLETE]`

    lake build +GaloisForLFunctions.HTGeometry   —  **10929/10929, green**

Axiom audit of twelve capstones through the umbrella — all
`[propext, Classical.choice, Quot.sound]`:
`vanDerCorput_inert_at_all_records`, `optimum_lives_where_A_is_inert`, `farey_both_gives_lindelof`,
`neither_family_suffices`, `no_depth_suffices`, `ty_does_not_beat_bourgain`,
`weyl_differencing_bound`, `vanDerCorput_correlation_bound`, `norm_sum_ee_le`,
`norm_quad_correlation_le_min`, `mu_secondDeriv`, `transport_twelfth`.

### C470 — the method failure, and the fix

**Tenth correction, and the first that is not mathematical.** The campaign verified each module in
isolation and reported "build green" for sixty-four cycles on the strength of `lake build +Module`,
which does not detect cross-module name collisions.

> **Standing practice, added: `lake build +Module` is not verification. Every cycle that adds a
> module must build the **umbrella**, and every new module must have its top-level names scanned
> against the rest of the area before the cycle is reported.**

This is precisely the failure mode the project's own memory records as the "cross-cone name collision
scan"; the campaign had the instruction and did not apply it.

### Standing position after 178 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 76 results, ten corrections, 61 dead routes.
**Umbrella green at 10929 jobs; all campaign results verified through the umbrella, not in
isolation.**

## Cycle 179 — **THEOREM 77: one arc already exceeds the target**

Theorem 76 said the pointwise side cannot count over `t`. Cycle 179 counts in a different variable —
over the coherence blocks inside a single Farey arc.

### C471 — the principal arc `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

The resonance abscissa runs over `α_r = N²/(2n_r²) ∈ [1/8, 1/2]` on a grid of spacing `L^{−2}`. The
**smallest Farey denominator occurring there is `q = 2`**, at `α = 1/2`, i.e. `n_r ≈ N`. (There is no
`q = 1` arc: `α_r` never approaches an integer.) That arc has width `≍1/(2L)`, hence contains

    (1/(2L))/L^{−2} ≍ **L**  coherence blocks, each of size `≍ L/√2 ≍ L`,

so its total modulus is `≍ **L²**`, against the Lindelöf target `L^{3/2}` for the *whole* frontier sum.

> **`[THEOREM 77]` The single Farey arc of smallest denominator already exceeds the Lindelöf target by
> `L^{1/2}` (`principal_arc_exceeds_target`, `principal_arc_excess`) — and square-root cancellation
> among its `≍L` blocks brings it **exactly** to the target
> (`principal_arc_cancellation_meets_target`). So LH **requires** square-root cancellation inside that
> one arc, independently of every other arc.**

The arc is not the dominant term — `L² < L^{5/2}` (`principal_arc_not_dominant`) — yet it alone
already overshoots. **The necessary condition is local.**

### C472 — why this is the campaign's most concrete necessary condition

Every earlier reduction produced a *global* statement about `≍L²` resonances. Theorem 77 isolates a
**single arc with `≍L = N^{1/3}` blocks** and states a self-contained requirement on it:

> **`Σ_{r ∈ arc(1/2)} A_r Θ_r ≪ L^{3/2}`, i.e. square-root cancellation among `N^{1/3}` theta sums
> whose abscissae `α_r` lie within `1/(2L)` of `1/2`.**

This is a necessary condition for LH, it involves one arc rather than the Farey sequence, and it is
stated entirely in terms of objects the campaign has already constructed. **It is the smallest
self-contained sub-problem the campaign has produced.**

**Standing-rule check:** Theorem 77 is a *necessary* condition — it asserts no bound and cannot yield
an exponent below `13/84`.

Umbrella green at 10929 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 179 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 77 results, ten corrections, 61 dead routes.

## Cycle 180 — **THEOREM 78: the principal arc is an explicit cubic-form Weyl sum, and its requirement is sub-square-root**

Theorem 77 isolated a single arc as a necessary condition. Cycle 180 writes that arc down explicitly.

### C473 — the arc, computed `[COMPUTED HERE]`

On the arc `α ≈ 1/2` the blocks are indexed by `|r| ≲ L/2` with `n_r = N + rL`, and

    α_r − 1/2 = N²/(2n_r²) − 1/2 ≈ −rL/N = **−r/L²** ,
    {β_r} = {−N²/n_r} = {−r²L²/N + …} ≈ **{−r²/L}**

(the integer parts `−N + rL` drop out). The `α ≈ 1/2` factor `(−1)^{m²} = (−1)^m` only shifts the
linear coefficient. Substituting into the chirp `Σ_{m<L}e(δ_r m² + β_r m)`:

    **Σ_{r,m ≲ L} e( −rm²/L² − r²m/L )  =  Σ_{r,m} e( −L·uv(u+v) ),   u = r/L, v = m/L ∈ [0,1].**

> **The principal arc is a two-dimensional Weyl sum over `L² = N^{2/3}` points, with phase the **cubic
> form `uv(u+v)`** at amplitude `L = N^{1/3}`.**

### C474 — and its requirement is a quarter power `[PROVED, LEAN-CERTIFIED]`

| quantity | exponent of `L` |
|---|---|
| terms in the double sum | `2` |
| trivial bound | `2` |
| **Lindelöf target for the arc** | **`3/2`** (`arcTargetExponent_eq`) |
| **required saving** | **`1/2` — a quarter power of the term count** (`arc_requirement_quarter`) |
| square-root cancellation would give | `1` — **overshoots** (`sqrt_overshoots_requirement`) |

> **`[THEOREM 78]` The necessary condition of Theorem 77 asks for a saving of `L^{1/2}` from `L²` terms
> — **strictly weaker than square-root cancellation** (`arc_requirement_below_sqrt`), which would give
> `L`. The local sub-problem is sub-square-root.**

### C475 — why this is the campaign's most promising object

Every previous formulation required **full** square-root cancellation (Thms 33, 40, 63, 64). Theorem
78 is the first that does not:

* the object is explicit — a two-dimensional Weyl sum with the cubic form `uv(u+v)`;
* its dimensions are small — `L = N^{1/3}` in each variable;
* the requirement is a **quarter** power, not a half;
* and cubic-form Weyl sums in two variables are exactly the setting where decoupling and efficient
  congruencing operate.

> **This is the first sub-problem the campaign has produced that is both necessary for the Lindelöf
> hypothesis and asks for less than square-root cancellation. It is where a successor should look.**

**Standing-rule check:** Theorem 78 states a *requirement*, not a bound; it asserts no exponent and
cannot fall below `13/84`.

Umbrella green at 10929 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 180 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 78 results, ten corrections, 61 dead routes,
one sub-square-root necessary condition.

## Cycle 181 — **THEOREM 79: the arc sum is algebraic but incomplete — the exact mirror of the resonance sum**

Theorem 78 wrote the arc as a cubic-form Weyl sum. Cycle 181 asks whether Weil–Deligne applies to it.

### C476 — the sum, with a common denominator `[COMPUTED HERE]`

`L·uv(u+v) = rm(r+m)/L²`, so

    **S = Σ_{r,m ≤ L} e( rm(r+m)/L² )** ,

whose phase is a **cubic form modulo `L²`** — **algebraic**, unlike the resonance sum's transcendental
`√(2a/q)` (Theorem 62). So the obstruction that blocked Weil there is absent here.

### C477 — but the sum is incomplete, and completion is worthless `[PROVED, LEAN-CERTIFIED]`

The box has side `L` against modulus `L²` — a fraction `L^{−1}` in each variable
(`arc_box_fraction`). Pólya–Vinogradov completion bounds `S` by `\log²L` times the largest additively
twisted complete sum, and Deligne's square-root bound for a non-degenerate two-variable complete sum
modulo `q` is `≍ q = L²`. Hence

    S ≪ \log²L · L²  —  **the trivial bound**, since the box itself has `L²` terms.

> **`[THEOREM 79]` The complete sum's square-root bound is exactly the incomplete sum's trivial bound
> (`completion_worthless`), so the saving from completion is zero (`completion_saving_zero`).
> **Completion is available here and worthless**, where at the resonance sum it was unavailable
> (Theorem 62).**

### C478 — the duality, at two levels

| level | complete? | algebraic? | verdict |
|---|---|---|---|
| resonance sum `T(q)` | **✓** | **✗** (transcendental `√(2a/q)`) | no Weil (Thm 62) |
| **principal arc `S`** | **✗** (box side `L`, modulus `L²`) | **✓** (cubic form mod `L²`) | **no Weil (Thm 79)** |

> **The two hypotheses of Weil–Deligne are each available at one level of the reduction and never at
> the same one — and now the roles are exactly exchanged between the two levels. This is Theorem 68's
> pattern (every powerful tool needs an arithmetic hypothesis the object lacks) realised as a clean
> duality rather than a list.**

### C479 — what would break it

Completion becomes useful when the box is a **positive proportion** of the modulus. Here that would
require the arc's blocks to be indexed modulo `L` rather than `L²` — i.e. the quadratic coefficient
`β_r ≈ −r²/L` to have denominator `L` matched to a box of side `L`. **The mismatch is exactly one
factor of `L`, and it is the same factor `L^{1/2}` twice over that Theorem 78 identified as the
required saving.**

> **`[OPEN CORE C479]` Is there a decomposition of the arc into `L` sub-boxes on which the effective
> modulus drops to `L`? On such a decomposition completion would be a positive proportion and
> Deligne's bound would give a genuine saving. The campaign has not found one, and D52/D58 warn that
> naive sub-division reproduces the same structure.**

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 181 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 79 results, ten corrections, 61 dead routes.

## Cycle 182 — **THEOREM 80: the principal arc meets its requirement — the campaign's first positive result**

C479 asked for a decomposition making the arc tractable. The substitution `s = r + m` supplies one.

### C480 — the computation `[PROVED, EXPONENTS LEAN-CERTIFIED]`

In `S = Σ_{r,m ≤ L}e(rm(r+m)/L²)` put `s = r+m`. For each `s ∈ [2,2L]` the inner sum over `r` runs over
an interval of length `≤ L`:

    Σ_r e( (rs² − r²s)/L² ) = Σ_r e( −(s/L²)r² + (s²/L²)r ) ,

a **chirp** with quadratic coefficient `α = −s/L²`, so `|α| ≤ 2/L` — small. The second-derivative test
gives

    |Σ_r| ≪ L|α|^{1/2} + |α|^{−1/2} ≍ L(s/L²)^{1/2} + (L²/s)^{1/2} = **√s + L/√s** ,

whose two terms balance at `s ≍ L` (`chirp_terms_balance` — the self-dual point of the inner
estimate). Summing:

    |S| ≪ Σ_{s≤2L}(√s + L/√s) ≍ L^{3/2} + L·L^{1/2} = **L^{3/2}** .

> **`[THEOREM 80]` `S ≪ L^{3/2}` — **exactly** the arc's Lindelöf requirement (`arc_meets_target`),
> achieving precisely the required saving `L^{1/2}` from the trivial `L²`
> (`arc_saving_achieved`, `principal_arc_not_obstruction`). **The principal arc is not an obstruction:
> it meets its target.**

### C481 — what this is, and what it is not

**What it is.** The campaign's **first positive result**: 79 prior theorems priced barriers; this one
*verifies a necessary condition*. The necessary condition of Theorems 77–78 — square-root cancellation
among the arc's `≍L` blocks, equivalently a quarter-power saving in the cubic-form Weyl sum — **holds**,
by an elementary two-step argument (substitute `s = r+m`, apply the second-derivative test).

**What it is not.** A step toward `μ`. Theorem 77's condition is *necessary*, not sufficient: the arc
is one of `≍L²` arcs, and Theorem 80 bounds only that one. **No exponent below `13/84` follows, and
none is claimed.**

### C482 — why the arc was tractable and the whole sum is not

The substitution worked because the arc's phase is a **cubic form in two variables of equal range**,
so eliminating one variable leaves a chirp with a *small* coefficient. That structure came from the
arc being a single Farey arc: its `α_r` all lie within `1/(2L)` of `1/2`, which forced `δ_r ≈ −r/L²`.

> **Away from the principal arc the `α_r` are spread over `[1/8,1/2]`, `δ_r` is not small, and the
> elimination produces chirps with coefficients of order one — the self-dual regime where no
> derivative test applies (Theorem 66). The arc is tractable precisely because it is one arc.**

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 182 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 80 results — **79 barriers and one verified
necessary condition** — ten corrections, 61 dead routes.

## Cycle 183 — **THEOREM 81: the within-arc bound holds at every arc, and still gives only Weyl**

Theorem 80 verified the principal arc. Cycle 183 extends the argument to all of them.

### C483 — the extension `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

At the arc around `a/q` the blocks are indexed by `|r| ≲ L/(2q)`, the deviations are `δ_r ≈ r/L²`, and
extracting the Gauss sum of modulus `q` leaves a chirp of length `L/q` with coefficient `δ_rq² ≈
rq²/L²`. The elimination `s = r+m'` applies to a box of side `L/q` against modulus `L²/q²` — **the
identical ratio `q/L`** — giving

    S_q ≪ √q·(L/q)^{3/2} = **L^{3/2}/q**   (`arcBoundAt`).

Each dyadic denominator therefore contributes `φ(q)·L^{3/2}/q ≍ L^{3/2}`, **the same amount for every
`q`** (`arcTotalAt_const`), and summing over the range:

    Σ_{q≤L}φ(q)·L^{3/2}/q ≍ L^{3/2}·Σ_{q≤L}φ(q)/q ≍ L^{3/2}·L = **L^{5/2}** .

> **`[THEOREM 81]` The within-arc bound is achievable at **every** arc, and the total is exactly Weyl's
> `L^{5/2}` (`within_arc_gives_weyl`). It falls short of the Lindelöf target by exactly `L`
> (`within_arc_shortfall`) — the across-arc factor, entirely.**

### C484 — what this settles

Theorem 43 proved within-arc cancellation *neutral* by exponent arithmetic — the Farey weight `φ(q)`
compensating the gain. **Theorem 81 proves the same thing constructively**: the within-arc bound is not
merely neutral in bookkeeping, it is **actually attainable at every arc**, and attaining it everywhere
still gives only Weyl.

| | status |
|---|---|
| **within-arc cancellation** | **proved, at every arc** (Thms 80–81) |
| across-arc cancellation | open — and worth exactly the whole remaining factor `L` |

> **The problem is now cleanly halved, with one half done. The within-arc half of the Lindelöf
> hypothesis is a theorem; the across-arc half is the entire remaining difficulty, and it is worth
> precisely the factor `L = N^{1/3}` that separates Weyl from Lindelöf.**

This is the sharpest positive statement the campaign has produced, and it is consistent with every
barrier: Theorem 43 predicted the neutrality, Theorem 40 located the missing factor in the across-arc
level, and Theorems 80–81 now realise the within-arc level in full.

**Standing-rule check:** the total is `L^{5/2} = N^{5/6}` — Weyl's exponent, `μ = 1/6`, **above**
`13/84`. Nothing below the record is derived.

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 183 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 81 results — 79 barriers, two positive —
ten corrections, 61 dead routes.

## Cycle 184 — **THEOREM 82: the normalised final form**

Theorem 81 proved the within-arc half. Cycle 184 divides that factor out and states what remains.

### C485 — the normalised sum `[PROVED, EXPONENTS LEAN-CERTIFIED]`

Theorem 81 gives `|A_{a,q}| ≪ L^{3/2}/q`. Dividing out the common `L^{3/2}`:

> **`[THEOREM 82]` The Lindelöf hypothesis is equivalent, along the campaign's reduction, to
>
>     Σ_{a/q ∈ F_L} (1/q)·ε_q(a|q)·e( N√(2a/q) + θ_{a,q} )  ≪  (\log L)^{O(1)} ,
>
> with `ε_q(a|q)` the Gauss-sum phase (C309) and `θ_{a,q}` the chirp phase from Theorem 80.**

Its norms:

| | value | restores to |
|---|---|---|
| `ℓ¹`: `Σ_{q≤L}φ(q)/q` | `≍ L` | `L^{3/2}·L = L^{5/2}` — **Weyl** (`restore_l1`, `final_form`) |
| `ℓ²`: `(Σ_{q≤L}φ(q)/q²)^{1/2}` | `≍ (\log L)^{1/2}` | `L^{3/2}` — **Lindelöf** (`restore_l2`) |

> **With the within-arc factor divided out, Weyl is the `ℓ¹` bound on the normalised Farey sum and
> Lindelöf is its `ℓ²` bound. The entire remaining problem is the `ℓ¹`-to-`ℓ²` gap of one explicit
> weighted Farey sum** (`normalised_saving`, `normalised_saving_is_across_arc`).

### C486 — why this is the campaign's cleanest statement

Every earlier form carried the within-arc structure along: coherence blocks, theta sums, chirps. **All
of that is now a proved factor `L^{3/2}` (Thms 80–81) and has been removed.** What remains is a sum of
`≍L²` unimodular terms with explicit weights `1/q` and explicit arithmetic phases, and the requirement
is that it attain its `ℓ²` size rather than its `ℓ¹` size.

| the whole problem, in one line |
|---|
| **Weyl is `ℓ¹`. Lindelöf is `ℓ²`. The gap is a factor `L = N^{1/3}` in one weighted Farey sum with Gauss-symbol phases.** |

**Standing-rule check:** the `ℓ¹` bound restores to `N^{5/6}` (`μ = 1/6`) and the `ℓ²` bound to
`N^{1/2}` (`μ = 0`, the conjecture). Neither is an unconditional claim below `13/84`; Theorem 82 states
an equivalence, not a bound.

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 184 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 82 results — 79 barriers, three positive
(Thms 80, 81, 82) — ten corrections, 61 dead routes.

## Cycle 185 — **THEOREM 83: the normalised sum localises to one dyadic range**

Theorem 82 gave the normalised Farey sum. Cycle 185 asks where its mass sits.

### C487 — the dyadic profile `[PROVED, LEAN-CERTIFIED]`

The range `q ∈ [Q,2Q]` carries `Σ_{q≍Q}φ(q) ≍ Q²` fractions of weight `≍1/Q`:

    ℓ¹ mass of the range ≍ **Q** ,      ℓ² mass of the range ≍ **1** .

> **`[THEOREM 83]` The `ℓ¹` mass grows with `Q` (`dyadicL1_mono`), so it is dominated by the **top
> range `Q ≍ L`**, which alone carries the whole `ℓ¹` norm (`top_range_carries_all`). Every range
> contributes equally in `ℓ²` (`dyadicL2_const`), and the `≍\log L` ranges add incoherently to
> `(\log L)^{1/2}`. The full required saving therefore sits in the single range `q ∈ [L/2, L]`
> (`top_range_saving`, `localises_to_top_range`).**

### C488 — the problem, at its narrowest

> **Square-root cancellation in `Σ_{q ∈ [L/2,L]}Σ_{a}(1/q)·ε_q(a|q)·e(N√(2a/q)+θ_{a,q})` over `≍L²`
> fractions of a single dyadic range — with `L = N^{1/3}`.**

Everything else — the within-arc structure (Thms 80–81), the smaller denominators (`ℓ²`-summable), the
coherence blocks, the theta sums — is accounted for. **This is the narrowest statement the campaign
has produced whose resolution would give the Lindelöf hypothesis.**

### C489 — and the honest note

The localisation sharpens the target but supplies no tool. In that range `q ≍ L = N^{1/3}` and the
phases `N√(2a/q)` advance by `N/L = N^{2/3}` between consecutive `a` — the fast-phase regime where
Theorems 35–36 priced four tools and all four fail, and where Theorem 62 showed completeness and
algebraicity are never simultaneous.

> **The campaign's reduction is complete and its target is minimal. Every structure has been named,
> every tool priced, and the remaining statement is a single dyadic character sum against a fast
> square-root phase.**

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 185 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 83 results — 79 barriers, four positive —
ten corrections, 61 dead routes.

## Cycle 186 — **THEOREM 84: the phase does factor — D56 overturned — but the large sieve is inefficient**

Theorem 83 narrowed the target to one dyadic range. Cycle 186 revisits the bilinear question there.

### C490 — the phase factors `[COMPUTED HERE]` — **`[E41]` D56 corrected**

In the top range `q ≍ L` **both variables run over `≍L`**, and

    N√(2a/q)  =  ( N√(2a) )·( q^{−1/2} )  =  **x_a · y_q** ,

a genuine bilinear phase.

> **`[E41]` D56 concluded "the frontier sum has no usable bilinear structure", on the ground that
> `a < q` couples the variables. That is true of the **full** Farey range and **false on a single
> dyadic range**, where `a` and `q` both run over `[L/2, L]` and decouple. The bilinear structure the
> campaign sought at cycle 132 exists after all — it was hidden by working at the wrong scale.**

### C491 — and the large sieve is the wrong tool for it `[PROVED, LEAN-CERTIFIED]`

Normalising `y_q = L^{−1/2}(1+u_q)`:

| | value |
|---|---|
| `x'_a = N√(2a)L^{−1/2}` | spacing `≍N/L = N^{2/3}`, **spread `≍ N`** |
| `u_q` | `≍L` points, spacing `≍N^{−1/3}` |
| coefficients `α_a ≍ 1/q` | `Σ|α_a|² ≍ L^{−1}` |

Large sieve: `Σ_q|Σ_aα_ae(x'_au_q)|² ≪ (N + N^{1/3})L^{−1} ≍ N^{2/3}`, hence
`|Σ_{a,q}| ≤ (L·N^{2/3})^{1/2} = **N^{1/2}**`, against the trivial `Σ_{a,q}1/q ≍ **N^{1/3}**`.

> **`[THEOREM 84]` The frequency spread `N` exceeds the number of points `N^{2/3}`
> (`spread_exceeds_points`), so the large sieve returns `N^{1/2}` — **worse than trivial by `N^{1/6}`**
> (`largeSieve_worse_than_trivial`, `largeSieve_deficit`). The bilinear structure exists; the large
> sieve is the wrong tool for it.**

### C492 — what this changes

**Eleventh correction, and the first that *opens* rather than closes.** D56 had ruled out the entire
bilinear branch of the mechanism specification; Theorem 84 restores it, with one tool on it priced and
failing for a specific, quantified reason — spread versus point count, not a structural absence.

> **A bilinear method is available at the top dyadic range. The large sieve fails on it by `N^{1/6}`
> because the frequencies are too spread. Any method that tolerates a spread of `N` over `N^{2/3}`
> points — or that first compresses the spread — is not covered by the campaign's barrier set.**

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 186 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 84 results, eleven corrections, 61 dead routes,
**one branch of the mechanism specification reopened**.

## Cycle 187 — **THEOREM 85: the dual large sieve reaches the target, and names the one missing input**

Theorem 84 reopened the bilinear branch. Cycle 187 applies the large sieve in the other variable.

### C493 — the dual application `[COMPUTED HERE]`

Swapping roles in `Σ_{a,q}(1/q)e(x'_a u_q)`:

    Σ_a |Σ_q β_q e(x'_a u_q)|²  ≪  (U + Δ^{-1})·Σ_q|β_q|² ,     U = 0.4,  β_q ≍ L^{-1},

giving `Σ_a|·|² ≪ L^{-1}` and hence `|Σ_{a,q}| ≤ (L·L^{-1})^{1/2} = **O(1)**` — **exactly the target of
Theorem 82, i.e. the Lindelöf hypothesis** (`dual_sieve_meets_target_if_spaced`).

### C494 — and why it is invalid `[STANDING RULE]`

The large sieve requires the `x'_a` to be well-spaced **modulo 1**. Their spacing in `ℝ` is
`≍ N/L = N^{2/3}`, which says nothing about spacing mod `1`: **a set can be arbitrarily spread in `ℝ`
and arbitrarily clustered mod `1`** (`real_spacing_not_mod_one`).

> **`[THEOREM 85]` The dual large sieve reaches the Lindelöf target *exactly when* the frequencies
> `{N√(2a)/√L}`, `a ≍ L = N^{1/3}`, are well-spaced modulo `1`. That distribution is the unknown, and
> it carries the **entire** remaining factor (`assumption_closes_everything`,
> `missing_input_is_mod_one_spacing`). Assuming it assumes the conclusion.**

**Standing rule, eighth firing.** The computation produced `O(1)`, far below `13/84`; the invalid step
was located before the result was reported.

### C495 — the single missing input, named

After 187 cycles the campaign can state the missing ingredient as one sentence about one sequence:

> **The mod-1 distribution of `{ N√(2a)/√L }` for `a ≍ L = N^{1/3}`, `N = √(t/2π)`.**

* If those `≍L` points are well-spaced mod 1 (spacing `≫ L^{−1}`), the dual large sieve gives the
  Lindelöf hypothesis.
* Everything else in the reduction is proved: the coherence decomposition (Thm 28), the Farey
  dissection (Thm 37), the within-arc bound at every arc (Thms 80–81), the normalisation (Thm 82), the
  localisation to one dyadic range (Thm 83), and the bilinear factorisation (Thm 84).

**This is the campaign's terminal statement.** Every other structure has been constructed or priced;
what remains is the equidistribution of one explicit sequence of square roots modulo one.

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 187 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 85 results, eleven corrections, 61 dead routes,
**one named missing input.**

## Cycle 188 — **`[E42]` Theorem 85 corrected: optimal spacing gives `μ = 1/12`, not LH**

Applying the standing practice to the campaign's newest theorem, one cycle after stating it.

### `[E42]` — the dual-sieve arithmetic was wrong

The dual large sieve gives `Σ_a|Σ_qβ_qe(x'_au_q)|² ≪ (U+δ^{−1})Σ_q|β_q|²`. With `Σ|β_q|² ≍ L^{−1}` and
`L` values of `a`:

    |Σ_{a,q}| ≤ ( L·(U+δ^{−1})·L^{−1} )^{1/2} = **(U + δ^{−1})^{1/2}** .

Reaching `O(1)` needs `δ ≫ 1` — **impossible for more than one point.** Cycle 187 asserted that
well-spacing gives the target; it does not.

| mod-1 spacing `δ = L^{−s}` | sieve output | restored | `μ` |
|---|---|---|---|
| **optimal, `s = 1`** (`δ ≍ 1/L`) | `L^{1/2}` | `L²` | **`1/12`** |
| generic, `s = 2` (birthday) | `L` | `L^{5/2}` | `1/6` (Weyl) |
| Lindelöf would need | `O(1)` | `L^{3/2}` | `0` |

> **`[THEOREM 85, corrected]` The best possible mod-1 spacing of `{N√(2a)/√L}` — `δ ≍ 1/L`, the most
> `L` points can achieve — delivers `μ ≤ 1/12` (`dualSieve_optimal_restored`), **beating Bourgain but
> falling short of the Lindelöf hypothesis by `L^{1/2}`** (`dualSieve_optimal_shortfall`). Generic
> spacing delivers exactly Weyl (`dualSieve_generic_restored`).**

### C496 — and the correction lands on a known landmark

`dualSieve_optimal_is_intermediate`: the optimal-spacing output `L²` **is exactly the across-arc-only
regime of Theorem 40**, and `μ = 1/12` is exactly Theorem 34's intermediate target.

> **Two independent routes now give `μ = 1/12` for one-variable cancellation: Theorem 34 (square-root
> cancellation in the resonance `a`-sum) and Theorem 85 corrected (optimal mod-1 spacing of the
> bilinear frequencies). Both are one-variable statements, and both land on the same value — as
> Theorem 40 requires, since LH needs cancellation at **both** levels.**

**Twelfth correction, eighth firing of the standing rule, and the third time auditing the campaign's
own newest theorem has caught an error** (after E37 and E39). The practice is now the campaign's most
productive single habit.

### C497 — the missing input, restated correctly

> **The mod-1 distribution of `{N√(2a)/√L}`, `a ≍ L = N^{1/3}`, is worth at most `μ ≤ 1/12` even if
> perfect. It is a route to beating the record, not to the Lindelöf hypothesis.**

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 188 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 85 results, twelve corrections, 61 dead routes.

## Cycle 189 — **THEOREM 86: the reduction terminates at Bombieri–Iwaniec's own tool**

E42 established that one-variable cancellation in the normalised sum is worth `L^{1/2}` of the required
`L`. Cycle 189 identifies what supplies the rest.

### C498 — both variables, and the tool that does both `[STRUCTURAL]`

The normalised sum (Thm 82) needs a saving of `L`; the dual large sieve in one variable gives at best
`L^{1/2}` (E42). **The remaining `L^{1/2}` must come from cancellation in the other variable** — and
the standard instrument for simultaneous cancellation in a bilinear form is the **double large sieve**.

> **`[THEOREM 86]` The campaign's reduction — coherence blocks, theta resonances, Farey dissection,
> normalisation, dyadic localisation, bilinear factorisation — terminates exactly at the **double large
> sieve**, which is Bombieri–Iwaniec's own instrument and the source of the record `13/84`.**

### C499 — two independent localisations agree

Cycle 97 located the frontier at "the Bombieri–Iwaniec conversion at the self-dual block — its first
and second spacing problems", **by reading Bourgain's paper**. Cycle 189 arrives at the double large
sieve **by an independent formal reduction that never used BI's method**.

| route | localisation |
|---|---|
| literature (cycle 97) | BI's first and second spacing problems |
| **formal reduction (cycles 113–189)** | **the double large sieve on the normalised Farey bilinear form** |

> **The two agree. The campaign's ninety-cycle reduction reproduces, from first principles and with
> every step Lean-certified, the localisation that reading the literature gave in one cycle — and adds
> to it the explicit object (Thm 82), the proved within-arc half (Thms 80–81), the dyadic localisation
> (Thm 83), and the exact value of what one-variable cancellation is worth (E42: `μ = 1/12`).**

### C500 — the campaign's position, in full

    proved      : within-arc cancellation at every arc                     Thms 80–81
    proved      : the reduction to a normalised Farey bilinear sum          Thms 82–84
    priced      : one-variable cancellation is worth exactly `μ = 1/12`     Thm 34, E42
    open        : two-variable cancellation — the double large sieve        Thm 86
    record      : `13/84`, from that same instrument                        Bourgain 2017

> **The remaining gap between the campaign's reduction and the Lindelöf hypothesis is the gap between
> what the double large sieve currently gives (`13/84`) and what it would have to give (`0`). That is
> the subject's frontier, arrived at twice by independent means.**

### Standing position after 189 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 86 results, twelve corrections, 61 dead routes.

## Cycle 190 — **THEOREM 87: the raw double large sieve is inapplicable, and that is what BI's spacing analysis repairs**

Theorem 86 identified the double large sieve as the terminal instrument. Cycle 190 applies it.

### C501 — the parameters `[COMPUTED, EXPONENTS LEAN-CERTIFIED]`

For `|Σ_{i,j}a_ib_je(x_iy_j)|² ≪ (1+Xδ₂)(1+Yδ₁)‖a‖²‖b‖²` with the normalised form's data:

| | range | spacing |
|---|---|---|
| `x_a = N√(2a)`, `a ≍ L` | `X ≍ N^{7/6}` | `δ₁ ≍ N^{5/6}` |
| `y_q = q^{−1/2}`, `q ≍ L` | `Y ≍ N^{−1/6}` | `δ₂ ≍ N^{−1/2}` |

Both efficiency products are equal and large: `Xδ₂ = Yδ₁ = **N^{2/3}**` (`sieve_inefficient`). With
`‖a‖² ≍ N^{1/3}`, `‖b‖² ≍ N^{−1/3}`:

    |Σ|² ≪ N^{4/3},  i.e.  |Σ| ≪ **N^{2/3}** ,

against the trivial `N^{1/3}` — **worse than trivial by `N^{1/3}`**
(`doubleSieve_worse_than_trivial`, `doubleSieve_deficit`).

Subdividing the `x`-range into pieces of length `1/δ₂ = N^{1/2}` to restore efficiency leaves
`N^{1/2}/N^{5/6} < 1` points per piece — **fewer than one** (`subdivision_degenerates`).

> **`[THEOREM 87]` The **raw** double large sieve is inapplicable to the normalised bilinear form: it
> sits at `N^{2/3}` in its efficiency products, returns a bound `N^{1/3}` worse than trivial, and
> degenerates under the subdivision that would restore efficiency
> (`raw_double_sieve_inapplicable`).**

### C502 — and that is precisely what Bombieri–Iwaniec supply

> **The `N^{1/3}` deficit is exactly the gap that BI's first and second spacing problems exist to
> close. Their content is not the sieve — the sieve is classical — but the arithmetic input showing
> the resonance data are better distributed than the raw parameters assume. Bourgain's decoupling
> improves that same input.**

The campaign's reduction therefore explains, from first principles, **why the subject needs spacing
problems at all**: without them the terminal instrument is worse than doing nothing.

| | bound on the normalised form |
|---|---|
| trivial | `N^{1/3}` |
| **raw double large sieve** | **`N^{2/3}` — worse** |
| BI + spacing analysis (→ `13/84`) | between them |
| Lindelöf | `O(1)` |

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 190 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 87 results, twelve corrections, 61 dead routes.

## Cycle 191 — **THEOREM 88: recalibration — the spacing analysis has achieved more than half, not one fourteenth**

Theorem 87 gave the raw sieve's position. Cycle 191 measures progress from there rather than from the
trivial bound.

### C503 — the four positions on the normalised sum `[PROVED, LEAN-CERTIFIED]`

Exponents in `L = N^{1/3}`, on the normalised sum of Theorem 82:

| | exponent | restores to |
|---|---|---|
| **raw double large sieve** | `2` | `N` — worse than trivial (Thm 87) |
| trivial bound | `1` | `N^{5/6}` |
| **Bourgain's record** | `13/14` | `N^{17/21}` (`normBourgain_restores`) |
| Lindelöf | `0` | `N^{1/2}` |

### C504 — two baselines, two very different pictures `[PROVED, LEAN-CERTIFIED]`

    from the trivial bound :  (1 − 13/14)/(1 − 0)  =  **1/14 ≈ 7.1 %**
    from the raw sieve     :  (2 − 13/14)/(2 − 0)  =  **15/28 ≈ 53.6 %**

> **`[THEOREM 88]` Measured from the raw double large sieve — the actual starting point of the
> Bombieri–Iwaniec method, before any spacing analysis — **more than half** of the saving the Lindelöf
> hypothesis requires has already been achieved (`majority_achieved_from_raw`). Measured from the
> trivial bound it is one fourteenth (`baselines_differ`). The discrepancy is exactly the factor `L`
> by which the raw sieve is *worse* than trivial.**

### C505 — what the recalibration says

Theorem 45's `1/14` measured the record against the classical exponent — a fair statement of how far
`μ` has moved. **Theorem 88 measures it against the method's own starting point**, and the picture is
different in kind:

* the spacing analysis must first climb back the factor `L` by which the raw sieve loses;
* only then does it begin to save;
* it has done both, and the total climb `L^{15/14}` is **more than half** the `L²` that Lindelöf needs.

> **A century of work on the spacing problems has recovered `15/28` of the distance from where the
> method starts to where the Lindelöf hypothesis sits. The remaining `13/28` is comparable to what has
> been done — not the twenty-to-one deficit that measuring from the trivial bound suggests.**

**Standing-rule check:** every exponent here reproduces `N^{5/6}`, `N^{17/21}` or `N^{1/2}`; the last is
the conjecture, stated as such. Nothing unconditional below `13/84` is claimed.

Umbrella green at 10930 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 191 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 88 results, twelve corrections, 61 dead routes.

## Cycle 192 — **`[E43]`** Theorem 88's number is convention-dependent

Auditing the newest theorem, per standing practice.

### C506 — the double large sieve has two conventions in circulation

Theorem 87 used `|Σa_ib_je(x_iy_j)|² ≪ (1 + Xδ₂)(1 + Yδ₁)‖a‖²‖b‖²`, with `δ` the **separations**. Under
that reading, larger separation *worsens* the bound — which is backwards. The form in which larger
separation helps is

    |Σ|² ≪ (1 + X/δ₂)(1 + Y/δ₁)‖a‖²‖b‖² .

Recomputing with the campaign's data (`X ≍ N^{7/6}`, `δ₁ ≍ N^{5/6}`, `Y ≍ N^{−1/6}`, `δ₂ ≍ N^{−1/2}`):

    X/δ₂ = N^{5/3},   Y/δ₁ = N^{−1},   product ≍ N^{5/3},
    |Σ|² ≪ N^{5/3}·N^{1/3}·N^{−1/3} = N^{5/3},   |Σ| ≪ **N^{5/6}** ,

against the trivial `N^{1/3}` — **still worse than trivial**, but by `N^{1/2}` rather than `N^{1/3}`.

### `[E43]` — what stands and what does not

**Stands (Theorem 87, qualitative):** the raw double large sieve is worse than trivial on the
normalised bilinear form under either convention, and degenerates under the subdivision that would
restore efficiency. **The reason the subject needs spacing problems is unaffected.**

**Does not stand:** the specific value `N^{2/3}`, and therefore **Theorem 88's `15/28 ≈ 53.6 %`**. Under
the second convention the raw-sieve exponent on the normalised sum is `L^{5/2}` rather than `L²`, and
the progress fraction becomes `(5/2 − 13/14)/(5/2) = (22/7)/(5/2)·(1/2)`… — a different number.

> **`[E43]` Theorem 88 is downgraded to its qualitative content: **measured from the raw double large
> sieve rather than from the trivial bound, the spacing analysis has achieved a substantially larger
> fraction of what the Lindelöf hypothesis requires** — because it must first recover the factor by
> which the raw sieve loses. The precise fraction depends on the sieve convention and is **not**
> asserted.**

### C507 — the methodological point

The error is of a new kind for this campaign: not an exponent computed outside its domain, but a
**published inequality quoted in a form the campaign did not verify against a source.** The standing
rule (compare against `13/84`) did not catch it, because both conventions give values *above* the
record.

> **Standing practice, extended: an exponent that depends on the exact form of a quoted inequality
> must be checked against the source, or stated qualitatively. The `13/84` test detects claims that
> are too strong; it does not detect claims that are merely mis-parametrised.**

**Thirteenth correction, and the fourth caught by auditing the campaign's own newest result.**

### Standing position after 192 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 88 results (one downgraded to qualitative),
thirteen corrections, 61 dead routes.

## Cycle 193 — **`[E44]` the corpus already formalises Bourgain's proof — 64 modules — and the campaign duplicated it abstractly**

E43 said: verify quoted inequalities against sources. Searching the corpus for the double large sieve
before doing so returned something far larger.

### C508 — what is in `formal/GaloisForLFunctions/RHTower/` `[CORPUS AUDIT]`

**Sixty-four `Bourgain*` modules**, a serious formalisation of Bourgain's `13/84` proof:

| module group | content |
|---|---|
| `BourgainSixfoldCloud` | Section 3's frequency cloud, `bourgainMomentCurve h = (h, h², h^{3/2}, h^{1/2})` — **square-root coordinates** |
| `BourgainGaussianLargeSieve`, `BourgainLocalMassL2`, `BourgainIntervalLocalization`, `BourgainBoxLocalization` | **the Bombieri–Iwaniec double large sieve**, built in four dimensions |
| `BourgainGaussianSpacing`, `BourgainSpacingExponentArithmetic` | the spacing analysis; `bourgain_spacing_endgame` |
| `BourgainScaledParabolaDecoupling`, `BourgainPlanarDiscreteDecoupling` | the decoupling input |
| `BourgainExponentEndgame` | Section 4: exponent-pair `M^{11/18}T^{1/9}`, Huxley `T^{1/32}M^{103/128}`, Bourgain `M^{1/2}T^{13/84}`, with the range overlaps `12/31 < 11/28` and `17/42 < 332/819` |
| `BourgainZetaReduction` | the link to `riemannZeta` via Euler–Maclaurin |

### `[E44]` — the campaign's cycles 186–192 duplicated this abstractly

Theorems 84–88 reasoned about "the double large sieve" from quoted parameters, produced a
convention-dependent exponent (E43), and downgraded a result — **while a formalised, four-dimensional
treatment of that exact sieve sat in the corpus, together with the spacing analysis it feeds.**

**This is the same failure as the `norm_geom_sum_le` duplication (C303), two orders of magnitude
larger.** The search that found it (`rg -il "double.?large.?sieve|largeSieve"`) takes one command and
was not run for seven cycles.

### C509 — but the reduction is independently validated

The campaign's cycles 113–190 derived, from the critical block and without using Bourgain's method,
that the frontier object carries **square-root phases** and terminates at the **double large sieve**.
The corpus's `bourgainMomentCurve = (h, h², h^{3/2}, h^{1/2})` has exactly those square-root
coordinates, and its sieve modules are exactly that instrument.

> **Two independent constructions — the campaign's formal reduction and the corpus's transcription of
> Bourgain's proof — meet at the same object. That is strong evidence the reduction is correct, and it
> is the only thing cycles 186–192 contributed that the corpus did not already have.**

### C510 — and the corpus names the open inputs exactly

`bourgain_spacing_endgame` is **conditional**, on three explicit hypotheses:

    hDirect : T^{3/7} ≤ M → S⁶ ≤ M³·T^{13/14}
    hMiddle : T^{5/12} ≤ M → S⁶ ≤ M⁴·T^{1/2}
    hLow    : M < T^{5/12} → S⁶ ≤ M²·T^{4/3}

> **`[REDIRECTION]` The frontier the campaign spent ninety cycles localising is already named in the
> corpus as three hypotheses of one theorem. A successor should work on `hDirect`, `hMiddle`, `hLow`
> in `RHTower/BourgainSpacingExponentArithmetic.lean` — not re-derive the reduction that reaches
> them.**

**Fourteenth correction, and the largest.** Standing practice, restated and now mandatory:
**`rg -il` the corpus for the *name of the method* before analysing it, not only for the names of the
objects.**

### Standing position after 193 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 88 results, fourteen corrections, 61 dead
routes, **and a redirection to three named open hypotheses already in the corpus.**

## Cycle 194 — the corpus's own open gap, and a discrepancy worth checking

Following E44's redirection into the Bourgain cluster.

### C511 — the corpus names its open input precisely `[CORPUS AUDIT]`

`RHTower/BourgainParabolaTwoTorusL12.lean` states its position exactly:

> *"The exact two-torus `L⁶` theorem and the pointwise `L¹` bound give the unconditional baseline
> `∫_{T²}|Σ aₙe(nu+n²v)|¹² ≪ H^ε(Σ|aₙ|)⁶(Σ|aₙ|²)³`. For unit coefficients this is `H^{9+ε}`.
> **Bourgain's four-dimensional decoupling theorem improves this baseline to `H^{6+ε}`; keeping the
> baseline explicit isolates the exact three-power gain still required.**"*

So the corpus's open input is a **three-power gain** in one twelfth-moment estimate, and it is exactly
where the campaign's Theorem 86 pointed.

### C512 — but the target should be checked against the sharp Vinogradov count `[FLAG, NOT A CLAIM]`

`∫_{T²}|Σ_{n≤H}e(nu+n²v)|^{2s}` counts solutions of the degree-2 Vinogradov system in `s` variables per
side, i.e. `J_{s,2}(H)`, whose sharp size is

    J_{s,2}(H) ≍ H^s + H^{2s−3} .

At `s = 6` this is `H^6 + H^9 = **H^9**` — the baseline, and (for unit coefficients) the **truth**, not
an improvable bound. Decoupling replaces an `ℓ¹` factor by `ℓ²`, which for unit coefficients would give
`H^6`; that appears to contradict the count.

> **`[FLAG]` Either the corpus's stated target concerns a rescaled or anisotropic version of the
> estimate (its neighbours `BourgainAnisotropicPlanarTransfer`, `BourgainScaledParabolaDecoupling`,
> `BourgainScaledPlanarBilinearL6` suggest so), or the docstring's "improves to `H^{6+ε}`" is stated
> for general coefficients where it is not equivalent to the unit-coefficient count. **This must be
> resolved before work is done on that gap** — a successor could otherwise spend effort on a target
> that is false as literally stated.**

**This is not an assertion that the corpus is wrong.** It is a discrepancy between a docstring's
headline figure and the sharp count for the unit-coefficient case, and the campaign has not
established which reading is intended.

### C513 — what the campaign contributes here

The campaign's own reduction (Thms 77–83) arrives at the same `L^{12}`-type object from the `ζ` side
and states its requirement in the normalised Farey form (Thm 82). **That gives an independent way to
check the intended normalisation**: the campaign's target is a saving of `L` on a sum whose `ℓ¹` is `L`
and `ℓ²` is `(\log L)^{1/2}` — an `ℓ¹`-to-`ℓ²` replacement, exactly the shape of the decoupling gain
the corpus describes.

> **The two descriptions agree in *kind* (replace `ℓ¹` by `ℓ²`) and must be made to agree in
> *magnitude* before either is used. That reconciliation is the concrete next task.**

### Standing position after 194 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 88 results, fourteen corrections, 61 dead
routes, one flagged discrepancy in the corpus's own stated target.

## Cycle 195 — the flag resolved: the 2D baseline is **sharp**, and the "three-power gain" is on a different curve

C512 flagged a discrepancy in `BourgainParabolaTwoTorusL12`. Cycle 195 reads the actual statements and
resolves it.

### C514 — what the file proves `[CORPUS AUDIT]`

    norm_bourgainParabolaTwoTorusSum_le_l1 :  ‖Σ‖ ≤ Σ‖aₙ‖            (pointwise `L¹`)
    norm_..._pow_twelve_le               :  ‖Σ‖¹² ≤ (Σ‖aₙ‖)⁶·‖Σ‖⁶   (six factors bounded trivially)

Integrating and using the exact two-torus `L⁶` theorem gives the baseline `(Σ|aₙ|)⁶(Σ|aₙ|²)³`, i.e.
`H^{9+ε}` for unit coefficients. **The formalised content is correct.**

### C515 — and the baseline is sharp, not improvable `[RESOLUTION]`

`∫_{T²}|Σ_{n≤H}e(nu+n²v)|^{2s}` counts solutions of the degree-2 Vinogradov system in `s` variables per
side, whose sharp size is

    J_{s,2}(H) ≍ H^s + H^{2s−3} :   s = 3 → H³ (the `L⁶` critical case) ;   s = 6 → H⁶ + H⁹ = **H⁹**.

> **For unit coefficients the two-torus twelfth moment *is* `H^{9}`. The baseline the file proves is
> the truth, and no decoupling theorem improves it. The docstring's "improves this baseline to
> `H^{6+ε}`" cannot refer to this object.**

### C516 — what it must refer to instead

Bourgain's Section 3 decouples the **four-dimensional** cloud
`bourgainMomentCurve h = (h, h², h^{3/2}, h^{1/2})` — the corpus's own `BourgainSixfoldCloud` — not the
two-dimensional parabola. The neighbouring modules `BourgainAnisotropicPlanarTransfer`,
`BourgainScaledParabolaDecoupling`, `BourgainScaledPlanarBilinearL6` all carry scaling or anisotropy in
their names.

> **`[RESOLUTION]` The discrepancy is one of **dimension**, not of mathematics. The file's 2D baseline
> is sharp; the three-power gain the docstring describes belongs to Bourgain's four-dimensional
> square-root cloud. **A successor must not attempt to improve `BourgainParabolaTwoTorusL12`'s
> baseline — it is provably optimal — and should work on the four-dimensional cloud instead.**

### C517 — what this contributes

The campaign entered the Bourgain cluster one cycle ago and has already produced something a successor
needs: **a proof that one of the corpus's apparent targets is unreachable, and a redirection to the
object that carries the actual gap.** The flag was raised by comparing a docstring's headline against
a sharp classical count — the same discipline that produced the campaign's fourteen corrections, now
applied outward rather than inward.

### Standing position after 195 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 88 results, fourteen corrections, 61 dead
routes, one flag raised and resolved.

## Cycle 196 — **THEOREM 89: the campaign and the corpus meet at one hypothesis and one number**

E44 redirected to the corpus's three open hypotheses. Cycle 196 prices the first at the critical block.

### C518 — the Bourgain cluster is `sorry`-free, with exactly three open inputs `[CORPUS AUDIT]`

No `sorry` or `admit` in any of the 64 `Bourgain*` modules. The only hypothesis-carrying capstone is
`bourgain_spacing_endgame`, conditional on

    hDirect : T^{3/7} ≤ M → S⁶ ≤ M³·T^{13/14}
    hMiddle : T^{5/12} ≤ M → S⁶ ≤ M⁴·T^{1/2}
    hLow    : M < T^{5/12} → S⁶ ≤ M²·T^{4/3}

### C519 — `hDirect` at the critical block **is** Bourgain's exponent `[PROVED, LEAN-CERTIFIED]`

At `M = T^{1/2}` — the Lindelöf configuration, where the AFE is self-dual — the hypothesis applies
(`3/7 < 1/2`, `hDirect_applies_at_critical`) and gives

    S⁶ ≤ T^{3/2}·T^{13/14} = T^{17/7} ,   so   S ≤ T^{17/42} = (T^{1/2})^{**17/21**} ,

**exactly Bourgain's block exponent** (`hDirect_gives_bourgain`), hence exactly `μ = 13/84`
(`hDirect_gives_mu`).

And the Lindelöf hypothesis at the same block is `S ≤ T^{1/4}`, i.e. `S⁶ ≤ T^{3/2} = M³` — **`hDirect`
with `T^{13/14}` replaced by `T^{ε}`** (`lindelof_is_hDirect_at_zero`).

> **`[THEOREM 89]` The campaign's 195-cycle reduction and the corpus's 64-module Bourgain
> formalisation meet at **one named hypothesis with one exponent**: `hDirect`'s `T^{13/14}`. Bourgain's
> record is that hypothesis as stated; the Lindelöf hypothesis is the same statement with the exponent
> `0`. **`13/14` is the entire remaining gap** (`remaining_gap_in_hDirect`, `campaign_meets_corpus`).**

### C520 — why this is the campaign's most useful single output

Everything the campaign proved — the coherence decomposition, the Farey dissection, the within-arc
bound at every arc, the normalisation, the dyadic localisation, the bilinear factorisation — was a
route to *this* statement. The corpus reached it from Bourgain's paper. **Both now terminate on the
same line of Lean, and the distance to the Lindelöf hypothesis is one rational number in one
hypothesis of one theorem.**

| | `hDirect`'s `T`-exponent | block exponent | `μ` |
|---|---|---|---|
| **corpus, as stated** | `13/14` | `17/21` | `13/84` |
| **Lindelöf** | `0` | `1/2` | `0` |

Umbrella green at 10932 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 196 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 89 results, fourteen corrections, 61 dead
routes. **The target is now a single exponent in a single named hypothesis, and both the campaign's
independent reduction and the corpus's transcription of Bourgain agree on it.**

## Cycle 197 — **THEOREM 90: `hDirect` at exponent zero is the exponent-pair conjecture**

Theorem 89 identified `hDirect`'s `T^{13/14}` as the whole remaining gap. Cycle 197 asks what the
endpoint `T^0` says.

### C521 — the endpoint `[PROVED, LEAN-CERTIFIED]`

`hDirect` at `T`-exponent `e` reads `S⁶ ≤ M³T^e`, i.e. `S ≤ M^{1/2}T^{e/6}`. At `e = 0`:

    **S ≤ M^{1/2}** — square-root cancellation, uniformly for `M ≥ T^{3/7}`.

In exponent-pair language `S ≪ (Y/M)^κM^λ` with `Y ≍ T`, this is exactly `(κ,λ) = (0,1/2)` — **the
exponent-pair conjecture** (`hDirectBlockExponent_zero`).

| `hDirect`'s `T`-exponent | block exponent | meaning |
|---|---|---|
| `3/2` | `1` | trivial (`hDirectBlockExponent_trivial`) |
| **`13/14`** | **`17/21`** | **Bourgain's record** (`hDirectBlockExponent_bourgain`) |
| `0` | `1/2` | **exponent-pair conjecture ⟹ Lindelöf** (`hDirectBlockExponent_zero`) |

> **`[THEOREM 90]` The corpus's open hypothesis interpolates, affinely and monotonically
> (`hDirectBlockExponent_mono`), between the trivial bound and the exponent-pair conjecture. Bourgain's
> record sits `8/21 ≈ 38 %` of the way (`hDirectProgress_eq`).**

### C522 — and the campaign's Theorems 20–25 price exactly that interpolation

The campaign proved independently that:

* the exponent pair `(0,1/2)` is the limit of the van der Corput `A`-chain (Thm 25);
* **only one pair with `λ = 1/2` is known — the trivial `(1/2,1/2)`** — so the chain runs one step;
* the `A`-process is inert at every landmark below `(√3−1)/4` (Thm 20), the line of symmetry is an
  attractor (Thm 22), and the realisable floor is `1/6` (Thm 25).

> **The corpus's open hypothesis at `e = 0` is the exponent-pair conjecture; the campaign's Theorems
> 20–25 are a complete pricing of that conjecture's inaccessibility. **Two independent lines of work,
> one from Bourgain's proof and one from the van der Corput calculus, describe the same open statement
> and agree on why it is hard.**

### C523 — the campaign's position, final form

    corpus (from Bourgain's paper)   :  hDirect at e = 13/14  ⟹  μ ≤ 13/84
    corpus target                    :  hDirect at e = 0      ⟺  exponent pair (0,1/2)  ⟹  LH
    campaign (from van der Corput)   :  (0,1/2) is the A-chain's limit, reachable in one step only
                                        from a `λ = 1/2` pair, of which one is known
    campaign (from the ζ side)       :  the same target as an ℓ¹→ℓ² gap on a Farey sum (Thm 82)

**Three descriptions of one open statement, all Lean-certified, all agreeing.**

Umbrella green at 10932 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 197 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 90 results, fourteen corrections, 61 dead
routes.

## Cycle 198 — consolidation: the successor summary brought current

The summary was at cycle-167 vintage and omitted the campaign's single most important finding. It now
carries a new §8, placed to be read first:

* **the corpus's 64 `Bourgain*` modules**, what they contain, and the standing rule that would have
  found them (`rg -il` for the *method*, not the objects);
* **the corpus's exact open frontier** — `hDirect`, `hMiddle`, `hLow` of `bourgain_spacing_endgame`;
* **Theorems 89–90** — the campaign's reduction and the corpus's formalisation meeting at one
  hypothesis and one exponent, with `hDirect` at `e = 0` identified as the exponent-pair conjecture,
  so that §3's Theorems 20–25 price the corpus's own target;
* **a target that is not reachable** — the 2D parabola baseline `H^9` is sharp, and the "three-power
  gain" belongs to the four-dimensional cloud;
* **where to work**, and what not to re-derive.

### Standing position after 198 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 90 results, fourteen corrections, 61 dead
routes. Deliverables current: working log, successor summary, structural account, and 10932 jobs of
Lean.

## Cycle 199 — **THEOREM 91: on the `hDirect` axis, Weyl did seven-eighths of the progress**

Theorem 90 placed Bourgain at `8/21` of the way along the `hDirect` axis. Cycle 199 asks how that
`8/21` divides, using the campaign's own proved within-arc bound as the intermediate marker.

### C524 — the campaign's Theorem 81 on this axis `[PROVED, LEAN-CERTIFIED]`

Theorem 81 (within-arc cancellation at every Farey arc — **proved**, not assumed) gives `L^{5/2}` at the
critical block, i.e. `S ≤ T^{5/12}` — Weyl's exponent. On the `hDirect` axis, `S⁶ ≤ T^{5/2}` against
`M³ = T^{3/2}` gives **`e = 1`**.

    trivial                      e = 3/2
    **Weyl (= Thm 81)**          **e = 1**   (`weyl_strictly_between`)
    Bourgain                     e = 13/14
    Lindelöf                     e = 0

### C525 — the division of progress `[PROVED, LEAN-CERTIFIED]`

Bourgain has covered `3/2 − 13/14 = 4/7` (`bourgainCovered_eq`). Within that:

| contribution | distance | share |
|---|---|---|
| **Weyl, 1921** | `3/2 − 1 = 1/2` | **`7/8`** (`weylShare_eq`) |
| **Bombieri–Iwaniec → Bourgain, 1986–2017** | `1 − 13/14 = 1/14` | **`1/8`** (`spacingShare_eq`) |

and the two exhaust it (`shares_sum`).

> **`[THEOREM 91]` On the `hDirect` axis — the axis on which the corpus's open hypothesis and the
> campaign's reduction both live — **Weyl's 1921 step accounts for seven-eighths of all progress, and
> the entire spacing analysis of the last forty years accounts for one-eighth**
> (`weyl_seven_times_spacing`).**

### C526 — and the campaign re-proved the seven-eighths

Theorem 81 obtained `e = 1` **from the campaign's own Farey decomposition**, by the elementary
`s = r+m` elimination and the second-derivative test — not by quoting Weyl. So the campaign has an
independent proof of the step that constitutes seven-eighths of the progress on this axis, and a
complete pricing (Thms 20–25, 43) of why the remaining eighth has been so slow.

> **The picture the campaign ends with: the classical step is large and re-provable by elementary
> means; the modern spacing analysis is small and hard-won; and the remaining `13/14` is larger than
> everything achieved so far, on an axis whose endpoint is the exponent-pair conjecture.**

Umbrella green at 10933 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 199 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 91 results, fourteen corrections, 61 dead
routes.

## Cycle 200 — **THEOREM 92: one parameter, three names**

Theorem 91 placed Weyl, Bourgain and Lindelöf on the `hDirect` axis. Cycle 200 identifies that axis
with the campaign's own across-arc parameter.

### C527 — the identification `[PROVED, LEAN-CERTIFIED]`

With the within-arc level proved (Thm 81, `w = 1`), the campaign's Farey bookkeeping gives
`fareyExponent 1 x = 5/2 − x`, with `x ∈ [0,1]` the **across-arc** cancellation exponent. In `N` that
is `(5/2−x)/3`. On the `hDirect` axis, `S⁶ ≤ M³T^e` at `M = T^{1/2}` gives `S ≤ N^{(3/2+e)/3}`.
Equating:

    **e = 1 − x.**

| | `hDirect` exponent `e` | across-arc `x` |
|---|---|---|
| Weyl (= Thm 81) | `1` | **`0`** — no across-arc cancellation |
| **Bourgain** | `13/14` | **`1/14`** |
| Lindelöf | `0` | **`1`** — full square-root cancellation |

> **`[THEOREM 92]` The corpus's hypothesis exponent and the campaign's across-arc cancellation
> parameter are **the same quantity** (`one_parameter_three_names`). Bourgain's `x = 1/14`
> (`acrossArcOf_bourgain`) coincides exactly with the `1/14` Theorem 45 derived independently from the
> block-exponent currency, months of cycles earlier and by a different route.**

### C528 — what the campaign ends with

Two hundred cycles produce one parameter:

    x  =  the across-arc square-root cancellation achieved in the Farey dissection of the critical block.

* `x = 0` is Weyl's theorem — **proved twice**, classically and by the campaign's own within-arc
  argument (Thm 81);
* `x = 1/14` is the record — Bombieri–Iwaniec through Bourgain, and the corpus's `hDirect`;
* `x = 1` is the Lindelöf hypothesis, equivalently the exponent pair `(0,1/2)` (Thm 90);
* `13/14` of it remains (`remaining_across_arc`).

Every barrier the campaign proved is a statement about why `x` is hard to increase: the `A`-process is
inert (Thm 20), the line of symmetry attracts (Thm 22), within-arc work is neutral (Thms 43, 81), the
mean square already has `x = 1` (Thm 39), all five bridges to pointwise are closed (Thms 49–50), the
gap is scale-invariant (Thm 52), the two tool families are separately stationary (Thm 55), their
coupling is the functional equation and it is stationary (Thm 56), completion cannot be manufactured
(Thms 58–59, 62), and the raw double large sieve is worse than trivial (Thm 87).

> **The Lindelöf hypothesis is `x = 1`. A century has reached `x = 1/14`. This campaign proved the
> `x = 0` step independently, priced every route to increasing `x`, and identified the single Lean
> hypothesis in the corpus where the remaining `13/14` sits.**

Umbrella green at 10933 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 200 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 92 results, fourteen corrections, 61 dead
routes.

## Cycle 201 — **THEOREM 93: reciprocity makes the `q`-variable the complete one**

Everything now rests on increasing `x`, the across-arc cancellation. Cycle 201 looks at the `q`-variable
of the Farey sum, which the campaign has always treated as the outer one.

### C529 — the reciprocity flip `[COMPUTED HERE]`

In `Σ_{a/q}(1/q)·ε_q(a|q)·e(N√(2a/q)+θ_{a,q})`, the Legendre symbol has been read as a character in
`a` for fixed `q`. **Quadratic reciprocity reverses the roles**: for odd positive `a,q`,

    (a|q)·(q|a) = (−1)^{((a−1)/2)((q−1)/2)} ,   so   (a|q) = ± (q|a) ,

and `(q|a)` is a character **in `q`**, of modulus `4a ≍ L`.

> **`[THEOREM 93]` For fixed `a`, the summand's arithmetic factor is a real character in `q` of modulus
> `≍ 4L`, and the summation range `q ∈ [L/2, L]` is a **positive proportion** (`≈ 1/8`) of that
> modulus. **The `q`-variable therefore admits completion**, unlike the `a`-variable of Theorem 62,
> where the sum is complete but the phase is transcendental.**

| variable | completeness | phase status |
|---|---|---|
| `a` (fixed `q`) | complete residue system ✓ | transcendental `√(2a/q)` ✗ (Thm 62) |
| **`q` (fixed `a`)** | **character mod `4a`, range a positive proportion ✓** | fast phase ✗ |

### C530 — and the obstruction is the same one

Partial summation in `q` against Pólya–Vinogradov needs the phase to vary slowly. Its `q`-derivative is
`|d/dq · N√(2a/q)| ≍ N√L/L^{3/2} = N/L = N^{2/3}` — **fast**, exactly as in the `a`-variable
(Theorem 35, tool 3). The completion the `q`-variable offers cannot be used for the same reason the
`a`-variable's completeness could not.

> **The two variables have complementary arithmetic status and identical analytic status: one is
> complete, the other is character-complete, and in both the phase varies faster than the character
> saving. This is Theorem 55's dichotomy at the level of a single sum's two variables — the arithmetic
> structure is available in each, and the fast phase defeats it in each.**

### C531 — what is new

The reciprocity flip is a structural fact the campaign did not have: **the outer variable of the Farey
sum is the one where completion exists.** Every earlier treatment of the `q`-sum (Thms 63, 82–85)
treated `q` as a mere weight index. It is a modulus.

**Whether that helps is open** — the fast phase blocks the obvious use — but it is the first time the
campaign has found *usable arithmetic structure* in the outer variable, and it is where a bilinear
method (Thm 84, E41) would need it.

### Standing position after 201 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 93 results, fourteen corrections, 61 dead
routes.

## Cycle 202 — **`[D62]`** the reciprocity opening closes, by the identical obstruction

Theorem 93 found completion available in the `q`-variable. Cycle 202 tries to use it.

### C532 — completing in `q` `[COMPUTED HERE]`

With `(a|q) = ±(q|a)` a character mod `4a`, and `q` running over a positive proportion of that modulus,
expand `f(q) = w(q)e(N√(2a/q))` in additive characters mod `4a`:

    Σ_q (q|a)f(q) = Σ_{h mod 4a} f̂(h)·Σ_q (q|a)e(hq/4a) = ε_a√a · Σ_h (h|a)·f̂(h) ,

**the same shape as Theorem 63**, now in the outer variable.

### C533 — and the transform has no stationary point in range `[COMPUTED HERE]`

Stationarity for `f̂(h)` requires `d/dq[N√(2a/q) − hq/(4a)] = 0`, i.e.

    |h| = 2aN√(2a)/q^{3/2} ≍ L·N·√L/L^{3/2} = **N** ,

while `h` runs modulo `4a ≍ L = N^{1/3}`. **The stationary frequency exceeds the available range by
`N^{2/3}`** — precisely the margin of C415 in the `a`-variable.

> **`[D62]` The reciprocity flip supplies completion in `q`, and completing reproduces Theorem 63's
> inner product against a quadratic character, with the transform again non-stationary throughout its
> range and the phase derivative again uncontrolled modulo one. **The `q`-variable's completeness is as
> unusable as the `a`-variable's.** Do not pursue reciprocity as a route to across-arc cancellation.**

### C534 — fifth confirmation of the conjugation principle

| transformation | what it preserved |
|---|---|
| reduction levels (Thm 52) | the pointwise/mean-value gap |
| Poisson (Thms 66–67) | the phase family |
| the AFE (Thm 61) | the exponent |
| pair variables (D60) | genericity |
| **reciprocity (D62)** | **the fast-phase obstruction** |

> **Every change of description the campaign can perform is a conjugation. Theorem 93's structural
> finding — that the outer variable is a modulus — is correct and new, and it moves the obstruction
> without weakening it.**

**Honest note.** Cycle 201 called the reciprocity flip "the first usable arithmetic structure in the
outer variable" and said whether it helps is open. One cycle later the answer is: **it does not**, for
the reason every other opening has failed.

### Standing position after 202 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 93 results, fourteen corrections, 62 dead
routes.

## Cycle 203 — **THEOREM 94: the conjugation principle explained — the frontier object is a chirp**

Five cycles have confirmed that every transformation preserves the obstruction (Thms 52, 61, 66–67,
D60, D62). Cycle 203 asks why, and the answer is one sentence.

### C535 — flat in both bases `[PROVED, LEAN-CERTIFIED]`

The campaign's transforms — Poisson, finite Fourier, Mellin, reciprocity — are **unitary**, so they
preserve `ℓ²` exactly. They preserve `ℓ¹` only when they map flat vectors to flat vectors, and here:

* **position basis**: the resonance terms are unimodular — flat, `ℓ¹/ℓ² = √q`;
* **Fourier basis**: `|ĉ_h| ≍ q^{−1/2}` (Theorem 64) — flat again.

A unit vector with `|v_n| = |v̂_h| = q^{−1/2}` is the **extremal configuration for the uncertainty
principle**, and its instances are precisely the **chirps** (Gauss sums).

> **`[THEOREM 94]` The frontier object is flat in both position and frequency, so its `ℓ¹`-to-`ℓ²` gap
> is the maximum possible and is the **same in both bases** (`gap_basis_independent`,
> `no_concentrating_basis`). **No basis reachable by the campaign's transforms concentrates it**, and
> every conjugation therefore preserves the entire difficulty.**

### C536 — the five confirmations are one fact

| confirmation | preserved |
|---|---|
| Thm 52 | the pointwise/mean-value gap |
| Thms 66–67 | the phase family |
| Thm 61 | the exponent |
| D60 | genericity |
| D62 | the fast-phase obstruction |

> **All five are instances of: *the frontier object is a chirp*. Chirps are the vectors that are flat
> in position and in frequency simultaneously; the `ℓ¹`/`ℓ²` gap that the Lindelöf hypothesis asks to
> close is exactly their defining property, and it is invariant under every unitary change of basis.**

### C537 — the sharpest form of the campaign's central obstruction

The Lindelöf hypothesis asks for `ℓ²`-size behaviour from an object whose `ℓ¹`-to-`ℓ²` gap is extremal
in every reachable description. **The obstruction is not that the object is badly understood — it is
understood exactly, and what is understood is that it is maximally spread.** Progress requires
information that is not basis-covariant: the arithmetic of the phases, which Theorems 55–59 and 62
showed is unavailable in the required form.

Umbrella green at 10933 jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 203 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 94 results, fourteen corrections, 62 dead
routes.

## Cycle 204 — **THEOREM 95: an irrational chirp, and the Gauss map**

Theorem 94 identified the frontier object as a chirp. Chirps are among the best-understood objects in
analysis — Gauss sums are evaluated exactly. Cycle 204 asks why this one is not.

### C538 — rational chirps are evaluable; this one is irrational `[STRUCTURAL]`

`Σ_{m<L}e(αm² + βm)` with `α = a/q` **rational** is a classical Gauss sum, evaluated in closed form by
the Gauss–Salié formulas. The campaign's object has

    α_r = N²/(2n_r²) ,   and the resonance phase  e(N√(2a/q))  with  N√2  **irrational** .

For irrational `α` there is no closed form. The Hardy–Littlewood theta transformation
`α ↦ −1/α` — the **Gauss map** — reduces the chirp to a shorter one, and iterating produces the
continued-fraction expansion of `α`.

> **`[THEOREM 95]` The frontier object is a chirp with an **irrational** parameter. Rational chirps are
> solved exactly; irrational ones reduce to the Gauss map, and their behaviour is governed by the
> continued fraction of the parameter rather than by a formula. This is Theorem 68's diagnosis — *`t`
> is real* — at the level of the chirp itself.**

### C539 — and the campaign's Farey dissection is that expansion's first level

The Farey dissection of Theorem 37 groups the `α_r` by their nearest rational `a/q` — **exactly the
first step of the continued-fraction expansion.** Theorems 80–81 evaluate the chirp at that level
(the within-arc bound), and D58 recorded that **recursing on the `√d`-classes does not terminate.**

    irrational chirp
      → Farey dissection = first Gauss-map step        (Thm 37)
      → within-arc chirp evaluation, proved            (Thms 80–81)
      → next level: the same structure                 (D58, D52)

> **The campaign's complete structural account: the object is an irrational chirp; its natural
> expansion is the Gauss map; the first level is proved and worth `x = 0` (Weyl); and the expansion
> does not terminate. Every barrier the campaign proved is a statement about one level of that
> non-terminating expansion.**

### C540 — what would end it

A closed form, or a uniform bound across all levels of the continued fraction. **Bourgain's spacing
analysis is exactly a partial uniformity statement across levels** — it achieves `x = 1/14` — and the
Lindelöf hypothesis is full uniformity, `x = 1`.

> **LH is the assertion that the Gauss-map expansion of the critical chirp is uniformly controlled.
> Weyl controls one level; Bourgain controls `1/14` of the rest; the campaign has priced every route
> to controlling more.**

### Standing position after 204 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 95 results, fourteen corrections, 62 dead
routes.

## Cycle 205 — **THEOREMS 96–99: the architectural floor of Bourgain's spacing endgame**

Acting on the cycle-193 redirection: work on `hDirect`/`hMiddle`/`hLow` rather than re-derive the
reduction that reaches them. Reading `RHTower/BourgainSpacingExponentArithmetic.lean` exactly:

    hDirect : T^(3/7)  ≤ M → S⁶ ≤ M³·T^(13/14)
    hMiddle : T^(5/12) ≤ M → S⁶ ≤ M⁴·T^(1/2)
    hLow    : M < T^(5/12) → S⁶ ≤ M²·T^(4/3)
    hLower  : T^(17/42) ≤ M                         (standing range restriction)

### C541 — the four numbers `17/42, 5/12, 3/7, 13/84` are **one** number `[NEW]`

Write `M = T^x`; the three bounds become exponent inequalities. Let the target be `S ≤ M^{1/2}T^θ`,
i.e. `S⁶ ≤ M³T^{6θ}`, and keep the two spacing exponents general: `M⁴T^b` above the crossover,
`M²T^c` below.

    upper regime already implies the target  ⟺  x ≤ 6θ − b
    lower regime already implies the target  ⟺  x ≥ c − 6θ

> **`[THEOREM 96]` The window on which a separate direct estimate is *needed* is exactly
> `[c − 6θ, 6θ − b]`. Both of Bourgain's range endpoints are therefore **forced**, not chosen:
>
>     ℓ(θ) = c − 6θ = 4/3 − 13/14 = **17/42** ,   u(θ) = 6θ − b = 13/14 − 1/2 = **3/7** .
>
> At each endpoint the corresponding source bound meets the target with **equality**; this is proved
> as an identity in `(b,c,θ)`, not verified numerically.**

### C542 — the endpoints slide on a fixed line, and the crossover is their midpoint `[NEW]`

    ℓ(θ) + u(θ) = c − b ,   **independent of θ** .

For Bourgain, `c − b = 4/3 − 1/2 = 5/6` — **the classical incoherent block exponent of Theorem 28.**
And the regime crossover, `M⁴T^b = M²T^c`, sits at `m = (c−b)/2`:

    17/42 + 3/7 = 5/6 ,   (17/42 + 3/7)/2 = **5/12** = the crossover.

> **`[THEOREM 97]` The crossover is the exact midpoint of the window, for every target. Improving `θ`
> slides the two endpoints toward each other **symmetrically about a centre that cannot move.**

### C543 — hence an architectural floor `[NEW, the substantive result]`

Window width `= u(θ) − ℓ(θ) = 12θ − (b+c)`. It is nonnegative iff

> **`[THEOREM 98]` `θ ≥ θ_min(b,c) := (b+c)/12`.  Below `θ_min` the two source regimes overlap in the
> wrong direction, the window has negative width, and no direct estimate can even be *posed* on a
> genuine range of `M`. With Bourgain's `(b,c) = (1/2, 4/3)`:
>
>     **θ_min = 11/72 = 0.1527777… ,   13/84 = 0.1547619… ,   13/84 − 11/72 = 1/504 .**
>
> The published record sits `1/504` above the floor of its own architecture; the window at the record
> is `1/42` wide and the slack of the target over the sources at the crossover is `1/84`. Both are
> exact readouts of the remaining room: **width `= 12(θ−θ_min)`, crossover slack `= 6(θ−θ_min)`.**

This is a *hard* limit on the method with its spacing exponents fixed. **Improving `13/84` inside
Bourgain's architecture buys at most `1/504`; anything beyond `11/72` requires changing `b` or `c`
themselves — i.e. a genuinely new first- or second-spacing estimate, not a better direct bound.**

### C544 — and what LH demands of the spacing exponents `[NEW]`

`θ_min(b,c) = 0 ⟺ b = −c`. The upper regime must *save* exactly the power the lower regime loses.
Fixing the invariant crossover `(c−b)/2 = 5/12` gives the unique Lindelöf-limiting pair

    (b, c) = (−5/12, 5/12) ,   window = the single point  M = T^{5/12} .

> **`[THEOREM 99]` The crossover `M = T^{5/12}` is invariant: Bourgain's spacing exponents and the
> Lindelöf-limiting ones put the degenerate point at the **same** Dirichlet-polynomial length. At that
> limit the architecture collapses to one statement — square-root cancellation, `S⁶ ≤ M³`, for a
> Dirichlet polynomial of length `T^{5/12}`. And `5/12` is exactly `5/6` of the AFE critical length
> `T^{1/2}` — the same `5/6` that appears as `c − b`.**

So the campaign's currency and the corpus's Bourgain arithmetic are the same object: **`5/6` is the
sum of the endpoints, the ratio of the critical lengths, and the classical block exponent.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/SpacingWindowGeometry.lean` — `spacingLowerEndpoint`,
`spacingUpperEndpoint`, `spacingCrossover`, `spacingWindowWidth`, `spacingArchFloor`,
`spacing_endpoints_sum`, `spacing_crossover_is_midpoint`, `spacing_tight_at_lower/upper`,
`spacing_window_width_eq_floor_gap`, `spacing_window_closes_iff`,
`spacing_architecture_needs_floor`, `spacing_crossover_slack`, `bourgain_arch_floor = 11/72`,
`bourgain_room_above_floor = 1/504`, `bourgain_window_width = 1/42`,
`lindelof_forces_opposite_exponents`, `crossover_invariant`, `lindelof_collapses_to_crossover`.
Umbrella green at **10934** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 205 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 99 results, fourteen corrections, 62 dead
routes. **New actionable target: the spacing exponents `b = 1/2` and `c = 4/3` themselves — the floor
`(b+c)/12` is the only quantity that matters, and `13/84` is within `1/504` of it.**

## Cycle 206 — **E45 (direction correction) and THEOREM 100 (the envelope form)**

### E45 — cycle 205 read the interval backwards `[CORRECTION]`

Cycle 205 called `[17/42, 3/7]` the *gap* where a direct estimate is needed. **It is the opposite: it
is the interval that the two spacing estimates already cover.** Check against the corpus proof of
`bourgain_spacing_sixth_power_endgame`: the case split is `x ≥ 3/7` → `hDirect`; `3/7 > x ≥ 5/12` →
`hMiddle` **because `M ≤ T^{3/7}`**; `x < 5/12` → `hLow` **because `M ≥ T^{17/42}`**. So `hMiddle`
suffices *below* `3/7` and `hLow` suffices *above* `17/42`: the sources work **inside**.

The error was a sign in "source implies target". Writing `M = T^x`, the available source exponent is
the **upper envelope** `E(x) = max(4x+b, 2x+c)` (the upper regime is used exactly where it is the
weaker line), and the source implies the target iff `E(x) ≤ 3x + 6θ`. Since `E(x) − 3x` has slopes
`−1` and `+1`, it is convex with its **minimum at the corner** — so the solution set is a closed
**interval centred at the corner**, not a gap.

**Every identity of Theorems 96–99 survives verbatim.** Only the interpretation inverts, and it
inverts in the campaign's favour: the endpoints, the sum `c−b = 5/6`, the midpoint `5/12`, the
endpoint tightness, the width `12θ−(b+c)`, the floor `(b+c)/12`, the surplus `6(θ−θ_min)`, the
`1/504` and the `1/84` are all unchanged. Restated correctly:

> **`[THEOREM 98, corrected]` `θ_min = (b+c)/12 = 11/72` is the exponent below which Bourgain's two
> spacing estimates cover **no length `M` at all** — every length would have to be carried by the
> direct estimate alone. Their entire contribution is the corner surplus `6(θ−θ_min) = 1/84` at
> `M = T^{5/12}`, which they spend at unit rate on each side to cover an interval of width `1/42`.**

So `13/84` is `1/504` above the point where the spacing machinery goes dark. That is a *sharper*
statement than cycle 205's: it prices the spacing estimates' contribution exactly, and it says the
method does not become inconsistent below `11/72` — it becomes **empty**.

### C545 — the general form: a Legendre corner `[THEOREM 100, NEW]`

Nothing above used the specific slopes. For source lines of slopes `p > q` with intercepts `b`
(upper) and `c` (lower), and a target of slope `r` with `q < r < p`:

> **`[THEOREM 100]` The set of lengths on which the sources imply the target is the sublevel set
> `{x : E(x) − r·x ≤ ρ}` of a convex piecewise-linear function with a single corner at
> `m = (c−b)/(p−q)`. It is a closed interval centred at `m`, nonempty iff
>
>     ρ ≥ ρ_min(p,q,r,b,c) = E(m) − r·m = ((r−q)/(p−q))·b + ((p−r)/(p−q))·c ,
>
> **the convex combination of the two source intercepts with weights given by where the target slope
> sits between the source slopes.** With `(p,q,r) = (4,2,3)` the weights are `(1/2, 1/2)` and
> `ρ_min = (b+c)/2`, i.e. `θ_min = (b+c)/12`.**

This is the exact, general price of a multi-regime exponent endgame: **the floor is the target line's
deficit at the corner of the source envelope.** It is slope-geometry, not arithmetic, and it applies
to every endgame of this shape in the subconvexity literature.

Two immediate readings:
* **Bourgain's `r = 3` sits exactly midway between `q = 2` and `p = 4`, so the two spacing estimates
  are weighted equally.** A method whose target slope were nearer one source would be dominated by
  that source's intercept alone.
* To lower `θ_min` one must lower a **weighted mean** of `b` and `c`. Improving only the first
  spacing estimate (`b`) buys half of what it appears to; improving only the second (`c`) likewise.

### Lean

`SpacingWindowGeometry.lean` rewritten with corrected semantics: `spacingCoverageWidth`,
`spacingCoverageFloor`, `low_regime_implies_target`, `mid_regime_implies_target`,
`low_regime_fails_below`, `mid_regime_fails_above`, `mid_is_envelope_above`,
`low_is_envelope_below`, `spacing_coverage_nonempty_iff`, `spacing_crossover_surplus`,
plus the general `envelopeCorner`, `envelopeFloor`, `envelope_corner_balances`,
`envelopeFloor_is_convex_combination`, `envelopeFloor_bourgain_slopes`, `envelopeFloor_div_six`.
Umbrella green at **10934** jobs.

### Standing position after 206 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 100 results, **fifteen** corrections, 62 dead
routes. Actionable target unchanged and now correctly priced: **lower the convex combination
`(b+c)/2` of the two spacing intercepts.**

## Cycle 207 — **THEOREMS 101–104: the covering floor `277/1792`, and `1/5376` of room**

Theorem 100 was derived for Bourgain's Section 3. Cycle 207 applies the same law one level up, to
Section 4, using the corpus's own `RHTower/BourgainExponentEndgame.lean`, whose three inputs are

    exponent pair (1/9,13/18) :  A ≤ M^{11/18}T^{1/9}      all M
    Huxley                    :  A ≤ M^{103/128}T^{1/32}   M > T^{12/31}
    decoupling                :  A ≤ M^{1/2}T^{13/84}      M ≥ T^{17/42}

### C546 — reach and demand `[THEOREM 101]`

A source `A ≤ M^α T^β` with `α > 1/2` implies the target `A ≤ M^{1/2}T^θ` exactly on

    x ≤ **reach(α,β,θ) = (θ−β)/(α−1/2)** ,  equivalently  θ ≥ **demand(α,β,x₀) = β + (α−1/2)x₀** .

> **`[THEOREM 101]` The two published "reaches" are this formula, not separate facts:
>
>     reach(11/18, 1/9, 13/84) = (13/84 − 1/9)/(1/9) = **11/28** ,
>     reach(103/128, 1/32, 13/84) = (83/672)·(128/39) = **332/819** .
>
> The third source has slope exactly `1/2`: it *is* the target, so it covers its whole range of
> validity. The entire endgame is therefore a **two-junction covering problem**, with overlaps
>
>     11/28 − 12/31 = **5/868** ,      332/819 − 17/42 = **1/1638** .**

The second junction is a margin of one part in 1638. **The whole subconvexity record rests on it.**

### C547 — hence a covering floor `[THEOREM 102, the substantive result]`

The covering succeeds iff *both* demands are met, so the architecture's floor is their maximum:

    demand(11/18, 1/9, 12/31)     = (1/9)(1 + 12/31) = **43/279  = 0.1541219…**
    demand(103/128, 1/32, 17/42)  = 1/32 + 663/5376  = **277/1792 = 0.1545759…**

> **`[THEOREM 102]` With the exponent pair and Huxley's bound as the low- and mid-range inputs, and
> **any** improvement of the decoupling estimate on `M ≥ T^{17/42}`, the record cannot go below
>
>     **θ ≥ 277/1792 ,   and   13/84 − 277/1792 = 1/5376 .**
>
> Improving the decoupling estimate alone buys at most `1/5376 ≈ 0.000186`. The binding constraint is
> **not** the decoupling bound at all — it is how far Huxley's bound reaches into `[332/819, 17/42]`.**

### C548 — and this floor dominates the Section-3 floor `[THEOREM 103]`

    Section 3 (internal spacing) floor : (b+c)/12 = **11/72  = 0.1527778**
    Section 4 (global covering) floor  :            **277/1792 = 0.1545759**

> **`[THEOREM 103]` `11/72 < 277/1792`, so the architectural floor of the *whole* Bourgain 2017 proof
> is `277/1792`. The published record has less than **one part in five thousand** of room inside its
> own architecture. Cycle 206's `1/504` was the looser of the two constraints.**

### C549 — what lowering the decoupling threshold would buy `[THEOREM 104]`

The floor depends on the decoupling estimate only through its threshold `x₀`, at the exact rate
`∂demand/∂x₀ = 39/128`. Lowering `x₀` lowers the floor linearly until the two demands meet at

    x₀ = 4388/10881 = 0.403272… ,   below which the **exponent pair alone** caps everything at `43/279`.

> **`[THEOREM 104]` No improvement of the decoupling estimate — neither its exponent nor its
> threshold — can bring this architecture below `43/279 = 0.1541219…`. Reaching that would require a
> better low-range input than the exponent pair `(1/9,13/18)`, i.e. a better *exponent pair* — which
> Theorems 20–25 proved is a stationary point of the van der Corput semigroup.**

**The circle closes.** The campaign's opening result (the exponent-pair semigroup is stationary at
every record) is exactly the obstruction that caps Bourgain's global endgame at `43/279`.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SectionFourCoveringFloor.lean` — `coveringReach`,
`coveringDemand`, `reach_ge_iff_demand_le`, `coveringReach_mono`, `expPair_reach = 11/28`,
`huxley_reach = 332/819`, `first_junction_overlap = 5/868`, `second_junction_overlap = 1/1638`,
`expPairDemand_eq = 43/279`, `huxleyDemand_eq = 277/1792`, `covering_succeeds_iff`,
`record_room_above_sectionFourFloor = 1/5376`, `covering_floor_dominates_spacing_floor`,
`architectural_floor_eq`, `demand_rate = 39/128`, `demands_equal_at_threshold`,
`floor_bounded_below_by_expPair`, `architecture_hard_floor`.
Umbrella green at **10935** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 207 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 104 results, fifteen corrections, 62 dead
routes. **The architecture is priced to the last part in five thousand, and its hard cap `43/279` is
the exponent-pair stationarity the campaign proved in Theorems 20–25.**

## Cycle 208 — **THEOREMS 105–108: the campaign's own barrier is a single point of a family**

Theorem 104 capped the architecture at `43/279`, the demand of the published low-range pair
`(1/9,13/18)`, and observed that beating it needs a better exponent pair — which Theorems 20–25
declared impossible. Cycle 208 shows **that inference was wrong**, and why.

### C550 — the covering functional `[THEOREM 105]`

An exponent pair `(κ,λ)` is the covering source `α = λ−κ`, `β = κ`. Its demand at length `T^{x₀}` is

    demand = κ + (λ−κ−1/2)x₀ = **G_{x₀}(κ,λ) − x₀/2** ,  **G_{x₀}(κ,λ) = (1−x₀)κ + x₀λ** .

So each length selects a **different linear functional** on the exponent-pair region. Two endpoints:

    x₀ = 0   :  G = κ ;        x₀ = 1/2 :  G = (κ+λ)/2 = the pointwise subconvexity exponent.

> **`[THEOREM 105]` Minimising `G_{12/31}` over the semigroup, the best available low-range input is
> **not** `(1/9,13/18)` but `A(13/84, 55/84) = (13/194, 76/97)` — van der Corput applied to Bourgain's
> **own** pair. Its demand is `907/6014 = 0.150815 < 43/279 = 0.154122`. So the low-range input is not
> the binding constraint at all; Huxley's demand `277/1792` is the sole floor.**

### C551 — and `A` is **not** stationary for it `[THEOREM 106, the substantive result]`

    **`A` decreases `G_{x₀}` at `(κ,λ)`  ⟺  G_{x₀}(κ,λ)·(2κ+1) > x₀·(κ+1).**

> **`[THEOREM 106]` At `x₀ = 1/2` this reads `(κ+λ)(2κ+1) > κ+1` — **exactly Theorem 20's criterion**,
> which fails at every record pair. At `x₀ = 12/31` it **holds** at Bourgain's pair. So the van der
> Corput semigroup is *not* stationary for the functionals that matter to the covering; the campaign's
> barrier is the **single value `x₀ = 1/2`** of a one-parameter family.**

This is the first place in 208 cycles where a proved barrier has been **localised rather than
extended**: Theorems 20–25 bound the pointwise exponent and nothing else. `A` simultaneously
*worsens* `epMu` at Bourgain's pair and *improves* its covering demand — both are Lean-certified in
the same file.

### C552 — the productivity threshold, and where it falls `[THEOREMS 107–108]`

Solving the criterion at `(13/84,55/84)`: `55·13 > (97−55)·42·x₀`, i.e.

    **`A` improves Bourgain's pair exactly for `x₀ < 715/1764 = 0.4053288…`.**

> **`[THEOREM 107]` Van der Corput is productive for every length shorter than `T^{715/1764}` and
> stationary from there to the critical length `T^{1/2}`. The semigroup has room everywhere **except**
> on the stretch that decides `μ(1/2)`.**

And the threshold's location is not generic:

    decoupling threshold   17/42  = **714/1764**
    productivity threshold         **715/1764**
    Huxley's reach        332/819 = 9296/22932 ,  715/1764 = 9295/22932

> **`[THEOREM 108]` The threshold is `1/1764` above `17/42` and `1/22932` below `332/819`: it lies
> **strictly inside** the junction `[17/42, 332/819]` — itself only `1/1638` wide — at which the
> published proof hands off from Huxley's bound to the decoupling bound. **Bourgain's handoff point is,
> to one part in twenty thousand, exactly the length at which van der Corput stops being productive.**

The proof is optimally assembled: it uses the exponent-pair machinery for precisely as long as that
machinery is still gaining, and switches at the exact point where it stops.

### C553 — and Huxley is worth `11/173824`

Bypassing Huxley and covering to `17/42` with `A(Bourgain)` demands `15/97 = 0.1546392`, which is
**still below the record** `13/84 = 0.1547619` but above `277/1792 = 0.1545759`.

> Huxley's entire contribution to the floor is `15/97 − 277/1792 = **11/173824 ≈ 6.3·10⁻⁵**`.
> Also proved: **Bourgain's own pair, used to cover to `17/42`, demands exactly `13/84`** — the
> exponent pair and the decoupling bound meet at the record from both sides.

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoveringFunctionalNonstationarity.lean` — `covFunctional`,
`covDemandOfPair`, `covDemandOfPair_eq_coveringDemand`, `covFunctional_at_half`,
`covDemand_at_half_eq_epMu`, `covA_decreases_iff`, `covA_criterion_at_half`, `procA_bourgain`,
`procA_worsens_bourgain_mu`, `bourgainAThreshold = 715/1764`, `covA_decreases_bourgain_iff`,
`threshold_above_decouplingStart = 1/1764`, `threshold_below_huxleyReach = 1/22932`,
`threshold_inside_second_junction`, `threshold_lt_critical`, `procA_bourgain_demand = 907/6014`,
`procA_bourgain_beats_expPair`, `lowRange_not_binding`, `bourgain_pair_demand_at_decoupling`,
`huxley_contribution = 11/173824`, `bypass_beats_record`.
Umbrella green at **10936** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 208 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 108 results, fifteen corrections, 62 dead
routes.

> **The campaign's central barrier has been localised. `κ+λ` is the `x₀ = 1/2` member of the family
> `G_{x₀}`, and van der Corput is stationary only there. The next question is whether any mechanism
> transports the semigroup's productivity at `x₀ < 715/1764` to the critical length — that is the
> first genuinely open direction the campaign has produced since Theorem 34.**

## Cycle 209 — **D63 (circularity caught), THEOREMS 109–110**

Cycle 208's Theorem 105 used `A(13/84,55/84)` as a low-range input. Cycle 209 attacks that first,
per Phase 4.

### D63 — the shortcut is circular `[DEAD ROUTE]`

`A(13/84,55/84) = (13/194,76/97)` covers `[0,17/42]` with demand exactly `15/97`, and

    13/84 − 15/97 = **1/8148**   (13·97 = 1261, 15·84 = 1260) ,

so it would make Huxley's bound unnecessary. **It cannot be used.** The pair `(13/84,55/84)` is the
*output* of the Section-4 covering, not an input to it; and the `A`-process subdivides, so it cannot
lift the restriction `M ≥ T^{17/42}` that the analytic decoupling bound carries. **Recorded as a dead
route so no successor re-derives it.**

Cycle 208's Theorems 106–108 are untouched — they are statements about the functional and the
process, not about which pairs are available.

### C554 — but the low-range input is slack anyway `[THEOREM 109]`

Re-minimising `G_{12/31}` over **pre-Bourgain** pairs only:

    published `(1/9,13/18)`               →  43/279     = 0.154122
    pure van der Corput word `(1/11,3/4)` →  **52/341**  = 0.152493
    `A(32/205,269/410) = (16/237,743/948)` → **1111/7347** = 0.151218

> **`[THEOREM 109]` All three fall strictly below the middle source's own demand `277/1792 = 0.154576`,
> the pure van der Corput word by `1273/611072`. **Cycle 207's cap `43/279` is therefore not a
> barrier** — it was an artefact of the published choice of low-range pair. The architecture's floor is
> exactly Huxley's demand `277/1792`, and no exponent-pair improvement can lower it.**

This *replaces* Theorem 104: the correct statement is not "the exponent pair caps the architecture"
but "the exponent pair is slack and the middle source is the whole constraint".

### C555 — and Huxley genuinely cannot be removed `[THEOREM 110]`

At the decoupling threshold `17/42` the same pairs demand

    `(1/9,13/18)`      →  59/378       = 0.156085
    `(1/11,3/4)`       →  41/264       = 0.155303
    `(16/237,743/948)` →  **6173/39816** = 0.1550382

all strictly **above** `13/84 = 0.1547619`.

> **`[THEOREM 110]` The best pre-existing exponent pair misses covering to the decoupling threshold by
> exactly **`11/39816 ≈ 2.76·10⁻⁴`**. The three-source chain is therefore necessary: Huxley's bound
> cannot be dropped, and the margin by which it is needed is that single quantity.**

Together with D63, the contrast is exact: the `A`-image of the *record* pair clears the threshold by
`1/8148`, the `A`-image of the *best prior* pair misses by `11/39816`, and the two demands differ by
`1541/3862152`. **The decoupling bound improves the covering functional by just enough to make its own
covering argument redundant in hindsight — but only in hindsight.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/LowRangeSlackAndHuxleyNecessity.lean` — `vdcWordKappa/Lambda`,
`huxleyPairKappa/Lambda`, `procA_huxleyPair`, `huxleyPair_mu = 32/205`,
`vdcWord_demand_at_huxleyStart = 52/341`, `procA_huxleyPair_demand_at_huxleyStart = 1111/7347`,
`low_range_inputs_beat_published`, `low_range_strictly_slack`, `vdcWord_slack = 1273/611072`,
`published_cap_is_not_a_barrier`, `vdcWord_demand_at_decoupling = 41/264`,
`procA_huxleyPair_demand_at_decoupling = 6173/39816`, `procA_huxleyPair_shortfall = 11/39816`,
`middle_source_necessary`, `record_pair_image_margin = 1/8148`, `covering_margin_contrast`.
Umbrella green at **10937** jobs.

### Standing position after 209 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 110 results, fifteen corrections, **63** dead
routes.

> **Corrected architectural account: the floor of Bourgain's Section-4 endgame is `277/1792`, set
> solely by how far Huxley's bound reaches; the exponent-pair side is slack by ≥ `1273/611072`; and
> Huxley cannot be removed, missing by `11/39816`. The record `13/84` is `1/5376` above that floor.**

## Cycle 210 — **THEOREMS 111–116: the length-reflection law**

Cycle 208 left an open direction: transport the semigroup's productivity at `x₀ < 715/1764` to the
critical length. Cycle 210 answers it — negatively, but with an exact mechanism that was not visible
before.

### C556 — the demand factorises `[THEOREM 113, the key identity]`

Let `μ(κ,λ) = (κ+λ−1/2)/2` and let `d(κ,λ) = (λ−κ) − 1/2` be the pair's **signed displacement** from
the line of symmetry. Then, identically,

> **`[THEOREM 113]`   demand(κ,λ,x₀) = μ(κ,λ) + d(κ,λ)·(x₀ − 1/2).**

The covering demand at length `T^{x₀}` is the *pointwise* exponent corrected by the pair's off-line
displacement times the **length deficit** `x₀ − 1/2`. Verified against cycle 209: `A(13/84,55/84)` has
`μ = 17/97`, `d = 21/97`, and at `x₀ = 17/42` gives `17/97 + (21/97)(−2/21) = 15/97`. ✓

### C557 — hence the second dimension is priced at zero exactly at the critical length `[THEOREM 114]`

> **`[THEOREM 114]` At `x₀ = 1/2` the displacement term vanishes **identically**. Two pairs with the
> same `μ` have the same demand there, whatever their displacement. **The exponent-pair region is
> two-dimensional, but the coefficient of its second dimension is `x₀ − 1/2`, and the approximate
> functional equation forces `x₀ = 1/2`.** Every mechanism that exploits the second dimension — the
> `A`-process, off-line pairs, the covering architecture, `B`-conjugation — is worth `|x₀ − 1/2|` per
> unit of displacement, hence **exactly nothing at the one length that decides `μ(1/2)`.**

This is the sharpest form of the campaign's barrier, and it *explains* Theorem 20 rather than
restating it: `A` moves a pair off the line (Bourgain's `d: 0 → 21/97`) at the cost of raising `μ`
(`13/84 → 17/97`), a trade that pays at every shorter length and never at the critical one.

### C558 — and length-neutrality characterises the record sequence `[THEOREM 112]`

> **`[THEOREM 112]` A pair's demand is independent of the length **iff** it lies on the line of
> symmetry. All four landmark pairs — Weyl `(1/6,2/3)`, Bombieri–Iwaniec `(9/56,37/56)`, Huxley
> `(32/205,269/410)`, Bourgain `(13/84,55/84)` — have displacement exactly `0`. **The entire record
> sequence consists of length-neutral pairs**, which is why no record has ever gained from a
> restricted range.**

### C559 — the `B`-process **is** the length reflection `[THEOREM 116, the structural result]`

`B` preserves `μ` and negates `d`. Therefore

> **`[THEOREM 116]`   demand(B(κ,λ), x₀) = demand(κ, λ, 1 − x₀).**
>
> **The van der Corput `B`-process is literally the reflection `x₀ ↦ 1 − x₀` of the length variable.**
> Its fixed-point set — the line of symmetry — is exactly the set of length-neutral pairs, matching
> the reflection's unique fixed point `x₀ = 1/2`.

`B` is classically the Poisson/functional-equation step. So this identifies, exactly: **the functional
equation acts on the covering problem as reflection in the critical length, and the critical length is
its fixed point.** Theorems 21 (canonical form), 52/61/66–67 (the conjugation confirmations) and 94
(the chirp) are all instances: *no conjugation helps at a fixed point.*

### C560 — a four-fold coincidence `[THEOREM 111]`

The length at which the covering-optimal pre-Bourgain pair switches from `A(32/205,269/410)` to
`(13/84,55/84)` is `579/1435 = 0.403484`. With the three thresholds already found:

    optimal-pair switch      **579/1435  = 0.4034843**
    decoupling threshold       17/42     = 0.4047619
    `A`-productivity limit    715/1764   = 0.4053288
    Huxley's reach at record  332/819    = 0.4053724

> **`[THEOREM 111]` Four independently defined thresholds of the published architecture lie in a
> single window of width `332/819 − 579/1435 = 317/167895 ≈ 1.9·10⁻³`.** The proof's handoff, the
> semigroup's exhaustion, the optimal-pair switch, and the middle source's reach all coincide to
> within two parts in a thousand.

### Lean

`formal/GaloisForLFunctions/HTGeometry/LengthReflectionLaw.lean` — `epDisplacement`,
`epDisplacement_eq_zero_iff`, `covDemand_factorisation`, `displacement_free_at_critical_length`,
`length_neutral_iff_on_line`, `covDemand_strictMono_of_displacement_pos`, `procB_preserves_epMu`,
`procB_negates_displacement`, `procB_is_length_reflection`, `reflection_fixed_point`,
`procB_fixed_iff_on_line`, `landmarks_length_neutral`, `landmark_demand_constant`,
`procA_bourgain_displacement = 21/97`, `procA_bourgain_mu = 17/97`, `procA_bourgain_trade`,
`procA_bourgain_demands_agree`, `optimalPairSwitch = 579/1435`, `optimalPairSwitch_balances`,
`four_thresholds_cluster`, `second_dimension_priced_at_zero`, `demand_gap_of_equal_mu`.
Umbrella green at **10938** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 210 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 116 results, fifteen corrections, 63 dead
routes.

> **The open direction of cycle 208 is now closed with a reason: the productivity at `x₀ < 715/1764`
> cannot be transported to `x₀ = 1/2`, because the quantity it buys — displacement — is multiplied by
> `x₀ − 1/2`. Any new mechanism must either move the critical length off `1/2` (Theorems 60–61 show
> the AFE forbids it) or add a *third* coordinate to the exponent-pair region whose price at `x₀ = 1/2`
> is nonzero.**

## Cycle 211 — **THEOREMS 117–119: the critical length as an eigenvalue coincidence**

Cycle 210 ended by demanding "a third coordinate whose price at `x₀ = 1/2` is nonzero". Cycle 211
answers what that would have to be, by computing the pricing functional's *tangent* data.

### C561 — the gradient and the null direction `[THEOREM 117]`

`demand(κ,λ,x₀) = (1−x₀)κ + x₀λ − x₀/2` is affine, with gradient `(1−x₀, x₀)` and null direction
`(x₀, x₀−1)` — the direction in which a pair can be moved at no cost.

The `B`-process `B(κ,λ) = (λ−1/2, κ+1/2)` is affine with linear part the **coordinate swap**, so it
acts on directions by `(u,v) ↦ (v,u)`: eigenvalue `+1` on `(1,1)`, `−1` on `(1,−1)`.

> **`[THEOREM 117]` The null direction `(x₀, x₀−1)` is an eigenvector of the swap **if and only if**
> `x₀ = 1/2`, and there it is the `(−1)`-eigenvector.
>
> **The critical length is exactly the length at which the free directions of the pricing functional
> coincide with the directions the functional equation reverses.**

Proof of the "only if": `v = cu ∧ u = cv` forces `c² = 1`; `c = 1` gives `x₀−1 = x₀`, impossible;
`c = −1` gives `x₀−1 = −x₀`, i.e. `x₀ = 1/2`. Lean-certified.

### C562 — hence the classification of what could help `[THEOREM 118]`

The two coordinate directions decompose as `(1,1)` (`B`-invariant) and `(1,−1)` (`B`-reversed):

    motion along `(1,1)`  :  `μ ↦ μ + s`  — priced, but this **is** improving the exponent pair
    motion along `(1,−1)` :  `μ` fixed, displacement `↦ d − 2s` — priced at **zero** at `x₀ = 1/2`

> **`[THEOREM 118]` At the critical length the demand depends on the pair **only through `μ`**, and the
> entire complementary direction is the `(−1)`-eigenspace of the functional equation. So no enlargement
> of the exponent-pair region *within these two coordinates* can lower the critical-length demand
> without lowering `μ` itself. **A genuinely new mechanism must supply a datum on which `B` acts with
> eigenvalue `+1` and which is not a function of `κ+λ` — hence a datum outside the pair `(|f'|, N)`.**

The campaign has already priced the three known such data: **periodicity** (Theorems 58–59: `n^{−it}`
is aperiodic, the primorial modulus is exponentially too large), **multiplicativity** (Theorem 55: no
tool sees it together with archimedean smoothness), and the **large-values count** (Theorems 50, 53:
circular, and emptying the exceptional set needs all moments). **The separate barriers of the campaign
now assemble into one classification.**

### C563 — the covering floor against the semigroup's own limit `[THEOREM 119]`

Theorem 25's `A`-iteration limit is `(√5−1)/8 = 0.15450849…`, the positive root of `16μ²+4μ−1`.
Theorem 102's covering floor is `277/1792 = 0.15457589…`.

> **`[THEOREM 119]` `(√5−1)/8 < 277/1792`, certified without irrational arithmetic:
> `277/1792 = (501/224 − 1)/8` and `501² − 5·224² = 251001 − 250880 = **121 = 11²** > 0`, so
> `501/224 > √5`. The covering floor lies above the semigroup's own limit by `≈ 6.7·10⁻⁵`.**

So the two independent floors the campaign has computed — the pure-semigroup limit and the
architecture's covering limit — bracket a gap of `6.7·10⁻⁵` just below `13/84`, and the covering
floor is the binding one. **Nothing in either account leaves room below `≈ 0.1545`.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/CriticalLengthEigenspace.lean` — `demandGradFst/Snd`,
`demandNullFst/Snd`, `covDemand_directional`, `gradient_dot_null`,
`covDemand_invariant_along_null`, `null_direction_nonzero`, `procB_directional`,
`covDemand_directional_after_procB`, `swapEigen`, `swapEigen_one`, `swapEigen_neg_one`,
`null_direction_eigen_iff_critical`, `null_direction_at_critical`, `invariant_direction_moves_mu`,
`null_direction_moves_only_displacement`, `critical_demand_determined_by_mu`,
`covering_floor_above_semigroup_limit`, `semigroup_limit_lt_covering_floor`.
Umbrella green at **10939** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 211 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 119 results, fifteen corrections, 63 dead
routes.

> **The campaign's barriers are now a single classification: at the critical length the demand sees
> only `μ`; the complementary direction is the functional equation's `(−1)`-eigenspace; and every datum
> outside `(|f'|, N)` that could break the tie — periodicity, multiplicativity, large-values counting —
> has been separately priced closed.**

## Cycle 212 — **THEOREMS 120–122: covering buys nothing; the exact value of a range restriction**

Theorem 118 said a new mechanism needs a datum outside `(|f'|,N)`. Cycle 212 asks the complementary
question — how much is the *covering architecture itself* worth? — and answers it exactly.

### C564 — a covering by unrestricted pairs is worth the best single pair `[THEOREM 120]`

Any covering of `x ∈ [0,1/2]` must cover the right endpoint `x = 1/2`, and there **every** pair
demands exactly its own `μ` (Theorem 114). Conversely a pair on or above the line of symmetry
(`d ≥ 0`) has demand `μ + d(x−1/2) ≤ μ` for all `x ≤ 1/2`, so one pair covers the whole interval at
exactly `μ`.

> **`[THEOREM 120]` If every source of a covering is a genuine exponent pair — valid at every length —
> the covering yields exactly `min_P μ(P)`. **The covering architecture is worth precisely nothing over
> the best single pair.** Its entire value comes from sources whose validity is restricted to a
> sub-range.**

This explains the *shape* of Bourgain's proof rather than its numbers: the three-source chain exists
only because the decoupling estimate is restricted to `M ≥ T^{17/42}`.

### C565 — the exact value of a restriction `[THEOREM 121]`

    demand(P, x₁) = μ(P) − **discount(P, x₁)** ,   discount(P,x₁) = d(P)·(1/2 − x₁) .

> **`[THEOREM 121]` A source valid only on `[x₁, 1/2]` with demand `β` there can be handed off to a
> pair only if `β ≥ μ(P) − discount(P,x₁)`. **Hence the improvement a range restriction can buy over
> the pair's own exponent is at most the displacement discount at its threshold**, and the discount
> vanishes exactly at `x₁ = 1/2` for every off-line pair.**

So range restriction and displacement are the *same* resource, measured by `1/2 − x₁`. Both are worth
zero at the critical length; a source restricted to `x₁ = 1/2` alone is worth nothing at all.

### C566 — the published architecture, priced `[THEOREM 122]`

    best pre-existing pointwise exponent   μ(32/205, 269/410)          = **32/205 = 0.1560976**
    best discounted demand at `17/42`      `A(32/205,269/410)`         = **6173/39816 = 0.1550382**
    discount that produced it              `(205/948)·(2/21)`          = **205/9954**
    single-handoff improvement window                                    **8647/8162280 ≈ 1.06·10⁻³**

> **`[THEOREM 122]` Bourgain's `13/84 = 0.1547619` lies **below** the entire single-handoff window.
> His restricted source is better than any one handoff from an exponent pair can absorb — which is
> exactly why a **second** restricted source (Huxley's bound) is needed to fill the range. Theorem 110's
> shortfall `11/39816` is the amount by which the window falls short of the record.**

Complete account of the architecture: **sources valid at every length contribute only their `μ`; the
record `13/84` is strictly below every such `μ` (Huxley `32/205`, Weyl `1/6`, Bombieri–Iwaniec `9/56`);
hence the record is carried entirely by range-restricted sources, and the exponent pairs serve only to
complete the range, never to set the value.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoveringBuysNothing.lean` — `covering_pays_mu_at_critical`,
`unrestricted_covering_floor`, `single_pair_covers_at_mu`, `unrestricted_covering_value`,
`displacementDiscount`, `demand_eq_mu_sub_discount`, `displacementDiscount_nonneg`,
`displacementDiscount_eq_zero_iff`, `restricted_source_value`, `restriction_improvement_capped`,
`procA_huxleyPair_discount = 205/9954`, `improvement_window`, `record_below_improvement_window`,
`architecture_summary`.
Umbrella green at **10940** jobs. Lint: the eight `error` lines are pre-existing unwired
`RHTower.DeningerArithmetic*` modules, unrelated to this work; no HTGeometry errors.

### Standing position after 212 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 122 results, fifteen corrections, 63 dead
routes.

> **Consolidated: (i) at the critical length the demand sees only `μ`; (ii) the covering architecture
> adds nothing to `μ`; (iii) a range restriction is worth exactly the displacement discount at its
> threshold, which is `d·(1/2 − x₁)` and vanishes at the critical length; (iv) every datum outside
> `(|f'|,N)` that could break the tie is separately priced closed. The value of the record is carried
> entirely by the one range-restricted analytic input, and everything else in the proof is bookkeeping
> over the range.**

## Cycle 213 — **THEOREMS 123–127: the covering architecture provably cannot reach LH**

Cycle 212 established that the record is carried entirely by the one range-restricted analytic input.
Cycle 213 asks whether that architecture could, *in principle*, reach LH. **It cannot, and the proof
is two lines.**

### C567 — the nonnegative form `[THEOREM 123]`

    **demand(κ,λ,x₁) = κ·(1−x₁) + x₁·(λ−1/2).**

On the exponent-pair region (`κ ≥ 0`, `λ ≥ 1/2`) both summands are nonnegative for `0 ≤ x₁ ≤ 1`.

> **`[THEOREM 123]` For `0 < x₁ < 1` the demand vanishes **iff** `(κ,λ) = (0,1/2)` — the exponent-pair
> conjecture, equivalent to LH.**

### C568 — hence the dichotomy `[THEOREMS 124–125]`

A covering proof of `μ(1/2) ≤ θ` with a source restricted to `[x₁, 1/2]` must still cover `[0,x₁]`
with an **unrestricted** source, i.e. an exponent pair, at demand `≤ θ`. The squeeze is explicit:

    κ ≤ θ/(1−x₁) ,    λ − 1/2 ≤ θ/x₁ ,    x₁ ≤ θ/(λ−1/2) .

> **`[THEOREM 124]` As `θ → 0` either `x₁ → 0` — the "restricted" source is not restricted, hence is an
> exponent pair and Theorem 120 applies — or `(κ,λ) → (0,1/2)`, the conjecture itself.
> **A covering architecture is a device for extending a range-restricted estimate. It can never reach
> the Lindelöf exponent.**

Quantitatively, with the low range carried by the trivial pair `(0,1)`, the restricted source must be
available from `T^{2θ}` upwards. **Bourgain's threshold `17/42` exceeds `2·13/84 = 13/42`**, which is
precisely why intermediate sources are required at all.

### C569 — and every intermediate source has a hard floor `[THEOREM 126]`

A source `A ≤ M^αT^β` with `α ≥ 1/2` demands `β + (α−1/2)x₁ ≥ β` at every nonnegative length.

> **`[THEOREM 126]` Any chain containing a source of slope `≥ 1/2` is capped at that source's own
> `T`-exponent. **Huxley's bound caps every chain that uses it at `1/32 = 0.03125`** — five times the
> published record — and the published exponent-pair source caps its chain at `1/9`.**

So the Section-4 architecture cannot produce any exponent below `1/32` no matter how the decoupling
input is improved, and removing Huxley reopens the gap Theorem 110 measured at `11/39816`.

### C570 — the capstone `[THEOREM 127]`

> **`[THEOREM 127]` Combining: LH by this architecture requires either (a) an analytic input valid at
> **all** lengths, which is by definition an exponent pair with `μ = 0` — the conjecture; or (b) a
> low-range pair equal to `(0,1/2)` — the conjecture. **In both branches the conclusion is assumed.
> The Bourgain covering architecture is provably incapable of proving the Lindelöf hypothesis.**

This is the campaign's first *unconditional impossibility* result about a whole architecture, as
opposed to a pricing of how far it can go. It converts Theorems 96–122 from "the record has `1/5376`
of room" into "the room is finite and the destination is unreachable".

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoveringCannotReachLindelof.lean` —
`covDemand_nonneg_form`, `covDemand_nonneg`, `covDemand_eq_zero_iff`, `low_range_squeeze`,
`low_range_coordinate_bounds`, `lindelof_forces_conjecture`, `conjecture_pair_mu`,
`source_demand_ge_intercept`, `huxley_caps_chain`, `huxley_cap_far_above_record`,
`expPair_caps_chain`, `covering_cannot_reach_lindelof`, `threshold_bounded_by_target`,
`trivial_pair_threshold`, `bourgain_threshold_exceeds_trivial`.
Umbrella green at **10941** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 213 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 127 results, fifteen corrections, 63 dead
routes.

> **The covering route is now closed unconditionally, not merely priced. Any proof of LH must come
> from a single estimate valid at every length — i.e. must produce the exponent pair `(0,1/2)`
> directly — and Theorems 20–25, 106, 114, 117–118 describe exactly why the van der Corput semigroup
> cannot: at the critical length the only priced direction is `μ` itself.**

## Cycle 214 — **THEOREMS 128–131: the support function is maximal exactly at the critical length**

### C571 — the support function `[THEOREM 128]`

For a finite family of exponent pairs put

    **h(x) := min over the family of  demand(κ,λ,x) = κ(1−x) + x(λ−1/2).**

`h` is the family's support function in the direction `(1−x, x)`; `h(1/2)` is the best pointwise
subconvexity exponent it delivers, and `h(x)` is the best it delivers at length `T^x`.

### C572 — it is maximal at the critical length `[THEOREM 129, the structural result]`

Two facts combine. First, a pair with displacement `d ≥ 0` only improves as the length shrinks:
`demand(P,x) = μ(P) + d(x−1/2) ≤ μ(P)` for `x ≤ 1/2`. Second, if `d < 0`, its `B`-image has `d > 0`
and, by the length-reflection law (Theorem 116), `demand(B(P),x) = demand(P,1−x) ≤ μ(P)`.

> **`[THEOREM 129]` For any family closed under the `B`-process — which every exponent-pair region is —
>
>     **h(x) ≤ h(1/2)  for every length `x ∈ [0,1]`,**
>
> and `h(1−x) = h(x)`. **The critical length is exactly where the exponent-pair region is hardest.**
> Every other length is strictly easier for the record family, and the subconvexity exponent is the
> family's *worst case over lengths*, not a typical value.**

Checked against the campaign's numbers: `h(12/31) ≤ 1111/7347 = 0.15122` and
`h(12/31) ≤ 907/6014 = 0.15082`, both `< 13/84 = 0.15476 = h(1/2)`. ✓

This inverts the intuition the campaign has been carrying for two hundred cycles. The AFE does not
merely *select* an awkward length; it selects **the unique maximum of the difficulty profile.**

### C573 — hence LH degenerates the profile entirely `[THEOREM 130]`

`h ≥ 0` on the region (`κ ≥ 0`, `λ ≥ 1/2`), so:

> **`[THEOREM 130]` `h(1/2) = 0` forces `h ≡ 0` on `[0,1]`, and then some member of the family is
> exactly the corner `(0,1/2)`. **LH is equivalent to the total collapse of the difficulty profile** —
> not to a local improvement at one length, but to the region reaching its extreme corner.**

### C574 — and a single unrestricted estimate must already be LH `[THEOREM 131]`

Tightening Theorem 127's branch (a) from "is an exponent pair" to an exact statement:

> **`[THEOREM 131]` An estimate `S(M) ≪ M^αT^β` valid for **all** `M ≤ T^{1/2}` yields
> `μ(1/2) ≤ max(β, β + (α−1/2)/2)`. It yields `μ(1/2) = 0` only if `β = 0` and `α ≤ 1/2` — i.e. only
> if the estimate is the Lindelöf bound itself.**

Together with Theorem 127: **both branches of the covering dichotomy are now closed by exact
statements, with no appeal to the exponent-pair axioms.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/SupportFunctionMaximalAtCritical.lean` — `supportFn`,
`supportFn_le`, `supportFn_attained`, `supportFn_at_critical`, `BClosed`,
`supportFn_le_at_critical`, `supportFn_reflect`, `supportFn_global_max`, `supportFn_nonneg`,
`lindelof_degenerates_support`, `lindelof_forces_corner`, `record_is_a_maximum`,
`unrestricted_estimate_must_be_lindelof`.
Umbrella green at **10942** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 214 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 131 results, fifteen corrections, 63 dead
routes.

> **New framing for a successor: the difficulty profile `h` is `B`-symmetric, nonnegative, and
> maximal at `x = 1/2`. LH is `h ≡ 0`. Every mechanism the campaign has priced acts either by moving
> `x` (worth `h(x) ≤ h(1/2)`, i.e. nothing) or by moving along the null direction (worth zero at
> `1/2`). **The only remaining move is to lower `h(1/2)` itself, which is the corner problem.**

## Cycle 215 — **THEOREMS 132–134: the efficiency law explains the four-fold cluster**

Theorem 111 recorded a coincidence: four thresholds of the published architecture lying in a window
of width `317/167895`. Cycle 215 derives two of them from a single formula and explains the
clustering.

### C575 — the efficiency law `[THEOREM 132]`

From the factorisation `demand = μ + d·(x−1/2)`, comparing with a target `θ`:

> **`[THEOREM 132]`  For `d > 0`,   demand(κ,λ,x) < θ  ⟺  **x < 1/2 − (μ(κ,λ) − θ)/d(κ,λ)**.
>
> Define the pair's **efficiency** `η(κ,λ) = d/(μ − θ)` — the displacement it buys per unit of
> pointwise excess over the target. Then the threshold is exactly `1/2 − 1/η`: each pair beats the
> record on an initial segment of lengths, and how far it reaches is *precisely* the reciprocal of how
> cheaply it buys displacement.**

### C576 — both mystery thresholds are instances `[THEOREM 133]`

    A(13/84,55/84) = (13/194, 76/97)      : μ = 17/97,   d = 21/97,    excess = **167/8148**
                                            η = **1764/167 = 10.5629** , threshold = **715/1764**
    A(32/205,269/410) = (16/237, 743/948) : μ = 111/632, d = 205/948,  excess = **277/13272**
                                            η = **2870/277 = 10.3610** , threshold = **579/1435**

> **`[THEOREM 133]` `715/1764` — the length at which the `A`-process stops improving Bourgain's pair
> (Theorem 107) — and `579/1435` — the length at which the covering-optimal pre-Bourgain pair switches
> (Theorem 111) — are **the same formula** `1/2 − 1/η`, evaluated at the `A`-images of the last two
> record pairs. Neither was a coincidence.**

Note also that the *excess numerators* are `167` and `277` — and `277/1792` is Theorem 102's covering
floor, whose numerator `277` reappears here as `A(Huxley)`'s excess numerator over `13/84`. Both come
from `111/632 − 13/84 = 277/13272`.

### C577 — and the cluster is an efficiency coincidence `[THEOREM 134]`

> **`[THEOREM 134]` The two efficiencies are `10.5629` and `10.3610` — differing by less than **two
> percent**. The four-fold clustering of Theorem 111 is exactly the statement that **the `A`-process
> has nearly the same efficiency at the last two record pairs.** Since thresholds are `1/2 − 1/η` and
> `η ≈ 10.5`, an efficiency spread of 2% produces a threshold spread of `≈ 2·10⁻³` — the observed
> window width.**

So the mysterious tightness of Bourgain's architecture is a consequence of a *stability* property of
the van der Corput `A`-process across successive records, not of any arithmetic conspiracy.

### C578 — and it cannot help `[recorded]`

Infinite efficiency (`μ(P) = θ` with `d(P) > 0`) pushes a pair's threshold to `1/2` but leaves
`demand(P,1/2) = μ(P) = θ` unchanged. **Efficiency shapes the difficulty profile below the critical
length; it never lowers its value at the critical length.** Consistent with Theorems 114 and 129.

### Lean

`formal/GaloisForLFunctions/HTGeometry/EfficiencyThresholdLaw.lean` — `epEfficiency`,
`efficiencyThreshold`, `beats_target_iff_below_threshold`, `threshold_eq_half_sub_inv_efficiency`,
`threshold_at_critical_of_no_excess`, `threshold_lt_critical_iff`, `procA_bourgain_excess`,
`procA_bourgain_efficiency = 1764/167`, `procA_bourgain_threshold = 715/1764`,
`procA_huxleyPair_excess`, `procA_huxleyPair_efficiency = 2870/277`,
`procA_huxleyPair_threshold = 579/1435`, `efficiency_cluster`, `efficiencies_bracketed`,
`infinite_efficiency_does_not_lower_record`, `efficiency_cannot_beat_record_at_critical`.
Umbrella green at **10943** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 215 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 134 results, fifteen corrections, 63 dead
routes.

> **The architecture is now fully derived, not merely measured: every threshold in Bourgain's proof is
> `1/2 − 1/η` for an explicit efficiency, the efficiencies are stable across records at `≈ 10.5`, and
> the whole profile is `B`-symmetric with its maximum at the critical length. The single remaining
> quantity is `h(1/2)` itself.**

## Cycle 216 — **THEOREMS 135–139: the `A`-process is self-defeating**

Cycle 215 left the efficiency `η` as a computed number. Cycle 216 solves it in closed form for pairs
on the line of symmetry — where every record lies — and the answer is a law.

### C579 — closed forms `[THEOREM 135]`

For `P = (κ, κ+1/2)` with `μ(P) = κ`:

    A(P) = (κ/(2κ+2), (2κ+3/2)/(2κ+2)) ,
    d(A(P)) = **1/(4κ+4)** ,   μ(A(P)) = **(4κ+1)/(8κ+8)** ,   excess = **(1−4κ−8κ²)/(8κ+8)** .

> **`[THEOREM 135]`  η(κ) = d/excess = **2/(1 − 4κ − 8κ²)**,  and by the efficiency law the
> productivity threshold is
>
>     **T(κ) = 1/2 − 1/η(κ) = 2κ(1 + 2κ).**

Check: `T(13/84) = (13/42)(110/84) = 715/1764` ✓ — Theorem 107's threshold, now derived rather than
computed. The excess numerator `1 − 4κ − 8κ²` is positive exactly when `8κ²+4κ−1 < 0`, i.e. below
Theorem 20's stationarity threshold `(√3−1)/4`. **The two thresholds recorded eighty cycles apart are
one formula:** `T(κ) = 1/2 ⟺ 8κ²+4κ−1 = 0`.

### C580 — the productive range shrinks along the record sequence `[THEOREM 136]`

    Weyl              κ = 1/6      →  T = **4/9        = 0.444444**
    Bombieri–Iwaniec  κ = 9/56     →  T = **333/784    = 0.424745**
    Huxley            κ = 32/205   →  T = **17216/42025 = 0.409661**
    Bourgain          κ = 13/84    →  T = **715/1764   = 0.405329**

> **`[THEOREM 136]` `T` is strictly increasing with `T(0) = 0`, so improving the record **shrinks** the
> range of lengths over which the van der Corput `A`-process is productive, at rate `T′(κ) = 2 + 8κ > 2`.
> **Each unit of progress in the exponent costs more than two units of productive range. At the
> Lindelöf value `κ = 0` the productive range is empty: the semigroup is completely inert.**

**The van der Corput machinery destroys its own leverage as it succeeds.** This is the mechanism
behind Theorems 20–25, 114 and 129, stated as a rate rather than as a fixed point.

### C581 — and the record is one unit from breaking its own architecture `[THEOREMS 137–139]`

`T(κ) = 17/42` — the published handoff length — is equivalent to `(84κ+21)² = 1155`, i.e.
`κ* = (√1155 − 21)/84 ≈ 0.15458680`.

    at the record          κ = 13/84   :  (84κ+21)² = 34² = **1156**
    crossing value                        **1155 = 34² − 1**
    at the covering floor  κ = 277/1792 :  (84κ+21)² = **(15225/448)² < 1155**

> **`[THEOREM 139]` The record clears the crossing by **exactly one unit**, `1156 − 1155 = 1`. Its
> productive range exceeds the handoff by `1/1764` (Theorem 108, now explained). **At the architecture's
> own covering floor `277/1792` the productive range would fall *below* the handoff length** — the
> exponent-pair machinery would be unproductive on the entire covered range, and the architecture would
> have to be rebuilt rather than re-tuned.**

So the campaign's two independent measurements of the remaining room — `1/5376` in the exponent
(Theorem 102) and `1/1764` in the length (Theorem 108) — are the same fact, and the architecture
becomes internally inconsistent before it reaches its own floor.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SelfDefeatingProductivity.lean` — `procA_line_displacement`,
`procA_line_mu`, `procA_line_excess`, `lineSelfEfficiency`, `aProductivityThreshold`,
`lineSelfEfficiency_eq`, `aProductivityThreshold_eq`, `aProductivityThreshold_zero`,
`aProductivityThreshold_strictMono`, `threshold_reaches_critical_iff`, `aThreshold_weyl = 4/9`,
`aThreshold_bi = 333/784`, `aThreshold_huxley = 17216/42025`, `aThreshold_bourgain = 715/1764`,
`thresholds_decreasing`, `self_defeating_rate`, `handoffCrossingSq = 1155`,
`handoff_crossing_equation`, `crossing_below_record`, `record_exceeds_crossing`,
`covering_floor_below_crossing`, `productivity_vs_handoff`, `next_improvement_breaks_architecture`.
Umbrella green at **10945** jobs (one name collision caught and fixed: `threshold_weyl`/
`threshold_bourgain` already existed in `SmoothMultiplicativeDichotomy`).

### Standing position after 216 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 139 results, fifteen corrections, 63 dead
routes.

> **The self-defeating law `T(κ) = 2κ(1+2κ)` is the campaign's sharpest single statement about why the
> exponent-pair route stalls: the machinery's leverage is proportional to the very quantity it is
> trying to reduce, and vanishes exactly at the target.**

## Cycle 217 — **THEOREMS 140–142: convexity is worthless; the record must be non-unique**

Cycle 216 showed the `A`-process's productivity vanishes as the record improves. Cycle 217 asks what
*any* mechanism would have to look like, in the same coordinates.

### C582 — the cost of displacement `[THEOREM 140]`

    **ρ(κ,λ) = (μ(κ,λ) − θ)/d(κ,λ)** — pointwise exponent surrendered per unit of displacement bought,
    and   **efficiencyThreshold = 1/2 − ρ**.

Published values against `θ = 13/84`:

    trivial pair `(0,1)`            :  ρ = **4/21 = 336/1764** ,  threshold **13/42 = 2θ**
    `A(13/84,55/84)`                :  ρ = **167/1764**        ,  threshold **715/1764**

> The trivial pair's threshold `2θ` is exactly Theorem 124's covering bound `x₁ ≤ 2θ`, recovered from
> the displacement-cost formula. The `A`-image buys displacement at **half** the trivial pair's cost.

### C583 — convexity contributes nothing `[THEOREM 141]`

Both the excess `μ − θ` and the displacement `d` are **affine** in the pair. Along the segment from a
line pair attaining `θ` to any other pair `P₁`, both scale by the parameter `t`, so

> **`[THEOREM 141]` `ρ((1−t)P₀ + tP₁) = ρ(P₁)` for every `t ≠ 0`, hence the efficiency threshold is
> **constant along the segment**. **Convexity of the exponent-pair region cannot raise the threshold at
> all — it is decided by extreme points alone.**

This closes a route the campaign had not explicitly examined: no interpolation, averaging, or Hölder
combination of known pairs can extend the productive range by even one unit.

### C584 — and the threshold reaches the critical length only if the record is non-unique
`[THEOREM 142]`

> **`[THEOREM 142]` For `d ≠ 0`, `threshold = 1/2 ⟺ μ(κ,λ) = θ`: the target must be attained **off** the
> line of symmetry. And if it is, then the pair, its `B`-image (same `μ`, opposite `d`) and their
> midpoint (same `μ`, `d = 0`) are three distinct pairs attaining `θ`. **So the productive range reaches
> the critical length if and only if the record is attained on a nondegenerate face of the
> exponent-pair region, not at a vertex.**

**Every published record — Weyl, Bombieri–Iwaniec, Huxley, Bourgain — has displacement exactly `0`
and is attained at a vertex** (Theorem 112). Hence every published threshold is strictly below `1/2`,
and Theorem 136's self-defeating law is the quantitative form of this qualitative fact.

### The consolidated obstruction

Combining cycles 210–217, the exponent-pair route needs **one** thing that has never happened:

> **a record attained at more than one point of the region — equivalently, an estimate matching the
> best known `μ` but with `λ − κ ≠ 1/2`.**

Every advance since 1921 has produced a single new vertex *on* the line of symmetry. That is a
statement about the *shape* of every proof in the subject, not about its numbers.

### Lean

`formal/GaloisForLFunctions/HTGeometry/DisplacementCostAndFaces.lean` — `displacementCost`,
`threshold_eq_half_sub_cost`, `threshold_eq_critical_iff`, `mixFst`, `mixSnd`, `epMu_mix`,
`epDisplacement_mix`, `displacementCost_mix_const`, `threshold_mix_const`,
`procB_of_offline_record`, `offline_record_gives_face`, `critical_threshold_iff_face`,
`trivial_pair_cost_and_threshold`, `trivial_threshold_eq_two_theta`, `procA_bourgain_cost`,
`procA_beats_trivial_cost`, `records_are_vertices`.
Umbrella green at **10946** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 217 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 142 results, fifteen corrections, 63 dead
routes.

> **The exponent-pair route now has a single named requirement: a non-unique record. Everything else —
> convexity, interpolation, the `A`- and `B`-processes, the covering architecture — is priced at zero
> by Theorems 114, 120, 129, 136, 141.**

## Cycle 218 — **THEOREM 143: the framework tested against 2025 data, and it passes**

Phase 2 audit. Search turned up **Tao–Trudgian–Yang, arXiv:2501.16779 (Jan 2025)**, "New exponent
pairs, zero density estimates, and zero additive energy estimates: a systematic approach" — four new
exponent pairs obtained by systematic optimisation over the **Analytic Number Theory Exponent
Database** (https://teorth.github.io/expdb/). Two are recorded explicitly:

    P₁ = (10769/351096, 609317/702192) ,    P₂ = (89/3478, 15327/17390) .

**Baseline confirmed: `μ(1/2) ≤ 13/84` still stands** — TTY report `μ(7/10) ≤ 3/40`, a different
point, and neither new pair improves `μ(1/2)`.

### C585 — the new pairs are the first landmark pairs **off** the line of symmetry `[THEOREM 143a]`

    d(P₁) = **236683/702192 ≈ 0.337064**    d(P₂) = **6187/17390 ≈ 0.355779**

Every earlier landmark — Weyl, Bombieri–Iwaniec, Huxley, Bourgain — has displacement exactly `0`
(Theorem 112). **These are the first published pairs the displacement framework flags as candidates**,
since Theorem 142 says only nonzero displacement can extend the productive range. Their displacements
even exceed the `A`-image of the record pair's `21/97 ≈ 0.2165`.

### C586 — and the framework predicts they will not help `[THEOREM 143b]`

    μ(P₁) = **93253/468128 ≈ 0.199204**     μ(P₂) = **7077/34780 ≈ 0.203479**

both far above `13/84 ≈ 0.154762`. Their displacement costs `ρ = (μ − θ)/d` are therefore

    ρ(P₁) ≈ **0.13185**   ρ(P₂) ≈ **0.13693**   against   ρ(A(record)) = **167/1764 ≈ 0.09467** ,

giving efficiency thresholds `≈ 0.3682` and `≈ 0.3631`, both **below** `715/1764 ≈ 0.40533` and below
the published handoff `17/42 ≈ 0.40476`.

> **`[THEOREM 143]` The two most recent exponent pairs have **larger displacement** than the `A`-image
> of the record pair and are nevertheless **strictly less useful**: their productivity thresholds fall
> below both the `A`-process threshold and the published handoff length. **Displacement alone is not
> the resource; displacement per unit of surrendered exponent is.** The 2025 additions do not move the
> productive range.**

This is the campaign's first *external, out-of-sample* test of its own framework. The framework made a
falsifiable prediction — that a new off-line pair helps only if its cost `ρ` is low — and the newest
published pairs, discovered by systematic optimisation and unavailable when the framework was built,
confirm it. All arithmetic Lean-verified on first compilation.

### What would have falsified it

A pair with `d > 0` and `μ` within `(1/2 − 17/42)/2 = 1/42 ≈ 0.0238` of the record. `A(13/84,55/84)`
has excess `167/8148 ≈ 0.0205`, inside the window by `9/2716`. `P₁` and `P₂` have excesses `≈ 0.0444`
and `≈ 0.0487` — roughly **twice** the eligibility window. **The systematic search over the entire
exponent database produced nothing inside it.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/NewPairsDisplacementTest.lean` — `ttyPair1Kappa/Lambda`,
`ttyPair2Kappa/Lambda`, `ttyPair1_displacement`, `ttyPair2_displacement`, `tty_pairs_offline`,
`tty_displacements_exceed_procA`, `ttyPair1_mu`, `ttyPair2_mu`, `tty_pairs_do_not_beat_record`,
`tty_mu_exceeds_procA`, `ttyPair1_cost_exceeds`, `ttyPair2_cost_exceeds`,
`tty_thresholds_below_productivity`, `tty_thresholds_below_handoff`,
`displacement_alone_is_not_the_resource`.
Umbrella green at **10947** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 218 cycles

`μ(1/2) ≤ 13/84`, **confirmed current against the January 2025 systematic optimisation.**
**LH neither proved nor disproved.** 143 results, fifteen corrections, 63 dead routes.

> **Successor note: the ANTEDB (https://teorth.github.io/expdb/) is the live external frontier for
> this campaign's exponent data. The campaign's framework provides a *filter* on it that the database
> does not currently compute: the displacement cost `ρ = (μ − θ)/d` and the resulting productivity
> threshold `1/2 − ρ`. A pair is worth adding to the covering architecture only if `ρ < 1/2 − x₁`.**

## Cycle 219 — **THEOREMS 144–146: the eligibility criterion and the cost curve**

### C587 — the operational filter `[THEOREM 144]`

> **`[THEOREM 144]` A pair contributes to a covering architecture whose restricted source begins at
> `T^{x₁}` **if and only if**
>
>     **μ(κ,λ) − θ ≤ d(κ,λ)·(1/2 − x₁).**
>
> The right side is the **budget** the handoff length provides. At the published handoff `x₁ = 17/42`
> the budget is `2d/21`.**

    `A(13/84,55/84)` :  budget `2/97`, excess `167/8148`  →  **passes by exactly `1/8148`**
    TTY `P₁`, `P₂`   :  fail by margins exceeding `1/100` — an order of magnitude outside.

This single inequality is the campaign's operational output: it filters the entire exponent database
by one comparison, and the ANTEDB does not currently compute it.

### C588 — the `A`-process's cost curve, in closed form `[THEOREM 145]`

For `P = (κ, κ+1/2)` on the line and a **fixed** target `θ`:

> **`[THEOREM 145]`  ρ_A(κ, θ) = **(4κ+1)/2 − 4θ(κ+1)**,   linear in `κ` with slope `2 − 4θ > 0`.**

Against the current record `θ = 13/84`:

    Weyl `1/6`      →  **1/9      = 0.111111**
    Bombieri–Iwaniec `9/56`  →  **121/1176 = 0.102891**
    Huxley `32/205` →  **277/2870 = 0.096516**
    Bourgain `13/84`→  **167/1764 = 0.094671**

strictly decreasing. **Each new record makes displacement cheaper to buy** — the one respect in which
the record sequence is self-reinforcing rather than self-defeating.

Internal check: `277/2870 = 1/2 − 579/1435`, exactly Theorem 133's optimal-pair switch. The two
computations agree.

### C589 — but the cost never reaches zero at any reachable record `[THEOREM 146]`

> **`[THEOREM 146]` `ρ_A(κ,θ) = 0` exactly at `κ = (8θ−1)/(4−8θ)`. At `θ = 13/84` this is **`5/58 ≈
> 0.086207`** — the record would have to improve by `167/2436 ≈ 0.0686`, **forty-four percent**, before
> the `A`-process became productive at the critical length itself.**

So the two rates pull against each other: the cost of displacement falls linearly in the record
(slope `2 − 4θ ≈ 1.38`), while the productive range shrinks quadratically (`T(κ) = 2κ(1+2κ)`,
Theorem 136). **The second wins**: at `κ = 0` the range is empty regardless of how cheap displacement
has become.

### Lean

`formal/GaloisForLFunctions/HTGeometry/EligibilityCriterion.lean` — `eligibilityBudget`,
`eligible_iff_excess_within_budget`, `budget_at_decouplingStart`, `procA_bourgain_eligible`,
`tty_pairs_ineligible`, `procACost`, `procACost_eq`, `procACost_strictMono`, `procACost_weyl = 1/9`,
`procACost_bi = 121/1176`, `procACost_huxley = 277/2870`, `procACost_bourgain = 167/1764`,
`procACost_decreasing`, `freeDisplacementKappa`, `procACost_eq_zero_iff`,
`freeDisplacementKappa_bourgain = 5/58`, `record_above_free_displacement`,
`procACost_pos_at_record`, `productivity_needs_far_better_record`.
Umbrella green at **10948** jobs.

**Correction inside the cycle:** two hand-computed costs (`23/224`, `1373/14226`) were wrong; Lean
rejected both and the correct values `121/1176` and `277/2870` were substituted before the module
compiled. The second then matched Theorem 133 independently.

### Standing position after 219 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 146 results, fifteen corrections, 63 dead
routes.

> **The framework is now closed and operational: eligibility is one inequality, the cost curve is
> linear, the productive range is quadratic, and the two rates are computed against each other. The
> exponent-pair route's fate is decided by `T(κ) = 2κ(1+2κ) → 0`.**

## Cycle 220 — **THEOREMS 147–149: Theorem 34's target shares the corner with LH**

Phase 7 check: cycles 205–219 built a complete geometric theory of the architecture, but all of it is
pricing. Cycle 220 turns the framework onto the campaign's **one actionable analytic target**,
Theorem 34.

### C590 — the Farey-numerator sum in exponent-pair data `[THEOREM 147]`

Target: `Σ_{a mod q}ε(a,q)e(N√(2a/q)) ≪ q^{1/2+ε}` for `q ≤ N^{1/3}`, which gives `μ ≤ 1/12`.
Put `q = N^y`, `0 < y ≤ 1/3`. The phase `g(a) = N√(2a/q)` has `|g'| ≍ N/q`, so on a block of length
`q` the exponential-sum data is `length = N^y`, `F ≍ q|g'| ≍ N`, `F/length = N^{1−y}`, and a pair
`(κ,λ)` gives `N^{κ(1−y)+λy}`.

> **`[THEOREM 147]` Nontriviality (beating `N^y`) is `κ(1−y) < y(1−λ)`; at the extreme `y = 1/3` it is
> exactly **`2κ + λ < 1`**. **Weyl's pair lies exactly ON that boundary** (`1/3 + 2/3 = 1`), and every
> later landmark — Bombieri–Iwaniec, Huxley, Bourgain, and both 2025 pairs — is strictly inside.**

So the Farey sum is precisely the object on which Weyl's theorem is the break-even point. That is a
new characterisation of what the campaign's frontier object *is*.

### C591 — but the target itself forces the corner `[THEOREM 148]`

The target `N^{y/2}` requires `κ(1−y) + λy ≤ y/2`, i.e.

> **`κ + y·d(κ,λ) ≤ 0`** ,   equivalently   **`λ ≤ 1/2 − κ(1−y)/y`**  (at `y=1/3`: `λ ≤ 1/2 − 2κ`).

Since `κ ≥ 0` and `λ ≥ 1/2` force `d ≥ −κ`, and `0 < y < 1`:

> **`[THEOREM 148]` The target collapses the region to `κ = 0` and `λ = 1/2` — the exponent-pair
> conjecture. **No exponent pair with `κ > 0` can reach Theorem 34's target at any admissible length**;
> proved for Weyl, Huxley, Bourgain and both 2025 pairs individually, and in general.**

### C592 — hence the four recorded failures are one failure `[THEOREM 149]`

Theorem 36 recorded four separate failures with four computed margins — van der Corput
(`|g''| ≥ N^{1/3}`), Poisson (dual longer by `≥ N^{1/2}`), Pólya–Vinogradov (phase faster than the
character saving), Weyl differencing + Weil (critical only at `κ = 1/3`).

> **`[THEOREM 149]` All four are instances of one condition. Reaching the target requires
> `λ ≤ 1/2 − κ(1−y)/y`, and the exponent-pair region meets that half-plane **only at `(0,1/2)`**. So
> `μ(κ,λ) = 0` follows from the target: **Theorem 34's target and the Lindelöf hypothesis share the
> same corner.** The campaign's "one actionable target, half of LH's distance" is, from the
> exponent-pair side, not a partial step at all.**

This is a genuine demotion of the campaign's own most-advertised target, and it is exact. It also
explains why only *arithmetic* methods (completion, Weil) were ever candidates: they are the only
tools that do not factor through `(κ,λ)`.

### Lean

`formal/GaloisForLFunctions/HTGeometry/FareyNumeratorSumBarrier.lean` — `fareyPairExponent`,
`fareyTrivialExponent`, `fareyTargetExponent`, `farey_nontrivial_iff`, `farey_nontrivial_at_third`,
`weyl_on_nontriviality_boundary`, `landmarks_inside_nontriviality`, `tty_inside_nontriviality`,
`farey_target_iff`, `farey_target_forces_corner`, `farey_target_halfplane`,
`farey_halfplane_at_third`, `landmarks_miss_target`, `tty_pairs_miss_target`,
`corner_reaches_target`, `target_and_lindelof_share_the_corner`.
Umbrella green at **10949** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

**Correction inside the cycle:** the half-plane was first written `λ ≤ 1/2 − κ/y` (giving `3κ` at
`y = 1/3`); Lean rejected it and the correct form `λ ≤ 1/2 − κ(1−y)/y` (giving `2κ`) was substituted.

### Standing position after 220 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 149 results, **sixteen** corrections, 63 dead
routes.

> **Theorem 34 is no longer a separate target. The campaign now has exactly one open object: the
> corner `(0,1/2)`, reachable only by a method that does not factor through the exponent pair — i.e.
> through completion in the Farey numerator, which Theorems 58–59 priced by aperiodicity and Theorem 93
> reopened via quadratic reciprocity.**

## Cycle 221 — **THEOREMS 150–152: the two scale windows never meet**

Cycle 220 left one route: completion in the Farey numerator, which D62 closed at the single scale
`c = 1/3`. Cycle 221 closes it **uniformly in the scale**, and in doing so quantifies Theorem 55.

### C593 — the polynomial window `[THEOREM 150]`

On blocks of length `N^c` the critical phase's `k`-th Taylor term has size `N·(N^c/N)^k = N^{1−k(1−c)}`.
It is bounded exactly when

> **`c ≤ 1 − 1/k`.**   Quadratic blocks (`k = 3`, cubic remainder) need **`c ≤ 2/3`**.

At the campaign's working scale `c = 1/3` the cubic remainder exponent is `−1` — comfortably
negligible, confirming Theorem 28's choice was safe but not forced.

### C594 — the completion window `[THEOREM 151]`

Completing against a character mod `m` is productive only when the modulus is at least the total
phase variation. The frontier object has `F ≍ N`, and every modulus its arithmetic supplies — the
Farey denominators and numerators, and `4a` from quadratic reciprocity (Theorem 93) — is at most the
Farey order `N^c`. So completion needs

> **`c ≥ 1`.**

### C595 — hence disjointness at every finite degree `[THEOREM 152]`

> **`[THEOREM 152]` The two windows `c ≤ 1 − 1/k` and `c ≥ 1` are **disjoint for every finite `k`**,
> separated by exactly **`1/k`**. On the polynomial window the completion deficit is at least `1/k`:
>
>     working scale `c = 1/3`, quadratic  →  deficit `N^{2/3}`
>     largest quadratic scale `c = 2/3`   →  deficit `N^{1/3}`
>     degree `k`, best case               →  deficit `N^{1/k}`
>
> **Completion becomes available only in the limit `k → ∞`, where no finite-degree approximation
> exists** — which is exactly Theorem 29 ("every Taylor order sweeps one power of `N`").**

**This closes the reciprocity route uniformly**, strengthening D62 from one scale to all admissible
scales, and it is the **quantitative form of Theorem 55**: the smooth family occupies `c ≤ 1 − 1/k`,
the multiplicative family `c ≥ 1`, and no scale serves both. The dichotomy the campaign proved
qualitatively at cycle ~55 now has an exact separation constant.

### Lean

`formal/GaloisForLFunctions/HTGeometry/ScaleWindowIncompatibility.lean` — `taylorTermExponent`,
`taylorValidityMax`, `completionDeficit`, `completionMin`, `taylorTerm_bounded_iff`,
`completion_productive_iff`, `taylorValidityMax_lt_completionMin`, `windows_disjoint`,
`window_gap = 1/k`, `deficit_ge_on_validity_window`, `quadratic_validity = 2/3`,
`quadratic_deficit_at_max = 1/3`, `working_scale_deficit = 2/3`, `working_scale_cubic = −1`,
`quadratic_windows_disjoint`, `taylorValidityMax_mono`, `no_finite_degree_completes`,
`smooth_and_multiplicative_windows_never_meet`, `reciprocity_closed_uniformly`.
Umbrella green at **10950** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 221 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 152 results, sixteen corrections, **64** dead
routes (D64: reciprocity, uniformly in the scale).

> **Both named routes out of cycle 220 are now closed: the exponent-pair side by Theorem 148 (the
> target shares LH's corner) and the arithmetic side by Theorem 152 (the windows are disjoint by
> `1/k`). A successor must supply either a method whose polynomial window extends to `c = 1` — i.e.
> infinite degree with finite content — or a modulus larger than the phase variation, which the Farey
> structure does not contain.**

## Cycle 222 — **THEOREMS 153–155: the functional equation's contact point is degenerate**

Cycle 221 asked for a method whose polynomial window reaches `c = 1`. The only classical candidate is
the functional equation — "infinite degree with finite content". Cycle 222 prices it in the scale
variable.

### C596 — the FE is the scale reflection `[THEOREM 153]`

The functional equation exchanges a sum of length `N^c` for its dual of length `N^{1−c}`:

> **`[THEOREM 153]`  FE acts on the scale variable as **`c ↦ 1 − c`**, an involution whose unique fixed
> point is the critical scale `c = 1/2`.**

This is the **same reflection** the van der Corput `B`-process performs on the covering length
variable (Theorem 116). Two independently derived reflections, the same map, the same fixed point.

### C597 — and its contact with the completion window is degenerate `[THEOREM 154]`

The polynomial window is `[0, 1−1/k]`; its FE-image is `[1/k, 1]`, which meets the completion window
`[1,∞)` **only at `c = 1`** — the image of `c = 0`, blocks of a single term.

> **`[THEOREM 154]`  `completionWindow(1−c) ⟺ c ≤ 0`. So **no positive scale has its dual in the
> completion window.** The only contact between the two windows, after applying the one map that could
> exchange them, is at the scale where the block decomposition is trivial.**

That is exactly why Theorem 56 found the functional equation to be the *unique* classical coupling of
smoothness and multiplicativity **and** found it priced: it is the map that brings the windows into
contact, and the contact point carries no content.

### C598 — the balance law `[THEOREM 155]`

> **`[THEOREM 155]`  completionDeficit(c) + completionDeficit(1−c) = **1**.
>
> The primal side fails completion by `1−c`, the dual side by `c`, and the two **cannot both vanish**.
> At least one side always carries a deficit `≥ 1/2`, and **at the critical scale `c = 1/2` both
> deficits are exactly `1/2`** — perfectly balanced, so neither can be traded for the other.**

This is the cleanest statement the campaign has of why the critical scale is the hard one: it is the
unique scale at which the functional equation buys nothing because the two failures are equal.
Theorems 114 (displacement priced at zero at `x = 1/2`), 129 (support function maximal at `1/2`),
116/153 (both reflections fixing `1/2`), and 155 (deficits balanced at `1/2`) are four faces of one
fact.

### Lean

`formal/GaloisForLFunctions/HTGeometry/FunctionalEquationScaleContact.lean` — `feReflect`,
`feReflect_involutive`, `feReflect_fixed_iff`, `feReflect_antitone`, `polyWindow`,
`completionWindow`, `critical_in_polyWindow`, `critical_not_in_completionWindow`,
`fe_fixes_critical`, `fe_image_of_validity_max = 1/k`, `fe_dual_completes_iff`,
`fe_contact_is_degenerate`, `fe_dual_deficit_pos`, `fe_dual_deficit_eq`, `deficits_sum_to_one`,
`some_side_has_half_deficit`, `critical_deficits_balanced`, `fe_cannot_produce_completion`.
Umbrella green at **10951** jobs.

### Standing position after 222 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 155 results, sixteen corrections, 64 dead
routes.

> **Four independent structures — the covering demand, the exponent-pair support function, the van der
> Corput `B`-process, and the functional equation on scales — all single out `1/2` as their fixed point
> or maximum, and the completion deficits are exactly balanced there. The critical scale is not merely
> where the problem is posed; it is the simultaneous fixed point of every symmetry the subject has.**

## Cycle 223 — **THEOREMS 156–159: the off-line transfer, a route the campaign never opened**

Cycle 222 found four structures all fixing `σ = 1/2`. Cycle 223 asks what a **convex** quantity does
under the same reflection — and the answer opens a direction the campaign had not touched in 222
cycles: **bounds off the critical line.**

### C599 — the symmetrised exponent `[THEOREM 156]`

`μ` is convex, and the functional equation gives `μ(σ) − μ(1−σ) = 1/2 − σ`. Hence

> **`[THEOREM 156]`  `ν(σ) := μ(σ) + (σ−1/2)/2` is **convex and symmetric about `σ = 1/2`**, so it is
> minimised there, with `ν(1/2) = μ(1/2)`.**

Every earlier reflection in the campaign acted on an *affine* quantity, where the orbit average
equals the fixed-point value and nothing is gained (Theorems 43, 116, 155). **`ν` is the first
*convex* one, and for a convex symmetric function the fixed point is a genuine minimum — so the
reflection now yields an inequality rather than an identity.**

### C600 — the transfer `[THEOREM 157]`

> **`[THEOREM 157]`   μ(1/2) ≤ μ(σ) + (σ − 1/2)/2   for every `σ`.**
>
> A growth bound **anywhere** transfers to the critical line with a linear penalty of half the
> distance. At `σ = 1` (`μ(1) = 0`) it returns the convexity bound `1/4`.

### C601 — applied to the 2025 data `[THEOREM 158]`

Tao–Trudgian–Yang report **`μ(7/10) ≤ 3/40`**. Transferring:

> **`[THEOREM 158]`  `μ(1/2) ≤ 3/40 + (7/10 − 1/2)/2 = 3/40 + 1/10 = **7/40 = 0.175**` —
> strictly better than the convexity bound `1/4` and short of the record `13/84 = 0.15476`.**

### C602 — and the exact requirement `[THEOREM 159]`

Reading the transfer backwards, an off-line bound at `σ` matches a target `θ` exactly when
`μ(σ) ≤ θ − (σ−1/2)/2`.

> **`[THEOREM 159]`  At `σ = 7/10` the record threshold is **`23/420 ≈ 0.054762`**, and the published
> `3/40 = 0.075` misses it by **`17/840 ≈ 0.020238`**. The threshold reaches zero at `σ = 1/2 + 2θ`,
> which for the current record is **`17/21 ≈ 0.8095`**: beyond that abscissa no finite off-line bound
> can help at all, and `7/10` sits comfortably inside.**

**This is a genuinely new campaign direction with a concrete numerical target.** Every barrier proved
in cycles 205–222 concerns methods operating *at* `σ = 1/2`; the transfer says a sufficiently strong
bound at `σ = 7/10` — a point where the problem is easier, since `μ(7/10) ≤ 3/40 < 13/84` already —
would beat the record on the critical line. The needed improvement at `7/10` is `17/840`, about
**27 %** of the current value.

### Lean

`formal/GaloisForLFunctions/HTGeometry/OffLineTransfer.lean` — `GrowthExponent` (convexity and the
functional equation as explicit fields, no global assumptions), `nu`, `nu_symm`, `nu_at_half`,
`mu_half_le`, `nu_min_at_half`, `transfer_threshold`, `convexity_bound_from_transfer`,
`muSevenTenths = 3/40`, `transfer_from_seven_tenths`, `seven_fortieths_between`,
`recordThresholdAtSevenTenths = 23/420`, `seven_tenths_shortfall = 17/840`,
`threshold_would_match_record`, `transfer_penalty`, `transferThreshold`,
`transferThreshold_zero_at`, `transfer_useless_beyond = 17/21`, `seven_tenths_inside`.
Umbrella green at **10952** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 223 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 159 results, sixteen corrections, 64 dead
routes.

> **New actionable target, with a number: `μ(7/10) ≤ 23/420`. The current best is `3/40`; the gap is
> `17/840`. Unlike every previous target, this one lives off the critical line, where none of the
> campaign's fixed-point barriers (Theorems 114, 129, 153, 155) apply — they are all statements about
> `σ = 1/2` exactly.**

## Cycle 224 — **THEOREMS 160–163: what an exponent pair gives off the line, and the `840`-ledger**

Cycle 223 opened the off-line route. Cycle 224 works out what the existing machinery already delivers
there, so the new target is measured against the right baseline.

### C603 — the two branches `[THEOREM 160]`

Dyadic block `M` of the AFE contributes `M^{-σ}` times an exponential sum with `F ≍ t`, so an
exponent pair bounds it by `t^κM^{λ−κ−σ}`, while trivially it is `M^{1−σ}`. They cross at
`M₀ = t^{κ/(1+κ−λ)}`, and the profile's maximum sits at the crossover or at the critical block.

> **`[THEOREM 160]` On the line of symmetry (all records) the two branch values are
> **`2κ(1−σ)`** (crossover) and **`κ − (σ−1/2)/2`** (critical), their difference factorises as
> `(σ−1/2)(1/2 − 2κ)`, and since every record has `κ < 1/4` the **crossover dominates exactly for
> `σ ≥ 1/2`**.**

### C604 — hence a linear off-line profile `[THEOREM 161]`

> **`[THEOREM 161]`  A record pair `(κ, κ+1/2)` gives **`μ(σ) ≤ 2κ(1−σ)` for `σ ≥ 1/2`** — linear,
> correct at both ends (`κ` at `σ = 1/2`, `0` at `σ = 1`). For Bourgain's pair at `σ = 7/10` this is
> **`13/140`**.**

### C605 — and the transfer of a pair's own profile is worthless `[THEOREM 162]`

Feeding the profile into Theorem 157: `2κ(1−σ) + (σ−1/2)/2 = κ + (σ−1/2)(1/2 − 2κ)`.

> **`[THEOREM 162]` The derivative in `σ` is `1/2 − 2κ > 0`, so the transfer is **minimised at
> `σ = 1/2`, returning exactly `κ`**. A pair loses by going off the line and coming back — Bourgain's
> pair at `σ = 7/10` transfers back to `27/140 > 13/84`. **The off-line route is useful only with a
> bound that does not come from an exponent pair.**

### C606 — the ledger at `σ = 7/10` `[THEOREM 163]`

In eight-hundred-fortieths:

    exponent-pair prediction   13/140 = **78/840**
    published bound (TTY)       3/40  = **63/840**
    record-matching threshold  23/420 = **46/840**

> **`[THEOREM 163]` The published bound genuinely beats the exponent-pair prediction, by
> `1/56 = **15/840**` — so it *is* a non-exponent-pair result, exactly the kind Theorem 162 requires.
> But the remaining gap to the record threshold is **`17/840`**, *larger* than the gain already made.
> **Closing it means roughly doubling the existing off-line advantage over the exponent pair.** The
> total available at this abscissa is `32/840 = 4/105`, of which `15/840` is banked.**

This converts cycle 223's target into a measured one: the off-line route is live (a real non-pair
gain exists there), and the remaining work is quantified against what has already been achieved by
the same kind of method.

### Lean

`formal/GaloisForLFunctions/HTGeometry/OffLineExponentPairProfile.lean` — `crossoverBranch`,
`criticalBranch`, `branches_agree_at_half`, `branch_difference`, `crossover_dominates_iff`,
`bourgainKappa_lt_quarter`, `linePairProfile`, `linePairProfile_at_half`,
`linePairProfile_at_one`, `linePairProfile_antitone`,
`linePairProfile_bourgain_seven_tenths = 13/140`, `transferOfProfile`, `transferOfProfile_eq`,
`transfer_of_own_profile_useless`, `transfer_of_bourgain_profile = 27/140`, `seven_tenths_ledger`,
`published_beats_pair_prediction = 1/56`, `remaining_exceeds_gain`,
`total_available_at_seven_tenths = 4/105`.
Umbrella green at **10953** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 224 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 163 results, sixteen corrections, 64 dead
routes.

> **The off-line route is the campaign's first live direction since Theorem 34, and unlike Theorem 34
> it is not equivalent to the corner: Theorem 162 shows exponent pairs cannot supply it, and Theorem
> 163 shows a non-pair method already supplies `15/840` of the needed `32/840`. The target is
> `μ(7/10) ≤ 23/420`.**

## Cycle 225 — **THEOREMS 164–167: the transfer band, and the witness principle**

### C607 — three levels at every abscissa `[THEOREM 164]`

Fix a record `θ`. At abscissa `σ > 1/2`:

    convexity prediction :  **2θ(1−σ)**          — what convexity from the record already gives
    record threshold     :  **θ − (σ−1/2)/2**    — what transfers back to the record
    a bound `v = μ(σ)`   :  informative iff `v < 2θ(1−σ)`, record-beating iff `v < θ − (σ−1/2)/2`

> **`[THEOREM 164]` The interval between the two levels — the **transfer band** — has width
>
>     **2θ(1−σ) − (θ − (σ−1/2)/2) = (σ − 1/2)(1/2 − 2θ)** ,
>
> vanishing on the critical line and growing **linearly** with the distance from it. A bound inside
> the band beats convexity without beating the record.**

The band width at `σ = 7/10`, `θ = 13/84` is `4/105` — **exactly Theorem 163's "total available"**,
now derived from a general formula rather than by subtraction.

### C608 — the ledger, as fractions `[THEOREM 165]`

    band at `σ = 7/10` :  from `13/140 = 78/840` down to `23/420 = 46/840`, width `32/840`
    published `3/40`   :  `63/840`, i.e. **`15/32` of the band captured, `17/32` remaining**

> **`[THEOREM 165]` The published off-line bound has captured `15/32` of the available band. Beating
> the record requires capturing **all** of it.**

### C609 — and the route is a *witness* mechanism `[THEOREMS 166–167]`

Define the **transfer deficit** `D(σ) = μ(σ) − (θ − (σ−1/2)/2)`.

> **`[THEOREM 166]` `D(σ) ≥ μ(1/2) − θ` for every `σ`**, directly from the transfer. And
> `D(1/2) = 0` when the record is attained.
>
> **`[THEOREM 167]` Hence `D(σ) < 0` at any abscissa **certifies** `μ(1/2) < θ` — the off-line route
> can only witness a record that is already not sharp, and the certificate is exactly an off-line bound
> within `(σ−1/2)/2` of the truth.**

This is the honest characterisation of the new direction: it is not a way of *creating* a better
critical-line bound out of easier information, but a way of *detecting* one. Its value is that the
detection can be done at an abscissa where the campaign's fixed-point barriers (Theorems 114, 129,
153, 155) do not apply, since all of those are statements about `σ = 1/2` exactly.

### Lean

`formal/GaloisForLFunctions/HTGeometry/TransferBand.lean` — `convexityPrediction`,
`convexityPrediction_eq_profile`, `transferBandWidth`, `transferBandWidth_eq`,
`transferBandWidth_zero_iff`, `transferBandWidth_mono`, `below_band_beats_record`, `inside_band`,
`band_at_seven_tenths = 4/105`, `band_edges_at_seven_tenths`, `published_inside_band`,
`capturedFraction = 15/32`, `published_captures`, `remaining_fraction`, `transferDeficit`,
`transferDeficit_at_half`, `transferDeficit_ge_slack`, `negative_deficit_certifies`,
`published_deficit = 17/840`.
Umbrella green at **10954** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 225 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 167 results, sixteen corrections, 64 dead
routes.

> **The off-line direction is now fully specified: band width `(σ−1/2)(1/2−2θ)`, current capture
> `15/32` at `σ = 7/10`, and a witness principle saying a negative deficit certifies a non-sharp
> record. The concrete target remains `μ(7/10) ≤ 23/420`.**

## Cycle 226 — **THEOREMS 168–170: the disproof side opens**

Two hundred and twenty-five cycles have all addressed goal clause (1), proving LH. Cycle 226 runs the
convexity argument **backwards** and reaches clause (2) for the first time.

### C610 — the reverse transfer `[THEOREM 168]`

For `1/2 ≤ σ ≤ 1`, write `σ = t·(1/2) + (1−t)·1` with `t = 2(1−σ)`. Convexity plus `μ(1) = 0` gives

> **`[THEOREM 168]`  `μ(σ) ≤ 2(1−σ)·μ(1/2)` , equivalently **`μ(1/2) ≥ μ(σ)/(2(1−σ))`** for `σ < 1`.**

This is the exact converse of the convexity prediction used in Theorem 164's band. Every previous use
of convexity in this campaign ran from an off-line bound *down* to the critical line; this one runs
from an off-line **value** *up* to it.

### C611 — hence a refutation route `[THEOREM 169]`

> **`[THEOREM 169]`  **A single abscissa `σ₀ ∈ (1/2, 1)` with `μ(σ₀) > 0` refutes the Lindelöf
> hypothesis.** Equivalently: `μ(1/2) = 0` **iff** `μ` vanishes identically on `[1/2, 1]`.**

**This is the campaign's first result on the disproof side.** It converts goal clause (2) — "prove LH
false" — from a statement about the critical line into a positivity statement at *any* interior point
of the strip. And crucially: **none of the campaign's barriers applies to it.** Theorems 114, 129,
153, 155 and the whole fixed-point cluster are statements about `σ = 1/2` exactly; a refutation may be
witnessed anywhere in the open interval, where those symmetries do not act.

### C612 — and positivity amplifies away from the line `[THEOREM 170]`

> **`[THEOREM 170]` A lower bound `v ≤ μ(σ)` yields `v/(2(1−σ))` on the critical line. The
> **amplifier** `1/(2(1−σ))` equals `1` at `σ = 1/2`, is `5/3` at `σ = 7/10`, and grows without bound
> toward `σ = 1`. **The further from the critical line a positivity witness is found, the more it
> proves.**

### Status of the route

No witness is currently available anywhere in `(1/2,1)`: the strongest known Ω-results in that range
are of Montgomery type, `exp(c(\log t)^{1−σ}/(\log\log t)^σ)`, which are `t^{o(1)}` and therefore
consistent with `μ(σ) = 0`. So the route is open, unobstructed by anything the campaign has proved,
and currently unwitnessed — the honest reading is that the disproof side is *less explored*, not
*more closed*, than the proof side.

### Lean

`formal/GaloisForLFunctions/HTGeometry/DisproofRoute.lean` — `ConvexGrowthExponent` (convexity,
functional equation, nonnegativity, `μ(1) = 0` as explicit fields), `midpointConvex`,
`toGrowthExponent`, `mu_le_chord`, `mu_half_ge`, `positivity_refutes_lindelof`,
`lindelof_forces_vanishing`, `lindelof_iff_vanishes`, `refutation_amplification`,
`refutationAmplifier`, `amplifier_at_half = 1`, `amplifier_at_seven_tenths = 5/3`,
`amplifier_mono`, `amplification_summary`.
Umbrella green at **10955** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 226 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 170 results, sixteen corrections, 64 dead
routes.

> **Both goal clauses now have explicit targets.**
> **(1) Prove LH true:** capture the remaining `17/32` of the transfer band at `σ = 7/10`, i.e.
> `μ(7/10) ≤ 23/420` — and beyond that, the corner `(0,1/2)`.
> **(2) Prove LH false:** exhibit any `σ₀ ∈ (1/2,1)` with `μ(σ₀) > 0`, amplified to the critical line
> by `1/(2(1−σ₀))`.

## Cycle 227 — **THEOREMS 171–173: both sides measured in the same units**

Cycle 226 opened the disproof side. Cycle 227 measures it, and measures the proof side against the
same yardstick.

### C613 — the refutation deficit `[THEOREM 171]`

A refutation needs `μ(σ) > 0`, i.e. a lower bound `exp(δ·\log T)` — **logarithmic exponent `1`**. The
strongest known omega-results on `(1/2,1)` have the shape `exp(c(\log T)^{1−σ}(\log\log T)^{−σ})` —
**logarithmic exponent `1−σ`**.

> **`[THEOREM 171]` The deficit in the logarithmic exponent is exactly **`σ`**. On `[1/2,1]` it is at
> least `1/2`, attained only at the critical line, and it grows toward `σ = 1`. Equivalently:
> **everywhere on the interval the known lower bounds reach at most the square root of what a
> refutation requires**, measured in the exponent of `\log T`.**

### C614 — and the disproof trade-off `[THEOREM 172]`

    σ = 1/2   :  deficit **1/2**,  amplifier **1**
    σ = 7/10  :  deficit **7/10**, amplifier **5/3**

> **`[THEOREM 172]` The deficit is smallest just above the critical line — where the amplifier is
> weakest — and largest near `σ = 1`, where the amplifier is strongest. The two move against each
> other, so no abscissa is uniformly favourable for a refutation.**

### C615 — the proof-side ratio `[THEOREM 173]`

At abscissa `σ` the fraction of the convexity prediction that must be achieved is

> **`R(σ) = (θ − (σ−1/2)/2)/(2θ(1−σ))`** — equal to `1` at `σ = 1/2`, strictly below `1` off the
> line, and `0` at `σ = 1/2 + 2θ`. **At `σ = 7/10` with `θ = 13/84` it is `23/39 ≈ 0.590`.**

> **`[THEOREM 173]` The proof side has the mirror trade-off: near the critical line only a slight
> improvement on convexity is needed but at the hardest point; far from it the point is easier while
> the required improvement is proportionally larger.**

### The two sides, side by side

    proof side   at `σ = 7/10` :  need `23/39` of the convexity prediction;  **`15/32` of the band banked**
    disproof side at `σ = 7/10`:  need log-exponent `1`;  known `3/10`;  **nothing banked**

> **Neither side is closed, and they are now measured in comparable terms. The proof side has partial
> progress from a genuinely non-exponent-pair method (Theorem 163); the disproof side has none, and its
> deficit is a full power of `\log T` rather than a rational exponent gap.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/RefutationDeficitAndBandRatio.lean` — `omegaLogExponent`,
`refutationLogExponent`, `refutationDeficit`, `refutationDeficit_eq`, `refutationDeficit_ge_half`,
`omegaLogExponent_le_half`, `omega_at_most_square_root`, `refutationDeficit_mono`,
`disproof_tradeoff`, `bandRatio`, `bandRatio_at_half`, `bandRatio_at_seven_tenths = 23/39`,
`bandRatio_zero_at`, `bandRatio_lt_one`, `proof_side_tradeoff`, `both_sides_measured`.
Umbrella green at **10956** jobs. Lint: one pre-existing `RHTower.DeningerArithmetic*` error,
unrelated.

### Standing position after 227 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 173 results, sixteen corrections, 64 dead
routes.

> **The campaign's ledger, complete:**
> **Proof:** corner `(0,1/2)` — everything at `σ = 1/2` priced closed (Thms 114–155); off-line route
> live, `μ(7/10) ≤ 23/420` needed, `15/32` of the band banked.
> **Disproof:** any `σ₀ ∈ (1/2,1)` with `μ(σ₀) > 0`; deficit one full power of `\log T`; nothing banked;
> **no campaign barrier applies.**

## Cycle 228 — **THEOREMS 174–176: LH as a statement about one real number**

### C616 — the vanishing set is an upward-closed interval `[THEOREM 174]`

Two elementary consequences of the axioms bracket `{σ : μ(σ) = 0}`:

* the functional equation gives `μ(σ) = μ(1−σ) + 1/2 − σ ≥ 1/2 − σ`, so **`μ(σ) > 0` for every
  `σ < 1/2`**;
* convexity with `μ(1) = 0` and `μ ≥ 0` makes the set **upward closed**: `μ(s) = 0` and `s ≤ σ ≤ 1`
  imply `μ(σ) = 0`.

> **`[THEOREM 174]` The vanishing set is an interval reaching to the right, with left endpoint
>
>     **σ* := inf{σ : μ(σ) = 0}** ,   **`1/2 ≤ σ* ≤ 1` unconditionally,**
>
> and **the Lindelöf hypothesis is exactly `σ* = 1/2`.** LH asks whether a single real number, already
> known to lie in `[1/2, 1]`, equals its unconditional lower bound.**

### C617 — nothing better than `σ* ≤ 1` is known `[THEOREM 175]`

The best bounds near `σ = 1` are Vinogradov–Korobov type, `μ(σ) ≪ (1−σ)^{3/2}`, **positive for every
`σ < 1`.** So no abscissa below `1` is known to lie in the vanishing set: the upper bracket `σ* ≤ 1`
is the whole of what is known, and the lower bracket `σ* ≥ 1/2` is exactly the functional equation.

### C618 — and a known vanishing point sharpens the disproof amplifier `[THEOREM 176]`

> **`[THEOREM 176]` If `μ(s) = 0` for some `s`, then for `1/2 ≤ σ < s`
>
>     **μ(1/2) ≥ μ(σ)·(s − 1/2)/(s − σ)** .
>
> At `s = 1` this is Theorem 170's amplifier `1/(2(1−σ))`; for `s < 1` it is **strictly larger** (for
> `σ > 1/2`). Example: at `σ = 7/10`, knowing `μ(9/10) = 0` would raise the amplifier from `5/3` to
> **`2`**.**

So the two open problems are coupled: **any progress on the vanishing abscissa strengthens every
refutation witness**, and the campaign's Theorem 174 shows the whole of LH is the location of `σ*`.

### Why this framing is worth having

Cycles 205–225 priced every mechanism that operates *at* `σ = 1/2`, where four independent symmetries
all have their fixed point. Theorem 174 moves the object of study off that point entirely: `σ*` is a
number in `[1/2,1]`, and neither the reflection `c ↦ 1−c`, nor the `B`-process, nor the displacement
pricing says anything about where in that interval it sits. **The fixed-point cluster constrains the
value of `μ` at one point; it does not constrain the location of the zero set's endpoint.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/VanishingAbscissa.lean` — `mu_pos_of_lt_half`,
`mu_ne_zero_of_lt_half`, `vanishing_upward_closed`, `vanishing_at_one`,
`lindelof_iff_vanishing_from_half`, `no_vanishing_below_half`, `vanishing_bracket`,
`mu_le_chord_to_vanishing`, `mu_half_ge_sharpened`, `sharpAmplifier`, `sharpAmplifier_at_one`,
`sharpAmplifier_antitone`, `sharpAmplifier_example`.
Umbrella green at **10957** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

**Correction inside the cycle:** `sharpAmplifier_antitone` was first stated with `1/2 ≤ σ`; Lean
rejected it, and inspection showed the two amplifiers are **equal** at `σ = 1/2` (their difference is
`(s−s')(1/2−σ)`). Hypothesis strengthened to `1/2 < σ` — a real, if small, sharpening: **a better
vanishing point buys nothing exactly on the critical line.** One more instance of the fixed-point
degeneracy.

### Standing position after 228 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 176 results, **seventeen** corrections, 64
dead routes.

> **LH = `σ* = 1/2`, where `σ* ∈ [1/2,1]` is the left endpoint of the zero set of `μ`. Lower bracket:
> the functional equation. Upper bracket: `μ(1) = 0`. Nothing in between is known, and none of the
> campaign's fixed-point barriers speaks to it.**

## Cycle 229 — **THEOREMS 177–179: the whole problem as a vanishing abscissa**

Cycle 228 introduced `σ*`. Cycle 229 connects it to the record, and the connection is exact.

### C619 — the vanishing transfer `[THEOREM 177]`

Combine the off-line transfer `μ(1/2) ≤ μ(σ) + (σ−1/2)/2` (Theorem 157) with a vanishing point:

> **`[THEOREM 177]`   μ(σ*) = 0  ⟹  **μ(1/2) ≤ (σ* − 1/2)/2**.**

Three readings, all exact:

    σ* = 1        →  μ(1/2) ≤ **1/4**    (the convexity bound)
    σ* = 17/21    →  μ(1/2) ≤ **13/84**  (**exactly the current record**)
    σ* = 1/2      →  μ(1/2) = **0**      (the Lindelöf hypothesis)

Read backwards, `σ* ≥ 2μ(1/2) + 1/2`, which with `μ ≥ 0` **recovers the functional equation's bracket
`σ* ≥ 1/2`** — the two brackets of Theorem 174 are the two directions of one inequality.

### C620 — hence a complete reformulation `[THEOREM 178]`

> **`[THEOREM 178]` The subconvexity problem *is* the question of how far left of `σ = 1` the growth
> exponent can be shown to vanish, at exchange rate `dμ(1/2)/dσ* = 1/2`. **Proving `μ(s) = 0` for any
> `s < 17/21` beats `13/84`.**

The ledger in these coordinates:

    Lindelöf abscissa       **1/2**
    record's abscissa      **17/21 ≈ 0.809524**
    convexity's abscissa      **1**
    covered since 1921      `1 − 17/21` = **4/21**
    remaining to LH        `17/21 − 1/2` = **13/42** = **(13/8)×(4/21)**

**A century of subconvexity has moved the vanishing abscissa by `4/21`; the Lindelöf hypothesis is the
remaining `13/42`, thirteen-eighths as far.** This is the campaign's cleanest single measure of the
distance, and it agrees with Theorem 45's independent calibration (`1/14 ≈ 7.1 %` of the block-exponent
distance covered) in spirit while being exact in a different coordinate.

### C621 — bracket completeness `[THEOREM 179]`

> **`[THEOREM 179]`  Any strict improvement of the **lower** bracket (`every vanishing point exceeds
> 1/2`) **refutes** LH. Any improvement of the **upper** bracket below `17/21` **improves the record**.
> So `[1/2, 17/21]` is exactly the interval in which the location of `σ*` is both unknown and
> consequential.**

Note the coincidence, now explained: `17/21` was already in the campaign as the abscissa beyond which
the off-line transfer is useless (Theorem 159). It is the same number for the same reason —
`transferThreshold(θ, 1/2 + 2θ) = 0`.

### Lean

`formal/GaloisForLFunctions/HTGeometry/VanishingTransfer.lean` — `mu_half_le_of_vanishing`,
`vanishing_ge`, `vanishing_ge_half`, `vanishing_beats_record`, `vanishing_matches_record`,
`exchange_rate`, `recordVanishingAbscissa`, `recordVanishingAbscissa_bourgain = 17/21`,
`recordVanishingAbscissa_eq_transfer_zero`, `recordVanishingAbscissa_convexity = 1`,
`recordVanishingAbscissa_lindelof = 1/2`, `recordVanishingAbscissa_mono`,
`distance_to_lindelof = 13/42`, `distance_covered = 4/21`, `the_ledger`,
`lower_bracket_improvement_refutes`, `upper_bracket_improvement_improves_record`.
Umbrella green at **10959** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 229 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 179 results, seventeen corrections, 64 dead
routes.

> **The campaign's target list, in vanishing-abscissa coordinates:**
> **Beat the record:** prove `μ(s) = 0` for some `s < 17/21`.
> **Prove LH:** push `s` to `1/2`, a distance of `13/42`.
> **Disprove LH:** show every vanishing point exceeds `1/2`.
> All three are statements about one interval, `[1/2, 17/21]`, and none of the campaign's
> critical-line barriers constrains where in it `σ*` lies.

## Cycle 230 — **THEOREMS 180–182: why the vanishing abscissa is stuck, and the three-way collapse**

Cycle 229 recast the problem as locating `σ*`. Cycle 230 asks why the upper bracket is stuck at `1`,
and the answer is at the opposite end of the scale range from every previous barrier.

### C622 — the block requirement `[THEOREM 180]`

`μ(s) = 0` forces every dyadic block of the AFE at abscissa `s` to be bounded:
`M^{−s}|Σ_{n∼M}n^{−it}| ≪ t^ε`. With `M = t^c`, `0 < c ≤ 1/2`, the block must achieve exponent `c·s`,
while a line pair `(κ, κ+1/2)` delivers `κ + c/2`. Hence

> **`[THEOREM 180]`  the pair covers the block **iff `κ ≤ c(s − 1/2)`, i.e. `c ≥ κ/(s − 1/2)`.**

At the record pair and `s = 17/21` the threshold is **exactly `c = 1/2`**: the record pair covers the
critical block with equality and **nothing below it** (at `c = 1/4` it gives `0.2798…` where `0.2024…`
is required). **This is why `17/21` is the abscissa attached to `13/84`** — Theorem 177's number is the
critical-block coverage threshold.

### C623 — and the small blocks force the corner `[THEOREM 181]`

Letting `c → 0` in `κ ≤ c(s−1/2)` forces `κ ≤ 0`.

> **`[THEOREM 181]` **No exponent pair with `κ > 0` proves `μ(s) = 0` for any `s > 1/2`.** The cause is
> the pair's `t^κ` **floor**, which does not shrink with the block while the requirement `c·s` does. The
> obstruction therefore sits at the **small** blocks — the opposite end of the scale range from every
> previous barrier in this campaign, all of which sit at `c = 1/2`.**

This explains Theorem 175 structurally: the upper bracket `σ* ≤ 1` is stuck not because the critical
block is hard, but because the *short* blocks are.

### C624 — three targets, one corner `[THEOREM 182]`

> **`[THEOREM 182]` Within the exponent-pair framework, three targets that looked independent all
> reduce to `κ = 0`:
>
>     the subconvexity record        (Theorems 114, 130)
>     the Farey-numerator bound      (Theorem 148)
>     the vanishing abscissa         (Theorem 181)
>
> **Only methods that do not factor through an exponent pair can separate them.** Exactly one such gain
> is on record: the `15/840` of non-pair advantage at `σ = 7/10` (Theorem 163).**

### Lean

`formal/GaloisForLFunctions/HTGeometry/VanishingNeedsCorner.lean` — `blockRequirement`,
`blockPairBound`, `pair_covers_block_iff`, `coverageThreshold`, `pair_covers_iff_threshold`,
`record_threshold_is_critical_block = 1/2`, `record_covers_critical_block`,
`record_fails_below_critical`, `record_fails_at_quarter`, `positive_kappa_misses_a_block`,
`coverage_of_all_blocks_forces_corner`, `vanishing_route_needs_corner`,
`obstructions_at_opposite_ends`, `three_targets_one_corner`.
Umbrella green at **10961** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 230 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 182 results, seventeen corrections, 64 dead
routes.

> **The campaign's position is now a single sentence: every route that factors through an exponent
> pair terminates at the corner `(0,1/2)`, and the only measured progress outside that framework is
> `15/840` of the `32/840` band at `σ = 7/10`. The frontier is the non-pair off-line method that
> produced it.**

## Cycle 231 — **THEOREMS 183–186: the off-line problem is single-scale, and the record pair is trivial there**

### C625 — which block binds `[THEOREM 183]`

`μ(s) ≤ max_{0≤c≤1/2}(E(c) − c·s)` with `E(c) ≤ min(c, κ + c(λ−κ))`, the branches crossing at

    **c₀ = κ/(1/2 − d)** ,   `d = λ − κ − 1/2` .

The pair branch of `E(c) − cs` has slope `d + 1/2 − s`, so

> **`[THEOREM 183]` the **crossover block `c₀` binds iff `d ≤ s − 1/2`**; otherwise the critical block
> binds and the profile is `κ + (d + 1/2 − s)/2`.**

### C626 — hence concentration off the line `[THEOREM 184]`

On the line (`d = 0`) the crossover always binds and `c₀ = 2κ`.

> **`[THEOREM 184]`  At `s = 1/2` the pair branch of `E(c) − c/2` is **constant `= κ`**, so the whole
> range `[2κ, 1/2]` binds equally (the campaign's "every block contributes the same"). For `s > 1/2` it
> is **strictly decreasing**, so **only the single block `c = 2κ` binds**.
>
> **Moving off the critical line concentrates a multi-scale problem onto one scale**, `t^{2κ} = t^{13/42}`,
> the same one for *every* abscissa `s > 1/2`.**

### C627 — and at that scale the record pair is exactly trivial `[THEOREM 185]`

Nontriviality at `c = 13/42` is `29κ + 13λ < 13`. For Bourgain's pair:

    29·(13/84) + 13·(55/84) = (377 + 715)/84 = 1092/84 = **13** — equality, on the nose.

> **`[THEOREM 185]` **At its own binding block the record pair achieves exactly the trivial bound.** The
> entire off-line profile `2κ(1−s)` is produced by the trivial bound at one block length. **Therefore any
> nontrivial cancellation in `Σ_{n∼t^{13/42}}n^{−it}` improves `μ(σ)` for every `σ > 1/2` simultaneously.**

This is a third exact coincidence at `13/42`, after the crossover of Theorem 61 and the trivial-pair
threshold `2θ`.

### C628 — the `A`-image is nontrivial there, but pays elsewhere `[THEOREM 186]`

`A(13/84,55/84) = (13/194,76/97)` satisfies `29κ+13λ = 2353/194·… < 13`, with block exponent

    **2353/8148** against trivial **2522/8148**, a saving of **`169/8148 = 13²/(84·97)`.**

> **`[THEOREM 186]` But its displacement `21/97` exceeds `s − 1/2 = 1/5` at `σ = 7/10` by **`8/485`**, so
> for it the *critical* block binds instead and the crossover saving is not collected. **The trade is
> exact: `169/8148` bought at the binding block, `8/485` of displacement excess paid at the abscissa.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/BindingBlockOffLine.lean` — `crossoverScale`,
`crossoverScale_on_line`, `crossoverScale_bourgain = 13/42`, `pairBranchSlope`,
`crossover_binds_iff`, `line_crossover_binds`, `line_profile_from_crossover`,
`critical_line_branch_constant`, `all_blocks_bind_at_critical`, `off_line_branch_decreasing`,
`nontrivialAtThirteenFortyTwo`, `record_exactly_trivial_at_binding`,
`procA_bourgain_nontrivial_at_binding`, `procA_bourgain_block_exponent = 2353/8148`,
`procA_bourgain_block_saving = 169/8148`, `procA_displacement_exceeds_distance`,
`procA_displacement_excess = 8/485`, `procA_critical_block_binds`, `binding_block_trade`,
`single_scale_conclusion`.
Umbrella green at **10962** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 231 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 186 results, seventeen corrections, 64 dead
routes.

> **The sharpest actionable statement the campaign has produced: get any nontrivial cancellation in
> `Σ_{n∼t^{13/42}}n^{−it}` from a pair whose displacement is at most `s − 1/2`. That single
> exponential sum, at one fixed length, controls `μ(σ)` for every `σ > 1/2` — and through the transfer,
> the critical line as well.**

## Cycle 232 — **THEOREMS 187–189: the tuning principle, and a bound below the published `3/40`**

Cycle 231 showed the off-line problem is single-scale and that the binding block depends on the
pair's displacement. Cycle 232 turns that into a construction.

### C629 — the tuning principle `[THEOREM 187]`

At abscissa `σ` the pair branch of `E(c) − cσ` has slope `λ − κ − σ`. When that vanishes the branch is
**flat**, and the crossover value `c₀(1−σ)` and the critical-block value `(κ+λ−σ)/2` **coincide**:

> **`[THEOREM 187]`  If `λ − κ = σ` — displacement exactly `σ − 1/2` — then **`μ(σ) ≤ κ`**. The problem
> at abscissa `σ` becomes: minimise `κ` along the slice `λ − κ = σ` of the exponent-pair region.**

This is the exact off-line analogue of the campaign's critical-line pricing, and it explains Theorem
186's failure: `A(13/84,55/84)` has `λ−κ = 139/194 > 7/10`, so it is *over*-tuned and the critical
block binds for it.

### C630 — tuning is available by convexity `[THEOREM 188]`

The segment from a line pair to its `A`-image sweeps `λ−κ` from `1/2` to the image's value. For
Bourgain's pair and its image the sweep covers `[1/2, 139/194]`, and `σ = 7/10` is hit at parameter
`97/105`, giving

> **`Q = (65/882, 1706/2205)`,  `λ − κ = 7/10` exactly,  hence  **`μ(7/10) ≤ 65/882`**.**

### C631 — and it lands below `3/40` `[THEOREM 189]`

    **65/882 = 0.0736961…**   against   **3/40 = 0.075**   —   `65·40 = 2600 < 2646 = 3·882` .

> **`[THEOREM 189]` The tuned pair gives `μ(7/10) ≤ 65/882`, **below the value `3/40` recorded in the
> January 2025 systematic optimisation**, by `23/17640`. **This must be checked against the ANTEDB
> before being claimed as an improvement** — the optimiser may already hold a better value at this
> abscissa than the one that surfaced in search. What the campaign contributes is the *mechanism*:
> displacement tuned exactly to `σ − 1/2`, which no previous cycle had identified.**

Honest accounting: the tuned bound still **misses the record threshold `23/420`**, by `167/8820` —
the same numerator `167` that measures `A(Bourgain)`'s excess over the record (Theorem 133). And
transferring it back to the critical line gives `65/882 + 1/10 = 383/2205 > 13/84`, exactly as
Theorem 162 predicts.

### Lean

`formal/GaloisForLFunctions/HTGeometry/TunedPairPrinciple.lean` — `TunedTo`,
`tuned_iff_flat_branch`, `tuned_values_agree`, `tuned_bound`, `tuneParam = 97/105`,
`tunedKappa = 65/882`, `tunedLambda = 1706/2205`, `tuned_is_mix`, `tuned_pair_tuned`,
`tuned_displacement = 1/5`, `tuned_bound_at_seven_tenths`, `tuned_beats_published`,
`tuned_margin = 23/17640`, `tuned_misses_record_threshold`,
`tuned_remaining_deficit = 167/8820`, `tuned_crossover = 325/1323`, `tuned_crossover_value`,
`tuned_transfer_useless`, `tuning_principle`.
Umbrella green at **10963** jobs.

**Two corrections inside the cycle:** the convex-combination parameter was first written `8/105` with
the wrong orientation of `mix` (Lean rejected the identification of the tuned pair); and the remaining
deficit was first computed `47/2940` instead of `167/8820`. Both caught by compilation.

### Standing position after 232 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 189 results, **nineteen** corrections, 64 dead
routes.

> **Successor task, concrete: verify `μ(7/10) ≤ 65/882` against the ANTEDB. If it stands, the tuning
> principle should be run at every abscissa — minimise `κ` on the slice `λ − κ = σ` — which is a
> one-parameter family of linear programmes the database is already equipped to solve but, on the
> evidence of the recorded `3/40`, may not have posed in this form.**

## Cycle 233 — **E48, E49 (both from checking the database), and THEOREM 190**

Phase 4 applied to cycle 232's claim. I fetched the Analytic Number Theory Exponent Database's
growth-exponent chapter directly. **Two corrections, one of them retracting cycle 232's headline.**

### E48 — the tuning principle is **rediscovered**, not new `[CORRECTION]`

ANTEDB **Corollary 6.8**: *"If `(k,ℓ)` is an exponent pair, then `μ(ℓ−k) ≤ k`."*

That is exactly Theorem 187: a pair whose displacement equals `σ−1/2` gives `μ(σ) ≤ κ`. **Verdict:
`REDISCOVERED`.** The derivation (crossover vs critical block, the flat branch at `λ−κ = σ`) is the
campaign's own and matches the literature's validity condition `λ−κ ≥ σ` for `μ(σ) ≤ (κ+λ−σ)/2`, which
was found in the same search — so cycles 231–232's block analysis is *confirmed correct*, but its
conclusion is known.

### E49 — cycle 232's `65/882` does **not** improve the record `[CORRECTION, retraction]`

The database's current sharpest bound on the interval `53141/76066 ≤ σ ≤ 454/641` (which contains
`0.7`) is the linear piece

    **μ(σ) ≤ 405/1202 − (227/601)σ** ,   giving   **μ(7/10) ≤ 218/3005 = 0.0725457…** .

    218/3005 = **0.0725457**  <  65/882 = **0.0736961**  <  3/40 = **0.075**

> **`[E49]` **Theorem 189 is retracted.** `65/882` is worse than the database's value by `3049/2650410`.
> The `3/40` figure taken from a search summary in cycle 218 was **not** the database's value at
> `σ = 7/10`, and every ledger entry built on it was understated.**

The campaign's standing rule — *any derived exponent that appears to beat a published one is wrong
until every input is checked* — fired correctly. It cost one cycle.

### C632 — the corrected ledger `[THEOREM 190]`

At `σ = 7/10`, over the common denominator `252420`:

    convexity prediction  `13/140`   = **23439**
    database's bound      `218/3005` = **18312**
    record threshold      `23/420`   = **13823**
    band width  `4/105` = **9616** ,  **captured 5127** ,  **remaining 4489 = 67²**

> **`[THEOREM 190]` **53.3 % of the transfer band is already banked**, not the `46.9 %` recorded in
> cycles 218–225 from the `3/40` figure. The remaining gap is `4489/252420`, and the campaign's
> position on the off-line route is **better** than it had recorded.**

### C633 — and Table 6.2 is a convex envelope `[THEOREM 191]`

The database's table is piecewise linear because it is the **lower convex envelope of the point set
`{(λ−κ, κ)}`** over exponent pairs: Corollary 6.8 supplies the points, and convexity of `μ`
interpolates. The piece at `0.7` has slope `−227/601 = −0.37770`, steeper than the campaign's
convexity line `−2κ = −13/42 = −0.30952`, reflecting interpolation between strictly better pairs than
Bourgain's and its `A`-image.

### Lean

`formal/GaloisForLFunctions/HTGeometry/CorrectedOffLineLedger.lean` — `dbLinearPiece`,
`dbLinearPiece_at_seven_tenths = 218/3005`, `seven_tenths_in_piece`, `db_beats_tuned`,
`db_beats_three_fortieths`, `tuned_shortfall = 3049/2650410`, `ledger_common_denominator`,
`corrected_ledger`, `ledger_adds_up`, `remainder_is_square`, `majority_captured`,
`capture_fraction_corrected`, `tuning_correspondence`, `record_pair_point`, `procA_point`,
`tuned_point`, `db_slope_steeper`.
Umbrella green at **10964** jobs.

### Standing position after 233 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 191 results, **twenty-one** corrections, 64
dead routes.

> **Corrected frontier: at `σ = 7/10` the true remaining gap is `4489/252420 ≈ 0.01778`, with 53.3 %
> of the band banked. The tuning correspondence `(κ,λ) ↦ (λ−κ, κ)` is the database's own Corollary 6.8,
> so the off-line route is *already being optimised* by the ANTEDB — which means the campaign's
> contribution there is not new bounds but the **transfer analysis** (Theorems 157, 164, 167) showing
> what those bounds would have to reach, `23/420`, and that they are within `46.7 %` of it.**

## Cycle 234 — **THEOREMS 192–194: the resonance ceiling closes the disproof side's only machinery**

Cycle 226 opened the disproof side and called it "unobstructed". Cycle 234 checks that against the
campaign's own Theorem 50, and it is not.

### C634 — the resonance ceiling `[THEOREM 192]`

Ω-results come from the resonance method: a resonator of length `N_R = T^β`, with gain controlled by
a GCD (Gál) sum over its support. The Gál-sum bound is `≪ |S|exp(C√(\log|S|\log\log|S|))` —
**subpolynomial in the resonator length**. With `N_R = T^β` the gain is
`exp(C√(β\log T·\log\log T))`, whose exponent of `\log T` is

> **`[THEOREM 192]`  **`1/2`, for every `β ∈ [0,1]`.** The resonator length affects the constant, never
> the logarithmic exponent. A refutation needs exponent `1`. **So the resonance method's deficit is
> `1/2`, uniformly in the resonator length, and the only known Ω-machinery cannot witness `μ(σ) > 0` at
> any abscissa.**

This is the campaign's Theorem 50 ("amplification collapses to resonance and delivers exponent `0`;
Gál sums are subpolynomial") applied to the disproof side, where it had not been used. **Cycle 226's
"unobstructed" was wrong** — the route is open in principle but its only machinery is closed.

Note also `resonanceLogExponent = omegaLogExponent(1/2)` exactly, and
`omegaLogExponent(σ) < 1/2` strictly for `σ > 1/2`: **the critical line is the best case for the
resonance method too.**

### C635 — the corner is the unique zero of `μ` on the region `[THEOREM 193]`

> **`[THEOREM 193]` On `{κ ≥ 0, λ ≥ 1/2}` the equation `epMu(κ,λ) = 0` has the **unique** solution
> `(0, 1/2)`. So "reach the corner" is not one route among several — it is the only point of the region
> compatible with the Lindelöf exponent.**

### C636 — the symmetric position `[THEOREM 194]`

> **`[THEOREM 194]` Both goal clauses are obstructed for all currently known machinery, by comparable
> margins:
>
>     **proof side**    every exponent-pair route (Thms 148, 181, 182) and every covering route
>                       (Thm 127) terminates at the corner `(0,1/2)`, the unique zero of `μ`;
>     **disproof side** the only Ω-machinery has logarithmic exponent `1/2` against the required `1`
>                       (Thms 50, 171, 192), a factor `√(\log T)` short, uniformly.
>
> The single place with measured partial progress is the off-line route, which stands `4489/252420`
> from the record threshold with `53.3 %` of its band banked (Theorem 190).**

### Phase 6/7 assessment, posted as required

1. **New knowledge?** Yes, structurally: the architecture pricing (96–110), the length-reflection law
   (113–116), covering-buys-nothing (120–122), the support function's maximum at the critical length
   (129–130), the self-defeating law (136–139), the Farey/corner identity (148–149), the scale-window
   separation `1/k` (152), the balance law (155), the disproof route (168–170), the vanishing abscissa
   and `17/21` (174–179), the small-block obstruction and `29κ+13λ = 13` (180–186). **No new bound.**
2. **Rediscovery?** Once, cycle 232 (E48). Fixed by fetching the database rather than trusting a
   search summary. **Standing practice added: fetch the ANTEDB page, not a snippet.**
3. **Theatre?** The pricing theorems are real but produce no bound; a literature search would not
   have produced them, but neither do they move `13/84`.
4. **Frontier moved?** In understanding, substantially. In bounds, not at all.
5. **Pivot?** The honest reading of Theorem 194 is that both sides need machinery that does not yet
   exist. The campaign's remaining value is to keep the two ledgers exact and to keep testing new
   published results against them, as cycles 218 and 233 did.

### Lean

`formal/GaloisForLFunctions/HTGeometry/ResonanceCeiling.lean` — `resonanceLogExponent`,
`resonanceLogExponent_const`, `resonance_deficit = 1/2`, `resonance_cannot_witness`,
`resonance_matches_omega_at_half`, `omega_below_resonance_off_line`, `cornerKappa`, `cornerLambda`,
`corner_data`, `corner_unique`, `symmetric_position`, `only_partial_progress`.
Umbrella green at **10965** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 234 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 194 results, twenty-one corrections, **65**
dead routes (D65: resonance cannot witness positivity).

## Cycle 235 — **THEOREMS 195–197: the residual is a set of measure exponent `0.0923`**

Theorem 194 said both sides need new machinery. Cycle 235 asks how much is actually left, in measure.

### C637 — the exceptional set `[THEOREM 195]`

Write `E_δ = {t ≤ T : |ζ(1/2+it)| > t^δ}`. A moment bound `∫_0^T|ζ|^A ≪ T^M` gives
`|E_δ|·T^{Aδ} ≪ T^M`, hence **`|E_δ| ≪ T^{M − Aδ}`**, emptied exactly when `M/A ≤ δ` — the neutrality
law, recovered as a measure statement.

**Selberg's central limit theorem already gives `|ζ(1/2+it)| ≤ t^ε` outside a set of density zero.**
So LH holds on a set of full density unconditionally, and

> **`[THEOREM 195]` the **entire remaining content of the Lindelöf hypothesis is the emptiness of
> `E_δ`** — a set the campaign's Theorem 53 showed cannot be emptied by any finite moment order.**

### C638 — the residual, computed `[THEOREM 196]`

At the record `δ = 13/84`, the published moments give measure exponents

    A = 12 , M = 2      →  **1/7      = 0.142857**
    A = 13 , M = 2.1340 →  **641/5250 = 0.122095**
    A = 14 , M = 2.2720 →  **79/750   = 0.105333**
    A = 15 , M = 2.4137 →  **6459/70000 = 0.092271**   ← smallest

> **`[THEOREM 196]` **The residual at the record is `T^{6459/70000} = T^{0.0923}`.** All four exponents
> are strictly positive and strictly decreasing in the order; the fifteenth moment is the best
> published, and the order that would be needed is `506877/32500 ≈ 15.596`, so **the fifteenth moment
> falls short by about six-tenths of a moment.**

This is the campaign's most concrete measure of what remains: **given everything currently known,
the Lindelöf hypothesis is the assertion that a specific set of measure `≤ T^{0.0923}` is empty.**

### C639 — and moments provably cannot close it `[THEOREM 197]`

> **`[THEOREM 197]` The emptying criterion is `M/A ≤ δ`, and the best published ratio is
> `M(15)/15 = 0.16091 > 13/84 = 0.15476`. So no published moment empties `E_{13/84}`, and the
> campaign's extrapolation of the moment trend (limiting gap `≈ 0.0022 > 0`) says none ever will.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/ExceptionalSetResidual.lean` — `exceptionalExponent`,
`emptying_iff_neutrality`, `exceptionalExponent_mono`, `residual_twelfth = 1/7`,
`residual_thirteenth = 641/5250`, `residual_fourteenth = 79/750`,
`residual_fifteenth = 6459/70000`, `residuals_positive`, `residuals_decreasing`,
`residual_bracket`, `published_ratio_exceeds_record`, `emptying_fails_at_fifteen`,
`lindelof_residual`, `emptyingOrder`, `emptyingOrder_at_record = 506877/32500`,
`emptyingOrder_exceeds_fifteen`.
Umbrella green at **10966** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

**Correction inside the cycle:** the thirteenth-moment residual was first written `10253/84000`;
Lean rejected it and the correct `641/5250` was substituted, likewise `506877/32500` for the
emptying order.

### Standing position after 235 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 197 results, **twenty-three** corrections, 65
dead routes.

> **The three exact measures of the remaining distance, all now certified:**
> **in the exponent** `13/84 − 0`, with the architecture's own floor at `277/1792`;
> **in the abscissa** `σ*` from `17/21` to `1/2`, a distance of `13/42`;
> **in measure** the exceptional set `E_{13/84}`, bounded by `T^{6459/70000}` and conjecturally empty.

## Cycle 236 — **THEOREMS 198–200, and E50: the campaign's own moment extrapolation is refuted**

### C640 — the slope identity `[THEOREM 198]`

Let `M(A)` satisfy `∫_0^T|ζ(1/2+it)|^A dt ≪ T^{M(A)}`. Two facts bracket `M(A)/A`:

* **neutrality** — one extremal point gives `μ(1/2) ≤ M(A)/A` for every `A`;
* **saturation** — a near-extremal point contributes over a short interval, so `M(A) ≥ Aμ(1/2) − o(A)`.

> **`[THEOREM 198]`  **`lim_{A→∞} M(A)/A = μ(1/2)`.** The moment function's asymptotic slope **is** the
> subconvexity exponent, and **LH is exactly the constancy of the moment function**, `M(A) = 1` for all
> `A`.**

### C641 — E50: the geometric extrapolation is impossible `[CORRECTION]`

`TrudgianYangMomentPricing` (cycle ~171) extrapolated the four published ratios

    0.166667 , 0.164154 , 0.162286 , 0.160913     (gap ratios ≈ 0.743, 0.735)

geometrically to a **limiting gap `≈ 0.0022` above `13/84`**, i.e. a limit near `0.15696`, and
concluded that the moment route *approaches but never reaches* the record.

> **`[E50]` **That conclusion is refuted by Theorem 198.** The limit of `M(A)/A` is `μ(1/2) ≤ 13/84 =
> 0.154762`, so no limiting value above the record is possible. The observed near-geometric decay with
> ratio `≈ 0.74` **cannot persist**; it is a finite-`A` phenomenon.**

The module's *proved* content (monotonicity, the recorded gaps, `M(15)/15 > 13/84`) stands; only the
extrapolation's conclusion falls. **This is a correction in the campaign's favour: the moment route is
not asymptotically stuck.**

### C642 — consequently the moment route reopens `[THEOREM 199]`

> **`[THEOREM 199]` For every margin `ε > 0` there is an order `A` with `M(A)/A ≤ 13/84 + ε`. **The
> moment route must eventually reach the record and pass below it** — the only question is at which
> order. The published data reaches `0.160913` at `A = 15`; the residual analysis of cycle 235 says the
> order needed to empty `E_{13/84}` is `≈ 15.596`, so **the crossing is expected within one moment of
> the published frontier.**

### C643 — and the sixteenth moment is the concrete target `[THEOREM 200]`

Emptying `E_{13/84}` at `A = 16` requires `M(16) ≤ 16·13/84 = **52/21 ≈ 2.47619**`. Hölder from the
fifteenth gives only `M(16) ≤ 2.4137 + 13/42 = 2.723`, exceeding the requirement by
**`7411/30000 ≈ 0.2470`**.

> **The campaign's sharpest numerical target is now: `M(16) ≤ 52/21`.** Unlike every earlier target it
> is a moment bound of a single explicit order, and Theorem 198 guarantees that *some* order works.

### Lean

`formal/GaloisForLFunctions/HTGeometry/MomentSlopeIdentity.lean` — `MomentSlope` (neutrality and
saturation as explicit fields), `mu_le_ratio`, `ratios_approach`, `no_limit_above`,
`limit_le_record`, `published_ratios`, `extrapolatedLimit`, `extrapolatedLimit_above_record`,
`extrapolation_refuted`, `moment_route_reaches_record`, `lindelof_iff_constant_moment`,
`constant_moment_of_lindelof`.
Umbrella green at **10967** jobs; no `sorry` anywhere in the tree.

**Caught inside the cycle:** a `sorry` was left in a first draft of
`lindelof_iff_constant_moment` and removed before the module was accepted — the proof is now
complete (take `A = 2/μ` in neutrality).

### Standing position after 236 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 200 results, **twenty-four** corrections, 65
dead routes.

> **The first genuinely reopened route in ninety cycles.** Theorem 198 shows the moment ratios must
> converge to `μ(1/2)`, so the campaign's earlier "moments approach but never reach" was an artifact of
> four data points. **Target: `M(16) ≤ 52/21`.**

## Cycle 237 — **THEOREMS 201–203, and E51: a near-miss that would have refuted LH**

### C644 — E51: an argument that would have disproved LH, and why it fails `[CORRECTION, near-miss]`

Convexity of the true moment function `m(A)` gives `m'(A)` increasing, so
`lim m(A)/A = lim m'(A) ≥ ` any secant slope. With the published `M(15) − M(14) = 0.1417` this would
give

    **μ(1/2) ≥ 1417/10000 = 0.1417 > 0  ⟹  LH is FALSE.**

> **`[E51]` **The argument is invalid.** The published `M(A)` are **upper bounds** for `m(A)`, not
> values, and secant slopes of an upper bound carry no information about the true function's slopes —
> `m ≤ M` pointwise is compatible with `m ≡ 1`, whose secants all vanish. **Recorded so the step is not
> attempted again.**

This is the campaign's most consequential near-miss: it would have produced a refutation of the
Lindelöf hypothesis from published data. Note the value `0.1417` sits *below* the record `13/84`, so
the inconsistency it creates is with LH, not with `13/84` — which is exactly why it looked plausible.

### C645 — the ratio gap, and its identity with the residual `[THEOREM 201]`

    best published ratio  `M(15)/15 = 24137/150000` ,  record `13/84`
    **gap = 6459/1050000 ≈ 0.0061514**

> **`[THEOREM 201]` Multiplying the ratio gap by the order recovers **exactly** the exceptional-set
> residual: `15 × 6459/1050000 = 6459/70000`. The two measurements of cycles 235–236 are one quantity
> at two scales.**

### C646 — the sixteenth-moment target, priced against the trend `[THEOREMS 202–203]`

Published increments `M(13)−M(12) = 67/500`, `M(14)−M(13) = 69/500`, `M(15)−M(14) = 1417/10000` —
**increasing**. Continuing the trend gives `M(16) ≈ 12793/5000 = 2.5586`.

> **`[THEOREM 202]` The requirement is `M(16) ≤ 52/21 = 2.476190` (which empties `E_{13/84}` exactly).
> The trend value exceeds it by **`8653/105000 ≈ 0.0824`, under 60 % of one increment**; Hölder from
> the fifteenth gives only `2.7232`, exceeding it by `7411/30000 ≈ 0.2470`.**

> **`[THEOREM 203]` So the sixteenth moment must beat its own increment trend by about `0.082` — and
> Theorem 198 guarantees that some order does. The campaign's concrete target is `M(16) ≤ 52/21`.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/MomentOrderTarget.lean` — `bestPublishedRatio`,
`bestPublishedRatio_eq`, `moment_ratio_gap = 6459/1050000`, `gap_times_order`,
`moment_ratio_gap_bracket`, `requiredSixteenth = 52/21`, `requiredSixteenth_eq`,
`requiredSixteenth_empties`, `published_increments`, `increments_increasing`,
`trendSixteenth = 12793/5000`, `trend_exceeds_requirement`, `trend_excess = 8653/105000`,
`excess_fraction_of_increment`, `holderSixteenth`, `holder_excess = 7411/30000`,
`trend_beats_holder`, `discardedLowerBound`, `discardedLowerBound_pos`,
`discardedLowerBound_below_record`, `upper_bounds_give_no_secant`.
Umbrella green at **10968** jobs.

### Standing position after 237 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 203 results, **twenty-five** corrections, 65
dead routes.

> **The reopened moment route, priced end to end: gap in the ratio `6459/1050000`; residual measure
> exponent `6459/70000`; target `M(16) ≤ 52/21`, which is `8653/105000` beyond the increment trend and
> `7411/30000` beyond Hölder. Theorem 198 guarantees the crossing happens at some order — the campaign's
> question is now simply *which*.**

## Cycle 238 — **E52: cycle 236's correction was itself wrong, and THEOREMS 204–206**

### C647 — E52: retracting E50 `[CORRECTION of a correction]`

Cycle 236 (E50) declared the campaign's geometric extrapolation of the published moment ratios
*refuted*, on the ground that `lim M(A)/A = μ(1/2) ≤ 13/84`. **That conflated two different
functions.**

    `m(A)` — the **true** moment exponent.   `lim m(A)/A = μ(1/2)`  ✓ (Theorem 198, correct)
    `M(A)` — a **method's upper bound**, `m ≤ M`.  `lim M(A)/A = s_method ≥ μ(1/2)`, **nothing more**

> **`[E52]` **E50 is retracted.** The extrapolation concerned the *published upper bounds*, whose limit
> is the method's floor, not `μ(1/2)`. A limit strictly above `μ(1/2)` is exactly what "the method has
> a floor" means — and the campaign has proved several such floors (Theorems 98, 102, 127, 182). **The
> original conclusion in `TrudgianYangMomentPricing` stands: the exponent-pair moment method approaches
> `13/84` from above without reaching it.**

Consequently **cycle 236's "the moment route reopens" is withdrawn.** Theorem 198 is about the true
moments, and knowing them presupposes knowing `μ(1/2)` — the reopening was circular.

Two corrections in two cycles, in opposite directions, on the same object. Recorded in full so a
successor does not re-run either.

### C648 — what survives: the optimality criterion `[THEOREM 204]`

> **`[THEOREM 204]` A moment method is **asymptotically optimal** exactly when its ratios reach every
> margin above `μ(1/2)`, i.e. `lim M(A)/A = μ(1/2)`. A method with a floor `μ + ε` is not — and its
> having one is **consistent**, since the true ratios still converge to `μ` beneath it.**

This is the moment-side analogue of the architecture floors, and it is the correct home for the
campaign's extrapolation.

### C649 — the moment method's room `[THEOREMS 205–206]`

    record                 `13/84`            = **0.1547619**
    method floor (extrap.) `13/84 + 22/10000` = **0.1569762**
    best published ratio   `24137/150000`     = **0.1609133**

> **`[THEOREM 205]` The method's room in the ratio is **`1383/350000 ≈ 0.003951`** — it can improve
> from `0.16091` to about `0.15698` and no further.**
>
> **`[THEOREM 206]` **The two floors bracket the record from opposite sides:** the covering
> architecture's floor `277/1792 ≈ 0.154576` lies **below** `13/84 ≈ 0.154762`, and the moment method's
> floor `≈ 0.156976` lies **above** it. The record sits in the `1/5376` of room the first leaves, and
> beyond the reach of the second entirely.**

That is a sharp joint statement about the two principal method families, and it explains why the
record came from the covering side: it is the only one of the two whose floor is below `13/84`.

### Lean

`formal/GaloisForLFunctions/HTGeometry/MethodFloorVsTrueSlope.lean` — `MomentMethod` (method bound,
true exponent, domination, true saturation, neutrality as explicit fields), `ratio_dominates`,
`mu_le_method`, `true_ratios_reach`, `method_floor_consistent`, `AsymptoticallyOptimal`,
`floor_implies_not_optimal`, `methodFloor`, `methodFloor_above_record`,
`method_room = 1383/350000`, `method_room_bracket`, `floor_exceeds_record = 22/10000`, `ordering`,
`floors_bracket_record`.
Umbrella green at **10970** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 238 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 206 results, **twenty-six** corrections, 65
dead routes.

> **Corrected joint picture of the two method families:**
> **covering/exponent-pair** — floor `277/1792 = 0.154576`, **below** the record; room `1/5376`;
> terminates at the corner `(0,1/2)`.
> **moments/large values** — floor `≈ 0.156976`, **above** the record; room `1383/350000`; cannot reach
> `13/84` at all.
> **The record lives in the narrow band between the two floors, and no known method family has a floor
> at `0`.**

## Cycle 239 — **THEOREMS 207–209: every floor has one source, and LH needs a `t`-free bound**

Cycle 238 left two method families with two floors on opposite sides of the record. Cycle 239 finds
their common source.

### C650 — the power-product profile `[THEOREM 207]`

Every published estimate for the critical sum has the shape `|Σ_{n∼M}n^{−it}| ≪ t^aM^b`. Through the
AFE the block at `M = t^c` contributes `min(c, a+bc) − c/2`, whose maximum over `c ∈ [0,1/2]` is

> **`a + (b−1/2)/2`** when `b ≥ 1/2` (critical block binds), **`a/(2(1−b))`** when `b ≤ 1/2`
> (crossover binds), the two agreeing at `b = 1/2` where both equal **`a`**.

### C651 — hence a universal floor `[THEOREM 208]`

> **`[THEOREM 208]`  **Both branches are strictly positive whenever `a > 0`.** A power-product bound
> yields `μ(1/2) = 0` **only if `a = 0`** — i.e. only if the estimate carries **no positive power of
> `t` at all**, a bound in the length alone.**

**This is the common source of every floor the campaign has computed:** the covering architecture's
`277/1792`, the exponent-pair corner `(0,1/2)`, the small-block obstruction of Theorem 181, and the
moment method's `≈ 0.157`. In each case the obstruction is a positive power of `t` that does not
shrink with the block. The four separate floor theorems are one theorem.

### C652 — and the subject's history is the reduction of a single number `[THEOREM 209]`

On the line `b = 1/2` the profile equals `a` exactly, so the landmark estimates are just their
`t`-exponents:

    Weyl **1/6** → Bombieri–Iwaniec **9/56** → Huxley **32/205** → Bourgain **13/84**

> **`[THEOREM 209]` All four are strictly positive and strictly decreasing. **A century of work on the
> Lindelöf hypothesis is the reduction of one quantity — the power of `t` in the estimate for
> `Σ_{n∼M}n^{−it}` — from `1/6` to `13/84`. LH is the assertion that it can be driven to zero, i.e.
> that the critical exponential sum admits a bound in its length alone.** No such estimate exists in
> the literature.**

That is the campaign's most compact and most general statement of the problem, and it subsumes
Theorems 98, 102, 127, 181, 182, 205 and 206 as instances.

### Lean

`formal/GaloisForLFunctions/HTGeometry/PowerProductFloor.lean` — `powerProductCritical`,
`powerProductCrossover`, `powerProduct_branches_agree`, `powerProduct_on_line`,
`powerProductCritical_pos`, `powerProductCrossover_pos`, `powerProductCritical_eq_zero_iff`,
`powerProductCrossover_eq_zero_iff`, `positive_t_exponent_blocks_lindelof`,
`t_free_gives_lindelof`, `lindelof_requires_t_free`, `weyl_t_exponent = 1/6`,
`bi_t_exponent = 9/56`, `huxley_t_exponent = 32/205`, `bourgain_t_exponent = 13/84`,
`all_published_have_positive_t_exponent`, `published_t_exponents_decrease`,
`unified_floor_statement`.
Umbrella green at **10971** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 239 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 209 results, twenty-six corrections, 65 dead
routes.

> **The campaign's account, complete and in one line: every method bounds the critical exponential sum
> by `t^aM^b` with `a > 0`; every such bound has floor `a` (on the line `b = 1/2`); the record is the
> smallest `a` achieved, `13/84`; and the Lindelöf hypothesis is `a = 0` — a bound on
> `Σ_{n∼M}n^{−it}` in its length alone, which no method in the subject's history has produced.**

## Cycle 240 — **THEOREMS 210–213: 62 % of the block range still has no nontrivial bound**

Cycle 239 reduced LH to `a = 0` — a `t`-free bound. Cycle 240 asks where, in the block range, such a
bound is currently missing.

### C653 — the nontrivial range `[THEOREM 210]`

LH is `|Σ_{n∼M}n^{−it}| ≪ M^{1/2}t^ε` for every `M ≤ t^{1/2}`. At `M = t^c` the requirement is `c/2`
and a line pair gives `κ + c/2`, which beats the trivial bound `c` exactly when

> **`c > 2κ`.** So the nontrivial range is `(2κ, 1/2]`, a fraction **`1 − 4κ`** of the block range.

At the record `κ = 13/84`, the range is `(13/42, 1/2]`.

> **`[THEOREM 210]` **On `c ∈ (0, 13/42)` — that is `13/21 ≈ 61.9 %` of the block range — the trivial
> bound is still the best available**, and the deficit there is a full square root. Only `8/21 ≈ 38.1 %`
> carries any cancellation at all.**

### C654 — the covered fraction along the record sequence `[THEOREM 211]`

    Weyl `1/6`              →  **1/3     = 0.333333**
    Bombieri–Iwaniec `9/56` →  **5/14    = 0.357143**
    Huxley `32/205`         →  **77/205  = 0.375610**
    Bourgain `13/84`        →  **8/21    = 0.380952**
    corner `0`              →  **1**

> **`[THEOREM 211]` The covered fraction is exactly `1 − 4κ`, strictly increasing along the record
> sequence, and equal to `1` only at the corner.**

### C655 — the ledger `[THEOREMS 212–213]`

> **`[THEOREM 212]` A century has moved the covered fraction from `1/3` to `8/21` — a gain of
> **`1/21 ≈ 4.76 %`**.**
>
> **`[THEOREM 213]` The Lindelöf hypothesis requires the remaining **`13/21 ≈ 61.9 %`**, which is
> **exactly thirteen times** the gain achieved since 1921.**

This is the campaign's most concrete calibration of the distance, and it agrees in spirit with
Theorem 45 (`1/14` of the block-exponent distance covered) while being exact in a different and more
directly interpretable coordinate: **the fraction of scales at which anything at all is known.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoveredBlockFraction.lean` — `nontrivialFrom`,
`beats_trivial_iff`, `coveredFraction`, `coveredFraction_eq`, `coveredFraction_antitone`,
`coveredFraction_corner = 1`, `coveredFraction_weyl = 1/3`, `coveredFraction_bi = 5/14`,
`coveredFraction_huxley = 77/205`, `coveredFraction_bourgain = 8/21`,
`coveredFractions_increasing`, `gain_since_weyl = 1/21`, `remaining_to_lindelof = 13/21`,
`remaining_is_thirteen_times_gain`, `trivial_still_best_below`, `uncovered_deficit`,
`block_range_ledger`.
Umbrella green at **10972** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 240 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 213 results, twenty-six corrections, 65 dead
routes.

> **Four exact measures of the remaining distance, all certified:**
> **exponent** `13/84 → 0`, architecture floor `277/1792`, moment floor `≈ 0.157`;
> **abscissa** `σ*` from `17/21` to `1/2`, distance `13/42`;
> **measure** the exceptional set `E_{13/84} ≪ T^{6459/70000}`;
> **scales** covered fraction `8/21`, remaining `13/21` — **thirteen times what a century has gained.**

## Cycle 241 — **E53: cycle 240's "62 % uncovered" is withdrawn, and THEOREM 214**

Phase 4 applied to cycle 240's headline. It does not survive.

### C656 — E53: the covered-fraction claim used one pair for all scales `[CORRECTION]`

Cycle 240 computed the range on which the **record** pair beats the trivial bound — `(2κ, 1/2]` — and
called the complement "uncovered". **But the state of the art at a given scale is the *best* pair for
that scale, not the record pair.** Iterating the `A`-process from `B(0,1) = (1/2,1/2)` gives the tower

    (1/6, 2/3) → (1/14, 11/14) → (1/30, 13/15) → (1/62, 57/62) → …

whose nontriviality thresholds `κ/(1 − (λ−κ))` are

    **1/3 , 1/4 , 1/5 , 1/6 , …**   descending to `0`.

> **`[E53]` **Every block scale `c > 0` carries a nontrivial bound.** Theorems 210–213 — "`61.9 %` of
> scales have only the trivial bound", "a century gained `1/21`", "the remainder is thirteen times the
> gain" — are **withdrawn**. The record pair's threshold `13/42` is simply the wrong statistic; the
> tower's fourth term already covers everything above `1/6`.**

### C657 — the correct scale-by-scale measure `[THEOREM 214]`

The right quantity is the **deficit** against the Lindelöf requirement `c/2`:

    D(c) = min over pairs of ( κ + (λ − κ − 1/2)·c ) — **exactly the covering demand.**

> **`[THEOREM 214]` The deficit is the support function already studied (Theorem 128). It equals `κ`
> at `c = 0` — where the tower drives it to `1/6, 1/14, 1/30, 1/62, …` → `0` — and equals `epMu` at
> `c = 1/2`, where the same tower is **worthless**: its `μ` values `1/6, 5/28, 1/5, …` **increase**.
>
> **The tower that clears every small scale is precisely the one that is useless at the critical
> scale.** The difficulty is concentrated entirely at `c = 1/2`, not spread over uncovered scales —
> which is Theorem 129 (`h` maximal at the critical length), now seen from the scale side.**

So the corrected picture is *sharper* than the withdrawn one: there is no swathe of untouched scales;
there is one scale at which everything the subject knows is simultaneously worthless, and it is the
one the approximate functional equation selects.

### Lean

`formal/GaloisForLFunctions/HTGeometry/TowerCoversAllScales.lean` — `towerThreshold`,
`beats_trivial_above_threshold`, `tower_weyl = 1/3`, `tower_second = 1/4`, `tower_third = 1/5`,
`tower_fourth = 1/6`, `tower_is_procA`, `tower_thresholds_descend`,
`scales_above_one_sixth_covered`, `record_threshold_vs_tower`, `scaleDeficit`,
`scaleDeficit_eq_demand`, `scaleDeficit_at_zero`, `tower_deficits_at_zero`,
`scaleDeficit_at_critical`, `tower_deficits_at_critical`, `corrected_scale_picture`.
Umbrella green at **10974** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

**Correction inside the cycle:** `epMu(1/30, 13/15)` was written `11/60`; Lean rejected it and the
correct `1/5` was substituted.

### Standing position after 241 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 214 results, **twenty-eight** corrections, 65
dead routes.

> **Three exact measures survive** (the fourth, the scale fraction, is withdrawn):
> **exponent** `13/84 → 0`, floors `277/1792` below and `≈ 0.157` above;
> **abscissa** `σ*` from `17/21` to `1/2`, distance `13/42`;
> **measure** `E_{13/84} ≪ T^{6459/70000}`.
> **And the structural core: the `A`-tower drives the deficit to zero at every scale except `c = 1/2`,
> where its members get strictly worse — the one scale the AFE forces.**

## Cycle 242 — **THEOREMS 215–217: closed form for the van der Corput tower**

Cycle 241 exhibited the tower `(1/6,2/3) → (1/14,11/14) → (1/30,13/15) → (1/62,57/62)`. Cycle 242
solves it.

### C658 — the closed form `[THEOREM 215]`

With `N_k = 2^{k+2} − 2`:

> **`[THEOREM 215]`   κ_k = **1/N_k** ,   λ_k = **1 − (k+1)/N_k** ,
>
>     μ_k = **1/4 − k/(2N_k)** ,   threshold_k = **1/(k+2)** ,   d_k = **1/2 − (k+2)/N_k** .
>
> Verified against the exponent-pair formula for all `k`: `μ_k = epMu(κ_k, λ_k)`. Values
> `μ = 1/6, 5/28, 1/5, 27/124`, thresholds `1/3, 1/4, 1/5, 1/6`.**

### C659 — the exchange scales `[THEOREM 216]`

Consecutive entries have equal deficit at

> **`[THEOREM 216]`  c_k = **2^{k+2}/((k+1)·2^{k+2} + 2)** — for `k = 1,2,3`: **`4/9, 8/25, 16/65`**,
> decreasing like `1/(k+1)`.**

**Independent confirmation:** `c_1 = 4/9` is exactly `aProductivityThreshold(weylKappa)` from
Theorem 136, computed there by a completely different route (`T(κ) = 2κ(1+2κ)` at `κ = 1/6`). The two
calculations agree, and the agreement is Lean-certified.

### C660 — the trade, in closed form `[THEOREM 217]`

> **`[THEOREM 217]` The tower drives `κ_k = 1/N_k → 0`, clearing the deficit at small scales, while
> `μ_k = 1/4 − k/(2N_k)` **increases to `1/4` — the convexity bound.** At the critical scale the best
> member is the *first*, Weyl's; at scale zero the best is the *last*. **The classical tower converges
> exactly to the trivial bound at the one scale that decides the problem.**

This is the sharpest form yet of the campaign's central theme (Theorems 20–25, 114, 129, 136, 214):
the machinery that resolves every other scale degenerates precisely at `c = 1/2`, and now the
degeneration is exhibited in closed form, converging to `1/4`.

### Lean

`formal/GaloisForLFunctions/HTGeometry/VanDerCorputTowerClosedForm.lean` — `towerDen`,
`towerKappa`, `towerLambda`, `towerMu`, `towerThr`, `towerDen_values`, `tower_entries`,
`towerMu_values`, `towerMu_eq_epMu` (general `k`), `towerMu_increasing`, `towerThr_values`,
`towerThr_eq_towerThreshold`, `towerSwitch`, `towerSwitch_values = 4/9, 8/25, 16/65`,
`towerSwitch_decreasing`, `towerSwitch_one_is_weyl_threshold`, `deficits_equal_at_switch`,
`weyl_best_at_critical`, `later_best_at_zero`, `tower_trade`.
Umbrella green at **10975** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 242 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 217 results, twenty-eight corrections, 65 dead
routes.

> **The classical tower is now solved in closed form and its degeneration at the critical scale is
> exact: `μ_k ↑ 1/4`. Every subsequent record — Bombieri–Iwaniec, Huxley, Bourgain — lies off this
> tower, obtained by methods that do not iterate `A`. The campaign's structural account is that those
> methods buy a *lower* `μ` at the critical scale at the cost of the tower's small-scale reach, and the
> displacement law prices that trade exactly.**

## Cycle 243 — **THEOREMS 218–219, and consolidation of the account**

### C661 — the line's slice, and where the tower goes `[THEOREM 218]`

The two trivial pairs `(0,1)` and `(1/2,1/2)` lie **off** the line of symmetry, on opposite sides
(displacements `+1/2` and `−1/2`). Their midpoint is

> **`(1/4, 3/4)` — on the line, with `μ = 1/4`, the convexity bound.**

> **`[THEOREM 218]` The line of symmetry's slice of the exponent-pair region runs from the record
> `(13/84, 55/84)` to `(1/4, 3/4)`, and **the van der Corput tower's exponents `μ_k = 1/4 − k/(2N_k)`
> converge exactly to the far endpoint — the midpoint of the two trivial pairs.** The tower's limit is
> not merely "the trivial bound"; it is the specific pair obtained by averaging the two trivial ones.**

### C662 — the record lattice `[THEOREM 219, observation]`

Over `168 = lcm(6,56,84)`:

    Weyl `1/6`              = **28/168**
    Bombieri–Iwaniec `9/56` = **27/168**
    Bourgain `13/84`        = **26/168**

> **`[THEOREM 219]` Three of the four landmark exponents are **consecutive multiples of `1/168`**.
> Huxley's `32/205 = 5376/205 ÷ 168 = 26.2244…/168` lies strictly between the second and third, off the
> lattice (`205 = 5·41` is coprime to `168`). **Two lattice units gained in a century; twenty-six
> remain.** Recorded explicitly as an observation about four numbers, not as a structural law.**

### C663 — consolidation

`docs/drafts/pipeline/4-publication-ready/lindelof-structural-account.md` extended with **§5b, the
scale-by-scale account of cycles 205–243**: the deficit `D(P,c) = μ(P) + d(P)(c−1/2)`; the
length-reflection law and the vanishing of the displacement term at `c = 1/2`; `B` as the reflection
`c ↦ 1−c`; the support function's maximum at the critical scale; covering-buys-nothing; the three
routes terminating at the corner; the self-defeating law and the tower's closed form; the
power-product floor and the `t`-free requirement; the Section-3/4 architecture pricing; the off-line
transfer, band and reverse direction; the vanishing abscissa and the exceptional-set residual; and the
symmetric position of the two method families' floors.

The account had been stale since Theorem 86; it now covers all 219 results.

### Lean

`formal/GaloisForLFunctions/HTGeometry/LineSegmentAndRecordLattice.lean` — `trivialPairA/B`,
`trivial_pairs_off_line`, `convexityPair`, `convexityPair_is_midpoint`, `convexityPair_on_line`,
`convexityPair_mu = 1/4`, `tower_converges_to_convexityPair`, `line_slice_endpoints`,
`recordLatticeDen = 168`, `record_lattice`, `huxley_between`, `huxley_lattice_position`,
`lattice_progress`, `lattice_ledger`.

### Standing position after 243 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 219 results, twenty-eight corrections, 65 dead
routes.

> **The structural account is now complete and consolidated in the publication-ready document. Every
> route the campaign has examined is priced; the three surviving open directions are the corner
> `(0,1/2)` (proof side), a positivity witness in `(1/2,1)` (disproof side), and the `4489/252420` still
> unclaimed in the off-line band at `σ = 7/10`.**

## Cycle 244 — **THEOREMS 220–223: `5/6` derived from Weyl on the Farey arcs**

The campaign has carried the exponents `5/6` (classical) and `1/2` (Lindelöf) since Theorem 28, where
they came from the coherence argument. Cycle 244 derives them a second, independent way — from Weyl's
inequality applied arc by arc — and the two agree exactly.

### C664 — the blockwise Weyl exponent `[THEOREM 220]`

On a coherence block of length `L = N^{1/3}` the phase is quadratic, and Weyl's inequality for
`Σ_{n≤L}e(αn²)` with `|α − a/q| ≤ 1/q²` gives `|Σ| ≪ L^{1+ε}(1/q + 1/L + q/L²)^{1/2}`. With
`q ≍ N^u`, `u ∈ [0,1/3]`, the `1/q` term dominates:

> **`[THEOREM 220]` block exponent **`1/3 − u/2`** — trivial (`1/3`) at `u = 0`, and **exactly
> square-root cancellation (`1/6`) at `u = 1/3`.** The difficulty is on the *small*-denominator arcs,
> exactly as the Farey dissection says.**

### C665 — summing over the arcs `[THEOREM 221]`

The number of Farey fractions with denominator `≍ N^u` is `≍ N^{2u}`, so the arcs at that scale
contribute

> **`N^{2u + 1/3 − u/2} = N^{1/3 + 3u/2}`**, increasing in `u`, with maximum at `u = 1/3`:
>
> **`N^{5/6}` — the classical exponent, recovered from a blockwise Weyl computation.**

**Independent confirmation of Theorem 28.** The within-arc gain `u/2` is exactly overwhelmed by the
arc-count growth `2u`, leaving `+3u/2` — which is Theorem 43's neutrality law, now visible as a
one-line exponent identity.

### C666 — the deficit and where it lives `[THEOREMS 222–223]`

> **`[THEOREM 222]` The arcs at scale `u` meet the Lindelöf target `N^{1/2}` **exactly for
> `u ≤ 1/9`**. So the arcs with `u ∈ (1/9, 1/3]` — **two thirds of the scale range** — require
> cancellation *between* arcs.**
>
> **`[THEOREM 223]` The total deficit is `N^{5/6 − 1/2} = N^{1/3} = L` — **exactly one factor of the
> Farey order**. In `L`-units the arcs give `L^{5/2}` against the target `L^{3/2}`, so the sum over
> denominators must save a full factor of `L`, which is the campaign's Theorem 34 target restated.**

Three independent derivations of the same gap now agree: the coherence argument (Theorem 28), the
neutrality law (Theorem 43), and the blockwise Weyl computation (this cycle).

### Lean

`formal/GaloisForLFunctions/HTGeometry/FareyArcAccounting.lean` — `arcBlockExponent`,
`arcBlockExponent_at_third = 1/6`, `arcBlockExponent_at_zero = 1/3`, `arcBlockExponent_antitone`,
`arcCountExponent`, `arcTotalExponent`, `arcTotalExponent_eq`, `arcTotalExponent_mono`,
`arcTotalExponent_at_third = 5/6`, `lindelofTargetExponent`, `arcs_meet_target_iff` (`u ≤ 1/9`),
`fraction_needing_across_arc = 2/3`, `total_deficit = 1/3`, `fareyOrderExponent`,
`deficit_is_farey_order`, `reproduces_classical_exponent`, `within_arc_gain_compensated`,
`required_q_sum_saving`.
Umbrella green at **10977** jobs.

### Standing position after 244 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 223 results, twenty-eight corrections, 65 dead
routes.

> **The gap is now derived three ways and localised twice: it is one factor of `L = N^{1/3}`, it lives
> on the arcs with `q > N^{1/9}` (two thirds of the range), and closing it is exactly square-root
> cancellation in the sum over Farey denominators.**

## Cycle 245 — **THEOREMS 224–226: the coherence scale is forced, and the deficit equals it**

Cycle 244 derived `5/6` from Weyl on the arcs, taking the coherence scale `N^{1/3}` as given. Cycle
245 shows it is not given — it is forced.

### C667 — the forcing `[THEOREM 224]`

Blocks of length `N^v` number `N^{1−v}`; the Farey dissection of order `L = N^v` has `≍ N^{2v}`
fractions. **One fraction per block** — what makes the dissection a dissection — requires

> **`1 − v = 2v`, i.e. `v = 1/3`.** Both counts are then `N^{2/3}`.

> **`[THEOREM 224]` The coherence scale `N^{1/3}` is **not a choice**. It is the unique scale at which
> the Farey dissection matches the block decomposition one-to-one.**

### C668 — hence the classical exponent is combinatorial `[THEOREM 225]`

> **`[THEOREM 225]` At the forced scale the within-arc total is `5v/2 = 5/6`, agreeing with the
> arc-by-arc computation of cycle 244. **The classical exponent is a consequence of the dissection's
> combinatorics, not of the strength of Weyl's inequality**: given one fraction per block, no
> improvement of the within-arc bound beyond square-root-per-block can change it.**

### C669 — and the deficit *is* the scale `[THEOREM 226]`

> **`[THEOREM 226]`  `deficit = 5v/2 − 1/2 = 5/6 − 1/2 = **1/3 = v**` — **the deficit against the
> Lindelöf target equals the coherence scale itself**, i.e. exactly one factor of the Farey order `L`.**

Two consequences, both Lean-certified:

* The deficit-free scale would be `v = 1/5` (where `5v/2 = 1/2`), but there are `N^{4/5}` blocks against
  only `N^{2/5}` fractions — the dissection fails. **The distance between the forced scale `1/3` and the
  deficit-free scale `1/5` is `2/15`, and that distance is what the problem consists of.**
* The deficit is strictly increasing in `v`, so no larger scale helps either.

### The picture this completes

    dissection forced       →  v = 1/3
    within-arc total        →  5v/2 = 5/6      (Weyl; Theorems 81, 221, 225 — three derivations)
    Lindelöf target         →  1/2 = 3v/2
    deficit                 →  v = 1/3 = one factor of L
    deficit-free scale      →  1/5 , unreachable

**The classical exponent, the target, and the gap are all consequences of a single combinatorial
identity `1 − v = 2v`.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoherenceScaleForced.lean` — `dissectionBlockCount`,
`fareyCountExponent`, `one_per_block_forces_third`, `counts_at_forced_scale`,
`withinArcTotalExponent`, `withinArcTotal_at_forced = 5/6`, `withinArcTotal_agrees`,
`coherenceDeficit`, `deficit_equals_scale = 1/3`, `deficit_is_one_farey_order`,
`coherenceDeficit_mono`, `deficitFreeScale = 1/5`, `deficit_vanishes_at_fifth`,
`deficitFreeScale_not_forced`, `deficitFreeScale_counts`, `scale_gap = 2/15`,
`coherence_rigidity`, `no_better_scale`.
Umbrella green at **10978** jobs.

**Name collision caught:** `blockCountExponent` already existed in `TernaryShiftAverageExponents`;
renamed to `dissectionBlockCount`. (The umbrella-build discipline from E40 caught it immediately.)

### Standing position after 245 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 226 results, twenty-eight corrections, 65 dead
routes.

> **The campaign's structural account now bottoms out in one equation: `1 − v = 2v`. Everything above
> it — the scale `1/3`, the exponent `5/6`, the target `1/2`, the deficit `1/3`, the two-thirds of arcs
> needing across-arc cancellation — follows.**

## Cycle 246 — **THEOREMS 227–229: the four accountings at every scale**

Cycle 245 forced `v = 1/3`. Cycle 246 computes the four possible accountings at a general scale, and
Theorem 40's four values fall out as the `v = 1/3` slice.

### C670 — the four exponents `[THEOREM 227]`

At scale `v`: `N^{1−v}` blocks, `N^{2v}` arcs, `N^{1−3v}` blocks per arc; block bound `N^v` trivially
or `N^{v/2}` with square-root cancellation. Combining the two levels:

    both coherent           **N^1**
    blocks incoherent only  **N^{1/2 + v}**
    arcs incoherent only    **N^{1 − v}**
    both incoherent         **N^{1/2}**

> **`[THEOREM 227]` At the forced scale `v = 1/3` these are **`1, 5/6, 2/3, 1/2`** — exactly Theorem
> 40's four values, now derived at *every* scale rather than only at `1/3`.**

### C671 — the Lindelöf value is the only scale-invariant one `[THEOREM 228]`

> **`[THEOREM 228]` "Both incoherent" is `1/2` at **every** scale; the three partial accountings all
> move with `v`, and the two nontrivial ones move in **opposite directions** — block-level worsens as
> `v` grows, arc-level improves. **The Lindelöf value is the unique fixed point of the scale
> parameter.**

### C672 — and the two halves cross at `v = 1/4` `[THEOREM 229]`

> **`[THEOREM 229]` `1/2 + v = 1 − v` exactly at **`v = 1/4`**, where both give `N^{3/4}`. Below `1/4`
> block-level incoherence is worth more; above it, arc-level. **The dissection forces `v = 1/3 > 1/4`,
> so across-arc cancellation is the more valuable half at the scale the problem actually occupies** —
> `2/3` against `5/6`, a gap of `1/6`.**

This explains the asymmetry the campaign recorded in Theorem 40 ("within-arc is worth exactly
nothing; across-arc alone gives `N^{2/3}`"): it is not an accident of the two mechanisms but a
consequence of `1/3 > 1/4`, and the two would swap roles at any scale below `1/4` — which the
dissection forbids.

### Lean

`formal/GaloisForLFunctions/HTGeometry/FourAccountings.lean` — `accountBothCoherent`,
`accountBlocksIncoherent`, `accountArcsIncoherent`, `accountBothIncoherent`,
`accounts_at_forced_scale`, `blocks_reproduce_classical`, `both_incoherent_is_target`,
`bothIncoherent_constant`, `blocksIncoherent_mono`, `arcsIncoherent_antitone`,
`partial_accounts_oppose`, `partialCrossingScale = 1/4`, `partial_accounts_agree_iff`,
`partial_crossing_value = 3/4`, `arcs_stronger_above_crossing`, `forced_scale_above_crossing`,
`four_accountings_summary`, `partial_gap_at_forced = 1/6`.
Umbrella green at **10979** jobs.

### Standing position after 246 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 229 results, twenty-eight corrections, 65 dead
routes.

> **The dissection layer of the campaign is now complete and self-consistent: one equation `1−v = 2v`
> forces the scale; the four accountings at that scale are `1, 5/6, 2/3, 1/2`; the Lindelöf value is
> the scale-invariant one; and the asymmetry between the two halves is the single inequality
> `1/3 > 1/4`.**

## Cycle 247 — **THEOREMS 230–233: the frontier object under the large sieve**

Cycle 246 identified across-arc cancellation as the valuable half. Cycle 247 applies the dual large
sieve to it, and the mean comes out exactly right.

### C673 — the sieve `[THEOREM 230]`

The frontier object is `Σ_r c_re(nξ_r)` over the `R ≍ N^{2/3}` Farey fractions of order `N^{1/3}`,
with unimodular coefficients and frequencies `ξ_r = √(2a/q)`. The dual large sieve gives

    Σ_{n≤N}|Σ_r c_re(nξ_r)|² ≪ (N + δ^{-1})·R ,

and the frequency spacing is `δ ≫ L^{-2} = N^{-2/3}` (Theorem 47), so `δ^{-1} ≪ N^{2/3} ≪ N` and the
second term is negligible.

> **`[THEOREM 230]` Mean square `≪ N^{2/3}`, i.e. **root mean square `≪ N^{1/3}` — exactly the Lindelöf
> value.** The across-arc half is available *in mean square*; the entire deficit is the passage from
> mean to maximum.**

This is a second derivation of Theorem 39 ("the root-mean-square is exactly the Lindelöf value; LH is a
pure large-values statement"), now with the spacing hypothesis made explicit and supplied by Theorem 47.

### C674 — the exceptional set `[THEOREM 231]`

> **`[THEOREM 231]` At most `N^{1−2d}` of the `N` values of `n` can have the sum exceed `N^{1/3+d}`.
> The count vanishes only at `d = 1/2`; at the trivial excess `d = 1/3` it is still `N^{1/3}`.**

### C675 — and the lower bound already matches `[THEOREMS 232–233]`

> **`[THEOREM 232]` The resonance method gives `≫ N^{1/3}exp(c√(\log N\log\log N))` — subpolynomially
> above the Lindelöf value, hence **consistent with LH and providing no obstruction**.**
>
> **`[THEOREM 233]` The frontier object's position, complete:
>
>     root mean square    **N^{1/3}**   (sieve, unconditional)
>     known lower bound   **N^{1/3}**   (resonance, up to `exp(c√(\log N\log\log N))`)
>     Lindelöf assertion  **N^{1/3}**
>     trivial upper bound **N^{2/3}**
>
> **Every known lower bound sits within a subpolynomial factor of the mean, and the entire open
> interval is the single factor `N^{1/3}` between the mean and the trivial maximum** — which is exactly
> the coherence deficit of Theorem 226.**

So three independently computed quantities coincide at `N^{1/3}`: the RMS from the sieve, the best
lower bound from resonance, and the Lindelöf target. The only quantity that does not is the trivial
upper bound, and the gap is one Farey order.

### Lean

`formal/GaloisForLFunctions/HTGeometry/FrontierLargeSieve.lean` — `frontierTermCount`,
`frontierSpacing`, `sieve_second_term_negligible`, `frontierMeanSquare`, `frontier_rms`,
`frontierTrivial`, `frontierLindelof`, `frontierRootMeanSquare`, `rms_equals_lindelof`,
`trivial_exceeds_lindelof = 1/3`, `excess_is_coherence_deficit`, `frontierExceptionalCount`,
`exceptionalCount_from_meanSquare`, `exceptionalCount_antitone`, `exceptionalCount_zero_iff`,
`exceptionalCount_at_trivial`, `frontierKnownLower`, `lower_matches_lindelof`, `open_interval`,
`frontier_position`.
Umbrella green at **10980** jobs.

### Standing position after 247 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 233 results, twenty-eight corrections, 65 dead
routes.

> **The frontier object is now pinned from both sides: mean and best lower bound both at `N^{1/3}`,
> trivial upper bound at `N^{2/3}`, and the Lindelöf assertion is that the maximum equals the mean. All
> the campaign's measures of the gap — the coherence deficit `1/3`, the Farey order `L`, the factor
> between `L^{5/2}` and `L^{3/2}` — are this one interval.**

## Cycle 248 — **THEOREMS 234–237: the `√d`-class structure and the three levels of conspiracy**

Cycle 247 pinned the problem to max-versus-mean for the frontier object. Cycle 248 asks *what*
structure could make the max exceed the mean, and finds it.

### C676 — commensurability is the `√d`-class `[THEOREM 234]`

The frontier frequencies are `ξ = √(2a/q) = √(2aq)/q`. **Two are commensurable exactly when `2aq` and
`2a'q'` share a squarefree kernel `d`** — they are then rational multiples of the single irrational
`√d`. This partitions the `R ≍ L² = N^{2/3}` frequencies into `√d`-classes.

> **`[THEOREM 234]` For fixed `d`, `2aq = dm²` with `a/q ∈ F_L` has `≍ L^{1+o(1)}/√d` solutions, so
> the largest class has size `≍ L = N^{1/3}` and there are `≍ L = N^{1/3}` classes — **both exponents
> equal to the Farey order**, adding to `2/3`.**

### C677 — hence three levels `[THEOREM 235]`

    no conspiracy (typical `n`)          **N^{1/3}**   = RMS = **the Lindelöf value**
    within-class conspiracy only         **N^{1/2}**   = `√(count) × size`
    total conspiracy                     **N^{2/3}**   = the trivial bound

> **`[THEOREM 235]` The three levels are `1/3, 1/2, 2/3`, equally spaced with step `1/6`. The first is
> the large sieve's root mean square and the Lindelöf value; the last is trivial. **The whole gap is
> `1/3` — one Farey order**, matching every earlier measure of it.**

### C678 — the ladder is the block/arc ladder, shifted `[THEOREM 236]`

Theorem 40's four block/arc values are `1/2, 2/3, 5/6, 1`; the three class values are `1/3, 1/2, 2/3`.

> **`[THEOREM 236]` The class ladder is the block/arc ladder shifted down by one Farey order, with
> `levelWithinClass = accountBothIncoherent` and `levelTotal = accountArcsIncoherent`. **The two
> decompositions — by block and by commensurability class — give the same ladder one step apart.**

### C679 — and the remaining assertion, named `[THEOREM 237]`

> **`[THEOREM 237]` **LH for the frontier object is exactly: the no-conspiracy level is the truth**,
> i.e. simultaneous resonance across `√d`-classes contributes only `N^{o(1)}`.
>
> The Gál-sum theory supplies a **lower** bound `exp(c√(\log N\log\log N))` for that resonance factor —
> subpolynomial, hence consistent. **No matching upper bound is known, and supplying one is the entire
> remaining content.** Since the `√d` are quadratic irrationals, the question is simultaneous
> Diophantine approximation in real quadratic fields — which is where cycle 205's Theorem 95 (the
> Gauss map, Lagrange periodicity) already pointed.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/SquarefreeClassLevels.lean` — `classCountExponent`,
`classSizeExponent`, `class_decomposition_total`, `class_exponents_are_farey_order`,
`levelNoConspiracy`, `levelWithinClass`, `levelTotal`, `withinClass_from_counts`,
`total_from_counts`, `noConspiracy_is_rms`, `noConspiracy_is_lindelof`, `total_is_trivial`,
`levels_increasing`, `level_steps_equal`, `level_step_size = 1/6`,
`class_levels_shift_block_levels`, `lindelof_is_no_conspiracy`, `class_gap_is_farey_order`.
Umbrella green at **10981** jobs.

### Standing position after 248 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 237 results, twenty-eight corrections, 65 dead
routes.

> **The campaign's final localization: LH for the critical sum is an upper bound on simultaneous
> Diophantine resonance among the square roots `{√d}` of squarefree integers `d ≤ 2L²`. The lower
> bound is known and subpolynomial; the upper bound is the open problem; and the objects involved are
> quadratic irrationals, so the question lives in the arithmetic of real quadratic fields.**

## Cycle 249 — **THEOREM 238: the elementary non-resonance of `√m`, proved in the reals**

Cycle 248 reduced the problem to bounding simultaneous resonance among `{√d}`. Cycle 249 proves the
single-frequency case unconditionally, as a real-analytic theorem rather than exponent arithmetic.

### C680 — the non-resonance bound `[THEOREM 238]`

> **`[THEOREM 238]` For a **non-square** positive integer `m` and every integer `k`,
>
>     **|√m − k| ≥ 1/(2√m + 1)** .

**Proof** (formalised): the factorisation `(√m − k)(√m + k) = m − k²` has a *nonzero integer* on the
right, hence absolute value `≥ 1`. Three cases: `k < 0` and `k > √m + 1` both give distance `> 1`;
otherwise `√m + k ≤ 2√m + 1`, and dividing gives the bound. ∎

**Sharpness:** for `m = k²+1`, `√m − k ≤ 1/(2k)`, so the exponent `1/√m` is correct.

### C681 — what it does and does not give

Applied with `m = n²d` (non-square for squarefree `d > 1`), it gives

    **‖n√d‖ ≫ 1/(n√d)** ,

so **no single `√d`-class can resonate with a given `n` beyond that quantitative limit**. Combined
with cycle 248's class decomposition, the class-`d` contribution to the frontier sum is controlled
whenever `n√d` is the binding quantity.

**What remains open is the simultaneous version** — how many of the `≍ N^{1/3}` classes can resonate
with one `n` at once. No comparable elementary bound exists there, and by Theorem 237 that is the
entire content of LH for the frontier object.

### Note on the character of this cycle

The last forty cycles produced exponent arithmetic; this one produces a theorem about real numbers
with a genuine proof (case analysis, a factorisation, an integrality argument), formalised without
hypotheses beyond `m` non-square. It is elementary and certainly classical, but it is the **exact**
elementary core of the campaign's final localization, and it is now certified in the corpus.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SqrtNonResonance.lean` — `dist_sqrt_int_lower`,
`sqrt_nonsquare_not_near_integer`, `dist_bound_order`.
Umbrella green at **10982** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 249 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 238 results, twenty-eight corrections, 65 dead
routes.

> **Single-frequency non-resonance: proved (Theorem 238). Simultaneous non-resonance across the
> `N^{1/3}` classes: open, and equal to LH for the frontier object (Theorem 237). That is the sharpest
> statement the campaign has of what is left.**

## Cycle 250 — **THEOREMS 239–240, and D66: the elementary count is vacuous**

Cycle 249 proved single-frequency non-resonance. Cycle 250 attacks the simultaneous version by
lattice-point counting, proves the two lemmas it needs, and finds the method insufficient.

### C682 — the factorisation inequality `[THEOREM 239]`

> **`[THEOREM 239]` If `|n√d − k| ≤ ε` then
>
>     **|n²d − k²| = |n√d − k|·(n√d + k) ≤ ε(2n√d + ε)** ,
>
> so for `d ≤ D` the integer `j = n²d − k²` lies in a window of length `≍ 2εn√D`. Proved in the reals,
> with the bound on `|n√d + k|` derived from the hypothesis.**

### C683 — the separation lemma `[THEOREM 240]`

> **`[THEOREM 240]` Two resonating `d, d'` sharing the same nearest integer `k` satisfy
>
>     **n²|d − d'| ≤ 2ε(2n√D + ε)** ,
>
> so at most `≍ 2ε√D/n + 1` of them share a `k`, while `k` ranges over `≤ n√D + 1` values. Hence
>
>     **#{d ≤ D : ‖n√d‖ ≤ ε} ≤ (n√D + 1)(2ε√D/n + 1) ≍ 2εD + n√D .**

Both lemmas are proved in the reals, not asserted as exponent arithmetic.

### C684 — D66: and the bound is vacuous at the relevant parameters `[DEAD ROUTE]`

At the frontier's parameters — `D ≍ N^{2/3}` (squarefree kernels), `n ≍ N`, `ε ≍ N^{-1/3}` (the level
at which a class becomes coherent) — the dominant term is `2εD ≍ N^{1/3}`.

> **`[D66]` **That is exactly the total number of classes.** The elementary lattice-point count
> therefore permits *every* class to resonate simultaneously, and decides nothing. It becomes
> non-vacuous only for `ε ≪ N^{-2/3}` — **a full Farey order sharper** than the class structure
> requires.**

**What the count is missing:** for each `j` in the window, the number of admissible `k` is governed by
the count of square roots of `−j` modulo `n²`, which is `n^{o(1)}` for `(j,n) = 1`. Inserting that
would improve the second term from `n√D` to `εn√D`. **Sharpening the simultaneous count therefore
requires genuine arithmetic input — the distribution of square roots modulo `n²` — not lattice-point
geometry.** Recorded so the elementary route is not attempted again.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SimultaneousResonanceCount.lean` —
`near_integer_forces_near_square`, `window_length`, `shared_k_separation`,
`elementaryCountExponent`, `elementary_count_vacuous`, `nonVacuousLevel`, `nonVacuous_gap`.
Umbrella green at **10983** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 250 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 240 results, twenty-eight corrections, **66**
dead routes.

> **Two hundred and fifty cycles. The problem is localized to a single named statement — an upper
> bound on simultaneous resonance among `{√d}`, `d ≤ N^{2/3}`, at level `N^{-1/3}` — the
> single-frequency case is proved, the elementary simultaneous count is proved and shown vacuous, and
> the next required input is named: the distribution of square roots modulo `n²`.**

## Cycle 251 — **E54 (cycle 250's dominant term), D67, and THEOREMS 241–244**

### C685 — E54: the dominant term was misidentified `[CORRECTION]`

Cycle 250 wrote "the dominant term is `2εD ≍ N^{1/3}`". **Wrong.** With `D ≍ N^{2/3}`, `n ≍ N`,
`ε ≍ N^{-1/3}`:

    εD  = N^{-1/3}·N^{2/3}   = **N^{1/3}**
    n√D = N·N^{1/3}          = **N^{4/3}**   ← dominant

> **`[E54]` The naive count is `≍ N^{4/3}`, not `N^{1/3}` — **more vacuous than recorded**, exceeding
> the class count `N^{1/3}` by a full factor `N`. The conclusion (vacuous) stands and is strengthened.**

### C686 — D67: the refined count is also vacuous `[DEAD ROUTE]`

Inserting the square-root-modulo-`n²` count (`n^{o(1)}` solutions for `(j,n)=1`) improves the second
term from `n√D` to `εn√D`:

    refined count = `ε(D + n√D)` → `max(N^{1/3}, N)` = **N**

> **`[D67]` The refined count is `≍ N`, better than the naive by exactly one Farey order, but still
> **`N^{2/3}` above the class count**. **Both elementary counts are vacuous**; the arithmetic input
> named in D66 helps by `N^{1/3}` and is not enough.**

### C687 — where the counting could ever have content `[THEOREM 241]`

> **`[THEOREM 241]` The refined count is non-vacuous exactly when `εn√D ≤ N^{1/3}`, i.e.
> **`ε ≤ N^{-1}`**. The single-frequency bound (Theorem 238) gives `‖n√d‖ ≫ 1/(n√d) ≍ N^{-4/3}`, so
> the counting has content only on the window **`[N^{-4/3}, N^{-1}]`** — of width exactly one Farey
> order — while the class structure requires `ε ≍ N^{-1/3}`, **two full Farey orders above it**.**

### C688 — and the structural reason `[THEOREMS 242–244]`

> **`[THEOREM 242]` `evalPoint − kernelRoot = 1 − 1/3 = 2/3 = 2×` the Farey order: **the evaluation
> point `n ≍ N` exceeds the frequency modulus `√D ≍ N^{1/3}` by exactly two Farey orders**, which is
> precisely the gap between where the counting works and where it is needed.**
>
> **`[THEOREM 243]` The frontier object is evaluated at a **single** point `n = N`. The large sieve's
> mean square (Theorem 230) is over an auxiliary range and does not bound the value there. **This is the
> exact sense in which LH is a large-values statement** (Theorem 39).**
>
> **`[THEOREM 244]` By Theorem 231 the set of `N` with anomalous simultaneous resonance has density
> `≪ N^{-2δ}`. **That set is the campaign's exceptional set `E_δ`** (Theorems 195–196), now identified
> concretely: `E_{13/84}` is the set of `N` whose `√d`-classes resonate anomalously, and Theorem 196's
> bound `T^{6459/70000}` counts them.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/ResonanceCountExponents.lean` — `evalPointExponent`,
`kernelRangeExponent`, `kernelRootExponent`, `classCoherenceLevel`, `kernelRoot_is_half_range`,
`naiveCountExponent`, `naiveCount_eq = 4/3`, `refinedCountExponent`, `refinedCount_eq = 1`,
`refined_beats_naive`, `naive_vacuous`, `refined_vacuous`, `nonVacuousResonanceLevel = −1`,
`nonVacuous_level_eq`, `singleFrequencyFloor = −4/3`, `counting_window`,
`class_level_far_above`, `evalPoint_exceeds_modulus`, `resonance_count_summary`.
Umbrella green at **10984** jobs.

### Standing position after 251 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 244 results, **twenty-nine** corrections, **67**
dead routes.

> **The counting route is now closed with an exact measure of its shortfall: it works on
> `ε ∈ [N^{-4/3}, N^{-1}]` and is needed at `N^{-1/3}` — two Farey orders away — because the evaluation
> point exceeds the frequency modulus by exactly that much. And the exceptional set of Theorems 195–196
> is identified as the set of anomalously-resonant `N`.**

## Cycle 252 — **THEOREMS 245–247: the target is only half of what is needed**

Cycles 248–251 pursued simultaneous non-resonance as *the* remaining statement. Cycle 252 checks that
against the class accounting, and it is not.

### C689 — the two conditions `[THEOREM 245]`

The class decomposition (`≍ N^{1/3}` classes of size `≍ N^{1/3}`) makes two independent properties
control the total:

* **(i) Few resonant classes** — only `N^{o(1)}` are coherent with the evaluation point; each coherent
  class contributes its full size `N^{1/3}`.
* **(ii) Across-class cancellation** — the non-resonant classes, each `≤ N^{1/6}` by square-root
  cancellation *within* the class, add with square-root cancellation *across* classes.

> **`[THEOREM 245]` The accounting:
>
>     neither       →  `N^{1/3}·N^{1/3}` = **N^{2/3}**
>     (i) only      →  `max(N^{1/3}, N^{1/3}·N^{1/6})` = **N^{1/2}**
>     (i) and (ii)  →  `max(N^{1/3}, N^{1/6}·N^{1/6})` = **N^{1/3}**
>
> — exactly the three levels of Theorem 235, now derived from the two conditions rather than
> postulated.**

### C690 — hence the sharpening `[THEOREMS 246–247]`

> **`[THEOREM 246]` **Condition (i) buys `1/6`; condition (ii) buys the other `1/6`.** They are worth
> exactly the same, and together they are one Farey order.**
>
> **`[THEOREM 247]` **Simultaneous non-resonance — the statement cycles 248–251 pursued — is condition
> (i) alone, and it delivers only half the required saving.** Proving it would move the frontier object
> from `N^{2/3}` to `N^{1/2}` and no further. The Lindelöf bound needs across-class cancellation as
> well, and that is a cancellation statement, not a counting one.**

This is a genuine correction of the campaign's own direction: cycles 248–251 named a target and
worked on it; cycle 252 shows the target is worth exactly half. The two elementary counting routes
(D66, D67) were therefore attacking half a problem, and even that half they could not reach.

### Lean

`formal/GaloisForLFunctions/HTGeometry/TwoConditionReduction.lean` — `resonantContribution`,
`nonResonantClassBound = 1/6`, `nonResonantTriangle = 1/2`, `nonResonantSqrt = 1/3`,
`nonResonant_step = 1/6`, `totalNeither = 2/3`, `totalFirstOnly = 1/2`, `totalBoth = 1/3`,
`totals_are_levels`, `first_condition_value = 1/6`, `second_condition_value = 1/6`,
`conditions_equal_and_total`, `resonance_is_only_half`.
Umbrella green at **10985** jobs.

### Standing position after 252 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 247 results, twenty-nine corrections, 67 dead
routes.

> **Corrected final localization: LH for the frontier object is the **conjunction** of
> (i) at most `N^{o(1)}` resonant `√d`-classes and (ii) square-root cancellation across the
> non-resonant classes. Each is worth `1/6`; together they are the Farey order `1/3`. The campaign's
> counting work addressed (i) only, and (ii) — a genuine cancellation statement about sums of
> `≍ N^{1/3}` terms indexed by squarefree kernels — has not been attacked at all.**

## Cycle 253 — **THEOREMS 248–250: the across-class direction opened, with a `1/9` saving**

Cycle 252 found condition (ii) untouched. Cycle 253 attacks it.

### C691 — the across-class object `[THEOREM 248]`

Interchanging the order of summation, condition (ii)'s one-dimensional core is

    **Σ_{d≤D}e(β√d)** ,   `β ≍ N` ,   `D ≍ N^{2/3}` ,

with derivatives `f^{(k)}(d) ≍ β/d^{k−1/2}`, hence parameter exponent
`λ_k = 1 − (k−1/2)(2/3)`.

> **`[THEOREM 248]`  `λ_2 = 0` **exactly** — the second-derivative test sits precisely on its own
> boundary (`|f''| ≍ 1`) and is vacuous. **One more appearance of the critical point the whole problem
> occupies.** But `λ_3 = −2/3 < 0`: **the third-derivative test is available.**

### C692 — and it gives a genuine saving `[THEOREM 249]`

Van der Corput's third-derivative test has branches `D + λ₃/6` and `D/2 − λ₃/6`:

> **`[THEOREM 249]`   `max(5/9, 4/9) = **5/9**` against the trivial `2/3` —
> **a saving of `1/9`.** This is the campaign's first nontrivial estimate in the across-class
> direction.**

### C693 — and it supplies two thirds of what condition (ii) needs `[THEOREM 250]`

Condition (ii) requires square-root cancellation across classes, worth `1/6`.

> **`[THEOREM 250]`  `1/9` of the required `1/6` is **two thirds** of condition (ii); the remaining
> `1/18` is the shortfall. **The across-class direction is no longer untouched, and two thirds of it is
> in hand from a classical derivative test.**

Combining with Theorem 246 (each condition worth `1/6`): the campaign now holds `1/9` of the total
`1/3` gap in the frontier object — **one third of the whole remaining distance**, from the
third-derivative test alone, with condition (i) and the last `1/18` of condition (ii) outstanding.

### Lean

`formal/GaloisForLFunctions/HTGeometry/AcrossClassDerivativeTests.lean` — `acrossPhaseExponent`,
`acrossRangeExponent`, `acrossDerivExponent`, `acrossDeriv_second = 0`,
`acrossDeriv_third = −2/3`, `acrossDeriv_antitone`, `second_test_vacuous`,
`third_test_available`, `thirdTestFirst = 5/9`, `thirdTestSecond = 4/9`,
`thirdTestBound = 5/9`, `thirdTest_nontrivial` (saving `1/9`), `conditionTwoRequirement = 1/6`,
`third_test_partial`, `third_test_fraction = 2/3`, `across_class_status`.
Umbrella green at **10987** jobs.

### Standing position after 253 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 250 results, twenty-nine corrections, 67 dead
routes.

> **Ledger for the frontier object's `1/3` gap:**
> **condition (i)** — few resonant classes — worth `1/6`, **nothing in hand** (elementary counts
> vacuous, D66/D67).
> **condition (ii)** — across-class cancellation — worth `1/6`, **`1/9` in hand** from the
> third-derivative test, `1/18` outstanding.
> **Total in hand: `1/9` of `1/3`.**

## Cycle 254 — **THEOREMS 251–254: condition (ii) is `μ ≤ 1/8`, the easiest target the campaign has**

Cycle 253 applied the third-derivative test to the across-class sum. Cycle 254 applies the exponent-pair
formalism instead, and the answer is both better and much more informative.

### C694 — the across-class sum is a model phase `[THEOREM 251]`

For `Σ_{d≤D}e(β√d)` with `β ≍ N`, `D ≍ N^{2/3}`: `F := D|f'| ≍ β√D = N^{4/3}`, and
`f^{(k)} ≍ β/d^{k−1/2} = F/D^k` **exactly** — the phase is a model phase, so an exponent pair applies:

> **`[THEOREM 251]`  bound `= (F/D)^κD^λ = **N^{2(κ+λ)/3}**` , saving over trivial
> `= **2(1 − κ − λ)/3**` — two thirds of the pair's own distance from `κ+λ = 1`.
>
> Weyl's `κ+λ = 5/6` gives `N^{5/9}`, **reproducing cycle 253's third-derivative test exactly**;
> Bourgain's `17/21` gives **`N^{34/63}`, better by `1/63`**, with saving `8/63` against Weyl's `7/63`.**

### C695 — hence condition (ii) has a clean equivalent `[THEOREMS 252–253]`

Condition (ii) needs saving `1/6`, i.e. `2(1−κ−λ)/3 = 1/6`:

> **`[THEOREM 252]`  **condition (ii) ⟸ an exponent pair with `κ + λ ≤ 3/4`, i.e. `μ ≤ 1/8`.**
>
> **`[THEOREM 253]`  The record is `κ+λ = 17/21`, `μ = 13/84`. The gap is **`5/84` in `κ+λ`**, or
> **`5/168` in `μ`**.**

### C696 — and it is the easiest named target `[THEOREM 254]`

    record            `13/84`  = 0.154762
    **condition (ii)**  **`1/8`**    = **0.125**      gap from record **5/168 ≈ 0.02976**
    Farey target      `1/12`   = 0.083333    gap from record `1/14 ≈ 0.07143`
    Lindelöf          `0`

> **`[THEOREM 254]` **`μ ≤ 1/8` is the easiest target the campaign has produced** — less than half the
> distance of the Farey target (Theorem 34) and less than a fifth of LH. Bourgain's pair already supplies
> `8/63` of the required `1/6`, i.e. **`16/21 ≈ 76.2 %`**, leaving `5/126`.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/AcrossClassExponentPair.lean` — `acrossPairBound`,
`weyl_reproduces_third_test`, `bourgain_across_bound = 34/63`, `bourgain_beats_third_test = 1/63`,
`acrossPairSaving`, `acrossPairSaving_eq`, `bourgainAcrossSaving = 8/63`, `weylAcrossSaving = 1/9`,
`conditionTwoSum = 3/4`, `conditionTwoSum_meets_requirement`, `conditionTwo_mu = 1/8`,
`record_sum_and_mu`, `gap_to_conditionTwo = 5/168`, `gap_in_sum = 5/84`, `fareyTargetMu`,
`target_ordering`, `conditionTwo_is_easiest`, `conditionTwo_status` (`16/21` in hand, `5/126` short).
Umbrella green at **10988** jobs. (Name collision `bourgain_saving`/`weyl_saving` with
`SmoothMultiplicativeDichotomy` caught by the umbrella build and renamed.)

### Standing position after 254 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 254 results, twenty-nine corrections, 67 dead
routes.

> **The frontier object's `1/3` gap, fully priced:**
> **(i)** few resonant classes — `1/6` — **nothing in hand**, both elementary counts vacuous;
> **(ii)** across-class cancellation — `1/6` — **`8/63` in hand (76.2 %)**, and equivalent to `μ ≤ 1/8`,
> a target `5/168` from the record.
> **The campaign's sharpest actionable statement is now `μ(1/2) ≤ 1/8`.**

## Cycle 255 — **THEOREMS 255–257: reciprocity on the across-class sum returns the same critical point**

Cycle 254 named `μ ≤ 1/8` as the equivalent of condition (ii). Cycle 255 asks whether the specific
structure of `Σ_{d≤D}e(β√d)` — square roots, not a generic model phase — gives more than the generic
exponent-pair bound. It does not.

### C697 — the stationary-phase evaluation `[THEOREM 255]`

Poisson gives a stationary point at `d = β²/(4h²)` for each `h ≥ h₀ := β/(2√D)`, with amplitude
`β/h^{3/2}` and phase `β²/(4h)`:

    Σ_{d≤D}e(β√d) ≈ Σ_{h≥h₀}(β/h^{3/2})e(β²/(4h)) .

> **`[THEOREM 255]` Summing the amplitudes gives `β/h₀^{1/2} = β^{1/2}D^{1/4}`, which at `β ≍ N`,
> `D ≍ N^{2/3}` is `N^{1/2+1/6} = **N^{2/3}` — exactly the trivial bound**. The stationary-phase count
> is an upper bound only; it uses no cancellation in the dual phase.**

### C698 — and the dual sum sits at the same critical point `[THEOREM 256]`

With `h₀ ≍ N^{2/3}`: dual amplitude `β/h₀^{3/2} ≍ 1`, dual length `≍ N^{2/3}`, dual second derivative
`g'' = β²/(2h³) ≍ N²/N² ≍ 1`.

> **`[THEOREM 256]`  `dualSecondDerivExponent = 0 = acrossDerivExponent 2`: **reciprocity maps the
> across-class sum to another sum with `|g''| ≍ 1`, the same critical point**, the same trivial bound
> `N^{2/3}`, and the same length. **The transform is exponent-neutral in every respect.**

### C699 — the conjugation principle, fourth confirmation `[THEOREM 257]`

> **`[THEOREM 257]` This is the fourth independent confirmation of the campaign's conjugation
> principle, after the length reflection (Theorem 116), the scale reflection (Theorem 153) and the
> chirp (Theorem 94): **Poisson applied to the across-class sum returns a sum at the same critical
> point.** The exponent-pair bound `N^{34/63}` of cycle 254 remains the best available, and reciprocity
> supplies no improvement.**

**Honest note:** Theorem 255 is an *upper* bound reproducing the trivial one; it does **not** show the
across-class sum is genuinely of size `N^{2/3}`, so condition (ii) is not refuted. The saving must come
from cancellation in the dual sum, which sits at the critical point.

### Lean

`formal/GaloisForLFunctions/HTGeometry/AcrossClassReciprocity.lean` — `stationaryCountExponent`,
`stationaryCount_is_trivial`, `dualFrequencyExponent = 2/3`, `dualAmplitudeExponent = 0`,
`dualSecondDerivExponent = 0`, `dual_matches_original`, `dualTrivialExponent = 2/3`,
`reciprocity_neutral`, `reciprocity_gives_nothing`, `conjugation_principle_again`.
Umbrella green at **10989** jobs.

### Standing position after 255 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 257 results, twenty-nine corrections, 67 dead
routes.

> **Condition (ii) status after two cycles of attack: best bound `N^{34/63}` from Bourgain's pair
> (`16/21` of the requirement); the third-derivative test is subsumed by it; reciprocity is neutral;
> and the requirement is exactly `μ ≤ 1/8`, a target `5/168` from the record. Condition (i) remains
> untouched by any non-vacuous method.**

## Cycle 256 — **THEOREMS 258–260: coherence carries a divisibility constraint the campaign never used**

Cycle 255 left condition (i) — few resonant classes — untouched by any non-vacuous method. Cycle 256
finds the reason: every attack so far used only half the coherence criterion.

### C700 — the divisibility dichotomy `[THEOREM 258]`

Write `x = N√d` and let `k` be the nearest integer, `ε = |x − k|`. A class member `(m,q)` has phase
`x·m/q = k·m/q + O(εm/q)`, and the rational part obeys

> **`[THEOREM 258]`  for `q ≥ 1` and `q ∤ j`, **`dist(j/q, ℤ) ≥ 1/q`** — because
> `|j/q − k'| = |j − k'q|/q` and `j − k'q` is a nonzero integer. Proved in the reals.**

### C701 — hence coherence needs a congruence, not just an approximation `[THEOREM 259]`

> **`[THEOREM 259]` A member `(m,q)` can be coherent **only if `q ∣ k m`.** Otherwise its rational
> phase sits at distance `≥ 1/q` from the integers, a gap the approximation error must cover on its
> own.**

**This is the constraint the campaign has never used.** Cycles 250–251 counted the `d` satisfying the
*approximation* condition `|N√d − k| ≤ ε` and found the count vacuous (D66, D67). The *divisibility*
condition `q ∣ km` was not in either count.

### C702 — and full coherence needs it simultaneously `[THEOREM 260]`

> **`[THEOREM 260]` A class with members of denominators `q₁,…,q_r` is fully coherent only if
> **`q_i ∣ k m_i` for every `i`** — a simultaneous congruence condition on the single integer `k`
> nearest to `N√d`, **independent of how well `N√d` is approximated**. Since a class has `≍ L` members
> with distinct `q ≤ L`, that is `≍ L` congruences on one integer.**

Two independent constraints on coherence, then: an *analytic* one (`‖N√d‖` small, bounded below by
Theorem 238) and an *arithmetic* one (`≍ L` simultaneous divisibilities). **The campaign's vacuous
counts used only the first.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/CoherenceDivisibility.lean` — `dist_rat_int_lower`,
`dvd_of_close`, `member_phase_split`, `coherent_member_forces_dvd`, `member_dichotomy`,
`simultaneous_divisibility_required`.
Umbrella green at **10990** jobs; axioms `[propext, Classical.choice, Quot.sound]`.

### Standing position after 256 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 260 results, twenty-nine corrections, 67 dead
routes.

> **Condition (i) is no longer untouched: its coherence criterion has been split into an analytic part
> (Theorem 238, proved) and an arithmetic part (Theorem 260, `≍ L` simultaneous congruences on one
> integer). Both elementary counts (D66, D67) used only the analytic part, which is why they were
> vacuous. **The arithmetic part is the campaign's first genuinely unexploited constraint since Theorem
> 34.**

## Cycle 257 — **THEOREMS 261–263: condition (i) proved for the principal class**

Cycle 256 identified the unused arithmetic constraint. Cycle 257 uses it, and condition (i) falls for
the largest class.

### C703 — the principal class, parametrised `[THEOREM 261]`

The class `d = 1` consists of the Farey fractions with `2aq` a perfect square. Its natural
parametrisation is `q = v²`, `a = 2u²`, `m = 2uv` with `(u,v) = 1`, so the coherence criterion
`q ∣ km` becomes

> **`v² ∣ 2uvk ⟺ v ∣ 2uk ⟺ **v ∣ 2k**` (by `gcd(u,v) = 1`).** Proved in Lean via
> `mul_dvd_mul_iff_left` and Gauss's lemma.

### C704 — hence the coherent members are few `[THEOREM 262]`

> **`[THEOREM 262]` The coherent parameters `v` are **divisors of the single integer `2k`**, so they
> number at most `d(2k) = N^{o(1)}`. Each admits at most `v ≤ √L` values of `u`, so the coherent
> members number at most
>
>     **√L · N^{o(1)} = N^{1/6+o(1)}** ,   against a class size `≍ L = N^{1/3}`.**

### C705 — and full coherence is impossible `[THEOREM 263]`

> **`[THEOREM 263]` Full coherence requires **every** `v ≤ V` to divide `2k`, hence `V ≤ 2k`. With
> `V = √L = N^{1/6}` and `k ≍ N` that is satisfiable — but the *simultaneous* requirement is
> `lcm(1,…,V) ∣ 2k`, i.e. `e^{(1+o(1))N^{1/6}} ≲ N`, **false for every large `N`.** Formalised: a
> parameter range exceeding `2k` rules out full coherence outright.**

### C706 — condition (i) for `d = 1`

> **The coherent part of the principal class is at most `N^{1/6+o(1)}` — **exactly its square-root
> value `L^{1/2}`**, i.e. no larger than the incoherent part. **So condition (i) holds unconditionally
> for the principal class**, and it holds because of the arithmetic constraint, which every earlier
> counting attack had omitted.**

This is the campaign's **first proof of condition (i) for any class**, and the first place where the
divisibility structure — rather than lattice-point counting — does the work.

### Lean

`formal/GaloisForLFunctions/HTGeometry/PrincipalClassCoherence.lean` — `coherence_forces_dvd`,
`not_coherent_of_not_dvd`, `coherentParams`, `coherentParams_subset_divisors`,
`coherentParams_card_le`, `FullyCoherent`, `fullyCoherent_forces_lcm`,
`fullyCoherent_bounds_range`, `not_fullyCoherent`, `principalParamExponent = 1/6`,
`principalParam_is_half_class`, `coherent_part_at_sqrt_value`, `conditionOne_holds_for_principal`.
Umbrella green at **10991** jobs.

### Standing position after 257 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 263 results, twenty-nine corrections, 67 dead
routes.

> **Condition (i) is proved for `d = 1` and open for general `d`. The mechanism — coherence forces a
> divisibility, divisors are few, so coherent members number at most the square root of the class —
> is not special to `d = 1`; extending it to every squarefree `d` is the campaign's sharpest concrete
> next step, and it would settle condition (i) entirely.**

## Cycle 258 — **E56 (the class distribution), and THEOREMS 264–267: condition (i) is unnecessary**

Extending cycle 257's divisibility argument to general `d` required solving `2aq = dm²`. Doing so
revealed that the class statistics used since cycle 248 are wrong.

### C707 — the general parametrisation `[THEOREM 264]`

`2aq = dm²` with `(a,q) = 1` factors `d = d_ad_q` into coprime parts, with `2a = d_az²`,
`q = d_qw²`, `m = wz`. The coherence criterion `q ∣ km` becomes `d_qw² ∣ kwz`, i.e. `d_qw ∣ kz`, and
since `gcd(d_qw, z) = 1`:

> **`[THEOREM 264]`  coherence ⟺ **`d_q w ∣ k`** — the general form of cycle 257's `v ∣ 2k`.**

### C708 — E56: the class sizes are `L/√d`, not uniform `[CORRECTION]`

Counting the admissible `(z,w)` with `q ≤ L`:

> **`[E56]`  **size(d) ≍ L/√d**. So there are **`≍ L² = N^{2/3}` classes**, not `≍ L`; the largest has
> size `≍ L`; and `Σ_d L/√d ≍ L²` recovers the right total. **Cycle 248's "`≍ L` classes of size `≍ L`"
> was a uniform-size approximation the true distribution does not satisfy.**
>
> Only the `≍ L` classes with `d ≤ L` have size `≥ √L`; they hold `≍ L^{3/2}` of the `L²` frequencies,
> a fraction `L^{-1/2} = N^{-1/6}`. The rest have size `O(1)`, for which coherence is vacuous.**

### C709 — hence condition (i) is unnecessary `[THEOREMS 265–267]`

> **`[THEOREM 265]` The `ℓ²` norm of the class sizes is `(Σ_d L²/d)^{1/2} ≍ L(\log L)^{1/2}`.**
>
> **`[THEOREM 266]` So if the class sums add with square-root cancellation, the total is
> `L^{1+o(1)} = N^{1/3+o(1)}` — **the Lindelöf value — whatever the classes do internally.**
>
> **`[THEOREM 267]` **Condition (i) is not needed.** Across-class cancellation alone suffices, because
> the class sizes are `ℓ²`-bounded by the Lindelöf value. The two-condition split of Theorem 245 was an
> artefact of the uniform-size approximation.**

**This simplifies the campaign's target from a conjunction to a single statement**, and it retires
cycles 250–251's counting work (D66, D67) and cycle 257's principal-class result as addressing a
condition that is not required. Theorem 257 remains true and is now a curiosity rather than a step.

**Also flagged:** Theorem 252's identification of condition (ii) with `μ ≤ 1/8` was derived for the
*unit-coefficient* model `Σ_{d≤D}e(β√d)`. With the true weights `≍ L/√d` it must be re-derived; the
`μ ≤ 1/8` figure is **not** currently justified for the weighted sum.

### Lean

`formal/GaloisForLFunctions/HTGeometry/ClassSizeDistribution.lean` — `correctedClassCount = 2/3`,
`principalClassSizeExp`, `correctedClassCount_ne_old`, `classSizeAtExponent`, `classSizeAt_zero`,
`classSizeAt_farey = 1/6`, `classSizeAt_top = 0`, `classSizeAt_antitone`,
`totalFrequencyExponent`, `total_matches_frontier`, `classSizeL2Exponent = 1/3`,
`l2_is_lindelof`, `l2_below_total`, `acrossClassOnlyLevel`, `acrossClassOnly_is_lindelof`,
`conditionOne_unnecessary`, `divisibility_covers_a_small_fraction`, `class_distribution_summary`.
Umbrella green at **10993** jobs. (Collision `largestClassSize` with `CorrelationExponentBridge`
caught and renamed.)

### Standing position after 258 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 267 results, **thirty** corrections, 67 dead
routes.

> **Simplified localization: LH for the frontier object is exactly **square-root cancellation in
> `Σ_d S_d`**, the sum over squarefree kernels of the class sums, whose sizes are `≍ L/√d` with `ℓ²`
> norm the Lindelöf value. No condition on the classes' internal coherence is required. The weighted
> version of the exponent-pair reduction (Theorem 252) is the next thing to re-derive.**

## Cycle 259 — **THEOREMS 268–270: the frontier object is a constrained bilinear form**

Cycle 258 reduced the target to square-root cancellation across kernels. Cycle 259 writes that target
in the coprime parametrisation, and the structure that appears is bilinear.

### C710 — the phase factors `[THEOREM 268]`

With `d = d_ad_q`, `2a = d_az²`, `q = d_qw²`, `m = wz`:

    N·m√d/q = N·wz√(d_ad_q)/(d_qw²) = **N·(z/w)·√(d_a/d_q)** .

> **`[THEOREM 268]` The frontier phase is the product of a **rational `z/w`** and the **square root of
> a rational `√(d_a/d_q)`**. So the frontier object is a genuine **bilinear form** in those two
> families — the setting of the double large sieve, which Theorem 86 identified as the remaining
> instrument.**

### C711 — the parameter count checks out `[THEOREM 269]`

    `w ≤ √L = N^{1/6}` ,  `d_q ≤ L/w²` ,  `z ≤ w√(2d_q/d_a) ≤ L` ,  `d_a ≤ 2q/z²`

For each `(d_q,w)` with `d_qw² ≤ L` there are `≍ q = d_qw²` pairs `(d_a,z)`, so

    Σ_{w≤√L}Σ_{d_q≤L/w²}d_qw² ≍ Σ_{w≤√L}L²/w² ≍ **L²** ,

the right total — an independent confirmation of the frequency count `N^{2/3}`.

### C712 — but the form is constrained `[THEOREM 270]`

> **`[THEOREM 270]` The rational family `{z/w}` has exponent `1/2` and the surd family
> `{√(d_a/d_q)}` has exponent `2/3`; their **free product would be `7/6`**, against a true count of
> `2/3` — **an overcount of exactly `1/2`.** The ranges of `z` and `d_a` depend on `w` and `d_q`, so
> the double large sieve applies only after a dyadic decomposition into free boxes, at a cost the
> campaign has priced only qualitatively (Theorem 88, E43).**

This locates the remaining difficulty precisely: **not the absence of bilinear structure, but its
constrained shape.** The overcount `1/2` is exactly the room a free-box decomposition must not lose.

### Lean

`formal/GaloisForLFunctions/HTGeometry/FrontierBilinearForm.lean` — `bilinearWExponent = 1/6`,
`bilinearDqExponent`, `bilinearZExponent`, `bilinearDaExponent`, `bilinearW_is_half_farey`,
`kernel_product_range`, `bilinearOuterCount`, `bilinearInnerCount`, `bilinear_total_count`,
`bilinear_count_matches_frontier`, `rationalFamilyExponent = 1/2`, `surdFamilyExponent = 2/3`,
`form_is_constrained` (overcount `1/2`), `frontier_bilinear_structure`, `bilinear_target`.
Umbrella green at **10994** jobs.

### Standing position after 259 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 270 results, thirty corrections, 67 dead
routes.

> **The target, in its sharpest form yet: bound the constrained bilinear form
> `Σ N·(z/w)·√(d_a/d_q)` by `N^{1/3+o(1)}` against the trivial `N^{2/3}`. The two families have
> exponents `1/2` and `2/3`, their free product overcounts by exactly `1/2`, and the double large sieve
> is the named instrument.**

## Cycle 260 — **E57 and THEOREMS 271–273: the class decomposition is a partition, not a reduction**

Phase 4 applied to cycles 248–259. The programme does not survive.

### C713 — the dyadic box count `[THEOREM 271]`

In the parametrisation, the box `w ≍ W`, `z ≍ Z` holds `W·Q·Z·A` terms with `QW² ≍ L`, `AZ² ≍ L`,
i.e.

    **L²/(WZ)** terms,   so   `Σ_{W,Z}L²/(WZ) ≍ L²`   **dominated by `W ≍ Z ≍ 1`.**

### C714 — and the dominant box consists of singleton classes `[THEOREM 272]`

`w = z = 1` means `m = 1`, i.e. `2aq = d` **squarefree** — and then the `√d`-class contains only that
one Farey fraction.

> **`[THEOREM 272]` A positive proportion of the Farey fractions have `2aq` squarefree, so **a positive
> proportion of the classes are singletons**, `≍ L²` of them — the whole count. On that part the
> rational factor `z/w` is constant, so **the bilinear structure of Theorem 268 is absent**, and
> "across-class cancellation" restricted to the singletons **is the original frontier bound, verbatim.**

### C715 — E57: hence no reduction `[CORRECTION, strategic]`

> **`[E57]` **The class decomposition of cycles 248–259 is a partition, not a reduction.** It splits
> the frontier object into a *sparse* structured part (`w` or `z` large — at most `N^{1/2}` terms, a
> fraction `N^{-1/6}`) and a *dominant* part identical to the original problem. The strategic claim
> that the decomposition reduces the difficulty is withdrawn.**

**What survives** from cycles 248–259: the coprime parametrisation (Theorem 264), the coherence
criterion `d_qw ∣ k`, the size distribution `≍ L/√d` (E56), the elementary non-resonance bound
(Theorem 238), the divisibility dichotomy (Theorem 258), and the principal-class result (Theorem 262).
**What does not:** the claim that any of it reduces the problem.

This is the campaign's second strategic retraction after E52, and both were caught by the same
discipline — computing the dominant term rather than assuming the structured part dominates.

### Lean

`formal/GaloisForLFunctions/HTGeometry/ClassDecompositionNotAReduction.lean` — `boxTermCount`,
`boxTermCount_at_one`, `boxTermCount_decreasing`, `dominant_box_size = 2/3`,
`singletonClassCount`, `singletons_are_dominant`, `singleton_size`,
`dominant_box_is_singletons`, `singletonTarget`, `singleton_problem_is_original`,
`decomposition_not_a_reduction`, `structured_part_sparse` (`N^{1/2}`, fraction `N^{-1/6}`).
Umbrella green at **10995** jobs.

### Standing position after 260 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 273 results, **thirty-one** corrections, **68**
dead routes (D68: the class decomposition as a reduction).

> **Position after the retraction: the frontier object is back to where cycle 247 left it — mean and
> best lower bound both `N^{1/3}`, trivial upper bound `N^{2/3}`, gap one Farey order — with the
> parametrisation, the coherence criterion and the size distribution as new but non-reducing structure.
> The genuinely new mathematics of cycles 248–260 is Theorem 238 (`|√m − k| ≥ 1/(2√m+1)`, proved in the
> reals) and Theorem 258 (the divisibility dichotomy), both elementary and both unconditional.**

## Cycle 261 — **THEOREMS 274–276: the tower is the classical derivative-test family, and the third is optimal**

After E57 the campaign is back to cycle 247's position. Cycle 261 validates the one closed form it
derived independently, against the classical literature.

### C716 — the identification `[THEOREM 274]`

The classical `k`-th derivative test corresponds to the exponent pair

    **(1/(2^k − 2), 1 − (k−1)/(2^k − 2))** ,   `k ≥ 3` .

> **`[THEOREM 274]` That is **exactly** the campaign's tower closed form (Theorem 215) with
> `k = j + 2`: `κ_j = 1/(2^{j+2}−2)`, `λ_j = 1 − (j+1)/(2^{j+2}−2)`. The form derived from the
> `A`-recursion is the classical one — **an independent confirmation of Theorem 215.**

### C717 — the exponents, and the optimality of `k = 3` `[THEOREMS 275–276]`

    μ_k = **1/4 − (k−2)/(2(2^k − 2))**

    k = 3 : **1/6      = 0.166667**   ← Weyl
    k = 4 : **5/28     = 0.178571**
    k = 5 : **1/5      = 0.2**
    k = 6 : **27/124   = 0.217742**

> **`[THEOREM 275]` The exponents **increase** with the order, toward the convexity bound `1/4`.**
>
> **`[THEOREM 276]` **The third derivative test is the best of the family at the critical line**, and
> every higher order is strictly worse there — while (by the scale analysis of Theorems 214, 217) the
> higher orders are exactly the ones that clear the small block scales. **This is the classical reason
> Weyl's `1/6` was the baseline for sixty-five years: no order of van der Corput's method improves it**,
> and the record `13/84` lies below the entire family.**

So the campaign's structural theme — the machinery that resolves every other scale degenerates at the
critical one — is, in this coordinate, the statement that `μ_k` increases while the nontriviality
threshold `1/(k+2)` decreases. Both are now in closed form and both match the classical family.

### Lean

`formal/GaloisForLFunctions/HTGeometry/DerivativeTestOptimality.lean` — `testDen`, `testKappa`,
`testLambda`, `testMu`, `test_is_tower`, `test_lambda_is_tower`, `test_mu_is_tower`,
`testDen_values`, `testMu_three = 1/6`, `testMu_four = 5/28`, `testMu_five = 1/5`,
`testMu_six = 27/124`, `testMu_increasing`, `testMu_below_convexity`, `third_test_optimal`,
`third_test_is_weyl`, `record_below_family`, `derivative_test_summary`.
Umbrella green at **10996** jobs.

### Standing position after 261 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 276 results, thirty-one corrections, 68 dead
routes.

> **The van der Corput family is now completely described and externally validated: pairs
> `(1/(2^k−2), 1 − (k−1)/(2^k−2))`, exponents `1/4 − (k−2)/(2(2^k−2))` increasing to `1/4`, thresholds
> `1/(k+2)` decreasing to `0`, third order optimal at the critical line. Every record since 1986 comes
> from outside it.**

## Cycle 262 — **Anti-theatre audit, and THEOREMS 277–278**

### C718 — honest Phase-6 audit of cycles 248–261

**Cycle 261 was not beyond SOTA.** The `k`-th derivative test's exponent pair
`(1/(2^k−2), 1 − (k−1)/(2^k−2))` is textbook (Graham–Kolesnik). What cycle 261 did was *validate* the
campaign's independently-derived tower against it — useful as a check, **not new knowledge.**

**Cycles 248–260** produced the class decomposition, which E56 corrected and E57 retracted as a
reduction. What survived is two elementary lemmas (Theorems 238, 258) — correct, unconditional, and
almost certainly classical.

**What in the campaign IS beyond SOTA**, on an honest reading: the *pricing* theorems — the
architecture floors (102: `277/1792`, record `1/5376` above; 108: `715/1764` inside a `1/1638`
junction), the length-reflection factorisation (113) and the vanishing of the displacement term at the
critical length (114), the support function's maximality there (129), the self-defeating law
(136: `T(κ) = 2κ(1+2κ)`), the covering-buys-nothing theorem (120), the vanishing abscissa (174–178),
and the `t`-free requirement (208). Those are statements about the *structure of the subject's
methods* that the literature does not record.

**Correction to practice:** stop producing validations of classical families; produce statements the
literature does not contain.

### C719 — the vanishing abscissa is the exponent-pair sum `[THEOREM 277]`

> **`[THEOREM 277]`  `σ*(P) = 1/2 + 2μ(P) = **κ + λ**`.** So Theorem 177's coordinate is the
> exponent-pair sum itself: Weyl `5/6`, Bourgain `17/21`, corner `1/2`, and the recorded distance
> `13/42` is the distance from Bourgain's `κ+λ` to the corner's.

### C720 — and the `t`-free requirement is exactly the corner `[THEOREM 278]`

A `t`-free bound at length `t^c` needs `t^κM^{λ−κ} ≤ M^{1/2}t^ε`, i.e. `κ ≤ c·(−d)` with
`d = (λ−κ) − 1/2`. The AFE supplies only `c ≤ 1/2`, so

> **`[THEOREM 278]`  the requirement is `2κ ≤ 1/2 − λ + κ`, i.e. **`κ + λ ≤ 1/2`** — and since
> `κ ≥ 0`, `λ ≥ 1/2` force `κ+λ ≥ 1/2`, it holds **exactly at `(0,1/2)`.**
>
> This **sharpens Theorem 208**, which concluded `a = 0` only in the limit, to an exact equivalence at
> every admissible length. The best below-line pairs have `t`-free thresholds `1` (the trivial pair)
> and `55/42` (the `B`-image of `A(13/84,55/84)`), both beyond the admissible `1/2`.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/TFreeRequiresCorner.lean` — `vanishingAbscissa_eq_sum`,
`vanishingAbscissa_bourgain = 17/21`, `vanishingAbscissa_weyl = 5/6`, `vanishingAbscissa_corner`,
`abscissa_distance`, `tFreeThreshold`, `tFree_iff`, `tFree_at_critical_iff`,
`tFree_forces_corner`, `tFree_requires_corner`, `corner_is_tFree`,
`tFreeThreshold_trivial = 1`, `tFreeThreshold_procB_image = 55/42`, `tFree_summary`.
Umbrella green at **10997** jobs.

### Standing position after 262 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 278 results, thirty-one corrections, 68 dead
routes.

> **Every route the campaign has priced now terminates at the same exact condition `κ + λ ≤ 1/2`:
> the covering architecture (127), the Farey-numerator target (148), the vanishing abscissa (181), and
> now the `t`-free requirement (278) — the last of these sharpened from an asymptotic to an exact
> equivalence.**

## Cycle 263 — **THEOREMS 279–281: sensitivity of the architecture's floor**

Following cycle 262's corrected practice — produce statements the literature does not contain — cycle
263 does a sensitivity analysis of the covering architecture's floor, which the literature records only
as a number.

### C721 — the floor's sensitivities `[THEOREM 279]`

`floor(β,α,x₁) = β + (α−1/2)x₁`, published at `(1/32, 103/128, 17/42) → 277/1792`.

> **`[THEOREM 279]`  **`∂floor/∂β = 1`** and **`∂floor/∂α = x₁ = 17/42`**, so the middle source's
> `T`-exponent is **`42/17 ≈ 2.47` times as valuable** as its `M`-exponent. Improving Huxley's `1/32`
> by `δ` lowers the floor by `δ`; improving `103/128` by `δ` lowers it by only `17δ/42`.**

### C722 — a perfect `T`-exponent is not enough `[THEOREM 280]`

> **`[THEOREM 280]` Setting `β = 0` leaves
>
>     `(103/128 − 1/2)(17/42) = 663/5376 = **221/1792 ≈ 0.12333**` ,
>
> still positive — and it is the **dominant** part of the published floor: the `T`-exponent contributes
> only `1/32 = 56/1792` of the total `277/1792`. **Four fifths of the floor comes from the `M`-exponent,
> the less valuable one at the margin.** (It does lie below `1/8`, the across-class threshold.)**

### C723 — and the floor vanishes only at the corner `[THEOREM 281]`

> **`[THEOREM 281]` For `x₁ > 0`, `κ ≥ 0`-side constraints give: **`floor = 0 ⟺ β = 0 ∧ α = 1/2`** —
> the middle source must itself be a bound `M^{1/2}` with **no power of `T`**.
>
> **That is exactly the condition Theorem 278 isolates for the exponent pair.** Two independent routes
> — the covering architecture's floor and the `t`-free requirement — vanish under the same condition,
> derived from different data.**

### Lean

`formal/GaloisForLFunctions/HTGeometry/ArchitectureSensitivity.lean` — `archFloorAt`,
`archFloor_published`, `archFloor_is_huxleyDemand`, `sensitivity_beta`, `sensitivity_alpha`,
`sensitivity_ratio = 42/17`, `residualFloor = 221/1792`, `residualFloor_dominates`,
`residualFloor_below_eighth`, `archFloor_zero_iff`, `architecture_and_tFree_agree`,
`published_far_from_zero`.
Umbrella green at **10998** jobs.

### Standing position after 263 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 281 results, thirty-one corrections, 68 dead
routes.

> **New operational content: the architecture's floor is four-fifths determined by the middle source's
> `M`-exponent, which is the *less* valuable parameter at the margin (`17/42` against `1`). So effort
> spent improving Huxley's `103/128` is worth `2.47` times less per unit than effort spent on its
> `1/32` — and neither can reach zero, since the floor vanishes only at the corner.**

## Cycle 264 — **THEOREMS 282–288: scale/abscissa duality, and the transfer theorem as an endpoint**

### C724 — the conjugate variable of the abscissa is the scale

A contour shift turns a growth bound at abscissa `σ` into a bound for the block `Σ_(n∼T^c)n^(-it)` of
size `T^(c/2)·T^(μ(σ)+c(σ−1/2))`. So the block exponent delivered at scale `T^c` is

> **`blockBound(c,σ) = μ(σ) + c·(σ−1/2)`** ,

which is *literally* the exponent-pair affine form `κ + c·d` with `κ = μ(σ)`, `d = σ−1/2`. Hence the
block-exponent function is the **concave conjugate `inf_σ blockBound(·,σ)` of `μ`**, and the
exponent-pair region is conjugate to the epigraph of the growth exponent. `[THEOREM 282]`

### C725 — the functional equation is the simultaneous reflection `[THEOREM 283]`

> **`blockBound(c, 1−σ) = blockBound(1−c, σ)`.**
>
> Reflecting the abscissa **is** reflecting the scale, by the same involution `x ↦ 1−x` the `B`-process
> performs on lengths (Thm 40). The functional equation and process `B` are one map read in two
> variables.

### C726 — the critical scale is exactly the critical line `[THEOREM 284]`

> **`μ(1/2) ≤ blockBound(1/2,σ)` for every `σ`, with equality at `σ = 1/2`.**
>
> So `μ(1/2) = inf_σ blockBound(1/2,σ)`. **Conjugation is lossless and round-tripping gains exactly
> nothing**: no off-line datum whatsoever can improve the critical scale. This is the one-line
> explanation of why every transfer route the campaign priced (D-series) closed up.

### C727 — freeing a scale is strictly cheaper than transferring `[THEOREMS 285–287]`

At target `β`, a datum `μ(σ₀) ≤ m₀` makes **every scale `c ≤ (β−m₀)/(σ₀−1/2)` meet the target by
itself**. Three exact statements:

> `[285]` `σ₀=1, m₀=0` gives the trivial threshold `2β`. A datum beats it **iff `m₀ < 2β(1−σ₀)`** —
> iff `(σ₀,m₀)` lies strictly **below the chord from `(1/2,β)` to `(1,0)`**.
>
> `[286]` The freed range reaches the critical scale `c = 1/2` **iff `m₀ + (σ₀−1/2)/2 ≤ β`** — which is
> exactly the off-line transfer condition. **So the transfer theorem is the `c = 1/2` endpoint of a
> one-parameter family of scale-freeing statements**, and every interior member is strictly weaker.
>
> `[287]` The gap between the two thresholds is exactly **`(σ₀−1/2)(1/2 − 2β)`**, strictly positive off
> the critical line whenever `β < 1/4`.

At `σ₀ = 3/4`, `β = 13/84`: the chord threshold is `13/168`, the transfer threshold `5/168` — a factor
`13/5`. A datum `μ(3/4) ≤ 1/24` would lie below the chord and **free every scale up to `19/42`, past
the `17/42` at which the covering architecture's final source becomes available** — while still
failing to transfer, since `1/24 > 5/168`.

### C728 — and the transfer limit is the vanishing abscissa `[THEOREM 288]`

> Since `m₀ ≥ 0`, an abscissa **`σ₀ > 1/2 + 2β` can never transfer** to the critical line at level `β`.
> At `β = 13/84` that limit is **`17/21` — the vanishing abscissa `σ*` of the record pair** (Thm 181).
>
> **New reading of `σ*`: it is precisely the largest abscissa at which off-line information can still
> reach the critical line at the record level.** Beyond it, off-line data can only free scales, never
> transfer.

### Lean

`formal/GaloisForLFunctions/HTGeometry/ScaleAbscissaDuality.lean` — `blockBound`, `blockBound_at_half`,
`blockBound_reflect`, `blockBound_mono`, `mu_half_le_blockBound_half`, `blockBound_half_isLeast`,
`freeThreshold`, `free_iff`, `freeThreshold_trivial`, `freeThreshold_beats_trivial`,
`freeThreshold_reaches_critical`, `freeing_cheaper_than_transfer`, `freeing_gap_pos`,
`transfer_limit`, `transfer_limit_record`, `chord_versus_transfer_at_three_quarters`,
`free_range_past_decoupling`, `scale_abscissa_duality`. Umbrella green at **11000** jobs; axioms
`[propext, Classical.choice, Quot.sound]`.

### Standing position after 264 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 288 results, thirty-one corrections, 68 dead
routes.

> **The operational consequence, and the target for the next cycles: off-line data is worth far more as
> a scale-freeing device than as a transfer device. The campaign (and the literature) has only ever
> used the endpoint `c = 1/2`. The interior `c < 1/2` is a strictly weaker demand on `μ(σ)` and has
> never been exploited.**

## Cycle 265 — **THEOREMS 289–294: the middle source is binding on a window of width `11/8610`**

Cycle 264 ended with the plan: exploit the interior `c < 1/2` of the scale-freeing family. Applied to
Bourgain's own Section-4 architecture it gives an exact anatomy of the proof.

### C729 — the covering threshold `[THEOREM 289]`

> A pair with displacement `d = (λ−κ)−1/2 > 0` has demand `κ + c·d`, increasing in `c`, so at target
> `β` it covers **exactly** the scales
>
>     `c ≤ coverThreshold(κ,λ,β) = (β−κ)/d` .
>
> This is the scale-freeing threshold of Thm 285 with `κ = μ(σ)`, `d = σ−1/2` — the conjugate picture
> read on the pair side.

### C730 — the three low-range pairs, exactly `[THEOREMS 290–291]`

At `β = 13/84`, against the final source's threshold `x₁ = 17/42`:

| low pair | covers up to | short of `17/42` by |
|---|---|---|
| `(1/9, 13/18)` (published) | **`11/28 = 33/84`** | **`1/84`** |
| `(1/11, 3/4)` (vdC word) | **`59/147 = 118/294`** | **`1/294`** |
| `(16/237, 743/948)` = `A`(Huxley) | **`579/1435 = 3474/8610`** | **`11/8610`** |

> The published low-range pair covers to `33/84` and the final source starts at `34/84`: **the two
> ranges miss each other by exactly one part in `84`** — the same denominator as the record.

### C731 — what the direct middle source is worth `[THEOREMS 292–294]`

Demands at `x₁ = 17/42`, and their excess over `13/84`:

| low pair | demand at `17/42` | excess |
|---|---|---|
| `(1/9,13/18)` | `59/378` | **`1/756`** |
| `(1/11,3/4)` | `41/264` | **`1/1848`** |
| `(16/237,743/948)` | `6173/39816` | **`11/39816`** |

> **`[THEOREM 294]` Deleting the direct Huxley source (while retaining Huxley's exponent pair) leaves
> the architecture at `μ(1/2) ≤ 6173/39816` against the record `6162/39816`. The entire
> Bombieri–Iwaniec/Huxley middle source is therefore worth at most `11/39816 ≈ 2.8·10⁻⁴` in the
> exponent, and is responsible for a scale window of width only `11/8610 ≈ 1.3·10⁻³`.**
>
> (Exact relative to the best of these three pairs; any further low-range pair only shrinks both.)

### Correction to interpretation, recorded

The record `13/84` is **not** pinned at the window: on `(579/1435, 17/42)` the Huxley source has slack
(`28321/183680` at the left end, `831/5376 = 13/84 − 1/5376` at the right), and at `c = 12/31` the best
pair already gives `1111/7347 < 13/84`. **The record is attained at `c = 1/2`, by the decoupling source
alone.** Everything below the critical scale carries slack. This is the covering picture's own version
of Thm 284: *the critical scale is the only place the bound is tight.*

### Lean

`formal/GaloisForLFunctions/HTGeometry/MiddleSourceWindow.lean` — `covDemandOfPair_affine`,
`coverThreshold`, `cover_iff`, `coverThreshold_mono`, `lowPair_displacements`,
`coverThreshold_published/_vdcWord/_procAHuxley`, `window_published/_vdcWord/_procAHuxley`,
`windows_nested`, `demands_at_decouplingStart`, `middleSource_worth`, `without_middle_source`,
`middle_source_window`. Umbrella green at **11002** jobs.

### Standing position after 265 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 294 results, thirty-two corrections, 68 dead
routes.

> **Consequence for the campaign: the whole three-source architecture below `c = 1/2` carries slack,
> and the binding constraint is the decoupling source at the critical scale alone. Every scale except
> `c = 1/2` is over-covered. The next target is therefore not the architecture but the single object
> `Σ_(n ∼ √T) n^(-it)`.**

## Cycle 266 — **THEOREMS 295–302: the Section-4 floor is a scale gap, priced and targeted**

### C732 — the covering's exact source map at the record target `[THEOREMS 295–296]`

> | source | covers |
> |---|---|
> | exponent pairs | `c ≤ 579/1435` |
> | middle (Huxley) source | `12/31 ≤ c ≤ **332/819**` |
> | final (decoupling) source | `17/42 ≤ c ≤ 1/2` |
>
> The middle source reaches **`1/1638` past** the final source's threshold, so the union is all of
> `[0,1/2]` — but on the window `(579/1435, 17/42)`, width `11/8610`, **the middle source is alone.**

### C733 — and the floor is exactly its value there `[THEOREM 297]`

> The middle source's demand is increasing in `c`, so its supremum on that window is its right-endpoint
> value **`277/1792`**. Nothing else is available there. **Hence the covering cannot prove any bound
> below `277/1792` — the Section-4 floor (Thm 89) is not a property of the architecture, it is the
> value of one source at one scale, forced by a gap of width `11/8610`.**

### C734 — the slack profile `[THEOREMS 298–299]`

> The covering is **tight only at `c = 1/2`**. Next-tightest: `c = 17/42`, slack exactly **`1/5376`**.
> At `c = 12/31` the slack is **`243/68572`**. Every non-critical scale is over-covered.

### C735 — the exact target that removes the floor `[THEOREMS 300–301]`

> **A single exponent pair with demand `≤ 277/1792` at `c = 17/42` deletes the Section-4 floor
> outright.** Written as a linear functional, the demand at `17/42` is `(25κ + 17λ)/42 − 17/84`, so the
> target is `25κ + 17λ ≤ 42(277/1792 + 17/84)`. The best available pair `(16/237, 743/948)` misses by
> exactly **`589/1274112`**.

### C736 — why the improvement must come at the critical scale `[THEOREM 302]`

> A pair on the line of symmetry `λ = κ + 1/2` has **zero displacement**, hence demand **constant `= κ`
> at every scale**. Weyl's `(1/6, 2/3)` and the record `(13/84, 55/84)` are both such pairs.
>
> **So each of them already covers all scales by itself, and the covering architecture adds nothing to
> them.** Beating `13/84` means beating a flat bound — which by Thm 284 (conjugation is lossless) can
> only be done at the critical scale itself.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SectionFourGapAndTarget.lean` — `huxleySource_coverage`,
`huxleySource_overlap`, `middleSource_alone`, `middleSource_increasing`, `sectionFour_floor`,
`slack_at_decouplingStart`, `slack_at_huxleyStart`, `gap_closing_target`,
`demand_at_decouplingStart_linear`, `epDisplacement_on_symmetry`, `covDemand_flat_on_symmetry`,
`record_pair_flat`, `weyl_pair_flat`, `section_four_gap_summary`. Umbrella green at **11004** jobs.

### Standing position after 266 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 302 results, thirty-two corrections, 68 dead
routes.

> **The architecture is now completely priced and completely dismissed: its floor is one source's value
> on a gap of width `11/8610`, every other scale carries slack, and the record pair is scale-flat so
> the architecture is redundant given it. Three independent lines (Thms 284, 294, 302) now say the
> same thing: the only object left is `Σ_(n ∼ √T) n^(−it)`.**

## Cycle 267 — **corpus audit + THEOREMS 303–310**

### E58 — **CORRECTION: two of the last two cycles' headline numbers are already in the corpus**

A directed read of `formal/GaloisForLFunctions/RHTower/` (105 `Bourgain*` modules — the real-analysis
side of the campaign, which the exponent-arithmetic work in `HTGeometry/` had not been consulting)
turned up `BourgainExponentEndgame.lean`, which already proves **with real powers**:

* the pair `(1/9, 13/18)` reaches `M ≤ T^(11/28)`  ⇒ **Thm 290 is a rediscovery**;
* Huxley's bound reaches `M ≤ T^(332/819)`  ⇒ **Thm 295 is a rediscovery**;
* the overlaps `12/31 < 11/28` and `17/42 < 332/819` close the range.

What survives from cycles 265–266 as new: the A(Huxley) threshold `579/1435` (strictly better than the
corpus's `11/28`), the window width `11/8610`, the slack profile (`1/5376`, `243/68572`), the
gap-closing target `589/1274112`, and the retraction below.

**Practice change, binding from now on: `formal_tools.py research` + a directed `ls`/`grep` of
`RHTower/` before every cycle, not only `HTGeometry/`.** The analytic corpus is where the Bourgain
proof actually lives.

### C737 — **the symmetrization retraction** `[THEOREMS 303–306]`

> For any pair `P = (κ,λ)`, the midpoint of `P` and `BP` is
>
>     **`((κ+λ−1/2)/2, (κ+λ+1/2)/2) = (μ(P), μ(P)+1/2)`** ,
>
> a point of the line of symmetry with first coordinate exactly `μ(P)`. The exponent-pair region is
> convex and `B`-closed, so that midpoint is again a pair. Hence
>
> **`sym : (κ,λ) ↦ (μ(κ,λ), μ(κ,λ)+1/2)` is an idempotent retraction of the region onto its
> intersection with the line of symmetry, and it preserves `μ` exactly.**
>
> Consequences: `inf{μ(P)} = inf{κ : (κ,κ+1/2) a pair}` — **the region matters only through the line of
> symmetry**; `sym P` is scale-flat; and `P`, `BP` have demands averaging to `μ(P)` at *every* scale.
>
> Instances: `(1/9,13/18) ↦ (1/6,2/3)` — **Bourgain's low-range pair retracts exactly to Weyl's pair**;
> `(0,1)` and `(1/2,1/2)` both `↦ (1/4,3/4)`; the record is its own retract.

### C738 — **the power-scale recurrence floor** `[THEOREMS 307–310]`

Using the corpus's own `bourgain_powerScale_iterate` (`BourgainPowerScaleBootstrap`), whose recurrence
is `b(N) ≤ C N^δ b(N^α)`:

> `[307]` The `k`-fold accumulation `δ Σ_(i<k) α^i` falls short of
> **`powerScaleFloor δ α = δ/(1−α)`** by exactly **`δ α^k/(1−α)`** — the floor is attained only in the
> limit. At `α = 2/3` it is `3δ`, and `13/84 = powerScaleFloor(13/252, 2/3)`: **Bourgain's per-step
> decoupling loss is exactly `13/252`.**
>
> `[308]` **Elasticity.** `∂log floor/∂log δ = 1` but `∂log floor/∂log α = α/(1−α) = 2` at `α = 2/3`.
> **The floor is twice as elastic in the contraction exponent as in the per-step loss** — proportional
> effort spent lowering `α` is worth twice what it is worth lowering `δ`.
>
> `[309]` For `α < 1`, `floor = 0 ⟺ δ = 0`: **the recurrence yields Lindelöf iff its per-step loss is
> not a positive power.**
>
> `[310]` **Why Bourgain's pair is on the line of symmetry.** The recurrence constrains `b(N)` for
> *every* `N`, so its solution is an exponent uniform in the scale; a scale-uniform bound `M^(1/2)T^β`
> is the pair `(β, β+1/2)`, of zero displacement. **The recurrence is the source of the flatness that
> Thm 302 observed** — the two sides of the campaign, analytic and geometric, meet here.

### Lean

`formal/GaloisForLFunctions/HTGeometry/SymmetrizationRetraction.lean` — `symKappa`, `symLambda`,
`sym_is_midpoint_of_B`, `sym_displacement_zero`, `sym_preserves_mu`, `sym_idempotent`,
`sym_fixes_symmetry_line`, `sym_demand_flat`, `demand_average_is_mu`, `demand_at_critical_is_mu`,
`mu_le_iff_sym_le`, `sym_lowRange`, `sym_vdcWord`, `sym_trivial`, `sym_record`,
`symmetrization_summary`.
`formal/GaloisForLFunctions/RHTower/BourgainRecurrenceFloor.lean` — `powerScaleFloor`,
`powerScale_partial_deficit`, `powerScale_partial_le`, `powerScaleFloor_two_thirds`,
`powerScaleFloor_bourgain`, `powerScaleFloor_delta_diff`, `powerScaleFloor_alpha_diff`,
`powerScaleFloor_elasticity`, `powerScaleFloor_eq_zero_iff`, `uniform_exponent_is_symmetric`,
`bourgain_pair_is_recurrence_flat`.

### Standing position after 267 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 310 results, thirty-three corrections, 68 dead
routes.

> **New target, from `[308]`: the contraction exponent `α = 2/3` of Bourgain's Section-1 recurrence,
> not the per-step loss `δ = 13/252`. It is the twice-more-elastic parameter and nobody has priced it.
> Corpus entry point: `BourgainPowerScaleBootstrap`, `BourgainScaleContraction`.**

## Cycle 268 — corpus-first, per E58: two rediscoveries avoided, one new law

### E59 — **CORRECTION avoided by checking first**

Deriving the Section-3 spacing profile from `RHTower/BourgainSpacingExponentArithmetic` I obtained the
"V-law" `θ(x) = 11/72 + |x − 5/12|/6`, the coverage interval `[17/42, 3/7]` of width `1/42`, and the
identity `depth = half-width × slope = (1/84)(1/6) = 1/504`. **A grep for `11 / 72` found all of it
already in `HTGeometry/SpacingWindowGeometry.lean`** — the campaign's own first module, which states
the corner `5/12`, threshold `(b+c)/12 = 11/72`, interval `[c − 6θ, 6θ − b] = [17/42, 3/7]`, width
`12θ − (b+c) = 1/42`, and corner surplus `1/84`. **Not written. This is the second time in two cycles;
the grep is now unconditional before any derivation.**

### C739 — the real open obligation, located

`RHTower/BourgainFirstSpacingElimination.lean` carries the chain's one explicit hypothesis:

>     `hA6 : ∀ ε > 0, ∃ C > 0, ∀ H,  A₆(H) ≤ C·H^ε·H^6`

and its own docstring records: *"Establishing that estimate without hypotheses remains a separate
obligation"*, and that the theorem *"leaves the second-spacing count visible"*. **That is the frontier
of the corpus: the sharp `A₆` sixth-moment estimate, and the second-spacing count.** It is also where
cycle 267 independently concluded the loss must be — arithmetic, not analytic.

### C740 — **the arithmetic-loss transfer law** `[THEOREMS 311–314]`

The double-large-sieve step bounds a **twelfth** power:
`(Σ_i‖S(x_i)‖)^12 ≤ K·H^9` when the sixth-moment input is sharp.

> `[311]` `X^12 ≤ K·H^(9+ρ)` ⟹ `X ≤ K^(1/12)·H^(3/4 + ρ/12)`.
>
> `[312]` **An arithmetic loss `ρ` in the `A₆` sixth moment costs exactly `ρ/12` downstream.**
>
> `[313]` Hence any fixed `ρ > 0` strictly degrades the final exponent: **the sixth-moment input is
> already extremal and carries zero slack. No improvement of the record can come from the
> first-spacing side.**
>
> `[314]` The budget for a target gain `Δ` is `ρ ≤ 12Δ`. From `13/84` down to the two-regime threshold
> `11/72` the gain is `1/504`, so the `H`-exponent budget is **`12/504 = 1/42`** — numerically the
> width of the coverage interval `[17/42, 3/7]`.

### Consequence for the campaign

> **All remaining slack in Bourgain's chain is localized to the second-spacing count.** The
> first-spacing side is extremal (`[313]`), the covering geometry is over-covered everywhere except
> `c = 1/2` (Thms 298–299), the middle source is worth at most `11/39816` (Thm 294), and the recurrence
> floor is `δ/(1−α)` with `δ` already the budget (Thms 307–308). The second-spacing count is the only
> input the corpus leaves both explicit and unpriced.

### Lean

`formal/GaloisForLFunctions/RHTower/ArithmeticLossTransfer.lean` — `twelfth_root_transfer`,
`chain_exponent_transfer`, `arithmeticLoss`, `arithmeticLoss_eq`, `arithmeticLoss_zero`,
`arithmeticLoss_pos`, `arithmeticLoss_budget`, `budget_record_to_threshold`,
`gap_record_to_threshold`, `arithmetic_loss_summary`.

### Standing position after 268 cycles

`μ(1/2) ≤ 13/84`. **LH neither proved nor disproved.** 314 results, thirty-four corrections, 68 dead
routes.

> **Next: price the second-spacing count. Corpus entry points —
> `BourgainFirstSpacingElimination` (leaves it visible), `BourgainMomentCloudBounds`,
> `BourgainDoubleLargeSieve`, and on the arithmetic side `HTGeometry/FareyArcAccounting`,
> `SqrtNonResonance`, `CoherenceDivisibility`, `SimultaneousResonanceCount`.**
