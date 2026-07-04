# 77 — The Relay Tier: the Half-Law, the Survival-Channel Discrepancy, and the Signed Ledger

**Register: SEARCH, with the §1 core at promotion grade** (task #23; doc 76 §6
force order). §1 derives the two-level relay rate from banked pieces — the
half-law is exact and parameter-free. §2 pre-registers the null-model check
(binds, written before the run; results appended §4). §3 is the
survival-channel discrepancy write-out with its honest boundary. §5 the
signed relay ledger (Lean: RelayLedger.lean). §6 what opens.

## 1. The two-level relay rate: the half-law [derivation from PROVED parts]

**The signed walk is exact and already banked.** At fixed height t\*, entry
n+1 moves the pair's SIGNED squared depth by one real number:

> D_{n+1} = D_n + q_{n+1},  q_{n+1} = a_{n+1}·cos φ_{n+1}(t\*),
> a_{n+1} = 2(n+1)^{−1/2}/‖g‖ > 0,  φ_{n+1} = θ(t\*) − t\*·log(n+1),

and the configuration is read off the sign — D > 0: off-line conjugate pair
at ±i√D; D ≤ 0: on-line pair at ±√(−D). This is not a model: it is the
literal zero motion, machine-checked (`DepthUpdate.lean`:
`quadratic_pair_zeros_pos` / `quadratic_pair_zeros_nonpos`, both signs), on
doc 48 §2's exact dichotomy. Absorption and relay are the SAME walker
crossing 0 — the probe's "deaths are 100% absorption, relays at 18–128× the
spontaneous-birth baseline" (doc 76 §5) is this walker seen through a
detector that only reported the D > 0 side.

**Two-level relay criterion [exact].** An on-line pair with D_n = −v₀² ≤ 0
relays (lifts off) at entry n+1 iff

> v₀² < a_{n+1}·cos φ_{n+1}(t\*)

— doc 48 §2's reverse dichotomy, verbatim, in the signed coordinate.

**The half-law [PROVED HERE — one line, parameter-free].** For x ∈ [0, 1],
meas{φ ∈ [0, 2π) : cos φ > x} = 2·arccos(x); hence under phase
equidistribution (§3) the one-entry relay probability of a pair at
overshoot ratio x = v₀²/a is

> P₁(x) = arccos(x)/π,  P₁(0) = **1/2**.

The ½ needs no lattice input, no envelope input, no height input: it is the
measure of a half-circle. A freshly absorbed pair has overshoot
v₀² = |D_{n−1} + q_n| ≤ a_n (the overshoot cannot exceed the killing step),
so x ∈ [0, 1] automatically, and shallow-at-death pairs sit at x ≪ 1, i.e.
at P₁ ≈ ½. The measured relay rate 0.46–0.56 (within ≤ 3 levels, doc 76 §5)
is this half-law plus the overshoot correction (lowers P₁) plus the two
extra chances (raise it back); §2/§4 check that the net lands where measured.

**Frozen-lattice form.** On the lattice the phases are deterministic,
φ advancing by ϑ = π(1 + 4p) per entry; the half-law survives verbatim
because {β : cos(β + mϑ) > 0} has measure π for EVERY m and ϑ — the ½ is
per-step exact in the birth phase β, not an ensemble artifact. What the
lattice adds is the RECURRENCE structure: on the frozen circle the partial
sums oscillate with period 2π/ϑ, so a down-crossing is followed by an
up-crossing within one wrap ⌈2π/ϑ⌉ unless the envelope/drift moves first —
relay chains are the wrap structure of doc 51 §2 read on both sides of the
barrier.

**What this changes in the accounting.** The relay is not an alignment
anomaly to explain away; it is forced by the exact dichotomy at rate ~½.
The object with a right to die is the CHAIN (walker + its recrossings), and
the sub-criticality measured for ζ (geometric chain tails, N-uniform,
doc 76 §5) against the super-criticality at D–H zeros is the entire
remaining content of (XLD). The half-law converts (XLD) from "creation
events decorrelate" to a sharper split:

- per-step relay rate = ½ + O(x) + O(D_L) — PROVABLE (this section + §3);
- chain SUB-criticality — i.e. the walk at a fixed mid-band height has no
  conspiracy holding D > 0 (or regenerating it indefinitely) across the
  domination window — OPEN, Euler-specific, = (XLD) proper.

## 2. Pre-registered null checks [written BEFORE the run; these bind]

MC (mc_relay_null.py, runpod): (a) iid null — walk D ← D + cos U, U iid
uniform; at every down-crossing of 0, record whether the walk recrosses
within ≤ 3 steps; ≥ 10⁶ crossings. (b) lattice null — steps cos(β + mϑ),
β uniform, ϑ = π(1+4p), p uniform; same statistic. (c) envelope variant —
a_m = (1 − m/(3N))^{−1/2} slow growth, same statistic.

- **P-R1:** the iid-null 3-step recross rate lands in [0.40, 0.60] —
  bracketing the measured ζ relay rates 0.46–0.56: the relay channel is
  EXPLAINED by the signed-walk null; no residual alignment needed.
- **P-R2:** the lattice-null rate differs from the iid-null rate by ≤ 0.05
  (the half-law is lattice-independent; wrap recurrence only matters past
  3 steps).
- **P-R3:** one-step recross rates match E[arccos(V)/π] computed from each
  run's own overshoot sample to ≤ 0.01 (internal consistency of §1's
  formula).

Failure semantics: P-R1 failing low (null ≪ measured) would mean the ζ
carrier relays MORE than its own walk allows — real cross-level alignment
beyond the dichotomy, and (XLD) would need strengthening even for the
sub-critical claim. P-R1 failing high means the probe's ≤3-level window
undercounts; recalibrate before any use of the 0.46–0.56 numbers.

## 3. The survival channel: (SURV-EQ), the discrepancy write-out

**Claim to be proved (window-averaged phase-neutrality).** Fix
t\* = 2π(N+p)². Doc 49 §2 [PROVED there — Taylor with explicit error]:
for offset m = N − n ≤ M,

> φ_{N−m}(t\*) ≡ φ_N(t\*) − 4πp·m − π·m² (mod 2π),
> error O((m³ + pm² + p²m)/N).

In units of 2π, with u_m = φ_{N−m}/2π mod 1: πm² mod 2π = π·(m mod 2), so

> u_m = u_0 − 2pm − ½·[m odd] (mod 1)

— **two arithmetic progressions** (even/odd offsets) of common difference
‖4p‖, displaced by ½. The survival-relevant events are phase sets of
bounded complexity: for a valley of margin c the one-entry survival
indicator is 1{a cos(φ + const) > −c}, a union of ≤ 2 arcs, total variation
≤ 4. Koksma's inequality then gives, for any window of L consecutive
levels,

> |empirical survival rate − P_null| ≤ 4·D_L,

with D_L the discrepancy of {u_m}_{m<L}. The discrepancy splits:

1. **AP regime** [CLASSICAL — Erdős–Turán / three-distance]: for
   ‖4p‖ ≥ L₀/L, each parity class is an AP mod 1;
   D_L ≪ (log L)/(L·‖4p‖) + ‖4p‖. Generic p: D_L ~ log L/L.
2. **Coherent exceptions** p ≈ ¼, ¾ (‖4p‖ small — doc 49 §2(2)'s in-phase
   points): the pure lattice does NOT equidistribute; rescue is the
   certified cubic drift (doc 50 §4: accumulated phase 2πm³/(3N)) — over
   m ~ N^{1/3} the effective p sweeps O(1), and Weyl differencing on the
   cubic gives D_L → 0 on the L ~ N^{1/3} scale [CLASSICAL-shaped,
   bookkeeping not done here].
3. **Expansion error** [PROVED, doc 49 §2]: O(L³/N) — harmless for
   L ≤ N^{1/3−ε}, and the m ~ N^{1/3} boundary is exactly the (DRIFT-dip)
   clock, as it must be.

So: **on windows up to the drift clock, the window-averaged one-entry
survival (and relay) rates equal the uniform-phase null to
O(log L/L + L³/N)** — no zero-density input, no Euler input, elementary +
classical technology on top of the proved lattice. This is the provable
face of doc 76's P-X2 (measured: null to ≤ 6%).

**The honest boundary — where (XLD) actually lives.** (SURV-EQ) is a
WINDOW-AVERAGED statement. It does not give the pointwise conditional
P(C_{n+1} | C_n) = null: conditioning on the event configuration can in
principle bias the phase subsequence the events see. And it CANNOT be
otherwise at this level: D–H's truncation phases satisfy the SAME lattice
expansion and the same discrepancy bounds — its conspiracy at off-line
zeros is carried by the amplitude/sign pattern of its coefficients against
the phases (the remaining terms sum to restore D), not by a failure of
phase equidistribution. The discriminator therefore sits exactly one level
up: whether the walk INCREMENTS are conditionally unbiased given the
walk's own past at that height. That conditional statement is (XLD) proper;
(SURV-EQ) fences it to a single, sharply-typed residue.

## 4. Null-check results [appended after the run]

## 5. The signed relay ledger (Lean upgrade)

`RelayLedger.lean` (this cycle): the ledger's binary alive/dead walk
replaced by the signed depth walk; excursions and upcrossings become the
native objects; the relay re-cut of doc 76 §2 becomes a theorem schema:

- signed prefix depths over the push list (both signs legal — the walk
  continues through the barrier, as `DepthUpdate` licenses);
- `upcrossAt` / off-line runs; first-passage lemmas both directions;
- **excursion bound consumes ephemerality**: hypothesis (EXC-ℓ) = every
  upcrossing re-absorbs within ℓ entries; theorem: every maximal off-line
  run has length ≤ ℓ — so continuous forced presence over J > ℓ levels is
  impossible;
- **relay counting consumes the budget**: presence at k+1 levels pairwise
  more than ℓ apart forces ≥ k upcrossings; with an upcrossing budget R,
  presence cannot spread past (R+1) blocks — the formal consumption point
  for (CR-density) × (XLD) sub-criticality;
- compatibility: the old `SurvivesFrom` is exactly "off-line at every
  prefix", tying the new ledger to `SweepCascade`.

Deep-enough putative pairs (η above the AFE error across the window) force
CONTINUOUS presence — one excursion of length J — so for them the excursion
bound alone contradicts, no relay counting needed; the chain accounting is
only for the marginal regime η ~ AFE error. This matches the D–H probe's
depth split (deep zeros: window-covering presence; shallow: frayed runs).
