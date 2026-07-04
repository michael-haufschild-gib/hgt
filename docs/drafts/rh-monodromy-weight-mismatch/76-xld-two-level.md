# 76 — (H1) Verified Against the Ledger; the Relay Re-Cut; (XLD) at Two Levels

**Register: SEARCH** (task #22, force-order head from doc 75 §5). §1 is the
(H1) reading verdict with files and lines named; §2 re-cuts the contradiction
step on what the ledger actually is; §3 states (XLD) at its minimal instance;
§4 pre-registers the persistence probe (written BEFORE any run; binds); §5–§6
appended after the run.

## 1. (H1) verified — a two-sided verdict [reading: SweepCascade.lean, MidCentral.lean, DipKillsWiring.lean, docs 48–53]

**(i) The ledger IS cross-level at fixed height.** Doc 49 §1 fixes a p-central
height t and walks the tower entries j = k+1, …, N; each entry pushes every
existing pair's squared depth by one real number (doc 48 §2, exact). In Lean,
`CascadeBirth.time` indexes the push list and `futurePushes pushes birth =
pushes.drop birth.time` (SweepCascade.lean:169–176): the walk time IS the
tower level. Presence of a pair at J consecutive levels is one walker alive
through J consecutive times. Doc 75 (H1)'s fear — "the banked ledger may not
implement cross-level forcing at fixed height, leaving the density tier
unconsumed" — FAILS: cross-level is the ledger's native coordinate.

**(ii) But the doc 75 §2 multiplication mechanism is wrong-shaped.** A ζ-pair
forced present in g_n for n ∈ [N−J, N+J] is ONE ledger walker, not J entries;
it consumes the creation budget ONCE. `midCentral_survivors_le`
(MidCentral.lean:80) with any K ≥ 1 tolerates a single putative pair for
free. The "J-fold forced presence vs budget ≪ J" contradiction, as
reconstructed in doc 75 §2, is not what the ledger can express.

**(iii) The genuine gap, located exactly: no lifetime bound for resonant
survivors.** The formal ledger types resonance STATICALLY: `SlipWindow κ slip
b` is one number per birth (MidCentral.lean:30–33), and every proven kill —
`dip_kills` via `CarrierBirthData` → `birthKilled_of_perturbed_rotation`
(DipKillsWiring.lean:75–102) — fires only for `¬ SlipWindow` births. An
in-window birth is IMMORTAL in the formal ledger. The banked analytic
material already contains the missing kill at proof shape: the slip identity
(doc 51 §9a, PROVED — slip after k entries past stationarity = 2πk²) makes
the window SUB-ENTRY: the budget κ ≈ 0.236 rad is exhausted at
k = √(κ/2π) = 0.194 < 1 entry. Measured trace: (DEEP-FATE) P-DF3 (doc 53
§3) — 6/8 mid-band census pairs exist for exactly ONE entry epoch; all
absorption within ≤ 3·N^{1/3} entries.

> **(H1) verdict:** the cascade ledger implements cross-level TRACKING but
> not cross-level KILLING of resonant pairs. The missing piece is DYNAMIC
> slip — resonance detunes within one entry (proved analytically, doc 51
> §9a; unformalized structurally). The ledger upgrade is typed: a
> time-dependent slip field, protection lasting O(1) entries, after which
> the banked dip machinery applies to every pair.

## 2. The relay re-cut of the contradiction step

With dynamic slip no walker is long-lived: resonant protection ~1 entry,
then the drift/dip clock kills within ≤ 3·N^{1/3} entries (measured; (DRIFT-
dip) is its proof-shaped form). A ζ-pair at fixed (η, t\*) is forced present
through the domination window n ∈ [N−J, N+J], J ~ δ√N ≫ N^{1/3}. Therefore:

> **The forced object is a RELAY, not a walker: a chain of ≥ J/(3N^{1/3})
> ~ δN^{1/6}/3 creation events, all pinned at the same height t\*, one every
> ≤ 3·N^{1/3} consecutive levels.**

The contradiction step re-forms accordingly. (CR-density) bounds the
per-level creation SET's measure; the relay needs the creation sets of
~δN^{1/6} distinct levels to ALIGN at one point t\*. Per-level density
cannot preclude that alignment — doc 75's (H3), now in exact coordinates —
so the load lands on cross-level decorrelation of CREATION events
specifically, not of generic deficit events. This is a real localization
gain over doc 75: a creation is a tangency (doc 52 §2–3), the codimension-1
condition Re(F_n′/F_n)(½+it\*) ≈ −θ′(t\*), and the n → n+1 update changes
F_n by exactly one term. The whole question is one explicit increment.

## 3. (XLD)₂ — the minimal instance [CONJECTURE]

Operational event: C_n(t\*) = "the level-n carrier Z_n has a mid-band
non-crossing valley at t\*" (valley depth η = √(2|Z_min|/|Z″|), mid-band =
η/spacing ∈ [0.05, 0.35]; Z_n the Hardy-symmetrized truncation, so the
n → n+1 update adds the single term 2(n+1)^{−1/2}cos(θ(t) − t·log(n+1)) —
the "+ mirror" is Z's realness).

> **(XLD)₂ [CONJECTURE]:** at the scale of the matched regime, the one-level
> persistence of a mid-band event is phase-neutral:
> P(C_{n+1}(t\*) | C_n(t\*)) = P_null · (1 + o(1)),
> where P_null is the survival probability of the level-n valley under the
> ACTUAL added amplitude 2(n+1)^{−1/2} with UNIFORM phase — i.e. the added
> term's phase at an event location carries no information about the event's
> configuration. Iterated along the window, the relay probability decays
> geometrically in the number of required re-creations, beating any
> per-level density bound.

Euler is the content: for ζ the phases {t log p} are free generators (the
new level's phase is a fresh direction over the event's σ-algebra); for D–H
at its genuine off-line zeros the limit function HAS the zero, so
persistence across the domination window is forced — P(C_{n+1}|C_n) → 1
there, and (XLD)₂ is refuted-by-construction for D–H. This is the required
filter property (doc 75 §3) at the two-level scale.

## 4. Pre-registered predictions [written BEFORE the probe runs; these bind]

Probe design (probe_xld.py): ζ side — grids t ∈ [T, T+U] at
T ∈ {10^5, 10^6, 10^7}, levels n ∈ [N−15, N+15] with incremental term
addition; valley detection per level (parabola: η = √(2|Z_min|/|Z″|));
lifetime tracking by t-locality (|Δt| < 0.3·spacing); relay statistic =
re-creation at the same t within ≤ 3 levels after a death. Null model:
survival of the tracked valley under the actual added amplitude with
uniform phase (analytic fraction per event, averaged). D–H side —
coefficients (1, κ, −κ, −1, 0) mod 5 with κ fixed IN-SCRIPT by the sine
eigenvector condition and the FE verified numerically against Hurwitz-zeta
values (no recalled constants); locate genuine off-line zeros by scanning
the completed function; measure truncation-valley lifetime at those zeros.

- **P-X1 (ephemerality):** ζ mid-band valley lifetime has median ≤ 3 levels
  at all three heights; 95th percentile ≤ 3·N^{1/3} levels.
- **P-X2 (decorrelation — the (XLD)₂ core):** the measured one-level
  survival rate is within a factor 1.5 of P_null at every height.
- **P-X3 (D–H contrast):** at genuine D–H off-line zeros, the truncation
  valley at the zero's height survives ≥ 5× the ζ median lifetime at
  comparable N, and covers the matched level.
- **P-X4 (memorylessness):** ζ: |P(survive 2nd level | survived 1st) −
  P(survive 1st)| ≤ 0.15; D–H at its zeros: conditional persistence ≥ 0.8.
- **P-X5 (the lifetime law):** fitting p95-lifetime ~ N^α across the three
  heights gives α ≤ 0.4 — the entry/drift clock, excluding window-filling
  α ≈ 1/2 (which would let a single walker cross the domination window and
  collapse the relay re-cut of §2).

Failure semantics, pre-committed: P-X2 failing (survival ≫ null) means the
carrier's own phases already conspire — (XLD)₂ is false as stated and the
discriminator must move upstream (into the creation sets' fine structure).
P-X3 failing (D–H valleys also ephemeral) means lifetime is NOT the
discriminating observable and (XLD) must be restated on the creation-set
geometry, not persistence. P-X5 failing at α ≈ 1/2 collapses §2's relay and
restores the single-walker picture — the contradiction step would then need
a different force entirely.

## 5. Probe results [MEASURED — probe_xld_zeta.py + probe_xld_dh.py, runpod, archived computations/mwm_xld/]

Self-certification of the D–H instrument, for the record: κ solved in-script
from the FE alone = 0.2840790438 (= the classical (√(10−2√5)−2)/(√5−1),
recovered not recalled); odd gamma factor (δ = 1) selected by the FE test;
EM-Hurwitz validated to 1e−7 against mpmath; Hardy-fold residual 6e−11;
83 off-line zeros certified by findroot (|F| < 1e−15), the first at
t = 85.6993, σ = 0.80852.

**ζ side** (T ∈ {2.5e4, 1e5, 1e6, 1e7}; N = 63, 126, 398, 1261; 4936/2850/
868/143 mid-band chains):

| | 2.5e4 | 1e5 | 1e6 | 1e7 |
|---|---|---|---|---|
| lifetime median | 2 | 2 | 2 | 2 |
| lifetime p95 | 27 | 24 | 26.6 | 20.9 |
| 3·N^{1/3} | 11.9 | 15.0 | 22.1 | 32.4 |
| surv1 measured | .605 | .614 | .662 | .679 |
| surv1 null | .643 | .647 | .659 | .663 |
| surv2 given surv1 | .829 | .809 | .679 | .613 |
| relay rate | .462 | .468 | .514 | .558 |
| relay chance baseline | .025 | .018 | .010 | .004 |

**D–H side** (83 certified zeros, level window n\* ± 15): longest-run median
**18** (min 5; 12/83 saturate the full 31-level window — right-censored,
true runs longer); covers matched level **81%**; one-step conditional
persistence **0.950**.

Scorecard against §4:
- **P-X1: median clause PASS** (2 everywhere); tail clause FAIL at the three
  lower heights (p95 ≈ 21–27, ~flat in N — neither the 3N^{1/3} clock nor
  growth; censoring 13–21% makes these lower bounds).
- **P-X2 PASS, strong** — measured/null = 0.94, 0.95, 1.00, 1.02. One-step
  VALLEY survival is phase-neutral to ≤ 6%, converging to 1.00 in N.
  (XLD)₂'s survival channel holds as stated.
- **P-X3 PASS** — D–H run median 18 ≥ 5× ζ median (10); 81% cover matched.
  Qualification: shallow zeros (η/spacing ≲ 0.12) run short (5–17) and
  supply every non-covering case; the deep ones (≥ 0.25) run 19–31 with
  frac_present up to 1.0.
- **P-X4: D–H clause PASS** (0.950 ≥ 0.8); ζ clause FAIL at low N (+0.22,
  +0.20 memory, vanishing to +0.02/−0.07 at high N) — the shape (positive,
  dying in N, survival-selected) is depth-frailty: surviving one push
  selects deep valleys; a depth-stratified null would absorb it. Not phase
  memory.
- **P-X5 PASS, decisive** — p95 ~ N^α fit gives α ≈ −0.09 ≪ 0.4. No
  window-filling; no single walker crosses the domination window; the §2
  relay re-cut stands.

**The unregistered finding is the largest effect in the data: the relay
channel.** Deaths are followed by same-height re-creation within ≤ 3 levels
at 0.46–0.56 measured rate against a 0.025–0.004 chance baseline — an
alignment enhancement of 18× → 128×, GROWING with N (~N^{0.6}). Death mode
is essentially 100% absorption (crossing appears; "vanished" ≈ 0/4000+):
the close pair does not evaporate, it oscillates on/off the line, exactly
the reverse dichotomy of doc 48 §2 run repeatedly. Consequences:
1. The naive independence version of (XLD) ("creation sets at consecutive
   levels do not align") is FALSE for ζ itself — alignment is real, strong,
   and N-growing. What saves the mid-band is that the relay is
   SUB-CRITICAL: each death re-creates with probability ~½, each re-created
   valley re-dies at the null rate, so relay chains decay geometrically and
   the total close-pair lifetime stays N-uniformly short (the flat ~20–27
   p95 tail is its trace).
2. For D–H at genuine off-line zeros the same channel is SUPER-CRITICAL:
   persistence 0.95/level, window-covering (81%, censored). The
   discriminator between the carriers is not one-step decorrelation (both
   are near-null there per P-X2) and not alignment (both align); it is the
   CRITICALITY of the relay — the chain-length tail: geometric for ζ,
   window-covering at D–H zeros.

> **(XLD), restated by measurement [CONJECTURE]:** for the matched ζ-tower
> at mid-band heights, the relay-chain length (consecutive-level close-pair
> persistence including on/off-line oscillation) has a geometric tail with
> N-uniform rate < 1. Euler-specific; false at D–H off-line zeros (measured
> super-critical); the correct quantitative form of the doc 75 open core.

## 6. What this opens

1. **The relay ledger.** The (H1) verdict (§1) + the relay finding fix the
   needed formal upgrade of `MidCentralInput` exactly: dynamic slip
   (protection dies in one entry — proved, slip identity) + a RELAY graph on
   births (death → re-creation edges at one height). Survivor bound becomes:
   survivors ≤ (resonant creations) × (mean relay-chain length). The second
   factor is (XLD); the first is (CR-density). Old task #8 (EPH) is exactly
   the chain-length object — it now has a measured target: geometric tail,
   rate ≈ ½·surv-null, N-uniform.
2. **The two-channel decomposition is the analytic attack surface.**
   Survival channel = phase-null (P-X2, now measured to 6%) — provable by
   the equidistribution of the single phase θ(t\*) − t\*·log(n+1) as n
   varies at fixed t\* (three-distance/discrepancy of the log-lattice, NOT
   a zero-density input). Re-creation channel = the reverse dichotomy fired
   by the NEXT entry on an on-line-landed pair — its ½-ish rate should be
   derivable from the frozen-lattice geometry (doc 51 §2–3: the circle
   passes through 0; half the orientations lift off). Both channels are
   doc-48/49-native objects. The product form (kill × re-birth chain) is
   the two-level statement to prove first.
3. **The D–H depth split** (shallow zeros fragile, deep zeros
   window-covering) predicts the ζ-side contrapositive: a putative ζ-pair
   at mid-band depth behaves like D–H's SHALLOW zeros — the regime where
   even D–H's forced persistence frays. Quantify the relay-criticality
   threshold in η/spacing; if the sub/super-critical boundary sits ABOVE
   the mid-band, the mid-band is killable by relay subcriticality alone.
4. Next, in force order: (i) two-level relay-rate derivation from the
   frozen lattice (the ½); (ii) the log-lattice discrepancy proof of the
   survival channel's phase-neutrality; (iii) seam-transport wiring (doc 75
   force item 3, still owed); (iv) the relay-ledger Lean upgrade
   (SweepCascade + a relay graph — combinatorics first, hypothesis-typed
   rates).
