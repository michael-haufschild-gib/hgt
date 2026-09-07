# CCM-FU: increasing middle-prime order with fixed scalar reserves

- **ID:** CCM-FU-MIDDLE-RESERVES
- **Stage:** 5-failed
- **Type:** FALSIFIED scheduling class; positive source amplification formalized
- **Parent:** [adaptive prime ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Source:** [actual growing signed batches](../3-formalized/ccm-fu-growing-signed-prime-batches.md)
- **Boundary:** General adaptive orders, PE4, PE4G, PE4C, SD1 and RH remain open.

## Full proof chain and frozen claim

Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints
→ signed curvature → prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green
→ RH. The divisor-order proposal must provide the missing arithmetic bound
through complete source coverage. Growing selected signed batches already
have an unconditional uniform quadratic ceiling, but leave the middle primes.

The retired claim is that increasing processing of those middle primes can
stay under some fixed quadratic ceiling when supplemented by arbitrary
interleavings of the fixed scalar reserve: primes q with `M/8<q<M`, isolated
after the core of primes below eight. The reserve selection may depend on M
and may include either sign. Its cardinality and total mass are unrestricted.
This does not retire schedules that move nonisolated primes across the
increasing middle front.

Write `P_N={p prime : p<4N}`, `M_N=64N²`, and let `F_M(P,R)` be the actual
retained fibre with processed set P and retained label R. Let `E_M(P)` be the
sum of all retained fibre squares. Lean proves the unconditional statement:

For every real C, eventually for all natural N and **every** finite pool L
of primes satisfying `M_N/8<q<M_N`,

`C M_N² < E_(M_N)(P_N union L)`.

Every increasing-middle order supplemented only by those scalar primes
passes through such a state. Hence no fixed quadratic ceiling works for this
scheduling class, even if the number of scalar interleavings grows arbitrarily.

## Dependency-closed paper proof

The argument uses corpus identities, the unconditional prime-window count,
and the already proved complete-source limit
`S(K) log(K)/(K sqrt(K)) -> 0`, where `S(K)=sum_d mu(d) K_d(K)`.
No numerical channel value or energy observation is used.

1. **Exact child head.** For `N>=1` and `K<=8N`, every prime with `p²<K`
   belongs to P_N. Every remaining prime lies in the late singleton sector.
   The terminal source identity and its exact negative singleton sign give
   `F_K(P_N,empty)=S(K)+sum_(p<K, p notin P_N) K_p(K)`.

2. **Uniform positive child mass.** For `7N<=K<=8N` and prime
   `4N<p<=5N`, the first-block formula is
   `K_p(K)=(sqrt(K)-sqrt(p)) D(1)`.
   The corpus harmonic remainder bound at four and analytic logarithm bound
   give `D(1)>=1/10`. Squaring rational bounds gives
   `sqrt(K)>=13sqrt(N)/5` and `sqrt(p)<=23sqrt(N)/10`, hence
   `K_p(K)>=sqrt(N)/40`. The prime-window count eventually gives at least
   `N/(2log(4N))` such primes. All other unsigned channels are nonnegative,
   so the entire late mass is at least `N sqrt(N)/(80log(4N))`.

3. **Uniform complete-source correction.** Apply the complete-source limit
   with tolerance `1/3840`. Throughout the whole child window,
   `K sqrt(K)<=24N sqrt(N)` and `log(K)>=log(4N)`. A single threshold in N
   therefore ensures `abs(S(K))<=N sqrt(N)/(160log(4N))` for every such K.
   Combining with the exact identity proves
   `F_K(P_N,empty)>=N sqrt(N)/(160log(4N))` uniformly on `[7N,8N]`.

4. **Clipped parent amplification.** For every prime `8N<p<=9N`, both
   `k=floor(M_N/p)` and `k+1` lie in `[7N,8N]`. Exact prime reflection gives
   `F_(M_N)(P_N,{p})=-sqrt(p)*((1-w)F_k(P_N,empty)+w F_(k+1)(P_N,empty))`,
   with `0<=w<1`. Retaining both endpoints, weakening the child denominator
   to `log(8N)`, and using `sqrt(p)>=2sqrt(N)` gives
   `F_(M_N)(P_N,{p})<=-N²/(80log(8N))`.

5. **Invariance under scalar control.** More generally, if every prime q in
   L has its complete adjacent quotient core already in P, consuming L
   leaves every nonempty coordinate R disjoint from L unchanged. The exact
   insertion formula adds the q-containing child coordinate, which vanishes
   for nonempty R in this isolated situation. Induction proves this for any
   finite L. For N>=2, the core below eight is in P_N, every q in the fixed
   reserve is isolated, and `(8N,9N]` is disjoint from that reserve. Thus the
   entire parent singleton window in step 4 persists for every allowed L.

6. **Quantitative energy escape.** The parent prime-window count is
   eventually at least `N/(2log(8N))`. Distinct singleton labels index a
   subfamily of the literal energy squares. Squaring step 4, summing those
   labels, and dividing by `M_N²` yields, uniformly over every allowed L,
   `N/(52428800 log(8N)^3) <= E_(M_N)(P_N union L)/M_N²`.
   The left side tends to positive infinity by the logarithm-power
   little-o theorem. It exceeds every fixed real C eventually, proving the
   frozen claim false without an assumed energy ceiling or final-source bound.

## Strongest positive survivor

The positive result is an explicit nested source-amplification theorem:
large partially processed child heads become a whole family of large,
nonempty parent singleton coordinates, with a proved diverging normalized
square sum. The generic exact invariant in step 5 shows why scalar head
adjustment cannot affect that sector, regardless of available signed mass.
This is stronger than a failed one-step contraction or finite diagonal excess.

A surviving complete bounded-energy schedule must alter the coupled
nonempty field before the indicated increasing-middle state. It must move
nonisolated operations across the middle front, or use another ordering that
avoids the proved sector growth. Abundant scalar reserves alone do not supply
that control. No construction of the required complete order, or estimate for
the final signed source, follows from this obstruction.

## Lean certificate and audit

[MobiusDivisorMiddleChildHead.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorMiddleChildHead.lean)
contains the exact child-head decomposition and its uniform lower bound:

- `RHTower.mobiusDivisorMiddleChildHead_eq_total_add_tail`
- `RHTower.eventually_mobiusDivisorMiddleChildHead_lower`

[MobiusDivisorMiddleReserveEscape.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusDivisorMiddleReserveEscape.lean)
contains the generic invariant and singleton-energy inclusion, the actual
parent-fibre bound, explicit normalized-energy lower bound, and final escape:

- `RHTower.mobiusDivisorSelectionFibre_union_isolated_nonempty`
- `RHTower.sum_mobiusDivisorSelectionSingleton_sq_le_energy`
- `RHTower.eventually_mobiusDivisorMiddlePrimeFibre_upper`
- `RHTower.eventually_mobiusDivisorMiddleEnergy_lower`
- `RHTower.eventually_mobiusDivisorMiddleEnergy_escape`

Both scratch files and exact leaves passed foreground `lake env lean`, one
owned Lean process at a time. Only the two required new oleans were emitted.
All seven new public theorems were axiom-audited once: only `propext`,
`Classical.choice`, and `Quot.sound`; no added axiom, `sorryAx`, or numerical
proof oracle. Both leaves are wired once into `RHTower.lean`. No full,
umbrella, or dependency build ran. Existing dependencies were not re-audited. The single
global `scripts/formal_tools.py lint` run passed. New artifact links and
scoped whitespace checks passed.

## Diagnostic provenance and limits

The [bounded RunPod diagnostic](../2-fully-proven/computations/ccm-fu-middle-prime-energy-2026-09-07/README.md)
examined 21 sampled cutoffs through 2^20, using eight forked workers on a
16-core host, and completed in 1.653 seconds. It exposed growing retained
singleton contributions after removing the fixed scalar reserve. That finite
observation motivated the independent analytic argument; it proves neither
divergence nor any statement about all adaptive orders. Script and results
were downloaded, all four SHA-256 hashes matched the remote originals, and
all owned remote computation files were removed after verification.
