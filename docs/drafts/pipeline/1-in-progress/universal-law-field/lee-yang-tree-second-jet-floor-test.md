# The tree-uniform second-jet floor — executing the corpus's recorded next test

- **ID:** ULF-FIELD-5
- **Stage:** 1-in-progress
- **Type:** DECISION TEST (corpus-recorded open test, now typed and partially computed)
- **Parents:** corpus `PrimeIsingTreeCentralMassFloorLaw.lean` + lane-elimination map entry
  "Next test: a tree-uniform floor on the second central jet would close that too";
  `PrimeIsingTreeBalancedCentering.lean` (the balanced family: even, entire, B(0)=1, only
  real zeros; "only the source-comparison theorem for the balanced family remains in the
  Lee–Yang route to RH")
- **Status:** [FIRST COMPUTATION DONE] [FOUR VERIFICATION OBLIGATIONS OPEN] [NOT RH]
  [NO LEAN — directive]

## The test, typed

For a finite prime Ising tree T let B_T be the balanced partition (corpus: even, entire of
order ≤ 1, B_T(0) = 1, all zeros real). Hadamard for an even, order ≤ 1, normalized entire
function forces B_T(z) = Π_k (1 − z²/x_k²), so the second central jet is

    (log B_T)''(0) = B_T''(0) = −2 Σ_k 1/x_k²  < 0   (strictly, if zeros exist).

**Test:** is the zero mass μ(T) := Σ_k 1/x_k² uniformly bounded below over all finite trees
by a constant c₀ > Σ_γ 1/γ² (sum over Xi zero ordinates)? If yes, no locally uniform limit of
balanced tree partitions can equal XiC — because locally uniform convergence of entire
functions carries the central jets, and XiC's second central jet is −2Σ_γ 1/γ² — and the
balanced Lee–Yang tree route to RH is CLOSED unconditionally, finishing the corpus's
mass-floor program (first jet killed the unfactored family; the second jet would kill the
balanced one). If no (some tree family dilutes the zero mass below the Xi value), the closing
device dies and the route stays open with a quantified constraint — also a recorded verdict.

## First computation (this cycle)

Single free vertex at prime p (decoupled tree): partition 1 + u_p(z) with the centered
unimodular field u_p(z) = p^{iz} (verification obligation V1 below): zeros exactly at
z = (2k+1)π/log p, k ∈ ℤ, paired ±. Zero mass:

    μ = Σ_{k≥0} 2·(log p / ((2k+1)π))²·(1/2-pairing convention fixed in V3)
      = (log p)²/π² · (π²/8) · 2 = (log p)²/4.

So the single-vertex mass is (log p)²/4 ≥ (log 2)²/4 ≈ 0.1201. The comparison constant:
Σ_γ 1/γ² ≈ 0.0231 (classical, absolutely convergent, unconditional), so the Xi second jet is
≈ −0.0462 while every single-vertex tree has jet ≤ −0.2402·(1/2-convention, V3). The gap is
a factor ≈ 5: robust, but the conventions must be pinned before any claim.

## Verification obligations (all four before the verdict; none is optional)

- **V1 — the field.** Read `centeredPrimeLeeYangField`'s exact definition; confirm u_p is
  unimodular on the real axis with frequency log p (else recompute the zero locations).
- **V2 — cavity monotonicity.** The decisive step: prove μ(T) ≥ c₀ for ALL trees, not just
  decoupled ones. Danger to refute or confirm: ferromagnetic couplings could repel zeros
  from the origin and dilute μ below the single-vertex value. Candidate tools: the corpus's
  cavity/Blaschke contraction structure (`cavityTransfer` = Blaschke factor, strict disk
  preservation), GHS-type monotonicity, or a direct interlacing argument on the pair block
  vs its decoupled limit. If dilution is possible, find the extremal family and compute its
  infimum — the test's answer is whatever the infimum says relative to 2Σ1/γ².
- **V3 — normalization matching.** Pin the variable conventions: the tree zeros' variable vs
  XiC's variable (the corpus's XiC has zeros at the ordinates γ iff RH; unconditionally
  (log XiC)''(0) = −2Σ_ρ over the divisor in the centered variable — verify the exact
  constant against the corpus's `CentralReciprocalMoments`/Xi-jet modules rather than the
  classical tables; the factor-of-2 and pairing conventions must come from the tree, not
  from habit).
- **V4 — the jet-convergence step.** Locally uniform convergence transports central jets
  (corpus already owns `iteratedDeriv_tendsto_of_locallyUniform` — cited by the mass-floor
  law); confirm it applies verbatim to the balanced family.

## Why this is the right next attack (program-level)

It is the corpus's OWN recorded next test on a recorded live door (the balanced Lee–Yang
family is the unique survivor of the mass-floor law); both outcomes are new recorded
knowledge (route closed unconditionally, or closing device refuted with an extremal family);
the computation is finite and elementary per tree; and it is exactly E2-adjacent — the
Lee–Yang cone-with-corners mechanism is the one exit the field's classification leaves
open, so deciding its strongest in-tree instance is deciding a live obstruction, not
classifying it.

## Log

- 2026-08-09 — chartered; single-vertex mass computed ((log p)²/4, floor (log 2)²/4 vs Xi's
  ≈ 0.0462 with conventions unpinned); four verification obligations named, V2 (cavity
  monotonicity vs dilution) identified as the decisive one. No Lean.
