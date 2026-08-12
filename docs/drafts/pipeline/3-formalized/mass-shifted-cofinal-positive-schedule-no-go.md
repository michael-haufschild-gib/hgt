# Mass-shifted cofinal positive-schedule no-go

- **ID:** mass-shifted-cofinal-positive-schedule-no-go
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL DIAGONAL RECESSION + RATE NO-GO
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3

## Open core attacked

Fixed-degree far-right positivity was previously separated from cofinal degree growth.  The new
projective-spread law accepts any cofinal schedule of positive shifted-Xi blocks, but does not
construct one.  Determine whether qualitative fixed-degree recession supplies such a schedule and
whether its projective spread or harmonic source work can carry RH information.

## Conjecture loop

1. **C1 — no cofinal positive schedule follows from fixed-degree recession.** **FAILED.**  Choose a
   positivity threshold independently at every degree and evaluate beyond both that threshold and
   the degree.  This gives an unconditional mass schedule tending to infinity with its degree-`n`
   shifted-Xi block positive.
2. **C2 — projective spread on such a schedule detects off-line zeros.** **FAILED.**  The schedule
   is constructed from unconditional fixed-block recession.  Existing projective-spread transport
   then forces divergent spread on it without any RH premise.
3. **C3 — prescribing faster escape can restore detection.** **FAILED.**  The threshold selection
   can majorize an arbitrary real-valued floor `g(n)`.  Any lower growth requirement is therefore
   compatible with the unconditional positive schedule.
4. **C4 — qualitative recession supplies the parabolic upper rate `w = O(n)`.** **FAILED AS A
   LOGICAL CONSEQUENCE.** Pointwise convergence in every fixed matrix size gives no upper bound on
   its degree-dependent positivity threshold.  The closed delayed-switch countermodel has positive
   fixed-degree limit `1`, yet equals `-1` on the degree-matched diagonal at every grade.
5. **C5 — prescribing a fast projective-spread rate in the observation index restores RH
   sensitivity.** **FAILED.** Reindex the unconditional positive schedule cofinally.  For arbitrary
   real floors `g(l)` and `h(l)`, one may force both `w_l ≥ g(l)` and projective spread `> h(l)`
   while degree and mass still tend to infinity and every selected actual block remains positive.

## Exact representation lesson

The relevant invariant is not cofinality. The iterated limit “fixed degree, then mass to infinity”
admits arbitrarily late thresholds and is blind to RH. An upper mass/degree law is indispensable for
transporting fixed-degree recession to a specified diagonal, but it is not itself an RH
discriminator: the paper-proved parabolic horizon already gives unconditional positivity in the
region `y >= K N^2`. Under RH failure, the complementary first-contact sequence has bounded
nonzero `N/sqrt y` and compactifies to a finite-type restricted-Weil null state. Thus rate is an
admission coordinate. The surviving source invariant is the compactified first-contact boundary
state and, specifically, whether its finite nonzero zero-edge hyperbolic-capacity branch can occur.

## Formal targets

- construct an actual shifted-Xi cofinal positive schedule above every prescribed lower floor;
- derive divergent projective Gauss-root spread on that schedule;
- simultaneously derive the eventual harmonic projective-source lower bound;
- formalize a delayed-switch diagonal countermodel showing pointwise eventual positivity alone
  cannot supply any prescribed upper schedule.

## Fully proved survivor

For every floor `g : ℕ → ℝ`, there is a schedule `w(n) ≥ max(n,g(n))` tending to infinity such that
the actual degree-`n+2` shifted-Xi moment block is positive definite.  Along the same schedule the
normalized projective Gauss-root spread tends to infinity.  One unconditional schedule also
satisfies, at every `n ≥ 2`, the harmonic projective arithmetic-surplus bound

\[
 \mathfrak S_n(w_n)\ge \frac{1}{2(2n+1)}\,\mathfrak F_n(w_n)^2.
\]

Hence no lower escape law, cofinal positivity law, divergent spread law, externally prescribed
spread-rate law, or harmonic source-work law can distinguish RH. External schedule index has a
cofinal reparametrization gauge. Upper diagonal effectivity is necessary to leave the iterated-limit
regime, but existing Route U paper theorems show that parabolic rate alone is also unconditional.
The next live datum is source admission of the compactified boundary state: exclude its finite
nonzero zero-edge capacity branch, including the multiple-root/odd-sector alternative, not merely
bound the schedule.

## Lean formalization

Module:
`formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionCofinalScheduleNoGo.lean`

Capstones:

- `fixedDegreePositiveLimit_negative_degreeDiagonal`;
- `exists_xiShiftedCofinalPositiveProjectiveSchedule_above`;
- `exists_xiShiftedCofinalPositiveProjectiveSchedule_above_spreadFloor`;
- `exists_xiShiftedCofinalPositiveSchedule_spread_and_harmonicWork`.

Verification on 2026-08-12:

- direct `lake env lean` passed;
- targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCofinalScheduleNoGo`
  passed (11,809 jobs);
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound` for the capstones;
- the module contains no `sorry`, `admit`, declared `axiom`, `opaque`, or `unsafe`.

## Literature audit

Varying-degree Hankel and smallest-eigenvalue results located in explicit positive-weight models do
not provide shifted-Xi source admission at compactified first contact. Classical varying-weight
asymptotics and the abstract delayed-switch countermodel explain the order-of-limits issue; neither
identifies or excludes the shifted-Xi zero-edge capacity branch.
