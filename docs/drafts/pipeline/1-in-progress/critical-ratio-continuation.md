# Critical-ratio continuation without a fixed aliasing floor

- **ID:** critical-ratio-continuation
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Astra frontier](../../../reports/review-0311/astra.md)
- **Statement:** For every fixed real compact C² test H, establish compensated Weil nonnegativity along unbounded critical ratios R, or establish unweighted Weil nonnegativity directly.

## Exact target

Let aφ = (∫φ)²/∫φ² for the tilted unit spline, J = tiltedJordanOne > 0,
and B(H) = ∫ exp(-8y)H(y)² dy. For every A ≥ 0 and C² function H
supported in [-A,0], prove that arbitrarily large R > 0 satisfy

    aφ Q(H) + 7 J B(H) / R ≥ 0.

The quantifiers allow R and all finite-horizon thresholds to depend on H.
This target removes compensation by passage to infinity and reaches the
existing half-weight Weil criterion. A larger bounded interval is progress,
not completion. An alternative sufficient target is whole-space positivity
at every fixed critical multiple c = 2K(log N)^(1/8).

## Established input

- `CriticalMultipleCompleteWeilPositivity`: whole-space quantitative positivity
  throughout one fixed small critical band.
- `CompleteWeilCriticalMultipleAndWindowCorollaries`: uniform finite-horizon
  window Gram consequences and compensated window limits.
- `OneCriticalMultiplePaysEveryWindow`: an independent aperture-uniform
  weighted lower floor; this alone retains positive compensation.
- `TheCanonicalCriticalClockEntersFromTheNegativeSide`: a nonzero equality
  profile enters from negative finite-horizon energy on the canonical clock.

## Open core

The remaining dual-collar and far-reserve bounds absorb dimensionless losses
R = c⁸/log N and R². Their smallness cannot be obtained by increasing N at
fixed R. Recover the signed arithmetic interaction behind these losses, or
construct a source-preserving replacement whose compensation vanishes.
No unproved positivity, residual improvement, or continuation assumption
may enter a theorem's premises.

## Signed residual

Let B(c,N) be `completeWeilMatrix tiltedUnitSpline c N`, v_m(N) the
normalized Ramanujan horizon vector, E_m(c) its completed conductor energy,
and g = 2 + γ - log(4π) > 0. For each fixed m,l ≥ 1 and R > 0,
with c_N≥1 and c_N⁸/log N→R, the checked theorem gives

    (log N / c_N) ⟨B(c_N,N)v_m - E_m(c_N)v_m,v_l⟩
      → aφ g [m=1][l=1].

Together with the proved Jordan law c⁷E_m(c) → J(m) and Gram convergence,
the checked fixed-block corollary gives
the critical limit diag(J(m)) + R aφ g e₁e₁ᵀ on every fixed finite
conductor block, positive for every R.
`TheCriticalConductorFormRetainsThePolarGenus.lean` passes its final
actual-path audit with `[propext, Classical.choice, Quot.sound]` and is
wired into its umbrella. It is not a whole-space conclusion.

**Existing support, not new conjectures:**
`TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons` already represents
every atomic vector by its exact Möbius horizons.
`TheHorizonChargeIsBlindToTheRealPartsOfTheZeros` already proves positivity
of the individual pole charge throughout the open zero strip.
`TheBulkAtThePoleReadsTheArchimedeanGenus` already proves the stated positive
rank-one contribution from all low zeros. The new limit concerns the
complete form after its conductor energy is subtracted; none of those
results controls that remaining signed contribution at critical scale.

**Current proof boundary:** the complete seven-channel signed limit is
checked with the standard three axioms, including its actual-path no-olean
audit. The growing packet through Q=floor((log N)^(13/32)) now has the
same signed polar correction, with relative error ≤εΣE_m b_m² uniformly
in coefficients at every fixed R>0. Its main transfer passes the final
actual-path check; the complement retains separate R and R² losses.

One part already has a sharper consequence. For fixed m > 1 the exact
reference identity gives

    shellCorrection(c,m) = completeWeilAdjunctionEnergy(1,m)
                           - log c - E_m(c).

Since E_m(c) → 0, this term is O_m(1+log c), hence o(c).
For m=1 its linear coefficient is aφ. These follow from
`completeWeilAdjunctionEnergy_eq_at_one_sub_log`,
`completedConductorEnergy_eq_sub_shellCorrection` and the proved decay of
E_m. They isolate the leading conductor; they do not estimate the other
rows or justify uniformity in growing m.

The seven-channel decomposition narrows the fixed-pair calculation
further. After multiplication by log N/c_N, the existing bounds send the
ratio-prime residual, self error and pole error to zero. The center term
is linear in c and has the explicit `centerSecondOrder` limit. Its signed
combination with separated cross error, combined near-Gamma/downward/center
rows, and the upward-prime residual supplies the stated genus. The
separated-regime theorem `tendsto_completeWeilBulkEntry` assumes c<1;
its filename does not authorize using it on a growing critical clock.

The [upward-prime signed limit](critical-upward-residual-signed-limit.md)
now checks in Lean: its leading term is −aφ(γ+1)e₁e₁ᵀ, with cancellation
of all other fixed conductor pairs. The critical-curve corollary holds
at every R>0 and passes its no-olean audit with the standard three axioms.
The [joint Gamma–center limit](critical-gamma-center-signed-limit.md) now
passes its final no-olean audit with the standard three axioms;
its listed support-file audits remain pending. The complete signed residual passes its actual-path no-olean
audit with the same axioms.

**Attack:** the positive low-zero term alone did not identify this limit;
the complete arithmetic calculation was needed. Growing-conductor receiving
charges and coupling to the horizon complement remain. The existing m²l² residual
majorant, divided by conductor energies ≳m⁷/c⁷ below overlap, has summable
weights m⁻³. They give the checked growing-packet transfer; they do not
pay the dual-collar coupling. Verdict: `BRIDGE`. The remaining issue is
coupling to the horizon complement and that complement's energy.
No whole-space all-R theorem follows. See the
[growing-packet proof](../3-formalized/critical-low-packet-signed-compactness.md) and
[window-complement localization theorem](../3-formalized/critical-windows-survive-low-conductor-removal.md).
The [signed pole–window transport conjecture](critical-pole-window-signed-transport.md)
targets the inverse-energy mixed pairing needed for optimized arithmetic
correctors, which ordinary orthogonal removal does not control.
The [receiving-capacity growth theorem](../3-formalized/critical-receiving-capacity-growth.md)
separately tests whether the new arbitrarily small raw prime-charge costs
occur fast enough on the critical clock. Its dilation capacity is now
proved to be `log log N+O(1)`, with a final actual-path audit using the
standard three axioms. Its checked critical-scale corollary gives
`c_N t²/C_N→∞` for every nonzero fixed charge. A complete-energy
comparison and mixed-response rate remain open. The existing raw-cost
obstruction supplies no prescribed rate.

## Surviving bounded-range improvement

**Joint pole payment.** For p > 1 set

    d(p) = 1 / (sqrt(p+1) sqrt(p-1)) - 1/p,
    Cjoint(p) = |gammaBracket(0)| + 2 exponentialPrimeMass(p) + d(p).

The proved lower floor is Q(H) ≥ -Cjoint(p) exponentialMass(p,H).
It strictly improves the existing floor, whose pole cost is
1/(p+1) + 1/(p-1). This is a bounded-range bridge, not compensation removal.

**Dependency-closed paper argument for the pole estimate.** Put
F(y)=exp(-py/2)H(y), u(y)=sqrt(p+1) exp((p+1)y/2) and
v(y)=sqrt(p-1) exp((p-1)y/2), with u,v restricted to y≤0.
Then ||u||²=||v||²=1 and <u,v>=sqrt(p+1)sqrt(p-1)/p.
Write a=∫H exp(y/2), b=∫H exp(-y/2), s=sqrt(p+1), t=sqrt(p-1).
Cauchy–Schwarz gives

    (sa-tb)² ≤ (2-2st/p) exponentialMass(p,H).

Since 4st ab=(sa+tb)²-(sa-tb)², the full pole term 2ab is
at least -d(p) exponentialMass(p,H). The prime and diagonal bounds and
nonnegative archimedean jump energy already in
`TheAliasingWeightPaysEveryWindow` give the stated complete floor.
Here 0<st<p, so d(p)>0; also d(p)<1/(p-1)<1/(p+1)+1/(p-1).
Consequently 7J/(aφ Cjoint(8)) strictly exceeds the previous natural
weighted-floor threshold 7J/(aφ exponentialWeilFloor(8)).

**Attack verdict:** BRIDGE. The argument is an exact rank-two pole
calculation, extending the corpus's unweighted centred-pole method to its
aliasing norm. It supplies no source cancellation for the remaining prime
or Gamma losses and no claim of new mathematics beyond the corpus audit.
The two source modules and their principal results pass Lean with exactly
`[propext, Classical.choice, Quot.sound]`; see the
[formalized bounded extension](../3-formalized/joint-pole-payment-extends-the-critical-ratio.md).
The strict finite-horizon conclusion is per fixed independent family.
No comparison with the separate whole-space small-band threshold is proved.

## Rejected compensation mechanism

Adding a fixed finite Ramanujan twist cannot lower the limiting untwisted
energy. `graded_ramComb_criticalCurve_exact` gives the original pencil plus
a nonnegative Jordan-weighted aliasing mass; `tendsto_mixedGram` gives zero
mixed block. The positive survivor is this exact graded decomposition.
This excludes that fixed-period correction mechanism, not correctors whose
period or amplitude varies with N.

Some moving correctors are covered too. `exists_uniform_conductor_range`
in `TheConductorDecompositionHoldsOnAGrowingRange` gives a range M(N)→∞
with quadratic error ≤εΣb_m², uniformly in coefficients, for fixed window
profiles. Thus corrections supported in that range with bounded Σb_m²
cannot lower the untwisted limit. This last consequence is an elementary
deduction; the theorem supplies no prescribed growth rate for M(N), and
does not control coefficients with unbounded square mass.

## Gates

- [x] Exact target and existing small-band source identified.
- [ ] Derive and attack an explicit signed interaction or compensation-removal mechanism.
- [x] Complete a dependency-closed proof of an unconditional bounded advance.
- [x] Formalize that bounded advance and audit its transitive axioms.
- [ ] Reach unbounded R or remove compensation; audit the original target.

## Audit scope

Local Lean corpus only, as requested. No numerical experiments. The new
task's supplied Lean instructions require formalization and a final
`lake --old env lean` audit for completed proofs. Source claims remain
distinct from successful kernel checks.
