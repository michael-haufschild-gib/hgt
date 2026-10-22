# Principal-relative carrier for completed unit-Riesz CCM source

- **ID:** `ccm-unit-riesz-coherent-principal-relative-carrier`
- **Stage:** 3-formalized
- **Type:** SOURCE-FAITHFUL CODIAGONAL / HG ADMISSION / BOUNDARY-CHARGE RECONSTRUCTION
- **Scientific status:** `[UNCONDITIONALLY PROVED IN LEAN]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Formal module:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMUnitRieszCoherentRelativeCarrier.lean`
- **Parent:** `ccm-unit-riesz-coherent-arithmetic-tail-charge`

## Result

Let `C_N(u)` be literal completed unit-Riesz coherent response and, for `h>0`, define its shift
codiagonal

```text
Delta_h C_N(u) = C_N(u+h)-C_N(u).
```

For `u>=log N`, Lean proves exact two-mode tail law

```text
Delta_h C_N(u)
 = exp(-u/2)(exp(-h/2)-1)(B_prime(N)-sqrt N)
   +(4/3)sqrt N exp(-u)(exp(-h)-1).
```

Thus `Delta_h C_N(u)->0`: codiagonal kills exactly constant tail charge. More importantly, it does
not erase source. Finite telescoping and completed-response tail limit give

```text
sum_(j=0)^(m-1) Delta_h C_N(u+jh)
 = C_N(u+mh)-C_N(u)

lim_(m->infinity) sum_(j=0)^(m-1) Delta_h C_N(u+jh)
 = R_1(log N)/2-C_N(u).
```

The increment kernel vanishes at zero for every nonnegative lag. Since literal prime and polar lags
are nonnegative, Lean proves `C_N(0)=0`, hence capstone identity

```text
R_1(log N)/2
 = lim_(m->infinity) sum_(j=0)^(m-1) Delta_h C_N(jh).
```

Finally, module constructs continuous closed representative on all real `u` and complex profile

```text
ell_(N,h)(u)=Delta_h C_N^closed(u).
```

For every `N>=2`, `h>=0`, this is an HG `LeakProfile`: strongly measurable and

```text
integral_(0,infinity) (1+u)|ell_(N,h)(u)|^2 du < infinity.
```

## Scientific consequence

Earlier direct-HG obstruction is fully repaired at carrier level. Canonical completed CCM datum is
not one Hilbert vector but principal-relative pair

```text
(decaying bulk Delta_h C_N, boundary charge R_1(log N)/2).
```

Pair is source-faithful: charge is reconstructed from translated bulk itself. This is stronger than
renormalization by subtracting an unknown constant, and gives concrete common object for Route O,
CCM-FU, CCM-UR, CCM-HG, CCM-GS, and CCM-EP.

New hard core is quantitative, not representational. Follow-up finite-boundary-readout theorem has
now eliminated infinite-series issue by aperture-matched rank-two tail recurrence. It remains to
derive unconditional signed/energy control of three bulk samples strong enough to bound `R_1`.

## Claim-to-Lean closure

| Claim | Declaration |
|---|---|
| exact codiagonal right tail | `unitRieszCoherentCompletedShiftCodiagonal_eq_rightTail` |
| codiagonal decay | `tendsto_unitRieszCoherentCompletedShiftCodiagonal` |
| finite telescoping | `sum_unitRieszCoherentCompletedShiftCodiagonal` |
| zero-boundary kernel | `unitExponentialIncrementKernel_zero_right` |
| literal prime response vanishes at zero | `unitRieszCoherentPrimeKernelResponse_zero` |
| completed response vanishes at zero | `unitRieszCoherentCompletedKernelResponse_zero` |
| relative reconstruction at arbitrary basepoint | `tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal` |
| arithmetic charge as bulk series | `tendsto_sum_unitRieszCoherentCompletedShiftCodiagonal_zero` |
| closed continuous representative | `unitRieszCoherentCompletedKernelResponseClosed`, `continuous_unitRieszCoherentCompletedKernelResponseClosed` |
| HG profile | `unitRieszCoherentCompletedShiftCodiagonalProfile`, `leakProfile_unitRieszCoherentCompletedShiftCodiagonalProfile` |

All theorem declarations have `#print axioms` output exactly
`[propext, Classical.choice, Quot.sound]`. Direct module check and exact leaf build pass. Module is
imported by `GaloisForLFunctions.RHTower` umbrella; umbrella itself was not built.

## Theatre and novelty audit

Finite-difference telescoping is classical and not claimed as new. Candidate novelty is exact
composition of four facts for literal CCM arithmetic source:

```text
forbidden coherent tail = R_1/2,
canonical codiagonal is HG-admissible,
zero boundary is forced by increment geometry,
R_1/2 is reconstructed as infinite codiagonal bulk series.
```

This closes previously named open carrier problem. It does not prove any bound on `R_1`, so it is
not represented as RH progress beyond moving frontier from construction to a sharp quantitative
inequality. Prior targeted corpus and primary-source audit found no exact statement; external
priority remains unverified.

## New open core

Superseded by `ccm-unit-riesz-coherent-finite-boundary-readout`: at `h=log N`, infinite sum below
collapses to three uniformly conditioned samples. Prove source-specific point/graph estimate for
those samples:

```text
sum_(j>=0) Delta_h C_N(jh)=R_1(log N)/2.
```

Reporter-only `L2` admissibility remains insufficient; source covariance, boundary relative trace,
GS incidence, or EP operator-valued dephasing must control finite point evaluations.

## Gates

- [x] canonical charge-cancelling codiagonal
- [x] source-faithful reconstruction
- [x] arithmetic charge as exact bulk series
- [x] closed HG profile
- [x] unconditional Lean proof
- [x] umbrella wiring
- [ ] independent mathematical audit
- [ ] external priority audit
- [x] finite uniformly conditioned replacement for summable dual
- [ ] source-specific three-sample estimate
- [ ] unconditional `R_1` bound
- [ ] RH endpoint

## Log

- 2026-08-16 -- Derived two-mode shift-codiagonal tail and decay.
- 2026-08-16 -- Proved finite/infinite source reconstruction and `C_N(0)=0`.
- 2026-08-16 -- Identified half resolvent as infinite bulk-increment series.
- 2026-08-16 -- Constructed and proved HG-admissible continuous complex profile.
- 2026-08-16 -- Audited axioms, built leaf module, wired umbrella.
