# CCM self-polarized complex Dirac shear

- **ID:** `ccm-self-polarized-complex-dirac-shear`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** complex Dirac two-shear plane × source-selected adaptive shear × Julia orientation-preserving plane lift × quantum complex-Gram energy
- **Lean module:** `GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracSelfPolarizedShear`
- **Statement:** The actual matched complex phase symbol canonically selects a Hermitian shear whose nodal form is its squared norm and whose Dirac determinant has one strict global sign away from spectral center.

## Goal

Turn the nowhere-zero two-shear crossing covector into a scalar determinant without choosing a
fragile fixed projection and without dividing by its norm. This removes every off-center
determinant crossing at each actual prime-power wall and preserves labels under finite packets.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture extracted from Lean-proved C2 identities and adjacent corpus search
- [x] 1 → 2  fully-proven: complete proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem, direct check, exact leaf build, axiom audit
- [ ] 3 → 4  publication-ready: standalone paper

## The law `[LEAN-PROVED]`

For the full matched symbol `Z=Z_n(x)`, define its division-free self-polarized shear

```text
B_Z = Re(Z) B_re + Im(Z) B_im.
```

Lean proves `B_Z` Hermitian. On the canonical gauge-dressed nodal vector `v`, its exact crossing
form is

```text
v* B_Z v = 2 gauge(n)^2 normSq(Z).
```

Thus every actual prime-power crossing form is strictly positive exactly off center and zero
exactly at center. Define the source-selected Dirac family

```text
A_n(x,t) = H(Z_n(x)) + t B_{Z_n(x)}.
```

It is Hermitian and equals the C2 two-shear family at parameters
`(t Re Z_n(x), t Im Z_n(x))`. Its determinant is the exact scalar

```text
det A_n(x,t) = -2 t normSq(Z_n(x)).
```

No phase normalization, square root, inverse, or branch choice occurs. The determinant and Krein
form obey the division-free reciprocity law

```text
gauge(n)^2 Re(det A_n(x,t)) = -t (v*B_Z v).
```

For every actual prime-power atom and every `t>0`:

```text
Re(det A_n(x,t)) < 0 ↔ x ≠ 0,
Re(det A_n(x,t)) = 0 ↔ x = 0.
```

The center is therefore the unique zero and a global determinant maximum, not merely a local
chamber seed. A nonempty finite label-preserving sum of determinant responses has the same strict
negative-off-center and unique-zero laws.

## Main Lean declarations

- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedShear_isHermitian`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_eq`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_primePower_pos_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingForm_primePower_eq_zero_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_isHermitian`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_eq_twoShear`
- `det_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedDeterminantKreinReciprocity`
- `det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_neg_iff`
- `det_re_ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_eq_zero_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceSelfPolarizedCrossingFamily_primePower_global_max_zero`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_neg_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeComplexSourceFinitePrimePowerSelfPolarizedDeterminantResponse_eq_zero_iff`

## New scientific knowledge

Scalarization does not require selecting one fixed component of an oriented source plane. The
source plane has a canonical nonlinear dual: pair the source coordinate with itself. In the Dirac
carrier this is implemented by a Hermitian shear whose coefficients are the intact complex phase
coordinates. The result is a signed determinant equal to negative complex Gram energy.

This is the exact shared principle behind four corpus mechanisms:

1. Julia lifts retain a hidden channel before lossy scalar recombination.
2. Quantum metric–Berry strictness is controlled by complex Gram energy, not phase curvature.
3. Adaptive Hankel shears are source-selected connection observables.
4. Projective-wedge transport warns that moving-frame connection terms must be retained.

C3 fuses them into an actual matched-CCM theorem. It upgrades C1's local scalar chamber and C2's
global vector nonvanishing to one global scalar determinant chamber.

## Frontier effect

Off-center determinant crossings are no longer the obstruction. The remaining task is exact
coefficient-faithful descent: identify or transport this source-selected determinant response into
an RH-complete scalar receiver without discarding the adaptive connection term. No published
Weil/Xi positivity or RH conclusion is claimed here.

## Verification

- scratch: `lake env lean /tmp/CCMSelfPolarized.lean` — PASS
- direct source check: `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracSelfPolarizedShear.lean` — PASS
- exact leaf build: `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseProjectiveGaugeComplexDiracSelfPolarizedShear` — PASS
- axiom audit of Hermitian, crossing-form, determinant, reciprocity, global-sign, and finite-packet theorems: only `[propext, Classical.choice, Quot.sound]`
- umbrella import added to `GaloisForLFunctions.RHTower`
- no umbrella/full build run

## Log

- 2026-08-21 — conjectured after broad corpus search across Julia lifts, quantum metric–Berry gaps, involutive projective wedge transport, adaptive Hankel shears, and Plücker covariant connections.
- 2026-08-21 — self-polarized Hermitian shear, exact determinant, atom global chamber, and finite-packet laws proved in Lean scratch.
- 2026-08-21 — direct check, exact leaf build, and axiom audit passed; promoted to stage 3.
