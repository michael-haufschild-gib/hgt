# Transverse Information Fusion Mechanics (ULF-TIFM-1) — STAGE 3 COMPLETE (2026-08-12)

Card: `docs/drafts/pipeline/3-formalized/universal-law-field/transverse-information-fusion-mechanics/prime-boolean-mass-hankel-recurrence-transverse-information-law.md`
Certificate: same folder, `...-formalized.md`.
Ledger row 79 = DONE.

## Literal fusion theorem
One ramification-diagonal high-exponent Euler shell yields finite Boolean Gibbs configurations with
prime clocks.  It generates:
1. Route-E parity/clock Schur capacity `D`;
2. Gibbs-damped half-density Mass current `j`, with `‖j‖² = C` and `j_{σ=1,p} = p/(p+1)·(log p/√p)`;
3. positive prime-clock Hankel block `H₁ = [[A,B],[B,C]]`, `det = AC − B²`;
4. recurrent pure-state phase orbit with transverse QFI `𝓘_⊥ = 4D`.
Exact laws: `D‖j‖² = π² det H₁`;  `𝓘_⊥‖j‖² = 4π² det H₁`.
First `2d` moments reconstruct clocks/aperture/weights; tilt response is `4π² Cov(r,R²)`.

## RH audit
At `σ = 1` with ≥2 primes: `D>0`, `det H₁>0`, `𝓘_⊥>0`.  Criticality is NOT vanishing finite
transverse QFI (`not_forall_apertureTransverseQFI_eq_zero`).  Surviving successor gate: the
shared-gauge quotient-fusion problem, i.e. card
`quotient-fusion-genesis-mechanics/shared-gauge-quotient-fusion-genesis-and-partition-qfi-law.md`.
Do not regress into finite factor vanishing.

## Lean
Two modules, both under `HTGeometry.UniversalLawField`:
- `HTGeometry/PrimeBooleanMassHankelQuantumFusion.lean` — abstract capstones
  (`fusionTransverseQFI_mul_massEnergy`, QFI, positivity, tilt response, Prony reconstruction,
  prime-clock recurrence).
- `HTGeometry/PrimeBooleanFusionSourcePacket.lean` (NEW 2026-08-12) — everything the first module
  left as paper: `fusionMassCurrent`/`sum_fusionMassCurrent_sq`, `clockMoment`,
  `fusionHankelMatrix`(+`_eq_moments`,`det_`), `fusionHankel_quadratic_nonneg`,
  `schurCapacity_mul_massEnergy`, `pairEnergy_eq_schurCapacity_mul_massEnergy`,
  `fusionTangentQFI`(+`_eq`,`_one`), `pureStateQuantumFisherValue_parityClock_tangent`,
  `isLeast_fusionTransverseQFI`, the three `..._of_subsingleton` degenerations,
  `apertureFug`/`apertureOcc`/`apertureWt`(+`_eq` forms), `bernoulliVar_apertureOcc`,
  `apertureEnergy_pos` (DERIVED, kills the `0 < capC` hypothesis at the prime source),
  `primeClockVec_injective`, `apertureMassCurrent_one`, `aperture_*_pos`,
  `aperture_schurCapacity_mul_massEnergy`, `aperture_fusionTransverseQFI_mul_massEnergy`,
  `exp_primeClockVec`, `occProb_eq_probOfVar_occVar`, `eq_of_occVar_eq`,
  `sigma_eq_of_apertureWt_eq`, `norm_prod_sub_one_le`, `fusionSourceState`,
  `norm_fusionSourceState` (unit vector), `exp_clock_eq_prod_shellFlow`,
  `fusionSourceState_exists_large_return`, `not_forall_apertureTransverseQFI_eq_zero`.

## Corpus reuse that mattered (do not re-derive)
- `ConstraintFrameRelativity/SchurCapacity.lean` — `capA/capB/capC/schurCapacity`,
  `capA_mul_capC_sub_capB_sq(_lt)`, `capC_pos`, `schurCapacity_pos`, `schurCapacity_eq_ratio`,
  `isLeast_schurCapacity`, `bernoulliCov_affine_clock`.
- `ConstraintFrameRelativity/ShellCapacityDepth.lean` — `occProb`, `occVar`(+`_eq/_pos/_mono`),
  and the `Aperture` structure (an alternative prime-aperture encoding on `Fin card`).
- `ConstraintFrameRelativity/EscortLogit.lean` — `probToOdds`/`oddsToProb`, `shellOcc`,
  `bernVar`, `probOfVar`, `bernVar_probOfVar` (the smaller-root inverse of `q(1−q)=w`).
- `ConstraintFrameRelativity/PhaseHistoryDilation.lean` — `primeClockVec`, `shellFlow`,
  `exists_large_return` (arbitrarily late prime-phase returns).
- `ConstraintFrameRelativity/BernoulliBooleanGibbs.lean` / `BooleanGibbsCapacityResponse.lean` —
  `bernoulliWeight`, `sum_bernoulliWeight`, `linearStat`, `bernoulliVar`, tilt response.
- `HTGeometry/ProjectiveQuantumFisherValue.lean` — `pureStateQuantumFisherValue`.

## Lean traps hit
- `EuclideanSpace ℂ n` is `WithLp 2 (n → ℂ)`: build with `WithLp.toLp 2 f`; then
  `(x).ofLp i = f i` and `(x - y).ofLp i = x.ofLp i - y.ofLp i` are both `rfl`.
  `EuclideanSpace.equiv` unfolds to `PiLp.continuousLinearEquiv` and blocks `simp only`.
- `Nat.Primes` literals: `({⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩} : Finset Nat.Primes)` fails
  instance-wise because the anonymous constructor elaborates at `{p // Nat.Prime p}`.  Introduce
  top-level `def primeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩` first.
- `Finset.card_insert_of_not_mem` is now `Finset.card_insert_of_notMem`.
- `exists_large_return` takes `F` explicitly; passing `(F := F)` as well silently mis-binds `T`.
