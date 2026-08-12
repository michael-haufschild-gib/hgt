# Prime Boolean--Mass--Hankel--recurrence transverse-information law — Lean certification

- **ID:** ULF-TIF-1
- **Stage:** 3 — formalized in Lean 4
- **Paper card:**
  `docs/drafts/pipeline/3-formalized/universal-law-field/transverse-information-fusion-mechanics/prime-boolean-mass-hankel-recurrence-transverse-information-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.PrimeBooleanMassHankelQuantumFusion`,
  `GaloisForLFunctions.HTGeometry.PrimeBooleanFusionSourcePacket`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

## Certified mechanism

One positive finite clock packet with weights `w` and clock labels `lam` generates four unlike
shadows:

1. Schur capacity of the Boolean parity grade transverse to the clock;
2. Gibbs-damped Mass energy `C`;
3. first Hankel determinant `AC - B²`;
4. pure-state quantum Fisher information of the parity/clock phase family.

Lean certifies the exact conservation identity

```text
fusionTransverseQFI(w, lam) * fusionMassEnergy(w, lam)
  = 4 * pi^2 * fusionHankelDet(w, lam).
```

This is not an analogy between routes.  All factors are functions of one marked coefficient
packet, and the equality is unconditional.

## Certified declarations

| Mathematical clause | Lean declaration |
|---|---|
| Mass energy is clock variance | `fusionMassEnergy_eq_capC` |
| transverse QFI is four times Schur capacity | `fusionTransverseQFI_eq_four_mul_schurCapacity` |
| actual pure-state QFI equals directional covariance | `pureStateQuantumFisherValue_booleanParityClock_eq_directional` |
| transverse QFI is the directional lower bound | `fusionTransverseQFI_le_directional` |
| canonical minimizing direction | `fusionDirectionalQFI_canonical` |
| four-organ conservation | `fusionTransverseQFI_mul_massEnergy` |
| strict transverse-QFI positivity | `fusionTransverseQFI_pos` |
| strict Hankel-determinant positivity | `fusionHankelDet_pos` |
| Gibbs-damped/primitive Mass comparison | `gibbsDampedMassEnergy_eq_damping_sq_mul_primitive` |
| intervention response | `hasDerivAt_booleanTiltTransverseQFI` |
| spectrum reconstruction from moments | `realClockSpectrumPoly_eq_of_moments_eq` |
| weight reconstruction from moments | `realClockWeights_eq_of_moments_eq` |
| arbitrarily late prime-clock recurrence | `primeBooleanFusion_exists_large_return` |

The reconstruction declarations reuse the corpus finite cyclic-process theorem: equality of the
required finite moment window forces equality of the spectrum polynomial and then of every marked
weight.  This is joint determinacy, not a numerical algorithm.

## Certified declarations — literal prime source packet

`GaloisForLFunctions.HTGeometry.PrimeBooleanFusionSourcePacket` evaluates every organ on the
aperture source itself, so no nondegeneracy input is assumed: the clock energy moment is derived,
not hypothesised.

| Mathematical clause | Lean declaration |
|---|---|
| Mass current `j_p = √(w_p) lam_p`, `‖j‖² = C` | `fusionMassCurrent`, `sum_fusionMassCurrent_sq` |
| clock moments `M_k`, and `M₀ = A`, `M₁ = B`, `M₂ = C` | `clockMoment`, `clockMoment_zero`, `clockMoment_one`, `clockMoment_two` |
| first Hankel block and its determinant | `fusionHankelMatrix`, `fusionHankelMatrix_eq_moments`, `det_fusionHankelMatrix` |
| the block is positive semidefinite | `fusionHankel_quadratic_nonneg` |
| three-organ conservation `D·C = π² det H₁` | `schurCapacity_mul_massEnergy` |
| conservation in clock-gap form | `pairEnergy_eq_schurCapacity_mul_massEnergy` |
| two-parameter pure-state QFI `I(a,b) = 4 Var(π a N − b E)` | `fusionTangentQFI`, `fusionTangentQFI_eq`, `pureStateQuantumFisherValue_parityClock_tangent` |
| transverse QFI is the exact infimum over clock gauges | `isLeast_fusionTransverseQFI` |
| one marked clock kills all three transverse organs | `fusionHankelDet_eq_zero_of_subsingleton`, `schurCapacity_eq_zero_of_subsingleton`, `fusionTransverseQFI_eq_zero_of_subsingleton` |
| prime fugacity, occupation `q_p = 1/(1+p^σ)`, weight `w_p = p^σ/(1+p^σ)²` | `apertureFug`, `apertureOcc`, `apertureWt`, `apertureOcc_eq`, `apertureWt_eq` |
| the Gibbs weight is the Bernoulli variance of the source law | `bernoulliVar_apertureOcc` |
| exact half-density Mass damping `j_{1,p} = (p/(p+1))·(log p/√p)` | `apertureMassCurrent_one` |
| derived positivity of the clock energy moment | `apertureEnergy_pos` |
| distinct marked primes have distinct clocks | `primeClockVec_injective` |
| strict positivity of capacity, Hankel determinant, transverse QFI | `aperture_schurCapacity_pos`, `aperture_fusionHankelDet_pos`, `aperture_fusionTransverseQFI_pos` |
| three- and four-organ conservation at the prime source | `aperture_schurCapacity_mul_massEnergy`, `aperture_fusionTransverseQFI_mul_massEnergy` |
| the marked prime is recovered from its clock | `exp_primeClockVec` |
| the occupation is the smaller root of `q(1−q) = w` | `occProb_eq_probOfVar_occVar`, `eq_of_occVar_eq` |
| one marked Gibbs weight determines the inverse temperature | `sigma_eq_of_apertureWt_eq` |
| the normalised Boolean source state on `ℓ²(𝒫(F))` is a unit vector | `fusionSourceState`, `norm_fusionSourceState` |
| the configuration phase factorises over marked primes | `exp_clock_eq_prod_shellFlow`, `norm_prod_sub_one_le` |
| the pure clock orbit returns in norm at arbitrarily late times | `fusionSourceState_exists_large_return` |
| "criticality = vanishing transverse information" is false | `not_forall_apertureTransverseQFI_eq_zero` |

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/PrimeBooleanMassHankelQuantumFusion.lean
lake env lean GaloisForLFunctions/HTGeometry/PrimeBooleanFusionSourcePacket.lean
lake build GaloisForLFunctions.HTGeometry.PrimeBooleanFusionSourcePacket
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
python3 scripts/formal_tools.py lint --check-generated
```

Direct elaboration of both modules passes with no diagnostics.  Foreground leaf build of the source
packet completes 8,677 jobs; foreground umbrella build completes 11,852 jobs.  Target scan contains
no `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.

`#print axioms` on all twenty-eight source-packet capstones, and on the nine earlier capstones,
reports only:

```text
propext
Classical.choice
Quot.sound
```

No computation certificate, RH premise, Xi specialization, route endpoint, or cofinal completion
enters the proof.

## Exact field consequence

The corpus-wide intervention grammar now has one literal fusion cell satisfying all five research
gates: common generation, three-organ fusion, exact conservation, finite reconstruction, and a
fourth-organ prediction.  Lean also certifies the hostile boundary: under positive weights and two
distinct clocks, transverse QFI and Hankel determinant are strictly positive.  Hence finite
criticality cannot mean vanishing transverse information.  Any future RH selector in this field
must compare nonzero conserved packets or construct a singular cofinal balance.
