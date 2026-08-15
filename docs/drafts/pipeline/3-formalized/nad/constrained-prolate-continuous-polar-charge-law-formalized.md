# The constrained prolate exterior tail has bounded continuous polar charge — formalized

- **ID:** `constrained-prolate-continuous-polar-charge-law-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `constrained-prolate-continuous-polar-charge-law.md`
- **Umbrella imports:** `GaloisForLFunctions.RHTower`, `GaloisForLFunctions.HTGeometry`

## What is formalized

The card's theorem is the exterior seed law: an explicitly constructed constrained prolate source
has a growing half-line primitive of size `O(lambda^{-1/2})` — equation `(11)` — and therefore a
continuous polar charge of size `O(lambda^{-1})` — equations `(18)`/`(51)`.

Both are now closed in Lean with **no hypotheses at all**:

```text
RHTower.exists_prolate_source_polar_primitive_bound        -- (11)
RHTower.exists_prolate_source_polar_charge_bound           -- (18)/(51)
```

The paper's route cited two classical inputs — Dunster's exterior Liouville–Green expansion `(48)`
and the PSWF asymptotics `d_0/d_1 = O(lambda^{-8})` together with the Hermite limits of `chi_n`.
**None of them is used.**  The Lean realization replaces the asymptotics by an exact construction:
the mode is produced variationally, and its separation-ratio bound `s < 1/2` — the paper's only
genuinely quantitative PSWF input — is proved.

## The chain

| Step | Lean | Content |
|---|---|---|
| self-reciprocity | `RHTower/ProlateGlobalBandEigen.lean` | the unit-band extension satisfies the finite-Fourier eigen-relation at **every** real point, so `Fourier(source)(w) = chi · q(w/a)` far outside the aperture |
| no simplicity needed | `RHTower/ProlateEvenEigenspaceDecomposition.lean` | every even global Slepian eigenfunction is a finite sum of joint prolate modes |
| trial vector | `RHTower/ProlateGaussianTrial.lean`, `…TrialPositive.lean` | `L_c v = (-c + 3cx² - c²x⁴)v` for `v = exp(-cx²/2)`, and `∫(L_c v)v > -(c²/2)∫v²` for `c ≥ 400` |
| finite-dimensional half | `RHTower/ProlateEvenEigenspaceQuadratic.lean` | one large quadratic-form value on an even band eigenspace produces a mode with high prolate eigenvalue |
| `L²` diagonalization | `RHTower/ProlateBandHilbertSum.lean` | `L²[-1,1]` is the Hilbert sum of the band operator's eigenspaces (mathlib's compact self-adjoint spectral theorem) |
| parity | `RHTower/ProlateReflection.lean`, `…BandComponentEven.lean` | reflection intertwines both operators; every eigencomponent of an even profile is even |
| entirety for `L¹` | `HTGeometry/CompactFourierIntegrableEntire.lean` | the compact Fourier transform of an **integrable** amplitude is entire; uniqueness from a window of real frequencies |
| injectivity | `RHTower/ProlateBandOperatorInjective.lean` | the band operator is the square of the finite Fourier transform, hence injective: the eigenvalue `0` drops out |
| **`s < 1/2`** | `RHTower/ProlateLowSeparationMode.lean` | **`exists_even_joint_prolate_eigen_separation_lt_half`** |
| channel bound | `RHTower/ProlateUnconditionalChannelBound.lean` | every hypothesis of the exact-channel estimate discharged |
| finite-Fourier eigen | `RHTower/ProlateFourierBandEigen.lean` | the prolate action commutes with the aperture transform; the even prolate eigenline is one dimensional, so the mode *is* a finite-Fourier eigenfunction |
| the source | `RHTower/ProlateModeSource.lean` | the mode cut off with the half-endpoint convention; its Fourier transform; the symmetric-Lebesgue condition |
| mean zero | `RHTower/ProlateMeanZeroSource.lean` | the mass-matched dilate; Fourier dilation law; periodization additivity |
| all channels | `RHTower/ProlateAllChannelLeftEndpoint.lean` | left endpoint `L ≥ 2` puts every channel in the oscillatory regime |
| channel primitives | `RHTower/ProlateChannelPrimitiveBound.lean` | the exponential substitution and the summed bound, uniform in the endpoint |
| **`(11)`** | `RHTower/ProlateSourcePolarPrimitive.lean` | **`exists_prolate_source_polar_primitive_bound`** |
| bounded variation | `RHTower/ProlateSourceVariation.lean` | the source is an antitone step times a Lipschitz profile |
| **`(18)`/`(51)`** | `RHTower/ProlateSourcePolarCharge.lean` | **`exists_prolate_source_polar_charge_bound`** |

## Audited declarations

Each resolves and `#print axioms` reports exactly `propext`, `Classical.choice`, `Quot.sound`.

- `RHTower.exists_even_joint_prolate_eigen_separation_lt_half` — for every `c ≥ 400` an even joint
  band/prolate eigenfunction with `radialSeparationRatio c eta < 1/2`;
- `RHTower.exists_radialProlate_channel_bound` — the all-channel radial primitive bound with no
  hypotheses beyond the bandwidth;
- `RHTower.exists_realFourierBandTransform_eigen` — the selected mode is a finite-Fourier
  eigenfunction, `kappa mu² = lam`, at every real point;
- `RHTower.eq_zero_of_bandOperatorL2_eq_zero` — the Slepian band operator is injective;
- `RHTower.exists_prolate_source_polar_primitive_bound` — `(11)`;
- `RHTower.exists_prolate_source_polar_charge_bound` — `(18)`/`(51)`.

## What the card does not claim

The card's own hostile audit stands: the theorem concerns one explicit source sequence, is not
Weil-complete, and neither proves a restricted-Weil floor nor implies RH.  The remaining gate on the
card — the true cofinal Weil floor — is its declared *next* wall, not part of this theorem.
