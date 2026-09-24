# RG-ETA: dyadic finite-work source inequality

- **ID:** RG-ETA-DW
- **Stage:** 1-in-progress
- **Type:** CANDIDATE, with a formalized sharp obstruction theorem
- **Source:** RG-ETA paired-eta finite-prefix energy transport
- **Target:** For every nontrivial zero on or right of the critical line, prove from the literal finite eta prefixes that its dyadic signed energy-work block is nonpositive at arbitrarily late cutoffs.

## Exact current theorem

Let `E_N(ρ)` be the completed partner finite-prefix magnitude squared minus the completed original finite-prefix magnitude squared, and let `W_j(ρ) = E_j(ρ) - E_{j+1}(ρ)`. The Lean theorem in [EtaTopPrefixDyadicEnergyWork.lean](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaTopPrefixDyadicEnergyWork.lean) proves the exact finite identity

`∑_{j=N}^{2N-1} W_j(ρ) = E_N(ρ) - E_{2N}(ρ)`.

At a hypothetical zero with `Re ρ = σ > 1/2`, put `p = 1 - σ` and let `C_ρ > 0` be the sharp completed partner-tail constant. Then the same module proves

`(2N+3)^(2p) ∑_{j=N}^{2N-1} W_j(ρ) → (1 - 2^(-2p)) C_ρ² > 0`.

Thus every sufficiently late dyadic block has positive literal finite arithmetic work at such a zero. The assertion uses the actual zero multiplicity and requires no simplicity assumption. It follows from the existing sharp centered-tail limit and the exact finite transport law; it makes no one-step sign claim.

The [isolated-leading-current theorem](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaTopPrefixDyadicLeadingFlux.lean) proves the same sharp limit with each `W_j` replaced by the single leading eta flux. The difference is negligible at this scale because both the increment-energy current and the lower-hierarchy remainder flux have unconditionally summable endpoint-weighted absolute values. At multiplicity one the isolated current is the new-head/successor-prefix pairing; at higher multiplicity it is the adjacent centered-moment pairing.

The [head-kernel factorization](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaEnergyLeadingFluxKernelFactorization.lean) isolates the multiplicity-one source obstruction. Write `L_N` for the new-head cutoff, `x` for translated head time, `t` for prefix time, `γ = Im ρ`, and `H_ρ(v)` for the complementary horizontal-tilt bracket. The literal head kernel is exactly

`-2 cos(γ(t-L_N-x)) H_ρ(L_N+x+t)`.

For `Re ρ > 1/2`, `H_ρ(v)` has one explicit crossover and is positive beyond it. Once `L_N` exceeds that crossover, the bracket is positive almost everywhere on the entire head–prefix product measure, so the kernel is negative exactly where the displayed cosine is positive. Consequently the multiplicity-one source step is a **signed Fourier correlation estimate**, not a pointwise positivity statement. The higher-multiplicity adjacent kernel already has a corresponding four-factor decomposition: positive shift scale, negative centered monomial, cosine, and the same horizontal bracket.

The [dyadic head-cosine theorem](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaTopPrefixDyadicHeadCosine.lean) defines the literal weighted cosine correlation `Q_N(ρ)` and proves `leadingFlux_N(ρ) = -2 Q_N(ρ)` at multiplicity one. At a hypothetical simple right-half zero it proves the **sharp negative law**

`(2N+3)^(2p) ∑_{j=N}^{2N-1} Q_j(ρ) → -(1/2)(1-2^(-2p)) C_ρ² < 0`.

Thus a cofinal nonnegative dyadic cosine block would exclude all simple off-line zeros. A source-side `o(N^(-2p))` bound would also contradict the sharp limit, so strict sign control is stronger than necessary. The negative leading coefficient shows why an estimate based only on oscillation of the new head is insufficient: at a hypothetical zero the head and remaining prefix are phase-locked after multiplication, leaving a coherent real dyadic contribution. Higher multiplicity still requires its separate adjacent-moment estimate.

The existing positive cosine-interval lemmas require phase spread `|Im ρ| log(2N) ≤ π` or stronger, so they cannot cover cofinal cutoffs at a fixed nonzero ordinate. Replacing the cross term by a self-Gram term gives a positive square but leaves a signed endpoint difference and does not orient the original current. Any successful bound must use a source law across the full eta support, including its alternating gaps, rather than intervalwise phase positivity alone.

The source has a further exact real invariant. In log-time cell `n`, eta occupies `(log(2n+1),log(2n+2)]` and omits `(log(2n+2),log(2n+3)]`. Let `D(t)` be occupied length in `(0,t]` minus `t/2`. At `t=log(2N+1)`,

`D(t) = (1/2) log W_N`, where `W_N = ∏_{n<N}(2n+2)^2/((2n+1)(2n+3))`.

The cell surpluses are strictly positive, and `D(log(2N+1))` increases to `(1/2)log(π/2)`. These finite and limiting statements are Lean-proved in [EtaWallisLogOccupationSurplus.lean](../../../../formal/GaloisForLFunctions/RHTower/RiemannGaussian/EtaWallisLogOccupationSurplus.lean). The full primitive `D(t)` is positive and bounded by the same cell geometry. For `Re s>0`, integration by parts and the positive-support Laplace representation give the paper identity `s² ∫₀∞ e^(-st)D(t)dt = pairedEtaCore(s) - 1/2`. Hence every nontrivial zero imposes the exact value `-1/2` on its left side. A proposed half-plane nonnegative-real-part bound for that left side is false: it is negative at actual critical-line zeros and remains negative at nearby points to their right by continuity. Wallis positivity therefore supplies a source primitive but no complex phase orientation. The full-primitive transform identity and this phase failure are paper-level here, not Lean claims.

## Open source step

Derive an opposing cofinal nonpositive dyadic-block inequality for the isolated leading current, or a quantitatively smaller block at its sharp scale. In the multiplicity-one branch this requires a source-side nonnegative or `o(N^(-2p))` dyadic average of the weighted head–prefix Fourier cosine after the crossover. The existing positive Gram and endpoint tail bounds do not orient this cross-correlation. In the higher-multiplicity branch the centered monomial has fixed negative sign, but both full-prefix variables continue to sample early times; the horizontal crossover can remain inside their support at every cutoff. Both the cosine and the crossover then need source control. A one-step sign argument additionally needs control of *differences* of the normalized tail remainder: the available `O(1/N)` remainder is at the scale of the proposed one-step leading term after subtraction. The dyadic block theorem avoids that rate gap but does not itself establish the opposing source inequality.
