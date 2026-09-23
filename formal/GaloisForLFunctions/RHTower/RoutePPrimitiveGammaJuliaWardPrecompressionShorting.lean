import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaTwoPrimeWardBudgetNoGo
import GaloisForLFunctions.RHTower.GammaSewnMobiusJuliaSourceTransport

/-!
# Route P Gamma--Julia Ward precompression shorting

P-G205 proves that the literal depth-zero prime-two/prime-three Ward energy stays positive while
the completed eight-unit budget tends to zero.  Hence every compression-monotone Ward comparison
fails.  This module constructs the required order-reversing survivor from an independent source
operation already in the corpus.

The normalized environment coordinate of the canonical Gamma-sewn Julia lift is defined on every
prime before any finite packet is chosen.  Multiply its two-cell exterior difference by both
literal reciprocal-promotion amplitudes.  This gives a skew, coefficient-faithful, all-cell source
coupling.  Only afterwards select and normalize the `(2,3)` packet.

The resulting resolved-source/environment block is a positive rank-one Gram.  Its source corner
is exactly the finite-aperture Ward energy, while shorting through the environment pivot is zero.
As aperture tends to the lossless wall, the compressed corner tends to P-G205's strictly positive
literal Ward energy.  Thus short-then-compress is eventually strictly smaller than
compress-without-environment: compression monotonicity is genuinely broken.

This closes coupling and order of operations, not Xi-divisor identification.  A remaining
completed-source theorem must transport this exact Julia short through Gamma/polar descent while
retaining Xi multiplicity.
-/

open Filter Topology Set Matrix

namespace RHTower

noncomputable section

/-- Literal Gamma--Julia clock on every prime-depth source cell, before any finite selection. -/
def routePPrimitiveGammaJuliaWardSourceEnergyLevel
    (x : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveFourthDepthGammaCyclicAmplitude *
    gammaSewnMobiusJuliaNormalizedPrimeLog x pe.1

/-- Global coefficient-faithful exterior coupling on two source cells.  Prime labels and divisor
depths remain in the two reciprocal-promotion amplitudes; the Julia clock is applied before any
finite prime packet is chosen. -/
def routePPrimitiveGammaJuliaWardSourceExteriorCoupling
    (x u : ℝ) (i j : Nat.Primes × ℕ) : ℝ :=
  Real.sqrt 2 *
    xiGammaEulerPrimitiveDescentTestAmplitude u i *
    xiGammaEulerPrimitiveDescentTestAmplitude u j *
    (routePPrimitiveGammaJuliaWardSourceEnergyLevel x i -
      routePPrimitiveGammaJuliaWardSourceEnergyLevel x j)

@[simp] theorem routePPrimitiveGammaJuliaWardSourceExteriorCoupling_self
    (x u : ℝ) (i : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaWardSourceExteriorCoupling x u i i = 0 := by
  simp [routePPrimitiveGammaJuliaWardSourceExteriorCoupling]

theorem routePPrimitiveGammaJuliaWardSourceExteriorCoupling_swap
    (x u : ℝ) (i j : Nat.Primes × ℕ) :
    routePPrimitiveGammaJuliaWardSourceExteriorCoupling x u j i =
      -routePPrimitiveGammaJuliaWardSourceExteriorCoupling x u i j := by
  unfold routePPrimitiveGammaJuliaWardSourceExteriorCoupling
  ring

/-- Gamma--Julia energy level retained in the environment before scalar recombination. -/
def routePTwoPrimeJuliaWardEnergyLevel (x : ℝ) (i : Fin 2) : ℝ :=
  routePPrimitiveGammaJuliaWardSourceEnergyLevel x (routePTwoPrimeWardCell i)

/-- Ward energy of the literal two-prime co-source against the finite-aperture Julia clock. -/
def routePTwoPrimeJuliaWardCompressedEnergy (x u : ℝ) : ℝ :=
  2 * routePTwoPrimeWardWeight u 0 * routePTwoPrimeWardWeight u 1 *
    (routePTwoPrimeJuliaWardEnergyLevel x 0 -
      routePTwoPrimeJuliaWardEnergyLevel x 1) ^ (2 : ℕ)

/-- Nonlocal cross term produced before cell compression from both reciprocal-promotion
amplitudes and the Gamma--Julia environment clock. -/
def routePTwoPrimeJuliaWardNonlocalCoupling (x u : ℝ) : ℝ :=
  routePPrimitiveGammaJuliaWardSourceExteriorCoupling x u
    (routePTwoPrimeWardCell 0) (routePTwoPrimeWardCell 1) /
      routePTwoPrimeWardMass u

/-- Finite two-prime coupling is only normalization of pre-existing all-cell exterior kernel. -/
theorem routePTwoPrimeJuliaWardNonlocalCoupling_eq_sourceCompression
    (x u : ℝ) :
    routePTwoPrimeJuliaWardNonlocalCoupling x u =
      routePPrimitiveGammaJuliaWardSourceExteriorCoupling x u
          (routePTwoPrimeWardCell 0) (routePTwoPrimeWardCell 1) /
        routePTwoPrimeWardMass u := rfl

/-- Positive resolved-source/Julia-environment block before prime-cell compression. -/
def routePTwoPrimeJuliaWardPrecompressionBlock (x u : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  let c := routePTwoPrimeJuliaWardNonlocalCoupling x u
  !![routePTwoPrimeJuliaWardCompressedEnergy x u, c; c, 1]

/-- Scalar Schur short of the resolved source corner through the Julia environment pivot. -/
def routePTwoPrimeJuliaWardPrecompressionShortedEnergy (x u : ℝ) : ℝ :=
  let B := routePTwoPrimeJuliaWardPrecompressionBlock x u
  B 0 0 - B 0 1 * (B 1 1)⁻¹ * B 1 0

theorem routePTwoPrimeJuliaWardNonlocalCoupling_sq (x u : ℝ) :
    routePTwoPrimeJuliaWardNonlocalCoupling x u ^ (2 : ℕ) =
      routePTwoPrimeJuliaWardCompressedEnergy x u := by
  have hsqrt : Real.sqrt 2 ^ (2 : ℕ) = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  rw [routePTwoPrimeJuliaWardNonlocalCoupling,
    routePPrimitiveGammaJuliaWardSourceExteriorCoupling,
    routePTwoPrimeJuliaWardCompressedEnergy,
    routePTwoPrimeWardWeight, routePTwoPrimeWardWeight,
    routePTwoPrimeWardRawWeight, routePTwoPrimeWardRawWeight]
  simp only [routePTwoPrimeJuliaWardEnergyLevel]
  rw [div_pow, mul_pow, mul_pow, mul_pow, hsqrt]
  ring

theorem routePTwoPrimeJuliaWardPrecompressionBlock_compressed_eq
    (x u : ℝ) :
    routePTwoPrimeJuliaWardPrecompressionBlock x u 0 0 =
      routePTwoPrimeJuliaWardCompressedEnergy x u := by
  simp [routePTwoPrimeJuliaWardPrecompressionBlock]

/-- Environment pivot is the normalized literal two-prime source mass, not a free conductor. -/
theorem routePTwoPrimeJuliaWardPrecompressionBlock_environmentPivot_eq_sourceMass
    (x u : ℝ) :
    routePTwoPrimeJuliaWardPrecompressionBlock x u 1 1 =
      ∑ i : Fin 2, routePTwoPrimeWardWeight u i := by
  rw [routePTwoPrimeWardWeight_sum]
  simp [routePTwoPrimeJuliaWardPrecompressionBlock]

theorem routePTwoPrimeJuliaWardPrecompressionBlock_posSemidef
    (x u : ℝ) :
    (routePTwoPrimeJuliaWardPrecompressionBlock x u).PosSemidef := by
  let c := routePTwoPrimeJuliaWardNonlocalCoupling x u
  let R : Matrix (Fin 1) (Fin 2) ℝ := !![c, 1]
  have hc : routePTwoPrimeJuliaWardCompressedEnergy x u = c ^ (2 : ℕ) := by
    simpa [c] using (routePTwoPrimeJuliaWardNonlocalCoupling_sq x u).symm
  have hGram : routePTwoPrimeJuliaWardPrecompressionBlock x u = Rᴴ * R := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [routePTwoPrimeJuliaWardPrecompressionBlock, R, c, Matrix.mul_apply,
        pow_two, hc]
  rw [hGram]
  exact Matrix.posSemidef_conjTranspose_mul_self R

theorem routePTwoPrimeJuliaWardPrecompressionBlock_det
    (x u : ℝ) :
    (routePTwoPrimeJuliaWardPrecompressionBlock x u).det = 0 := by
  rw [routePTwoPrimeJuliaWardPrecompressionBlock, Matrix.det_fin_two]
  change routePTwoPrimeJuliaWardCompressedEnergy x u * 1 -
    routePTwoPrimeJuliaWardNonlocalCoupling x u *
      routePTwoPrimeJuliaWardNonlocalCoupling x u = 0
  rw [← routePTwoPrimeJuliaWardNonlocalCoupling_sq]
  ring

theorem routePTwoPrimeJuliaWardPrecompressionShortedEnergy_eq_zero
    (x u : ℝ) :
    routePTwoPrimeJuliaWardPrecompressionShortedEnergy x u = 0 := by
  rw [routePTwoPrimeJuliaWardPrecompressionShortedEnergy]
  change routePTwoPrimeJuliaWardCompressedEnergy x u -
    routePTwoPrimeJuliaWardNonlocalCoupling x u * 1⁻¹ *
      routePTwoPrimeJuliaWardNonlocalCoupling x u = 0
  rw [inv_one, mul_one]
  rw [← routePTwoPrimeJuliaWardNonlocalCoupling_sq]
  ring

theorem tendsto_routePTwoPrimeJuliaWardEnergyLevel_nhdsGT_zero
    (i : Fin 2) :
    Tendsto (fun x : ℝ => routePTwoPrimeJuliaWardEnergyLevel x i)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (routePTwoPrimeWardEnergyLevel i)) := by
  have hc : Tendsto
      (fun _ : ℝ => routePPrimitiveFourthDepthGammaCyclicAmplitude)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds routePPrimitiveFourthDepthGammaCyclicAmplitude) :=
    tendsto_const_nhds
  have h := hc.mul
    (tendsto_gammaSewnMobiusJuliaNormalizedPrimeLog_nhdsGT_zero
      (routePTwoPrimeWardCell i).1)
  simpa [routePTwoPrimeJuliaWardEnergyLevel,
    routePPrimitiveGammaJuliaWardSourceEnergyLevel,
    routePTwoPrimeWardEnergyLevel,
    routePPrimitiveJointDepthGammaJuliaLogMultiplier] using h

theorem tendsto_routePTwoPrimeJuliaWardCompressedEnergy_nhdsGT_zero
    (u : ℝ) :
    Tendsto (fun x : ℝ => routePTwoPrimeJuliaWardCompressedEnergy x u)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (routePTwoPrimeSourceStateWardEnergy u)) := by
  have hconst : Tendsto
      (fun _ : ℝ =>
        2 * routePTwoPrimeWardWeight u 0 * routePTwoPrimeWardWeight u 1)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (2 * routePTwoPrimeWardWeight u 0 *
        routePTwoPrimeWardWeight u 1)) := tendsto_const_nhds
  have hdiff :=
    (tendsto_routePTwoPrimeJuliaWardEnergyLevel_nhdsGT_zero 0).sub
      (tendsto_routePTwoPrimeJuliaWardEnergyLevel_nhdsGT_zero 1)
  have h := hconst.mul (hdiff.pow 2)
  rw [routePTwoPrimeSourceStateWardEnergy_eq_pair]
  simpa [routePTwoPrimeJuliaWardCompressedEnergy] using h

theorem eventually_routePTwoPrimeJuliaWardPrecompressionShorting_breaks_compression
    (u : ℝ) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ),
      routePTwoPrimeJuliaWardPrecompressionShortedEnergy x u <
        routePTwoPrimeJuliaWardPrecompressionBlock x u 0 0 := by
  have hpos : 0 < routePTwoPrimeSourceStateWardEnergy u :=
    routePTwoPrimeSourceStateWardEnergy_pos u
  have hevent : ∀ᶠ x in 𝓝[>] (0 : ℝ),
      0 < routePTwoPrimeJuliaWardCompressedEnergy x u :=
    (tendsto_routePTwoPrimeJuliaWardCompressedEnergy_nhdsGT_zero u).eventually
      (eventually_gt_nhds hpos)
  filter_upwards [hevent] with x hx
  rw [routePTwoPrimeJuliaWardPrecompressionShortedEnergy_eq_zero,
    routePTwoPrimeJuliaWardPrecompressionBlock_compressed_eq]
  exact hx

/-- P-G206 capstone: canonical Julia source transport supplies a positive nonlocal block whose
Schur short vanishes before compression, while its literal two-prime compression converges to the
strictly positive Ward energy and is eventually strictly larger. -/
theorem routePPrimitiveGammaJuliaWard_precompressionShorting
    (u : ℝ) :
    (∀ x : ℝ,
      (routePTwoPrimeJuliaWardPrecompressionBlock x u).PosSemidef ∧
      routePTwoPrimeJuliaWardPrecompressionShortedEnergy x u = 0 ∧
      routePTwoPrimeJuliaWardPrecompressionBlock x u 0 0 =
        routePTwoPrimeJuliaWardCompressedEnergy x u) ∧
    Tendsto (fun x : ℝ => routePTwoPrimeJuliaWardCompressedEnergy x u)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (routePTwoPrimeSourceStateWardEnergy u)) ∧
    (∀ᶠ x in 𝓝[>] (0 : ℝ),
      routePTwoPrimeJuliaWardPrecompressionShortedEnergy x u <
        routePTwoPrimeJuliaWardPrecompressionBlock x u 0 0) := by
  exact ⟨fun x =>
      ⟨routePTwoPrimeJuliaWardPrecompressionBlock_posSemidef x u,
        routePTwoPrimeJuliaWardPrecompressionShortedEnergy_eq_zero x u,
        routePTwoPrimeJuliaWardPrecompressionBlock_compressed_eq x u⟩,
    tendsto_routePTwoPrimeJuliaWardCompressedEnergy_nhdsGT_zero u,
    eventually_routePTwoPrimeJuliaWardPrecompressionShorting_breaks_compression u⟩

end

end RHTower
