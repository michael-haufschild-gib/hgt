import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardCofinalBoundaryLift
import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients

/-!
# Möbius-parity likelihoods have the Hardy Cauchy Gram at criticality

The Möbius parity is a unitary gauge on the squarefree source support.  Consequently it preserves
the complete two-aperture likelihood Gram, not merely the norm of one source vector.  At the Euler
critical boundary this common Gram is the right-half-plane Hardy Cauchy kernel on the real
normal-cone ray.

This identifies the exact positive upper-left block available to a parity-based singular Ward
lift.  It does not divide by the signed parity overlap and does not assert positivity of the
continued Xi Ward boundary column.
-/

open Complex Filter Set
open scoped BigOperators ComplexOrder Topology

namespace RHTower

noncomputable section

private theorem exp_pair_mul_probability_eq_boundaryLayerTerm
    {sigma u v : ℝ} (n : ℕ) :
    Real.exp (-(v * (sigma - 1) * Real.log n)) *
          Real.exp (-(u * (sigma - 1) * Real.log n)) *
          squarefreeMobiusProbability sigma n =
        squarefreeMobiusBoundaryLayerTerm sigma (u + v) n := by
  by_cases hsq : Squarefree n
  · have hn0 : n ≠ 0 := fun hn => by
      subst n
      exact not_squarefree_zero hsq
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
    rw [squarefreeMobiusBoundaryLayerTerm, Real.rpow_def_of_pos hnpos,
      ← Real.exp_add]
    have harg :
        -(v * (sigma - 1) * Real.log n) +
            -(u * (sigma - 1) * Real.log n) =
          Real.log n * -((u + v) * (sigma - 1)) := by
      ring
    rw [harg]
    ring
  · simp [squarefreeMobiusBoundaryLayerTerm, squarefreeMobiusProbability,
      squarefreeMobiusMass, hsq]

/-- The complete two-aperture damped-source Gram is the positive squarefree boundary transform at
the sum of the two apertures. -/
theorem inner_infiniteMobiusCriticalDampedSignedWeightLp_eq_boundaryLayerLaplace
    {sigma u v : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    inner ℂ
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma v hsigma hv) =
      squarefreeMobiusBoundaryLayerLaplace sigma (u + v) := by
  rw [lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  rw [show
      (∑' n : ℕ,
        infiniteMobiusCriticalDampedSignedWeight sigma v n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalDampedSignedWeight sigma u n)) =
        ∑' n : ℕ,
          (squarefreeMobiusBoundaryLayerTerm sigma (u + v) n : ℂ) by
    apply tsum_congr
    intro n
    rw [infiniteMobiusCriticalDampedSignedWeight,
      infiniteMobiusCriticalDampedSignedWeight]
    have hnorm :
        infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n) =
          (squarefreeMobiusProbability sigma n : ℂ) := by
      calc
        _ = ((‖infiniteMobiusSignedWeight sigma n‖ : ℂ) ^ 2) :=
          RCLike.mul_conj (infiniteMobiusSignedWeight sigma n)
        _ = _ := by
          rw [← Complex.ofReal_pow, norm_infiniteMobiusSignedWeight_sq hsigma]
    simp only [map_mul, Complex.conj_ofReal]
    rw [show
      (Real.exp (-(v * (sigma - 1) * Real.log n)) : ℂ) *
            infiniteMobiusSignedWeight sigma n *
          ((Real.exp (-(u * (sigma - 1) * Real.log n)) : ℂ) *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) =
        ((Real.exp (-(v * (sigma - 1) * Real.log n)) *
          Real.exp (-(u * (sigma - 1) * Real.log n)) : ℝ) : ℂ) *
          (infiniteMobiusSignedWeight sigma n *
            (starRingEnd ℂ) (infiniteMobiusSignedWeight sigma n)) by
      push_cast
      ring]
    rw [hnorm]
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal
      (exp_pair_mul_probability_eq_boundaryLayerTerm
        (sigma := sigma) (u := u) (v := v) n)]
  rw [← Complex.ofReal_tsum
    (squarefreeMobiusBoundaryLayerTerm sigma (u + v))]
  exact ofReal_tsum_squarefreeMobiusBoundaryLayerTerm sigma (u + v)

private theorem parityDamped_inner_term_eq_damped
    {sigma u v : ℝ} (n : ℕ) :
    infiniteMobiusCriticalParityDampedWeight sigma v n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalParityDampedWeight sigma u n) =
      infiniteMobiusCriticalDampedSignedWeight sigma v n *
          (starRingEnd ℂ)
            (infiniteMobiusCriticalDampedSignedWeight sigma u n) := by
  by_cases hsq : Squarefree n
  · have hmu :
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 2) = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    have hstar :
        (starRingEnd ℂ) (((ArithmeticFunction.moebius n : ℤ) : ℂ)) =
          (((ArithmeticFunction.moebius n : ℤ) : ℂ)) := by
      simp
    unfold infiniteMobiusCriticalParityDampedWeight
    rw [map_mul, hstar]
    rw [show
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            infiniteMobiusCriticalDampedSignedWeight sigma v n *
          (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
            (starRingEnd ℂ)
              (infiniteMobiusCriticalDampedSignedWeight sigma u n)) =
        (((ArithmeticFunction.moebius n : ℤ) : ℂ) ^ 2) *
          (infiniteMobiusCriticalDampedSignedWeight sigma v n *
            (starRingEnd ℂ)
              (infiniteMobiusCriticalDampedSignedWeight sigma u n)) by ring,
      hmu, one_mul]
  · rw [infiniteMobiusCriticalParityDampedWeight,
      infiniteMobiusCriticalParityDampedWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp [infiniteMobiusCriticalDampedSignedWeight, infiniteMobiusSignedWeight,
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- Möbius parity preserves every two-aperture likelihood inner product exactly. -/
theorem inner_infiniteMobiusCriticalParityDampedWeightLp_eq_damped
    {sigma u v : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    inner ℂ
        (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalParityDampedWeightLp sigma v hsigma hv) =
      inner ℂ
        (infiniteMobiusCriticalDampedSignedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalDampedSignedWeightLp sigma v hsigma hv) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [infiniteMobiusCriticalParityDampedWeightLp,
    infiniteMobiusCriticalDampedSignedWeightLp, RCLike.inner_apply]
  apply tsum_congr
  exact parityDamped_inner_term_eq_damped

/-- Exact finite-`sigma` parity likelihood Gram.  The parity gauge leaves the positive
squarefree boundary transform unchanged. -/
theorem inner_infiniteMobiusCriticalParityDampedWeightLp_eq_boundaryLayerLaplace
    {sigma u v : ℝ} (hsigma : 1 < sigma) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    inner ℂ
        (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu)
        (infiniteMobiusCriticalParityDampedWeightLp sigma v hsigma hv) =
      squarefreeMobiusBoundaryLayerLaplace sigma (u + v) := by
  rw [inner_infiniteMobiusCriticalParityDampedWeightLp_eq_damped
    hsigma hu hv]
  exact inner_infiniteMobiusCriticalDampedSignedWeightLp_eq_boundaryLayerLaplace
    hsigma hu hv

/-- The critical two-aperture parity Gram is the universal Cauchy value
`1 / (1 + u + v)`. -/
theorem tendsto_inner_infiniteMobiusCriticalParityDampedWeightLp
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Tendsto
      (fun sigma : ℝ =>
        if hsigma : 1 < sigma then
          inner ℂ
            (infiniteMobiusCriticalParityDampedWeightLp sigma u hsigma hu)
            (infiniteMobiusCriticalParityDampedWeightLp sigma v hsigma hv)
        else 0)
      (𝓝[>] (1 : ℝ))
      (𝓝 (((1 + u + v : ℝ) : ℂ)⁻¹)) := by
  have hlimit := tendsto_squarefreeMobiusBoundaryLayerLaplace
    (show 0 ≤ u + v by positivity)
  have htarget :
      (((1 + (u + v) : ℝ) : ℂ))⁻¹ =
        (((1 + u + v : ℝ) : ℂ))⁻¹ := by
    congr 2
    ring
  rw [← htarget]
  apply hlimit.congr'
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  change 1 < sigma at hsigma
  rw [dif_pos hsigma,
    inner_infiniteMobiusCriticalParityDampedWeightLp_eq_boundaryLayerLaplace
      hsigma hu hv]

/-- Real normal-cone nodes used by the critical parity likelihood family. -/
def mobiusParityHardyNode {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : ℂ :=
  ((u i + 1 / 2 : ℝ) : ℂ)

/-- The limiting parity likelihood Gram is exactly the right-half-plane Hardy Cauchy Gram. -/
theorem rightHalfPlaneHardyCauchyGram_mobiusParityHardyNode
    {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) :
    rightHalfPlaneHardyCauchyGram (mobiusParityHardyNode u) i j =
      (((1 + u i + u j : ℝ) : ℂ))⁻¹ := by
  change
    (1 / (((u i + 1 / 2 : ℝ) : ℂ) +
      (starRingEnd ℂ) (((u j + 1 / 2 : ℝ) : ℂ)))) =
        (((1 + u i + u j : ℝ) : ℂ))⁻¹
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- Hence every nonnegative real aperture packet has a positive semidefinite critical parity
likelihood Gram, with no target-divisor input. -/
theorem mobiusParityCriticalHardyGram_posSemidef
    {n : ℕ} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (rightHalfPlaneHardyCauchyGram (mobiusParityHardyNode u)).PosSemidef := by
  apply rightHalfPlaneHardyCauchyGram_posSemidef
  intro i
  rw [mobiusParityHardyNode, ofReal_re]
  linarith [hu i]

end

end RHTower
