import GaloisForLFunctions.RHTower.MobiusMertensSelfConvolutionCriterion

/-!
# Positive reversal-energy criterion for RH

The Mertens self-convolution is the difference between the `+1` and `-1` eigenspace energies of
finite coordinate reversal.  Dropping the nonnegative antisymmetric energy gives a positive
subpower criterion for RH.  The classical Mertens half-power family supplies that positive source.
-/

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- Energy of the palindromic (`+1` reversal) component of the finite Mertens vector. -/
def mobiusMertensPalindromicEnergy (N : ℕ) : ℝ :=
  (1 / 4 : ℝ) * ∑ ab ∈ Finset.antidiagonal N,
    ((mobiusMertensPartialSum ab.1).re + (mobiusMertensPartialSum ab.2).re) ^ 2

/-- Energy of the anti-palindromic (`-1` reversal) component. -/
def mobiusMertensAntipalindromicEnergy (N : ℕ) : ℝ :=
  (1 / 4 : ℝ) * ∑ ab ∈ Finset.antidiagonal N,
    ((mobiusMertensPartialSum ab.1).re - (mobiusMertensPartialSum ab.2).re) ^ 2

theorem mobiusMertensPalindromicEnergy_nonneg (N : ℕ) :
    0 ≤ mobiusMertensPalindromicEnergy N := by
  rw [mobiusMertensPalindromicEnergy]
  positivity

theorem mobiusMertensAntipalindromicEnergy_nonneg (N : ℕ) :
    0 ≤ mobiusMertensAntipalindromicEnergy N := by
  rw [mobiusMertensAntipalindromicEnergy]
  positivity

/-- Mertens partial sums are real. -/
theorem mobiusMertensPartialSum_im_eq_zero (N : ℕ) :
    (mobiusMertensPartialSum N).im = 0 := by
  simp [mobiusMertensPartialSum, mobiusComplexCoefficient]

/-- Exact reversal polarization of the Mertens self-convolution. -/
theorem mobiusMertensSelfConvolution_re_eq_palindromic_sub_antipalindromic (N : ℕ) :
    (mobiusMertensSelfConvolution N).re =
      mobiusMertensPalindromicEnergy N - mobiusMertensAntipalindromicEnergy N := by
  have hre : (mobiusMertensSelfConvolution N).re =
      ∑ ab ∈ Finset.antidiagonal N,
        (mobiusMertensPartialSum ab.1).re * (mobiusMertensPartialSum ab.2).re := by
    simp [mobiusMertensSelfConvolution, Complex.mul_re,
      mobiusMertensPartialSum_im_eq_zero]
  rw [hre, mobiusMertensPalindromicEnergy, mobiusMertensAntipalindromicEnergy]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _hab
  ring

/-- The second-Cesàro coefficient is bounded above by the positive palindromic energy. -/
theorem mobiusAdditiveTriangleSecondCesaro_re_le_palindromicEnergy (N : ℕ) :
    (mobiusAdditiveTriangleSecondCesaro N).re ≤ mobiusMertensPalindromicEnergy N := by
  rw [mobiusAdditiveTriangleSecondCesaro_eq_mobiusMertensSelfConvolution,
    mobiusMertensSelfConvolution_re_eq_palindromic_sub_antipalindromic]
  linarith [mobiusMertensAntipalindromicEnergy_nonneg N]

/-- Positive all-ε palindromic reversal-energy source. -/
def MobiusMertensPalindromicEnergySubpowerUpperBound : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
    mobiusMertensPalindromicEnergy N ≤ C * ((N : ℝ) + 1) ^ (2 + ε)

/-- Positive reversal-energy control implies the one-sided second-Cesàro source. -/
theorem mobiusMertensPalindromicEnergySubpowerUpperBound_implies_secondCesaroSubpowerUpperBound
    (henergy : MobiusMertensPalindromicEnergySubpowerUpperBound) :
    MobiusAdditiveTriangleSecondCesaroSubpowerUpperBound := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := henergy ε hε
  exact ⟨C, hC, fun N =>
    (mobiusAdditiveTriangleSecondCesaro_re_le_palindromicEnergy N).trans (hbound N)⟩

/-- **Positive reversal-energy criterion for RH.** -/
theorem mobiusMertensPalindromicEnergySubpowerUpperBound_implies_riemannHypothesis
    (henergy : MobiusMertensPalindromicEnergySubpowerUpperBound) :
    RiemannHypothesis :=
  mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis
    (mobiusMertensPalindromicEnergySubpowerUpperBound_implies_secondCesaroSubpowerUpperBound
      henergy)

/-- The classical Mertens all-strict-half-power source controls the positive reversal energy. -/
theorem mobiusMertensAllStrictHalfPowerBound_implies_palindromicEnergySubpowerUpperBound
    (hMertens : MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensPalindromicEnergySubpowerUpperBound := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨C, hC, hM⟩ := hMertens δ hδ
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro N
  let X : ℝ := (N : ℝ) + 1
  let θ : ℝ := (1 / 2 : ℝ) + δ
  have hX : 0 < X := by dsimp [X]; positivity
  have hθ : 0 ≤ θ := by dsimp [θ]; linarith
  have hpoint : ∀ ab ∈ Finset.antidiagonal N,
      ((mobiusMertensPartialSum ab.1).re + (mobiusMertensPartialSum ab.2).re) ^ 2 ≤
        (2 * C * X ^ θ) ^ 2 := by
    intro ab hab
    have habSum : ab.1 + ab.2 = N := Finset.mem_antidiagonal.mp hab
    have haN : ab.1 ≤ N := by omega
    have hbN : ab.2 ≤ N := by omega
    have haBase : (ab.1 : ℝ) + 1 ≤ X := by
      dsimp [X]
      exact_mod_cast Nat.add_le_add_right haN 1
    have hbBase : (ab.2 : ℝ) + 1 ≤ X := by
      dsimp [X]
      exact_mod_cast Nat.add_le_add_right hbN 1
    have haPow : ((ab.1 : ℝ) + 1) ^ θ ≤ X ^ θ :=
      Real.rpow_le_rpow (by positivity) haBase hθ
    have hbPow : ((ab.2 : ℝ) + 1) ^ θ ≤ X ^ θ :=
      Real.rpow_le_rpow (by positivity) hbBase hθ
    have haNorm : ‖mobiusMertensPartialSum ab.1‖ ≤ C * X ^ θ := by
      calc
        ‖mobiusMertensPartialSum ab.1‖ ≤
            C * ((ab.1 : ℝ) + 1) ^ θ := by simpa only [θ] using hM ab.1
        _ ≤ C * X ^ θ := mul_le_mul_of_nonneg_left haPow hC
    have hbNorm : ‖mobiusMertensPartialSum ab.2‖ ≤ C * X ^ θ := by
      calc
        ‖mobiusMertensPartialSum ab.2‖ ≤
            C * ((ab.2 : ℝ) + 1) ^ θ := by simpa only [θ] using hM ab.2
        _ ≤ C * X ^ θ := mul_le_mul_of_nonneg_left hbPow hC
    have haRe : |(mobiusMertensPartialSum ab.1).re| ≤ C * X ^ θ :=
      (Complex.abs_re_le_norm _).trans haNorm
    have hbRe : |(mobiusMertensPartialSum ab.2).re| ≤ C * X ^ θ :=
      (Complex.abs_re_le_norm _).trans hbNorm
    have hsum : |(mobiusMertensPartialSum ab.1).re +
        (mobiusMertensPartialSum ab.2).re| ≤ 2 * C * X ^ θ := by
      calc
        |(mobiusMertensPartialSum ab.1).re +
            (mobiusMertensPartialSum ab.2).re| ≤
              |(mobiusMertensPartialSum ab.1).re| +
              |(mobiusMertensPartialSum ab.2).re| := abs_add_le _ _
        _ ≤ C * X ^ θ + C * X ^ θ := add_le_add haRe hbRe
        _ = 2 * C * X ^ θ := by ring
    have hright : 0 ≤ 2 * C * X ^ θ := by positivity
    have hleft := abs_nonneg ((mobiusMertensPartialSum ab.1).re +
      (mobiusMertensPartialSum ab.2).re)
    nlinarith [sq_abs ((mobiusMertensPartialSum ab.1).re +
      (mobiusMertensPartialSum ab.2).re)]
  rw [mobiusMertensPalindromicEnergy]
  calc
    (1 / 4 : ℝ) * ∑ ab ∈ Finset.antidiagonal N,
        ((mobiusMertensPartialSum ab.1).re +
          (mobiusMertensPartialSum ab.2).re) ^ 2 ≤
      (1 / 4 : ℝ) * ∑ _ab ∈ Finset.antidiagonal N,
        (2 * C * X ^ θ) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro ab hab
      exact hpoint ab hab
    _ = (1 / 4 : ℝ) * ((N : ℝ) + 1) * (2 * C * X ^ θ) ^ 2 := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
      norm_cast
      ring
    _ = C ^ 2 * ((N : ℝ) + 1) ^ (2 + ε) := by
      have hδeq : 2 * δ = ε := by dsimp [δ]; ring
      rw [show (N : ℝ) + 1 = X by rfl]
      have hpow : X ^ θ * X ^ θ = X ^ (2 * θ) := by
        calc
          X ^ θ * X ^ θ = X ^ (θ + θ) := (Real.rpow_add hX _ _).symm
          _ = X ^ (2 * θ) := by congr 1; ring
      rw [show (2 * C * X ^ θ) ^ 2 = 4 * C ^ 2 * (X ^ θ * X ^ θ) by ring,
        hpow]
      have hθeq : 2 * θ = 1 + ε := by dsimp [θ, δ]; ring
      rw [hθeq]
      calc
        (1 / 4 : ℝ) * X * (4 * C ^ 2 * X ^ (1 + ε)) =
            C ^ 2 * (X ^ (1 : ℝ) * X ^ (1 + ε)) := by
          rw [Real.rpow_one]
          ring
        _ = C ^ 2 * X ^ ((1 : ℝ) + (1 + ε)) := by
          congr 1
          exact (Real.rpow_add hX _ _).symm
        _ = C ^ 2 * X ^ (2 + ε) := by ring

/-- Conditional exact equivalence interface after supplying classical Littlewood. -/
theorem mobiusMertensPalindromicEnergySubpowerUpperBound_iff_riemannHypothesis_of_mertens
    (hLittlewood : RiemannHypothesis → MobiusMertensAllStrictHalfPowerBound) :
    MobiusMertensPalindromicEnergySubpowerUpperBound ↔ RiemannHypothesis := by
  constructor
  · exact mobiusMertensPalindromicEnergySubpowerUpperBound_implies_riemannHypothesis
  · intro hRH
    exact mobiusMertensAllStrictHalfPowerBound_implies_palindromicEnergySubpowerUpperBound
      (hLittlewood hRH)

end

end RHTower
