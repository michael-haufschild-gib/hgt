/-
# Gaussian continuous large sieve in four dimensions

This file proves the continuous `L²` estimate used on the Fourier side of
the Bombieri--Iwaniec double large sieve.  A weighted finite exponential
sum is integrated against the self-dual product Gaussian.  Exact Fourier
inversion turns the integral into a Gaussian pair energy, and
`BourgainGaussianClustering` bounds it by the sharp normalized near-pair
energy.  A Gaussian majorant then controls the normalized four-cube.
-/
import GaloisForLFunctions.RHTower.BourgainGaussianClustering
import GaloisForLFunctions.RHTower.BourgainGaussianFourier

open MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Weighted finite exponential sum at frequencies `y`, evaluated at the
coordinatewise scaled point `L*x`. -/
def bourgainWeightedFourierSum
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ i : ι, b i *
    bourgainAdditiveCharacter (bourgainCoordinateScale L x) (y i)

def bourgainComplexGaussianL2Integrand
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) (x : BourgainPhaseSpace) : ℂ :=
  bourgainFourierGaussianWeight x *
    ((‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ) : ℝ) : ℂ)

theorem bourgainComplexGaussianL2Integrand_eq_pairSum
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) (x : BourgainPhaseSpace) :
    bourgainComplexGaussianL2Integrand L y b x =
      ∑ i : ι, ∑ j : ι,
        b i * (starRingEnd ℂ) (b j) *
          bourgainGaussianPairIntegrand L (y i) (y j) x := by
  let G : ℂ := bourgainFourierGaussianWeight x
  let A : ι → ℂ := fun i =>
    b i * bourgainAdditiveCharacter
      (bourgainCoordinateScale L x) (y i)
  have hpair (i j : ι) :
      b i * (starRingEnd ℂ) (b j) *
          bourgainGaussianPairIntegrand L (y i) (y j) x =
        G * (A i * (starRingEnd ℂ) (A j)) := by
    dsimp [G, A]
    rw [bourgainGaussianPairIntegrand_eq_character_sub,
      bourgainAdditiveCharacter_sub]
    rw [map_mul]
    ring
  have hnorm :
      (((‖∑ i : ι, A i‖ ^ (2 : ℕ) : ℝ) : ℂ)) =
        (∑ i : ι, A i) * (starRingEnd ℂ) (∑ i : ι, A i) := by
    symm
    simpa [mul_comm] using Complex.conj_mul' (∑ i : ι, A i)
  unfold bourgainComplexGaussianL2Integrand bourgainWeightedFourierSum
  change G * (((‖∑ i : ι, A i‖ ^ (2 : ℕ) : ℝ) : ℂ)) = _
  rw [hnorm, map_sum]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro j
  rw [hpair]

theorem integrable_bourgainComplexGaussianL2Integrand
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    Integrable (bourgainComplexGaussianL2Integrand L y b) := by
  apply (integrable_finsetSum
    (s := (Finset.univ : Finset ι)) fun i hi => ?_).congr
  · filter_upwards [] with x
    exact (bourgainComplexGaussianL2Integrand_eq_pairSum L y b x).symm
  · apply integrable_finsetSum
    intro j hj
    exact
      (integrable_bourgainGaussianPairIntegrand L (y i) (y j)).const_mul _

/-- Exact weighted Gaussian Fourier identity. -/
theorem integral_bourgainComplexGaussianL2Integrand
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    ∫ x : BourgainPhaseSpace,
        bourgainComplexGaussianL2Integrand L y b x =
      ∑ i : ι, ∑ j : ι,
        b i * (starRingEnd ℂ) (b j) *
          Real.exp (-Real.pi * bourgainScaledSqDist L (y i) (y j)) := by
  rw [show
      (fun x => bourgainComplexGaussianL2Integrand L y b x) =
        fun x => ∑ i : ι, ∑ j : ι,
          b i * (starRingEnd ℂ) (b j) *
            bourgainGaussianPairIntegrand L (y i) (y j) x by
    funext x
    exact bourgainComplexGaussianL2Integrand_eq_pairSum L y b x]
  rw [integral_finsetSum]
  · apply Fintype.sum_congr
    intro i
    rw [integral_finsetSum]
    · apply Fintype.sum_congr
      intro j
      rw [integral_const_mul]
      rw [integral_bourgainGaussianPairIntegrand]
    · intro j hj
      exact
        (integrable_bourgainGaussianPairIntegrand L (y i) (y j)).const_mul _
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact
      (integrable_bourgainGaussianPairIntegrand L (y i) (y j)).const_mul _

/-- Positive real product Gaussian. -/
def bourgainRealFourierGaussianWeight
    (x : BourgainPhaseSpace) : ℝ :=
  Real.exp (-Real.pi * ∑ j : Fin 4, x j ^ (2 : ℕ))

def bourgainRealGaussianL2Integrand
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) (x : BourgainPhaseSpace) : ℝ :=
  bourgainRealFourierGaussianWeight x *
    ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)

theorem bourgainRealFourierGaussianWeight_cast
    (x : BourgainPhaseSpace) :
    (bourgainRealFourierGaussianWeight x : ℂ) =
      bourgainFourierGaussianWeight x := by
  unfold bourgainRealFourierGaussianWeight bourgainFourierGaussianWeight
  rw [Complex.ofReal_exp, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem bourgainRealGaussianL2Integrand_cast
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) (x : BourgainPhaseSpace) :
    (bourgainRealGaussianL2Integrand L y b x : ℂ) =
      bourgainComplexGaussianL2Integrand L y b x := by
  unfold bourgainRealGaussianL2Integrand
    bourgainComplexGaussianL2Integrand
  push_cast
  rw [bourgainRealFourierGaussianWeight_cast]

theorem integrable_bourgainRealGaussianL2Integrand
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    Integrable (bourgainRealGaussianL2Integrand L y b) := by
  have hc := (integrable_bourgainComplexGaussianL2Integrand L y b).re
  apply hc.congr
  filter_upwards [] with x
  have hx := congrArg Complex.re
    (bourgainRealGaussianL2Integrand_cast L y b x)
  simpa using hx.symm

/-- The real Gaussian `L²` integral is bounded by the corresponding
positive Gaussian pair energy. -/
theorem integral_bourgainRealGaussianL2Integrand_le
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand L y b x) ≤
      bourgainWeightedGaussianEnergy L y (fun i => ‖b i‖) := by
  let I : ℝ := ∫ x : BourgainPhaseSpace,
    bourgainRealGaussianL2Integrand L y b x
  have hI0 : 0 ≤ I := by
    exact integral_nonneg fun x => by
      unfold bourgainRealGaussianL2Integrand
        bourgainRealFourierGaussianWeight
      positivity
  have hcast :
      (I : ℂ) =
        ∑ i : ι, ∑ j : ι,
          b i * (starRingEnd ℂ) (b j) *
            Real.exp
              (-Real.pi * bourgainScaledSqDist L (y i) (y j)) := by
    calc
      (I : ℂ) =
          ∫ x : BourgainPhaseSpace,
            (bourgainRealGaussianL2Integrand L y b x : ℂ) := by
        unfold I
        exact
          (integral_ofReal
            (X := BourgainPhaseSpace) (μ := volume)
            (𝕜 := ℂ)
            (f := bourgainRealGaussianL2Integrand L y b)).symm
      _ = ∫ x : BourgainPhaseSpace,
          bourgainComplexGaussianL2Integrand L y b x := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact bourgainRealGaussianL2Integrand_cast L y b x
      _ = _ := integral_bourgainComplexGaussianL2Integrand L y b
  calc
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand L y b x) = ‖(I : ℂ)‖ := by
      unfold I
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hI0]
    _ = ‖∑ i : ι, ∑ j : ι,
          b i * (starRingEnd ℂ) (b j) *
            Real.exp
              (-Real.pi * bourgainScaledSqDist L (y i) (y j))‖ := by
      rw [hcast]
    _ ≤ ∑ i : ι,
        ‖∑ j : ι,
          b i * (starRingEnd ℂ) (b j) *
            Real.exp
              (-Real.pi * bourgainScaledSqDist L (y i) (y j))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : ι, ∑ j : ι,
        ‖b i * (starRingEnd ℂ) (b j) *
          Real.exp
            (-Real.pi * bourgainScaledSqDist L (y i) (y j))‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ = bourgainWeightedGaussianEnergy L y (fun i => ‖b i‖) := by
      unfold bourgainWeightedGaussianEnergy
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hstar :
          ‖(starRingEnd ℂ) (b j)‖ = ‖b j‖ := by
        simp
      rw [norm_mul, norm_mul, hstar, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring

theorem integral_bourgainRealGaussianL2Integrand_le_scaledNear
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    (∫ x : BourgainPhaseSpace,
        bourgainRealGaussianL2Integrand L y b x) ≤
      331776 *
        bourgainWeightedScaledNearEnergy L y (fun i => ‖b i‖) := by
  calc
    _ ≤ bourgainWeightedGaussianEnergy L y (fun i => ‖b i‖) :=
      integral_bourgainRealGaussianL2Integrand_le L y b
    _ ≤ _ :=
      bourgainWeightedGaussianEnergy_le_scaledNearEnergy
        L y (fun i => ‖b i‖) (fun i => norm_nonneg _)

/-- Normalized four-dimensional cube. -/
def bourgainFourCube : Set BourgainPhaseSpace :=
  {x | ‖x‖ ≤ 1}

/-- The normalized cube `L²` norm is bounded by the Gaussian `L²` norm. -/
theorem integral_bourgainFourCube_l2_le_gaussian
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    (∫ x in bourgainFourCube,
        ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)) ≤
      Real.exp (4 * Real.pi) *
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand L y b x) := by
  let f : BourgainPhaseSpace → ℝ :=
    fun x => ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)
  have hfcont : Continuous f := by
    unfold f bourgainWeightedFourierSum bourgainAdditiveCharacter
      bourgainCoordinateScale bourgainDot
    fun_prop
  have hcube :
      bourgainFourCube =
        Metric.closedBall (0 : BourgainPhaseSpace) 1 := by
    ext x
    simp [bourgainFourCube, Metric.mem_closedBall, dist_zero_right]
  have hfint : IntegrableOn f bourgainFourCube := by
    rw [hcube]
    exact hfcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : BourgainPhaseSpace) 1)
  have hcubeMeas : MeasurableSet bourgainFourCube := by
    unfold bourgainFourCube
    exact measurableSet_Iic.preimage continuous_norm.measurable
  have hweighted :
      Integrable (fun x : BourgainPhaseSpace =>
        Real.exp (4 * Real.pi) *
          bourgainRealGaussianL2Integrand L y b x) :=
    (integrable_bourgainRealGaussianL2Integrand L y b).const_mul _
  have hpoint (x : BourgainPhaseSpace) (hx : x ∈ bourgainFourCube) :
      f x ≤ Real.exp (4 * Real.pi) *
        bourgainRealGaussianL2Integrand L y b x := by
    have hxcoord (j : Fin 4) : |x j| ≤ 1 := by
      have hj :=
        (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mp hx j
      simpa [Real.norm_eq_abs] using hj
    have hsq (j : Fin 4) : x j ^ (2 : ℕ) ≤ 1 := by
      have hnonneg : 0 ≤ |x j| := abs_nonneg _
      calc
        x j ^ (2 : ℕ) = |x j| ^ (2 : ℕ) := (sq_abs (x j)).symm
        _ ≤ (1 : ℝ) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hnonneg (hxcoord j) 2
        _ = 1 := by norm_num
    have hsum : (∑ j : Fin 4, x j ^ (2 : ℕ)) ≤ 4 := by
      calc
        (∑ j : Fin 4, x j ^ (2 : ℕ)) ≤ ∑ _j : Fin 4, (1 : ℝ) :=
          Finset.sum_le_sum fun j hj => hsq j
        _ = 4 := by norm_num
    have hone :
        1 ≤ Real.exp (4 * Real.pi) *
          bourgainRealFourierGaussianWeight x := by
      unfold bourgainRealFourierGaussianWeight
      rw [← Real.exp_zero, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_pos]
    unfold f bourgainRealGaussianL2Integrand
    calc
      ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ) =
          1 * ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ) := by
            ring
      _ ≤ (Real.exp (4 * Real.pi) *
            bourgainRealFourierGaussianWeight x) *
          ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hone (sq_nonneg _)
      _ = Real.exp (4 * Real.pi) *
          (bourgainRealFourierGaussianWeight x *
            ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)) := by
              ring
  calc
    (∫ x in bourgainFourCube,
        ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)) =
        ∫ x in bourgainFourCube, f x := by rfl
    _ ≤ ∫ x in bourgainFourCube,
        Real.exp (4 * Real.pi) *
          bourgainRealGaussianL2Integrand L y b x := by
      apply integral_mono_ae hfint
        (hweighted.mono_measure Measure.restrict_le_self)
      filter_upwards [ae_restrict_mem hcubeMeas] with x hx
      exact hpoint x hx
    _ ≤ ∫ x : BourgainPhaseSpace,
        Real.exp (4 * Real.pi) *
          bourgainRealGaussianL2Integrand L y b x := by
      exact setIntegral_le_integral hweighted
        (Filter.Eventually.of_forall fun x => by
          apply mul_nonneg (Real.exp_pos _).le
          unfold bourgainRealGaussianL2Integrand
            bourgainRealFourierGaussianWeight
          positivity)
    _ = Real.exp (4 * Real.pi) *
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand L y b x) := by
      rw [integral_const_mul]

/-- Continuous Gaussian large sieve on the normalized four-cube. -/
theorem integral_bourgainFourCube_l2_le_scaledNear
    {ι : Type*} [Fintype ι]
    (L : BourgainPhaseSpace) (y : ι → BourgainPhaseSpace)
    (b : ι → ℂ) :
    (∫ x in bourgainFourCube,
        ‖bourgainWeightedFourierSum L y b x‖ ^ (2 : ℕ)) ≤
      (Real.exp (4 * Real.pi) * 331776) *
        bourgainWeightedScaledNearEnergy L y (fun i => ‖b i‖) := by
  calc
    _ ≤ Real.exp (4 * Real.pi) *
        (∫ x : BourgainPhaseSpace,
          bourgainRealGaussianL2Integrand L y b x) :=
      integral_bourgainFourCube_l2_le_gaussian L y b
    _ ≤ Real.exp (4 * Real.pi) *
        (331776 *
          bourgainWeightedScaledNearEnergy L y (fun i => ‖b i‖)) := by
      gcongr
      exact
        integral_bourgainRealGaussianL2Integrand_le_scaledNear L y b
    _ = _ := by ring

end

end RHTower
