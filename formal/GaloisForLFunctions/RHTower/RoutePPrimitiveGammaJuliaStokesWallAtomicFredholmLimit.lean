import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallFredholmCoefficientLimit
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# P-G105X: atomic SP-E Fredholm bridge and locally uniform wall limit

The quantile Fredholm coefficients from P-G105W are identified exactly with the complete
ordered prime-tuple determinant expansion of the normalized Stokes child.  The proof pushes the
atomic prime PMF and the unit-cube quantile law to the same finite product wall law.  Repeated
prime tuples are not discarded: they remain inside the complete signed-permutation determinant.

Hadamard's bound gives one summable majorant for every aperture and every point of a closed disc.
Consequently the full factorial-normalized Fredholm series converges for every complex parameter,
and its aperture-wall limit is uniform on every closed disc.  No determinant order, permutation,
or cross-prime incidence is truncated.

Identification with the existing cofinal child ordinary determinant and the physical squared-child
determinant remains a separate gate.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

local instance : MeasurableSpace Nat.Primes := ⊤

def routePPrimitiveGammaJuliaStokesWallPrimePMF (d : ℝ) (hd : 0 < d) : PMF Nat.Primes := by
  refine ⟨fun p => ENNReal.ofReal
    (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p), ?_⟩
  apply ENNReal.hasSum_coe.mpr
  rw [← ENNReal.toNNReal_one]
  have hsum : HasSum
      (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d) 1 := by
    rw [← tsum_wallNormalizedWeight hd]
    exact (summable_wallNormalizedWeight hd).hasSum
  simpa using hsum.toNNReal (wallNormalizedWeight_nonneg hd)

theorem routePPrimitiveGammaJuliaStokesWallPrimePMF_toReal
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    (routePPrimitiveGammaJuliaStokesWallPrimePMF d hd p).toReal =
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p := by
  change (ENNReal.ofReal
    (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p)).toReal = _
  rw [ENNReal.toReal_ofReal (wallNormalizedWeight_nonneg hd p)]

def routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF
    (d : ℝ) (hd : 0 < d) (n : ℕ) : PMF (Fin n → Nat.Primes) :=
  (Measure.pi (fun _ : Fin n => (routePPrimitiveGammaJuliaStokesWallPrimePMF d hd).toMeasure)).toPMF

theorem routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_toReal
    {d : ℝ} (hd : 0 < d) (n : ℕ) (a : Fin n → Nat.Primes) :
    (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n a).toReal =
      ∏ i : Fin n,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i) := by
  rw [routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF, Measure.toPMF_apply,
    ← Set.univ_pi_singleton, Measure.pi_pi]
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  exact routePPrimitiveGammaJuliaStokesWallPrimePMF_toReal hd (a i)

def routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix
    (n : ℕ) (a : Fin n → Nat.Primes) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (routePPrimitiveGammaJuliaStokesWallCubicKernel
    (Real.log (a i : ℝ)) (Real.log (a j : ℝ)) : ℂ)

def routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
    (n : ℕ) (a : Fin n → Nat.Primes) : ℂ :=
  Matrix.det (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a)

theorem norm_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_le
    (n : ℕ) (a : Fin n → Nat.Primes) :
    ‖routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a‖ ≤ (Real.sqrt n) ^ n := by
  unfold routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
  refine (ContinuousKernelFredholm.complex_hadamard_entry_bound
    (routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix n a) (M := 1) ?_).trans_eq ?_
  · intro i j
    have hi : (1 : ℝ) < (a i : ℝ) := by
      exact_mod_cast (a i).property.one_lt
    have hj : (1 : ℝ) < (a j : ℝ) := by
      exact_mod_cast (a j).property.one_lt
    have h := routePPrimitiveGammaJuliaStokesWallCubicKernel_zero_le_one
      (Real.log_pos hi).le (Real.log_pos hj).le
    rw [routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg h.1]
    exact h.2
  · ring

theorem integrable_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Integrable (routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n)
      (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure := by
  apply Integrable.mono' (integrable_const ((Real.sqrt n) ^ n))
    (measurable_of_countable
      (routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n)).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun a =>
    norm_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_le n a

theorem integral_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_eq_tsum
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (∫ a : Fin n → Nat.Primes, routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a
        ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure) =
      ∑' a : Fin n → Nat.Primes,
        (∏ i : Fin n,
          routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
          routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a := by
  rw [PMF.integral_eq_tsum _ _
    (integrable_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand hd n)]
  apply tsum_congr
  intro a
  rw [routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_toReal hd n a]
  rw [Complex.real_smul, Complex.ofReal_prod]

theorem map_routePPrimitiveGammaJuliaStokesWallPrimePMF_wallLogCoordinate
    {d : ℝ} (hd : 0 < d) :
    Measure.map (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
        (routePPrimitiveGammaJuliaStokesWallPrimePMF d hd).toMeasure =
      routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d := by
  ext s hs
  rw [Measure.map_apply (measurable_of_countable _) hs,
    (routePPrimitiveGammaJuliaStokesWallPrimePMF d hd).toMeasure_apply MeasurableSet.of_discrete,
    routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw,
    GaloisForLFunctions.HTGeometry.weightedPointLaw_apply _ _ hs]
  apply tsum_congr
  intro p
  by_cases hp : routePPrimitiveGammaJuliaStokesWallLogCoordinate d p ∈ s
  · rw [Set.indicator_of_mem (show p ∈
        routePPrimitiveGammaJuliaStokesWallLogCoordinate d ⁻¹' s from hp)]
    rw [Set.indicator_of_mem hp]
    rfl
  · rw [Set.indicator_of_notMem (show p ∉
        routePPrimitiveGammaJuliaStokesWallLogCoordinate d ⁻¹' s from hp)]
    rw [Set.indicator_of_notMem hp]

theorem map_routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_wallLogCoordinate
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Measure.map
        (fun a : Fin n → Nat.Primes => fun i =>
          routePPrimitiveGammaJuliaStokesWallLogCoordinate d (a i))
        (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure =
      Measure.pi (fun _ : Fin n =>
        routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  rw [routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF, Measure.toPMF_toMeasure,
    Measure.pi_map_pi]
  · congr 1
    funext i
    exact map_routePPrimitiveGammaJuliaStokesWallPrimePMF_wallLogCoordinate hd
  · intro i
    exact (measurable_of_countable _).aemeasurable

theorem map_routePPrimitiveGammaJuliaStokesWallUnitCube_quantile_eq_pi_wallRaw
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    Measure.map
        (fun x : Fin n → ℝ => fun i =>
          GaloisForLFunctions.HTGeometry.quantile
            (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) (x i))
        (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) =
      Measure.pi (fun _ : Fin n =>
        routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  rw [routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure,
    Measure.pi_map_pi]
  · congr 1
    funext i
    exact GaloisForLFunctions.HTGeometry.map_quantile_eq
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)
  · intro i
    exact (GaloisForLFunctions.HTGeometry.measurable_quantile
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)).aemeasurable

def routePPrimitiveGammaJuliaStokesWallRealFredholmMatrix
    (n : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (routePPrimitiveGammaJuliaStokesWallCubicKernel (x i) (x j) : ℂ)

def routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand
    (n : ℕ) (x : Fin n → ℝ) : ℂ :=
  Matrix.det (routePPrimitiveGammaJuliaStokesWallRealFredholmMatrix n x)

def routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand
    (n : ℕ) (x : Fin n → ℝ) : ℂ :=
  routePPrimitiveGammaJuliaStokesWallFredholmIntegrand (expMeasure 1) n
    (fun i => 1 - Real.exp (-(x i)))

theorem measurable_routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand (n : ℕ) :
    Measurable (routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  apply (measurable_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    (expMeasure 1) n).comp
  apply measurable_pi_lambda
  intro i
  exact measurable_const.sub
    (Real.measurable_exp.comp (measurable_pi_apply i).neg)

theorem routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand_eq_real
    (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n x =
      routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand n x := by
  unfold routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand
    routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
    routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand
  apply congrArg Matrix.det
  ext i j
  unfold routePPrimitiveGammaJuliaStokesWallFredholmMatrix
    routePPrimitiveGammaJuliaStokesWallQuantileKernel
    routePPrimitiveGammaJuliaStokesWallRealFredholmMatrix
  by_cases hi : x i = 0
  · simp [hi, routePPrimitiveGammaJuliaStokesWallCubicKernel]
  by_cases hj : x j = 0
  · simp [hj, routePPrimitiveGammaJuliaStokesWallCubicKernel]
  have hipos : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
  have hjpos : 0 < x j := lt_of_le_of_ne (hx j) (Ne.symm hj)
  have hi0 : 0 < 1 - Real.exp (-(x i)) := by
    rw [sub_pos]
    exact (Real.exp_lt_one_iff.mpr (by linarith [hipos]))
  have hi1 : 1 - Real.exp (-(x i)) < 1 := by
    linarith [Real.exp_pos (-(x i))]
  have hj0 : 0 < 1 - Real.exp (-(x j)) := by
    rw [sub_pos]
    exact (Real.exp_lt_one_iff.mpr (by linarith [hjpos]))
  have hj1 : 1 - Real.exp (-(x j)) < 1 := by
    linarith [Real.exp_pos (-(x j))]
  rw [if_pos ⟨⟨hi0, hi1⟩, ⟨hj0, hj1⟩⟩]
  rw [GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hi0 hi1,
    GaloisForLFunctions.HTGeometry.quantile_expMeasure_one hj0 hj1]
  simp

theorem ae_routePPrimitiveGammaJuliaStokesWallUnitCube_all_mem_Ioo (n : ℕ) :
    ∀ᵐ x ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n,
      ∀ i : Fin n, x i ∈ Ioo (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro i
  exact (Measure.quasiMeasurePreserving_eval
    (fun _ : Fin n => volume.restrict (Ioo (0 : ℝ) 1)) i).ae
      (ae_restrict_mem measurableSet_Ioo)

theorem routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_comp_quantile
    {d : ℝ} (hd : 0 < d) (n : ℕ) (x : Fin n → ℝ)
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) n x =
      routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n
        (fun i => GaloisForLFunctions.HTGeometry.quantile
          (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) (x i)) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  let y : Fin n → ℝ := fun i =>
    GaloisForLFunctions.HTGeometry.quantile
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) (x i)
  have hy : ∀ i, 0 ≤ y i := fun i =>
    GaloisForLFunctions.HTGeometry.quantile_nonneg
      (wallHalfLineLawRaw_Iio_zero hd) (hx i).1 (hx i).2
  calc
    routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) n x =
        routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand n y := by
      unfold routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
        routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand
      apply congrArg Matrix.det
      ext i j
      unfold routePPrimitiveGammaJuliaStokesWallFredholmMatrix
        routePPrimitiveGammaJuliaStokesWallQuantileKernel
        routePPrimitiveGammaJuliaStokesWallRealFredholmMatrix
      rw [if_pos ⟨hx i, hx j⟩]
    _ = routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y :=
      (routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand_eq_real n y hy).symm

theorem integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_pi_wallRaw
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (∫ x : Fin n → ℝ,
        routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
          (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) n x
        ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) =
      ∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
        ∂Measure.pi (fun _ : Fin n =>
          routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  let Q : (Fin n → ℝ) → (Fin n → ℝ) := fun x i =>
    GaloisForLFunctions.HTGeometry.quantile
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) (x i)
  have hQ : Measurable Q := by
    apply measurable_pi_lambda
    intro i
    exact (GaloisForLFunctions.HTGeometry.measurable_quantile
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)).comp
        (measurable_pi_apply i)
  calc
    (∫ x : Fin n → ℝ,
        routePPrimitiveGammaJuliaStokesWallFredholmIntegrand
          (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) n x
        ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) =
        ∫ x : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n (Q x)
          ∂routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n := by
      apply integral_congr_ae
      filter_upwards [ae_routePPrimitiveGammaJuliaStokesWallUnitCube_all_mem_Ioo n] with x hx
      exact routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_comp_quantile hd n x hx
    _ = ∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
          ∂Measure.map Q
            (routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n) := by
      symm
      exact integral_map_of_stronglyMeasurable hQ
        (measurable_routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n).stronglyMeasurable
    _ = ∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
          ∂Measure.pi (fun _ : Fin n =>
            routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
      rw [show Q = fun x : Fin n → ℝ => fun i =>
          GaloisForLFunctions.HTGeometry.quantile
            (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) (x i) by rfl,
        map_routePPrimitiveGammaJuliaStokesWallUnitCube_quantile_eq_pi_wallRaw hd n]

theorem routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand_wallLogCoordinate
    {d : ℝ} (hd : 0 < d) (n : ℕ) (a : Fin n → Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n
        (fun i => routePPrimitiveGammaJuliaStokesWallLogCoordinate d (a i)) =
      routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a := by
  rw [routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand_eq_real n _
    (fun i => (wallLogCoordinate_pos hd (a i)).le)]
  unfold routePPrimitiveGammaJuliaStokesWallRealFredholmIntegrand
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
  apply congrArg Matrix.det
  ext i j
  unfold routePPrimitiveGammaJuliaStokesWallRealFredholmMatrix routePPrimitiveGammaJuliaStokesWallPrimeFredholmMatrix
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel_logCoordinate_eq_primeLog
    hd (a i) (a j)]

theorem integral_routePPrimitiveGammaJuliaStokesWallPositive_pi_wallRaw_eq_primeFredholmIntegrand
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
        ∂Measure.pi (fun _ : Fin n =>
          routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)) =
      ∫ a : Fin n → Nat.Primes, routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a
        ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure := by
  let W : (Fin n → Nat.Primes) → (Fin n → ℝ) := fun a i =>
    routePPrimitiveGammaJuliaStokesWallLogCoordinate d (a i)
  have hW : Measurable W := measurable_of_countable _
  calc
    (∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
        ∂Measure.pi (fun _ : Fin n =>
          routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)) =
        ∫ y : Fin n → ℝ, routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n y
          ∂Measure.map W (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure := by
      rw [show W = fun a : Fin n → Nat.Primes => fun i =>
          routePPrimitiveGammaJuliaStokesWallLogCoordinate d (a i) by rfl,
        map_routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_wallLogCoordinate hd n]
    _ = ∫ a : Fin n → Nat.Primes,
          routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n (W a)
          ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure :=
      integral_map_of_stronglyMeasurable hW
        (measurable_routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand n).stronglyMeasurable
    _ = ∫ a : Fin n → Nat.Primes, routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a
          ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a =>
        routePPrimitiveGammaJuliaStokesWallPositiveFredholmIntegrand_wallLogCoordinate hd n a

theorem routePPrimitiveGammaJuliaStokesWallRawFredholmCoefficient_eq_orderedPrimeTuple_tsum
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) n =
      (∑' a : Fin n → Nat.Primes,
        (∏ i : Fin n,
          routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
          routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a) /
        (n.factorial : ℂ) := by
  unfold routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
  rw [integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_pi_wallRaw hd n,
    integral_routePPrimitiveGammaJuliaStokesWallPositive_pi_wallRaw_eq_primeFredholmIntegrand hd n,
    integral_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_eq_tsum hd n]

theorem routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_eq_orderedPrimeTuple_tsum
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n =
      (∑' a : Fin n → Nat.Primes,
        (∏ i : Fin n,
          routePPrimitiveGammaJuliaStokesWallNormalizedWeight d (a i)) *
          routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a) /
        (n.factorial : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd]
  exact routePPrimitiveGammaJuliaStokesWallRawFredholmCoefficient_eq_orderedPrimeTuple_tsum hd n

theorem routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ (n : ℕ) :
    routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n Set.univ = 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure, Measure.pi_univ]
  simp [Real.volume_Ioo]

theorem norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (n : ℕ) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n‖ ≤
      (Real.sqrt n) ^ n / (n.factorial : ℝ) := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n.factorial)
  have h := norm_integral_le_of_norm_le_const
    (μ := routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure n)
    (Filter.Eventually.of_forall fun x =>
      norm_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_le
        μ hsupp n x)
  simpa [Measure.real, routePPrimitiveGammaJuliaStokesWallUnitCubeMeasure_apply_univ] using h

def routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (μ : Measure ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n *
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n

theorem summable_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    (z : ℂ) :
    Summable (fun n : ℕ => z ^ n *
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n) := by
  apply Summable.of_norm_bounded
    (ContinuousKernelFredholm.summable_hadamard_majorant ‖z‖ (norm_nonneg z))
  intro n
  rw [norm_mul, norm_pow]
  calc
    ‖z‖ ^ n *
        ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n‖ ≤
        ‖z‖ ^ n * ((Real.sqrt n) ^ n / (n.factorial : ℝ)) := by
      gcongr
      exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le μ hsupp n
    _ = (Real.sqrt n * ‖z‖) ^ n / (n.factorial : ℝ) := by ring

theorem tendsto_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero (z : ℂ) :
    Tendsto
      (fun d : ℝ => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z)) := by
  unfold routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
  apply tendsto_tsum_of_dominated_convergence
    (ContinuousKernelFredholm.summable_hadamard_majorant ‖z‖ (norm_nonneg z))
  · intro n
    exact tendsto_const_nhds.mul
      (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero n)
  · exact Filter.Eventually.of_forall fun d n => by
      rw [norm_mul, norm_pow]
      calc
        ‖z‖ ^ n * ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n‖ ≤
            ‖z‖ ^ n * ((Real.sqrt n) ^ n / (n.factorial : ℝ)) := by
          gcongr
          exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
            (wallHalfLineLaw_Iio_zero d) n
        _ = (Real.sqrt n * ‖z‖) ^ n / (n.factorial : ℝ) := by ring

def routePPrimitiveGammaJuliaStokesWallFredholmMajorant (rho : ℝ) (n : ℕ) : ℝ :=
  (Real.sqrt n * rho) ^ n / (n.factorial : ℝ)

theorem summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Summable (routePPrimitiveGammaJuliaStokesWallFredholmMajorant rho) :=
  ContinuousKernelFredholm.summable_hadamard_majorant rho hrho

theorem norm_routePPrimitiveGammaJuliaStokesWallFredholmTerm_le_majorant
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hsupp : μ (Iio 0) = 0)
    {rho : ℝ} (hrho : 0 ≤ rho) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) rho) (n : ℕ) :
    ‖z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n‖ ≤
      routePPrimitiveGammaJuliaStokesWallFredholmMajorant rho n := by
  have hznorm : ‖z‖ ≤ rho := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  rw [norm_mul, norm_pow]
  calc
    ‖z‖ ^ n * ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient μ n‖ ≤
        rho ^ n * ((Real.sqrt n) ^ n / (n.factorial : ℝ)) := by
      gcongr
      exact norm_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_le μ hsupp n
    _ = routePPrimitiveGammaJuliaStokesWallFredholmMajorant rho n := by
      unfold routePPrimitiveGammaJuliaStokesWallFredholmMajorant
      ring

theorem tendstoUniformlyOn_routePPrimitiveGammaJuliaStokesWallFredholmEntireDet_nhdsGT_zero
    {rho : ℝ} (hrho : 0 ≤ rho) :
    TendstoUniformlyOn
      (fun d z => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1))
      (𝓝[>] (0 : ℝ)) (Metric.closedBall 0 rho) := by
  letI : IsProbabilityMeasure (expMeasure 1) :=
    isProbabilityMeasure_expMeasure one_pos
  let u : ℕ → ℝ := routePPrimitiveGammaJuliaStokesWallFredholmMajorant rho
  have hu : Summable u := summable_routePPrimitiveGammaJuliaStokesWallFredholmMajorant hrho
  have hsource : TendstoUniformlyOn
      (fun N : ℕ => fun p : ℝ × ℂ =>
        ∑ n ∈ Finset.range N,
          p.2 ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw p.1) n)
      (fun p : ℝ × ℂ => routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw p.1) p.2)
      atTop (Set.univ ×ˢ Metric.closedBall 0 rho) := by
    simpa [routePPrimitiveGammaJuliaStokesWallFredholmEntireDet] using
      (tendstoUniformlyOn_tsum_nat hu
        (s := Set.univ ×ˢ Metric.closedBall 0 rho)
        (f := fun (n : ℕ) (p : ℝ × ℂ) =>
          p.2 ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw p.1) n)
        (fun n p hp => norm_routePPrimitiveGammaJuliaStokesWallFredholmTerm_le_majorant
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw p.1)
          (wallHalfLineLaw_Iio_zero p.1) hrho hp.2 n))
  have htarget : TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1))
      atTop (Metric.closedBall 0 rho) := by
    change TendstoUniformlyOn
      (fun N : ℕ => fun z : ℂ =>
        ∑ n ∈ Finset.range N,
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
      (fun z : ℂ => ∑' n : ℕ,
        z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (expMeasure 1) n)
      atTop (Metric.closedBall 0 rho)
    exact
      (tendstoUniformlyOn_tsum_nat hu
        (s := Metric.closedBall (0 : ℂ) rho)
        (f := fun (n : ℕ) (z : ℂ) =>
          z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
            (expMeasure 1) n)
        (fun n z hz => norm_routePPrimitiveGammaJuliaStokesWallFredholmTerm_le_majorant
          (expMeasure 1) GaloisForLFunctions.HTGeometry.expMeasure_one_Iio_zero
          hrho hz n))
  rw [Metric.tendstoUniformlyOn_iff] at hsource htarget ⊢
  intro eps heps
  have heps3 : 0 < eps / 3 := by positivity
  have hs := hsource (eps / 3) heps3
  have ht := htarget (eps / 3) heps3
  obtain ⟨N, hNs, hNt⟩ := (hs.and ht).exists
  let E : ℝ → ℝ := fun d =>
    ∑ n ∈ Finset.range N, rho ^ n *
      ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n -
        routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n‖
  have hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    unfold E
    have hsum : Tendsto
        (fun d : ℝ =>
          ∑ n ∈ Finset.range N, rho ^ n *
            ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n -
              routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
                (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n‖)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∑ _n ∈ Finset.range N, (0 : ℝ))) := by
      apply tendsto_finsetSum (Finset.range N)
      intro n hn
      have hc : Tendsto
          (fun d : ℝ =>
            routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n -
              routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
                (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n)
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hconst : Tendsto
            (fun _d : ℝ =>
              routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n)
            (𝓝[>] (0 : ℝ))
            (𝓝 (routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
              (expMeasure 1) n)) := tendsto_const_nhds
        simpa using hconst.sub
          (tendsto_routePPrimitiveGammaJuliaStokesWallFredholmCoefficient_nhdsGT_zero n)
      simpa using tendsto_const_nhds.mul (tendsto_norm.comp hc)
    simpa using hsum
  filter_upwards [hE.eventually (Metric.ball_mem_nhds 0 heps3)] with d hdE
  have hElt : E d < eps / 3 := by
    rw [Real.dist_eq] at hdE
    simp only [sub_zero] at hdE
    exact (le_abs_self (E d)).trans_lt hdE
  intro z hz
  let targetHead : ℂ := ∑ n ∈ Finset.range N,
    z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n
  let sourceHead : ℂ := ∑ n ∈ Finset.range N,
    z ^ n * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n
  have htargetTail : dist
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z) targetHead < eps / 3 := by
    simpa [targetHead, dist_comm] using hNt z hz
  have hsourceTail : dist sourceHead
      (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z) < eps / 3 := by
    simpa [sourceHead, dist_comm] using hNs (d, z) ⟨Set.mem_univ d, hz⟩
  have hhead : dist targetHead sourceHead ≤ E d := by
    rw [dist_eq_norm]
    calc
      ‖targetHead - sourceHead‖ =
          ‖∑ n ∈ Finset.range N, z ^ n *
            (routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n -
              routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
                (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n)‖ := by
        congr 1
        unfold targetHead sourceHead
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ ∑ n ∈ Finset.range N,
          ‖z ^ n *
            (routePPrimitiveGammaJuliaStokesWallFredholmCoefficient (expMeasure 1) n -
              routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
                (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n)‖ :=
        norm_sum_le _ _
      _ ≤ E d := by
        unfold E
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul, norm_pow]
        gcongr
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
  calc
    dist (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z)
        (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z) ≤
        dist (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet (expMeasure 1) z) targetHead +
          dist targetHead sourceHead +
          dist sourceHead (routePPrimitiveGammaJuliaStokesWallFredholmEntireDet
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) z) :=
      dist_triangle4 _ _ _ _
    _ < eps / 3 + eps / 3 + eps / 3 := by
      gcongr
      exact hhead.trans_lt hElt
    _ = eps := by ring

end
end RHTower
