import GaloisForLFunctions.RHTower.VonMangoldtGammaBivariateMoment
import GaloisForLFunctions.HTGeometry.MomentHankelStrict
import GaloisForLFunctions.HTGeometry.PositiveReweightingSupport

/-!
# Strict Hankel law for the von Mangoldt--Gamma bivariate moments

Every Taylor-remainder channel has a strictly positive density on the unit interval.  Hence a
nonzero positive source channel makes the representing Hausdorff measure charge the complement
of every finite set.  The bivariate moment rows are therefore not merely Hankel positive
semidefinite: every finite Hankel block is positive definite and has positive determinant.

For the actual finite von Mangoldt source, any nonempty aperture contains the `2`-channel, whose
weight and logarithmic rate are strictly positive.  Thus strictness holds at every rate degree,
every real displacement, and every finite Hankel size.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- A Taylor-remainder channel charges the complement of every finite set. -/
theorem exponentialRemainderMeasure_infiniteSupport
    (rate : ℝ) (F : Finset ℝ) :
    0 < exponentialRemainderMeasure rate {u : ℝ | u ∉ F} := by
  let base : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  have hbase : 0 < base {u : ℝ | u ∉ F} := by
    have hFzero : volume (↑F : Set ℝ) = 0 :=
      F.finite_toSet.measure_zero volume
    change 0 < (volume.restrict (Ioc (0 : ℝ) 1)) ((↑F : Set ℝ)ᶜ)
    rw [Measure.restrict_apply F.measurableSet.compl]
    have hset : (↑F : Set ℝ)ᶜ ∩ Ioc (0 : ℝ) 1 =
        Ioc (0 : ℝ) 1 \ (↑F : Set ℝ) := by
      ext u
      simp [and_comm]
    rw [hset, measure_diff_null hFzero]
    norm_num
  have hmeas : Measurable
      (fun u : ℝ ↦ ((exponentialRemainderDensity rate u : NNReal) : ENNReal)) := by
    apply Measurable.coe_nnreal_ennreal
    unfold exponentialRemainderDensity
    fun_prop
  have hpos : ∀ᵐ u ∂base,
      ((exponentialRemainderDensity rate u : NNReal) : ENNReal) ≠ 0 := by
    filter_upwards with u
    simp only [exponentialRemainderDensity, ne_eq, ENNReal.coe_eq_zero]
    rw [← NNReal.coe_eq_zero,
      Real.coe_toNNReal _ (Real.exp_pos _).le]
    exact (Real.exp_pos _).ne'
  rw [pos_iff_ne_zero]
  intro hzero
  apply hbase.ne'
  exact (GaloisForLFunctions.HTGeometry.measure_withDensity_eq_zero_iff
    base hmeas hpos {u : ℝ | u ∉ F}).mp (by
      simpa [exponentialRemainderMeasure, base] using hzero)

/-- One strictly positive source weight makes every size-biased Hausdorff row measure infinitely
supported. -/
theorem finiteExponentialGammaHausdorffMeasure_infiniteSupport
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ) (a : ℕ)
    (hrate : ∀ p, 0 < rate p) (p0 : P) (hp0 : 0 < weight p0)
    (F : Finset ℝ) :
    0 < finiteExponentialGammaHausdorffMeasure weight rate x a
      {u : ℝ | u ∉ F} := by
  let coefficient : ℝ :=
    weight p0 * Real.exp (-x * rate p0) * rate p0 ^ a
  have hcoefficient : 0 < coefficient := by
    dsimp only [coefficient]
    exact mul_pos (mul_pos hp0 (Real.exp_pos _)) (pow_pos (hrate p0) a)
  have hsingle : 0 <
      (ENNReal.ofReal coefficient • exponentialRemainderMeasure (rate p0))
        {u : ℝ | u ∉ F} := by
    rw [Measure.smul_apply]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hcoefficient).ne'
      (exponentialRemainderMeasure_infiniteSupport (rate p0) F).ne'
  have hle :
      ENNReal.ofReal coefficient • exponentialRemainderMeasure (rate p0) ≤
        finiteExponentialGammaHausdorffMeasure weight rate x a := by
    rw [finiteExponentialGammaHausdorffMeasure]
    dsimp only [coefficient]
    exact Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ p0)
  exact hsingle.trans_le (hle {u : ℝ | u ∉ F})

/-- **Universal strict bivariate-moment law.**  Nonnegative weights, positive rates, and one
strictly positive channel make every fixed-rate-degree Hankel block positive definite. -/
theorem finiteExponentialGammaBivariateMoment_hankel_posDef
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (hrate : ∀ p, 0 < rate p)
    (p0 : P) (hp0 : 0 < weight p0) (a n : ℕ) :
    (HTGeometry.momentHankelMatrix
      (fun b ↦ finiteExponentialGammaBivariateMoment weight rate x a b) n).PosDef := by
  apply HTGeometry.momentHankelMatrix_posDef_of_infiniteSupport
    (s := fun b ↦ finiteExponentialGammaBivariateMoment weight rate x a b)
    (μ := finiteExponentialGammaHausdorffMeasure weight rate x a)
  · exact finiteExponentialGammaBivariateMoment_eq_integral
      weight rate x hweight hrate a
  · exact integrable_pow_finiteExponentialGammaHausdorffMeasure weight rate x a
  · exact finiteExponentialGammaHausdorffMeasure_infiniteSupport
      weight rate x a hrate p0 hp0

/-- Determinant form of the universal strict bivariate-moment law. -/
theorem det_finiteExponentialGammaBivariateMoment_hankel_pos
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (hrate : ∀ p, 0 < rate p)
    (p0 : P) (hp0 : 0 < weight p0) (a n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix
      (fun b ↦ finiteExponentialGammaBivariateMoment weight rate x a b) n).det :=
  (finiteExponentialGammaBivariateMoment_hankel_posDef
    weight rate x hweight hrate p0 hp0 a n).det_pos

/-- **Actual von Mangoldt--Gamma strict Hankel law.**  Every nonempty finite source aperture has
strictly positive Hankel determinants in every row and every finite size. -/
theorem det_finiteVonMangoldtGammaBivariateMoment_hankel_pos
    {M : ℕ} (hM : 0 < M) (x : ℝ) (a n : ℕ) :
    0 < (HTGeometry.momentHankelMatrix
      (fun b ↦ finiteVonMangoldtGammaBivariateMoment M x a b) n).det := by
  let p0 : Fin M := ⟨0, hM⟩
  apply det_finiteExponentialGammaBivariateMoment_hankel_pos
    (p0 := p0)
  · intro p
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · intro p
    exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))
  · dsimp only [p0]
    rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)

end

end RHTower
