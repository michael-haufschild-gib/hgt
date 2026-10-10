import GaloisForLFunctions.HTGeometry.PaperIntervalWallFourier
import GaloisForLFunctions.RHTower.SourceHorizontalRiggedKreinWallSingularityNoGo

/-! # Literal Fourier observations of the rigged Krein wall

An affine segment at arbitrary imaginary height crosses the critical wall inside the strip.
The source-selected fundamental symmetry acts on its canonical time axis by the two chamber
signs. Every vector assigned at the wall gives the same Fourier coefficients in every lattice
coordinate, although evaluation at the wall recovers the assigned vector exactly.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry MeasureTheory Set
open PreDivisorReflectionDefectStabilization

/-- A literal source segment from real part one quarter to three quarters. -/
def paperKreinWallSourcePoint (t x : ℝ) : ℂ :=
  ((1 / 4 + x / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I

theorem paperKreinWallSourcePoint_re (t x : ℝ) :
    (paperKreinWallSourcePoint t x).re = 1 / 4 + x / 2 := by
  simp [paperKreinWallSourcePoint]

/-- The chamber step is exactly the native source-selected action on the fixed time axis. -/
theorem paperKreinWallSource_action (t : ℝ) (x : unitInterval) :
    preDivisorRiggedPrimeFundamentalSymmetry (paperKreinWallSourcePoint t x)
      preDivisorRiggedPrimeTimeAxis =
      paperIntervalWallStep 0 x • preDivisorRiggedPrimeTimeAxis := by
  have h0 : 0 < (paperKreinWallSourcePoint t x).re := by
    rw [paperKreinWallSourcePoint_re]
    linarith [x.property.1]
  have h1 : (paperKreinWallSourcePoint t x).re < 1 := by
    rw [paperKreinWallSourcePoint_re]
    linarith [x.property.2]
  have hl : (paperKreinWallSourcePoint t x).re < 1 / 2 ↔ (x : ℝ) < 1 / 2 := by
    rw [paperKreinWallSourcePoint_re]
    constructor <;> intro h <;> linarith
  have hr : 1 / 2 < (paperKreinWallSourcePoint t x).re ↔ 1 / 2 < (x : ℝ) := by
    rw [paperKreinWallSourcePoint_re]
    constructor <;> intro h <;> linarith
  rw [preDivisorRiggedPrimeFundamentalSymmetry_timeAxis_chambers _ h0 h1]
  simp only [hl, hr, paperIntervalWallStep]
  split_ifs <;> module

theorem paperKreinWallSource_action_wall (t : ℝ) :
    preDivisorRiggedPrimeFundamentalSymmetry (paperKreinWallSourcePoint t (1 / 2))
      preDivisorRiggedPrimeTimeAxis = 0 := by
  simpa only [paperIntervalWallStep_wall, zero_smul] using
    paperKreinWallSource_action t ⟨1 / 2, by constructor <;> norm_num⟩

/-- Preserve both native chambers while assigning an arbitrary rigged vector at the wall. -/
def paperKreinWallCompletion (t : ℝ) (v : DeningerHeightKothe) (x : ℝ) : DeningerHeightKothe :=
  if x = 1 / 2 then v else
    preDivisorRiggedPrimeFundamentalSymmetry (paperKreinWallSourcePoint t x)
      preDivisorRiggedPrimeTimeAxis

theorem paperKreinWallCompletion_wall (t : ℝ) (v : DeningerHeightKothe) :
    paperKreinWallCompletion t v (1 / 2) = v := by
  simp [paperKreinWallCompletion]

theorem paperKreinWallCompletion_zero (t x : ℝ) :
    paperKreinWallCompletion t 0 x =
      preDivisorRiggedPrimeFundamentalSymmetry (paperKreinWallSourcePoint t x)
        preDivisorRiggedPrimeTimeAxis := by
  by_cases hx : x = 1 / 2
  · subst x
    rw [paperKreinWallCompletion_wall, paperKreinWallSource_action_wall]
  · exact if_neg hx

/-- The literal completions distinguish every possible vector value at the wall. -/
theorem paperKreinWallCompletion_injective (t : ℝ) :
    Function.Injective (paperKreinWallCompletion t) := by
  intro v w h
  simpa only [paperKreinWallCompletion_wall] using congrFun h (1 / 2)

/-- The first prime coordinate is a normalized observer of the native time axis. -/
theorem paperKreinTimeAxis_first_coordinate :
    (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ)
      (preDivisorRiggedPrimeAxis (nthPrimePoint 0)) = 1 := by
  have hp : nthPrimePoint 0 ≠ nthPrimePoint 1 :=
    preDivisorRiggedNthPrimePoint_injective.ne (by omega)
  change (preDivisorRiggedPrimeDelta (nthPrimePoint 0) : DeningerPrimeLattice → ℂ)
      (preDivisorRiggedPrimeAxis (nthPrimePoint 0)) +
    (preDivisorRiggedPrimeDelta (nthPrimePoint 1) : DeningerPrimeLattice → ℂ)
      (preDivisorRiggedPrimeAxis (nthPrimePoint 0)) = 1
  simp [preDivisorRiggedPrimeDelta_axis, hp]

theorem paperKreinWallCompletion_first_coordinate (t : ℝ) (v : DeningerHeightKothe)
    (x : unitInterval) :
    (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis (nthPrimePoint 0)) =
      paperIntervalWallStep
        ((v : DeningerPrimeLattice → ℂ) (preDivisorRiggedPrimeAxis (nthPrimePoint 0))) x := by
  by_cases hx : (x : ℝ) = 1 / 2
  · rw [hx, paperKreinWallCompletion_wall, paperIntervalWallStep_wall]
  · rw [paperKreinWallCompletion, if_neg hx, paperKreinWallSource_action]
    change paperIntervalWallStep 0 x *
      (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ)
        (preDivisorRiggedPrimeAxis (nthPrimePoint 0)) = _
    rw [paperKreinTimeAxis_first_coordinate, mul_one]
    rcases lt_or_gt_of_ne hx with h | h
    · simp only [paperIntervalWallStep, if_pos h]
    · simp only [paperIntervalWallStep, if_neg (not_lt.mpr h.le), if_pos h]

/-- Fourier coefficients erase the entire space of possible wall vectors. -/
theorem paperKreinWallCompletion_coefficient (t : ℝ) (v : DeningerHeightKothe)
    (q : DeningerPrimeLattice) (k : ℤ) :
    l2Pair (fourierChar k)
      (fun x => (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ) q) =
      (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q *
        l2Pair (fourierChar k) (paperIntervalWallStep 0) := by
  rw [← l2Pair_smul_right]
  unfold l2Pair
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne (1 / 2 : ℝ)] with x hx hxi
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hxi
  have h := paperKreinWallSource_action t ⟨x, hxi.1.le, hxi.2⟩
  rw [paperKreinWallCompletion, if_neg hx, h]
  change (starRingEnd ℂ) (fourierChar k x) *
      (paperIntervalWallStep 0 x * (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q) = _
  ring

theorem paperKreinWallCompletion_same_coefficients (t u : ℝ) (v w : DeningerHeightKothe)
    (q : DeningerPrimeLattice) (k : ℤ) :
    l2Pair (fourierChar k)
        (fun x => (paperKreinWallCompletion t v x : DeningerPrimeLattice → ℂ) q) =
      l2Pair (fourierChar k)
        (fun x => (paperKreinWallCompletion u w x : DeningerPrimeLattice → ℂ) q) := by
  rw [paperKreinWallCompletion_coefficient, paperKreinWallCompletion_coefficient]

/-- Every finite observation already has the exact native time-axis factorization. -/
theorem paperKreinWallCompletion_partialSum (t : ℝ) (v : DeningerHeightKothe)
    (q : DeningerPrimeLattice) (N : ℕ) (x : ℝ) :
    fourierPartialSum
      (fun y => (paperKreinWallCompletion t v y : DeningerPrimeLattice → ℂ) q) N x =
      (preDivisorRiggedPrimeTimeAxis : DeningerPrimeLattice → ℂ) q *
        fourierPartialSum (paperIntervalWallStep 0) N x := by
  simp only [fourierPartialSum, paperKreinWallCompletion_coefficient,
    Finset.mul_sum, mul_assoc]

end
end RHTower
