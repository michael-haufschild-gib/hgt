import GaloisForLFunctions.RHTower.WeilLogShiftFactorialMajorant
import GaloisForLFunctions.RHTower.WeilLogShiftFactorialRegularization
import GaloisForLFunctions.RHTower.WeilLogShiftImpulseLineObstruction
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# One possible factorial-regular amplitude on each late impulse line

Even when the shift, factorial order, exponential rate, prefactor, and cutoff
all vary with amplitude, there is at most one amplitude admitting a finite
factorial majorant. This follows from algebraic closure and the exact impulse
difference law. Every diffuse amplitude measure therefore gives joint
failure of all finite factorial normalizations almost everywhere.
-/

open Filter MeasureTheory Topology Real
open scoped BoundedContinuousFunction

namespace RHTower

open WeilExcess

/-- At most one amplitude admits any finite factorial majorant at any real
shift; every majorant parameter and the shift may depend on the amplitude. -/
theorem exists_weilLogShiftRecoveryImpulse_factorial_exceptional_subsingleton :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      Set.Subsingleton {t : ℝ | ∃ y : ℝ,
        WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t))} := by
  obtain ⟨K, hK, hNo⟩ := exists_weilLogShiftRecoveryMomentResponse_no_factorial_majorant
  refine ⟨K, hK, fun center k hk t ht u hu => ?_⟩
  by_contra htu
  have ht0 := (weilLogShiftHasFactorialMajorant_some_shift_iff_origin
    (weilLogShiftRecoveryImpulseHistory center k t)).mp ht
  have hu0 := (weilLogShiftHasFactorialMajorant_some_shift_iff_origin
    (weilLogShiftRecoveryImpulseHistory center k u)).mp hu
  have hscaled : WeilLogShiftHasFactorialMajorant
      (fun n => (t - u) * weilLogShiftRecoveryMomentResponse 0 n k) := by
    simpa only [weilLogShiftRecoveryImpulseHistory_moment_sub] using
      weilLogShiftHasFactorialMajorant_sub ht0 hu0
  have hresponse := (weilLogShiftHasFactorialMajorant_mul_iff (t - u)
    (sub_ne_zero.mpr htu) (fun n => weilLogShiftRecoveryMomentResponse 0 n k)).mp hscaled
  obtain ⟨m, A, D, N, hN⟩ := hresponse
  exact (hNo k hk 0 m A D) ⟨N, hN⟩

/-- Every point-null amplitude measure assigns zero measure to existence
of any factorial-regular shift, jointly over all majorant parameters. -/
theorem exists_weilLogShiftRecoveryImpulse_factorial_exception_measure_zero :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      ∀ (μ : Measure ℝ) [NullSingletonClass μ],
        μ {t : ℝ | ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t))} = 0 := by
  obtain ⟨K, hK, hsub⟩ := exists_weilLogShiftRecoveryImpulse_factorial_exceptional_subsingleton
  refine ⟨K, hK, ?_⟩
  intro center k hk μ hμ
  exact (hsub center k hk).measure_zero μ

/-- Almost every diffuse amplitude fails every finite factorial majorant
at every real shift, and every factorial/exponential signed normalization
is nonsummable. All quantifiers are inside one almost-everywhere statement. -/
theorem exists_weilLogShiftRecoveryImpulse_ae_no_factorial_regularization :
    ∃ K : ℕ, 625 ≤ K ∧ ∀ (center : ℕ →ᵇ ℝ) (k : ℕ), K ≤ k →
      ∀ (μ : Measure ℝ) [NullSingletonClass μ], ∀ᵐ t ∂μ,
        (∀ y : ℝ, ¬ WeilLogShiftHasFactorialMajorant
          (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t))) ∧
        ∀ (y : ℝ) (m : ℕ) (A : ℝ), ¬ Summable (fun n : ℕ => exp (-(A * n)) *
          weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t) n /
            (n.factorial : ℝ) ^ m) := by
  obtain ⟨K, hK, hzero⟩ := exists_weilLogShiftRecoveryImpulse_factorial_exception_measure_zero
  refine ⟨K, hK, ?_⟩
  intro center k hk μ hμ
  have hnot : ∀ᵐ t ∂μ, ¬ ∃ y : ℝ, WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) := by
    apply ae_iff.mpr
    simpa only [Classical.not_not] using hzero center k hk μ
  filter_upwards [hnot] with t ht
  have hno : ∀ y : ℝ, ¬ WeilLogShiftHasFactorialMajorant
      (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) :=
    fun y hy => ht ⟨y, hy⟩
  refine ⟨hno, fun y m A hs => ?_⟩
  exact hno y (weilLogShiftHasFactorialMajorant_of_summable_normalization
    (weilLogShiftRecoveryMoment y (weilLogShiftRecoveryImpulseHistory center k t)) m A hs)

end RHTower
