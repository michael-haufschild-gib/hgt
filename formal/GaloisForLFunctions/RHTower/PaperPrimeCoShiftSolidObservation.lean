import GaloisForLFunctions.RHTower.PaperPrimeCoShiftCofinalGap
import GaloisForLFunctions.HTGeometry.LpSolidUniform

/-! # Worst masked observations of cofinal prime packets

The full directed system of finite prime packets loses every masked fixed
history uniformly. Its norm-one, infinite-cost error survives simultaneously.
-/

namespace RHTower.PrimeCoShift
noncomputable section
open Filter Topology GaloisForLFunctions.HTGeometry
open scoped ENNReal

def paperCoShiftObservationDefect (s : PaperCoShiftParameter) (F : Finset Nat.Primes) : H →L[ℂ] H :=
  paperCoShiftFiniteProjection s F - paperCoShiftGroundProjection s.1

theorem paperCoShiftObservationDefect_norm (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    ‖paperCoShiftObservationDefect s F‖ = 1 :=
  paperCoShiftFiniteProjection_norm_sub_ground s F

theorem paperCoShiftObservationDefect_traceCost (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    compactOperatorTraceCost H (paperCoShiftObservationDefect s F) = ∞ :=
  paperCoShiftFiniteProjection_error_traceCost s F

theorem paperCoShiftObservationDefect_strong (s : PaperCoShiftParameter) (x : H) :
    Tendsto (fun F => paperCoShiftObservationDefect s F x) atTop (𝓝 0) := by
  simpa only [paperCoShiftObservationDefect, sub_apply, sub_self] using
    (paperCoShiftFiniteProjection_strong_tendsto s x).sub
      (tendsto_const_nhds (x := paperCoShiftGroundProjection s.1 x))

theorem paperCoShiftCofinal_uniform_solidHull (s : PaperCoShiftParameter) (x : H) :
    TendstoUniformlyOn (fun F y => paperCoShiftObservationDefect s F y)
      (fun _ => 0) atTop (lpSolidHull x) :=
  tendstoUniformlyOn_lpSolidHull _ 1 zero_le_one
    (fun F => (paperCoShiftObservationDefect_norm s F).le)
    (paperCoShiftObservationDefect_strong s) x

theorem paperCoShiftCofinal_uniform_masks (s : PaperCoShiftParameter) (x : H) :
    TendstoUniformly (fun F m => paperCoShiftObservationDefect s F (lpMaskedHistory x m))
      (fun _ => 0) atTop :=
  tendstoUniformly_lpMaskedHistory _ 1 zero_le_one
    (fun F => (paperCoShiftObservationDefect_norm s F).le)
    (paperCoShiftObservationDefect_strong s) x

theorem paperCoShiftCofinal_solidObservation_tendsto (s : PaperCoShiftParameter) (x : H) :
    Tendsto (fun F => lpSolidObservation (paperCoShiftObservationDefect s F) x) atTop (𝓝 0) :=
  tendsto_lpSolidObservation _ 1 zero_le_one
    (fun F => (paperCoShiftObservationDefect_norm s F).le)
    (paperCoShiftObservationDefect_strong s) x

theorem paperCoShiftCofinal_moving_mask_tendsto (s : PaperCoShiftParameter) (x : H)
    (m : Finset Nat.Primes → LpCoordinateMask ℕ+) :
    Tendsto (fun F => paperCoShiftObservationDefect s F (lpMaskedHistory x (m F))) atTop (𝓝 0) :=
  tendsto_moving_lpMaskedHistory _ 1 zero_le_one
    (fun F => (paperCoShiftObservationDefect_norm s F).le)
    (paperCoShiftObservationDefect_strong s) x m

theorem paperCoShiftCofinal_observation_attained (s : PaperCoShiftParameter)
    (F : Finset Nat.Primes) (x : H) :
    ∃ m : LpCoordinateMask ℕ+, ‖paperCoShiftObservationDefect s F (lpMaskedHistory x m)‖ =
      lpSolidObservation (paperCoShiftObservationDefect s F) x :=
  lpSolidObservation_attained _ x

end
end RHTower.PrimeCoShift
