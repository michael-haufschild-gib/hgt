import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ReceivingCharges.LiteralBoundedProfileNorm
import GaloisForLFunctions.ArithmeticCouplingTheory.ReceivingCharges.DilationPacketOperator

/-!
# Exact centering of the physical upward vector

Profile subtraction commutes with the literal operator. Its bounded
constant-profile norm controls the exact harmonic-centering correction.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open MeasureTheory Finset
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open GaloisForLFunctions.ArithmeticCouplingTheory
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

/-- Subtracting a profile is exact before or after applying the literal upward operator. -/
theorem upward_physical_packet_sub {φ : ℝ → ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hwidth : c / N ≤ 1) (F G : ℕ → ℝ) :
    upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector (fun j => F j - G j) N) =
      upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N) -
        upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector G N) := by
  have hfg : (fun j => F j - G j) = (fun j => F j + (-1 : ℝ) * G j) := by
    funext j
    ring
  have hcoeff :
      logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N (fun j => F j - G j) =
        fun n => logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N F n -
          logarithmicUpwardProfileCoefficient φ c (linearPrimeStrip c) N G n := by
    funext n
    rw [hfg, logarithmicUpwardProfileCoefficient_add, logarithmicUpwardProfileCoefficient_const_mul]
    ring
  have hpacket (U V : ℕ → ℝ) : packetVector (fun n => U n - V n) N =
      packetVector U N - packetVector V N := by
    ext n
    change (U n - V n) / Real.sqrt (n : ℕ) =
      U n / Real.sqrt (n : ℕ) - V n / Real.sqrt (n : ℕ)
    exact sub_div _ _ _
  simp only [upwardPrimeVector_smul, upwardPrimeVector_packet_eq hsupp hc hwidth]
  rw [hcoeff, hpacket, smul_sub]

/-- Exact harmonic centering changes the upward vector by at most its bounded constant-profile cost. -/
theorem upward_physical_centering_error_le {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c)
    {N : ℕ} (hlog : 1 ≤ Real.log N) (hwidth : c / N ≤ 1)
    (hB : linearPrimeStrip c ≤ N)
    (hsep : 2 * c * Real.exp 1 * linearPrimeStrip c ≤ N)
    (F : ℕ → ℝ) (η : ℝ) :
    ‖upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector (fun j => F j - η) N) -
      upwardPrimeVector φ c N ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)‖ ≤
      8 * (linearPrimeStrip c : ℝ) * |η| *
        (|Real.log (2 * c * Real.exp 1)| + mertensWindowConstant + 1) := by
  rw [upward_physical_packet_sub hsupp hc hwidth F (fun _ => η), sub_sub_cancel_left, norm_neg]
  exact upward_physical_bounded_profile_norm_le hφ hsupp hM hc hlog hwidth hB hsep
    (fun _ => η) (abs_nonneg η) (fun _ => le_rfl)

#print axioms upward_physical_packet_sub
#print axioms upward_physical_centering_error_le

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
