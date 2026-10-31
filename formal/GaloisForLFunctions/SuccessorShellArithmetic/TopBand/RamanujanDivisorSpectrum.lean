import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorMoments
import GaloisForLFunctions.RHTower.DirichletLogDerivation
import GaloisForLFunctions.RHTower.Deninger.DeningerVonMangoldtMoebiusConvolution
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheAdjunctionEnergySeparatesValuations

/-!
# The conductor spectrum of the logarithmic divisor jet

Logarithmic differentiation of the Möbius convolution gives the exact
finite conductor expansion of the downward divisor jet. Its coefficients
are nonnegative. Removing the constant conductor exposes an absolute
envelope attained at every conductor multiple, and bounds the normalized
centered jet by `2 sqrt(φ(m)) log m`.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticIntersectionTheory
noncomputable section


private def conductorDivisibilitySource (n : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ∣ n then (d : ℝ) else 0, by simp⟩

private theorem moebius_mul_conductorDivisibilitySource (m n : ℕ) :
    ((moebius : ArithmeticFunction ℝ) * conductorDivisibilitySource n) m =
      ramanujanLagCoefficient m n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun a b => (moebius : ArithmeticFunction ℝ) a * conductorDivisibilitySource n b)]
  simp [conductorDivisibilitySource, ramanujanLagCoefficient, moebiusReal]

private theorem moebius_mul_log_conductorDivisibilitySource (m n : ℕ) :
    ((moebius : ArithmeticFunction ℝ) *
      (conductorDivisibilitySource n).pmul ArithmeticFunction.log) m =
      ramanujanLogDivisorJet m n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal'
    (fun a b => (moebius : ArithmeticFunction ℝ) a *
      ((conductorDivisibilitySource n).pmul ArithmeticFunction.log) b), ramanujanLogDivisorJet]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ∣ n
  · simp [conductorDivisibilitySource, pmul_apply, hd, mul_assoc]
  · simp [conductorDivisibilitySource, pmul_apply, hd]

/-- The logarithmic divisor correction lowers conductors with nonnegative coefficients. -/
theorem ramanujanLogDivisorJet_eq_conductor_sum (m n : ℕ) :
    ramanujanLogDivisorJet m n = Real.log m * ramanujanLagCoefficient m n +
      ∑ d ∈ m.divisors, vonMangoldt d * ramanujanLagCoefficient (m / d) n := by
  have hder := _root_.RHTower.pmul_log_mul
    (moebius : ArithmeticFunction ℝ) (conductorDivisibilitySource n)
  have hμ : (moebius : ArithmeticFunction ℝ).pmul ArithmeticFunction.log =
      -(vonMangoldt * (moebius : ArithmeticFunction ℝ)) := by
    rw [GaloisForLFunctions.vonMangoldt_mul_moebius, neg_neg]
  rw [hμ, neg_mul, mul_assoc] at hder
  have he : (moebius : ArithmeticFunction ℝ) *
      (conductorDivisibilitySource n).pmul ArithmeticFunction.log =
      ((moebius : ArithmeticFunction ℝ) * conductorDivisibilitySource n).pmul ArithmeticFunction.log +
        vonMangoldt * ((moebius : ArithmeticFunction ℝ) * conductorDivisibilitySource n) := by
    linear_combination -hder
  have h := congrArg (fun f : ArithmeticFunction ℝ => f m) he
  simp only [ArithmeticFunction.add_apply, pmul_apply, log_apply,
    moebius_mul_conductorDivisibilitySource, moebius_mul_log_conductorDivisibilitySource] at h
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d k => vonMangoldt d *
      ((moebius : ArithmeticFunction ℝ) * conductorDivisibilitySource n) k)] at h
  simp only [moebius_mul_conductorDivisibilitySource] at h
  exact h.trans (by ring)

/-- Removing the exact mean leaves only nonpolar conductors. -/
theorem ramanujanLogDivisorJet_sub_mean_eq {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanLogDivisorJet m n - vonMangoldt m =
      Real.log m * ramanujanLagCoefficient m n +
        ∑ d ∈ m.divisors.erase m, vonMangoldt d * ramanujanLagCoefficient (m / d) n := by
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have hs := sum_erase_add m.divisors
    (fun d => vonMangoldt d * ramanujanLagCoefficient (m / d) n) hm_mem
  have hc1 : ramanujanLagCoefficient 1 n = 1 := by
    simpa only [Nat.totient_one, Nat.cast_one] using
      ramanujanLagCoefficient_of_dvd (one_dvd n)
  rw [Nat.div_self hm, hc1, mul_one] at hs
  rw [ramanujanLogDivisorJet_eq_conductor_sum, ← hs]
  ring

/-- Every conductor multiple simultaneously maximizes the positive conductor coefficients. -/
theorem ramanujanLogDivisorJet_of_dvd {m n : ℕ} (hm : 0 < m) (hmn : m ∣ n) :
    ramanujanLogDivisorJet m n =
      (m.totient : ℝ) * (Real.log m + tameDifferent m) := by
  calc
    _ = ∑ d ∈ m.divisors, (moebius (m / d) : ℝ) * d * Real.log d := by
      unfold ramanujanLogDivisorJet
      apply sum_congr rfl
      intro d hd
      rw [if_pos ((Nat.dvd_of_mem_divisors hd).trans hmn)]
    _ = _ := sum_moebius_mul_divisor_log_eq_totient_excitation hm

/-- The centered jet's maximum at conductor multiples is its exact absolute envelope. -/
theorem abs_ramanujanLogDivisorJet_sub_mean_le {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |ramanujanLogDivisorJet m n - vonMangoldt m| ≤
      (m.totient : ℝ) * (Real.log m + tameDifferent m) - vonMangoldt m := by
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have he := ramanujanLogDivisorJet_sub_mean_eq hm m
  rw [ramanujanLogDivisorJet_of_dvd hm dvd_rfl,
    ramanujanLagCoefficient_of_dvd dvd_rfl] at he
  have hsum : (∑ d ∈ m.divisors.erase m, vonMangoldt d * ramanujanLagCoefficient (m / d) m) =
      ∑ d ∈ m.divisors.erase m, vonMangoldt d * ((m / d).totient : ℝ) := by
    apply sum_congr rfl
    intro d hd
    rw [ramanujanLagCoefficient_of_dvd
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors (mem_erase.mp hd).2))]
  rw [hsum] at he
  rw [ramanujanLogDivisorJet_sub_mean_eq hm n]
  calc
    _ ≤ |Real.log m * ramanujanLagCoefficient m n| +
        |∑ d ∈ m.divisors.erase m, vonMangoldt d * ramanujanLagCoefficient (m / d) n| := abs_add_le _ _
    _ ≤ Real.log m * m.totient +
        ∑ d ∈ m.divisors.erase m, vonMangoldt d * ((m / d).totient : ℝ) := by
      rw [abs_mul, abs_of_nonneg hlog]
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m n) hlog
      · refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
        rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
        exact mul_le_mul_of_nonneg_left
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient (m / d) n)
          vonMangoldt_nonneg
    _ = _ := he.symm

/-- The absolute envelope is attained at every multiple of the conductor. -/
theorem abs_ramanujanLogDivisorJet_sub_mean_of_dvd {m n : ℕ}
    (hm : 0 < m) (hmn : m ∣ n) :
    |ramanujanLogDivisorJet m n - vonMangoldt m| =
      (m.totient : ℝ) * (Real.log m + tameDifferent m) - vonMangoldt m := by
  have hnonneg := (abs_nonneg _).trans (abs_ramanujanLogDivisorJet_sub_mean_le hm n)
  rw [ramanujanLogDivisorJet_of_dvd hm hmn, abs_of_nonneg hnonneg]

/-- The normalized centered jet grows at most logarithmically times its Ramanujan amplitude. -/
theorem abs_centeredRamanujanJet_le_logarithmic {m : ℕ} (hm : 0 < m) (n : ℕ) :
    |centeredRamanujanJet m n| ≤ 2 * Real.sqrt (m.totient : ℝ) * Real.log m := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hs : 0 < Real.sqrt (m.totient : ℝ) := Real.sqrt_pos.mpr hφ
  have hupper : (m.totient : ℝ) * (Real.log m + tameDifferent m) - vonMangoldt m ≤
      2 * m.totient * Real.log m := by
    have h := mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) hφ.le
    nlinarith only [h, show (0 : ℝ) ≤ vonMangoldt m from vonMangoldt_nonneg]
  rw [centeredRamanujanJet, abs_div, abs_of_pos hs]
  calc
    _ ≤ (2 * m.totient * Real.log m) / Real.sqrt (m.totient : ℝ) :=
      div_le_div_of_nonneg_right ((abs_ramanujanLogDivisorJet_sub_mean_le hm n).trans hupper) hs.le
    _ = _ := by
      apply (div_eq_iff hs.ne').mpr
      calc
        _ = 2 * (Real.sqrt (m.totient : ℝ)) ^ 2 * Real.log m := by
          rw [Real.sq_sqrt hφ.le]
        _ = _ := by ring

#print axioms ramanujanLogDivisorJet_eq_conductor_sum
#print axioms abs_ramanujanLogDivisorJet_sub_mean_le
#print axioms abs_ramanujanLogDivisorJet_sub_mean_of_dvd
#print axioms abs_centeredRamanujanJet_le_logarithmic
end
end GaloisForLFunctions.SuccessorShellArithmetic
