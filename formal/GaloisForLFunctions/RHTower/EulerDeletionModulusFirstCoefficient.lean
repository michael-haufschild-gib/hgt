import GaloisForLFunctions.RHTower.EulerDeletionRemainderFirstCoefficient
import GaloisForLFunctions.RHTower.ArithmeticZeroMinimumClasses
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The exact leading coefficient of the deletion modulus remainder

The scaled weighted ordinary remainder has a fixed coefficient and a summable
majorant in the multiples coordinate. Dominated convergence therefore determines
the growing-modulus coefficient of the literal infinite remainder.
-/

noncomputable section
open scoped BigOperators ArithmeticFunction.Moebius
open Filter Topology
namespace RHTower.DeletionMixedRefinement

private def scaledWeightedRemainder (s:ℂ) (N:ℕ) : ℂ :=
  weightedPowerRemainder s N * (((N:ℝ)^(2*s.re+1):ℝ):ℂ)

private theorem scaledWeighted_eq (s:ℂ) {N:ℕ} (hN:0<N) :
    scaledWeightedRemainder s N = star (powerSumRemainder s N*(N:ℂ)^(s+1)) := by
  have hNc : (N:ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : ((2*s.re+1:ℝ):ℂ) = s+star s+1 := by
    apply Complex.ext <;> simp
    ring
  rw [scaledWeightedRemainder, weightedPowerRemainder, kernel,
    Complex.ofReal_cpow (by positivity), he]
  push_cast
  rw [mul_comm ((N:ℂ)^(-s)), mul_assoc, ← Complex.cpow_add _ _ hNc]
  simp only [star_mul, star_nat_cpow, star_add, star_one]
  rw [show -s+(s+star s+1) = star s+1 by ring]
  ring

private theorem tendsto_scaledWeighted {s:ℂ} (hs:0<s.re) (hs1:s≠1) :
    Tendsto (scaledWeightedRemainder s) atTop (𝓝 (-star s/12)) := by
  have ht := (tendsto_powerSumRemainder_mul_endpoint (by linarith : -1<s.re) hs1).star
  simp only [star_div₀, star_neg, star_ofNat] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (scaledWeighted_eq s (by omega)).symm

private theorem norm_scaledWeighted_le {s:ℂ} (hs:0<s.re) (hs1:s≠1) {N:ℕ} (hN:0<N) :
    ‖scaledWeightedRemainder s N‖ ≤ ‖s*(s+1)‖/(s.re+1) := by
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  rw [scaledWeightedRemainder, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hNp _)]
  refine (mul_le_mul_of_nonneg_right (norm_weightedPowerRemainder_le hs hs1 hN)
    (Real.rpow_nonneg hNp.le _)).trans_eq ?_
  rw [mul_assoc, ← Real.rpow_add hNp, show -2*s.re-1+(2*s.re+1) = 0 by ring,
    Real.rpow_zero, mul_one]

private theorem modulus_scaled_eq_tsum (s:ℂ) {p:ℕ} (hp:0<p) :
    infiniteRemainder s p*(((p:ℝ)^(2*s.re):ℝ):ℂ) =
      ∑' n:ℕ+, (((n:ℝ)^(-2*s.re-1):ℝ):ℂ)*scaledWeightedRemainder s (p*n) := by
  have hpc : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpp : (0:ℝ)<p := by exact_mod_cast hp
  have he (n:ℕ+) : (((n:ℝ)^(-2*s.re-1):ℝ):ℂ)*scaledWeightedRemainder s (p*n) =
      weightedPowerRemainder s (p*n)*(((p:ℝ)^(2*s.re+1):ℝ):ℂ) := by
    dsimp [scaledWeightedRemainder]
    have hh : (n:ℝ)^(-2*s.re-1)*((p:ℝ)*(n:ℝ))^(2*s.re+1) =
        (p:ℝ)^(2*s.re+1) := by
      rw [Real.mul_rpow hpp.le (by positivity), mul_left_comm, ← Real.rpow_add (by positivity),
        show -2*s.re-1+(2*s.re+1) = 0 by ring, Real.rpow_zero, mul_one]
    push_cast
    rw [mul_left_comm, ← Complex.ofReal_mul, hh]
  simp_rw [he]
  rw [tsum_mul_right, ← infiniteRemainder_div_eq_multiples s hp,
    Real.rpow_add hpp, Real.rpow_one]
  push_cast
  field_simp

/-- The exact growing-modulus coefficient follows from dominated convergence of the actual sum. -/
theorem tendsto_infiniteRemainder_scaled {s:ℂ} (hs:0<s.re) (hs1:s≠1) :
    Tendsto (fun p:ℕ => infiniteRemainder s p*(((p:ℝ)^(2*s.re):ℝ):ℂ)) atTop
      (𝓝 ((-star s/12)*(∑' n:ℕ+, (n:ℝ)^(-2*s.re-1):ℝ))) := by
  have hsum : Summable (fun n:ℕ+ => (n:ℝ)^(-2*s.re-1)) :=
    (Real.summable_nat_rpow.mpr (by linarith)).subtype _
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun p:ℕ => fun n:ℕ+ => (((n:ℝ)^(-2*s.re-1):ℝ):ℂ)*scaledWeightedRemainder s (p*n))
    (g := fun n:ℕ+ => (((n:ℝ)^(-2*s.re-1):ℝ):ℂ)*(-star s/12))
    (bound := fun n:ℕ+ => (n:ℝ)^(-2*s.re-1)*(‖s*(s+1)‖/(s.re+1)))
    (hsum.mul_right _)
    (fun n => ((tendsto_scaledWeighted hs hs1).comp
      (tendsto_atTop_mono (fun p:ℕ => by change p ≤ p*(n:ℕ); nlinarith [n.pos]) tendsto_id)).const_mul _)
    (by
      filter_upwards [eventually_ge_atTop 1] with p hp
      intro n
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
      exact mul_le_mul_of_nonneg_left (norm_scaledWeighted_le hs hs1
        (Nat.mul_pos (by omega) n.pos)) (Real.rpow_nonneg (by positivity) _))
  simp only [tsum_mul_right, ← Complex.ofReal_tsum] at ht
  rw [show (↑(∑' n:ℕ+, (n:ℝ)^(-2*s.re-1)):ℂ)*(-star s/12) =
    (-star s/12)*↑(∑' n:ℕ+, (n:ℝ)^(-2*s.re-1)) by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  exact (modulus_scaled_eq_tsum s (by omega)).symm

end RHTower.DeletionMixedRefinement
