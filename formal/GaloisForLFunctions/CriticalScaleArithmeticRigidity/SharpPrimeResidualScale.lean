import GaloisForLFunctions.CriticalScaleArithmeticRigidity.PrimeIncidenceHarmonicWindows
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.SharpPrimeSector
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.AdjunctionResidualCoercivity
import GaloisForLFunctions.RHTower.Sieve.HarmonicDyadicBlock

/-!
# The quadratic logarithmic relative residual cost is attained

Positive prime incidence retains a cubic logarithmic complementary tail.
The scalar Mertens row has only quadratic logarithmic cost on the coherent
packet. This yields a matching lower scale for the literal prime residual,
uniformly in every horizon above the square root of the conductor cutoff.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open SignedArithmeticHodgeTheory

/-- The complementary quotient annulus retains one logarithm of its divisor threshold. -/
theorem harmonic_quotient_annulus_ge_log_sub_log_two {P N : ℕ}
    (hP : 0 < P) (hPN : P ≤ N) :
    Real.log P - Real.log 2 ≤ ∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ) := by
  have hA : N / P ≤ N := Nat.div_le_self N P
  have hmod := Nat.mod_add_div N P
  have hdiv : N / P * P ≤ N := by nlinarith only [hmod, Nat.zero_le (N % P)]
  have hmul : (N / P + 1) * P ≤ 2 * (N + 1) := by
    rw [Nat.add_mul, one_mul]
    omega
  have hpR : (0 : ℝ) < P := by exact_mod_cast hP
  have haR : (0 : ℝ) < ((N / P + 1 : ℕ) : ℝ) := by positivity
  have hnR : 0 < (N : ℝ) + 1 := by positivity
  have hlog : Real.log (((N / P + 1 : ℕ) : ℝ) * P) ≤
      Real.log (2 * ((N : ℝ) + 1)) :=
    Real.log_le_log (mul_pos haR hpR) (by exact_mod_cast hmul)
  rw [Real.log_mul haR.ne' hpR.ne', Real.log_mul two_ne_zero hnR.ne'] at hlog
  have hsum := _root_.RHTower.Sieve.log_sub_le_sum_Icc_one_div
    (m := N / P + 1) (n := N) (Nat.succ_le_succ (Nat.zero_le (N / P))) (by omega)
  linarith only [hlog, hsum]

private theorem primeWitness_mass_gap (Q : ℕ) :
    (2 * Real.log 2) * (∑ m ∈ Icc 1 Q, primeOnly primePoleWitness m ^ 2) ≤
      primePoleScale Q := by
  have heq : removeConstantConductor (primeOnly primePoleWitness) = primeOnly primePoleWitness := by
    funext m
    by_cases hm : m = 1
    · subst m
      rw [removeConstantConductor, if_pos rfl, primeOnly,
        if_neg (by decide : ¬ Nat.Prime 1)]
    · simp only [removeConstantConductor, if_neg hm]
  have h := coefficient_mass_le_adjunction_gap Q (primeOnly primePoleWitness)
  rwa [heq, (primePoleWitness_response_and_energy Q).2] at h

/-- The literal prime residual attains its quadratic logarithmic conductor scale
on an explicit coherent packet, uniformly over all `N≥P` with cutoff `Q=P²`. -/
theorem eventually_coherentPrimeResidual_logarithmic_lower :
    ∀ᶠ P : ℕ in atTop, ∀ N : ℕ, P ≤ N →
      (1 / 384 : ℝ) * Real.log (P * P : ℕ) ^ 2 *
          primeAdjunctionMass (P * P) (primeOnly primePoleWitness) ≤
        ∑ n ∈ Icc 1 N,
          (∑ m ∈ Icc 1 (P * P),
            primeOnly primePoleWitness m * ramanujanPrimeResidual m N n) ^ 2 := by
  obtain ⟨C, hC, hres⟩ := exists_primeResidual_sq_lower_of_tail
  let E : ℝ := (Real.log 4 + 4) + (8 + _root_.RHTower.Mertens.mertensTail)
  have hE : 0 ≤ E := (abs_nonneg (primePoleScale 1 - Real.log (1 : ℕ))).trans
    (primePoleScale_logarithmic (by decide : 1 ≤ (1 : ℕ)))
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let D : ℝ := 33 + 9 * C / (2 * Real.log 2)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hlog : Tendsto (fun P : ℕ => Real.log (P : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge := (tendsto_atTop.mp hlog) (1 + 4 * E + 2 * Real.log 2 + 32 * D)
  filter_upwards [eventually_ge_atTop 2, hlarge] with P hP hlarge
  intro N hPN
  let l : ℝ := Real.log P
  have hl1 : 1 ≤ l := by dsimp only [l]; linarith only [hlarge, hE, htwo, hD]
  have hl0 : 0 ≤ l := zero_le_one.trans hl1
  have hlE : 4 * E ≤ l := by dsimp only [l]; linarith only [hlarge, hE, htwo, hD]
  have hl2 : 2 * Real.log 2 ≤ l := by dsimp only [l]; linarith only [hlarge, hE, hD]
  have hlD : 32 * D ≤ l := by dsimp only [l]; linarith only [hlarge, hE, htwo]
  have hP0 : 0 < P := by omega
  have hQ : 2 ≤ P * P := by nlinarith only [hP]
  have hPQ : P ≤ P * P := by nlinarith only [hP]
  have hQlog : Real.log (P * P : ℕ) = 2 * l := by
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hP0.ne') (by exact_mod_cast hP0.ne')]
    dsimp only [l]
    ring
  have hQbound := abs_le.mp (primePoleScale_logarithmic (by omega : 1 ≤ P * P))
  have hPbound := abs_le.mp (primePoleScale_logarithmic (by omega : 1 ≤ P))
  rw [hQlog] at hQbound
  change -E ≤ primePoleScale P - l ∧ primePoleScale P - l ≤ E at hPbound
  change -E ≤ primePoleScale (P * P) - 2 * l ∧
    primePoleScale (P * P) - 2 * l ≤ E at hQbound
  have hBtotal : primePoleScale (P * P) ≤ 3 * l := by
    linarith only [hQbound.2, hlE, hE]
  have hB : l / 2 ≤ highPrimePoleMass P (P * P) := by
    rw [highPrimePoleMass_eq_sub hPQ]
    linarith only [hQbound.1, hPbound.2, hlE]
  have hBupper : highPrimePoleMass P (P * P) ≤ 3 * l :=
    (highPrimePoleMass_le P (P * P)).trans hBtotal
  have hB0 := highPrimePoleMass_nonneg P (P * P)
  have hAupper : highPrimeActivityMass P (P * P) ≤ 11 * l := by
    have h := (highPrimeActivityMass_le P (P * P)).trans
      (primeActivityMass_le_primePoleScale_add_eight (P * P))
    linarith only [h, hBtotal, hl1]
  have hH : l / 2 ≤ ∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ) := by
    have h := harmonic_quotient_annulus_ge_log_sub_log_two hP0 hPN
    change l - Real.log 2 ≤ _ at h
    linarith only [h, hl2]
  have hBsq : (l / 2) ^ 2 ≤ highPrimePoleMass P (P * P) ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hB)
      (add_nonneg hB0 (div_nonneg hl0 (by norm_num : (0 : ℝ) ≤ 2)))
    nlinarith only [hprod]
  have hmain : l ^ 3 / 8 ≤
      (∑ n ∈ Icc (N / P + 1) N, 1 / (n : ℝ)) * highPrimePoleMass P (P * P) ^ 2 := by
    have h := mul_le_mul hH hBsq (sq_nonneg (l / 2))
      (sum_nonneg fun n _ => div_nonneg (by norm_num) (Nat.cast_nonneg n))
    exact (show l ^ 3 / 8 = (l / 2) * (l / 2) ^ 2 by ring).trans_le h
  have hactivity : 2 * highPrimePoleMass P (P * P) * highPrimeActivityMass P (P * P) ≤
      66 * l ^ 2 := by
    calc
      _ ≤ 2 * highPrimePoleMass P (P * P) * (11 * l) :=
        mul_le_mul_of_nonneg_left hAupper (mul_nonneg (by norm_num) hB0)
      _ ≤ 2 * (3 * l) * (11 * l) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hBupper (by norm_num)) (by positivity)
      _ = _ := by ring
  have hboundary : 2 * highPrimePoleMass P (P * P) * highPrimeActivityMass P (P * P) /
      (((N / P : ℕ) : ℝ) + 1) ≤ 66 * l ^ 2 := by
    apply (div_le_iff₀ (by positivity : 0 < ((N / P : ℕ) : ℝ) + 1)).mpr
    have hnonneg := mul_nonneg (by positivity : (0 : ℝ) ≤ 66 * l ^ 2)
      (Nat.cast_nonneg (α := ℝ) (N / P))
    nlinarith only [hactivity, hnonneg]
  have htail := coherentPrimeTail_incidence_lower hP0 (P * P) N
  have htailLower : l ^ 3 / 8 - 66 * l ^ 2 ≤
      ∑ n ∈ Icc 1 N,
        completedPrimeDilationTail (P * P) (primeOnly primePoleWitness) (N / n) n ^ 2 /
          (n : ℝ) := by linarith only [htail, hmain, hboundary]
  have hmass : (∑ m ∈ Icc 1 (P * P), primeOnly primePoleWitness m ^ 2) ≤
      3 * l / (2 * Real.log 2) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) htwo)).mpr
    have h := (primeWitness_mass_gap (P * P)).trans hBtotal
    simpa only [mul_comm] using h
  have hHupper : 1 + Real.log (P * P : ℕ) ≤ 3 * l := by
    rw [hQlog]
    linarith only [hl1]
  have hscalar : C * (1 + Real.log (P * P : ℕ)) *
      (∑ m ∈ Icc 1 (P * P), primeOnly primePoleWitness m ^ 2) ≤
        (9 * C / (2 * Real.log 2)) * l ^ 2 := by
    calc
      _ ≤ C * (1 + Real.log (P * P : ℕ)) * (3 * l / (2 * Real.log 2)) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ ≤ C * (3 * l) * (3 * l / (2 * Real.log 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHupper hC.le) (by positivity)
      _ = _ := by ring
  have hr := hres (P * P) N hQ (by omega : 2 ≤ N) (primeOnly primePoleWitness)
  have hresLower : l ^ 3 / 16 - D * l ^ 2 ≤
      ∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 (P * P),
          primeOnly primePoleWitness m * ramanujanPrimeResidual m N n) ^ 2 := by
    dsimp only [D]
    linarith only [hr, htailLower, hscalar]
  have hdom := mul_le_mul_of_nonneg_right hlD (sq_nonneg l)
  have hresCube : l ^ 3 / 32 ≤
      ∑ n ∈ Icc 1 N,
        (∑ m ∈ Icc 1 (P * P),
          primeOnly primePoleWitness m * ramanujanPrimeResidual m N n) ^ 2 := by
    nlinarith only [hresLower, hdom]
  rw [(primePoleWitness_response_and_energy (P * P)).2, hQlog]
  have hscaled := mul_le_mul_of_nonneg_left hBtotal (sq_nonneg (2 * l))
  nlinarith only [hscaled, hresCube]

#print axioms harmonic_quotient_annulus_ge_log_sub_log_two
#print axioms eventually_coherentPrimeResidual_logarithmic_lower

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
