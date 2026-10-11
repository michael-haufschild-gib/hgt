import GaloisForLFunctions.RHTower.WeilLogShiftCosineGaussian

/-! The centered binomial phase sum is an exact cosine power. -/

open scoped BigOperators
open Filter Topology

noncomputable section
namespace RHTower

def finiteWeilBinomialCharacteristic (n : ℕ) (u : ℝ) : ℂ :=
  ∑ j : Fin (n + 1), (((n.choose (j : ℕ) : ℝ) / 2 ^ n : ℝ) : ℂ) *
    finiteWeilPhase (u * (((j : ℕ) : ℝ) - (n : ℝ) / 2))

theorem finiteWeilBinomialCharacteristic_eq (n : ℕ) (u : ℝ) :
    finiteWeilBinomialCharacteristic n u = (Real.cos (u / 2) : ℂ) ^ n := by
  symm
  simp only [Complex.ofReal_cos, Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [Complex.cos, div_pow, add_pow, Finset.sum_div,
    ← Fin.sum_univ_eq_sum_range (fun j => Complex.exp (((u : ℂ) / 2) * Complex.I) ^ j *
      Complex.exp (-((u : ℂ) / 2) * Complex.I) ^ (n - j) * (n.choose j : ℂ) / 2 ^ n)]
  unfold finiteWeilBinomialCharacteristic
  apply Finset.sum_congr rfl
  intro j hjmem
  have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold finiteWeilPhase
  push_cast [Nat.cast_sub hj]
  rw [show (j : ℂ) * (((u : ℂ) / 2) * Complex.I) +
      ((n : ℂ) - j) * (-((u : ℂ) / 2) * Complex.I) =
      ((u : ℂ) * ((j : ℂ) - (n : ℂ) / 2)) * Complex.I by ring]
  ring

theorem tendsto_finiteWeilBinomialCharacteristic_gaussian (α : ℝ) :
    Tendsto (fun r : ℕ => finiteWeilBinomialCharacteristic (r + 1)
      (α / Real.sqrt ((r + 1 : ℕ) : ℝ))) atTop (𝓝 ((Real.exp (-(α ^ 2 / 8)) : ℝ) : ℂ)) := by
  have h := (tendsto_finiteWeil_cosine_gaussian (α / 2)).comp
    (tendsto_atTop_mono (fun r : ℕ => Nat.le_succ r) tendsto_id)
  rw [show -((α / 2) ^ 2 / 2) = -(α ^ 2 / 8) by ring] at h
  have hc := (Complex.continuous_ofReal.tendsto _).comp h
  convert hc using 1
  funext r
  change finiteWeilBinomialCharacteristic (r + 1) (α / Real.sqrt ((r + 1 : ℕ) : ℝ)) =
    ((Real.cos ((α / 2) / Real.sqrt ((r + 1 : ℕ) : ℝ)) ^ (r + 1) : ℝ) : ℂ)
  rw [finiteWeilBinomialCharacteristic_eq, Complex.ofReal_pow,
    show (α / Real.sqrt ((r + 1 : ℕ) : ℝ)) / 2 = (α / 2) / Real.sqrt ((r + 1 : ℕ) : ℝ) by ring]

end RHTower
