import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseFiniteMellin
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleSign

/-!
# Periodicity and the two-label arithmetic Mellin form

The off-diagonal terms involve a rational frequency and its reciprocal.
Their coefficients remain positive as the real Mellin parameter tends to one.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceNormalizedCosineMellin (lam : ℕ → ℝ) (r σ : ℝ) : ℝ :=
  (σ - 1) ^ 2 * (mellin (sourceCosineProfile lam r) ((σ : ℂ) / 2)).re

theorem sourceCosineProfile_one (lam : ℕ → ℝ) :
    sourceCosineProfile lam 1 = sourceGaussianProfile lam := by
  funext t
  apply tsum_congr
  intro n
  have hc : Real.cos (2 * Real.pi * (n : ℝ)) = 1 := by
    rw [show 2 * Real.pi * (n : ℝ) = n * (2 * Real.pi) by ring]
    exact Real.cos_nat_mul_two_pi n
  simp only [sourceCosineCoeff, mul_one, hc, Complex.ofReal_one]

theorem sourceCosineProfile_zero (lam : ℕ → ℝ) :
    sourceCosineProfile lam 0 = sourceGaussianProfile lam := by
  funext t
  simp only [sourceCosineProfile, sourceCosineCoeff, mul_zero, Real.cos_zero,
    Complex.ofReal_one, mul_one, sourceGaussianProfile]

theorem sourceCosineProfile_add_nat (lam : ℕ → ℝ) (r : ℝ) (k : ℕ) :
    sourceCosineProfile lam (r + k) = sourceCosineProfile lam r := by
  funext t
  apply tsum_congr
  intro n
  have hc : Real.cos (2 * Real.pi * ((n : ℝ) * (r + k))) =
      Real.cos (2 * Real.pi * ((n : ℝ) * r)) := by
    convert Real.cos_add_nat_mul_two_pi (2 * Real.pi * ((n : ℝ) * r)) (n * k) using 1
    congr 1
    push_cast
    ring
  simp only [sourceCosineCoeff, hc]

theorem sourceNormalizedCosineMellin_add_nat (lam : ℕ → ℝ) (r : ℝ) (k : ℕ) (σ : ℝ) :
    sourceNormalizedCosineMellin lam (r + k) σ = sourceNormalizedCosineMellin lam r σ := by
  simp only [sourceNormalizedCosineMellin, sourceCosineProfile_add_nat]

theorem tendsto_sourceNormalizedCosineMellin_one {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Tendsto (sourceNormalizedCosineMellin lam 1) (𝓝[>] 1)
      (𝓝 (sourcePoleNumerator hW 1).re) := by
  change Tendsto (fun σ : ℝ => (σ - 1) ^ 2 *
    (mellin (sourceCosineProfile lam 1) ((σ : ℂ) / 2)).re) _ _
  rw [sourceCosineProfile_one]
  exact tendsto_sq_mul_re_mellin_sourceGaussianProfile hW

def sourceTwoLabelCoeff (m n : ℕ) (c : ℝ) (i : ℕ) : ℝ :=
  (if i = m then 1 else 0) + (if i = n then c else 0)

private theorem twoLabel_sum (N m n : ℕ) (c : ℝ) (f : ℕ → ℝ)
    (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) :
    (∑ i ∈ Finset.Icc 1 N, sourceTwoLabelCoeff m n c i * f i) = f m + c * f n := by
  simp [sourceTwoLabelCoeff, add_mul, Finset.sum_add_distrib, ite_mul,
    Finset.sum_ite_eq', hm, hn]

theorem re_mellin_sourceTwoLabelProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {N m n : ℕ} (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) (c : ℝ)
    {σ : ℝ} (hσ : 1 < σ) :
    (mellin (sourceFiniteCosineProfile lam N (sourceTwoLabelCoeff m n c)) ((σ : ℂ) / 2)).re =
      (1 / (m : ℝ) + c ^ 2 / n) * (mellin (sourceCosineProfile lam 1) ((σ : ℂ) / 2)).re +
      c / n * (((m : ℝ) / n) ^ 2) ^ (-(σ / 2)) *
        (mellin (sourceCosineProfile lam ((m : ℝ) / n)) ((σ : ℂ) / 2)).re +
      c / m * (((n : ℝ) / m) ^ 2) ^ (-(σ / 2)) *
        (mellin (sourceCosineProfile lam ((n : ℝ) / m)) ((σ : ℂ) / 2)).re := by
  rw [re_mellin_sourceFiniteCosineProfile hW N _ hσ]
  let F : ℕ → ℕ → ℝ := fun i j =>
    (1 / (j : ℝ)) * (((i : ℝ) / j) ^ 2) ^ (-(σ / 2)) *
      (mellin (sourceCosineProfile lam ((i : ℝ) / j)) ((σ : ℂ) / 2)).re
  have he : (∑ i ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc 1 N,
      (sourceTwoLabelCoeff m n c i * sourceTwoLabelCoeff m n c j / j) *
        (((i : ℝ) / j) ^ 2) ^ (-(σ / 2)) *
          (mellin (sourceCosineProfile lam ((i : ℝ) / j)) ((σ : ℂ) / 2)).re) =
      F m m + c * F m n + c * (F n m + c * F n n) := by
    calc
      _ = ∑ i ∈ Finset.Icc 1 N, sourceTwoLabelCoeff m n c i *
          ∑ j ∈ Finset.Icc 1 N, sourceTwoLabelCoeff m n c j * F i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [F]
        ring
      _ = _ := by
        simp_rw [twoLabel_sum N m n c _ hm hn]
  rw [he]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  dsimp only [F]
  rw [div_self hm0, div_self hn0]
  simp only [one_pow, Real.one_rpow, mul_one]
  ring

end RHTower.WeilSingularArithmetic
