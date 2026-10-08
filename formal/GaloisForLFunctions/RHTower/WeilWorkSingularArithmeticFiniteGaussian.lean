import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteWeight
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialGaussian

/-!
# One extraction constant for every finite polynomial

The coefficient budget is explicit. In particular its dependence on the
polynomial length is not hidden in an existential error constant.
-/

open Complex MeasureTheory Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def sourceFiniteGaussianSum (lam : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) (T : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ((c m : ℂ) * c n / n) * sourceTwistedGaussianSum lam T ((m : ℝ) / n)

theorem integral_sourceZetaPairing_finite_eq_scaled {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceFiniteWeight N c ((3 / 2 : ℂ) + t * I)) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, ((c m : ℂ) * c n / m) *
        ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
          ((((m : ℝ) / n : ℝ) : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) *
            gaussWeight T ((3 / 2 : ℂ) + t * I)) := by
  let S := Finset.Icc 1 N
  let f : ℕ → ℕ → ℝ → ℂ := fun m n t => ((c m : ℂ) * c n / m) *
    (sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      ((((m : ℝ) / n : ℝ) : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) *
        gaussWeight T ((3 / 2 : ℂ) + t * I)))
  have hi (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) : Integrable (f m n) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact (integrable_sourceZetaPairing_scaled_gaussian hW hT (div_pos hmR hnR)).const_mul _
  have he (t : ℝ) : sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceFiniteWeight N c ((3 / 2 : ℂ) + t * I) =
        ∑ m ∈ S, ∑ n ∈ S, f m n t := by
    rw [sourceFiniteWeight_expansion]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    ring
  simp_rw [he]
  rw [integral_finsetSum S (fun m hm => integrable_finsetSum S (hi m hm))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finsetSum S (hi m hm)]
  apply Finset.sum_congr rfl
  intro n _
  exact integral_const_mul _ _

/-- Every finite length and coefficient vector shares the same source constant. -/
theorem exists_norm_source_finite_contour_sub_gaussian_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : ℕ → ℝ) (T : ℝ), 1 ≤ T →
      ‖(∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
        gaussWeight T ((3 / 2 : ℂ) + t * I) * sourceFiniteWeight N c ((3 / 2 : ℂ) + t * I)) -
        (4 * Real.pi : ℂ) * sourceFiniteGaussianSum lam N c T‖ ≤
      C * T ^ (5 / 6 : ℝ) *
        (∑ m ∈ Finset.Icc 1 N, |c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) *
        (∑ n ∈ Finset.Icc 1 N, |c n| * (n : ℝ) ^ (1 / 8 : ℝ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_source_scaled_contour_sub_gaussian_le hW
  refine ⟨C, hC0, fun N c T hT => ?_⟩
  let S := Finset.Icc 1 N
  let J : ℝ → ℂ := fun r => ∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
    ((r : ℂ) ^ (1 - ((3 / 2 : ℂ) + t * I)) * gaussWeight T ((3 / 2 : ℂ) + t * I))
  let e : ℝ → ℂ := fun r => J r - (4 * Real.pi * r : ℂ) * sourceTwistedGaussianSum lam T r
  have he (r : ℝ) (hr : 0 < r) : ‖e r‖ ≤ C * r ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ) :=
    hC r hr T hT
  rw [integral_sourceZetaPairing_finite_eq_scaled hW N c hT]
  have hid : (∑ m ∈ S, ∑ n ∈ S, ((c m : ℂ) * c n / m) * J ((m : ℝ) / n)) -
      (4 * Real.pi : ℂ) * sourceFiniteGaussianSum lam N c T =
        ∑ m ∈ S, ∑ n ∈ S, ((c m : ℂ) * c n / m) * e ((m : ℝ) / n) := by
    unfold sourceFiniteGaussianSum
    change (∑ m ∈ S, ∑ n ∈ S, ((c m : ℂ) * c n / m) * J ((m : ℝ) / n)) -
      (4 * Real.pi : ℂ) * (∑ m ∈ S, ∑ n ∈ S,
        ((c m : ℂ) * c n / n) * sourceTwistedGaussianSum lam T ((m : ℝ) / n)) = _
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hm).1)
    have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (Finset.mem_Icc.mp hn).1)
    dsimp only [e]
    push_cast
    field_simp [hmC, hnC]
  change ‖(∑ m ∈ S, ∑ n ∈ S, ((c m : ℂ) * c n / m) * J ((m : ℝ) / n)) - _‖ ≤ _
  rw [hid]
  have hterm (m : ℕ) (hm : m ∈ S) (n : ℕ) (hn : n ∈ S) :
      ‖((c m : ℂ) * c n / m) * e ((m : ℝ) / n)‖ ≤
        C * T ^ (5 / 6 : ℝ) * (|c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) *
          (|c n| * (n : ℝ) ^ (1 / 8 : ℝ)) := by
    have hmR : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hp : ((m : ℝ) / n) ^ (-1 / 8 : ℝ) / m =
        (m : ℝ) ^ (-9 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
      rw [Real.div_rpow hmR.le hnR.le]
      have hm' : (m : ℝ) ^ (-1 / 8 : ℝ) / m = (m : ℝ) ^ (-9 / 8 : ℝ) := by
        calc
          _ = (m : ℝ) ^ (-1 / 8 : ℝ) / (m : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (m : ℝ) ^ ((-1 / 8 : ℝ) - 1) := (Real.rpow_sub hmR _ _).symm
          _ = _ := by norm_num
      have hn' : ((n : ℝ) ^ (-1 / 8 : ℝ))⁻¹ = (n : ℝ) ^ (1 / 8 : ℝ) := by
        rw [← Real.rpow_neg hnR.le]
        norm_num
      calc
        _ = ((m : ℝ) ^ (-1 / 8 : ℝ) / m) * ((n : ℝ) ^ (-1 / 8 : ℝ))⁻¹ := by ring
        _ = _ := by rw [hm', hn']
    rw [norm_mul, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_natCast]
    calc
      _ ≤ (|c m| * |c n| / m) * (C * ((m : ℝ) / n) ^ (-1 / 8 : ℝ) * T ^ (5 / 6 : ℝ)) :=
        mul_le_mul_of_nonneg_left (he _ (div_pos hmR hnR)) (by positivity)
      _ = C * T ^ (5 / 6 : ℝ) * |c m| * |c n| * (((m : ℝ) / n) ^ (-1 / 8 : ℝ) / m) := by ring
      _ = _ := by rw [hp]; ring
  calc
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, ‖((c m : ℂ) * c n / m) * e ((m : ℝ) / n)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => norm_sum_le _ _)
    _ ≤ ∑ m ∈ S, ∑ n ∈ S, C * T ^ (5 / 6 : ℝ) *
        (|c m| * (m : ℝ) ^ (-9 / 8 : ℝ)) * (|c n| * (n : ℝ) ^ (1 / 8 : ℝ)) :=
      Finset.sum_le_sum fun m hm => Finset.sum_le_sum (hterm m hm)
    _ = _ := by
      simp only [S, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]

end RHTower.WeilSingularArithmetic
