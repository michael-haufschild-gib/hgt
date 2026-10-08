import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCosineMellin
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticFiniteBound
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellinBound
import GaloisForLFunctions.RHTower.WeilDilationRigidity

/-!
# Finite arithmetic Gaussian forms have uniformly bounded real Mellin transforms

The signed small-parameter bound is supplied by full positivity of the original
source. Absolute convergence and the large-parameter bound are supplied separately.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceFiniteCosineProfile (lam : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ((c m : ℂ) * c n / n) * sourceScaledCosineProfile lam ((m : ℝ) / n) t

theorem sourceFiniteCosineProfile_eq_gaussian (lam : ℕ → ℝ) (N : ℕ) (c : ℕ → ℝ)
    {t : ℝ} (ht : 0 < t) :
    sourceFiniteCosineProfile lam N c t =
      sourceFiniteGaussianSum lam N c (Real.sqrt (4 * Real.pi / t)) := by
  simp only [sourceFiniteCosineProfile, sourceFiniteGaussianSum,
    sourceScaledCosineProfile_eq_twisted ht]

private theorem mellinConvergent_sum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℂ)
    {s : ℂ} (hF : ∀ i ∈ S, MellinConvergent (F i) s) :
    MellinConvergent (fun t => ∑ i ∈ S, F i t) s := by
  unfold MellinConvergent at *
  simp_rw [Finset.smul_sum]
  exact integrable_finsetSum S hF

theorem mellinConvergent_sourceFiniteCosineProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (sourceFiniteCosineProfile lam N c) (s / 2) := by
  apply mellinConvergent_sum
  intro m hm
  apply mellinConvergent_sum
  intro n hn
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  exact (mellinConvergent_sourceScaledCosineProfile hW (div_pos hm0 hn0) hs).const_smul
    ((c m : ℂ) * c n / n)

theorem re_mellin_sourceFiniteCosineProfile {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (N : ℕ) (c : ℕ → ℝ) {σ : ℝ} (hσ : 1 < σ) :
    (mellin (sourceFiniteCosineProfile lam N c) ((σ : ℂ) / 2)).re =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (c m * c n / n) * (((m : ℝ) / n) ^ 2) ^ (-(σ / 2)) *
          (mellin (sourceCosineProfile lam ((m : ℝ) / n)) ((σ : ℂ) / 2)).re := by
  have hterm (m : ℕ) (hm : m ∈ Finset.Icc 1 N) (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      MellinConvergent (fun t => ((c m : ℂ) * c n / n) *
        sourceScaledCosineProfile lam ((m : ℝ) / n) t) ((σ : ℂ) / 2) := by
    have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact (mellinConvergent_sourceScaledCosineProfile hW (div_pos hm0 hn0)
      (s := (σ : ℂ)) hσ).const_smul ((c m : ℂ) * c n / n)
  change (mellin (fun t => ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    ((c m : ℂ) * c n / n) * sourceScaledCosineProfile lam ((m : ℝ) / n) t)
    ((σ : ℂ) / 2)).re = _
  rw [mellin_finset_sum_of_convergent _ _
    (fun m hm => mellinConvergent_sum _ _ (hterm m hm)), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mellin_finset_sum_of_convergent _ _ (hterm m hm), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have he : (c m : ℂ) * c n / n = ((c m * c n / n : ℝ) : ℂ) := by push_cast; rfl
  change (mellin (fun t => ((c m : ℂ) * c n / n) •
    sourceScaledCosineProfile lam ((m : ℝ) / n) t) ((σ : ℂ) / 2)).re = _
  rw [mellin_const_smul, he]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [re_mellin_sourceScaledCosineProfile lam (div_pos hm0 hn0)]
  ring

theorem exists_re_sourceFiniteCosineProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (N : ℕ) (c : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      (sourceFiniteCosineProfile lam N c t).re ≤ C * t ^ (-5 / 12 : ℝ) := by
  obtain ⟨D, _, hD⟩ := exists_re_sourceFiniteGaussianSum_energy_le hW
  let A : ℝ := D * sourceFiniteEnergy N c * ((N : ℝ) + 1) ^ (9 / 8 : ℝ)
  refine ⟨|A| * (4 * Real.pi) ^ (5 / 12 : ℝ), by positivity, fun t ht ht1 => ?_⟩
  have hT : 1 ≤ Real.sqrt (4 * Real.pi / t) := by
    apply Real.one_le_sqrt.mpr
    apply (le_div_iff₀ ht).mpr
    nlinarith [Real.pi_gt_three]
  rw [sourceFiniteCosineProfile_eq_gaussian lam N c ht]
  calc
    _ ≤ A * (Real.sqrt (4 * Real.pi / t)) ^ (5 / 6 : ℝ) := hD N c _ hT
    _ ≤ |A| * (Real.sqrt (4 * Real.pi / t)) ^ (5 / 6 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 4 * Real.pi / t)]
      norm_num only [show (1 / 2 : ℝ) * (5 / 6) = 5 / 12 by norm_num]
      rw [Real.div_rpow (by positivity : 0 ≤ 4 * Real.pi) ht.le,
        div_eq_mul_inv, Real.rpow_neg ht.le]
      ring

private theorem profile_norm_bound_sum {ι : Type*} (S : Finset ι) (F : ι → ℝ → ℂ)
    (hF : ∀ i ∈ S, ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖F i t‖ ≤ C / t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖∑ i ∈ S, F i t‖ ≤ C / t := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, le_rfl, fun t _ => by simp⟩
  | @insert i S hi ih =>
    obtain ⟨A, hA0, hA⟩ := hF i (by simp)
    obtain ⟨B, hB0, hB⟩ := ih (fun j hj => hF j (by simp [hj]))
    refine ⟨A + B, add_nonneg hA0 hB0, fun t ht => ?_⟩
    rw [Finset.sum_insert hi, add_div]
    exact (norm_add_le (F i t) (∑ j ∈ S, F j t)).trans
      (add_le_add (hA t ht) (hB t ht))

theorem exists_norm_sourceFiniteCosineProfile_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (N : ℕ) (c : ℕ → ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, 0 < t → ‖sourceFiniteCosineProfile lam N c t‖ ≤ D / t := by
  apply profile_norm_bound_sum
  intro m hm
  apply profile_norm_bound_sum
  intro n hn
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  obtain ⟨C, hC0, hC⟩ := exists_norm_sourceScaledCosineProfile_le hW (div_pos hm0 hn0)
  refine ⟨‖(c m : ℂ) * c n / n‖ * C, by positivity, fun t ht => ?_⟩
  rw [norm_mul]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_left (hC t ht) (norm_nonneg ((c m : ℂ) * c n / n))

theorem exists_re_mellin_sourceFiniteCosineProfile_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (N : ℕ) (c : ℕ → ℝ) :
    ∃ B : ℝ, ∀ σ : ℝ, 1 < σ → σ < 3 / 2 →
      (mellin (sourceFiniteCosineProfile lam N c) ((σ : ℂ) / 2)).re ≤ B :=
  exists_re_mellin_le_of_profile_bounds (sourceFiniteCosineProfile lam N c)
    (fun _ hσ _ => mellinConvergent_sourceFiniteCosineProfile hW N c (by simpa using hσ))
    (exists_re_sourceFiniteCosineProfile_le hW N c)
    (exists_norm_sourceFiniteCosineProfile_le hW N c)

end RHTower.WeilSingularArithmetic
