import GaloisForLFunctions.ExceptionalLayerTheory.NonstationaryGaussianCorrelations
import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiGramSchur

/-!
# Nonstationary Gaussian type-II energy on dyadic rectangles

Below the first integer resonance, off-diagonal correlations cost the
reciprocal integer gap. Harmonic row sums and the symmetric Schur bound
then give a logarithmic loss. Both the product cutoff and the real
Gaussian damping remain in the estimate.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- A harmonic majorant for the Gaussian correlations on a dyadic rectangle. -/
def gaussianDyadicCorrelationKernel (ξ : ℝ) (D M m n : ℕ) : ℝ :=
  if m = n then D else Real.pi / (ξ * D * M) / |(m : ℝ) - n|

/-- Diagonal mass plus the harmonic off-diagonal row cost. -/
def gaussianDyadicRowBound (ξ : ℝ) (D M : ℕ) : ℝ :=
  D + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) / (ξ * D * M)

private theorem quadratic_gap_factor (m n : ℕ) :
    |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| = ((m : ℝ) + n) * |(m : ℝ) - n| := by
  rw [show (m : ℝ) ^ 2 - (n : ℝ) ^ 2 = ((m : ℝ) + n) * ((m : ℝ) - n) by ring,
    abs_mul, abs_of_nonneg (by positivity)]

private theorem gaussian_rectangle_damping_le {α : ℝ} (hα : 0 ≤ α)
    {D M P m n : ℕ} (hDP : D ≤ P) (hMm : M ≤ m) (hMn : M ≤ n) :
    Real.exp (-(α * ((m : ℝ) ^ 2 + (n : ℝ) ^ 2)) * (P : ℝ) ^ 2) ≤
      Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have hD : (D : ℝ) ^ 2 ≤ (P : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hDP 2
  have hm : (M : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hMm 2
  have hn : (M : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hMn 2
  have hs : 2 * (M : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 + (n : ℝ) ^ 2 := by linarith only [hm, hn]
  have hp := mul_le_mul hs hD (sq_nonneg (D : ℝ)) (by positivity)
  have hneg := mul_le_mul_of_nonpos_left hp (neg_nonpos.mpr hα)
  apply Real.exp_le_exp.mpr
  nlinarith only [hneg]

private theorem norm_gaussian_rectangle_correlation_le {α ξ : ℝ}
    (hα : 0 ≤ α) (hξ : 0 < ξ) (t : ℝ) {D M P Q m n : ℕ} (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hDP : D ≤ P) (hQ : Q ≤ 2 * D) (hm : m ∈ Ico M (2 * M)) (hn : n ∈ Ico M (2 * M))
    (hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi) :
    ‖∑ d ∈ Ico P Q, gaussianPrimePhase α ξ t (d * m) *
      (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * n))‖ ≤
      gaussianDyadicCorrelationKernel ξ D M m n *
        Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have hP : 1 ≤ P := hD.trans hDP
  have hm1 : 1 ≤ m := hM.trans (mem_Ico.mp hm).1
  have hn1 : 1 ≤ n := hM.trans (mem_Ico.mp hn).1
  have hdamp := gaussian_rectangle_damping_le hα hDP (mem_Ico.mp hm).1 (mem_Ico.mp hn).1
  by_cases hmn : m = n
  · subst n
    have hh := norm_sum_gaussianPrimePhase_correlation_le hα ξ t hP hm1 hm1 (Q := Q)
    simp only [gaussianPairBound, sub_self, mul_zero, quadraticSumBound] at hh
    rw [if_pos True.intro] at hh
    unfold gaussianDyadicCorrelationKernel
    rw [if_pos rfl]
    refine hh.trans (mul_le_mul ?_ hdamp (Real.exp_pos _).le (Nat.cast_nonneg D))
    exact_mod_cast (show Q - P ≤ D by omega)
  · have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hP0 : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
    have hgap : 0 < |(m : ℝ) - n| := abs_pos.mpr (sub_ne_zero.mpr (by exact_mod_cast hmn))
    have hsum : 2 * (M : ℝ) ≤ (m : ℝ) + n := by
      have h₁ : (M : ℝ) ≤ m := by exact_mod_cast (mem_Ico.mp hm).1
      have h₂ : (M : ℝ) ≤ n := by exact_mod_cast (mem_Ico.mp hn).1
      linarith only [h₁, h₂]
    have hsqpos : 0 < |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
      rw [quadratic_gap_factor]
      exact mul_pos (by linarith only [hsum, hM0]) hgap
    have hu : ξ * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2) ≠ 0 :=
      mul_ne_zero hξ.ne' (abs_pos.mp hsqpos)
    have habs : |ξ * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)| = ξ * |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| := by
      rw [abs_mul, abs_of_pos hξ]
    have hmax : |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| ≤ 4 * (M : ℝ) ^ 2 := by
      have hm2 : (m : ℝ) ^ 2 ≤ (2 * (M : ℝ)) ^ 2 := by
        exact_mod_cast Nat.pow_le_pow_left (mem_Ico.mp hm).2.le 2
      have hn2 : (n : ℝ) ^ 2 ≤ (2 * (M : ℝ)) ^ 2 := by
        exact_mod_cast Nat.pow_le_pow_left (mem_Ico.mp hn).2.le 2
      apply abs_le.mpr
      constructor <;> nlinarith only [hm2, hn2, sq_nonneg (m : ℝ), sq_nonneg (n : ℝ)]
    have hderiv : |ξ * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)| * Q / Real.pi ≤ 1 / 2 := by
      apply (div_le_iff₀ Real.pi_pos).mpr
      rw [habs]
      have hh : ξ * |(m : ℝ) ^ 2 - (n : ℝ) ^ 2| * Q ≤
          ξ * (4 * (M : ℝ) ^ 2) * (2 * (D : ℝ)) := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left hmax hξ.le)
          (by exact_mod_cast hQ) (Nat.cast_nonneg Q) (by positivity)
      nlinarith only [hh, hband]
    have hcoef : 2 * Real.pi / (|ξ * ((m : ℝ) ^ 2 - (n : ℝ) ^ 2)| * P) ≤
        Real.pi / (ξ * D * M) / |(m : ℝ) - n| := by
      rw [habs, div_div]
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      rw [quadratic_gap_factor]
      have hh : ξ * (2 * (M : ℝ) * |(m : ℝ) - n|) * D ≤
          ξ * (((m : ℝ) + n) * |(m : ℝ) - n|) * P := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hgap.le) hξ.le)
          (by exact_mod_cast hDP) (Nat.cast_nonneg D) (by positivity)
      nlinarith only [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]
    have hh := norm_gaussian_correlation_first_derivative_le hα t hP hm1 hn1 hu hderiv
    refine hh.trans ?_
    rw [gaussianDyadicCorrelationKernel, if_neg hmn]
    exact mul_le_mul hcoef hdamp (Real.exp_pos _).le (by positivity)

private theorem masked_gaussian_correlation_interval (α ξ t : ℝ) (A B D m n : ℕ) :
    (∑ d ∈ Ico D (2 * D), maskedGaussianPhase α ξ t A B d m *
      (starRingEnd ℂ) (maskedGaussianPhase α ξ t A B d n)) =
      ∑ d ∈ Ico (max D (max ((A - 1) / m + 1) ((A - 1) / n + 1)))
          (min (2 * D) (min ((B - 1) / m + 1) ((B - 1) / n + 1))),
        gaussianPrimePhase α ξ t (d * m) * (starRingEnd ℂ) (gaussianPrimePhase α ξ t (d * n)) := by
  classical
  have hs : (Ico D (2 * D)).filter (fun d => d ∈ fibreIco A B m ∧ d ∈ fibreIco A B n) =
      Ico (max D (max ((A - 1) / m + 1) ((A - 1) / n + 1)))
        (min (2 * D) (min ((B - 1) / m + 1) ((B - 1) / n + 1))) := by
    ext d
    simp only [mem_filter, fibreIco, mem_Ico, max_le_iff, lt_min_iff]
    tauto
  rw [← hs, sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases h₁ : d ∈ fibreIco A B m <;> by_cases h₂ : d ∈ fibreIco A B n <;>
    simp [maskedGaussianPhase, h₁, h₂]

/-- Product cutoffs preserve the reciprocal-gap majorant on a dyadic rectangle. -/
theorem norm_maskedGaussian_dyadic_correlation_le {α ξ : ℝ} (hα : 0 ≤ α) (hξ : 0 < ξ)
    (t : ℝ) (A B : ℕ) {D M m n : ℕ} (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hm : m ∈ Ico M (2 * M)) (hn : n ∈ Ico M (2 * M))
    (hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi) :
    ‖∑ d ∈ Ico D (2 * D), maskedGaussianPhase α ξ t A B d m *
      (starRingEnd ℂ) (maskedGaussianPhase α ξ t A B d n)‖ ≤
      gaussianDyadicCorrelationKernel ξ D M m n *
        Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  rw [masked_gaussian_correlation_interval α ξ t A B D m n]
  exact norm_gaussian_rectangle_correlation_le hα hξ t hD hM
    (le_max_left _ _) (min_le_left _ _) hm hn hband

private theorem gaussianDyadicCorrelationKernel_nonneg {ξ : ℝ} (hξ : 0 < ξ)
    (D M m n : ℕ) : 0 ≤ gaussianDyadicCorrelationKernel ξ D M m n := by
  unfold gaussianDyadicCorrelationKernel
  split_ifs <;> positivity

/-- Harmonic row sums aggregate all off-diagonal quadratic gaps. -/
theorem sum_gaussianDyadicCorrelationKernel_le {ξ : ℝ} (hξ : 0 < ξ)
    (D M : ℕ) {m : ℕ} (hm : m ∈ Ico M (2 * M)) :
    ∑ n ∈ Ico M (2 * M), gaussianDyadicCorrelationKernel ξ D M m n ≤
      gaussianDyadicRowBound ξ D M := by
  have he : (∑ n ∈ Ico M (2 * M), gaussianDyadicCorrelationKernel ξ D M m n) =
      (Real.pi / (ξ * D * M)) *
        (∑ n ∈ (Ico M (2 * M)).erase m, 1 / |(n : ℝ) - m|) + D := by
    rw [← sum_erase_add (Ico M (2 * M)) (gaussianDyadicCorrelationKernel ξ D M m) hm]
    have hself : gaussianDyadicCorrelationKernel ξ D M m m = D := by
      simp [gaussianDyadicCorrelationKernel]
    rw [hself, mul_sum]
    congr 1
    apply sum_congr rfl
    intro n hn
    rw [gaussianDyadicCorrelationKernel, if_neg (Ne.symm (mem_erase.mp hn).1), abs_sub_comm]
    ring
  have hsub : (Ico M (2 * M)).erase m ⊆ (range (2 * M)).erase m := by
    intro n hn
    exact mem_erase.mpr ⟨(mem_erase.mp hn).1,
      mem_range.mpr (mem_Ico.mp (mem_erase.mp hn).2).2⟩
  have hsum : (∑ n ∈ (Ico M (2 * M)).erase m, 1 / |(n : ℝ) - m|) ≤
      2 * (1 + Real.log ((2 * M : ℕ) : ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
      (sum_inv_abs_int_dist_le (mem_Ico.mp hm).2)
  rw [he]
  calc
    _ ≤ Real.pi / (ξ * D * M) * (2 * (1 + Real.log ((2 * M : ℕ) : ℝ))) + D := by
      gcongr
    _ = gaussianDyadicRowBound ξ D M := by
      unfold gaussianDyadicRowBound
      push_cast
      ring

/-- A dyadic Gaussian type-II sum has logarithmic off-diagonal cost.
The coefficient energies, real damping and product cutoff all remain explicit. -/
theorem norm_maskedGaussian_dyadic_nonstationary_sq_le {α ξ : ℝ}
    (hα : 0 ≤ α) (hξ : 0 < ξ) (t : ℝ) (A B : ℕ) {D M : ℕ}
    (hD : 1 ≤ D) (hM : 1 ≤ M) (hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi)
    (a b : ℕ → ℂ) :
    ‖∑ d ∈ Ico D (2 * D), a d *
      ∑ m ∈ Ico M (2 * M), b m * maskedGaussianPhase α ξ t A B d m‖ ^ 2 ≤
      (∑ d ∈ Ico D (2 * D), ‖a d‖ ^ 2) *
        (∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) *
          Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) * gaussianDyadicRowBound ξ D M := by
  have hschur := RiemannGaussian.finset_symmetric_schur_quadratic_le
    (Ico M (2 * M)) (fun m => ‖b m‖) (gaussianDyadicCorrelationKernel ξ D M)
    (gaussianDyadicRowBound ξ D M) (gaussianDyadicCorrelationKernel_nonneg hξ D M)
    (fun m n => by
      by_cases hmn : m = n
      · subst n; rfl
      · simp only [gaussianDyadicCorrelationKernel, if_neg hmn, if_neg (Ne.symm hmn), abs_sub_comm])
    (fun m hm => sum_gaussianDyadicCorrelationKernel_le hξ D M hm)
  have hinner : (∑ d ∈ Ico D (2 * D),
      ‖∑ m ∈ Ico M (2 * M), b m * maskedGaussianPhase α ξ t A B d m‖ ^ 2) ≤
      Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
        (gaussianDyadicRowBound ξ D M * ∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2) := by
    refine (sum_normSq_inner_le (Ico D (2 * D)) (Ico M (2 * M)) b
      (maskedGaussianPhase α ξ t A B)).trans ?_
    calc
      _ ≤ ∑ m ∈ Ico M (2 * M), ∑ n ∈ Ico M (2 * M), ‖b m‖ * ‖b n‖ *
          (gaussianDyadicCorrelationKernel ξ D M m n *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) := by
        apply sum_le_sum
        intro m hm
        apply sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_left
          (norm_maskedGaussian_dyadic_correlation_le hα hξ t A B hD hM hm hn hband)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
          (∑ m ∈ Ico M (2 * M), ∑ n ∈ Ico M (2 * M),
            ‖b m‖ * ‖b n‖ * gaussianDyadicCorrelationKernel ξ D M m n) := by
        simp_rw [mul_sum]
        apply sum_congr rfl
        intro m _
        apply sum_congr rfl
        intro n _
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hschur (Real.exp_pos _).le
  refine (norm_bilinear_sq_le (Ico D (2 * D)) a _).trans ?_
  calc
    _ ≤ (∑ d ∈ Ico D (2 * D), ‖a d‖ ^ 2) *
        (Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
          (gaussianDyadicRowBound ξ D M * ∑ m ∈ Ico M (2 * M), ‖b m‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hinner (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by ring

/-- A dyadic portion of the literal Gaussian Vaughan type-II term. -/
def gaussianVaughanDyadicSum (σ α ξ t : ℝ) (A B D M U V : ℕ) : ℂ :=
  ∑ d ∈ Ico D (2 * D), ∑ m ∈ Ico M (2 * M),
    if d * m ∈ Ico A B then
      ((typeIILong U d : ℝ) : ℂ) * ((typeIIShort V m : ℝ) : ℂ) *
        gaussianPrimeWeight σ α ξ t (d * m)
    else 0

/-- The harmonic bound applies to the actual arithmetic coefficients and
abscissa weight, with no assumed arithmetic cancellation. -/
theorem norm_gaussianVaughan_dyadic_nonstationary_sq_le {α ξ : ℝ}
    (hα : 0 ≤ α) (hξ : 0 < ξ) (σ t : ℝ) {A B D M : ℕ}
    (hA : 1 ≤ A) (hB : 1 ≤ B) (hD : 1 ≤ D) (hM : 1 ≤ M)
    (hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi) (U V : ℕ) :
    ‖gaussianVaughanDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
      (∑ d ∈ Ico D (2 * D), ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
        (∑ m ∈ Ico M (2 * M), ‖((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) *
          Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) * gaussianDyadicRowBound ξ D M := by
  have he : gaussianVaughanDyadicSum σ α ξ t A B D M U V =
      ∑ d ∈ Ico D (2 * D),
        (((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          ∑ m ∈ Ico M (2 * M),
            (((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)) *
              maskedGaussianPhase α ξ t A B d m := by
    unfold gaussianVaughanDyadicSum
    apply sum_congr rfl
    intro d hd
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    have hm1 : 1 ≤ m := hM.trans (mem_Ico.mp hm).1
    have hf : d * m ∈ Ico A B ↔ d ∈ fibreIco A B m := mem_fibre_iff hm1 hA hB d
    by_cases hc : d * m ∈ Ico A B
    · rw [if_pos hc, maskedGaussianPhase, if_pos (hf.mp hc)]
      simp only [gaussianPrimeWeight, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg d) (Nat.cast_nonneg m), Complex.ofReal_mul]
      ring
    · rw [if_neg hc, maskedGaussianPhase, if_neg (fun hh => hc (hf.mpr hh)), mul_zero, mul_zero]
  rw [he]
  exact norm_maskedGaussian_dyadic_nonstationary_sq_le hα hξ t A B hD hM hband _ _

/-- The normalized row cost has inverse-height rather than inverse-square-root-height loss
when the quadratic scale is `ξD²M²`. -/
theorem gaussianDyadicRowBound_normalized {ξ : ℝ} (hξ : 0 < ξ) {D M : ℕ}
    (hD : 1 ≤ D) (hM : 1 ≤ M) :
    gaussianDyadicRowBound ξ D M / ((D : ℝ) * M) =
      1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
        (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by
  have hD0 : (D : ℝ) ≠ 0 := by exact_mod_cast (show D ≠ 0 by omega)
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  unfold gaussianDyadicRowBound
  field_simp [hξ.ne', hD0, hM0]

#print axioms norm_maskedGaussian_dyadic_correlation_le
#print axioms sum_gaussianDyadicCorrelationKernel_le
#print axioms norm_maskedGaussian_dyadic_nonstationary_sq_le
#print axioms norm_gaussianVaughan_dyadic_nonstationary_sq_le
#print axioms gaussianDyadicRowBound_normalized

end GaloisForLFunctions.ExceptionalLayerTheory
