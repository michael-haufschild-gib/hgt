import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# The dyadic split with one kernel constant per block

The dyadic decomposition charges the kernel's decay once per block, so nothing forces the kernel's
*size* to be charged once for the whole range.  Replacing the single constant `C` of `G ≤ C/t` by a
sequence `C m` valid on the `m`-th block turns the geometric sums into weighted geometric sums,

`∫_{t₀}^{t₀2^M} F·G ≤ ∑_{m < M} C_m·((K√2/√t₀)(√2/2)^m + 2L)`,

for a block moment `∫_{block m} F ≤ K√(t₀2^{m+1}) + L(t₀2^{m+1})`.  Taking `C_m` constant recovers the
unweighted statement, since `∑(√2/2)^m ≤ (1 − √2/2)⁻¹` and `∑_{m<M} 1 = M`.

This is what a factor whose size *decays in the height* needs: a bound that varies with `t` is charged
its block maximum, and a decaying block maximum then beats the constant one by the whole weighted sum.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory Set

/-- **The dyadic decomposition with a kernel constant per block.** -/
theorem integral_mul_kernel_le_sum_dyadic_var {F G : ℝ → ℝ} {C : ℕ → ℝ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hC : ∀ m, 0 ≤ C m) (hF : ∀ t, 0 ≤ F t) {M : ℕ}
    (hG : ∀ m, m < M → ∀ t, t₀ * 2 ^ m ≤ t → t ≤ t₀ * 2 ^ (m + 1) → G t ≤ C m / t)
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ ∑ m ∈ Finset.range M,
          (C m / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t := by
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun t => F t * G t) (μ := volume) (a := fun m : ℕ => t₀ * 2 ^ m) (n := M) hFGint
  have h0 : t₀ * (2 : ℝ) ^ (0 : ℕ) = t₀ := by norm_num
  rw [h0] at hsplit
  rw [← hsplit]
  refine Finset.sum_le_sum fun m hm => ?_
  have hmM : m < M := Finset.mem_range.1 hm
  have hpos : 0 < t₀ * 2 ^ m := by positivity
  have hstep : (2 : ℝ) ^ m ≤ 2 ^ (m + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hle : t₀ * 2 ^ m ≤ t₀ * 2 ^ (m + 1) := mul_le_mul_of_nonneg_left hstep ht₀.le
  have hmono : ∀ t ∈ Set.Icc (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)),
      F t * G t ≤ F t * (C m / (t₀ * 2 ^ m)) := by
    intro t ht
    have hker : G t ≤ C m / (t₀ * 2 ^ m) :=
      le_trans (hG m hmM t ht.1 ht.2) (div_le_div_of_nonneg_left (hC m) hpos ht.1)
    exact mul_le_mul_of_nonneg_left hker (hF t)
  calc (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t * G t)
      ≤ ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t * (C m / (t₀ * 2 ^ m)) :=
        intervalIntegral.integral_mono_on hle (hFGint m hmM)
          ((hFint m hmM).mul_const _) hmono
    _ = (C m / (t₀ * 2 ^ m)) * ∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t := by
        rw [intervalIntegral.integral_mul_const]; ring

/-- **The vertical integral against an affine block moment, with a kernel constant per block.** -/
theorem integral_mul_kernel_le_of_affine_block_moment_var {F G : ℝ → ℝ} {C : ℕ → ℝ} {K L t₀ : ℝ}
    (ht₀ : 0 < t₀) (hC : ∀ m, 0 ≤ C m) (hF : ∀ t, 0 ≤ F t) {M : ℕ}
    (hG : ∀ m, m < M → ∀ t, t₀ * 2 ^ m ≤ t → t ≤ t₀ * 2 ^ (m + 1) → G t ≤ C m / t)
    (hFint : ∀ m, m < M → IntervalIntegrable F volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hFGint : ∀ m, m < M →
      IntervalIntegrable (fun t => F t * G t) volume (t₀ * 2 ^ m) (t₀ * 2 ^ (m + 1)))
    (hmom : ∀ m, m < M → (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t)
      ≤ K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :
    (∫ t in t₀..(t₀ * 2 ^ M), F t * G t)
      ≤ ∑ m ∈ Finset.range M, C m
          * ((K * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m + 2 * L) := by
  refine le_trans (integral_mul_kernel_le_sum_dyadic_var ht₀ hC hF hG hFint hFGint) ?_
  refine Finset.sum_le_sum fun m hm => ?_
  have hmM : m < M := Finset.mem_range.1 hm
  have hpos : (0 : ℝ) < t₀ * 2 ^ m := by positivity
  have hstep : (C m / (t₀ * 2 ^ m)) * (∫ t in (t₀ * 2 ^ m)..(t₀ * 2 ^ (m + 1)), F t)
      ≤ (C m / (t₀ * 2 ^ m))
          * (K * Real.sqrt (t₀ * 2 ^ (m + 1)) + L * (t₀ * 2 ^ (m + 1))) :=
    mul_le_mul_of_nonneg_left (hmom m hmM) (div_nonneg (hC m) hpos.le)
  refine le_trans hstep (le_of_eq ?_)
  have hsq := dyadic_sqrt_term_eq (C := C m) (K := K) ht₀ m
  have h2 : (C m / (t₀ * 2 ^ m)) * (L * (t₀ * 2 ^ (m + 1))) = C m * (2 * L) := by
    have hne : (t₀ * 2 ^ m) ≠ 0 := by positivity
    field_simp
    ring
  rw [mul_add, hsq, h2]
  ring

/-- **The vertical integral against a first-order kernel with a constant per block, from a mean
square.**  The mean square is charged as before; what varies with the height is only the kernel's
size. -/
theorem integral_norm_mul_kernel_le_of_affine_meanSquare_var {D : ℝ → ℂ} (hD : Continuous D)
    {G : ℝ → ℝ} (hGc : Continuous G) {C : ℕ → ℝ} {Q κ t₀ : ℝ} (hQ : 0 ≤ Q) (hκ : 0 ≤ κ)
    (hC : ∀ m, 0 ≤ C m) (ht₀ : 0 < t₀)
    (hms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ (2 : ℕ)) ≤ Q + κ * U) (M : ℕ)
    (hG : ∀ m, m < M → ∀ t, t₀ * 2 ^ m ≤ t → t ≤ t₀ * 2 ^ (m + 1) → G t ≤ C m / t) :
    (∫ t in t₀..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ ∑ m ∈ Finset.range M, C m
          * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
              + 2 * Real.sqrt κ) := by
  have hpow : ∀ m : ℕ, (0 : ℝ) < t₀ * 2 ^ m := fun m => by positivity
  have hge : ∀ m : ℕ, t₀ ≤ t₀ * 2 ^ m := by
    intro m
    have h1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith [ht₀.le]
  have hstep : ∀ m : ℕ, t₀ * 2 ^ m ≤ t₀ * 2 ^ (m + 1) := by
    intro m
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) ht₀.le
  refine integral_mul_kernel_le_of_affine_block_moment_var (F := fun t => ‖D t‖) ht₀ hC
    (fun t => norm_nonneg _) hG
    (fun m _ => (hD.norm.intervalIntegrable _ _))
    (fun m _ => ((hD.norm.mul hGc).intervalIntegrable _ _))
    (fun m _ => ?_)
  exact integral_norm_le_sqrt_affine hD hQ hκ (hms _ (hge (m + 1))) (hpow m).le (hstep m)
    (hpow (m + 1))

/-- **The vertical integral over a symmetric range, with a kernel constant per block.**  The kernel
bound is stated in `|t|`, so no evenness is needed: both flanks read it off the same block constant,
and the low range contributes the bounded-kernel term. -/
theorem integral_symm_norm_mul_kernel_var_le {D : ℝ → ℂ} (hD : Continuous D) {G : ℝ → ℝ}
    (hGc : Continuous G)
    {C : ℕ → ℝ} {C₀ Q κ t₀ : ℝ} (hC : ∀ m, 0 ≤ C m) (hC₀ : 0 ≤ C₀) (hQ : 0 ≤ Q) (hκ : 0 ≤ κ)
    (ht₀ : 0 < t₀) (hGlow : ∀ t, |t| ≤ t₀ → G t ≤ C₀)
    (hms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D t‖ ^ (2 : ℕ)) ≤ Q + κ * U) (M : ℕ)
    (hG : ∀ m, m < M → ∀ t : ℝ, t₀ * 2 ^ m ≤ |t| → |t| ≤ t₀ * 2 ^ (m + 1) → G t ≤ C m / |t|) :
    (∫ t in (-(t₀ * 2 ^ M))..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ 2 * (∑ m ∈ Finset.range M, C m
              * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
                  + 2 * Real.sqrt κ))
          + C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) := by
  have hone : (1 : ℝ) ≤ 2 ^ M := one_le_pow₀ (by norm_num)
  have hb : t₀ ≤ t₀ * 2 ^ M := by nlinarith [ht₀.le]
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t => ‖D t‖ * G t) volume u v :=
    fun u v => (hD.norm.mul hGc).intervalIntegrable _ _
  have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t => ‖D t‖ * G t) (μ := volume) (a := -(t₀ * 2 ^ M)) (b := -t₀) (c := t₀)
    (hint _ _) (hint _ _)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
    (f := fun t => ‖D t‖ * G t) (μ := volume) (a := -(t₀ * 2 ^ M)) (b := t₀)
    (c := t₀ * 2 ^ M) (hint _ _) (hint _ _)
  have hblockpos : ∀ m : ℕ, (0 : ℝ) < t₀ * 2 ^ m := fun m => by positivity
  have hGplus : ∀ m, m < M → ∀ t : ℝ, t₀ * 2 ^ m ≤ t → t ≤ t₀ * 2 ^ (m + 1) → G t ≤ C m / t := by
    intro m hm t ht htop
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (hblockpos m) ht
    have habs : |t| = t := abs_of_pos ht0
    have := hG m hm t (by rw [habs]; exact ht) (by rw [habs]; exact htop)
    rwa [habs] at this
  have hGminus : ∀ m, m < M → ∀ t : ℝ, t₀ * 2 ^ m ≤ t → t ≤ t₀ * 2 ^ (m + 1) →
      G (-t) ≤ C m / t := by
    intro m hm t ht htop
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le (hblockpos m) ht
    have habs : |(-t)| = t := by rw [abs_neg, abs_of_pos ht0]
    have := hG m hm (-t) (by rw [habs]; exact ht) (by rw [habs]; exact htop)
    rwa [habs] at this
  have hpos : (∫ t in t₀..(t₀ * 2 ^ M), ‖D t‖ * G t)
      ≤ ∑ m ∈ Finset.range M, C m
          * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
              + 2 * Real.sqrt κ) :=
    integral_norm_mul_kernel_le_of_affine_meanSquare_var hD hGc hQ hκ hC ht₀ hms M hGplus
  have hrefl : (∫ t in (-(t₀ * 2 ^ M))..(-t₀), ‖D t‖ * G t)
      = ∫ t in t₀..(t₀ * 2 ^ M), ‖D (-t)‖ * G (-t) := by
    rw [intervalIntegral.integral_comp_neg (fun t => ‖D t‖ * G t)]
  have hnegms : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖D (-t)‖ ^ (2 : ℕ)) ≤ Q + κ * U := by
    intro U hU
    rw [integral_Icc_normSq_comp_neg D (by linarith)]
    exact hms U hU
  have hneg : (∫ t in t₀..(t₀ * 2 ^ M), ‖D (-t)‖ * G (-t))
      ≤ ∑ m ∈ Finset.range M, C m
          * ((Real.sqrt Q * Real.sqrt 2 / Real.sqrt t₀) * (Real.sqrt 2 / 2) ^ m
              + 2 * Real.sqrt κ) :=
    integral_norm_mul_kernel_le_of_affine_meanSquare_var (hD.comp continuous_neg)
      (hGc.comp continuous_neg) hQ hκ hC ht₀ hnegms M hGminus
  have hlow : (∫ t in (-t₀)..t₀, ‖D t‖ * G t)
      ≤ C₀ * (Real.sqrt (2 * t₀) * Real.sqrt (Q + κ * t₀)) :=
    integral_norm_mul_kernel_low_le hD hGc hC₀ ht₀ hGlow (hms t₀ le_rfl)
  rw [hrefl] at hsplit1
  linarith [hsplit1, hsplit2]

end GaloisForLFunctions.HTGeometry
end
