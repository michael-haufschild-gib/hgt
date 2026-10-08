import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeCombinations
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticCoprimeEnergy

/-!
# Radial covariance of finite coprime masks

The square density retains the product-modulus cross terms. All limits are
right radial limits at one; no ordinary masked coefficient mean is asserted.
-/

open Complex Filter Finset
open scoped Topology
noncomputable section
namespace RHTower.WeilSingularArithmetic

theorem coprimePart_one_residue (Q : ℕ) [NeZero Q] :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (coprimePart Q 1) (s : ℂ)) (𝓝[>] 1) (𝓝 (coprimeDensity Q : ℂ)) := by
  have ht : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      DirichletCharacter.LFunctionTrivChar Q (s : ℂ)) (𝓝[>] 1)
      (𝓝 (coprimeDensity Q : ℂ)) := by
    simpa only [Function.comp_def, coprimeDensity, Complex.ofReal_prod,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using
      (DirichletCharacter.LFunctionTrivChar_residue_one (N := Q)).comp
        tendsto_ofReal_nhdsWithin_ne_one
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [LSeries_coprimePart_one Q (show 1 < (s : ℂ).re from hs)]

theorem constant_one_residue :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries 1 (s : ℂ))
      (𝓝[>] 1) (𝓝 (1 : ℂ)) := by
  have he : coprimePart 1 1 = (1 : ℕ → ℂ) := by
    funext n
    simp [coprimePart, coprimeMask]
  have ht := coprimePart_one_residue 1
  rw [he] at ht
  simpa [coprimeDensity] using ht

def coprimeAffineSquareDensity {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) : ℝ :=
  b ^ 2 + (∑ i ∈ S, (2 * b * c i) * coprimeDensity (Q i)) +
    ∑ i ∈ S, ∑ j ∈ S, (c i * c j) * coprimeDensity (Q i * Q j)

theorem coprimeAffineSquare_residue {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (hQ : ∀ i ∈ S, Q i ≠ 0) (c : ι → ℝ) (b : ℝ) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => ((coprimeAffineMask S Q c b n ^ 2 : ℝ) : ℂ)) (s : ℂ))
      (𝓝[>] 1) (𝓝 (coprimeAffineSquareDensity S Q c b : ℂ)) := by
  have hi := tendsto_finsetSum S fun i hi => by
    haveI : NeZero (Q i) := ⟨hQ i hi⟩
    exact (coprimePart_one_residue (Q i)).const_mul ((2 * b * c i : ℝ) : ℂ)
  have hij := tendsto_finsetSum S fun i hi => tendsto_finsetSum S fun j hj => by
    haveI : NeZero (Q i * Q j) := ⟨mul_ne_zero (hQ i hi) (hQ j hj)⟩
    exact (coprimePart_one_residue (Q i * Q j)).const_mul ((c i * c j : ℝ) : ℂ)
  have ht := ((constant_one_residue.const_mul ((b ^ 2 : ℝ) : ℂ)).add hi).add hij
  simp only [mul_one] at ht
  have he : (((b ^ 2 : ℝ) : ℂ) +
      (∑ i ∈ S, ((2 * b * c i : ℝ) : ℂ) * (coprimeDensity (Q i) : ℂ)) +
      ∑ i ∈ S, ∑ j ∈ S, ((c i * c j : ℝ) : ℂ) * (coprimeDensity (Q i * Q j) : ℂ)) =
      (coprimeAffineSquareDensity S Q c b : ℂ) := by
    simp only [coprimeAffineSquareDensity, Complex.ofReal_add, Complex.ofReal_sum,
      Complex.ofReal_mul]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [LSeries_coprimeAffineMask_sq S Q c b (show 1 < (s : ℂ).re from hs)]
  simp only [mul_add, Finset.mul_sum]
  ring_nf

private theorem affine_square_term_re {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {s : ℝ} (hs : 1 < s) (n : ℕ) :
    (LSeries.term (fun n => ((coprimeAffineMask S Q c b n ^ 2 : ℝ) : ℂ)) (s : ℂ) n).re =
      ‖(coprimeAffineMask S Q c b n : ℂ)‖ ^ 2 / (n : ℝ) ^ s := by
  by_cases hn : n = 0
  · simp [hn, LSeries.term, Real.zero_rpow (show s ≠ 0 by linarith)]
  rw [LSeries.term_of_ne_zero hn,
    show (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) by
      simpa only [Complex.ofReal_natCast] using
        (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm,
    ← Complex.ofReal_div, Complex.ofReal_re,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem summable_coprimeAffineMask_square {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖(coprimeAffineMask S Q c b n : ℂ)‖ ^ 2 / (n : ℝ) ^ s) := by
  have ht := Complex.hasSum_re
    (summable_coprimeAffineMask_sq S Q c b (show 1 < (s : ℂ).re from hs)).hasSum
  simpa only [affine_square_term_re S Q c b hs] using ht.summable

theorem coprimeAffineMask_square_residue {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (hQ : ∀ i ∈ S, Q i ≠ 0) (c : ι → ℝ) (b : ℝ) :
    Tendsto (fun s : ℝ => (s - 1) *
      ∑' n : ℕ, ‖(coprimeAffineMask S Q c b n : ℂ)‖ ^ 2 / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 (coprimeAffineSquareDensity S Q c b)) := by
  have ht := Complex.continuous_re.continuousAt.tendsto.comp
    (coprimeAffineSquare_residue S Q hQ c b)
  simp only [Complex.ofReal_re] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
    Complex.one_re, Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_self,
    zero_mul, sub_zero]
  congr 1
  rw [LSeries, Complex.re_tsum]
  · exact tsum_congr (affine_square_term_re S Q c b hs)
  · exact summable_coprimeAffineMask_sq S Q c b (show 1 < (s : ℂ).re from hs)

theorem coprimeAffineMask_residue {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) (b : ℝ) {f : ℕ → ℂ} {B : ℂ} {R : ι → ℂ}
    (hf : ∀ s : ℝ, 1 < s → LSeriesSummable f (s : ℂ))
    (hB : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries f (s : ℂ))
      (𝓝[>] 1) (𝓝 B))
    (hR : ∀ i ∈ S, Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (coprimePart (Q i) f) (s : ℂ)) (𝓝[>] 1) (𝓝 (R i))) :
    Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => f n * (coprimeAffineMask S Q c b n : ℂ)) (s : ℂ))
      (𝓝[>] 1) (𝓝 ((b : ℂ) * B + ∑ i ∈ S, (c i : ℂ) * R i)) := by
  have ht := (hB.const_mul (b : ℂ)).add
    (tendsto_finsetSum S fun i hi => (hR i hi).const_mul (c i : ℂ))
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [LSeries_coprimeAffineMask_mul S Q c b (hf s hs)]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Centering converts the affine second moment into its covariance form. -/
theorem coprimeAffineSquareDensity_centered {ι : Type*} (S : Finset ι) (Q : ι → ℕ)
    (c : ι → ℝ) :
    coprimeAffineSquareDensity S Q c (-(∑ i ∈ S, c i * coprimeDensity (Q i))) =
      ∑ i ∈ S, ∑ j ∈ S, c i * c j *
        (coprimeDensity (Q i * Q j) - coprimeDensity (Q i) * coprimeDensity (Q j)) := by
  let A := ∑ i ∈ S, c i * coprimeDensity (Q i)
  have hlin : (∑ i ∈ S, 2 * (-A) * c i * coprimeDensity (Q i)) = -2 * A ^ 2 := by
    calc
      _ = 2 * (-A) * ∑ i ∈ S, c i * coprimeDensity (Q i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by change 2 * (-A) * A = _; ring
  have hsq : (∑ i ∈ S, ∑ j ∈ S,
      c i * c j * (coprimeDensity (Q i) * coprimeDensity (Q j))) = A ^ 2 := by
    dsimp [A]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hsq]
  change (-A) ^ 2 + (∑ i ∈ S, 2 * (-A) * c i * coprimeDensity (Q i)) + _ = _
  rw [hlin]
  ring

end RHTower.WeilSingularArithmetic
