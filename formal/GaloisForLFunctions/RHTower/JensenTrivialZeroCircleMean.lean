import GaloisForLFunctions.RHTower.JensenTrivialZeroProducts
import GaloisForLFunctions.RHTower.BVCoPoissonHalfWeightResonance

/-!
# The explicit trivial-zero contribution bounds the actual circular mean

Apply the finite-radius Jensen mechanism of arXiv:2610.10584 to the
corpus's entire zeta function. The radius chosen at each index lies strictly
beyond the first `N` trivial zeros. Their complete telescoping product is
therefore an unconditional lower bound for the circular logarithmic mean.
-/

noncomputable section
open scoped BigOperators
open Complex Metric

namespace RHTower

theorem jensenTrivialRadius_strictMono : StrictMono jensenTrivialRadius := by
  intro n m hnm
  unfold jensenTrivialRadius
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  have h : (n : ℝ) < m := by exact_mod_cast hnm
  nlinarith

/-- A canonical interior circle enclosing the first `N` trivial zeros. -/
def jensenTrivialCircleRadius (N : ℕ) : ℝ := (1 + jensenTrivialRadius N) / 2

theorem jensenTrivialCircleRadius_pos (N : ℕ) : 0 < jensenTrivialCircleRadius N := by
  unfold jensenTrivialCircleRadius
  linarith [jensenTrivialRadius_pos N]

theorem jensenTrivialCircleRadius_lt_one (N : ℕ) : jensenTrivialCircleRadius N < 1 := by
  unfold jensenTrivialCircleRadius
  linarith [jensenTrivialRadius_lt_one N]

theorem jensenLeftZeta_center_ne_zero : jensenLeftZeta 1 0 ≠ 0 := by
  have harg : jensenLeftChart 1 0 = -(1 / 2 : ℂ) := by
    norm_num [jensenLeftChart]
  rw [jensenLeftZeta, harg, zetaEntire_eq (by norm_num)]
  apply mul_ne_zero (by norm_num)
  simpa using riemannZeta_neg_half_sub_two_nat_ne_zero 0

/-- The pulled-back entire function is analytic on each canonical closed disk. -/
theorem analyticOnNhd_jensenLeftZeta_trivialCircle (N : ℕ) :
    AnalyticOnNhd ℂ (jensenLeftZeta 1) (closedBall 0 (jensenTrivialCircleRadius N)) := by
  have hd : DifferentiableOn ℂ (jensenLeftZeta 1) ({1}ᶜ : Set ℂ) := by
    intro z hz
    have hz' : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    apply (differentiable_zetaEntire _).comp_differentiableWithinAt z
    unfold jensenLeftChart
    fun_prop
  intro z hz
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h := (mem_closedBall.mp hz)
    simp only [dist_zero_right, norm_one] at h
    linarith [jensenTrivialCircleRadius_lt_one N]
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz1)

/-- The exact trivial-zero product is a lower bound for the genuine Jensen
mean, with every analytic and zero-location input discharged. -/
theorem jensenLeftZeta_trivial_circleMean_lower (N : ℕ) :
    Real.log ‖jensenLeftZeta 1 0‖ +
      N * Real.log (jensenTrivialCircleRadius N) + Real.log ((4 * N + 3 : ℝ) / 3) ≤
        Real.circleAverage (fun z => Real.log ‖jensenLeftZeta 1 z‖) 0
          (jensenTrivialCircleRadius N) := by
  classical
  let f : ℕ → ℂ := fun n => jensenTrivialRadius n
  have hf : Function.Injective f := by
    intro i j hij
    apply jensenTrivialRadius_strictMono.injective
    exact Complex.ofReal_injective hij
  have hzero : ∀ z ∈ (Finset.range N).image f, jensenLeftZeta 1 z = 0 := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact jensenLeftZeta_trivial i
  have hinside : ∀ z ∈ (Finset.range N).image f, ‖z‖ < jensenTrivialCircleRadius N := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
    have hiN := jensenTrivialRadius_strictMono (Finset.mem_range.mp hi)
    change ‖(jensenTrivialRadius i : ℂ)‖ < _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jensenTrivialRadius_pos i)]
    unfold jensenTrivialCircleRadius
    linarith [jensenTrivialRadius_lt_one N]
  have hj := sum_log_div_norm_add_log_le_circleAverage
    (jensenTrivialCircleRadius_pos N) (analyticOnNhd_jensenLeftZeta_trivialCircle N)
    jensenLeftZeta_center_ne_zero hzero hinside
  rw [Finset.sum_image (fun i _ j _ hij => hf hij)] at hj
  have hs : (∑ i ∈ Finset.range N,
      Real.log (jensenTrivialCircleRadius N / ‖f i‖)) =
        N * Real.log (jensenTrivialCircleRadius N) + Real.log ((4 * N + 3 : ℝ) / 3) := by
    simp only [f, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (jensenTrivialRadius_pos _)]
    rw [← Real.log_prod (fun i _ =>
      (div_pos (jensenTrivialCircleRadius_pos N) (jensenTrivialRadius_pos i)).ne'),
      prod_div_jensenTrivialRadius,
      Real.log_mul (pow_pos (jensenTrivialCircleRadius_pos N) N).ne' (by positivity),
      Real.log_pow]
  rw [hs] at hj
  linarith

end RHTower
