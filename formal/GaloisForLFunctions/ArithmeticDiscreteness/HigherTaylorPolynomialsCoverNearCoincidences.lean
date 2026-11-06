import GaloisForLFunctions.ArithmeticDiscreteness.PolynomialCriticalValuesControlSmallDerivatives
import GaloisForLFunctions.ArithmeticDiscreteness.ANearCoincidenceFlattensZeta
import GaloisForLFunctions.HTGeometry.TaylorFiniteOrderPositiveAxisBound

/-!+# Higher Taylor polynomials cover near coincidences

Polynomial critical values cover the values of a holomorphic function at close equal-value
pairs. Uniform Taylor remainders allow the covering radii to decay to arbitrary order.
-/

open Complex Metric Set Polynomial Filter

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- The Taylor polynomial at zero, including degree `k`. -/
def originTaylorPolynomial (f : ℂ → ℂ) (k : ℕ) : ℂ[X] :=
  ∑ j ∈ Finset.range (k + 1),
    monomial j (((j.factorial : ℂ))⁻¹ * iteratedDeriv j f 0)

theorem originTaylorPolynomial_natDegree_le (f : ℂ → ℂ) (k : ℕ) :
    (originTaylorPolynomial f k).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro j hj
  exact (natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hj))

theorem originTaylorPolynomial_eval (f : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (originTaylorPolynomial f k).eval z =
      ∑ j ∈ Finset.range (k + 1),
        (((j.factorial : ℂ))⁻¹ * iteratedDeriv j f 0) * z ^ j := by
  simp only [originTaylorPolynomial, eval_finsetSum, eval_monomial]

/-- Cauchy's coefficient estimate bounds the Taylor tail uniformly on a shrinking disc. -/
theorem originTaylorPolynomial_error_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 (1 / 2))) {M h : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ closedBall (0 : ℂ) (1 / 4), ‖f z‖ ≤ M)
    (hh0 : 0 < h) (hh : h ≤ 1 / 64) (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 4 * h) :
    ‖f z - (originTaylorPolynomial f k).eval z‖ ≤
      (2 * 16 ^ (k + 1)) * M * h ^ (k + 1) := by
  let a : ℕ → ℂ := fun j => ((j.factorial : ℂ))⁻¹ * iteratedDeriv j f 0
  have hcoef : ∀ j, ‖a j‖ ≤ M / (1 / 4 : ℝ) ^ j :=
    GaloisForLFunctions.HTGeometry.norm_taylorCoeff_le_of_sphere hf
      (by norm_num) (by norm_num) (fun w hw => hM w (sphere_subset_closedBall hw))
  let q : ℝ := 16 * h
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqhalf : q ≤ 1 / 2 := by dsimp [q]; linarith only [hh]
  have hq1 : q < 1 := by linarith only [hqhalf]
  have hzball : z ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball, dist_zero_right]
    linarith only [hz, hh]
  have hseries : HasSum (fun j => a j * z ^ j) (f z) := by
    have hs := Complex.hasSum_taylorSeries_on_ball hf hzball
    simp only [sub_zero, smul_eq_mul] at hs
    exact hs.congr_fun (fun j => by dsimp [a]; ring)
  have htail := (hasSum_nat_add_iff' (k + 1)).mpr hseries
  have hgeo : HasSum (fun n : ℕ => M * q ^ (k + 1) * q ^ n)
      (M * q ^ (k + 1) / (1 - q)) := by
    simpa only [div_eq_mul_inv] using
      (hasSum_geometric_of_lt_one hq0 hq1).mul_left (M * q ^ (k + 1))
  have hb : ∀ n : ℕ, ‖a (n + (k + 1)) * z ^ (n + (k + 1))‖ ≤
      M * q ^ (k + 1) * q ^ n := by
    intro n
    rw [norm_mul, norm_pow]
    calc
      ‖a (n + (k + 1))‖ * ‖z‖ ^ (n + (k + 1))
          ≤ (M / (1 / 4 : ℝ) ^ (n + (k + 1))) * (4 * h) ^ (n + (k + 1)) :=
        mul_le_mul (hcoef _) (pow_le_pow_left₀ (norm_nonneg _) hz _) (by positivity)
          (div_nonneg hM0 (by positivity))
      _ = M * ((4 * h) / (1 / 4)) ^ (n + (k + 1)) := by
        conv_rhs => rw [div_pow]
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = M * q ^ (k + 1) * q ^ n := by
        rw [show (4 * h) / (1 / 4) = q by dsimp [q]; ring, pow_add]
        ring
  have ht := htail.norm_le_of_bounded hgeo hb
  rw [originTaylorPolynomial_eval]
  change ‖f z - ∑ j ∈ Finset.range (k + 1), a j * z ^ j‖ ≤ _
  calc
    ‖f z - ∑ j ∈ Finset.range (k + 1), a j * z ^ j‖
        ≤ M * q ^ (k + 1) / (1 - q) := ht
    _ ≤ M * q ^ (k + 1) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [hqhalf])
    _ = (2 * 16 ^ (k + 1)) * M * h ^ (k + 1) := by
      dsimp [q]
      rw [mul_pow]
      ring

/-- A second Cauchy estimate controls the derivative of the same Taylor tail. -/
theorem originTaylorPolynomial_derivative_error_le {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 (1 / 2))) {M h : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ closedBall (0 : ℂ) (1 / 4), ‖f z‖ ≤ M)
    (hh0 : 0 < h) (hh : h ≤ 1 / 64) (k : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2 * h) :
    ‖deriv f z - (originTaylorPolynomial f k).derivative.eval z‖ ≤
      (2 * 16 ^ (k + 1)) * M * h ^ k := by
  let P := originTaylorPolynomial f k
  have hsub : closedBall z h ⊆ ball (0 : ℂ) (1 / 2) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
      calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith only [hw, hz, hn, hh]
  have hd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hh0
    ((hf.sub P.differentiable.differentiableOn).diffContOnCl_ball hsub)
    (C := (2 * 16 ^ (k + 1)) * M * h ^ (k + 1)) (fun w hw => by
      apply originTaylorPolynomial_error_le hf hM0 hM hh0 hh k
      have hw' : ‖w - z‖ = h := by simpa only [mem_sphere, dist_eq_norm] using hw
      have hn : ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith only [hw', hn, hz, hh0])
  have hzf : DifferentiableAt ℂ f z := hf.differentiableAt
    (isOpen_ball.mem_nhds (hsub (mem_closedBall_self hh0.le)))
  rw [deriv_sub hzf (P.hasDerivAt z).differentiableAt, (P.hasDerivAt z).deriv] at hd
  calc
    ‖deriv f z - P.derivative.eval z‖
        ≤ ((2 * 16 ^ (k + 1)) * M * h ^ (k + 1)) / h := hd
    _ = (2 * 16 ^ (k + 1)) * M * h ^ k := by
      rw [pow_succ h]
      field_simp

/-- The constant in the high-order cover of common values of nearby pairs. -/
def nearCoincidenceCoverConstant (k : ℕ) : ℝ :=
  2 * 16 ^ (k + 1) + 2 ^ (k + 1) * (128 + 2 * 16 ^ (k + 1))

theorem nearCoincidenceCoverConstant_pos (k : ℕ) : 0 < nearCoincidenceCoverConstant k := by
  unfold nearCoincidenceCoverConstant
  positivity

/-- A degree-`k` Taylor polynomial covers common values of pairs separated by at most `h^k`
using at most `k+1` discs of radius `C_k M h^(k+1)`. -/
theorem close_pair_value_near_taylorCriticalCentre {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 (1 / 2))) {M h : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), ‖f z‖ ≤ M)
    (hh0 : 0 < h) (hh : h ≤ 1 / 64) {k : ℕ} (hk : 1 ≤ k)
    {u v : ℂ} (hu : ‖u‖ ≤ 2 * h) (heq : f u = f v) (hne : u ≠ v)
    (hclose : ‖v - u‖ ≤ h ^ k) :
    ∃ a ∈ polynomialCriticalCentres (originTaylorPolynomial f k) 0,
      ‖f u - a‖ ≤ nearCoincidenceCoverConstant k * M * h ^ (k + 1) := by
  let P := originTaylorPolynomial f k
  have hh1 : h ≤ 1 := by linarith only [hh]
  have hpow : h ^ k ≤ h := by
    calc h ^ k ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 hk
      _ = h := pow_one _
  have hd0 : 0 < ‖v - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)
  have hsub : closedBall u (1 / 4) ⊆ ball (0 : ℂ) (1 / 2) := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_zero_right]
    have hn : ‖z‖ ≤ ‖z - u‖ + ‖u‖ := by
      calc ‖z‖ = ‖(z - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    linarith only [hn, hz, hu, hh]
  have ht := norm_sub_taylor_le isOpen_ball hf (by norm_num : (0 : ℝ) < 1 / 4)
    hsub (fun z hz => hM z (ball_subset_closedBall (hsub hz)))
    (show ‖v - u‖ ≤ (1 / 4) / 4 by linarith only [hclose, hpow, hh])
  rw [← heq, sub_self, zero_sub, norm_neg, norm_mul] at ht
  have hderiv : ‖deriv f u‖ ≤ 128 * M * h ^ k := by
    have ht' : ‖deriv f u‖ * ‖v - u‖ ≤ (128 * M * ‖v - u‖) * ‖v - u‖ := by
      convert ht using 1
      ring
    exact ((mul_le_mul_iff_left₀ hd0).mp ht').trans
      (mul_le_mul_of_nonneg_left hclose (by positivity))
  have hMsmall : ∀ z ∈ closedBall (0 : ℂ) (1 / 4), ‖f z‖ ≤ M :=
    fun z hz => hM z ((closedBall_subset_closedBall (by norm_num)) hz)
  have hde := originTaylorPolynomial_derivative_error_le hf hM0 hMsmall hh0 hh k hu
  have hPe : ‖P.derivative.eval u‖ ≤ (128 + 2 * 16 ^ (k + 1)) * M * h ^ k := by
    calc
      ‖P.derivative.eval u‖ ≤ ‖deriv f u‖ + ‖deriv f u - P.derivative.eval u‖ := by
        have ht := norm_sub_le (deriv f u) (deriv f u - P.derivative.eval u)
        simpa only [sub_sub_cancel] using ht
      _ ≤ 128 * M * h ^ k + (2 * 16 ^ (k + 1)) * M * h ^ k := add_le_add hderiv hde
      _ = _ := by ring
  obtain ⟨a, ha, hPa⟩ := exists_polynomialCriticalCentre_near P 0 u
    (by simpa only [sub_zero] using hu) hPe
  have hdeg : (2 : ℝ) ^ P.natDegree ≤ 2 ^ k :=
    pow_le_pow_right₀ (by norm_num) (originTaylorPolynomial_natDegree_le f k)
  have hval := originTaylorPolynomial_error_le hf hM0 hMsmall hh0 hh k
    (show ‖u‖ ≤ 4 * h by linarith only [hu, hh0])
  refine ⟨a, ha, ?_⟩
  calc
    ‖f u - a‖ ≤ ‖f u - P.eval u‖ + ‖P.eval u - a‖ := by
      calc ‖f u - a‖ = ‖(f u - P.eval u) + (P.eval u - a)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    _ ≤ (2 * 16 ^ (k + 1)) * M * h ^ (k + 1) +
        2 ^ k * (2 * h) * ((128 + 2 * 16 ^ (k + 1)) * M * h ^ k) := by
      apply add_le_add hval
      refine hPa.trans ?_
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hdeg (by positivity)) (by positivity)
    _ = nearCoincidenceCoverConstant k * M * h ^ (k + 1) := by
      unfold nearCoincidenceCoverConstant
      simp only [pow_succ]
      ring

end GaloisForLFunctions.ArithmeticDiscreteness
