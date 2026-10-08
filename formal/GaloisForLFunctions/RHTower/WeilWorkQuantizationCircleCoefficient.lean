import GaloisForLFunctions.RHTower.WeilWorkQuantizationLaurentInverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Circle coefficients and the positive-factor annihilator

Absolute convergence justifies circle integration term by term. An exterior
power series times a bilateral Laurent series has the expected coefficients.
If their product is z times a function analytic in the disc, every nonpositive
coefficient vanishes. This proves the complete infinite annihilator identity.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral

theorem quantization_hasSum_unitCircleIntegral {ι : Type*} [Countable ι]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {b : ι → ℝ}
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 1))
    (hbound : ∀ i, ∀ z ∈ sphere (0 : ℂ) 1, ‖F i z‖ ≤ b i)
    (hb : Summable b) (hlim : ∀ z ∈ sphere (0 : ℂ) 1, HasSum (fun i => F i z) (f z)) :
    HasSum (fun i => ∮ z in C(0, 1), F i z) (∮ z in C(0, 1), f z) := by
  have hd : Continuous (fun θ : ℝ => deriv (circleMap 0 1) θ) := by
    simpa only [deriv_circleMap, Pi.mul_apply] using!
      (continuous_circleMap 0 1).mul continuous_const
  have hFc (i : ι) : Continuous (fun θ : ℝ =>
      deriv (circleMap 0 1) θ • F i (circleMap 0 1 θ)) :=
    hd.smul ((hcont i).comp_continuous (continuous_circleMap 0 1)
      (circleMap_mem_sphere 0 (by norm_num)))
  have hFb (i : ι) (θ : ℝ) :
      ‖deriv (circleMap 0 1) θ • F i (circleMap 0 1 θ)‖ ≤ b i := by
    simpa only [norm_smul, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_one, mul_one, one_mul] using hbound i _ (circleMap_mem_sphere 0 (by norm_num) θ)
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2 * Real.pi) (fun i _ => b i)
    (fun i => (hFc i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall (fun θ _ => hFb i θ))
    (Filter.Eventually.of_forall (fun _ _ => hb)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun θ _ =>
      (hlim _ (circleMap_mem_sphere 0 (by norm_num) θ)).const_smul
        (deriv (circleMap 0 1) θ)))


def quantizationCircleCoeff (f : ℂ → ℂ) (k : ℤ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∮ z in C(0, 1), z ^ (-k - 1) * f z

private theorem unitSphere_norm {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : ‖z‖ = 1 := by
  simpa only [mem_sphere_iff_norm, sub_zero] using hz

private theorem unitSphere_ne_zero {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : z ≠ 0 := by
  intro he
  have hn := unitSphere_norm hz
  norm_num [he] at hn

private theorem unitSphere_zpow_cont (k : ℤ) :
    ContinuousOn (fun z : ℂ => z ^ k) (sphere 0 1) :=
  continuousOn_id.zpow₀ k (fun _ hz => Or.inl (unitSphere_ne_zero hz))

theorem hasSum_quantizationCircleCoeff {ι : Type*} [Countable ι]
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {b : ι → ℝ}
    (hcont : ∀ i, ContinuousOn (F i) (sphere 0 1))
    (hbound : ∀ i, ∀ z ∈ sphere (0 : ℂ) 1, ‖F i z‖ ≤ b i)
    (hb : Summable b) (hlim : ∀ z ∈ sphere (0 : ℂ) 1, HasSum (fun i => F i z) (f z))
    (k : ℤ) : HasSum (fun i => quantizationCircleCoeff (F i) k)
      (quantizationCircleCoeff f k) := by
  apply (quantization_hasSum_unitCircleIntegral
    (fun i => (unitSphere_zpow_cont (-k - 1)).mul (hcont i))
    (b := b) ?_ hb (fun z hz => (hlim z hz).mul_left (z ^ (-k - 1)))).mul_left
      ((2 * Real.pi * I)⁻¹)
  intro i z hz
  simpa only [Pi.mul_apply, norm_mul, norm_zpow, unitSphere_norm hz, one_zpow, one_mul] using hbound i z hz

theorem quantizationCircleCoeff_const_mul (f : ℂ → ℂ) (a : ℂ) (k : ℤ) :
    quantizationCircleCoeff (fun z => a * f z) k = a * quantizationCircleCoeff f k := by
  unfold quantizationCircleCoeff
  simp_rw [mul_left_comm _ a]
  have hi := circleIntegral.integral_smul a (fun z : ℂ => z ^ (-k - 1) * f z) 0 1
  simp only [smul_eq_mul] at hi
  rw [hi]
  ring

theorem quantizationCircleCoeff_zpow_mul (f : ℂ → ℂ) (m k : ℤ) :
    quantizationCircleCoeff (fun z => z ^ m * f z) k = quantizationCircleCoeff f (k - m) := by
  unfold quantizationCircleCoeff
  congr 1
  apply circleIntegral.integral_congr (by norm_num)
  intro z hz
  dsimp only
  rw [← mul_assoc, ← zpow_add₀ (unitSphere_ne_zero hz)]
  congr 2
  ring

theorem quantizationCircleCoeff_zpow (n k : ℤ) :
    quantizationCircleCoeff (fun z : ℂ => z ^ n) k = if n = k then 1 else 0 := by
  unfold quantizationCircleCoeff
  have he : (∮ z in C(0, 1), z ^ (-k - 1) * z ^ n) =
      ∮ z in C(0, 1), z ^ (n - k - 1) := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    dsimp only
    rw [← zpow_add₀ (unitSphere_ne_zero hz)]
    congr 1
    ring
  rw [he]
  by_cases hn : n = k
  · subst n
    simp only [sub_self, zero_sub, zpow_neg_one, if_true]
    have hi := circleIntegral.integral_sub_center_inv (0 : ℂ) (R := 1) (by norm_num)
    simp only [sub_zero] at hi
    rw [hi, inv_mul_cancel₀]
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  · rw [if_neg hn]
    have hn' : n - k - 1 ≠ -1 := by omega
    have hi := circleIntegral.integral_sub_zpow_of_ne hn' (0 : ℂ) 0 1
    simpa only [sub_zero, hi, mul_zero] using congrArg (fun w : ℂ => (2 * Real.pi * I)⁻¹ * w) hi

theorem quantizationCircleCoeff_laurent {p : ℤ → ℂ} (hp : Summable fun k => ‖p k‖)
    {P : ℂ → ℂ} (hP : ∀ z ∈ sphere (0 : ℂ) 1, P z = ∑' k : ℤ, p k * z ^ k)
    (k : ℤ) : quantizationCircleCoeff P k = p k := by
  have hs := hasSum_quantizationCircleCoeff (F := fun (n : ℤ) (z : ℂ) => p n * z ^ n)
    (f := P) (fun n : ℤ => continuousOn_const.mul (unitSphere_zpow_cont n))
    (b := fun n => ‖p n‖)
    (fun n z hz => by simp only [norm_mul, norm_zpow, unitSphere_norm hz, one_zpow, mul_one]; rfl)
    hp (fun z hz => ?_) k
  · rw [← hs.tsum_eq]
    simp only [quantizationCircleCoeff_const_mul, quantizationCircleCoeff_zpow, mul_ite,
      mul_one, mul_zero]
    simp
  · rw [hP z hz]
    apply Summable.hasSum
    apply Summable.of_norm
    simpa only [norm_mul, norm_zpow, unitSphere_norm hz, one_zpow, mul_one] using hp


theorem quantizationCircleCoeff_exterior_mul {γ : ℕ → ℂ}
    (hγ : Summable fun l => ‖γ l‖) {G P : ℂ → ℂ}
    (hP : ContinuousOn P (sphere 0 1))
    (hG : ∀ z ∈ sphere (0 : ℂ) 1,
      HasSum (fun l : ℕ => γ l * z ^ (-(l : ℤ))) (G z)) (k : ℤ) :
    quantizationCircleCoeff (fun z => G z * P z) k =
      ∑' l : ℕ, γ l * quantizationCircleCoeff P (k + l) := by
  obtain ⟨M, _, hbound⟩ := GaloisForLFunctions.HTGeometry.exists_bound_on_sphere
    (by norm_num : (0 : ℝ) ≤ 1) hP
  have hs := hasSum_quantizationCircleCoeff
    (F := fun (l : ℕ) (z : ℂ) => γ l * (z ^ (-(l : ℤ)) * P z))
    (f := fun z => G z * P z) (b := fun l => ‖γ l‖ * M)
    (fun l => continuousOn_const.mul ((unitSphere_zpow_cont (-(l : ℤ))).mul hP))
    (fun l z hz => ?_) (hγ.mul_right M) (fun z hz => ?_) k
  · rw [← hs.tsum_eq]
    apply tsum_congr
    intro l
    rw [quantizationCircleCoeff_const_mul, quantizationCircleCoeff_zpow_mul]
    simp only [sub_neg_eq_add]
  · simp only [norm_mul, norm_zpow, unitSphere_norm hz, one_zpow, one_mul]
    exact mul_le_mul_of_nonneg_left (hbound z hz) (norm_nonneg _)
  · simpa only [mul_assoc] using (hG z hz).mul_right (P z)

/-- A strictly positive analytic factor has no nonpositive circle coefficients. -/
theorem quantizationCircleCoeff_positive_factor {G P H : ℂ → ℂ}
    (hH : DiffContOnCl ℂ H (ball 0 1))
    (hfactor : ∀ z ∈ sphere (0 : ℂ) 1, G z * P z = z * H z) (j : ℕ) :
    quantizationCircleCoeff (fun z => G z * P z) (-(j : ℤ)) = 0 := by
  unfold quantizationCircleCoeff
  have he : (∮ z in C(0, 1), z ^ (-(-(j : ℤ)) - 1) * (G z * P z)) =
      ∮ z in C(0, 1), z ^ j * H z := by
    apply circleIntegral.integral_congr (by norm_num)
    intro z hz
    dsimp only
    rw [hfactor z hz, ← mul_assoc]
    have hp : z ^ (-(-(j : ℤ)) - 1) * z = z ^ j := by
      conv_lhs => arg 2; rw [← zpow_one z]
      rw [← zpow_add₀ (unitSphere_ne_zero hz)]
      simp only [neg_neg, sub_add_cancel, zpow_natCast]
    rw [hp]
  rw [he]
  have hi : (∮ z in C(0, 1), z ^ j * H z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      (by norm_num) countable_empty
      ((continuousOn_id.pow j).mul hH.continuousOn_ball)
      (fun z hz => (differentiableAt_id.pow j).mul (hH.differentiableAt isOpen_ball hz.1))
  rw [hi, mul_zero]

/-- Circle analyticity produces the coefficient annihilator, including every infinite sum. -/
theorem quantization_annihilator_of_positive_factor {p : ℤ → ℂ} {γ : ℕ → ℂ}
    (hp : Summable fun k => ‖p k‖) (hγ : Summable fun l => ‖γ l‖)
    {G P H : ℂ → ℂ}
    (hP : ∀ z ∈ sphere (0 : ℂ) 1, P z = ∑' k : ℤ, p k * z ^ k)
    (hG : ∀ z ∈ sphere (0 : ℂ) 1,
      HasSum (fun l : ℕ => γ l * z ^ (-(l : ℤ))) (G z))
    (hH : DiffContOnCl ℂ H (ball 0 1))
    (hfactor : ∀ z ∈ sphere (0 : ℂ) 1, G z * P z = z * H z) :
    ∀ j : ℕ, (∑' l : ℕ, γ l * p ((l : ℤ) - j)) = 0 := by
  have hPc : ContinuousOn P (sphere 0 1) := by
    apply (continuousOn_tsum
      (f := fun (k : ℤ) (z : ℂ) => p k * z ^ k)
      (fun k => continuousOn_const.mul (unitSphere_zpow_cont k)) hp ?_).congr hP
    intro k z hz
    simp only [norm_mul, norm_zpow, unitSphere_norm hz, one_zpow, mul_one, le_refl]
  intro j
  have he := quantizationCircleCoeff_exterior_mul hγ hPc hG (-(j : ℤ))
  rw [quantizationCircleCoeff_positive_factor hH hfactor] at he
  simp_rw [quantizationCircleCoeff_laurent hp hP] at he
  have hind (l : ℕ) : -(j : ℤ) + l = l - j := by ring
  simpa only [hind] using he.symm

end RHTower.WeilSpectral


