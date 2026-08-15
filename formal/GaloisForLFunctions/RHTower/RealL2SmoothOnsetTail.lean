import GaloisForLFunctions.RHTower.RealL2LipschitzWeakDerivative
import GaloisForLFunctions.HTGeometry.SmoothWeight
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Smooth whole-line activation of exponentially decaying tails

An exponentially decaying Lipschitz tail on the positive half-line becomes a whole-line `H¹`
function after multiplication by `Real.smoothTransition`.  This module proves global Lipschitz
regularity, square-integrability of both function and classical `deriv`, endpoint vanishing, and
the exact complex tempered-distribution weak-derivative identity.  Tail differentiability is not
assumed: the classical `deriv` convention and Lipschitz absolute continuity suffice.
-/

open Set MeasureTheory Filter Topology
open scoped ENNReal SchwartzMap LineDeriv

noncomputable section

namespace RHTower

/-- Smooth activation of a tail on the positive half-line. -/
def smoothOnsetTail (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.smoothTransition x * q x

private theorem exists_smoothTransition_lipschitz :
    ∃ B : NNReal, LipschitzWith B Real.smoothTransition := by
  obtain ⟨B, hB, hderiv⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_iteratedDeriv_smoothTransition 1
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (Real.smoothTransition.contDiff (n := (1 : ℕ∞))).differentiable (by norm_num)
  refine ⟨Real.toNNReal B, lipschitzWith_of_nnnorm_deriv_le hdiff fun x => ?_⟩
  change ‖deriv Real.smoothTransition x‖ ≤ (Real.toNNReal B : ℝ)
  rw [Real.coe_toNNReal B hB]
  simpa [iteratedDeriv_one, Real.norm_eq_abs] using hderiv x

theorem exists_smoothOnsetTail_lipschitz
    (q : ℝ → ℝ) {K : NNReal} (hqLip : LipschitzWith K q)
    {A : ℝ} (hA : 0 ≤ A) (hqBound : ∀ x, |q x| ≤ A) :
    ∃ Kp : NNReal, LipschitzWith Kp (smoothOnsetTail q) := by
  obtain ⟨B, hηLip⟩ := exists_smoothTransition_lipschitz
  let Kp : NNReal := K + Real.toNNReal A * B
  refine ⟨Kp, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  have hηx : |Real.smoothTransition x| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]
    exact Real.smoothTransition.le_one x
  have hqy : |q y| ≤ A := hqBound y
  have hq := hqLip.dist_le_mul x y
  have hη := hηLip.dist_le_mul x y
  have hsplit :
      |Real.smoothTransition x * q x - Real.smoothTransition y * q y| ≤
        |Real.smoothTransition x| * |q x - q y| +
          |q y| * |Real.smoothTransition x - Real.smoothTransition y| := by
    calc
      |Real.smoothTransition x * q x - Real.smoothTransition y * q y| =
          |Real.smoothTransition x * (q x - q y) +
            q y * (Real.smoothTransition x - Real.smoothTransition y)| := by ring_nf
      _ ≤ |Real.smoothTransition x * (q x - q y)| +
          |q y * (Real.smoothTransition x - Real.smoothTransition y)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
  change |smoothOnsetTail q x - smoothOnsetTail q y| ≤ (Kp : ℝ) * |x - y|
  change |q x - q y| ≤ (K : ℝ) * |x - y| at hq
  change |Real.smoothTransition x - Real.smoothTransition y| ≤ (B : ℝ) * |x - y| at hη
  rw [show (Kp : ℝ) = (K : ℝ) + A * (B : ℝ) by
    simp [Kp, Real.coe_toNNReal A hA]]
  calc
    |smoothOnsetTail q x - smoothOnsetTail q y| ≤
        |Real.smoothTransition x| * |q x - q y| +
          |q y| * |Real.smoothTransition x - Real.smoothTransition y| := hsplit
    _ ≤ 1 * ((K : ℝ) * |x - y|) + A * ((B : ℝ) * |x - y|) := by
      apply add_le_add
      · exact mul_le_mul hηx hq (abs_nonneg _) (by norm_num)
      · exact mul_le_mul hqy hη (abs_nonneg _) hA
    _ = ((K : ℝ) + A * (B : ℝ)) * |x - y| := by ring

theorem abs_smoothOnsetTail_le_exp {q : ℝ → ℝ} {A x : ℝ}
    (hx : 0 ≤ x) (hqTail : ∀ y, 0 ≤ y → |q y| ≤ A * Real.exp (-y)) :
    |smoothOnsetTail q x| ≤ A * Real.exp (-x) := by
  rw [smoothOnsetTail, abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg x)]
  have hη := Real.smoothTransition.le_one x
  have hq := hqTail x hx
  nlinarith [abs_nonneg (q x), Real.exp_pos (-x)]

theorem smoothOnsetTail_memLp
    (q : ℝ → ℝ) {K : NNReal} (hqLip : LipschitzWith K q)
    {A : ℝ} (hA : 0 ≤ A) (hqTail : ∀ x, 0 ≤ x → |q x| ≤ A * Real.exp (-x)) :
    MemLp (smoothOnsetTail q) 2 (volume : Measure ℝ) := by
  have hpcont : Continuous (smoothOnsetTail q) :=
    Real.smoothTransition.continuous.mul hqLip.continuous
  apply (memLp_two_iff_integrable_sq_norm hpcont.aestronglyMeasurable).2
  have hmajor : IntegrableOn (fun x : ℝ => A ^ 2 * Real.exp (-2 * x)) (Ioi 0) volume := by
    exact (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0).const_mul (A ^ 2)
  have hsqOn : IntegrableOn (fun x : ℝ => smoothOnsetTail q x ^ 2) (Ioi 0) volume := by
    apply Integrable.mono' hmajor ((hpcont.aestronglyMeasurable.pow 2).restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hp := abs_smoothOnsetTail_le_exp hx.le hqTail
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hexp : (A * Real.exp (-x)) ^ 2 = A ^ 2 * Real.exp (-2 * x) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [← hexp]
    change smoothOnsetTail q x ^ 2 ≤ (A * Real.exp (-x)) ^ 2
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (smoothOnsetTail q x))
        (mul_nonneg hA (Real.exp_pos (-x)).le)).2 hp
  have hsq : Integrable (fun x : ℝ => smoothOnsetTail q x ^ 2) volume :=
    hsqOn.integrable_of_forall_notMem_eq_zero fun x hx => by
      have hx0 : x ≤ 0 := le_of_not_gt hx
      rw [smoothOnsetTail, Real.smoothTransition.zero_of_nonpos hx0, zero_mul, zero_pow]
      norm_num
  simpa [Real.norm_eq_abs, sq_abs] using hsq

theorem smoothOnsetTail_deriv_memLp
    (q : ℝ → ℝ) {Kp : NNReal} (hpLip : LipschitzWith Kp (smoothOnsetTail q))
    {A : ℝ}
    (hqDerivTail : ∀ x, 1 < x → |deriv q x| ≤ A * Real.exp (-x)) :
    MemLp (deriv (smoothOnsetTail q)) 2 (volume : Measure ℝ) := by
  have hdmeas : AEStronglyMeasurable (fun x : ℝ => deriv (smoothOnsetTail q) x ^ 2) volume :=
    ((measurable_deriv _).pow_const 2).aestronglyMeasurable
  have hcompactMajor : IntegrableOn (fun _ : ℝ => (Kp : ℝ) ^ 2) (Icc 0 1) volume :=
    continuous_const.integrableOn_Icc
  have hcompact : IntegrableOn (fun x : ℝ => deriv (smoothOnsetTail q) x ^ 2)
      (Icc 0 1) volume := by
    apply Integrable.mono' hcompactMajor hdmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    have hd := norm_deriv_le_of_lipschitz (x₀ := x) hpLip
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    rw [Real.norm_eq_abs] at hd
    nlinarith [sq_abs (deriv (smoothOnsetTail q) x),
      abs_nonneg (deriv (smoothOnsetTail q) x), (show 0 ≤ (Kp : ℝ) by positivity)]
  have htailMajor : IntegrableOn (fun x : ℝ => A ^ 2 * Real.exp (-2 * x)) (Ioi 1) volume := by
    exact (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 1).const_mul (A ^ 2)
  have htail : IntegrableOn (fun x : ℝ => deriv (smoothOnsetTail q) x ^ 2)
      (Ioi 1) volume := by
    apply Integrable.mono' htailMajor hdmeas.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have heq : smoothOnsetTail q =ᶠ[𝓝 x] q := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      rw [smoothOnsetTail, Real.smoothTransition.one_of_one_le hy.le, one_mul]
    have hd := hqDerivTail x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), heq.deriv_eq]
    have hexp : (A * Real.exp (-x)) ^ 2 = A ^ 2 * Real.exp (-2 * x) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [← hexp]
    nlinarith [sq_abs (deriv q x),
      abs_nonneg (deriv q x)]
  have hsets : Icc (0 : ℝ) 1 ∪ Ioi 1 = Ici 0 := by
    ext x
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (hx | hx)
      · exact hx.1
      · linarith
    · intro hx
      by_cases hx1 : x ≤ 1
      · exact Or.inl ⟨hx, hx1⟩
      · exact Or.inr (lt_of_not_ge hx1)
  have hnonneg : IntegrableOn (fun x : ℝ => deriv (smoothOnsetTail q) x ^ 2)
      (Ici 0) volume := by
    rw [← hsets]
    exact hcompact.union htail
  have hsq : Integrable (fun x : ℝ => deriv (smoothOnsetTail q) x ^ 2) volume :=
    hnonneg.integrable_of_forall_notMem_eq_zero fun x hx => by
      have hx0 : x < 0 := lt_of_not_ge hx
      have heq : smoothOnsetTail q =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        rw [smoothOnsetTail, Real.smoothTransition.zero_of_nonpos hy.le, zero_mul]
      rw [heq.deriv_eq, deriv_const, zero_pow]
      norm_num
  apply (memLp_two_iff_integrable_sq_norm (measurable_deriv _).aestronglyMeasurable).2
  simpa [Real.norm_eq_abs, sq_abs] using hsq

theorem smoothOnsetTail_tendsto_atTop_zero
    {q : ℝ → ℝ} {A : ℝ}
    (hqTail : ∀ x, 0 ≤ x → |q x| ≤ A * Real.exp (-x)) :
    Tendsto (smoothOnsetTail q) atTop (nhds 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [eventually_ge_atTop 0] with x hx
    simpa [Real.norm_eq_abs] using abs_smoothOnsetTail_le_exp hx hqTail
  · simpa [mul_comm] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul A

theorem smoothOnsetTail_tendsto_atBot_zero (q : ℝ → ℝ) :
    Tendsto (smoothOnsetTail q) atBot (nhds 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_lt_atBot 0] with x hx
  rw [smoothOnsetTail, Real.smoothTransition.zero_of_nonpos hx.le, zero_mul]

/-- Exponentially decaying Lipschitz tails produce unconditional complex `L²` weak-derivative
pairs after smooth activation. -/
theorem smoothOnsetTail_weakDerivative
    (q : ℝ → ℝ) {K : NNReal} (hqLip : LipschitzWith K q)
    {A : ℝ} (hA : 0 ≤ A) (hqBound : ∀ x, |q x| ≤ A)
    (hqTail : ∀ x, 0 ≤ x → |q x| ≤ A * Real.exp (-x))
    (hqDerivTail : ∀ x, 1 < x → |deriv q x| ≤ A * Real.exp (-x)) :
    ∂_{(1 : ℝ)}
        (realToComplexL2 (smoothOnsetTail q)
          (smoothOnsetTail_memLp q hqLip hA hqTail) : 𝓢'(ℝ, ℂ)) =
      (realToComplexL2 (deriv (smoothOnsetTail q))
        (by
          obtain ⟨Kp, hpLip⟩ := exists_smoothOnsetTail_lipschitz q hqLip hA hqBound
          exact smoothOnsetTail_deriv_memLp q hpLip hqDerivTail) : 𝓢'(ℝ, ℂ)) := by
  obtain ⟨Kp, hpLip⟩ := exists_smoothOnsetTail_lipschitz q hqLip hA hqBound
  apply realToComplexL2_weakDerivative (C := Kp) (p := smoothOnsetTail q) hpLip
    (smoothOnsetTail_memLp q hqLip hA hqTail)
    (smoothOnsetTail_deriv_memLp q hpLip hqDerivTail)
    (smoothOnsetTail_tendsto_atTop_zero hqTail)
    (smoothOnsetTail_tendsto_atBot_zero q)

end RHTower

end
