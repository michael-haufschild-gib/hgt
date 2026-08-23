import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw

open NormedSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

/-- Left-trivialized Duhamel response of an autonomous endpoint. -/
def duhamelConjugationPrimitive (x p : A) (t : ℝ) : A :=
  ∫ s : ℝ in 0..t, exp (s • (-x)) * p * exp (s • x)

theorem continuous_duhamelConjugationIntegrand (x p : A) :
    Continuous (fun s : ℝ => exp (s • (-x)) * p * exp (s • x)) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  fun_prop

theorem norm_exp_conjugation_eq
    (x p : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    ‖exp (s • (-x)) * p * exp (s • x)‖ = ‖p‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hleft : exp (s • (-x)) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint
      (by simpa [smul_neg, neg_smul] using skewAdjoint.smul_mem (-s) hx)
  have hright : exp (s • x) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx)
  rw [mul_assoc, CStarRing.norm_mem_unitary_mul _ hleft,
    CStarRing.norm_mul_mem_unitary _ hright]

theorem norm_exp_conjugation_sub_self_le
    (x p : A) (hx : x ∈ skewAdjoint A) (s : ℝ) :
    ‖exp (s • (-x)) * p * exp (s • x) - p‖ ≤
      2 * |s| * ‖x‖ * ‖p‖ := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hneg : -x ∈ skewAdjoint A := (skewAdjoint A).neg_mem hx
  have hzero : (0 : A) ∈ skewAdjoint A := (skewAdjoint A).zero_mem
  have hleft := exp_skewAdjoint_sub_exp_skewAdjoint_norm_le (-x) 0 hneg hzero s
  have hright := exp_skewAdjoint_sub_exp_skewAdjoint_norm_le x 0 hx hzero s
  have hunit : exp (s • x) ∈ unitary A :=
    exp_mem_unitary_of_mem_skewAdjoint (skewAdjoint.smul_mem s hx)
  have hunitNorm : ‖exp (s • x)‖ = 1 := CStarRing.norm_of_mem_unitary hunit
  have hleft' : ‖exp (s • (-x)) - 1‖ ≤ |s| * ‖x‖ := by
    simpa using hleft
  have hright' : ‖exp (s • x) - 1‖ ≤ |s| * ‖x‖ := by
    simpa using hright
  have hsplit :
      exp (s • (-x)) * p * exp (s • x) - p =
        (exp (s • (-x)) - 1) * p * exp (s • x) +
          p * (exp (s • x) - 1) := by
    noncomm_ring
  rw [hsplit]
  have hfirst :
      ‖(exp (s • (-x)) - 1) * p * exp (s • x)‖ ≤
        (|s| * ‖x‖) * ‖p‖ * 1 := by
    calc
      ‖(exp (s • (-x)) - 1) * p * exp (s • x)‖ ≤
          ‖exp (s • (-x)) - 1‖ * ‖p‖ * ‖exp (s • x)‖ := by
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (|s| * ‖x‖) * ‖p‖ * 1 := by gcongr
  have hsecond :
      ‖p * (exp (s • x) - 1)‖ ≤ ‖p‖ * (|s| * ‖x‖) := by
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hright' (norm_nonneg _))
  calc
    ‖(exp (s • (-x)) - 1) * p * exp (s • x) +
        p * (exp (s • x) - 1)‖ ≤
        ‖(exp (s • (-x)) - 1) * p * exp (s • x)‖ +
          ‖p * (exp (s • x) - 1)‖ := norm_add_le _ _
    _ ≤ (|s| * ‖x‖) * ‖p‖ * 1 + ‖p‖ * (|s| * ‖x‖) :=
      add_le_add hfirst hsecond
    _ = 2 * |s| * ‖x‖ * ‖p‖ := by ring

theorem norm_duhamelConjugationPrimitive_sub_smul_le
    (x p : A) (hx : x ∈ skewAdjoint A) {δ : ℝ} (hδ : 0 ≤ δ) :
    ‖duhamelConjugationPrimitive x p δ - δ • p‖ ≤
      2 * δ ^ 2 * ‖x‖ * ‖p‖ := by
  let f : ℝ → A := fun s => exp (s • (-x)) * p * exp (s • x)
  have hf : Continuous f := continuous_duhamelConjugationIntegrand x p
  have hsub :
      duhamelConjugationPrimitive x p δ - δ • p =
        ∫ s : ℝ in 0..δ, (f s - p) := by
    unfold duhamelConjugationPrimitive
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
      intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
  rw [hsub]
  calc
    ‖∫ s : ℝ in 0..δ, (f s - p)‖ ≤
        (2 * δ * ‖x‖ * ‖p‖) * |δ - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
        have hs' : s ∈ Set.Ioc (0 : ℝ) δ := by
          simpa [Set.uIoc_of_le hδ] using hs
        have hs0 : 0 ≤ s := hs'.1.le
        have hsδ : s ≤ δ := hs'.2
        have hpoint := norm_exp_conjugation_sub_self_le x p hx s
        rw [abs_of_nonneg hs0] at hpoint
        exact hpoint.trans (by gcongr))
    _ = 2 * δ ^ 2 * ‖x‖ * ‖p‖ := by
      rw [sub_zero, abs_of_nonneg hδ]
      ring

theorem duhamelConjugationPrimitive_shortTime_lower
    (x p : A) (hx : x ∈ skewAdjoint A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * ‖x‖ ≤ 1) :
    δ / 2 * ‖p‖ ≤ ‖duhamelConjugationPrimitive x p δ‖ := by
  have herr := norm_duhamelConjugationPrimitive_sub_smul_le x p hx hδ
  have hδp : ‖δ • p‖ = δ * ‖p‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hδ]
  have htri : ‖δ • p‖ ≤
      ‖duhamelConjugationPrimitive x p δ - δ • p‖ +
        ‖duhamelConjugationPrimitive x p δ‖ := by
    calc
      ‖δ • p‖ = ‖duhamelConjugationPrimitive x p δ -
          (duhamelConjugationPrimitive x p δ - δ • p)‖ := by
        congr 1
        abel
      _ ≤ ‖duhamelConjugationPrimitive x p δ‖ +
          ‖duhamelConjugationPrimitive x p δ - δ • p‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  rw [hδp] at htri
  have herror :
      2 * δ ^ 2 * ‖x‖ * ‖p‖ ≤ δ / 2 * ‖p‖ := by
    have hmul :
        (4 * δ * ‖x‖) * (δ * ‖p‖ / 2) ≤
          1 * (δ * ‖p‖ / 2) :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    calc
      2 * δ ^ 2 * ‖x‖ * ‖p‖ =
          (4 * δ * ‖x‖) * (δ * ‖p‖ / 2) := by ring
      _ ≤ 1 * (δ * ‖p‖ / 2) := hmul
      _ = δ / 2 * ‖p‖ := by ring
  linarith

theorem duhamelConjugationIntegrand_add
    (x p : A) (s t : ℝ) :
    exp ((s + t) • (-x)) * p * exp ((s + t) • x) =
      exp (t • (-x)) *
        (exp (s • (-x)) * p * exp (s • x)) * exp (t • x) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hnegComm : Commute (t • (-x)) (s • (-x)) := by
    exact (Commute.refl x).neg_left.neg_right.smul_left t |>.smul_right s
  have hposComm : Commute (s • x) (t • x) := by
    exact (Commute.refl x).smul_left s |>.smul_right t
  have hneg : exp ((s + t) • (-x)) =
      exp (t • (-x)) * exp (s • (-x)) := by
    rw [add_comm s t, add_smul, NormedSpace.exp_add_of_commute hnegComm]
  have hpos : exp ((s + t) • x) = exp (s • x) * exp (t • x) := by
    rw [add_smul, NormedSpace.exp_add_of_commute hposComm]
  rw [hneg, hpos]
  noncomm_ring

/-- Exact cocycle law: every two-time Duhamel difference is a unitary
conjugate of one short-time response. -/
theorem duhamelConjugationPrimitive_add_sub
    (x p : A) (t δ : ℝ) :
    duhamelConjugationPrimitive x p (t + δ) -
        duhamelConjugationPrimitive x p t =
      exp (t • (-x)) * duhamelConjugationPrimitive x p δ * exp (t • x) := by
  let _ : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  let f : ℝ → A := fun s => exp (s • (-x)) * p * exp (s • x)
  have hf : Continuous f := continuous_duhamelConjugationIntegrand x p
  have htail :
      (∫ s : ℝ in t..t + δ, f s) =
        ∫ s : ℝ in 0..δ, f (s + t) := by
    rw [intervalIntegral.integral_comp_add_right]
    simp only [zero_add, add_comm δ t]
  have hsplit :
      (∫ s : ℝ in 0..t, f s) + (∫ s : ℝ in t..t + δ, f s) =
        ∫ s : ℝ in 0..t + δ, f s :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  let L : A →L[ℝ] A :=
    (ContinuousLinearMap.mul ℝ A (exp (t • (-x)))).comp
      ((ContinuousLinearMap.mul ℝ A).flip (exp (t • x)))
  have hpull :
      (∫ s : ℝ in 0..δ,
          exp (t • (-x)) * f s * exp (t • x)) =
        exp (t • (-x)) * (∫ s : ℝ in 0..δ, f s) * exp (t • x) := by
    change (∫ s : ℝ in 0..δ, L (f s)) = L (∫ s : ℝ in 0..δ, f s)
    exact L.intervalIntegral_comp_comm (hf.intervalIntegrable _ _)
  unfold duhamelConjugationPrimitive
  change (∫ s : ℝ in 0..t + δ, f s) - (∫ s : ℝ in 0..t, f s) = _
  rw [← hsplit, add_sub_cancel_left, htail]
  calc
    (∫ s : ℝ in 0..δ, f (s + t)) =
        ∫ s : ℝ in 0..δ,
          exp (t • (-x)) * f s * exp (t • x) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact duhamelConjugationIntegrand_add x p s t
    _ = _ := hpull

theorem norm_sub_sq_le_two_mul_sum_sq (u v : A) :
    ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h := norm_sub_le u v
  have hsq : ‖u - v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 h
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- **Resonance-free two-time observer coercivity.** At every base time,
two endpoints separated by one sufficiently short step retain a uniform
Jacobian energy floor. The bound is independent of spectrum, spectral gaps,
and base time. -/
theorem duhamelConjugationPrimitive_twoTime_energy_lower
    (x p : A) (hx : x ∈ skewAdjoint A) (t : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 4 * δ * ‖x‖ ≤ 1) :
    δ ^ 2 / 8 * ‖p‖ ^ 2 ≤
      ‖duhamelConjugationPrimitive x p t‖ ^ 2 +
        ‖duhamelConjugationPrimitive x p (t + δ)‖ ^ 2 := by
  have hshort := duhamelConjugationPrimitive_shortTime_lower x p hx hδ hsmall
  have hinc := duhamelConjugationPrimitive_add_sub x p t δ
  have hnormInc :
      ‖duhamelConjugationPrimitive x p (t + δ) -
          duhamelConjugationPrimitive x p t‖ =
        ‖duhamelConjugationPrimitive x p δ‖ := by
    rw [hinc]
    exact norm_exp_conjugation_eq x
      (duhamelConjugationPrimitive x p δ) hx t
  have hdiffLower :
      δ / 2 * ‖p‖ ≤
        ‖duhamelConjugationPrimitive x p (t + δ) -
          duhamelConjugationPrimitive x p t‖ := by
    rw [hnormInc]
    exact hshort
  have hdiffSq :
      (δ / 2 * ‖p‖) ^ 2 ≤
        ‖duhamelConjugationPrimitive x p (t + δ) -
          duhamelConjugationPrimitive x p t‖ ^ 2 := by
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hdiffLower
  have hupper := norm_sub_sq_le_two_mul_sum_sq
    (duhamelConjugationPrimitive x p (t + δ))
    (duhamelConjugationPrimitive x p t)
  nlinarith

end

end GaloisForLFunctions.HTGeometry

