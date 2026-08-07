import GaloisForLFunctions.RHTower.BurnolSoninDividedShift
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinNonvanishing
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Nonvanishing of the extended Sonine evaluation vector

Burnol's completed-Mellin Riesz vector `k_{w,a}` of the extended Sonine space is nonzero at every
point of the open right half of the critical strip, including at a zero of `ζ`.

Off the zero set the explicit co-Poisson inhabitant is already a witness.  On the zero set no
co-Poisson vector can be one, because every co-Poisson Mellin transform carries the factor `ζ(w)`.
The argument here is metric instead.  If `k_{w,a}` vanished, then every vector of `L_a` would have
vanishing Mellin value at `w`, so the head law of the forward divided shift would make `L_a`
invariant under that shift.  Iterating the shift multiplies the Mellin transform at a nearby point
`v` by `1/(w-v)` each time while multiplying the norm by at most `1/(Re w - 1/2)`.  Choosing `v`
strictly closer to `w` than the critical line is forces the Mellin value at `v` to vanish, which
contradicts the explicit inhabitant.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Iterated forward divided shift. -/
def burnolShiftIter (w : ℂ) (g : evenSubspace) : ℕ → evenSubspace
  | 0 => g
  | (n + 1) => burnolShift w (burnolShiftIter w g n)

@[simp] theorem burnolShiftIter_zero (w : ℂ) (g : evenSubspace) :
    burnolShiftIter w g 0 = g := rfl

@[simp] theorem burnolShiftIter_succ (w : ℂ) (g : evenSubspace) (n : ℕ) :
    burnolShiftIter w g (n + 1) = burnolShift w (burnolShiftIter w g n) := rfl

/-- **Zeros of `ζ` are isolated inside the critical strip.** -/
theorem eventually_riemannZeta_ne_zero_nhdsNE {w : ℂ} (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    ∀ᶠ z in 𝓝[≠] w, riemannZeta z ≠ 0 := by
  have hnot : ¬ ∀ᶠ z in 𝓝 w, xi z = 0 := by
    intro hev
    have hall := xi_analyticOnNhd_univ.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ w) hev (Set.mem_univ 0)
    have hzero : xi 0 = 0 := hall
    rw [xi] at hzero
    norm_num at hzero
  have hpunct : ∀ᶠ z in 𝓝[≠] w, xi z ≠ 0 :=
    (xi_analyticOnNhd_univ w (Set.mem_univ w)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hnot
  have h1 : ∀ᶠ z : ℂ in 𝓝 w, 0 < z.re :=
    (Complex.continuous_re.tendsto w).eventually (eventually_gt_nhds hw0)
  have h2 : ∀ᶠ z : ℂ in 𝓝 w, z.re < 1 :=
    (Complex.continuous_re.tendsto w).eventually (eventually_lt_nhds hw1)
  filter_upwards [hpunct, h1.filter_mono nhdsWithin_le_nhds,
    h2.filter_mono nhdsWithin_le_nhds] with z hz hz0 hz1
  intro hzeta
  refine hz ((xi_eq_zero_iff hz0 ?_).mpr hzeta)
  intro hone
  rw [hone] at hz1
  norm_num at hz1

/-- **Burnol's evaluation vector is nonzero at every point of the open right half strip.** -/
theorem burnolExtendedSoninEvaluationVector_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0 := by
  by_cases hz : riemannZeta w ≠ 0
  · exact burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero' hlo hhi hz ha ha1
  push_neg at hz
  intro hzero
  have hw0 : (0 : ℝ) < w.re := by linarith
  -- every extended Sonine vector is annihilated at `w`
  have hall := (burnolExtendedSoninEvaluationVector_eq_zero_iff hlo hhi ha).mp hzero
  have hvanish : ∀ g : evenSubspace, g ∈ soninExtendedSpace a →
      (∫ t in Ioi (0 : ℝ), ((g : SoninL2) : ℝ → ℂ) t * soninMellinKernel w t) = 0 := by
    intro g hg
    have h := hall ⟨g, hg⟩
    rw [soninMellinEvaluation] at h
    exact (mul_eq_zero.mp h).resolve_left (mellinCompletionFactor_ne_zero hw0)
  -- the explicit inhabitant and its iterates
  set g0 : evenSubspace :=
    ((coPoissonIndicatorSoninCosine ha ha1.le : soninExtendedSpace a) : evenSubspace) with hg0
  have hmem : ∀ n : ℕ, burnolShiftIter w g0 n ∈ soninExtendedSpace a := by
    intro n
    induction n with
    | zero => exact (coPoissonIndicatorSoninCosine ha ha1.le).property
    | succ n ih =>
        exact burnolShift_mem_soninExtendedSpace hlo hhi ha ih (hvanish _ ih)
  set M : ℝ := (w.re - 1 / 2)⁻¹ with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact inv_pos.mpr (by linarith)
  have hnorm : ∀ n : ℕ, ‖burnolShiftIter w g0 n‖ ≤ M ^ n * ‖g0‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hstep := norm_burnolShift_le hlo (burnolShiftIter w g0 n)
        rw [div_eq_inv_mul] at hstep
        calc ‖burnolShiftIter w g0 (n + 1)‖ ≤ M * ‖burnolShiftIter w g0 n‖ := by
              rw [burnolShiftIter_succ]
              exact hstep
          _ ≤ M * (M ^ n * ‖g0‖) := by
              exact mul_le_mul_of_nonneg_left ih hMpos.le
          _ = M ^ (n + 1) * ‖g0‖ := by ring
  -- choose the comparison point
  have hnbhd : ∀ᶠ z in 𝓝[≠] w, riemannZeta z ≠ 0 :=
    eventually_riemannZeta_ne_zero_nhdsNE hw0 hhi
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp hnbhd
  obtain ⟨ε, hε0, hεδ, hεM⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ ε < w.re - 1 / 2 := by
    refine ⟨min (δ / 2) ((w.re - 1 / 2) / 2), ?_, ?_, ?_⟩
    · exact lt_min (half_pos hδ) (half_pos (by linarith))
    · exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set v : ℂ := w - (ε : ℂ) with hv
  have hvre : v.re = w.re - ε := by
    rw [hv, Complex.sub_re, Complex.ofReal_re]
  have hvlo : 1 / 2 < v.re := by rw [hvre]; linarith
  have hvhi : v.re < 1 := by rw [hvre]; linarith
  have hvw : v.re < w.re := by rw [hvre]; linarith
  have hwv : w - v = (ε : ℂ) := by rw [hv]; ring
  have hzv : riemannZeta v ≠ 0 := by
    refine hδsub ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, hv]
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0] using hεδ
    · intro hcontra
      have : (ε : ℂ) = 0 := by
        have := hcontra
        rw [Set.mem_singleton_iff, hv] at this
        linear_combination -this
      have : ε = 0 := by exact_mod_cast this
      linarith
  -- Mellin transport along the iterates
  have hmell : ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), ((burnolShiftIter w g0 n : evenSubspace) : SoninL2) t *
          soninMellinKernel v t) =
        (∫ t in Ioi (0 : ℝ), ((g0 : SoninL2) : ℝ → ℂ) t * soninMellinKernel v t) /
          (ε : ℂ) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hcongr : (∫ t in Ioi (0 : ℝ),
              ((burnolShiftIter w g0 (n + 1) : evenSubspace) : SoninL2) t *
                soninMellinKernel v t) =
            ∫ t in Ioi (0 : ℝ),
              burnolShiftFun w (((burnolShiftIter w g0 n : evenSubspace) : SoninL2) : ℝ → ℂ) t *
                soninMellinKernel v t := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_of_ae
            (coe_burnolShift_ae hlo (burnolShiftIter w g0 n))] with t ht
          rw [burnolShiftIter_succ, ht]
        rw [hcongr, integral_burnolShiftFun_mellinKernel hlo hvlo hvhi hvw ha (hmem n), ih, hwv]
        rw [pow_succ]
        field_simp
  -- the metric contradiction
  set I0 : ℂ := ∫ t in Ioi (0 : ℝ), ((g0 : SoninL2) : ℝ → ℂ) t * soninMellinKernel v t with hI0
  set K : ℝ := ‖burnolExtendedSoninEvaluationVector v a hvlo hvhi ha‖ * ‖g0‖ with hK
  have hbound : ∀ n : ℕ, ‖mellinCompletionFactor v * I0‖ ≤ K * (M * ε) ^ n := by
    intro n
    have hinner := inner_burnolExtendedSoninEvaluationVector v a hvlo hvhi ha
      ⟨burnolShiftIter w g0 n, hmem n⟩
    have hcs := norm_inner_le_norm (𝕜 := ℂ)
      (burnolExtendedSoninEvaluationVector v a hvlo hvhi ha)
      (⟨burnolShiftIter w g0 n, hmem n⟩ : soninExtendedSpace a)
    rw [hinner] at hcs
    have hval : soninMellinEvaluation v
        (((⟨burnolShiftIter w g0 n, hmem n⟩ : soninExtendedSpace a) : evenSubspace) : SoninL2) =
          mellinCompletionFactor v * (I0 / (ε : ℂ) ^ n) := by
      rw [soninMellinEvaluation, hmell n, hI0]
    rw [hval] at hcs
    have hnormval : ‖mellinCompletionFactor v * (I0 / (ε : ℂ) ^ n)‖ =
        ‖mellinCompletionFactor v * I0‖ / ε ^ n := by
      rw [← mul_div_assoc, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hε0]
    rw [hnormval] at hcs
    have hn : ‖(⟨burnolShiftIter w g0 n, hmem n⟩ : soninExtendedSpace a)‖ =
        ‖burnolShiftIter w g0 n‖ := rfl
    rw [hn] at hcs
    have hεn : (0 : ℝ) < ε ^ n := pow_pos hε0 n
    rw [div_le_iff₀ hεn] at hcs
    calc ‖mellinCompletionFactor v * I0‖
        ≤ ‖burnolExtendedSoninEvaluationVector v a hvlo hvhi ha‖ *
            ‖burnolShiftIter w g0 n‖ * ε ^ n := hcs
      _ ≤ ‖burnolExtendedSoninEvaluationVector v a hvlo hvhi ha‖ * (M ^ n * ‖g0‖) * ε ^ n := by
          gcongr
          exact hnorm n
      _ = K * (M * ε) ^ n := by rw [hK, mul_pow]; ring
  have hMε : M * ε < 1 := by
    rw [hM, inv_mul_eq_div, div_lt_one (by linarith)]
    exact hεM
  have hMε0 : 0 ≤ M * ε := by positivity
  have hlim : Tendsto (fun n : ℕ => K * (M * ε) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hMε0 hMε).const_mul K
    simpa using this
  have hle : ‖mellinCompletionFactor v * I0‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have hzeroval : mellinCompletionFactor v * I0 = 0 := by
    have := norm_nonneg (mellinCompletionFactor v * I0)
    exact norm_eq_zero.mp (le_antisymm hle this)
  have hg0val : soninMellinEvaluation v
      (((coPoissonIndicatorSoninCosine ha ha1.le : soninExtendedSpace a) : evenSubspace) :
        SoninL2) = 0 := by
    rw [soninMellinEvaluation]
    exact hzeroval
  exact (soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff ha ha1
    (by linarith : (0 : ℝ) < v.re) hvhi).mpr hzv hg0val

/-- **Reformulation: the completed Mellin evaluation is a nonzero functional at every strip
point.** -/
theorem exists_soninExtendedSpace_mellin_ne_zero
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ f : soninExtendedSpace a,
      soninMellinEvaluation w (((f : soninExtendedSpace a) : evenSubspace) : SoninL2) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  exact burnolExtendedSoninEvaluationVector_ne_zero hlo hhi ha ha1
    ((burnolExtendedSoninEvaluationVector_eq_zero_iff hlo hhi ha).mpr hcon)

end RHTower
