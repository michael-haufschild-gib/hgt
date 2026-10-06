import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeSampling
import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeAveraging

/-!
# Displacement of the actual hyperbolic prime average

Exact dilation of the half-open dual windows retains the complete sampled
kernel. A constant weight of mass one pays the normalization error.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Set
namespace RHTower

private theorem hyperbolic_kernel_zero_off_band (N : ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∉ Set.Ioc N (2 * N)) : chiCubicHyperbolicPrimeKernel N M x = 0 := by
  classical
  unfold chiCubicHyperbolicPrimeKernel
  apply Finset.sum_eq_zero
  intro pr _
  have hsup : x ∉ chiCubicHyperbolicPrimeSupport N M pr := fun h => hx h.1
  simp only [Set.indicator_apply, if_neg hsup]

private theorem hyperbolic_kernel_zero_off_closed_band (N : ℝ) (M : ℕ) {x : ℝ}
    (hx : x ∉ Set.Icc N (2 * N)) : chiCubicHyperbolicPrimeKernel N M x = 0 :=
  hyperbolic_kernel_zero_off_band N M (fun h => hx ⟨h.1.le, h.2⟩)

private theorem hyperbolic_kernel_integrable {N : ℝ} (hN : 1 < N) (M : ℕ) :
    Integrable (chiCubicHyperbolicPrimeKernel N M) volume := by
  classical
  have heq : (Set.Icc N (2 * N)).indicator (chiCubicHyperbolicPrimeKernel N M) =
      chiCubicHyperbolicPrimeKernel N M := by
    funext x
    by_cases hx : x ∈ Set.Icc N (2 * N)
    · exact Set.indicator_of_mem hx _
    · simp only [Set.indicator_apply, if_neg hx,
        hyperbolic_kernel_zero_off_closed_band N M hx]
  rw [← heq]
  exact (integrable_indicator_iff measurableSet_Icc).2
    (integrableOn_chiCubicHyperbolicPrimeKernel hN M)

private theorem sum_Ioc_zero_eq_range (f : ℕ → ℂ) (B : ℕ) :
    (∑ n ∈ Finset.Ioc 0 B, f n) = ∑ i ∈ Finset.range B, f (i + 1) := by
  classical
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    exact Finset.mem_Ioc.2 ⟨by omega, by have := Finset.mem_range.1 hi; omega⟩
  · intro i _ j _ hij
    omega
  · intro n hn
    have h := Finset.mem_Ioc.1 hn
    exact ⟨n - 1, Finset.mem_range.2 (by omega), by omega⟩
  · intro i _
    rfl

/-- Literal finite von Mangoldt trace on every dilated integer in the dual cutoff. -/
def chiCubicHyperbolicPrimeTrace (N : ℝ) (M : ℕ) (t : ℝ) : ℂ :=
  ∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
    chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ))

/-- At unit dilation the zero-extended trace is exactly the original discrete sum. -/
theorem chiCubicHyperbolicPrimeTrace_one {N : ℝ} (hN : 0 ≤ N) (M : ℕ) :
    chiCubicHyperbolicPrimeTrace N M 1 = chiCubicHyperbolicVonMangoldtSum N M := by
  classical
  have hsub : Finset.Ioc ⌊N⌋₊ ⌊2 * N⌋₊ ⊆ Finset.Ioc 0 ⌊3 * N⌋₊ := by
    intro n hn
    obtain ⟨hn0, hnB⟩ := Finset.mem_Ioc.1 hn
    refine Finset.mem_Ioc.2 ⟨by omega, hnB.trans ?_⟩
    apply Nat.le_floor
    exact (Nat.floor_le (show 0 ≤ 2 * N by positivity)).trans (by linarith)
  have heq : chiCubicHyperbolicVonMangoldtSum N M =
      ∑ n ∈ Finset.Ioc 0 ⌊3 * N⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℂ) * chiCubicHyperbolicPrimeKernel N M n := by
    unfold chiCubicHyperbolicVonMangoldtSum
    apply Finset.sum_subset hsub
    intro n _ hn
    have hzero : chiCubicHyperbolicPrimeKernel N M n = 0 := by
      apply hyperbolic_kernel_zero_off_band
      intro hx
      exact hn (Finset.mem_Ioc.2 ⟨(Nat.floor_lt hN).2 hx.1, Nat.le_floor hx.2⟩)
    rw [hzero, mul_zero]
  rw [heq, sum_Ioc_zero_eq_range]
  simp only [chiCubicHyperbolicPrimeTrace, one_mul]

private theorem norm_hyperbolic_trace_le {N : ℝ} (hN : 4 ≤ N)
    (hlog : 1 ≤ Real.log N) (M : ℕ) (t : ℝ) :
    ‖chiCubicHyperbolicPrimeTrace N M t‖ ≤
      (64 * Real.pi * ((M : ℝ) + 1)) * (3 * N * Real.log (3 * N)) := by
  classical
  have hN0 : 0 < N := by linarith
  have hK (x : ℝ) : ‖chiCubicHyperbolicPrimeKernel N M x‖ ≤
      64 * Real.pi * ((M : ℝ) + 1) := by
    by_cases hx : x ∈ Set.Icc N (2 * N)
    · exact norm_chiCubicHyperbolicPrimeKernel_le hN hlog M hx
    · rw [hyperbolic_kernel_zero_off_closed_band N M hx, norm_zero]
      positivity
  have hlog3 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  unfold chiCubicHyperbolicPrimeTrace
  calc
    _ ≤ ∑ _i ∈ Finset.range ⌊3 * N⌋₊,
        Real.log (3 * N) * (64 * Real.pi * ((M : ℝ) + 1)) := by
      apply norm_sum_le_of_le
      intro i hi
      have hiB : i + 1 ≤ ⌊3 * N⌋₊ := by have := Finset.mem_range.1 hi; omega
      have hiR : ((i + 1 : ℕ) : ℝ) ≤ 3 * N :=
        (show ((i + 1 : ℕ) : ℝ) ≤ ⌊3 * N⌋₊ by exact_mod_cast hiB).trans (Nat.floor_le (by positivity))
      have hi0 : (0 : ℝ) < (i + 1 : ℕ) := by positivity
      rw [norm_mul, Complex.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact mul_le_mul (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hi0 hiR))
        (hK _) (norm_nonneg _) hlog3
    _ = ((⌊3 * N⌋₊ : ℕ) : ℝ) *
        (Real.log (3 * N) * (64 * Real.pi * ((M : ℝ) + 1))) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (3 * N) * (Real.log (3 * N) * (64 * Real.pi * ((M : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity)
    _ = _ := by ring

private theorem hyperbolic_dilated_reciprocal_integrable {N δ : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) (M : ℕ) {n : ℕ} (hn : 0 < n) :
    IntegrableOn (fun t : ℝ => chiCubicHyperbolicPrimeKernel N M (t * n) / ((δ * t : ℝ) : ℂ))
      (Set.Icc (1 / (1 + δ)) 1) volume := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hg : Integrable (fun t : ℝ => chiCubicHyperbolicPrimeKernel N M (t * n)) volume := by
    simpa only [mul_comm (n : ℝ)] using
      (hyperbolic_kernel_integrable hN M).comp_mul_left' hnR.ne'
  have hc : ContinuousOn (fun t : ℝ => (((δ * t : ℝ) : ℂ))⁻¹) (Set.Icc (1 / (1 + δ)) 1) := by
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      have ht0 : 0 < t := (by positivity : (0 : ℝ) < 1 / (1 + δ)).trans_le ht.1
      exact_mod_cast (mul_pos hδ ht0).ne'
  simpa only [div_eq_mul_inv] using hg.integrableOn.mul_continuousOn hc isCompact_Icc

private theorem hyperbolic_trace_weight_integrable {N δ : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) (M : ℕ) :
    IntegrableOn (fun t : ℝ => chiCubicHyperbolicPrimeTrace N M t / ((δ * t : ℝ) : ℂ))
      (Set.Icc (1 / (1 + δ)) 1) volume := by
  classical
  have hi : IntegrableOn (fun t : ℝ => ∑ i ∈ Finset.range ⌊3 * N⌋₊,
      (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
        (chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)) / ((δ * t : ℝ) : ℂ)))
      (Set.Icc (1 / (1 + δ)) 1) volume :=
    integrable_finsetSum _ (fun i _ =>
      (hyperbolic_dilated_reciprocal_integrable hN hδ M (Nat.succ_pos i)).const_mul _)
  have heq : (fun t : ℝ => chiCubicHyperbolicPrimeTrace N M t / ((δ * t : ℝ) : ℂ)) =
      fun t => ∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
        (chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)) / ((δ * t : ℝ) : ℂ)) := by
    funext t
    unfold chiCubicHyperbolicPrimeTrace
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [heq]
  exact hi

private theorem integral_closed_dilation (f : ℝ → ℂ) {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) :
    (∫ x in Set.Icc (c * a) (c * b), f x) = c • ∫ t in Set.Icc a b, f (c * t) := by
  calc
    _ = ∫ x in (c * a)..(c * b), f x := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hc.le)]
    _ = c • ∫ t in a..b, f (c * t) := (intervalIntegral.smul_integral_comp_mul_left f c).symm
    _ = _ := by rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

private theorem hyperbolic_dual_term_dilation (N : ℝ) (M : ℕ) {δ : ℝ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < n) :
    (∫ x in Set.Ico ((n : ℝ) / (1 + δ)) n ∩ Set.Icc N (2 * N),
      chiCubicHyperbolicPrimeKernel N M x / ((δ * x : ℝ) : ℂ)) =
      ∫ t in Set.Icc (1 / (1 + δ)) 1,
        chiCubicHyperbolicPrimeKernel N M (t * n) / ((δ * t : ℝ) : ℂ) := by
  classical
  let F := fun x : ℝ => chiCubicHyperbolicPrimeKernel N M x / ((δ * x : ℝ) : ℂ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have ha : 1 / (1 + δ) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have heq : (Set.Icc N (2 * N)).indicator F = F := by
    funext x
    by_cases hx : x ∈ Set.Icc N (2 * N)
    · exact Set.indicator_of_mem hx _
    · simp only [Set.indicator_apply, if_neg hx, F,
        hyperbolic_kernel_zero_off_closed_band N M hx, zero_div]
  calc
    _ = ∫ x in Set.Ico ((n : ℝ) / (1 + δ)) n, F x := by
      rw [← setIntegral_indicator measurableSet_Icc, heq]
    _ = ∫ x in Set.Icc ((n : ℝ) * (1 / (1 + δ))) ((n : ℝ) * 1), F x := by
      rw [integral_Ico_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
      simp only [mul_one, mul_one_div]
    _ = (n : ℝ) • ∫ t in Set.Icc (1 / (1 + δ)) 1, F ((n : ℝ) * t) :=
      integral_closed_dilation F ha hnR
    _ = _ := by
      rw [← integral_smul]
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have ht0 : 0 < t := (by positivity : (0 : ℝ) < 1 / (1 + δ)).trans_le ht.1
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR.ne'
      have hδC : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
      have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
      dsimp only
      rw [Complex.real_smul]
      dsimp only [F]
      rw [mul_comm (n : ℝ) t]
      push_cast
      field_simp

/-- Exact positive dilation of every original half-open dual window, with the
complete weighted trace integrable on the common averaging interval. -/
theorem chiCubicHyperbolicVonMangoldtAverage_dilation {N : ℝ} (hN : 1 < N) (M : ℕ) :
    IntegrableOn (fun t : ℝ => chiCubicHyperbolicPrimeTrace N M t /
      ((N ^ ((1 : ℝ) / 5 - 1) * t : ℝ) : ℂ))
      (Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1) volume ∧
    chiCubicHyperbolicVonMangoldtAverage N M =
      ∫ t in Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
        chiCubicHyperbolicPrimeTrace N M t / ((N ^ ((1 : ℝ) / 5 - 1) * t : ℝ) : ℂ) := by
  classical
  have hN0 : 0 < N := by linarith
  have hδ : 0 < N ^ ((1 : ℝ) / 5 - 1) := Real.rpow_pos_of_pos hN0 _
  refine ⟨hyperbolic_trace_weight_integrable hN hδ M, ?_⟩
  unfold chiCubicHyperbolicVonMangoldtAverage
  rw [sum_Ioc_zero_eq_range]
  calc
    _ = ∑ i ∈ Finset.range ⌊3 * N⌋₊,
        ∫ t in Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
          (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
            (chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)) /
              ((N ^ ((1 : ℝ) / 5 - 1) * t : ℝ) : ℂ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hyperbolic_dual_term_dilation N M hδ (Nat.succ_pos i), integral_const_mul]
    _ = ∫ t in Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
        ∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
          (chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ)) /
            ((N ^ ((1 : ℝ) / 5 - 1) * t : ℝ) : ℂ)) :=
      (integral_finsetSum _ (fun i _ =>
        (hyperbolic_dilated_reciprocal_integrable hN hδ M (Nat.succ_pos i)).const_mul _)).symm
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp only
      unfold chiCubicHyperbolicPrimeTrace
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring

private theorem hyperbolic_trace_one_sub (N : ℝ) (M : ℕ) (t : ℝ) :
    chiCubicHyperbolicPrimeTrace N M 1 - chiCubicHyperbolicPrimeTrace N M t =
      ∑ i ∈ Finset.range ⌊3 * N⌋₊, (ArithmeticFunction.vonMangoldt (i + 1) : ℂ) *
        (chiCubicHyperbolicPrimeKernel N M (i + 1 : ℕ) -
          chiCubicHyperbolicPrimeKernel N M (t * (i + 1 : ℕ))) := by
  unfold chiCubicHyperbolicPrimeTrace
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_mul]
  ring

private theorem normalized_reciprocal_average_sub_le {δ q η : ℝ}
    (hδ : 0 < δ) (hq : 0 ≤ q) {F : ℝ → ℂ} {V : ℂ}
    (hF : IntegrableOn (fun t : ℝ => F t / ((δ * t : ℝ) : ℂ))
      (Set.Icc (1 / (1 + δ)) 1) volume)
    (hclose : ∀ t ∈ Set.Icc (1 / (1 + δ)) 1, q * ‖F t - V‖ ≤ η) :
    q * ‖(∫ t in Set.Icc (1 / (1 + δ)) 1, F t / ((δ * t : ℝ) : ℂ)) - V‖ ≤
      η + q * δ * ‖V‖ := by
  let a := 1 / (1 + δ)
  let c := (1 + δ) / δ
  have ha : a ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hc : 0 < c := by dsimp [c]; positivity
  have hcδ : c * δ = 1 + δ := by dsimp [c]; field_simp
  have hcminus : c - 1 = 1 / δ := by
    apply (eq_div_iff hδ.ne').2
    rw [sub_mul, hcδ, one_mul]
    ring
  have hmass : (1 - a) * c = 1 := by dsimp [a, c]; field_simp; ring
  have hlength : 1 - a ≤ δ := by
    have hlow : 1 - δ ≤ a := (le_div_iff₀ (by positivity)).2 (by nlinarith [sq_nonneg δ])
    linarith
  have hvol : volume.real (Set.Icc a 1) = 1 - a := Real.volume_real_Icc_of_le ha
  have hconst : (∫ _t in Set.Icc a 1, (c : ℂ) * V) = V := by
    rw [setIntegral_const, hvol, Complex.real_smul, ← mul_assoc,
      ← Complex.ofReal_mul, hmass, Complex.ofReal_one, one_mul]
  have hcint : IntegrableOn (fun _t : ℝ => (c : ℂ) * V) (Set.Icc a 1) volume :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have heq : (q : ℂ) * ((∫ t in Set.Icc a 1, F t / ((δ * t : ℝ) : ℂ)) - V) =
      ∫ t in Set.Icc a 1, (q : ℂ) * (F t / ((δ * t : ℝ) : ℂ) - (c : ℂ) * V) := by
    rw [integral_const_mul, integral_sub hF hcint, hconst]
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc a 1) :
      ‖(q : ℂ) * (F t / ((δ * t : ℝ) : ℂ) - (c : ℂ) * V)‖ ≤ c * η + q * ‖V‖ := by
    let w := 1 / (δ * t)
    have ht0 : 0 < t := (by dsimp [a]; positivity : 0 < a).trans_le ht.1
    have hw : 0 ≤ w := by dsimp [w]; positivity
    have htbase : 1 ≤ (1 + δ) * t := by
      have ht' : 1 / (1 + δ) ≤ t := ht.1
      have hh := (div_le_iff₀ (show 0 < 1 + δ by positivity)).1 ht'
      nlinarith
    have hwc : w ≤ c := by
      apply (div_le_iff₀ (mul_pos hδ ht0)).2
      calc 1 ≤ (1 + δ) * t := htbase
        _ = c * (δ * t) := by rw [← hcδ]; ring
    have hlow : 1 / δ ≤ w :=
      (div_le_div_iff₀ hδ (mul_pos hδ ht0)).2 (by nlinarith [ht.2])
    have hwcabs : |w - c| ≤ 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr hwc)]
      linarith [hcminus]
    have hnorm : ‖F t / ((δ * t : ℝ) : ℂ) - (c : ℂ) * V‖ ≤ w * ‖F t - V‖ + ‖V‖ := by
      calc
        _ = ‖(w : ℂ) * (F t - V) + ((w - c : ℝ) : ℂ) * V‖ := by
          congr 1
          dsimp only [w]
          push_cast
          ring
        _ ≤ ‖(w : ℂ) * (F t - V)‖ + ‖((w - c : ℝ) : ℂ) * V‖ := norm_add_le _ _
        _ = w * ‖F t - V‖ + |w - c| * ‖V‖ := by
          rw [norm_mul, norm_mul, Complex.norm_of_nonneg hw, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_right hwcabs (norm_nonneg V)
          simpa only [one_mul] using add_le_add le_rfl hh
    rw [norm_mul, Complex.norm_of_nonneg hq]
    calc
      _ ≤ q * (w * ‖F t - V‖ + ‖V‖) := mul_le_mul_of_nonneg_left hnorm hq
      _ ≤ q * (c * ‖F t - V‖ + ‖V‖) := by gcongr
      _ = c * (q * ‖F t - V‖) + q * ‖V‖ := by ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left (hclose t ht) hc.le) le_rfl
  calc
    _ = ‖(q : ℂ) * ((∫ t in Set.Icc a 1, F t / ((δ * t : ℝ) : ℂ)) - V)‖ := by
      rw [norm_mul, Complex.norm_of_nonneg hq]
    _ = ‖∫ t in Set.Icc a 1, (q : ℂ) * (F t / ((δ * t : ℝ) : ℂ) - (c : ℂ) * V)‖ := by rw [heq]
    _ ≤ (c * η + q * ‖V‖) * volume.real (Set.Icc a 1) :=
      norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top hpoint
    _ = η + q * (1 - a) * ‖V‖ := by
      rw [hvol]
      calc
        (c * η + q * ‖V‖) * (1 - a) =
            ((1 - a) * c) * η + q * (1 - a) * ‖V‖ := by ring
        _ = _ := by rw [hmass, one_mul]
    _ ≤ _ := by gcongr

private theorem hyperbolic_normalization_error_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N * N ^ ((1 : ℝ) / 5 - 1) *
      ‖chiCubicHyperbolicPrimeTrace N M 1‖) atTop (𝓝 0) := by
  let K := 64 * Real.pi * ((M : ℝ) + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hbase : Tendsto (fun N : ℝ => Real.log N ^ 3 / N ^ ((4 : ℝ) / 5)) atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := (4 : ℝ) / 5) (3 : ℕ)
      (by norm_num)).tendsto_div_nhds_zero
    simpa only [Real.rpow_natCast] using h
  have hlim := hbase.const_mul (9 * K)
  simp only [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1]
      with N hN hlog
    have hN0 : 0 < N := by linarith
    have hlog3 : Real.log (3 * N) ≤ 3 * Real.log N := by
      rw [Real.log_mul (by norm_num) hN0.ne']
      have hthree := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hp : 0 < N ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hN0 _
    have hδ : N ^ ((1 : ℝ) / 5 - 1) = 1 / N ^ ((4 : ℝ) / 5) := by
      apply (eq_div_iff hp.ne').2
      rw [← Real.rpow_add hN0]
      norm_num
    calc
      _ ≤ Real.log N ^ 2 / N * N ^ ((1 : ℝ) / 5 - 1) * (K * (3 * N * Real.log (3 * N))) :=
        mul_le_mul_of_nonneg_left (norm_hyperbolic_trace_le hN hlog M 1) (by positivity)
      _ ≤ Real.log N ^ 2 / N * N ^ ((1 : ℝ) / 5 - 1) * (K * (3 * N * (3 * Real.log N))) := by
        gcongr
      _ = _ := by rw [hδ]; field_simp; ring

/-- The actual finite dual average differs negligibly from the original discrete
von Mangoldt sum, with every sharp boundary and normalization error retained. -/
theorem chiCubicHyperbolicVonMangoldtDisplacement_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖chiCubicHyperbolicVonMangoldtAverage N M - chiCubicHyperbolicVonMangoldtSum N M‖)
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    exact ha.trans_le (by positivity)
  · intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    filter_upwards [eventually_ge_atTop (4 : ℝ),
      chiCubicHyperbolicPrimeKernel_shortWindow_sampling_tendsto M (ε / 2) hhalf,
      (hyperbolic_normalization_error_tendsto M).eventually_lt_const hhalf] with N hN hs hd
    have hN0 : 0 < N := by linarith
    have hN1 : 1 < N := by linarith
    have hδ : 0 < N ^ ((1 : ℝ) / 5 - 1) := Real.rpow_pos_of_pos hN0 _
    have hq : 0 ≤ Real.log N ^ 2 / N := by positivity
    have hi := chiCubicHyperbolicVonMangoldtAverage_dilation hN1 M
    have hclose : ∀ t ∈ Set.Icc (1 / (1 + N ^ ((1 : ℝ) / 5 - 1))) 1,
        Real.log N ^ 2 / N * ‖chiCubicHyperbolicPrimeTrace N M t - chiCubicHyperbolicPrimeTrace N M 1‖ ≤
          ε / 2 := by
      intro t ht
      rw [norm_sub_rev, hyperbolic_trace_one_sub]
      exact (hs t ht).le
    have hbound := normalized_reciprocal_average_sub_le hδ hq hi.1 hclose
    rw [← hi.2, chiCubicHyperbolicPrimeTrace_one hN0.le M] at hbound
    rw [chiCubicHyperbolicPrimeTrace_one hN0.le M] at hd
    exact hbound.trans_lt (by linarith)

/-- Unconditional transfer of the original ordered triple-prime packet to the
complete signed continuous hyperbolic kernel, at the required cubic scale. -/
theorem chiCubicHyperbolicPrimePacket_integral_tendsto (M : ℕ) :
    Tendsto (fun N : ℝ => Real.log N ^ 2 / N *
      ‖chiCubicHyperbolicPrimePacket N M -
        ∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x‖)
      atTop (𝓝 0) := by
  have hlim := ((chiCubicHyperbolicPrimePowerError_tendsto M).add
    (chiCubicHyperbolicVonMangoldtDisplacement_tendsto M)).add
      (chiCubicHyperbolicVonMangoldtAverage_tendsto M)
  simp only [add_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    positivity
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with N hN
    have hN0 : 0 < N := by linarith
    have hq : 0 ≤ Real.log N ^ 2 / N := by positivity
    let P := chiCubicHyperbolicPrimePacket N M
    let V := chiCubicHyperbolicVonMangoldtSum N M
    let A := chiCubicHyperbolicVonMangoldtAverage N M
    let J := ∫ x in Set.Icc N (2 * N), chiCubicHyperbolicPrimeKernel N M x
    have hnorm : ‖P - J‖ ≤ ‖V - P‖ + ‖A - V‖ + ‖A - J‖ := by
      calc
        _ = ‖(-(V - P) + -(A - V)) + (A - J)‖ := by congr 1; ring
        _ ≤ ‖-(V - P) + -(A - V)‖ + ‖A - J‖ := norm_add_le _ _
        _ ≤ (‖-(V - P)‖ + ‖-(A - V)‖) + ‖A - J‖ := add_le_add (norm_add_le _ _) le_rfl
        _ = _ := by rw [norm_neg, norm_neg]
    calc
      _ ≤ Real.log N ^ 2 / N * (‖V - P‖ + ‖A - V‖ + ‖A - J‖) :=
        mul_le_mul_of_nonneg_left hnorm hq
      _ = _ := by dsimp only [P, V, A, J]; ring

end RHTower
end
