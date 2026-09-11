import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusSignedEndpoint
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogarithmicNormalization

/-!
# Global admission and exact mass of the literal Gamma/Möbius logarithmic current

The actual current is admitted through an absolutely integrable signed Abel
assembly. The four-log Mertens saving absorbs the extra logarithm. Both the
pointwise Gamma terminal and the integrated scalar terminal are retained.
The logarithmic Möbius normalization then gives mass Gamma(3/2).

Every individual Euler dilation of the zero-mass preimage has zero mass,
while their complete current has mass Gamma(3/2). The exact interchange
defect is nonzero and its term norm integrals are not summable. Subtracting
the original Gamma source gives an admitted zero-mass difference. No global
parameter differentiation, spectral Ward identification or RH is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
noncomputable section

theorem pwGammaMertens_log_invSq_summable :
    Summable fun n : ℕ => |Sieve.mertensM n| * Real.log (n : ℝ) / (n : ℝ)^2 := by
  obtain ⟨B, hB, hrate⟩ := Sieve.deningerMertensM_log_pow_four_rate
  obtain ⟨K, hK⟩ := eventually_atTop.mp hrate
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1))
  let M := max K L
  have hMe : Real.exp 1 ≤ (M : ℝ) := hL M (le_max_right K L)
  have hmajor : Summable fun i : ℕ =>
      B / (((M : ℝ) + ((i : ℝ) + 1)) *
        Real.log ((M : ℝ) + ((i : ℝ) + 1)) ^ 3) := by
    simpa only [div_eq_mul_inv, one_div, one_mul] using
      (summable_one_div_mul_log_three hMe).mul_left B
  apply (summable_nat_add_iff (M + 1)).mp
  refine Summable.of_norm_bounded hmajor fun i => ?_
  let n := i + (M + 1)
  have hnM : M ≤ n := (Nat.le_succ M).trans (Nat.le_add_left _ _)
  have hne : Real.exp 1 ≤ (n : ℝ) := hMe.trans (by exact_mod_cast hnM)
  have hnpos : (0 : ℝ) < n := (Real.exp_pos 1).trans_le hne
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos
    ((Real.one_lt_exp_iff.mpr zero_lt_one).trans_le hne)
  have hr := hK n ((le_max_left K L).trans hnM)
  change ‖|Sieve.mertensM n| * Real.log (n : ℝ) / (n : ℝ)^2‖ ≤ _
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (B * (n : ℝ) / Real.log (n : ℝ)^4) * Real.log (n : ℝ) / (n : ℝ)^2 := by gcongr
    _ = B / ((n : ℝ) * Real.log (n : ℝ)^3) := by field_simp
    _ = _ := by
      have heq : (n : ℝ) = (M : ℝ) + ((i : ℝ) + 1) := by dsimp [n]; push_cast; ring
      rw [heq]

private theorem pwGamma_log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem pwGammaMertens_log_div_tendsto_zero :
    Tendsto (fun n : ℕ => Sieve.mertensM n * Real.log (n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  obtain ⟨B, hB, hrate⟩ := Sieve.deningerMertensM_log_pow_four_rate
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => (Real.log (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hlog
  have hmaj : Tendsto (fun n : ℕ => B / Real.log (n : ℝ)^3) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (hi.pow 3).const_mul B
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hrate, eventually_gt_atTop 1] with n hn hn1
  have hnr : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_one.trans hn1)
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn1)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hnr, abs_of_pos hl]
  calc
    _ ≤ (B * (n : ℝ) / Real.log (n : ℝ)^4) * Real.log (n : ℝ) / (n : ℝ) := by gcongr
    _ = _ := by field_simp

private theorem pwGammaLog_dilation_integrable {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun x => pwGammaRaySource (r*x)) (Ioi 0) := by
  apply (integrableOn_Ioi_comp_mul_left_iff pwGammaRaySource 0 hr).mpr
  simpa only [mul_zero] using pwGammaRaySource_integrable

/-- Signed atoms of the actual logarithmic current. -/
def pwGammaMobiusLogAbelAtom (n : ℕ) (x : ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ) *
    ((Real.log ((n : ℝ)+1) : ℂ) * pwGammaRaySource (((n : ℝ)+1)*x) -
      (Real.log (n : ℝ) : ℂ) * pwGammaRaySource ((n : ℝ)*x))

private theorem pwGammaLog_mertens_zero : Sieve.mertensM 0 = 0 := by simp [Sieve.mertensM]
private theorem pwGammaMobiusLogAbelAtom_zero : pwGammaMobiusLogAbelAtom 0 = 0 := by
  funext x
  simp [pwGammaMobiusLogAbelAtom, pwGammaLog_mertens_zero]

theorem pwGammaMobiusLogAbelAtom_integrable (n : ℕ) :
    IntegrableOn (pwGammaMobiusLogAbelAtom n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaMobiusLogAbelAtom_zero]; exact integrable_zero ℝ ℂ _
  · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
    exact (((pwGammaLog_dilation_integrable (show 0 < (n:ℝ)+1 by positivity)).const_mul _).sub
      ((pwGammaLog_dilation_integrable hnr).const_mul _)).const_mul _

theorem pwGammaMobiusLogAbelAtom_decomposition (n : ℕ) (x : ℝ) :
    pwGammaMobiusLogAbelAtom n x =
      -(Real.log (n : ℝ) : ℂ) * pwGammaMobiusAbelAtom n x +
      (Sieve.mertensM n : ℂ) * ((Real.log ((n : ℝ)+1) - Real.log (n : ℝ) : ℝ) : ℂ) *
        pwGammaRaySource (((n : ℝ)+1)*x) := by
  simp only [pwGammaMobiusLogAbelAtom, pwGammaMobiusAbelAtom, Complex.ofReal_sub]
  ring

theorem pwGammaMobiusLogAbelAtom_integral_norm_le (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusLogAbelAtom n x‖) ≤
      (Real.Gamma (3/2) + Real.Gamma (5/2)) *
        (|Sieve.mertensM n| * Real.log (n : ℝ) / (n : ℝ)^2) +
      Real.Gamma (3/2) * (|Sieve.mertensM n| / (n : ℝ)^2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusLogAbelAtom_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  have hl := pwGamma_log_nat_nonneg n
  have hd0 : 0 ≤ Real.log ((n : ℝ)+1) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hnr (by linarith))
  have hd := log_natCast_succ_sub_log_natCast_le_inv n hn
  have hq : (∫ x in Ioi (0 : ℝ), ‖pwGammaRaySource (((n : ℝ)+1)*x)‖) =
      Real.Gamma (3/2) / ((n : ℝ)+1) := by
    rw [integral_comp_mul_left_Ioi (fun y => ‖pwGammaRaySource y‖) 0 hn1]
    simp only [mul_zero, smul_eq_mul, pwGammaRaySource_norm_integral]
    ring
  have hg : 0 ≤ Real.Gamma (3/2) := (Real.Gamma_pos_of_pos (by positivity)).le
  have hb : (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusLogAbelAtom n x‖) ≤
      Real.log (n : ℝ) * (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusAbelAtom n x‖) +
      |Sieve.mertensM n| * (Real.log ((n : ℝ)+1) - Real.log (n : ℝ)) *
        (Real.Gamma (3/2) / ((n : ℝ)+1)) := by
    rw [← hq, ← integral_const_mul, ← integral_const_mul, ← integral_add
      ((pwGammaMobiusAbelAtom_integrable n).norm.const_mul _)
      ((pwGammaLog_dilation_integrable hn1).norm.const_mul _)]
    apply integral_mono (pwGammaMobiusLogAbelAtom_integrable n).norm
      (((pwGammaMobiusAbelAtom_integrable n).norm.const_mul _).add
        ((pwGammaLog_dilation_integrable hn1).norm.const_mul _))
    intro x
    change ‖pwGammaMobiusLogAbelAtom n x‖ ≤ Real.log (n : ℝ) * ‖pwGammaMobiusAbelAtom n x‖ +
      |Sieve.mertensM n| * (Real.log ((n : ℝ)+1) - Real.log (n : ℝ)) *
        ‖pwGammaRaySource (((n : ℝ)+1)*x)‖
    rw [pwGammaMobiusLogAbelAtom_decomposition]
    calc
      _ ≤ ‖-(Real.log (n : ℝ) : ℂ) * pwGammaMobiusAbelAtom n x‖ +
          ‖(Sieve.mertensM n : ℂ) * ((Real.log ((n : ℝ)+1) - Real.log (n : ℝ) : ℝ) : ℂ) *
            pwGammaRaySource (((n : ℝ)+1)*x)‖ := norm_add_le _ _
      _ = _ := by simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hl, abs_of_nonneg hd0]
  calc
    _ ≤ _ := hb
    _ ≤ Real.log (n : ℝ) *
        ((Real.Gamma (3/2)+Real.Gamma (5/2)) * (|Sieve.mertensM n| / (n : ℝ)^2)) +
        |Sieve.mertensM n| * (1/(n : ℝ)) * (Real.Gamma (3/2) / (n : ℝ)) := by
      gcongr
      · exact pwGammaMobiusAbelAtom_integral_norm_le n
      · linarith
    _ = _ := by ring

theorem pwGammaMobiusLogAbelAtom_norm_integrals_summable :
    Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusLogAbelAtom n x‖ := by
  exact ((pwGammaMertens_log_invSq_summable.mul_left
      (Real.Gamma (3/2)+Real.Gamma (5/2))).add
      (deningerMertensM_invSq_summable.mul_left (Real.Gamma (3/2)))).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) pwGammaMobiusLogAbelAtom_integral_norm_le

theorem pwGammaMobiusLogAbel_finite (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, pwGammaMobiusLogAbelAtom n x) =
      (∑ n ∈ Finset.range (N+1), ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((n : ℝ)*x)) +
      (Real.log (N : ℝ) : ℂ) * pwGammaRaySource ((N : ℝ)*x) * (Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => -(Real.log (n : ℝ) : ℂ) * pwGammaRaySource ((n : ℝ)*x)
  let G : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n+1), G j) = (Sieve.mertensM n : ℂ) := by
    intro n
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hd : (∑ n ∈ Finset.range N, (F (n+1)-F n) * (Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, pwGammaMobiusLogAbelAtom n x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, pwGammaMobiusLogAbelAtom, Nat.cast_add, Nat.cast_one]
    ring
  have hm : (∑ n ∈ Finset.range (N+1), F n * G n) =
      (∑ n ∈ Finset.range (N+1), ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((n : ℝ)*x)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, G, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  rw [hd, hm] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts

theorem pwGammaMobiusLogAbel_boundary_tendsto_zero {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ) : ℂ) * pwGammaRaySource ((n : ℝ)*x) *
      (Sieve.mertensM n : ℂ)) atTop (𝓝 0) := by
  let C : ℝ := Real.exp ((5/2)*Real.log (5/2)-5/2)
  have hm := ((pwGammaMertens_log_div_tendsto_zero.norm).mul
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).const_mul (C / x^2)
  simp only [norm_zero, mul_zero] at hm
  refine squeeze_zero_norm' ?_ hm
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := pwGamma_log_nat_nonneg n
  have hq := pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hl]
  calc
    _ ≤ Real.log (n : ℝ) * (C / ((n : ℝ)*x)^2) * |Sieve.mertensM n| := by gcongr
    _ = (C / x^2) * (‖Sieve.mertensM n * Real.log (n : ℝ) / (n : ℝ)‖ * (1/(n : ℝ))) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hl, abs_of_pos hnr, mul_pow]
      ring

theorem pwGammaMobiusLogAbelAtom_summable {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => pwGammaMobiusLogAbelAtom n x) := by
  let C : ℝ := Real.exp ((5/2)*Real.log (5/2)-5/2)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hm := ((pwGammaMertens_log_invSq_summable.mul_left 2).add
    deningerMertensM_invSq_summable).mul_left (C/x^2)
  refine Summable.of_norm_bounded hm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusLogAbelAtom_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := pwGamma_log_nat_nonneg n
  have hl1 : 0 ≤ Real.log ((n : ℝ)+1) := Real.log_nonneg (by linarith)
  have hd := log_natCast_succ_sub_log_natCast_le_inv n hn
  have hi : 1/(n : ℝ) ≤ 1 := (div_le_one hnr).mpr hnr1
  have hlb : Real.log ((n : ℝ)+1) ≤ Real.log (n : ℝ)+1 := by linarith
  have hq0 : ‖pwGammaRaySource ((n : ℝ)*x)‖ ≤ C/((n : ℝ)*x)^2 :=
    pwGammaRaySource_norm_le_inv_sq (mul_pos hnr hx)
  have hq1 : ‖pwGammaRaySource (((n : ℝ)+1)*x)‖ ≤ C/((n : ℝ)*x)^2 := by
    refine (pwGammaRaySource_norm_le_inv_sq (show 0 < ((n : ℝ)+1)*x by positivity)).trans ?_
    apply div_le_div_of_nonneg_left hC (sq_pos_of_pos (mul_pos hnr hx))
    gcongr
    linarith
  rw [pwGammaMobiusLogAbelAtom, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |Sieve.mertensM n| *
        (‖(Real.log ((n : ℝ)+1) : ℂ)*pwGammaRaySource (((n : ℝ)+1)*x)‖ +
          ‖(Real.log (n : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*x)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ = |Sieve.mertensM n| *
        (Real.log ((n : ℝ)+1)*‖pwGammaRaySource (((n : ℝ)+1)*x)‖ +
          Real.log (n : ℝ)*‖pwGammaRaySource ((n : ℝ)*x)‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hl1]
    _ ≤ |Sieve.mertensM n| *
        ((Real.log (n : ℝ)+1)*(C/((n : ℝ)*x)^2) + Real.log (n : ℝ)*(C/((n : ℝ)*x)^2)) := by gcongr
    _ = _ := by rw [mul_pow]; ring

theorem pwGammaMobiusLogAbel_hasSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => pwGammaMobiusLogAbelAtom n x) (pwGammaMobiusLogCurrent x) := by
  have hp : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1),
      ((-(((moebius n : ℤ) : ℝ)*Real.log (n : ℝ)) : ℝ) : ℂ) *
        pwGammaRaySource ((n : ℝ)*x)) atTop (𝓝 (pwGammaMobiusLogCurrent x)) :=
    (pwGammaMobiusLogCurrent_summable hx).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hh := hp.add (pwGammaMobiusLogAbel_boundary_tendsto_zero hx)
  simp only [add_zero] at hh
  have ht : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, pwGammaMobiusLogAbelAtom n x)
      atTop (𝓝 (pwGammaMobiusLogCurrent x)) :=
    hh.congr fun N => (pwGammaMobiusLogAbel_finite N x).symm
  exact (hasSum_iff_tendsto_nat_of_summable_norm (pwGammaMobiusLogAbelAtom_summable hx).norm).mpr ht

/-- The original, unregularized logarithmic current is globally admitted. -/
theorem pwGammaMobiusLogCurrent_integrable : IntegrableOn pwGammaMobiusLogCurrent (Ioi 0) := by
  have hs := integrable_tsum_of_summable_integral_norm pwGammaMobiusLogAbelAtom_integrable
    pwGammaMobiusLogAbelAtom_norm_integrals_summable
  exact IntegrableOn.congr_fun hs (fun x hx => (pwGammaMobiusLogAbel_hasSum hx).tsum_eq)
    measurableSet_Ioi

theorem pwGammaMobiusLogAbelAtom_integral (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogAbelAtom n x) =
      ((Sieve.mertensM n * (Real.log ((n : ℝ)+1)/((n : ℝ)+1) -
        Real.log (n : ℝ)/(n : ℝ)) : ℝ) : ℂ) * (Real.Gamma (3/2) : ℂ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusLogAbelAtom_zero, pwGammaLog_mertens_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  change (∫ x in Ioi (0 : ℝ), (Sieve.mertensM n : ℂ) *
    ((Real.log ((n : ℝ)+1) : ℂ) * pwGammaRaySource (((n : ℝ)+1)*x) -
      (Real.log (n : ℝ) : ℂ) * pwGammaRaySource ((n : ℝ)*x))) = _
  rw [integral_const_mul, integral_sub
    ((pwGammaLog_dilation_integrable hn1).const_mul _) ((pwGammaLog_dilation_integrable hnr).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_comp_mul_left_Ioi pwGammaRaySource 0 hn1,
    integral_comp_mul_left_Ioi pwGammaRaySource 0 hnr]
  simp only [mul_zero, pwGammaRaySource_integral, Complex.real_smul, Complex.ofReal_inv]
  push_cast
  ring

theorem pwGammaMobiusLogAbel_scalar_finite (N : ℕ) :
    (∑ n ∈ Finset.range N, Sieve.mertensM n *
      (Real.log ((n : ℝ)+1)/((n : ℝ)+1) - Real.log (n : ℝ)/(n : ℝ))) =
        Sieve.moebiusLogHarmonicPartial N + Sieve.mertensM N * Real.log (N : ℝ)/(N : ℝ) := by
  have ha := deningerAbelSummation (fun n => ((moebius n : ℤ) : ℝ))
    (fun n => -Real.log (n : ℝ)/(n : ℝ)) N
  have hs : ∀ n, deningerPartialSum (fun k => ((moebius k : ℤ) : ℝ)) n = Sieve.mertensM n :=
    fun _ => rfl
  simp only [hs, Nat.cast_add, Nat.cast_one, neg_div, neg_sub_neg] at ha
  have hm : (∑ n ∈ Finset.range (N+1), ((moebius n : ℤ) : ℝ) * -(Real.log (n : ℝ)/(n : ℝ))) =
      Sieve.moebiusLogHarmonicPartial N := by
    unfold Sieve.moebiusLogHarmonicPartial
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Sieve.moebiusLogHarmonicTerm, Real.rpow_neg_one]
    ring
  rw [hm] at ha
  linear_combination -ha

theorem pwGammaMobiusLogAbel_integral_hasSum :
    HasSum (fun n : ℕ => ∫ x in Ioi (0 : ℝ), pwGammaMobiusLogAbelAtom n x)
      (Real.Gamma (3/2) : ℂ) := by
  have hs : Summable (fun n : ℕ => ‖∫ x in Ioi (0 : ℝ), pwGammaMobiusLogAbelAtom n x‖) :=
    pwGammaMobiusLogAbelAtom_norm_integrals_summable.of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  have ht := Sieve.tendsto_moebiusLogHarmonicPartial_one.add pwGammaMertens_log_div_tendsto_zero
  simp only [add_zero] at ht
  have hc := ((Complex.continuous_ofReal.tendsto 1).comp ht).mul_const (Real.Gamma (3/2) : ℂ)
  simp only [Complex.ofReal_one, one_mul] at hc
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  refine hc.congr fun N => ?_
  simp only [pwGammaMobiusLogAbelAtom_integral, ← Finset.sum_mul,
    ← Complex.ofReal_sum, pwGammaMobiusLogAbel_scalar_finite]
  rfl

/-- The full current retains the exact nonzero Gamma mass. -/
theorem pwGammaMobiusLogCurrent_integral :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x) = (Real.Gamma (3/2) : ℂ) := by
  have he : (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x) =
      ∫ x in Ioi (0 : ℝ), ∑' n, pwGammaMobiusLogAbelAtom n x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => (pwGammaMobiusLogAbel_hasSum hx).tsum_eq.symm
  rw [he, ← integral_tsum_of_summable_integral_norm pwGammaMobiusLogAbelAtom_integrable
    pwGammaMobiusLogAbelAtom_norm_integrals_summable]
  exact pwGammaMobiusLogAbel_integral_hasSum.tsum_eq


/-- Every individual arithmetic-current term has zero mass. -/
theorem pwGammaMobiusEulerTerm_integral_zero (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [integral_const_mul, pwGammaMobiusPreimage_dilation_integral_zero (by exact_mod_cast hn), mul_zero]

theorem pwGammaMobiusEulerTerm_integrable (n : ℕ) :
    IntegrableOn (fun x => (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hh : IntegrableOn (fun x => pwGammaMobiusPreimage ((n : ℝ)*x)) (Ioi 0) := by
      apply (integrableOn_Ioi_comp_mul_left_iff pwGammaMobiusPreimage 0 (by exact_mod_cast hn)).mpr
      simpa only [mul_zero] using pwGammaMobiusPreimage_integrable
    exact hh.const_mul _

theorem pwGammaMobiusEulerCurrent_integrable :
    IntegrableOn (fun x => ∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) (Ioi 0) :=
  IntegrableOn.congr_fun pwGammaMobiusLogCurrent_integrable
    (fun _ hx => (pwGammaMobius_connection hx).symm) measurableSet_Ioi

theorem pwGammaMobiusEulerCurrent_integral :
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) =
      (Real.Gamma (3/2) : ℂ) := by
  rw [← pwGammaMobiusLogCurrent_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaMobius_connection hx

/-- The full Euler current has the same nonzero interchange defect as reconstruction. -/
theorem pwGammaMobiusEulerCurrent_integral_defect :
    (∫ x in Ioi (0 : ℝ), ∑' n : ℕ, (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) -
      (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) =
        (Real.Gamma (3/2) : ℂ) := by
  simp only [pwGammaMobiusEulerCurrent_integral, pwGammaMobiusEulerTerm_integral_zero, tsum_zero, sub_zero]

theorem pwGammaMobiusEulerCurrent_not_summable_norm_integrals :
    ¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      ‖(vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)‖) := by
  intro hs
  have hswap := integral_tsum_of_summable_integral_norm pwGammaMobiusEulerTerm_integrable hs
  have hd := pwGammaMobiusEulerCurrent_integral_defect
  rw [hswap, sub_self] at hd
  have hg : 0 < Real.Gamma (3/2) := Real.Gamma_pos_of_pos (by positivity)
  exact (Complex.ofReal_ne_zero.mpr hg.ne') hd.symm

/-- The complete current minus the original source has admitted zero total mass. -/
theorem pwGammaMobiusLogCurrent_sub_source_zero_mass :
    IntegrableOn (fun x => pwGammaMobiusLogCurrent x - pwGammaRaySource x) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x - pwGammaRaySource x) = 0 := by
  refine ⟨pwGammaMobiusLogCurrent_integrable.sub pwGammaRaySource_integrable, ?_⟩
  rw [integral_sub pwGammaMobiusLogCurrent_integrable pwGammaRaySource_integrable,
    pwGammaMobiusLogCurrent_integral, pwGammaRaySource_integral, sub_self]

/-- Closed global statement for the actual current and its complete source contribution. -/
theorem pwGammaMobiusLogarithmicCurrent_closed :
    IntegrableOn pwGammaMobiusLogCurrent (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x) = (Real.Gamma (3/2) : ℂ) ∧
    (∀ n : ℕ, (∫ x in Ioi (0 : ℝ), (vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)) = 0) ∧
    (¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ),
      ‖(vonMangoldt n : ℂ) * pwGammaMobiusPreimage ((n : ℝ)*x)‖)) ∧
    (IntegrableOn (fun x => pwGammaMobiusLogCurrent x - pwGammaRaySource x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), pwGammaMobiusLogCurrent x - pwGammaRaySource x) = 0) :=
  ⟨pwGammaMobiusLogCurrent_integrable, pwGammaMobiusLogCurrent_integral,
    pwGammaMobiusEulerTerm_integral_zero, pwGammaMobiusEulerCurrent_not_summable_norm_integrals,
    pwGammaMobiusLogCurrent_sub_source_zero_mass⟩

end
end RHTower
