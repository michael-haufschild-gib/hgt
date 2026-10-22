import GaloisForLFunctions.RHTower.MobiusThetaNativeJetEulerConnection
import GaloisForLFunctions.RHTower.MobiusThetaNativeEulerMass
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaMobiusLogarithmicCurrent

/-!
# Complete critical Euler currents and their origin contacts

On each original native collar, the complete undamped von Mangoldt current
is integrable and retains the original Xi-jet mass. Its admission follows
from a signed Abel assembly with an integrable logarithmic Mertens majorant.

The series of original causal pairings differs from the regular current
pairing by its exact value-at-origin contact. Subtracting the test value
inside the original terms gives a summable integral-of-norm bound from the
Möbius preimage's first absolute moment. Both native collar normalizations
are retained. These comparisons do not assert fixed Gamma/BV reader equality.
-/

set_option autoImplicit false
open Complex MeasureTheory ArithmeticFunction Filter Topology Set
open scoped SchwartzMap
noncomputable section
namespace RHTower

private abbrev H (h : DeningerExpSchwartz) := deningerLogPull h
private abbrev weightedVariation (h : DeningerExpSchwartz) := (deningerWeightedMomentMass h).toReal
private def Pabs (h : DeningerExpSchwartz) : ℝ := ∫ x in Set.Ioi (0 : ℝ), ‖H h x‖

private theorem log_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

private theorem delta_integral_norm_le (h : DeningerExpSchwartz) {n : ℕ} (hn : 0 < n) :
    (∫ x in Set.Ioi (0 : ℝ), ‖H h (((n : ℝ) + 1) * x) - H h ((n : ℝ) * x)‖) ≤
      weightedVariation h / (n : ℝ)^(2 : ℕ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hint := (deningerLogPull_dilation_integrable h.property
    (show 0 < (n : ℝ)+1 by positivity)).sub
      (deningerLogPull_dilation_integrable h.property hnR)
  have hint' : IntegrableOn (fun x => H h (((n : ℝ)+1)*x) - H h ((n : ℝ)*x)) (Ioi 0) := hint
  have hb := deningerAbelDifference_mass_le h hn
  have ht : ENNReal.ofReal (1 / ((n : ℝ) * ((n : ℝ) + 1))) *
      deningerWeightedMomentMass h ≠ ⊤ :=
    ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (deningerWeightedMomentMass_lt_top h.property))
  have hr := ENNReal.toReal_mono ht hb
  rw [integral_norm_eq_lintegral_enorm hint'.aestronglyMeasurable]
  calc
    _ ≤ (1 / ((n : ℝ) * ((n : ℝ) + 1))) * weightedVariation h := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
        (show 0 ≤ 1 / ((n : ℝ) * ((n : ℝ)+1)) by positivity)] at hr
      exact hr
    _ ≤ weightedVariation h / (n : ℝ)^(2 : ℕ) := by
      rw [one_div, mul_comm, ← div_eq_mul_inv]
      apply div_le_div_of_nonneg_left ENNReal.toReal_nonneg (by positivity)
      nlinarith

private def atom (h : DeningerExpSchwartz) (n : ℕ) (x : ℝ) : ℂ :=
  (Sieve.mertensM n : ℂ) *
    ((Real.log ((n : ℝ)+1) : ℂ) * H h (((n : ℝ)+1)*x) -
      (Real.log (n : ℝ) : ℂ) * H h ((n : ℝ)*x))

private theorem atom_zero (h : DeningerExpSchwartz) : atom h 0 = 0 := by
  funext x
  simp [atom, Sieve.mertensM]

private theorem atom_integrable (h : DeningerExpSchwartz) (n : ℕ) :
    IntegrableOn (atom h n) (Set.Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [atom_zero]; exact integrable_zero ℝ ℂ _
  · exact (((deningerLogPull_dilation_integrable h.property
      (show 0 < (n : ℝ)+1 by positivity)).const_mul _).sub
      ((deningerLogPull_dilation_integrable h.property (by exact_mod_cast hn)).const_mul _)).const_mul _

private theorem atom_decomposition (h : DeningerExpSchwartz) (n : ℕ) (x : ℝ) :
    atom h n x =
      ((Sieve.mertensM n : ℂ) * (Real.log (n : ℝ) : ℂ)) *
        (H h (((n : ℝ)+1)*x) - H h ((n : ℝ)*x)) +
      ((Sieve.mertensM n : ℂ) *
        ((Real.log ((n : ℝ)+1) - Real.log (n : ℝ) : ℝ) : ℂ)) * H h (((n : ℝ)+1)*x) := by
  simp only [atom, Complex.ofReal_sub]
  ring

private theorem atom_integral_norm_le (h : DeningerExpSchwartz) (n : ℕ) :
    (∫ x in Set.Ioi (0 : ℝ), ‖atom h n x‖) ≤
      weightedVariation h * (|Sieve.mertensM n| * Real.log (n : ℝ) / (n : ℝ)^(2 : ℕ)) +
      Pabs h * (|Sieve.mertensM n| / (n : ℝ)^(2 : ℕ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [atom_zero]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  have hl := log_nonneg n
  have hd0 : 0 ≤ Real.log ((n : ℝ)+1) - Real.log (n : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log hnR (by linarith))
  have hd := log_natCast_succ_sub_log_natCast_le_inv n hn
  have hp0 : 0 ≤ Pabs h := integral_nonneg fun _ => norm_nonneg _
  have hi0 := deningerLogPull_dilation_integrable h.property hnR
  have hi1 := deningerLogPull_dilation_integrable h.property hn1
  have hm : (∫ x in Set.Ioi (0 : ℝ), ‖H h (((n : ℝ)+1)*x)‖) =
      Pabs h / ((n : ℝ)+1) := by
    rw [integral_comp_mul_left_Ioi (fun y => ‖H h y‖) 0 hn1]
    simp only [mul_zero, smul_eq_mul, Pabs]
    ring
  have hb : (∫ x in Set.Ioi (0 : ℝ), ‖atom h n x‖) ≤
      (|Sieve.mertensM n| * Real.log (n : ℝ)) *
        (∫ x in Set.Ioi (0 : ℝ), ‖H h (((n : ℝ)+1)*x) - H h ((n : ℝ)*x)‖) +
      (|Sieve.mertensM n| * (Real.log ((n : ℝ)+1) - Real.log (n : ℝ))) *
        (Pabs h / ((n : ℝ)+1)) := by
    rw [← hm, ← integral_const_mul, ← integral_const_mul]
    change (∫ x in Set.Ioi (0 : ℝ), ‖atom h n x‖) ≤
      (∫ x in Set.Ioi (0 : ℝ), |Sieve.mertensM n| * Real.log (n : ℝ) *
        ‖((fun y => H h (((n : ℝ)+1)*y)) - (fun y => H h ((n : ℝ)*y))) x‖) + _
    rw [← integral_add ((hi1.sub hi0).norm.const_mul _) (hi1.norm.const_mul _)]
    apply integral_mono (atom_integrable h n).norm
      (((hi1.sub hi0).norm.const_mul _).add (hi1.norm.const_mul _))
    intro x
    change ‖atom h n x‖ ≤ |Sieve.mertensM n| * Real.log (n : ℝ) *
      ‖H h (((n : ℝ)+1)*x) - H h ((n : ℝ)*x)‖ +
      |Sieve.mertensM n| * (Real.log ((n : ℝ)+1) - Real.log (n : ℝ)) *
      ‖H h (((n : ℝ)+1)*x)‖
    rw [atom_decomposition]
    refine (norm_add_le _ _).trans_eq ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hl, abs_of_nonneg hd0]
  calc
    _ ≤ _ := hb
    _ ≤ (|Sieve.mertensM n| * Real.log (n : ℝ)) * (weightedVariation h / (n : ℝ)^(2 : ℕ)) +
        (|Sieve.mertensM n| * (1/(n : ℝ))) * (Pabs h / (n : ℝ)) := by
      gcongr
      · exact delta_integral_norm_le h hn
      · linarith
    _ = _ := by ring

private theorem atom_norm_integrals_summable (h : DeningerExpSchwartz) :
    Summable (fun n : ℕ => ∫ x in Set.Ioi (0 : ℝ), ‖atom h n x‖) :=
  ((pwGammaMertens_log_invSq_summable.mul_left (weightedVariation h)).add
    (deningerMertensM_invSq_summable.mul_left (Pabs h))).of_nonneg_of_le
      (fun _ => integral_nonneg fun _ => norm_nonneg _) (atom_integral_norm_le h)

private theorem current_summable (h : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
      H h ((n : ℝ) * x)) := by
  obtain ⟨C, hC0, hC⟩ := deningerLogPull_norm_le_inv_sq h.property
  refine Summable.of_norm_bounded (Sieve.summable_log_div_sq.mul_left (C / x^(2 : ℕ))) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := log_nonneg n
  have hmu : |((moebius n : ℤ) : ℝ)| ≤ 1 := by
    rcases moebius_eq_or n with hm | hm | hm <;> rw [hm] <;> norm_num
  have hpull := (hC ((n : ℝ)*x) (mul_pos hnR hx)).2
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
    abs_mul, abs_of_nonneg hl]
  calc
    _ ≤ 1 * Real.log (n : ℝ) * (C / ((n : ℝ)*x)^(2 : ℕ)) := by gcongr
    _ = _ := by rw [mul_pow]; ring


private theorem atom_finite (h : DeningerExpSchwartz) (N : ℕ) (x : ℝ) :
    (∑ n ∈ Finset.range N, atom h n x) =
      (∑ n ∈ Finset.range (N+1), ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        H h ((n : ℝ)*x)) +
      (Real.log (N : ℝ) : ℂ) * H h ((N : ℝ)*x) * (Sieve.mertensM N : ℂ) := by
  classical
  let F : ℕ → ℂ := fun n => -(Real.log (n : ℝ) : ℂ) * H h ((n : ℝ)*x)
  let G : ℕ → ℂ := fun n => ((moebius n : ℤ) : ℂ)
  have hsum : ∀ n : ℕ, (∑ j ∈ Finset.range (n+1), G j) = (Sieve.mertensM n : ℂ) := by
    intro n
    simp only [Sieve.mertensM, G, Complex.ofReal_sum, Complex.ofReal_intCast]
  have hparts := Finset.sum_range_by_parts F G (N+1)
  simp only [Nat.add_sub_cancel, smul_eq_mul, hsum] at hparts
  have hd : (∑ n ∈ Finset.range N, (F (n+1)-F n) * (Sieve.mertensM n : ℂ)) =
      -(∑ n ∈ Finset.range N, atom h n x) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, atom, Nat.cast_add, Nat.cast_one]
    ring
  have hm : (∑ n ∈ Finset.range (N+1), F n * G n) =
      (∑ n ∈ Finset.range (N+1), ((-(((moebius n : ℤ) : ℝ) * Real.log (n : ℝ)) : ℝ) : ℂ) *
        H h ((n : ℝ)*x)) := by
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [F, G, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  rw [hd, hm] at hparts
  dsimp only [F] at hparts
  linear_combination -hparts

private theorem boundary_tendsto_zero (h : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => (Real.log (n : ℝ) : ℂ) * H h ((n : ℝ)*x) *
      (Sieve.mertensM n : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := deningerLogPull_norm_le_inv_sq h.property
  have hm := ((pwGammaMertens_log_div_tendsto_zero.norm).mul
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))).const_mul (C / x^(2 : ℕ))
  simp only [norm_zero, mul_zero] at hm
  refine squeeze_zero_norm' ?_ hm
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hl := log_nonneg n
  have hq := (hbound _ (mul_pos hnr hx)).2
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hl]
  calc
    _ ≤ Real.log (n : ℝ) * (C / ((n : ℝ)*x)^(2 : ℕ)) * |Sieve.mertensM n| := by gcongr
    _ = (C / x^(2 : ℕ)) * (‖Sieve.mertensM n * Real.log (n : ℝ) / (n : ℝ)‖ * (1/(n : ℝ))) := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hl, abs_of_pos hnr, mul_pow]
      ring

private theorem atom_summable (h : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => atom h n x) := by
  obtain ⟨C, hC, hbound⟩ := deningerLogPull_norm_le_inv_sq h.property
  have hm := ((pwGammaMertens_log_invSq_summable.mul_left 2).add
    deningerMertensM_invSq_summable).mul_left (C/x^(2 : ℕ))
  refine Summable.of_norm_bounded hm fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [atom_zero h]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl := log_nonneg n
  have hl1 : 0 ≤ Real.log ((n : ℝ)+1) := Real.log_nonneg (by linarith)
  have hd := log_natCast_succ_sub_log_natCast_le_inv n hn
  have hi : 1/(n : ℝ) ≤ 1 := (div_le_one hnr).mpr hnr1
  have hlb : Real.log ((n : ℝ)+1) ≤ Real.log (n : ℝ)+1 := by linarith
  have hq0 : ‖H h ((n : ℝ)*x)‖ ≤ C/((n : ℝ)*x)^(2 : ℕ) :=
    (hbound _ (mul_pos hnr hx)).2
  have hq1 : ‖H h (((n : ℝ)+1)*x)‖ ≤ C/((n : ℝ)*x)^(2 : ℕ) := by
    refine ((hbound _ (show 0 < ((n : ℝ)+1)*x by positivity)).2).trans ?_
    apply div_le_div_of_nonneg_left hC (sq_pos_of_pos (mul_pos hnr hx))
    gcongr
    linarith
  rw [atom, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |Sieve.mertensM n| *
        (‖(Real.log ((n : ℝ)+1) : ℂ)*H h (((n : ℝ)+1)*x)‖ +
          ‖(Real.log (n : ℝ) : ℂ)*H h ((n : ℝ)*x)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg _)
    _ = |Sieve.mertensM n| *
        (Real.log ((n : ℝ)+1)*‖H h (((n : ℝ)+1)*x)‖ +
          Real.log (n : ℝ)*‖H h ((n : ℝ)*x)‖) := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hl1]
    _ ≤ |Sieve.mertensM n| *
        ((Real.log (n : ℝ)+1)*(C/((n : ℝ)*x)^(2 : ℕ)) + Real.log (n : ℝ)*(C/((n : ℝ)*x)^(2 : ℕ))) := by gcongr
    _ = _ := by rw [mul_pow]; ring

private theorem atom_hasSum (h : DeningerExpSchwartz) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n => atom h n x) (deningerMobiusDerivative h x) := by
  have hp : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range (N+1),
      ((-(((moebius n : ℤ) : ℝ)*Real.log (n : ℝ)) : ℝ) : ℂ) *
        H h ((n : ℝ)*x)) atTop (𝓝 (deningerMobiusDerivative h x)) :=
    (current_summable h hx).hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hh := hp.add (boundary_tendsto_zero h hx)
  simp only [add_zero] at hh
  have ht : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, atom h n x)
      atTop (𝓝 (deningerMobiusDerivative h x)) :=
    hh.congr fun N => (atom_finite h N x).symm
  exact (hasSum_iff_tendsto_nat_of_summable_norm (atom_summable h hx).norm).mpr ht

/-- The original, unregularized logarithmic current is globally admitted. -/
private theorem current_integrable (h : DeningerExpSchwartz) : IntegrableOn (deningerMobiusDerivative h) (Ioi 0) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm (atom_integrable h)
    (atom_norm_integrals_summable h)
  exact IntegrableOn.congr_fun hs (fun x hx => (atom_hasSum h hx).tsum_eq)
    measurableSet_Ioi

private theorem atom_integral (h : DeningerExpSchwartz) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), atom h n x) =
      ((Sieve.mertensM n * (Real.log ((n : ℝ)+1)/((n : ℝ)+1) -
        Real.log (n : ℝ)/(n : ℝ)) : ℝ) : ℂ) * deningerPullMass h := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [atom_zero h, Sieve.mertensM]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ)+1 := by positivity
  change (∫ x in Ioi (0 : ℝ), (Sieve.mertensM n : ℂ) *
    ((Real.log ((n : ℝ)+1) : ℂ) * H h (((n : ℝ)+1)*x) -
      (Real.log (n : ℝ) : ℂ) * H h ((n : ℝ)*x))) = _
  rw [integral_const_mul, integral_sub
    ((deningerLogPull_dilation_integrable h.property hn1).const_mul _) ((deningerLogPull_dilation_integrable h.property hnr).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_comp_mul_left_Ioi (H h) 0 hn1,
    integral_comp_mul_left_Ioi (H h) 0 hnr]
  simp only [mul_zero, deningerPullMass, Complex.real_smul, Complex.ofReal_inv]
  push_cast
  ring

private theorem atom_integral_hasSum (h : DeningerExpSchwartz) :
    HasSum (fun n : ℕ => ∫ x in Ioi (0 : ℝ), atom h n x)
      (deningerPullMass h) := by
  have hs : Summable (fun n : ℕ => ‖∫ x in Ioi (0 : ℝ), atom h n x‖) :=
    (atom_norm_integrals_summable h).of_nonneg_of_le
      (fun _ => norm_nonneg _) (fun _ => norm_integral_le_integral_norm _)
  have ht := Sieve.tendsto_moebiusLogHarmonicPartial_one.add pwGammaMertens_log_div_tendsto_zero
  simp only [add_zero] at ht
  have hc := ((Complex.continuous_ofReal.tendsto 1).comp ht).mul_const (deningerPullMass h)
  simp only [Complex.ofReal_one, one_mul] at hc
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).mpr
  refine hc.congr fun N => ?_
  simp only [atom_integral h, ← Finset.sum_mul,
    ← Complex.ofReal_sum, pwGammaMobiusLogAbel_scalar_finite]
  rfl

/-- The full critical current retains the original source mass. -/
private theorem current_integral (h : DeningerExpSchwartz) :
    (∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x) = deningerPullMass h := by
  have he : (∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x) =
      ∫ x in Ioi (0 : ℝ), ∑' n, atom h n x :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => (atom_hasSum h hx).tsum_eq.symm
  rw [he, ← integral_tsum_of_summable_integral_norm (atom_integrable h)
    (atom_norm_integrals_summable h)]
  exact (atom_integral_hasSum h).tsum_eq

/-- The complete native Euler current is integrable at the critical parameter. -/
theorem mobiusThetaNativeEulerCurrent_integrable (k : ℕ) (m : ℕ+) :
    IntegrableOn (mobiusThetaNativeEulerCurrent k m) (Ioi 0) := by
  let h : DeningerExpSchwartz :=
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩
  exact IntegrableOn.congr_fun (current_integrable h)
    (fun x hx => (deningerMobius_connection h.property hx).symm) measurableSet_Ioi

/-- The undamped native current retains the original Xi jet and Tate scale. -/
theorem mobiusThetaNativeEulerCurrent_integral (k : ℕ) (m : ℕ+) :
    (∫ x in Ioi (0 : ℝ), mobiusThetaNativeEulerCurrent k m x) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m) := by
  let h : DeningerExpSchwartz :=
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩
  calc
    _ = ∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => deningerMobius_connection h.property hx
    _ = deningerPullMass h := current_integral h
    _ = _ := mobiusThetaNativeCollarSource_pullMass k m

/-- The unchanged second collar's complete critical Euler current is integrable. -/
theorem mobiusThetaNativeSecondEulerCurrent_integrable (k : ℕ) (m : ℕ+) :
    IntegrableOn (mobiusThetaNativeSecondEulerCurrent k m) (Ioi 0) := by
  let h := DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)
  exact IntegrableOn.congr_fun (current_integrable h)
    (fun x hx => (deningerMobius_connection h.property hx).symm) measurableSet_Ioi

/-- The second critical current keeps its own source normalization. -/
theorem mobiusThetaNativeSecondEulerCurrent_integral (k : ℕ) (m : ℕ+) :
    (∫ x in Ioi (0 : ℝ), mobiusThetaNativeSecondEulerCurrent k m x) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC (I / 2) := by
  let h := DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)
  calc
    _ = ∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => deningerMobius_connection h.property hx
    _ = deningerPullMass h := current_integral h
    _ = _ := mobiusThetaNativeSecondCollarSource_pullMass k m


private theorem schwartz_lip (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖φ x - φ 0‖ ≤ (SchwartzMap.seminorm ℝ 0 1 φ) * |x| := by
  have hd : ∀ t : ℝ, ‖deriv φ t‖ ≤ SchwartzMap.seminorm ℝ 0 1 φ := by
    intro t
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using φ.le_seminorm' ℝ 0 1 t
  simpa only [sub_zero, Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t (_ : t ∈ (Set.univ : Set ℝ)) => φ.differentiableAt)
      (fun t _ => hd t) convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)

private theorem schwartz_norm (φ : SchwartzMap ℝ ℂ) (x : ℝ) :
    ‖φ x‖ ≤ SchwartzMap.seminorm ℝ 0 0 φ := by
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using φ.le_seminorm' ℝ 0 0 x

private abbrev preimage (h : DeningerExpSchwartz) := deningerMobiusPreimage h

private theorem preimage_moment (h : DeningerExpSchwartz) :
    IntegrableOn (fun y : ℝ => (y : ℂ) * preimage h y) (Ioi 0) := by
  simpa only [pow_one] using deningerMobiusPreimagePow_integrableOn h.property 1

private def testedPull (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (y : ℝ) : ℂ :=
  preimage h y * (φ (y / n) - φ 0)

private theorem testedPull_integrable (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    IntegrableOn (testedPull h φ n) (Ioi 0) := by
  apply (deningerMobiusPreimage_integrableOn h.property).mul_bdd
    (((φ.continuous.comp (continuous_id.div_const _)).sub continuous_const).aestronglyMeasurable)
  exact ae_of_all _ fun y => (norm_sub_le _ _).trans
    (add_le_add (schwartz_norm φ _) (schwartz_norm φ _))

private theorem testedPull_norm_integral_le (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ)
    {n : ℕ} (hn : 0 < n) :
    (∫ y in Ioi (0 : ℝ), ‖testedPull h φ n y‖) ≤
      (SchwartzMap.seminorm ℝ 0 1 φ / (n : ℝ)) * deningerCausalMass (preimage h) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm := deningerCausalMass_integrable (preimage_moment h)
  rw [deningerCausalMass, ← integral_const_mul]
  apply integral_mono_ae (testedPull_integrable h φ n).norm (hm.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hl := schwartz_lip φ (y / n)
  rw [abs_of_pos (div_pos hy hnR)] at hl
  calc
    ‖testedPull h φ n y‖ = ‖preimage h y‖ * ‖φ (y / n) - φ 0‖ := norm_mul _ _
    _ ≤ ‖preimage h y‖ * ((SchwartzMap.seminorm ℝ 0 1 φ) * (y / n)) :=
      mul_le_mul_of_nonneg_left hl (norm_nonneg _)
    _ = _ := by ring

private def testedEuler (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (vonMangoldt n : ℂ) * (preimage h ((n : ℝ)*x) * (φ x - φ 0))

private theorem testedEuler_eq_pull (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ)
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    testedEuler h φ n x = (vonMangoldt n : ℂ) * testedPull h φ n ((n : ℝ)*x) := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [testedEuler, testedPull, mul_div_cancel_left₀ x hnR]

private theorem testedEuler_integrable (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    IntegrableOn (testedEuler h φ n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hz : testedEuler h φ 0 = 0 := by
      funext x
      simp [testedEuler]
    rw [hz]
    exact integrable_zero ℝ ℂ _
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : IntegrableOn (fun x => testedPull h φ n ((n : ℝ)*x)) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (testedPull h φ n) 0 hnR).mpr
    simpa only [mul_zero] using testedPull_integrable h φ n
  exact (hp.const_mul (vonMangoldt n : ℂ)).congr
    (ae_of_all _ fun x => (testedEuler_eq_pull h φ hn x).symm)

private theorem testedEuler_norm_integral_le (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖testedEuler h φ n x‖) ≤
      ((SchwartzMap.seminorm ℝ 0 1 φ) * deningerCausalMass (preimage h)) *
        (vonMangoldt n / (n : ℝ)^(2 : ℕ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [testedEuler]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : (∫ x in Ioi (0 : ℝ), ‖testedEuler h φ n x‖) =
      (vonMangoldt n / (n : ℝ)) * (∫ y in Ioi (0 : ℝ), ‖testedPull h φ n y‖) := by
    simp_rw [testedEuler_eq_pull h φ hn, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    rw [integral_const_mul, integral_comp_mul_left_Ioi (fun y => ‖testedPull h φ n y‖) 0 hnR]
    simp only [mul_zero, smul_eq_mul]
    ring
  rw [he]
  calc
    _ ≤ (vonMangoldt n / (n : ℝ)) *
        ((SchwartzMap.seminorm ℝ 0 1 φ / (n : ℝ)) * deningerCausalMass (preimage h)) :=
      mul_le_mul_of_nonneg_left (testedPull_norm_integral_le h φ hn)
        (div_nonneg vonMangoldt_nonneg hnR.le)
    _ = _ := by ring

private theorem testedEuler_norm_integrals_summable (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖testedEuler h φ n x‖) :=
  (deningerVonMangoldt_summable_div_sq.mul_left _).of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _) (testedEuler_norm_integral_le h φ)

private theorem testedEuler_integral (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), testedEuler h φ n x) = deningerCausalTerm (preimage h) φ n := by
  have he := deningerCausalTerm_eq (schwartz_lip φ) φ.continuous
    (deningerMobiusPreimage_integrableOn h.property) (preimage_moment h) n
  rw [deningerMobiusPreimage_mass_eq_zero h.property, zero_mul, mul_zero, add_zero] at he
  rw [he]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [testedEuler, deningerCausalRenorm]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [testedEuler_eq_pull h φ hn]
  rw [integral_const_mul, integral_comp_mul_left_Ioi (testedPull h φ n) 0 hnR]
  simp only [mul_zero, Complex.real_smul, deningerCausalRenorm, testedPull, Complex.ofReal_div]
  push_cast
  ring

private theorem critical_contact (h : DeningerExpSchwartz) (φ : SchwartzMap ℝ ℂ) :
    (∑' n : ℕ, deningerCausalTerm (preimage h) φ n) =
      (∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x * φ x) - deningerPullMass h * φ 0 := by
  have hφ : IntegrableOn (fun x => deningerMobiusDerivative h x * φ x) (Ioi 0) :=
    (current_integrable h).mul_bdd φ.continuous.aestronglyMeasurable
      (ae_of_all _ (schwartz_norm φ))
  calc
    _ = ∫ x in Ioi (0 : ℝ), ∑' n : ℕ, testedEuler h φ n x := by
      rw [← integral_tsum_of_summable_integral_norm (testedEuler_integrable h φ)
        (testedEuler_norm_integrals_summable h φ)]
      exact tsum_congr fun n => (testedEuler_integral h φ n).symm
    _ = ∫ x in Ioi (0 : ℝ), deningerMobiusDerivative h x * (φ x - φ 0) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [testedEuler, ← mul_assoc]
      rw [tsum_mul_right]
      exact congrArg (fun z : ℂ => z * (φ x - φ 0)) (deningerMobius_connection h.property hx)
    _ = _ := by
      simp_rw [mul_sub]
      rw [integral_sub hφ ((current_integrable h).mul_const _), integral_mul_const,
        current_integral h]

/-- The original causal reader equals the complete native current with its exact origin contact. -/
theorem mobiusThetaNativeEulerCurrent_pairing_contact (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    (∑' n : ℕ, deningerCausalTerm
      (deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)) φ n) =
      (∫ x in Ioi (0 : ℝ), mobiusThetaNativeEulerCurrent k m x * φ x) -
        ((m : ℂ)⁻¹ * iteratedDeriv k XiC (mobiusThetaNativeMassParameter m)) * φ 0 := by
  let h : DeningerExpSchwartz :=
    ⟨_, mobiusThetaNativeCollarSource_mem_deningerExpSchwartz k m⟩
  have he := critical_contact h φ
  rw [show deningerPullMass h = _ from mobiusThetaNativeCollarSource_pullMass k m] at he
  refine he.trans ?_
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx =>
    congrArg (fun z : ℂ => z * φ x) (deningerMobius_connection h.property hx).symm

/-- The unchanged second collar carries its own Xi-jet origin contact. -/
theorem mobiusThetaNativeSecondEulerCurrent_pairing_contact (k : ℕ) (m : ℕ+) (φ : SchwartzMap ℝ ℂ) :
    (∑' n : ℕ, deningerCausalTerm
      (deningerMobiusPreimage (DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m))) φ n) =
      (∫ x in Ioi (0 : ℝ), mobiusThetaNativeSecondEulerCurrent k m x * φ x) -
        ((m : ℂ)⁻¹ * iteratedDeriv k XiC (I / 2)) * φ 0 := by
  let h := DeningerMeyerSource.toSource (mobiusThetaNativeSecondCollarSource k m)
  have he := critical_contact h φ
  rw [mobiusThetaNativeSecondCollarSource_pullMass] at he
  refine he.trans ?_
  congr 1
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx =>
    congrArg (fun z : ℂ => z * φ x) (deningerMobius_connection h.property hx).symm


end RHTower
