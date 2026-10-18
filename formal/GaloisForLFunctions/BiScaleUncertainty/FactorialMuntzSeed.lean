import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarCausalSource
import GaloisForLFunctions.HTGeometry.BoundedVariationNormAlgebra
import GaloisForLFunctions.RHTower.CCMBVMuntzSummation
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! An explicit zero-mean bounded-variation seed for the factorial ramp. -/

open MeasureTheory Set
open scoped BigOperators
namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
noncomputable section
set_option autoImplicit false

private def positiveRamp (ε a : ℝ) (t : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator (fun u => clampedRamp ε (u/a)) t

private theorem positiveRamp_support {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
    (t : ℝ) (ht : t ∉ Ioc (0 : ℝ) (a*(1+ε))) : positiveRamp ε a t = 0 := by
  by_cases hp : 0 < t
  · simp only [positiveRamp, indicator_apply, mem_Ioi, if_pos hp]
    apply clampedRamp_eq_zero hε
    apply (le_div_iff₀ ha).2
    have : a*(1+ε) < t := by simpa [hp] using ht
    nlinarith
  · simp only [positiveRamp, indicator_apply, mem_Ioi, if_neg hp]

private theorem positiveRamp_measurable (ε a : ℝ) : Measurable (positiveRamp ε a) :=
  (((continuous_clampedRamp ε).comp (continuous_id.div_const a)).measurable).indicator
    measurableSet_Ioi

private theorem positiveRamp_integrable {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) :
    Integrable (positiveRamp ε a) := by
  have he : positiveRamp ε a = (Ioc (0 : ℝ) (a*(1+ε))).indicator
      (fun u => clampedRamp ε (u/a)) := by
    funext t
    by_cases ht : t ∈ Ioc (0 : ℝ) (a*(1+ε))
    · rw [indicator_of_mem ht]
      simp only [positiveRamp, indicator_apply, mem_Ioi, if_pos ht.1]
    · rw [positiveRamp_support hε ha t ht, indicator_of_notMem ht]
  rw [he]
  exact ((((continuous_clampedRamp ε).comp (continuous_id.div_const a)).integrableOn_Icc).mono_set
    Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc

private theorem integral_positiveRamp {ε a : ℝ} (ha : 0 < a) :
    (∫ t : ℝ, positiveRamp ε a t) = a*(∫ t : ℝ, positiveRamp ε 1 t) := by
  have he : positiveRamp ε a = fun t => positiveRamp ε 1 (a⁻¹*t) := by
    funext t
    have hp : 0 < a⁻¹*t ↔ 0 < t := by
      rw [mul_pos_iff_of_pos_left (inv_pos.mpr ha)]
    simp only [positiveRamp, indicator_apply, mem_Ioi, hp, div_one]
    congr 2
    ring
  rw [he, Measure.integral_comp_inv_mul_left, abs_of_pos ha, smul_eq_mul]

private def leftStep (t : ℝ) : ℝ := if t ≤ 0 then 1 else 0

private theorem positiveRamp_eq {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a) (t : ℝ) :
    positiveRamp ε a t = clampedRamp ε (t/a)-leftStep t := by
  by_cases ht : t ≤ 0
  · rw [positiveRamp, indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht), leftStep, if_pos ht,
      clampedRamp_eq_one hε (le_trans (div_nonpos_of_nonpos_of_nonneg ht ha.le) (by norm_num))]
    ring
  · simp only [positiveRamp, indicator_apply, mem_Ioi, if_pos (lt_of_not_ge ht), leftStep, if_neg ht, sub_zero]

private theorem leftStep_antitone : Antitone leftStep := by
  intro a b hab
  unfold leftStep
  split_ifs <;> norm_num
  linarith

private theorem antitone_partition_le_one {f : ℝ → ℝ} (hf : Antitone f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f (u (i+1))-f (u i)‖) ≤ 1 := by
  calc
    _ = -(∑ i ∈ Finset.range n, (f (u (i+1))-f (u i))) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hf (hu (Nat.le_succ i))))]
    _ = f (u 0)-f (u n) := by rw [Finset.sum_range_sub (fun i => f (u i))]; ring
    _ ≤ 1 := by linarith [h0 (u n), h1 (u 0)]

/-- A concrete arithmetic seed; the common collar and dyadic coefficients
cancel its integral exactly. -/
def factorialMuntzSeed (n : ℕ) (t : ℝ) : ℝ :=
  positiveRamp (sourceFactorialCollar (n+1)) (4*((n+1 : ℕ) : ℝ)) t-
    4*positiveRamp (sourceFactorialCollar (n+1)) (2*((n+1 : ℕ) : ℝ)) t+
    4*positiveRamp (sourceFactorialCollar (n+1)) ((n+1 : ℕ) : ℝ) t

def factorialMuntzSupport (n : ℕ) : ℝ :=
  4*((n+1 : ℕ) : ℝ)*(1+sourceFactorialCollar (n+1))

theorem factorialMuntzSeed_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    factorialMuntzSeed n t =
      clampedRamp (sourceFactorialCollar (n+1)) (t/(4*((n+1 : ℕ) : ℝ)))-
        4*clampedRamp (sourceFactorialCollar (n+1)) (t/(2*((n+1 : ℕ) : ℝ)))+
        4*clampedRamp (sourceFactorialCollar (n+1)) (t/((n+1 : ℕ) : ℝ)) := by
  simp only [factorialMuntzSeed, positiveRamp, indicator_apply, mem_Ioi, if_pos ht]

theorem factorialMuntzSeed_measurable (n : ℕ) : Measurable (factorialMuntzSeed n) :=
  ((positiveRamp_measurable _ _).sub ((positiveRamp_measurable _ _).const_mul 4)).add
    ((positiveRamp_measurable _ _).const_mul 4)

theorem factorialMuntzSeed_support (n : ℕ) (t : ℝ)
    (ht : t ∉ Ioc (0 : ℝ) (factorialMuntzSupport n)) : factorialMuntzSeed n t = 0 := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have hn : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  have h2 : t ∉ Ioc (0 : ℝ) (2*((n+1 : ℕ) : ℝ)*(1+sourceFactorialCollar (n+1))) := by
    intro h
    apply ht
    refine ⟨h.1, h.2.trans ?_⟩
    unfold factorialMuntzSupport
    nlinarith
  have h1 : t ∉ Ioc (0 : ℝ) (((n+1 : ℕ) : ℝ)*(1+sourceFactorialCollar (n+1))) := by
    intro h
    apply h2
    exact ⟨h.1, h.2.trans (by nlinarith)⟩
  unfold factorialMuntzSeed
  rw [positiveRamp_support hε (by positivity) t ht,
    positiveRamp_support hε (by positivity) t h2, positiveRamp_support hε hn t h1]
  ring

theorem factorialMuntzSeed_abs_le (n : ℕ) (t : ℝ) : |factorialMuntzSeed n t| ≤ 9 := by
  have hb (a : ℝ) : 0 ≤ positiveRamp (sourceFactorialCollar (n+1)) a t ∧
      positiveRamp (sourceFactorialCollar (n+1)) a t ≤ 1 := by
    unfold positiveRamp
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
      exact ⟨clampedRamp_nonneg _ _, clampedRamp_le_one _ _⟩
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht)]
      norm_num
  rw [abs_le]
  have h4 := hb (4*((n+1 : ℕ) : ℝ))
  have h2 := hb (2*((n+1 : ℕ) : ℝ))
  have h1 := hb ((n+1 : ℕ) : ℝ)
  unfold factorialMuntzSeed
  constructor <;> linarith

theorem factorialMuntzSeed_integrable (n : ℕ) : Integrable (factorialMuntzSeed n) := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  exact ((positiveRamp_integrable hε (by positivity)).sub
    ((positiveRamp_integrable hε (by positivity)).const_mul 4)).add
    ((positiveRamp_integrable hε (by positivity)).const_mul 4)

theorem factorialMuntzSeed_integral (n : ℕ) : (∫ t : ℝ, factorialMuntzSeed n t) = 0 := by
  have hε := sourceFactorialCollar_pos (N := n+1) (by omega)
  have h4 : Integrable (positiveRamp (sourceFactorialCollar (n+1)) (4*((n+1 : ℕ) : ℝ))) :=
    positiveRamp_integrable hε (by positivity)
  have h2 : Integrable (positiveRamp (sourceFactorialCollar (n+1)) (2*((n+1 : ℕ) : ℝ))) :=
    positiveRamp_integrable hε (by positivity)
  have h1 : Integrable (positiveRamp (sourceFactorialCollar (n+1)) ((n+1 : ℕ) : ℝ)) :=
    positiveRamp_integrable hε (by positivity)
  have ha := integral_add (h4.sub (h2.const_mul 4)) (h1.const_mul 4)
  simp only [Pi.sub_apply] at ha
  unfold factorialMuntzSeed
  rw [ha, integral_sub h4 (h2.const_mul 4)]
  simp only [integral_const_mul]
  rw [integral_positiveRamp (by positivity : (0 : ℝ) < 4*((n+1 : ℕ) : ℝ)),
    integral_positiveRamp (by positivity : (0 : ℝ) < 2*((n+1 : ℕ) : ℝ)),
    integral_positiveRamp (by positivity : (0 : ℝ) < ((n+1 : ℕ) : ℝ))]
  ring

theorem factorialMuntzSeed_variation_le (n : ℕ) :
    eVariationOn (factorialMuntzSeed n) univ ≤ 10 := by
  apply le_trans (GaloisForLFunctions.HTGeometry.eVariationOn_le_of_norm_partitions ?_)
    (by norm_num : ENNReal.ofReal (10 : ℝ) ≤ 10)
  intro m u hu _
  let ε := sourceFactorialCollar (n+1)
  let N : ℝ := ((n+1 : ℕ) : ℝ)
  have hε : 0 < ε := sourceFactorialCollar_pos (by omega)
  have hN : 0 < N := by dsimp [N]; positivity
  let f := fun a t : ℝ => clampedRamp ε (t/a)
  have hb (a : ℝ) (ha : 0 < a) :
      (∑ i ∈ Finset.range m, ‖f a (u (i+1))-f a (u i)‖) ≤ 1 :=
    antitone_partition_le_one
      (fun _ _ h => antitone_clampedRamp hε (div_le_div_of_nonneg_right h ha.le))
      (fun _ => clampedRamp_nonneg _ _) (fun _ => clampedRamp_le_one _ _) u hu m
  have hs : (∑ i ∈ Finset.range m, ‖leftStep (u (i+1))-leftStep (u i)‖) ≤ 1 :=
    antitone_partition_le_one leftStep_antitone
      (by intro t; unfold leftStep; split_ifs <;> norm_num)
      (by intro t; unfold leftStep; split_ifs <;> norm_num) u hu m
  have he (t : ℝ) : factorialMuntzSeed n t = f (4*N) t-4*f (2*N) t+4*f N t-leftStep t := by
    unfold factorialMuntzSeed
    rw [positiveRamp_eq hε (by positivity), positiveRamp_eq hε (by positivity),
      positiveRamp_eq hε hN]
    dsimp [f, N, ε]
    ring
  calc
    _ ≤ ∑ i ∈ Finset.range m, (‖f (4*N) (u (i+1))-f (4*N) (u i)‖+
        4*‖f (2*N) (u (i+1))-f (2*N) (u i)‖+
        4*‖f N (u (i+1))-f N (u i)‖+‖leftStep (u (i+1))-leftStep (u i)‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [he, he]
      have hid : (f (4*N) (u (i+1))-4*f (2*N) (u (i+1))+4*f N (u (i+1))-leftStep (u (i+1)))-
          (f (4*N) (u i)-4*f (2*N) (u i)+4*f N (u i)-leftStep (u i)) =
          ((f (4*N) (u (i+1))-f (4*N) (u i))-4*(f (2*N) (u (i+1))-f (2*N) (u i))+
          4*(f N (u (i+1))-f N (u i)))-(leftStep (u (i+1))-leftStep (u i)) := by ring
      rw [hid]
      refine (norm_sub_le _ _).trans ?_
      gcongr
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Real.norm_ofNat]
      gcongr
      simpa only [norm_mul, Real.norm_ofNat] using norm_sub_le
        (f (4*N) (u (i+1))-f (4*N) (u i)) (4*(f (2*N) (u (i+1))-f (2*N) (u i)))
    _ ≤ 10 := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      linarith [hb (4*N) (by positivity), hb (2*N) (by positivity), hb N hN]

theorem factorialMuntzSeed_boundedVariation (n : ℕ) :
    BoundedVariationOn (factorialMuntzSeed n) univ :=
  ne_top_of_le_ne_top (by norm_num) (factorialMuntzSeed_variation_le n)

theorem factorialMuntzSeed_intervalIntegral (n : ℕ) :
    (∫ t in (0 : ℝ)..factorialMuntzSupport n, factorialMuntzSeed n t) = 0 := by
  have hL : 0 ≤ factorialMuntzSupport n := by
    unfold factorialMuntzSupport
    have := (sourceFactorialCollar_pos (N := n+1) (by omega)).le
    positivity
  rw [intervalIntegral.integral_of_le hL,
    setIntegral_eq_integral_of_forall_compl_eq_zero (factorialMuntzSeed_support n),
    factorialMuntzSeed_integral]

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
