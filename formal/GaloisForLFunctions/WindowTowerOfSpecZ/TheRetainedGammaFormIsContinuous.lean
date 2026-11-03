import GaloisForLFunctions.WindowTowerOfSpecZ.TheRetainedGammaLowerFormHasANegativeDirection
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit

/-!
# Continuity of the retained Gamma form on a fixed window

Pointwise convergence, a common unit support, and uniform size and Lipschitz
bounds preserve every term of the retained Gamma form. The Lipschitz bound
controls the logarithmic lag singularity by an integrable linear majorant.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ

private theorem unit_family_compact {Fs : ℕ → ℝ → ℝ}
    (hs : ∀ n {x}, x ∉ Icc (-(1/2 : ℝ)) (1/2) → Fs n x = 0) (n : ℕ) :
    HasCompactSupport (Fs n) :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => hs n hx)

section
variable {F : ℝ → ℝ} {Fs : ℕ → ℝ → ℝ} {K : ℝ}
  (hFs : ∀ n, ContDiff ℝ 2 (Fs n))
  (hs : ∀ n {x}, x ∉ Icc (-(1/2 : ℝ)) (1/2) → Fs n x = 0)
  (hb : ∀ n x, |Fs n x| ≤ 1)
  (hL : ∀ n x y, |Fs n x - Fs n y| ≤ K * |x-y|)
  (hlim : ∀ x, Tendsto (fun n => Fs n x) atTop (𝓝 (F x)))
include hFs hs hb hL hlim

private theorem unit_family_autocorr_tendsto (t : ℝ) :
    Tendsto (fun n => autocorr (Fs n) t) atTop
      (𝓝 (autocorr F t)) := by
  have hmajorant : Integrable (fun x : ℝ =>
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun _ => (1 : ℝ)) x) :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  change Tendsto (fun n => ∫ x, Fs n x * Fs n (x+t)) atTop
    (𝓝 (∫ x, F x * F (x+t)))
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hmajorant (fun n => ?_) ?_
  · exact ((hFs n).continuous.mul
      ((hFs n).continuous.comp (continuous_add_const t))).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
      · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul (hb n x)
          (hb n (x+t)) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      · rw [indicator_of_notMem hx, hs n hx, zero_mul, norm_zero]
  · exact Eventually.of_forall fun x =>
      (hlim x).mul (hlim (x+t))

theorem unitWindow_square_mass_tendsto :
    Tendsto (fun n => ∫ x, Fs n x ^ 2) atTop
      (𝓝 (∫ x, F x ^ 2)) := by
  simpa only [autocorr, add_zero, pow_two] using unit_family_autocorr_tendsto hFs hs hb hL hlim 0

/-- Uniform quadratic control of the lag deficit pays its logarithmic singularity. -/
private theorem unit_family_deficit_bound (n : ℕ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    0 ≤ (∫ x, Fs n x ^ 2) - autocorr (Fs n) t ∧
      (∫ x, Fs n x ^ 2) - autocorr (Fs n) t ≤ K ^ 2 * t ^ 2 := by
  let B : ℝ → ℝ := (Icc (-(3/2 : ℝ)) (1/2)).indicator (fun _ => K ^ 2 * t ^ 2)
  have hBi : Integrable B :=
    continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hB (x : ℝ) : ‖(Fs n x - Fs n (x+t)) ^ 2‖ ≤ B x := by
    dsimp only [B]
    by_cases hx : x ∈ Icc (-(3/2 : ℝ)) (1/2)
    · rw [indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h := hL n x (x+t)
      rw [show x-(x+t) = -t by ring, abs_neg, abs_of_pos ht.1] at h
      have hs := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs, mul_pow] at hs
      norm_num at hs
      exact hs
    · have hz : Fs n x = 0 ∧ Fs n (x+t) = 0 := by
        by_cases hl : x < -(3/2 : ℝ)
        · constructor
          · apply hs n
            intro hi
            linarith only [hl, hi.1]
          · apply hs n
            intro hi
            linarith only [hl, hi.1, ht.2]
        · have hr : (1/2 : ℝ) < x := not_le.mp (fun h => hx ⟨not_lt.mp hl, h⟩)
          constructor
          · apply hs n
            intro hi
            linarith only [hr, hi.2]
          · apply hs n
            intro hi
            linarith only [hr, hi.2, ht.1]
      rw [indicator_of_notMem hx, hz.1, hz.2, sub_self]
      norm_num
  have hBv : (∫ x, B x) = 2 * K ^ 2 * t ^ 2 := by
    dsimp only [B]
    rw [integral_indicator measurableSet_Icc, setIntegral_const]
    norm_num <;> ring
  have hnn : 0 ≤ ∫ x, (Fs n x - Fs n (x+t)) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hb := norm_integral_le_of_norm_le hBi (Eventually.of_forall hB)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, hBv] at hb
  have he := integral_sub_shift_sq (unit_family_compact hs n)
    (hFs n).continuous t
  have hzero : autocorr (Fs n) 0 = ∫ x, Fs n x ^ 2 := by
    simp only [autocorr, add_zero, pow_two]
  rw [hzero] at he
  constructor <;> linarith only [he, hnn, hb]

private theorem unit_family_logarithmic_tendsto :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) 1,
      ((∫ x, Fs n x ^ 2) - autocorr (Fs n) t) / t) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        ((∫ x, F x ^ 2) - autocorr F t) / t)) := by
  have hmajorant : IntegrableOn (fun t : ℝ => K ^ 2 * t) (Ioc (0 : ℝ) 1) :=
    (continuous_const.mul continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hmajorant (fun n => ?_) ?_
  · have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr
      (hFs n) (unit_family_compact hs n)
    exact ((continuous_const.sub hc).measurable.div measurable_id).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨h0, h1⟩ := unit_family_deficit_bound hFs hs hb hL hlim n ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h0 ht.1.le)]
    apply (div_le_iff₀ ht.1).mpr
    nlinarith only [h1]
  · exact Eventually.of_forall fun t =>
      ((unitWindow_square_mass_tendsto hFs hs hb hL hlim).sub
        (unit_family_autocorr_tendsto hFs hs hb hL hlim t)).div_const t

private theorem unit_family_first_moment_tendsto :
    Tendsto (fun n => ∫ t in Ioc (0 : ℝ) 1,
      t * ((∫ x, Fs n x ^ 2) - autocorr (Fs n) t)) atTop
      (𝓝 (∫ t in Ioc (0 : ℝ) 1,
        t * ((∫ x, F x ^ 2) - autocorr F t))) := by
  have hmajorant : IntegrableOn (fun _ : ℝ => (K ^ 2 : ℝ)) (Ioc (0 : ℝ) 1) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hmajorant (fun n => ?_) ?_
  · have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr
      (hFs n) (unit_family_compact hs n)
    exact (continuous_id.mul (continuous_const.sub hc)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨h0, h1⟩ := unit_family_deficit_bound hFs hs hb hL hlim n ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1.le h0)]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht.1, ht.2]
    have hd : (∫ x, Fs n x ^ 2) - autocorr (Fs n) t ≤ K ^ 2 := by
      nlinarith only [h1, mul_le_mul_of_nonneg_left ht2 (sq_nonneg K)]
    simpa only [one_mul] using mul_le_mul ht.2 hd h0 (by norm_num : (0 : ℝ) ≤ 1)
  · exact Eventually.of_forall fun t =>
      ((unitWindow_square_mass_tendsto hFs hs hb hL hlim).sub
        (unit_family_autocorr_tendsto hFs hs hb hL hlim t)).const_mul t

private theorem unit_family_weight_tendsto (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n => ∫ x, Fs n x * g x) atTop
      (𝓝 (∫ x, F x * g x)) := by
  have hmajorant : Integrable (fun x : ℝ =>
      (Icc (-(1/2 : ℝ)) (1/2)).indicator (fun x => |g x|) x) :=
    hg.abs.integrableOn_Icc.integrable_indicator measurableSet_Icc
  refine tendsto_integral_of_dominated_convergence _ (fun n => ?_) hmajorant (fun n => ?_) ?_
  · exact ((hFs n).continuous.mul hg).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by
      by_cases hx : x ∈ Icc (-(1/2 : ℝ)) (1/2)
      · rw [indicator_of_mem hx, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (hb n x) (abs_nonneg (g x))
      · rw [indicator_of_notMem hx, hs n hx, zero_mul, norm_zero]
  · exact Eventually.of_forall fun x => (hlim x).mul_const (g x)

/-- Every term of the retained lower form survives support-preserving smoothing. -/
theorem retainedOddGammaLowerForm_tendsto_of_unit_window :
    Tendsto (fun n => retainedOddGammaLowerForm (Fs n)) atTop
      (𝓝 (retainedOddGammaLowerForm F)) := by
  have hm : Tendsto (fun n => ∫ x, x * Fs n x) atTop
      (𝓝 (∫ x, x * F x)) := by
    simpa only [mul_comm] using unit_family_weight_tendsto hFs hs hb hL hlim (fun x => x) continuous_id
  have hp : Tendsto (fun n => sinhPairing (Fs n)) atTop
      (𝓝 (sinhPairing F)) :=
    unit_family_weight_tendsto hFs hs hb hL hlim (fun x => 2 * Real.sinh (x/2)) (by fun_prop)
  have harch := (unit_family_logarithmic_tendsto hFs hs hb hL hlim).sub
    ((unitWindow_square_mass_tendsto hFs hs hb hL hlim).const_mul
      (Real.eulerMascheroniConstant + Real.log Real.pi + Real.log 2))
  have hfirst := harch.sub ((unit_family_first_moment_tendsto hFs hs hb hL hlim).div_const 24)
  have hposition := hfirst.sub ((hm.pow 2).div_const 16)
  have hpole := hposition.sub ((hp.pow 2).div_const 2)
  exact hpole.sub
    ((unit_family_autocorr_tendsto hFs hs hb hL hlim (Real.log 2)).const_mul (2 * (Real.log 2 / Real.sqrt 2)))


end
end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedOddGammaLowerForm_tendsto_of_unit_window

