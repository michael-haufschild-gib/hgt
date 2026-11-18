import GaloisForLFunctions.HTGeometry.FourierDecayFromDerivative
import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant
import GaloisForLFunctions.RHTower.FourierPlancherelIntegral

/-!
# Fractional Fourier regularity from square increments

A translation of length 1/(4Y) controls the entire Fourier annulus
Y ≤ |ξ| ≤ 2Y. Summing the annuli gains every frequency power below one.
-/

noncomputable section
open MeasureTheory Set Filter Topology FourierTransform
open scoped FourierTransform
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry

private theorem annulus_symbol_ge_one {Y ξ : ℝ} (hY : 0 < Y)
    (hlo : Y ≤ |ξ|) (hhi : |ξ| ≤ 2*Y) :
    1 ≤ ‖differenceSymbol (1/(4*Y)) ξ‖^2 := by
  have hd : 0 < 4*Y := by positivity
  have hr : 1/(4*Y)*|ξ|=|ξ|/(4*Y) := by ring
  have hlo' : 1/4 ≤ |ξ|/(4*Y) := (le_div_iff₀ hd).2 (by linarith only [hlo])
  have hhi' : |ξ|/(4*Y) ≤ 1/2 := (div_le_iff₀ hd).2 (by linarith only [hhi])
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith only [Real.pi_pos] : -(Real.pi/2) ≤ Real.pi/4)
    (show Real.pi*(1/(4*Y)*|ξ|) ≤ Real.pi/2 by rw [hr]; linarith only [mul_le_mul_of_nonneg_left hhi' Real.pi_pos.le])
    (show Real.pi/4 ≤ Real.pi*(1/(4*Y)*|ξ|) by rw [hr]; linarith only [mul_le_mul_of_nonneg_left hlo' Real.pi_pos.le])
  rw [Real.sin_pi_div_four] at hs
  have h1 : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
  have hsin : 1/2 ≤ Real.sin (Real.pi*(1/(4*Y)*|ξ|)) := by linarith only [h1,hs]
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hsin 2
  have habs : Real.sin (Real.pi*(1/(4*Y)*ξ))^2 = Real.sin (Real.pi*(1/(4*Y)*|ξ|))^2 := by
    rcases le_or_gt 0 ξ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h,mul_neg,mul_neg,Real.sin_neg,neg_sq]
  rw [normSq_differenceSymbol,habs]
  linarith only [hpow]

/-- An O(h) squared translation modulus makes every squared Fourier weight
|ξ|ˢ integrable for 0 ≤ s < 1. -/
theorem integrable_fractional_fourier_energy_of_square_increments {f : ℝ → ℂ}
    (hi : Integrable f) (h2 : MemLp f 2) {C : ℝ}
    (hinc : ∀ h : ℝ, 0 < h → h ≤ 1 → (∫ x, ‖f x-f (x+h)‖^2) ≤ C*h)
    {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    Integrable fun ξ : ℝ => |ξ|^s*‖𝓕 f ξ‖^2 := by
  let w := fun ξ : ℝ => |ξ|^s*‖𝓕 f ξ‖^2
  let S := fun n : ℕ => {ξ : ℝ | (2:ℝ)^n ≤ |ξ| ∧ |ξ| ≤ 2*2^n}
  have hm (n : ℕ) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const measurable_id.abs).inter
      (measurableSet_le measurable_id.abs measurable_const)
  have hW : Measurable w := (measurable_id.abs.pow_const s).mul
    ((RHTower.continuous_fourier_of_integrable hi).norm.pow 2).measurable
  have hw (ξ : ℝ) : 0 ≤ w ξ := mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (sq_nonneg _)
  let q := (2:ℝ)^s/2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    apply (div_lt_one (by norm_num : (0:ℝ)<2)).2
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hs1
  have bounds (n : ℕ) : IntegrableOn w (S n) ∧
      (∫ ξ in S n, ‖w ξ‖) ≤ ((2:ℝ)^s*C/4)*q^n := by
    let Y := (2:ℝ)^n
    let h := 1/(4*Y)
    let g := fun x : ℝ => f x-f (x+h)
    have hY : 1 ≤ Y := one_le_pow₀ (by norm_num)
    have hY0 := zero_lt_one.trans_le hY
    have hh : 0 < h := by dsimp only [h]; positivity
    have hh1 : h ≤ 1 := (div_le_one (by positivity : 0 < 4*Y)).2 (by linarith)
    have hiG : Integrable g := hi.sub (hi.comp_add_right h)
    have h2G : MemLp g 2 := h2.sub (h2.comp_measurePreserving (measurePreserving_add_right volume h))
    have hiQ := (RHTower.integrable_norm_sq_fourier hiG h2G).const_mul ((2*Y)^s)
    have hpoint (ξ : ℝ) (hξ : ξ ∈ S n) : ‖w ξ‖ ≤ (2*Y)^s*‖𝓕 g ξ‖^2 := by
      have hz := annulus_symbol_ge_one hY0 hξ.1 hξ.2
      have he : (𝓕 g) ξ = differenceSymbol h ξ*(𝓕 f) ξ := fourier_sub_translate f hi h ξ
      rw [Real.norm_eq_abs,abs_of_nonneg (hw _),he,norm_mul,mul_pow]
      apply mul_le_mul (Real.rpow_le_rpow (abs_nonneg _) hξ.2 hs) _ (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)
      exact le_mul_of_one_le_left (sq_nonneg _) hz
    have hiS := hiQ.integrableOn.mono' hW.aestronglyMeasurable
      ((ae_restrict_iff' (hm n)).2 (Eventually.of_forall hpoint))
    refine ⟨hiS,?_⟩
    calc _ ≤ ∫ ξ in S n, (2*Y)^s*‖𝓕 g ξ‖^2 := integral_mono_ae hiS.norm hiQ.integrableOn
               ((ae_restrict_iff' (hm n)).2 (Eventually.of_forall hpoint))
      _ ≤ ∫ ξ, (2*Y)^s*‖𝓕 g ξ‖^2 := setIntegral_le_integral hiQ (Eventually.of_forall fun _ => by positivity)
      _ = (2*Y)^s*(∫ x, ‖g x‖^2) := by rw [integral_const_mul,RHTower.integral_norm_sq_fourier_eq hiG h2G]
      _ ≤ (2*Y)^s*(C*h) := mul_le_mul_of_nonneg_left (hinc h hh hh1) (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
             have hr : Y^s=((2:ℝ)^s)^n := by
               dsimp only [Y]
               rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
             rw [Real.mul_rpow (by norm_num) hY0.le,hr]
             dsimp only [h,Y,q]
             rw [div_pow]; ring
  have hU := integrableOn_iUnion_of_summable_integral_norm (fun n => (bounds n).1)
    (Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => (bounds n).2)
      ((summable_geometric_of_lt_one hq hq1).mul_left ((2:ℝ)^s*C/4)))
  let B := {ξ : ℝ | |ξ| ≤ 1}
  have hB : MeasurableSet B := measurableSet_le measurable_id.abs measurable_const
  have hiB : IntegrableOn w B := (RHTower.integrable_norm_sq_fourier hi h2).integrableOn.mono'
    hW.aestronglyMeasurable ((ae_restrict_iff' hB).2 (Eventually.of_forall fun ξ hξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hw _)]
      exact mul_le_of_le_one_left (sq_nonneg _) (Real.rpow_le_one (abs_nonneg _) hξ hs)))
  apply integrableOn_univ.1
  apply (hiB.union hU).mono_set
  intro ξ _
  by_cases hξ : |ξ| ≤ 1
  · exact Or.inl hξ
  obtain ⟨n,hl,hr⟩ := exists_nat_pow_near (le_of_not_ge hξ) (by norm_num : (1:ℝ)<2)
  exact Or.inr (mem_iUnion.2 ⟨n,hl,hr.le.trans_eq (pow_succ' (2:ℝ) n)⟩)

#print axioms integrable_fractional_fourier_energy_of_square_increments
end GaloisForLFunctions.ExclusionOfTheCriticalState
