import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalAngularForcing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Width-one cusp characters and absolutely convergent mean interchange.

This leaf proves the displayed source or cusp identity. Causal continuation,
left-QNM evaluation and Hawking-clock extinction remain separate obligations.
-/

open Complex MeasureTheory Set Filter Topology
namespace RHTower.D4BMCuspProjection
noncomputable section

/-- The width-one average on the original cusp strip. -/
def mean (f : ℝ → ℂ) : ℂ := ∫ x in Ioc (-1/2:ℝ) (1/2), f x

/-- Integer horizontal character in the original cusp coordinate. -/
def character (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(x:ℂ))

theorem character_continuous (k : ℤ) : Continuous (character k) := by
  unfold character
  fun_prop

theorem character_norm (k : ℤ) (x : ℝ) : ‖character k x‖ = 1 := by
  simp [character,Complex.norm_exp]

theorem character_mul (k l : ℤ) (x : ℝ) :
    character k x*character l x = character (k+l) x := by
  rw [character,character,character,← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mean_character (k : ℤ) : mean (character k) = if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · subst k
    norm_num [mean,character]
  rw [if_neg hk]
  have hc : 2*(Real.pi:ℂ)*Complex.I*(k:ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr
      Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hk)
  change (∫ x in Ioc (-1/2:ℝ) (1/2), Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*(x:ℂ)))=0
  rw [← intervalIntegral.integral_of_le (by norm_num : (-1/2:ℝ) ≤ 1/2),
    integral_exp_mul_complex hc]
  have he : Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*((1/2:ℝ):ℂ)) =
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*((-1/2:ℝ):ℂ)) := by
    have ha : 2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*((1/2:ℝ):ℂ) =
      (k:ℂ)*(2*(Real.pi:ℂ)*Complex.I)+
        2*(Real.pi:ℂ)*Complex.I*(k:ℂ)*((-1/2:ℝ):ℂ) := by push_cast; ring
    rw [ha,Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,one_mul]
  rw [he,sub_self,zero_div]

/-- Absolute uniform bounds justify integration of the entire original series. -/
theorem mean_tsum {ι : Type*} [Countable ι] (F : ι → ℝ → ℂ)
    (B : ι → ℝ) (hB : Summable B) (hc : ∀ i, Continuous (F i))
    (hb : ∀ i x, ‖F i x‖ ≤ B i) :
    mean (fun x => ∑' i, F i x) = ∑' i, mean (F i) := by
  have hi (i : ι) : IntegrableOn (F i) (Ioc (-1/2:ℝ) (1/2)) :=
    (hc i).integrableOn_Ioc
  have hn (i : ι) : (∫ x in Ioc (-1/2:ℝ) (1/2), ‖F i x‖) ≤ B i := by
    calc
      _ ≤ ∫ _x in Ioc (-1/2:ℝ) (1/2), B i :=
        integral_mono_ae (hi i).norm (integrable_const _) (Filter.Eventually.of_forall (hb i))
      _ = _ := by norm_num
  exact (integral_tsum_of_summable_integral_norm hi
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hn hB)).symm

end
end RHTower.D4BMCuspProjection
