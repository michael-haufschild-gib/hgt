import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCenteredMangoldtTailOfTheProduct
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheQuotientCellsOfTheCappedSpline

/-!
# The ordinary prime error below a quadratic product cut

On a single conductor a subquadratic band lies before the first spline
sample. Its remaining mesh, paired with the centered Mangoldt measure,
obeys the ordinary prime-error exponent at the upper product cutoff.
-/

noncomputable section
open Finset Filter ArithmeticFunction
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Uniform two-cut transfer back to the original capped coprime product. -/
theorem shell_centering_transfer :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V U : ℕ → ℕ) (N M : ℕ),
      |(∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
          cappedUpperProductReading (U n) n n)) -
        ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
          centeredProductReading (U n) n)| ≤ C*(M:ℝ)^3*conductorLog M := by
  obtain ⟨K,hK,h⟩ := partial_prefix_centered_product_transfer
  refine ⟨K+K,add_nonneg hK hK,fun V U N M => ?_⟩
  let E (D : ℕ → ℕ) := ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (D n) n -
    cappedUpperProductReading (D n) n n)
  have he : (∑ n ∈ Ioc N M, (n:ℝ)^2*(cappedUpperProductReading (V n) n n -
        cappedUpperProductReading (U n) n n)) -
        ∑ n ∈ Ioc N M, (n:ℝ)^2*(centeredProductReading (V n) n -
          centeredProductReading (U n) n) = E U - E V := by
    simp only [E,←sum_sub_distrib]
    exact sum_congr rfl fun _ _ => by ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add (h U N M) (h V N M)).trans_eq (by ring))

/-- Late subquadratic cuts lie before spline support, while the coprime
cofactor cap already lies below the lower product cut. -/
theorem subquadratic_cut_geometry {α β c : ℝ} (hα : 1 < α) (hαβ : α ≤ β) (hβ : β < 2)
    (hc : 1 ≤ c) (hc' : c ≤ 2) :
    ∀ᶠ n : ℕ in atTop,
      let V := ⌊(n:ℝ)^α⌋₊
      let U := ⌊c*(n:ℝ)^β⌋₊
      V ≤ U ∧ U ≤ splineHorizon n ∧ productLower 1 (splineHorizon n) ≤ V ∧
        (U:ℝ)+1 < Real.exp (-8)*(n:ℝ)^2 := by
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  have hg : Tendsto (fun n : ℕ => (n:ℝ)^(2-β)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hβ)).comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => (n:ℝ)^(α-1)) atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hα)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),hg.eventually_ge_atTop (4*Real.exp 8),
    hd.eventually_ge_atTop (2*A)] with n hn hgap hcap
  let X := (n:ℝ)^β
  let U := ⌊c*X⌋₊
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 := zero_lt_one.trans_le hn1
  have hX1 : 1 ≤ X := Real.one_le_rpow hn1 ((zero_lt_one.trans hα).le.trans hαβ)
  have hX := zero_lt_one.trans_le hX1
  have hU : (U:ℝ) ≤ 2*X := (Nat.floor_le (mul_nonneg (zero_le_one.trans hc) hX.le)).trans
    (mul_le_mul_of_nonneg_right hc' hX.le)
  have hpow : X*(n:ℝ)^(2-β) = (n:ℝ)^2 := by
    dsimp only [X]; rw [←Real.rpow_add hn0,show β+(2-β)=2 by ring,Real.rpow_two]
  have hx4 : 4 ≤ Real.exp (-8)*(n:ℝ)^(2-β) := by
    rw [Real.exp_neg,inv_mul_eq_div,le_div_iff₀ (Real.exp_pos 8)]
    exact hgap
  have hbefore : (U:ℝ)+1 < Real.exp (-8)*(n:ℝ)^2 := by
    have hh := mul_le_mul_of_nonneg_left hx4 hX.le
    rw [mul_left_comm X,hpow] at hh
    linarith only [hX1,hU,hh]
  have hscale := successorSquareWindowScale_bounds n
  have hL : (n:ℝ)^2 ≤ (splineHorizon n:ℝ) := by
    dsimp only [splineHorizon]
    push_cast
    linarith only [hscale.1,hscale.2.2,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
  have huL : (U:ℝ) ≤ splineHorizon n := by
    have hh := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by norm_num : (-8:ℝ) ≤ 0))
      (sq_nonneg (n:ℝ))
    linarith only [hbefore,hL,hh]
  refine ⟨Nat.floor_mono ((Real.rpow_le_rpow_of_exponent_le hn1 hαβ).trans
    (le_mul_of_one_le_left hX.le hc)),Nat.cast_le.mp huL,?_,hbefore⟩
  apply Nat.le_floor
  have hr := Real.sqrt_le_sqrt (hwin hn)
  rw [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn0.le)] at hr
  have hpl : (productLower 1 (splineHorizon n):ℝ) ≤ 2*Real.sqrt (splineHorizon n) := by
    refine (Nat.cast_le.mpr (min_le_right _ _)).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
  have he : (n:ℝ)^(α-1)*n=(n:ℝ)^α := by
    calc _ = (n:ℝ)^(α-1)*(n:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
         _ = _ := by rw [←Real.rpow_add hn0,sub_add_cancel]
  rw [←he]
  linarith only [hpl,hr,mul_le_mul_of_nonneg_right hcap hn0.le]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
