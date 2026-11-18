import GaloisForLFunctions.CountingHolography.Sections.OriginalSectionsAtEveryMultiplicity
import GaloisForLFunctions.CountingHolography.Sections.UnitMultiplicityOnThePoleHyperplane

/-!
# Sampling the continuous long lags at an integer square

Rounding a square root up by bounded distance costs its inverse in log
coordinates. This gains a power over both long trace increments.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology SquareRootThreshold ArithmeticScatteringHolography

/-- Integer square-root conductor assigned to a real logarithmic degree. -/
def upperSquareIndex (u : ℝ) : ℕ := ⌈Real.exp (u/2)⌉₊

theorem upperSquareIndex_pos (u : ℝ) : 0 < upperSquareIndex u :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

theorem upperSquareIndex_monotone : Monotone upperSquareIndex :=
  fun _ _ h => Nat.ceil_mono (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right h two_pos.le))

theorem tendsto_upperSquareIndex : Tendsto upperSquareIndex atTop atTop :=
  tendsto_nat_ceil_atTop.comp (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const two_pos))

/-- Rounding either square root by at most three changes its long trace
by a quantity tending to zero, since twice the zero width is less than one. -/
private theorem bounded_rounding_error (X Y : ℝ → ℝ) (hX : Tendsto X atTop atTop)
    (hY : ∀ᶠ u in atTop, X u ≤ Y u ∧ Y u ≤ X u+3) :
    Tendsto (fun u => realSplineTrace (2*Real.log (Y u))-realSplineTrace (2*Real.log (X u))) atTop (𝓝 0) := by
  obtain ⟨L,hL,hinc⟩ := realSplineTrace_increment
  let w := zetaZeroWidth
  have hw : 0 ≤ w := zetaZeroWidth_nonneg
  have hw' : 2*w-1 < 0 := by dsimp only [w]; linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]
  let C := 6*L*Real.exp (6*w)
  have hdecay := (Real.tendsto_exp_atBot.comp
    ((Real.tendsto_log_atTop.comp hX).const_mul_atTop_of_neg hw')).const_mul C
  apply squeeze_zero_norm' (a := fun u => C*Real.exp ((2*w-1)*Real.log (X u))) _ (by simpa only [mul_zero] using hdecay)
  filter_upwards [hY,hX.eventually_ge_atTop 1] with u hy hx
  let x := X u
  let y := Y u
  have hx' : 0 < x := zero_lt_one.trans_le hx
  have hy' : 0 < y := hx'.trans_le hy.1
  have hlog := Real.log_le_log hx' hy.1
  have hstep : 2*Real.log y-2*Real.log x ≤ 6/x := by
    rw [← mul_sub,← Real.log_div hy'.ne' hx'.ne']
    have h := Real.log_le_sub_one_of_pos (div_pos hy' hx')
    have hy₁ : y/x-1 ≤ 3/x := by
      rw [sub_le_iff_le_add,← div_self hx'.ne',← add_div,div_le_div_iff_of_pos_right hx']
      linarith only [hy.2]
    linarith only [h,hy₁]
  have hd : 6/x ≤ 6 := (div_le_iff₀ hx').mpr (by linarith only [hx])
  have hex := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (show 2*Real.log y ≤ 6+2*Real.log x by linarith only [hstep,hd]) hw)
  rw [Real.norm_eq_abs]
  calc _ ≤ L*(2*Real.log y-2*Real.log x)*Real.exp (w*(2*Real.log y)) :=
          hinc _ _ (mul_nonneg two_pos.le (Real.log_nonneg hx)) (mul_le_mul_of_nonneg_left hlog two_pos.le)
       _ ≤ (L*(6/x))*Real.exp (w*(6+2*Real.log x)) := mul_le_mul
         (mul_le_mul_of_nonneg_left hstep hL) hex (Real.exp_pos _).le (by positivity)
       _ = C*Real.exp ((2*w-1)*Real.log x) := by
         rw [show w*(6+2*Real.log x) = 6*w+2*w*Real.log x by ring,Real.exp_add,
           show (2*w-1)*Real.log x=2*w*Real.log x-Real.log x by ring,Real.exp_sub,Real.exp_log hx']
         dsimp only [C]
         ring

/-- The only surviving term after removing both continuous long lags
from the integer square degree is the fixed short-lag limit. -/
theorem upperSquareIndex_signed_degree :
    Tendsto (fun u : ℝ => integerProbe _ (successorSquareTriple (upperSquareIndex u))-
      (4*realSplineTrace u-2*realSplineTrace (u+Real.log 4))) atTop
        (𝓝 (6*realSplineTrace 0-4*realSplineTrace (Real.log 4))) := by
  let X := fun u : ℝ => Real.exp (u/2)
  let N := upperSquareIndex
  have hX : Tendsto X atTop atTop := Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const two_pos)
  have hnear (u : ℝ) : X u ≤ (N u:ℝ) ∧ (N u:ℝ) ≤ X u+1 :=
    ⟨Nat.le_ceil _,(Nat.ceil_lt_add_one (Real.exp_pos _).le).le⟩
  have h₁ := bounded_rounding_error X (fun u => (N u:ℝ)) hX (Eventually.of_forall fun u =>
    ⟨(hnear u).1,by linarith only [(hnear u).2]⟩)
  have h₂ := bounded_rounding_error (fun u => 2*X u) (fun u => ((2*N u+1:ℕ):ℝ))
    (hX.const_mul_atTop two_pos) (Eventually.of_forall fun u => by
      push_cast
      constructor <;> linarith only [(hnear u).1,(hnear u).2])
  have h₃ := successorSquare_relative_trace_limit.comp tendsto_upperSquareIndex
  have ht := ((h₁.const_mul 4).sub (h₂.const_mul 2)).add
    ((h₃.const_mul 4).const_sub (6*realSplineTrace 0))
  simp only [mul_zero,sub_zero,zero_add] at ht
  apply ht.congr fun u => ?_
  change 4*(realSplineTrace (2*Real.log (N u))-realSplineTrace (2*Real.log (X u)))-
    2*(realSplineTrace (2*Real.log ((2*N u+1:ℕ):ℝ))-realSplineTrace (2*Real.log (2*X u)))+
      (6*realSplineTrace 0-4*realSplineTrace _) = _
  have hxl : 2*Real.log (X u)=u := by dsimp only [X]; rw [Real.log_exp]; ring
  have hxl' : 2*Real.log (2*X u)=u+Real.log 4 := by
    rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne',show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    push_cast
    linarith only [hxl]
  rw [integerProbe_successorSquareTriple (upperSquareIndex_pos u),hxl,hxl']
  simp only [Real.log_pow,N]
  push_cast
  ring_nf

#print axioms upperSquareIndex_signed_degree

end GaloisForLFunctions.CountingHolography.Sections
