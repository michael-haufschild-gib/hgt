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

/-- Rounding the positive square root upward moves its logarithmic degree by at most two. -/
theorem upperSquareIndex_log_near {u : ℝ} (hu₀ : 0 ≤ u) :
    u ≤ 2*Real.log (upperSquareIndex u) ∧ 2*Real.log (upperSquareIndex u) ≤ u+2 := by
  let n := upperSquareIndex u
  let X := Real.exp (u/2)
  have hX : 1 ≤ X := Real.one_le_exp (by linarith only [hu₀])
  have hn : X ≤ (n:ℝ) := Nat.le_ceil _
  have hn' : (n:ℝ) ≤ 2*X := (Nat.ceil_lt_add_one (Real.exp_pos _).le).le.trans (by linarith only [hX])
  have hl := Real.log_le_log (Real.exp_pos _) hn
  have hu' := Real.log_le_log ((Real.exp_pos _).trans_le hn) hn'
  rw [Real.log_mul two_ne_zero (Real.exp_pos _).ne'] at hu'
  change Real.log (Real.exp (u/2)) ≤ Real.log n at hl
  change Real.log n ≤ Real.log 2+Real.log (Real.exp (u/2)) at hu'
  rw [Real.log_exp] at hl hu'
  have h₂ := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  constructor <;> linarith only [hl,hu',h₂]

/-- A root displacement of order x^β costs x^(2w+β-1) in the long trace. -/
theorem realSplineTrace_square_power_gap {β : ℝ} (hβ : β ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {x y : ℝ}, 1 ≤ x → x ≤ y → y ≤ x+7*x^β →
      |realSplineTrace (2*Real.log y)-realSplineTrace (2*Real.log x)| ≤ C*x^(2*zetaZeroWidth+β-1) := by
  obtain ⟨L,hL,h⟩ := realSplineTrace_increment
  let w := zetaZeroWidth
  have hw : 0 ≤ w := zetaZeroWidth_nonneg
  refine ⟨14*L*(8:ℝ)^(2*w),by positivity,fun {x y} hx hxy hy => ?_⟩
  have hx' := zero_lt_one.trans_le hx
  have hy' := hx'.trans_le hxy
  have hstep : 2*Real.log y-2*Real.log x ≤ 14*x^β/x := by
    rw [← mul_sub,← Real.log_div hy'.ne' hx'.ne']
    have h₁ := Real.log_le_sub_one_of_pos (div_pos hy' hx')
    have h₂ : y/x-1 ≤ 7*x^β/x := by
      rw [sub_le_iff_le_add,← div_self hx'.ne',← add_div,div_le_div_iff_of_pos_right hx']
      linarith only [hy]
    exact (mul_le_mul_of_nonneg_left (h₁.trans h₂) two_pos.le).trans_eq (by ring)
  have hb : y ≤ 8*x := by
    have hp := Real.rpow_le_rpow_of_exponent_le hx hβ
    rw [Real.rpow_one] at hp
    linarith only [hy,hp]
  have hpow : Real.exp (w*(2*Real.log y)) ≤ (8:ℝ)^(2*w)*x^(2*w) := by
    rw [show w*(2*Real.log y)=Real.log y*(2*w) by ring,← Real.rpow_def_of_pos hy',
      ← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 8) hx'.le]
    exact Real.rpow_le_rpow hy'.le hb (mul_nonneg two_pos.le hw)
  calc _ ≤ L*(2*Real.log y-2*Real.log x)*Real.exp (w*(2*Real.log y)) :=
          h _ _ (mul_nonneg two_pos.le (Real.log_nonneg hx)) (mul_le_mul_of_nonneg_left (Real.log_le_log hx' hxy) two_pos.le)
       _ ≤ (L*(14*x^β/x))*((8:ℝ)^(2*w)*x^(2*w)) := mul_le_mul
           (mul_le_mul_of_nonneg_left hstep hL) hpow (Real.exp_pos _).le (by positivity)
       _ = _ := by rw [Real.rpow_sub hx',Real.rpow_add hx',Real.rpow_one]; ring

/-- A fixed displacement of the root costs a vanishing error because twice
the zero width is less than one. -/
private theorem bounded_rounding_error (X Y : ℝ → ℝ) (hX : Tendsto X atTop atTop)
    (hY : ∀ᶠ u in atTop, X u ≤ Y u ∧ Y u ≤ X u+3) :
    Tendsto (fun u => realSplineTrace (2*Real.log (Y u))-realSplineTrace (2*Real.log (X u))) atTop (𝓝 0) := by
  obtain ⟨C,_,h⟩ := realSplineTrace_square_power_gap (β := 0) zero_le_one
  have hw : 0 < 1-2*zetaZeroWidth := by linarith only [ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths]
  have ht := ((tendsto_rpow_neg_atTop hw).comp hX).const_mul C
  have he : -(1-2*zetaZeroWidth)=2*zetaZeroWidth-1 := by ring
  simp only [Function.comp_apply,he,mul_zero] at ht
  apply squeeze_zero_norm' (a := fun u => C*X u^(2*zetaZeroWidth-1)) _ ht
  filter_upwards [hY,hX.eventually_ge_atTop 1] with u hy hx
  have hh := h hx hy.1 (show Y u ≤ X u+7*(X u)^(0:ℝ) by
    rw [Real.rpow_zero,mul_one]; linarith only [hy.2])
  simpa only [Real.norm_eq_abs,add_zero] using hh

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
