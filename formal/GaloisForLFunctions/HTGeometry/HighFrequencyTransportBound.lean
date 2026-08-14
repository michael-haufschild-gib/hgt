import GaloisForLFunctions.HTGeometry.ResolventDerivative
import GaloisForLFunctions.HTGeometry.FrequencyPropagator
import GaloisForLFunctions.HTGeometry.MonotoneSymbolTailEstimate
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# The high-frequency transport bound

An oscillatory integral against the frequency propagator is `O(1/L)` uniformly in the endpoint.
The mechanism is a single integration by parts with the resolvent of the shifted symbol as
integrating factor: since `W_L' = i B_L W_L` and `B_L` is invertible with `‖B_L^{-1}‖ ≤ (L-‖T‖/2)^{-1}`,

`f W_L = (1/i) [ (f B_L^{-1} W_L)' - f' B_L^{-1} W_L + f c' B_L^{-2} W_L ]`,

and each term on the right is absolutely integrable with a gain of one power of the frequency.  No
part of the Gamma phase is discarded: the symbol `r` enters only through its nonnegativity and the
exact telescoping of `c'/(c)²`.
-/

open Complex MeasureTheory intervalIntegral Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A] [NormedAlgebra ℂ A]
  [CompleteSpace A] [Nontrivial A] [StarModule ℂ A] [ContinuousStar A]

/-- **The high-frequency transport bound.**  An amplitude `f` bounded by `M` with integrable
derivative produces an oscillatory integral of size `O(1/L)`, with the constant depending only on
the amplitude and not on the symbol `r` or the endpoint `R`. -/
theorem norm_integral_freqPropagator_le {T : A} (hT : IsSelfAdjoint T)
    {r r' Rint f f' : ℝ → ℝ} {L ε R M : ℝ}
    (hTL : ‖T‖ / 2 < L) (hεR : ε ≤ R)
    (hr : ∀ x ∈ uIcc ε R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc ε R, 0 ≤ r x)
    (hr'nn : ∀ x ∈ uIcc ε R, 0 ≤ r' x)
    (hr'c : ContinuousOn r' (uIcc ε R))
    (hRint : ∀ x ∈ uIcc ε R, HasDerivAt Rint (r x) x)
    (hf : ∀ x ∈ uIcc ε R, HasDerivAt f (f' x) x)
    (hf'c : ContinuousOn f' (uIcc ε R))
    (hfb : ∀ x ∈ uIcc ε R, |f x| ≤ M) :
    ‖∫ η in ε..R, f η • freqPropagator L Rint T η‖
      ≤ (|f ε| + |f R| + (∫ η in ε..R, |f' η|) + M) * (L - ‖T‖ / 2)⁻¹ := by
  have hc₀ : (0:ℝ) < L - ‖T‖ / 2 := by linarith
  -- the shift and its derivative
  have hcderiv : ∀ x ∈ uIcc ε R, HasDerivAt (fun y => L + r y / 2) (r' x / 2) x := by
    intro x hx
    exact ((hr x hx).div_const 2).const_add L
  have hcgt : ∀ x ∈ uIcc ε R, ‖T‖ / 2 < L + r x / 2 := by
    intro x hx
    have := hrnn x hx
    linarith
  have hBnorm : ∀ x ∈ uIcc ε R,
      ‖shiftedSymbolInv (L + r x / 2) T‖ ≤ (L - ‖T‖ / 2 + r x / 2)⁻¹ := by
    intro x hx
    have h := norm_shiftedSymbolInv_le (c := L + r x / 2) (T := T) (hcgt x hx)
    have heq : L + r x / 2 - ‖T‖ / 2 = L - ‖T‖ / 2 + r x / 2 := by ring
    rwa [heq] at h
  have hBnorm' : ∀ x ∈ uIcc ε R, ‖shiftedSymbolInv (L + r x / 2) T‖ ≤ (L - ‖T‖ / 2)⁻¹ := by
    intro x hx
    refine le_trans (hBnorm x hx) (inv_anti₀ hc₀ ?_)
    have := hrnn x hx
    linarith
  have hWnorm : ∀ x : ℝ, ‖freqPropagator L Rint T x‖ = 1 := fun x =>
    norm_freqPropagator hT L Rint x
  -- derivatives of the resolvent and the propagator
  have hBderiv : ∀ x ∈ uIcc ε R,
      HasDerivAt (fun y => shiftedSymbolInv (L + r y / 2) T)
        (-((((r' x / 2 : ℝ)) : ℂ) • (shiftedSymbolInv (L + r x / 2) T *
          shiftedSymbolInv (L + r x / 2) T))) x := by
    intro x hx
    exact hasDerivAt_shiftedSymbolInv (T := T) (c := fun y => L + r y / 2)
      (c' := fun y => r' y / 2) (hcgt x hx) (hcderiv x hx)
  have hWderiv : ∀ x ∈ uIcc ε R,
      HasDerivAt (freqPropagator L Rint T)
        (I • (shiftedSymbolOp (L + r x / 2) T * freqPropagator L Rint T x)) x := by
    intro x hx
    exact hasDerivAt_freqPropagator (L := L) (Rint := Rint) (r := r) T (hRint x hx)
  -- the integration-by-parts primitive
  have hPderiv : ∀ x ∈ uIcc ε R,
      HasDerivAt (fun y => shiftedSymbolInv (L + r y / 2) T * freqPropagator L Rint T y)
        (-((((r' x / 2 : ℝ)) : ℂ) • (shiftedSymbolInv (L + r x / 2) T *
            shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x))
          + I • freqPropagator L Rint T x) x := by
    intro x hx
    have h := (hBderiv x hx).mul (hWderiv x hx)
    have e1 : (-((((r' x / 2 : ℝ)) : ℂ) • (shiftedSymbolInv (L + r x / 2) T *
        shiftedSymbolInv (L + r x / 2) T))) * freqPropagator L Rint T x
        = -((((r' x / 2 : ℝ)) : ℂ) • (shiftedSymbolInv (L + r x / 2) T *
            shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x)) := by
      rw [neg_mul, smul_mul_assoc]
    have e2 : shiftedSymbolInv (L + r x / 2) T *
        (I • (shiftedSymbolOp (L + r x / 2) T * freqPropagator L Rint T x))
        = I • freqPropagator L Rint T x := by
      rw [mul_smul_comm, ← mul_assoc, inv_mul_shiftedSymbolOp (hcgt x hx), one_mul]
    rw [e1, e2] at h
    exact h
  -- continuity of the ingredients
  have hWc : ContinuousOn (freqPropagator L Rint T) (uIcc ε R) := by
    intro x hx
    exact ((hWderiv x hx).continuousAt).continuousWithinAt
  have hBc : ContinuousOn (fun x => shiftedSymbolInv (L + r x / 2) T) (uIcc ε R) := by
    intro x hx
    exact ((hBderiv x hx).continuousAt).continuousWithinAt
  have hfc : ContinuousOn f (uIcc ε R) := by
    intro x hx
    exact ((hf x hx).continuousAt).continuousWithinAt
  have hrc : ContinuousOn r (uIcc ε R) := by
    intro x hx
    exact ((hr x hx).continuousAt).continuousWithinAt
  have hPc : ContinuousOn
      (fun x => shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x) (uIcc ε R) :=
    hBc.mul hWc
  have hPnorm : ∀ x ∈ uIcc ε R,
      ‖shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x‖ ≤ (L - ‖T‖ / 2)⁻¹ := by
    intro x hx
    refine le_trans (norm_mul_le _ _) ?_
    rw [hWnorm x, mul_one]
    exact hBnorm' x hx
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg (f ε)) (hfb ε left_mem_uIcc)
  -- integrability of the three pieces
  have hDc : ContinuousOn (fun x => -((((r' x / 2 : ℝ)) : ℂ) •
      (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
        freqPropagator L Rint T x))) (uIcc ε R) := by
    refine ContinuousOn.neg (ContinuousOn.smul ?_ ((hBc.mul hBc).mul hWc))
    exact Complex.continuous_ofReal.comp_continuousOn (hr'c.div_const 2)
  have hint_D : IntervalIntegrable (fun x => f x • (-((((r' x / 2 : ℝ)) : ℂ) •
      (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
        freqPropagator L Rint T x)))) volume ε R := (hfc.smul hDc).intervalIntegrable
  have hint_W : IntervalIntegrable (fun x => f x • (I • freqPropagator L Rint T x))
      volume ε R := by
    refine ContinuousOn.intervalIntegrable ?_
    exact hfc.smul (continuousOn_const.smul hWc)
  have hint_fP : IntervalIntegrable (fun x => f' x •
      (shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x)) volume ε R :=
    (hf'c.smul hPc).intervalIntegrable
  have hint_sum : IntervalIntegrable (fun x => f x • (-((((r' x / 2 : ℝ)) : ℂ) •
        (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
          freqPropagator L Rint T x))
        + I • freqPropagator L Rint T x)
      + f' x • (shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x))
      volume ε R := by
    refine IntervalIntegrable.add ?_ hint_fP
    refine ContinuousOn.intervalIntegrable ?_
    exact hfc.smul (hDc.add (continuousOn_const.smul hWc))
  -- the fundamental theorem of calculus for the integration-by-parts primitive
  have hGderiv : ∀ x ∈ uIcc ε R,
      HasDerivAt (fun y => f y • (shiftedSymbolInv (L + r y / 2) T * freqPropagator L Rint T y))
        (f x • (-((((r' x / 2 : ℝ)) : ℂ) • (shiftedSymbolInv (L + r x / 2) T *
              shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x))
            + I • freqPropagator L Rint T x)
          + f' x • (shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x)) x :=
    fun x hx => (hf x hx).smul (hPderiv x hx)
  have hFTC := integral_eq_sub_of_hasDerivAt hGderiv hint_sum
  -- split the integral into the three transport pieces
  have hsplit1 := integral_add
    (f := fun x => f x • (-((((r' x / 2 : ℝ)) : ℂ) •
        (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
          freqPropagator L Rint T x)) + I • freqPropagator L Rint T x))
    (g := fun x => f' x • (shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x))
    (a := ε) (b := R)
    (ContinuousOn.intervalIntegrable (hfc.smul (hDc.add (continuousOn_const.smul hWc)))) hint_fP
  have hsplit2 : (∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
        (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
          freqPropagator L Rint T x)) + I • freqPropagator L Rint T x))
      = (∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
          (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x))))
        + ∫ x in ε..R, f x • (I • freqPropagator L Rint T x) := by
    rw [← integral_add hint_D hint_W]
    refine integral_congr fun x _ => ?_
    show f x • (_ + _) = f x • _ + f x • _
    rw [smul_add]
  have hIout : (∫ x in ε..R, f x • (I • freqPropagator L Rint T x))
      = I • ∫ x in ε..R, f x • freqPropagator L Rint T x := by
    rw [← intervalIntegral.integral_smul]
    refine integral_congr fun x _ => ?_
    show f x • (I • freqPropagator L Rint T x) = I • (f x • freqPropagator L Rint T x)
    rw [smul_comm]
  have hkey : I • (∫ x in ε..R, f x • freqPropagator L Rint T x)
      = (f R • (shiftedSymbolInv (L + r R / 2) T * freqPropagator L Rint T R)
          - f ε • (shiftedSymbolInv (L + r ε / 2) T * freqPropagator L Rint T ε))
        - (∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
            (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
              freqPropagator L Rint T x))))
        - ∫ x in ε..R, f' x • (shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x) := by
    rw [hsplit1, hsplit2, hIout] at hFTC
    rw [← hFTC]
    abel
  have hnormI : ‖I • (∫ x in ε..R, f x • freqPropagator L Rint T x)‖
      = ‖∫ x in ε..R, f x • freqPropagator L Rint T x‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  -- boundary term
  have h1 : ‖f R • (shiftedSymbolInv (L + r R / 2) T * freqPropagator L Rint T R)
      - f ε • (shiftedSymbolInv (L + r ε / 2) T * freqPropagator L Rint T ε)‖
      ≤ (|f R| + |f ε|) * (L - ‖T‖ / 2)⁻¹ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, add_mul]
    gcongr
    · exact hPnorm R right_mem_uIcc
    · exact hPnorm ε left_mem_uIcc
  -- amplitude-derivative term
  have h2 : ‖∫ x in ε..R, f' x • (shiftedSymbolInv (L + r x / 2) T *
      freqPropagator L Rint T x)‖
      ≤ (∫ η in ε..R, |f' η|) * (L - ‖T‖ / 2)⁻¹ := by
    refine le_trans (norm_integral_le_integral_norm hεR) ?_
    have hmono : (∫ x in ε..R, ‖f' x • (shiftedSymbolInv (L + r x / 2) T *
          freqPropagator L Rint T x)‖)
        ≤ ∫ x in ε..R, |f' x| * (L - ‖T‖ / 2)⁻¹ := by
      refine integral_mono_on hεR ((hf'c.smul hPc).norm.intervalIntegrable)
        ((hf'c.abs.mul continuousOn_const).intervalIntegrable) fun x hx => ?_
      have hx' : x ∈ uIcc ε R := by rwa [uIcc_of_le hεR]
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hPnorm x hx') (abs_nonneg _)
    refine le_trans hmono (le_of_eq ?_)
    rw [intervalIntegral.integral_mul_const]
  -- symbol-derivative term
  have hdenc : ContinuousOn (fun x => r' x / (L - ‖T‖ / 2 + r x / 2) ^ 2) (uIcc ε R) := by
    refine hr'c.div ((continuousOn_const.add (hrc.div_const 2)).pow 2) fun x hx => ?_
    have := hrnn x hx
    positivity
  have hint_tail : IntervalIntegrable (fun x => r' x / (L - ‖T‖ / 2 + r x / 2) ^ 2)
      volume ε R := hdenc.intervalIntegrable
  have htail := integral_deriv_div_sq_le (r := r) (r' := r') (c := L - ‖T‖ / 2)
    (ε := ε) (R := R) hc₀ hrnn hr hint_tail
  have h3 : ‖∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
      (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
        freqPropagator L Rint T x)))‖ ≤ M * (L - ‖T‖ / 2)⁻¹ := by
    refine le_trans (norm_integral_le_integral_norm hεR) ?_
    have hmono : (∫ x in ε..R, ‖f x • (-((((r' x / 2 : ℝ)) : ℂ) •
          (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x)))‖)
        ≤ ∫ x in ε..R, (M / 2) * (r' x / (L - ‖T‖ / 2 + r x / 2) ^ 2) := by
      refine integral_mono_on hεR ((hfc.smul hDc).norm.intervalIntegrable)
        ((continuousOn_const.mul hdenc).intervalIntegrable) fun x hx => ?_
      have hx' : x ∈ uIcc ε R := by rwa [uIcc_of_le hεR]
      have hrx := hrnn x hx'
      have hr'x := hr'nn x hx'
      have hBx := hBnorm x hx'
      have hpos : (0:ℝ) < L - ‖T‖ / 2 + r x / 2 := by linarith
      have hprod : ‖shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
          freqPropagator L Rint T x‖ ≤ (L - ‖T‖ / 2 + r x / 2)⁻¹ ^ 2 :=
        calc ‖shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
              freqPropagator L Rint T x‖
            ≤ ‖shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T‖
              * ‖freqPropagator L Rint T x‖ := norm_mul_le _ _
          _ = ‖shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T‖ := by
              rw [hWnorm x, mul_one]
          _ ≤ ‖shiftedSymbolInv (L + r x / 2) T‖ * ‖shiftedSymbolInv (L + r x / 2) T‖ :=
              norm_mul_le _ _
          _ ≤ (L - ‖T‖ / 2 + r x / 2)⁻¹ * (L - ‖T‖ / 2 + r x / 2)⁻¹ :=
              mul_le_mul hBx hBx (norm_nonneg _) (by positivity)
          _ = (L - ‖T‖ / 2 + r x / 2)⁻¹ ^ 2 := (sq _).symm
      rw [norm_smul, Real.norm_eq_abs, norm_neg, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ r' x / 2)]
      have hfx := hfb x hx'
      have hstep : |f x| * (r' x / 2 *
          ‖shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x‖)
          ≤ M * (r' x / 2 * (L - ‖T‖ / 2 + r x / 2)⁻¹ ^ 2) := by
        refine mul_le_mul hfx ?_ (by positivity) hM0
        exact mul_le_mul_of_nonneg_left hprod (by linarith)
      refine le_trans hstep (le_of_eq ?_)
      rw [inv_pow, div_eq_mul_inv]
      ring
    refine le_trans hmono ?_
    rw [intervalIntegral.integral_const_mul]
    have hMhalf : (0:ℝ) ≤ M / 2 := by linarith
    have := mul_le_mul_of_nonneg_left htail hMhalf
    refine le_trans this (le_of_eq ?_)
    field_simp
  -- assemble
  rw [← hnormI, hkey]
  have hsplitnorm : ‖((f R • (shiftedSymbolInv (L + r R / 2) T * freqPropagator L Rint T R)
        - f ε • (shiftedSymbolInv (L + r ε / 2) T * freqPropagator L Rint T ε))
      - (∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
          (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x)))))
      - ∫ x in ε..R, f' x • (shiftedSymbolInv (L + r x / 2) T * freqPropagator L Rint T x)‖
      ≤ (‖(f R • (shiftedSymbolInv (L + r R / 2) T * freqPropagator L Rint T R)
            - f ε • (shiftedSymbolInv (L + r ε / 2) T * freqPropagator L Rint T ε))‖
          + ‖∫ x in ε..R, f x • (-((((r' x / 2 : ℝ)) : ℂ) •
              (shiftedSymbolInv (L + r x / 2) T * shiftedSymbolInv (L + r x / 2) T *
                freqPropagator L Rint T x)))‖)
        + ‖∫ x in ε..R, f' x • (shiftedSymbolInv (L + r x / 2) T *
            freqPropagator L Rint T x)‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    gcongr
    exact norm_sub_le _ _
  refine le_trans hsplitnorm ?_
  have hexp : (|f ε| + |f R| + (∫ η in ε..R, |f' η|) + M) * (L - ‖T‖ / 2)⁻¹
      = (|f R| + |f ε|) * (L - ‖T‖ / 2)⁻¹ + M * (L - ‖T‖ / 2)⁻¹
        + (∫ η in ε..R, |f' η|) * (L - ‖T‖ / 2)⁻¹ := by ring
  rw [hexp]
  linarith [h1, h2, h3]



/-- **The half-power high-frequency estimate.**  With the critical amplitude `η^{-1/2}` the
oscillatory integral against the propagator is bounded by `(3ε^{-1/2} + R^{-1/2})/(L - ‖T‖/2)`,
uniformly in the symbol and in the endpoint. -/
theorem norm_integral_halfPower_freqPropagator_le {T : A} (hT : IsSelfAdjoint T)
    {r r' Rint : ℝ → ℝ} {L ε R : ℝ}
    (hTL : ‖T‖ / 2 < L) (hε : 0 < ε) (hεR : ε ≤ R)
    (hr : ∀ x ∈ uIcc ε R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc ε R, 0 ≤ r x)
    (hr'nn : ∀ x ∈ uIcc ε R, 0 ≤ r' x)
    (hr'c : ContinuousOn r' (uIcc ε R))
    (hRint : ∀ x ∈ uIcc ε R, HasDerivAt Rint (r x) x) :
    ‖∫ η in ε..R, (η ^ (-(1:ℝ)/2)) • freqPropagator L Rint T η‖
      ≤ (3 * ε ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ := by
  have hc₀ : (0:ℝ) < L - ‖T‖ / 2 := by linarith
  have hIcc : uIcc ε R = Icc ε R := uIcc_of_le hεR
  have hpos : ∀ x ∈ uIcc ε R, 0 < x := by
    intro x hx
    rw [hIcc] at hx
    exact lt_of_lt_of_le hε hx.1
  set f : ℝ → ℝ := fun x => x ^ (-(1:ℝ)/2) with hfdef
  set f' : ℝ → ℝ := fun x => -(1:ℝ)/2 * x ^ (-(3:ℝ)/2) with hf'def
  have hfderiv : ∀ x ∈ uIcc ε R, HasDerivAt f (f' x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hpos x hx)
    have h := Real.hasDerivAt_rpow_const (x := x) (p := -(1:ℝ)/2) (Or.inl hx0)
    have hexp : (-(1:ℝ)/2 - 1) = -(3:ℝ)/2 := by norm_num
    rw [hexp] at h
    exact h
  have hf'c : ContinuousOn f' (uIcc ε R) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    have hb := Real.continuousAt_rpow_const x (-(3:ℝ)/2) (Or.inl (ne_of_gt (hpos x hx)))
    exact (hb.const_mul (-(1:ℝ)/2))
  have hfabs : ∀ x ∈ uIcc ε R, |f x| ≤ ε ^ (-(1:ℝ)/2) := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have hxpos : (0:ℝ) < x ^ (-(1:ℝ)/2) := Real.rpow_pos_of_pos hx0 _
    rw [abs_of_pos hxpos]
    have hεx : ε ≤ x := by
      rw [hIcc] at hx
      exact hx.1
    have hstep : ε ^ ((1:ℝ)/2) ≤ x ^ ((1:ℝ)/2) :=
      Real.rpow_le_rpow (le_of_lt hε) hεx (by norm_num)
    have hneg : ∀ y : ℝ, 0 < y → y ^ (-(1:ℝ)/2) = (y ^ ((1:ℝ)/2))⁻¹ := by
      intro y hy
      rw [show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg (le_of_lt hy)]
    rw [hneg x hx0, hneg ε hε]
    exact inv_anti₀ (Real.rpow_pos_of_pos hε _) hstep
  have habs : ∀ x ∈ uIcc ε R, |f' x| = x ^ (-(3:ℝ)/2) / 2 := by
    intro x hx
    have hx0 : 0 < x := hpos x hx
    have hxpos : (0:ℝ) < x ^ (-(3:ℝ)/2) := Real.rpow_pos_of_pos hx0 _
    rw [hf'def]
    rw [abs_of_nonpos (by nlinarith)]
    ring
  have hcont3 : ContinuousOn (fun x : ℝ => x ^ (-(3:ℝ)/2)) (uIcc ε R) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(3:ℝ)/2) (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  have hf'int : (∫ η in ε..R, |f' η|) ≤ ε ^ (-(1:ℝ)/2) := by
    have hcongr : (∫ η in ε..R, |f' η|) = ∫ η in ε..R, η ^ (-(3:ℝ)/2) / 2 := by
      refine integral_congr fun x hx => ?_
      exact habs x (by rwa [hIcc] at hx ⊢)
    rw [hcongr, intervalIntegral.integral_div]
    have h := integral_rpow_neg_three_halves_le hε hεR
    linarith
  have hmain := norm_integral_freqPropagator_le (T := T) (M := ε ^ (-(1:ℝ)/2)) hT hTL hεR
    hr hrnn hr'nn hr'c hRint hfderiv hf'c hfabs
  refine le_trans hmain ?_
  have hfε : |f ε| = ε ^ (-(1:ℝ)/2) := abs_of_pos (Real.rpow_pos_of_pos hε _)
  have hfR : |f R| = R ^ (-(1:ℝ)/2) :=
    abs_of_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le hε hεR) _)
  rw [hfε, hfR]
  have hinvnn : (0:ℝ) ≤ (L - ‖T‖ / 2)⁻¹ := by positivity
  nlinarith [hf'int, hinvnn]

section Vector

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- **The high-frequency estimate on a vector channel.**  Applied to a fixed vector the transport
integral of the critical amplitude is `O(‖v‖/L)`: this is the high-frequency half of the half-log
scattering asymptotic, with the whole Gamma phase retained. -/
theorem norm_integral_halfPower_freqPropagator_apply_le {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    {r r' Rint : ℝ → ℝ} {L ε R : ℝ} (v : X)
    (hTL : ‖T‖ / 2 < L) (hε : 0 < ε) (hεR : ε ≤ R)
    (hr : ∀ x ∈ uIcc ε R, HasDerivAt r (r' x) x)
    (hrnn : ∀ x ∈ uIcc ε R, 0 ≤ r x)
    (hr'nn : ∀ x ∈ uIcc ε R, 0 ≤ r' x)
    (hr'c : ContinuousOn r' (uIcc ε R))
    (hRint : ∀ x ∈ uIcc ε R, HasDerivAt Rint (r x) x) :
    ‖∫ η in ε..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η v)‖
      ≤ (3 * ε ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ * ‖v‖ := by
  have hmain := norm_integral_halfPower_freqPropagator_le hT hTL hε hεR hr hrnn hr'nn hr'c hRint
  have hIcc : uIcc ε R = Icc ε R := uIcc_of_le hεR
  have hpos : ∀ x ∈ uIcc ε R, 0 < x := by
    intro x hx
    rw [hIcc] at hx
    exact lt_of_lt_of_le hε hx.1
  have hWc : ContinuousOn (freqPropagator L Rint T) (uIcc ε R) := by
    intro x hx
    exact ((hasDerivAt_freqPropagator (L := L) (Rint := Rint) (r := r) T
      (hRint x hx)).continuousAt).continuousWithinAt
  have hac : ContinuousOn (fun x : ℝ => x ^ (-(1:ℝ)/2)) (uIcc ε R) := by
    intro x hx
    exact (Real.continuousAt_rpow_const x (-(1:ℝ)/2)
      (Or.inl (ne_of_gt (hpos x hx)))).continuousWithinAt
  have hint : IntervalIntegrable
      (fun η => (η ^ (-(1:ℝ)/2)) • freqPropagator L Rint T η) volume ε R :=
    (hac.smul hWc).intervalIntegrable
  have hcomm := (ContinuousLinearMap.apply ℂ X v).intervalIntegral_comp_comm hint
  have hpt : ∀ η : ℝ, (ContinuousLinearMap.apply ℂ X v)
      ((η ^ (-(1:ℝ)/2)) • freqPropagator L Rint T η)
      = (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η v) := by
    intro η
    rfl
  have hrewrite : (∫ η in ε..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η v))
      = (ContinuousLinearMap.apply ℂ X v)
        (∫ η in ε..R, (η ^ (-(1:ℝ)/2)) • freqPropagator L Rint T η) := by
    rw [← hcomm]
    exact integral_congr fun η _ => (hpt η).symm
  rw [hrewrite]
  show ‖(∫ η in ε..R, (η ^ (-(1:ℝ)/2)) • freqPropagator L Rint T η) v‖ ≤ _
  refine le_trans (ContinuousLinearMap.le_opNorm _ v) ?_
  exact mul_le_mul_of_nonneg_right hmain (norm_nonneg v)

end Vector

end

end GaloisForLFunctions.HTGeometry
