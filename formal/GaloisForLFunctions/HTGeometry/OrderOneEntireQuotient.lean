import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import GaloisForLFunctions.HTGeometry.FiniteOrderEntireQuotient

/-!
# Order-one growth of zero-free entire quotients

The quotient proximity estimate preserves the precise `r log r` envelope.
This is the growth step for finite-order theta half-port gauge rigidity.
-/

noncomputable section

open Complex Metric Set ValueDistribution

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions.QuotientProximity

/-- Subtraction preserves the order-one envelope. -/
theorem OrderOneEnvelope.sub {f g : ℂ → ℂ} (hf : OrderOneEnvelope f)
    (hg : OrderOneEnvelope g) : OrderOneEnvelope (fun z => f z - g z) :=
  (hf.add (hg.const_mul (-1))).congr fun _ => by ring

/-- Every polynomial has an order-one envelope. -/
theorem orderOneEnvelope_polynomial (P : Polynomial ℂ) :
    OrderOneEnvelope (fun z => P.eval z) := by
  have hid : OrderOneEnvelope (fun z : ℂ => z) := by
    refine ⟨1, by norm_num, fun z => ?_⟩
    have hz := norm_nonneg z
    have hlog : 0 ≤ Real.log (2 + ‖z‖) := Real.log_nonneg (by linarith)
    calc
      ‖z‖ ≤ 2 + ‖z‖ := by linarith
      _ = Real.exp (Real.log (2 + ‖z‖)) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (orderOneWeight 1 z) := by
        apply Real.exp_le_exp.mpr
        simp only [orderOneWeight, one_mul]
        nlinarith
  have hp (n : ℕ) : OrderOneEnvelope (fun z : ℂ => z ^ n) := by
    induction n with
    | zero => simpa using orderOneEnvelope_const 1
    | succ n ih => simpa only [pow_succ] using ih.mul hid
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n a => simpa only [Polynomial.eval_monomial] using (hp n).const_mul a

/-- Cauchy's estimate on a unit circle preserves the order-one envelope. -/
theorem OrderOneEnvelope.deriv {f : ℂ → ℂ} (hf : OrderOneEnvelope f)
    (hd : Differentiable ℂ f) : OrderOneEnvelope (deriv f) := by
  obtain ⟨C, hC, hb⟩ := hf
  refine ⟨4 * C, by positivity, fun z => ?_⟩
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := z) (R := 1) (C := Real.exp (orderOneWeight (4 * C) z))
    (by norm_num) hd.diffContOnCl ?_
  · simpa using hc
  intro w hw
  refine (hb w).trans (Real.exp_le_exp.mpr ?_)
  have hz := norm_nonneg z
  have hwz : ‖w‖ ≤ ‖z‖ + 1 := by
    have h := norm_sub_le w z
    have ht := norm_add_le (w - z) z
    rw [sub_add_cancel] at ht
    rw [← dist_eq_norm, Metric.mem_sphere.mp hw] at ht
    linarith
  have hlinear : 1 + ‖w‖ ≤ 2 * (1 + ‖z‖) := by linarith
  have hlog : Real.log (2 + ‖w‖) ≤ 2 * Real.log (2 + ‖z‖) := by
    calc
      Real.log (2 + ‖w‖) ≤ Real.log ((2 + ‖z‖) ^ (2 : ℕ)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      _ = 2 * Real.log (2 + ‖z‖) := by rw [Real.log_pow]; norm_num
  have hs := mul_le_mul hlinear hlog
    (Real.log_nonneg (by linarith [norm_nonneg w])) (by positivity)
  have hm := mul_le_mul_of_nonneg_left hs hC.le
  dsimp [orderOneWeight]
  nlinarith

private theorem proximity_le_orderOneWeight {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ z, ‖F z‖ ≤ Real.exp (orderOneWeight C z))
    {R : ℝ} (hR : 0 ≤ R) :
    proximity F ⊤ R ≤ C * (1 + R) * Real.log (2 + R) := by
  refine le_trans (proximity_top_le_posLog_of_norm
    (M := Real.exp (C * (1 + R) * Real.log (2 + R))) hR
    (fun z _ => (hF z (mem_univ z)).meromorphicAt) ?_) ?_
  · intro z hz
    simpa [orderOneWeight, hz] using hbound z
  · rw [Real.posLog, Real.log_exp]
    exact max_le (mul_nonneg (mul_nonneg hC (by linarith))
      (Real.log_nonneg (by linarith))) le_rfl

/-- A zero-free entire quotient of two nonzero entire functions with `r log r`
growth has the same growth envelope. -/
theorem OrderOneEnvelope.of_entire_quotient {F G H : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F univ) (hG : AnalyticOnNhd ℂ G univ)
    (hH : AnalyticOnNhd ℂ H univ)
    (hFne : ∃ z, F z ≠ 0) (hGne : ∃ z, G z ≠ 0)
    (hHzero : ∀ z, H z ≠ 0) (hfac : ∀ z, G z = H z * F z)
    (hFgrowth : OrderOneEnvelope F) (hGgrowth : OrderOneEnvelope G) :
    OrderOneEnvelope H := by
  obtain ⟨CF, hCF, hFb⟩ := hFgrowth
  obtain ⟨CG, hCG, hGb⟩ := hGgrowth
  obtain ⟨zF, hzF⟩ := hFne
  obtain ⟨zG, hzG⟩ := hGne
  have hFd := Complex.analyticOnNhd_univ_iff_differentiable.mp hF
  have hGd := Complex.analyticOnNhd_univ_iff_differentiable.mp hG
  have hFord : ∀ z, meromorphicOrderAt F z ≠ ⊤ := by
    intro z
    rw [(hF z (mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hFd hzF z]
  have hGord : ∀ z, meromorphicOrderAt G z ≠ ⊤ := by
    intro z
    rw [(hG z (mem_univ z)).meromorphicOrderAt_eq]
    simp [analyticOrderAt_ne_top_of_entire hGd hzG z]
  obtain ⟨K, hK⟩ := proximity_quotient_le hF hG hH hFord hGord hfac
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C := 3 * (6 * CG + 6 * CF + |K| / Real.log 2)
  refine ⟨C, by dsimp [C]; positivity, fun z => ?_⟩
  let R : ℝ := 2 * (1 + ‖z‖)
  have hz : 0 ≤ ‖z‖ := norm_nonneg z
  have hR : 1 ≤ R := by dsimp [R]; linarith
  have hshape : (1 + R) * Real.log (2 + R) ≤
      6 * ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    have hlinear : 1 + R ≤ 3 * (1 + ‖z‖) := by dsimp [R]; linarith
    have hlog : Real.log (2 + R) ≤ 2 * Real.log (2 + ‖z‖) := by
      calc
        Real.log (2 + R) ≤ Real.log ((2 + ‖z‖) ^ (2 : ℕ)) :=
          Real.log_le_log (by dsimp [R]; positivity) (by dsimp [R]; nlinarith)
        _ = 2 * Real.log (2 + ‖z‖) := by rw [Real.log_pow]; norm_num
    calc
      (1 + R) * Real.log (2 + R) ≤
          (3 * (1 + ‖z‖)) * (2 * Real.log (2 + ‖z‖)) :=
        mul_le_mul hlinear hlog (Real.log_nonneg (by linarith)) (by positivity)
      _ = _ := by ring
  have hKshape : K ≤ (|K| / Real.log 2) *
      ((1 + ‖z‖) * Real.log (2 + ‖z‖)) := by
    calc
      K ≤ |K| := le_abs_self K
      _ = (|K| / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (log_two_le_shape z) (by positivity)
  have hpF := proximity_le_orderOneWeight hF hCF.le hFb (by linarith : 0 ≤ R)
  have hpG := proximity_le_orderOneWeight hG hCG.le hGb (by linarith : 0 ≤ R)
  have hq := hK R hR
  have hlog := log_norm_le_three_mul_proximity hH hHzero z
  have hb : Real.log ‖H z‖ ≤ orderOneWeight C z := by
    change Real.log ‖H z‖ ≤ 3 * proximity H ⊤ R at hlog
    have hFshape := mul_le_mul_of_nonneg_left hshape hCF.le
    have hGshape := mul_le_mul_of_nonneg_left hshape hCG.le
    dsimp [C, orderOneWeight]
    nlinarith
  rw [← Real.exp_log (norm_pos_iff.mpr (hHzero z))]
  exact Real.exp_le_exp.mpr hb

end GaloisForLFunctions.HTGeometry
