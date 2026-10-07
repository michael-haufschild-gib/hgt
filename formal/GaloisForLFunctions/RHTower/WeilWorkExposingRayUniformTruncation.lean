import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality
import GaloisForLFunctions.RHTower.WeilFullConeMinorantRigidity

/-!
# Uniform theta-scale truncation of the literal exposing source

The autocorrelation error of the cutoff Riemann kernel is bounded by
`C * exp (-exp (2*(L-1))) * exp (-(2*|y|))`.
The bound remains uniform after both polar shifts, for every `c` in `[0,1]`.
The normalized archimedean energies converge to their actual von Mangoldt
pairings at the same double-exponential cutoff rate, uniformly in `c`.

These are unconditional source estimates; no zero-side sign is assumed.
They supply the error budget for natural-aperture exact finite realization.
They do not prove the universal exposing-ray energy lower bound.
Paper proof: docs/reports/weil-work/results/02-exposing-ray/UNIFORM-TRUNCATION-PROOF.md.
-/

open MeasureTheory Filter Topology Set Real Zeta23
noncomputable section
namespace RHTower
namespace ExposingRayTruncation

private theorem phi_weighted {c : ℝ} (hc : 0 < c) (hcπ : c < π) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, riemannKernelReal x ≤
      B * exp (-(c * exp (2 * |x|))) * exp (-(2*|x|)) := by
  let d := π - c
  have hd : 0 < d := by dsimp [d]; linarith
  let B := (101 / 100 : ℝ) * (4 * π ^ 2) * (24 / d ^ 4)
  refine ⟨B, by dsimp [B]; positivity, fun x => ?_⟩
  let u := |x|
  let X := exp (2 * u)
  have hu : 0 ≤ u := abs_nonneg x
  have hX : 0 < X := exp_pos _
  have hlead : riemannLeadTerm u ≤ 4 * π ^ 2 * exp (9 * u / 2) * exp (-(π * X)) := by
    unfold riemannLeadTerm
    have hp : 4 * π ^ 2 * exp (2 * u) - 6 * π ≤ 4 * π ^ 2 * exp (2 * u) := by
      linarith [Real.pi_pos]
    calc _ ≤ exp (5 * u / 2) * (4 * π ^ 2 * exp (2 * u)) * exp (-π * exp (2 * u)) := by gcongr
      _ = _ := by dsimp [X]; rw [show exp (5*u/2) * (4*π^2*exp (2*u)) =
          4*π^2*(exp (5*u/2)*exp (2*u)) by ring, ← exp_add]; congr 3 <;> ring
  have he : exp (9 * u / 2) ≤ X ^ 4 * exp (-(2*u)) := by
    dsimp [X]
    rw [← exp_nat_mul, ← exp_add]
    apply exp_le_exp.mpr; norm_num; linarith
  have ht := Real.pow_div_factorial_le_exp (x := d * X) (by positivity) 4
  norm_num [Nat.factorial] at ht
  have hpay : X ^ 4 * exp (-(d * X)) ≤ 24 / d ^ 4 := by
    have hx := exp_pos (-(d*X))
    have heq : exp (d*X) * exp (-(d*X)) = 1 := by rw [← exp_add]; simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pow d X 4]
  calc riemannKernelReal x ≤ (101/100) * riemannLeadTerm u := (riemannKernelReal_sandwich x).2
    _ ≤ (101/100) * (4 * π ^ 2 * exp (9*u/2) * exp (-(π*X))) := by gcongr
    _ ≤ (101/100) * (4 * π ^ 2 * (X^4*exp (-(2*u))) * exp (-(π*X))) := by gcongr
    _ = (101/100) * (4*π^2) * (X^4*exp (-(d*X))) * exp (-(c*X)) * exp (-(2*u)) := by
      have heq : exp (-(π*X)) = exp (-(d*X)) * exp (-(c*X)) := by
        rw [← exp_add]; congr 1; dsimp [d]; ring
      rw [heq]; ring
    _ ≤ (101/100) * (4*π^2) * (24/d^4) * exp (-(c*X)) * exp (-(2*u)) := by gcongr
    _ = _ := rfl

private theorem defect_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ L t : ℝ,
      |truncatedRiemannKernelReal L t - riemannKernelReal t| ≤
        B * exp (-exp (2*(L-1))) * exp (-(2*|t|)) := by
  obtain ⟨B, hB, hPhi⟩ := phi_weighted (c := 1) (by norm_num)
    (by linarith [Real.pi_gt_three])
  refine ⟨B, hB, fun L t => ?_⟩
  have hp := (riemannKernelReal_pos t).le
  have hb0 := bulkCutoff_nonneg L t
  have hb1 := bulkCutoff_le_one L t
  have hsign : 0 ≤ riemannKernelReal t - truncatedRiemannKernelReal L t := by
    unfold truncatedRiemannKernelReal; nlinarith
  rw [abs_sub_comm, abs_of_nonneg hsign]
  by_cases ht : |t| ≤ L-1
  · simp only [truncatedRiemannKernelReal, bulkCutoff_eq_one ht, mul_one, sub_self]
    positivity
  · have ht' : L-1 ≤ |t| := le_of_lt (lt_of_not_ge ht)
    calc _ ≤ riemannKernelReal t := by
          unfold truncatedRiemannKernelReal; nlinarith
      _ ≤ B * exp (-exp (2*|t|)) * exp (-(2*|t|)) := by simpa using hPhi t
      _ ≤ _ := by gcongr

/-- Cutoff error retains the theta scale, uniformly at every physical lag. -/
theorem autocorr_error :
    ∃ C : ℝ, 0 < C ∧ ∀ L y : ℝ,
      |crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y -
          riemannKernelAutocorr y| ≤
        C * exp (-exp (2*(L-1))) * exp (-(2*|y|)) := by
  obtain ⟨B, hB, hD⟩ := defect_bound
  obtain ⟨C, hC, hPhi⟩ := exists_riemannKernelReal_le
  let J := ∫ v : ℝ, exp (-(2*|v|))
  have hJ : 0 ≤ J := integral_nonneg fun _ => (exp_pos _).le
  refine ⟨2*B*C*J+1, by positivity, fun L y => ?_⟩
  let E := exp (-exp (2*(L-1)))
  have hE : 0 < E := exp_pos _
  have hPhi4 : ∀ t, |riemannKernelReal t| ≤ C*exp (-(4*|t|)) := fun t => by
    rw [abs_of_pos (riemannKernelReal_pos t)]; exact hPhi t
  have hPhi2 : ∀ t, |riemannKernelReal t| ≤ C*exp (-(2*|t|)) := fun t =>
    (hPhi4 t).trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr
      (by linarith [abs_nonneg t])) hC)
  have hU4 : ∀ t, |truncatedRiemannKernelReal L t| ≤ C*exp (-(4*|t|)) := by
    intro t
    rw [abs_of_nonneg (truncatedRiemannKernelReal_nonneg L t)]
    have := (riemannKernelReal_sub_truncated_le hPhi L t).1
    linarith [hPhi t]
  have hD2 : ∀ t, |truncatedRiemannKernelReal L t - riemannKernelReal t| ≤
      (B*E)*exp (-(2*|t|)) := hD L
  have hUc := continuous_truncatedRiemannKernelReal L
  have hUs := hasCompactSupport_truncatedRiemannKernelReal L
  have hDc : Continuous (fun t => truncatedRiemannKernelReal L t-riemannKernelReal t) :=
    hUc.sub continuous_riemannKernelReal
  have iUU := integrable_translate_prod hUc hUs hUc y
  have iPP := integrable_riemannKernel_mul_shift continuous_riemannKernelReal hC hPhi2 y
  have i1 := integrable_mul_translate_right hDc hUc hUs y
  have i2 : Integrable fun t => riemannKernelReal t *
      (truncatedRiemannKernelReal L (t-y)-riemannKernelReal (t-y)) := by
    have h := (integrable_riemannKernel_mul_shift hDc (by positivity) hD2 (-y)).comp_sub_right y
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [show t-y- -y=t by ring]; ring
  have hsplit : crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y -
      riemannKernelAutocorr y =
      (∫ t, (truncatedRiemannKernelReal L t-riemannKernelReal t)*truncatedRiemannKernelReal L (t-y)) +
      ∫ t, riemannKernelReal t*(truncatedRiemannKernelReal L (t-y)-riemannKernelReal (t-y)) := by
    simp only [riemannKernelAutocorr, crossCorr]
    rw [← integral_sub iUU iPP, ← integral_add i1 i2]
    exact integral_congr_ae (Eventually.of_forall fun t => by ring)
  have hswap : (∫ t, riemannKernelReal t*
      (truncatedRiemannKernelReal L (t-y)-riemannKernelReal (t-y))) =
      ∫ t, (truncatedRiemannKernelReal L t-riemannKernelReal t)*riemannKernelReal (t- -y) := by
    rw [← integral_add_right_eq_self (μ := volume) (fun t => riemannKernelReal t*
      (truncatedRiemannKernelReal L (t-y)-riemannKernelReal (t-y))) y]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [show t+y-y=t by ring, show t- -y=t+y by ring]; ring
  have b1 := abs_integral_mul_shift_le (by positivity) hC hD2 hU4 y
  have b2 := abs_integral_mul_shift_le (by positivity) hC hD2 hPhi4 (-y)
  rw [abs_neg] at b2
  rw [hsplit, hswap]
  calc _ ≤ |∫ t, (truncatedRiemannKernelReal L t-riemannKernelReal t)*truncatedRiemannKernelReal L (t-y)| +
        |∫ t, (truncatedRiemannKernelReal L t-riemannKernelReal t)*riemannKernelReal (t- -y)| := abs_add_le _ _
    _ ≤ (2*B*C*J+1)*E*exp (-(2*|y|)) := by dsimp [J] at *; nlinarith [exp_pos (-(2*|y|))]

private theorem polar_factor_le {c : ℝ} (hc1 : c ≤ 1) :
    (1+2*polarWeight c*exp (2*c))^2 ≤ (1+exp 2)^2 := by
  have hp := polarWeight_le_half c
  have hp0 := (polarWeight_pos c).le
  have he : exp (2*c) ≤ exp 2 := exp_le_exp.mpr (by linarith)
  have hpe : 2*polarWeight c*exp (2*c) ≤ exp 2 := by nlinarith [exp_pos (2*c)]
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- Uniformity across every shift in the literal exposing mixture. -/
theorem polar_autocorr_error :
    ∃ C : ℝ, 0 < C ∧ ∀ L c : ℝ, 0 ≤ c → c ≤ 1 → ∀ y : ℝ,
      |crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c) y -
          polarExposingKernel c y| ≤
        C * exp (-exp (2*(L-1))) * exp (-(2*|y|)) := by
  obtain ⟨C,hC,hD⟩ := autocorr_error
  refine ⟨C*(1+exp 2)^2, by positivity, fun L c hc hc1 y => ?_⟩
  have hp := abs_polarShift_polarShift_le hc (hD L) y
  have heq : crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c) y -
      polarExposingKernel c y = polarShift c (polarShift c (fun y =>
        crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y - riemannKernelAutocorr y)) y := by
    rw [crossCorr_polarRiemannDifferenceReal_self]
    simp only [polarExposingKernel, polarShift]; ring
  rw [heq]
  calc _ ≤ (C*exp (-exp (2*(L-1))))*(1+2*polarWeight c*exp (2*c))^2*exp (-(2*|y|)) := hp
    _ ≤ (C*exp (-exp (2*(L-1))))*(1+exp 2)^2*exp (-(2*|y|)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (polar_factor_le hc1) (by positivity)) (by positivity)
    _ = _ := by ring

/-- The entire actual von Mangoldt pairing converges uniformly in the polar shift. -/
theorem polar_pairing_error :
    ∃ C : ℝ, 0 < C ∧ ∀ L c : ℝ, 0 ≤ c → c ≤ 1 →
      |atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) -
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (polarExposingKernel c)| ≤
          C * exp (-exp (2*(L-1))) := by
  let w : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n
  have hw : Summable fun n => |w n|/(n:ℝ)^2 := by
    refine summable_vonMangoldt_div_sq.congr fun n => ?_
    simp only [w, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  let S := ∑' n : ℕ, |w n|/(n:ℝ)^2
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  obtain ⟨C,hC,hD⟩ := polar_autocorr_error
  obtain ⟨_,C₂,_,hC₂,_,hK⟩ := exists_riemannKernelAutocorr_decay
  refine ⟨2*C*S+1, by positivity, fun L c hc hc1 => ?_⟩
  let E := exp (-exp (2*(L-1)))
  let A := crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)
  let K := polarExposingKernel c
  let D := fun y => A y-K y
  have hD' : ∀ y, |D y| ≤ (C*E)*exp (-(2*|y|)) := hD L c hc hc1
  have hK' : ∀ y, |K y| ≤ (C₂*(1+exp 2)^2)*exp (-(2*|y|)) := by
    intro y
    refine (abs_polarShift_polarShift_le hc hK y).trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (polar_factor_le hc1) hC₂) (by positivity)
  have hA' : ∀ y, |A y| ≤ (C₂*(1+exp 2)^2+C*E)*exp (-(2*|y|)) := by
    intro y
    have ht : |A y| ≤ |D y|+|K y| := by
      simpa [D] using abs_add_le (A y-K y) (K y)
    have hd := hD' y
    have hk := hK' y
    nlinarith
  obtain ⟨sA,_⟩ := summable_atomPairing_of_decay hw hA'
  obtain ⟨sK,_⟩ := summable_atomPairing_of_decay hw hK'
  obtain ⟨_,bD⟩ := summable_atomPairing_of_decay hw hD'
  have hsub : atomPairing w A-atomPairing w K=atomPairing w D := by
    unfold atomPairing
    rw [← sA.tsum_sub sK]
    exact tsum_congr fun n => by dsimp [D]; ring
  change |atomPairing w A-atomPairing w K| ≤ (2*C*S+1)*E
  rw [hsub]
  calc _ ≤ 2*(C*E)*S := bD
    _ ≤ _ := by have := exp_pos (-exp (2*(L-1))); dsimp [E]; nlinarith

private theorem zero_side_error :
    ∃ M L₀ : ℝ, 0 ≤ M ∧ ∀ L : ℝ, L₀ ≤ L →
      (5/4)*zetaInvSqSum*truncatedRiemannTailEnergy L^2 ≤ M*exp (-exp (2*(L-1))) := by
  obtain ⟨Λ,hΛ0,hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨M,hM,hMI⟩ := exists_integral_norm_sq_truncatedRiemannKernel_le
  let Ystar := max 100 (log (720*nearRadicalConst zetaInvSqSum Λ+1))
  have hYstar : 0 < Ystar := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M,1+|log Ystar|/2,hM,fun L hL => ?_⟩
  let Y := exp (2*(L-1))
  have hY : Ystar ≤ Y := by
    calc Ystar = exp (log Ystar) := (exp_log hYstar).symm
      _ ≤ Y := exp_le_exp.mpr (by have := le_abs_self (log Ystar); linarith)
  have hY100 : 100 ≤ Y := (le_max_left _ _).trans hY
  have hYlog : log (720*nearRadicalConst zetaInvSqSum Λ+1) ≤ Y :=
    (le_max_right _ _).trans hY
  have hkY : ((0+2:ℕ):ℝ)+1 ≤ Y/10 := by norm_num; linarith
  have hW := nearRadicalEnergy_le_ratio L hΛ (by dsimp [Y] at hY100; linarith) hkY
  have hr := nearRadical_ratio_le (k:=0+2) zetaInvSqSum_nonneg hΛ0 hkY hY100 hYlog
  have hI : 0 ≤ ∫ u : ℝ, ‖truncatedRiemannKernel L u‖^2 := integral_nonneg fun _ => by positivity
  calc _ ≤ exp (-Y)*(∫ u : ℝ, ‖truncatedRiemannKernel L u‖^2) :=
      hW.trans (mul_le_mul_of_nonneg_right hr hI)
    _ ≤ exp (-Y)*M := mul_le_mul_of_nonneg_left (hMI L) (exp_pos _).le
    _ = _ := by ring

/-- Uniform source energy convergence at the same double-exponential cutoff scale.
No sign of the zero-side form is used. -/
theorem archimedean_error :
    ∃ C L₀ : ℝ, 0 < C ∧ ∀ L : ℝ, L₀ ≤ L → ∀ c : ℝ, 0 ≤ c → c ≤ 1 →
      |archEnergy (fun u => (polarRiemannDifferenceReal L c u : ℂ))/(2*π) -
        atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (polarExposingKernel c)| ≤
          C * exp (-exp (2*(L-1))) := by
  obtain ⟨M,L₀,hM,hZ⟩ := zero_side_error
  obtain ⟨C,hC,hP⟩ := polar_pairing_error
  obtain ⟨Λ,_,hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  refine ⟨9*M+C,L₀,by positivity,fun L hL c hc hc1 => ?_⟩
  have hz := norm_W_polarRiemannDifference_le L hc hΛ
  rw [polarRiemannDifference_eq] at hz
  have hr := (Complex.abs_re_le_norm _).trans hz
  have henergy := archEnergy_polarRiemannDifference_eq L hc
  have heq : archEnergy (fun u => (polarRiemannDifferenceReal L c u : ℂ))/(2*π) =
      (zetaZeroConfig.W (fun u => (polarRiemannDifferenceReal L c u : ℂ))
        (fun u => (polarRiemannDifferenceReal L c u : ℂ))).re +
      atomPairing (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (crossCorr (polarRiemannDifferenceReal L c) (polarRiemannDifferenceReal L c)) := by
    rw [henergy]
    field_simp
  rw [heq, add_sub_assoc]
  refine (abs_add_le _ _).trans ?_
  have hzero := hZ L hL
  have hpair := hP L c hc hc1
  nlinarith

end ExposingRayTruncation
end RHTower
