import GaloisForLFunctions.RHTower.ColdGammaShapeConcentration

/-!
# Falling Euler jets and exact Gaussian moment differences

Gaussian half-line integration by parts intertwines a degree shift with the spatial
Euler derivative. The second and third finite-difference identities retain the exact
Gamma factors. These identities avoid differentiating a square-root coordinate at zero.
-/

open Real Set Filter Topology MeasureTheory
namespace RHTower.ColdGamma
noncomputable section

def sourceMoment (L : ℝ) (j : ℕ) (H : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), kernel L j x * H x

def sourceAverage (L : ℝ) (j : ℕ) (H : ℝ → ℝ) : ℝ :=
  sourceMoment L j H / coldGaussianHalfMoment L j

theorem integrable_sourceMoment {L : ℝ} (hL : 0 < L) (j : ℕ)
    {H : ℝ → ℝ} (hH : Continuous H) {B : ℝ} (hB : ∀ x, |H x| ≤ B) :
    IntegrableOn (fun x => kernel L j x * H x) (Ioi 0) := by
  have hk : Continuous (kernel L j) := by unfold kernel; fun_prop
  apply ((integrable_kernel hL j).mul_const B).mono' (hk.mul hH).aestronglyMeasurable
  filter_upwards [] with x
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg L j x)]
  exact mul_le_mul_of_nonneg_left (hB x) (kernel_nonneg L j x)

theorem sourceAverage_eq_average (L : ℝ) (j : ℕ) (H : ℝ → ℝ) :
    sourceAverage L j H = average L j (fun y => H (Real.sqrt y)) := by
  unfold sourceAverage average sourceMoment moment
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Real.sqrt_sq hx.le]

theorem tendsto_sourceAverage {H : ℝ → ℝ} (hH : Continuous H)
    {B u : ℝ} (hB : ∀ x, |H x| ≤ B) (hu : 0 ≤ u)
    {L : ℕ → ℝ} {j : ℕ → ℕ} (hL : ∀ n, 0 < L n)
    (hcold : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0))
    (hratio : Tendsto (fun n => thetaCuspGaussianApertureGammaShape (j n)/L n) atTop (𝓝 u)) :
    Tendsto (fun n => sourceAverage (L n) (j n) H) atTop (𝓝 (H (Real.sqrt u))) := by
  simp only [sourceAverage_eq_average]
  exact tendsto_average (hH.comp Real.continuous_sqrt).continuousOn
    (fun y _ => hB (Real.sqrt y)) hu hL hcold hratio

def sourceBoundary (L : ℝ) (j : ℕ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  x^(2*j+1)*Real.exp (-L*x^2)*H x

private theorem hasDerivAt_sourceBoundary (L : ℝ) (j : ℕ) {H E : ℝ → ℝ}
    {x d : ℝ} (hd : HasDerivAt H d x) (he : x*d=2*E x) :
    HasDerivAt (sourceBoundary L j H)
      (2*thetaCuspGaussianApertureGammaShape j*(kernel L j x*H x) -
        2*L*(kernel L (j+1) x*H x) + 2*(kernel L j x*E x)) x := by
  have hp := (hasDerivAt_id x).pow (2*j+1)
  have hs : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one] using! (hasDerivAt_id x).pow 2
  have hexp := (hs.const_mul (-L)).exp
  have hh := (hp.mul hexp).mul hd
  convert! hh using 1
  simp only [kernel, thetaCuspGaussianApertureGammaShape, Pi.mul_apply, Pi.pow_apply,
    id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one, mul_one, Nat.mul_add, pow_succ]
  simp only [pow_zero, one_mul]
  linear_combination -(x^(2*j)*Real.exp (-L*(x*x)))*he

private theorem tendsto_sourceBoundary {L : ℝ} (hL : 0 < L) (j : ℕ) {H : ℝ → ℝ}
    {B : ℝ} (hB : ∀ x, |H x| ≤ B) :
    Tendsto (sourceBoundary L j H) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x^(2*j+1)*Real.exp (-L*x^2)) atTop (𝓝 0) := by
    have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hL ((2*j+1:ℕ):ℝ)).tendsto_zero_of_tendsto
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by norm_num : -(1/2:ℝ) < 0)))
    simpa only [Real.rpow_natCast] using h
  have h := bdd_le_mul_tendsto_zero' B (Eventually.of_forall hB) hg
  convert! h using 1
  funext x
  unfold sourceBoundary
  ring

/-- Euler form of Gamma shape shift; no square-root derivative at zero is used. -/
theorem sourceAverage_euler_shift {L : ℝ} (hL : 0 < L) (j : ℕ)
    {H E : ℝ → ℝ} (hH : Continuous H) (hE : Continuous E)
    {B C : ℝ} (hB : ∀ x, |H x| ≤ B) (hC : ∀ x, |E x| ≤ C)
    (hd : ∀ x > 0, ∃ d, HasDerivAt H d x ∧ x*d=2*E x) :
    thetaCuspGaussianApertureGammaShape j *
      (sourceAverage L (j+1) H - sourceAverage L j H) = sourceAverage L j E := by
  have hb : Continuous (sourceBoundary L j H) := by
    unfold sourceBoundary
    exact (((continuous_id.pow (2*j+1)).mul
      (((continuous_id.pow 2).const_mul (-L)).rexp)).mul hH)
  have hi0 := (integrable_sourceMoment hL j hH hB).const_mul (2*thetaCuspGaussianApertureGammaShape j)
  have hi1 := (integrable_sourceMoment hL (j+1) hH hB).const_mul (2*L)
  have hi2 := (integrable_sourceMoment hL j hE hC).const_mul 2
  have hi01 : Integrable (fun x => 2*thetaCuspGaussianApertureGammaShape j*(kernel L j x*H x) -
      2*L*(kernel L (j+1) x*H x)) (volume.restrict (Ioi 0)) := hi0.sub hi1
  have hint : IntegrableOn (fun x =>
      2*thetaCuspGaussianApertureGammaShape j*(kernel L j x*H x) -
        2*L*(kernel L (j+1) x*H x) + 2*(kernel L j x*E x)) (Ioi 0) := hi01.add hi2
  have hderiv : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (sourceBoundary L j H)
      (2*thetaCuspGaussianApertureGammaShape j*(kernel L j x*H x) -
        2*L*(kernel L (j+1) x*H x) + 2*(kernel L j x*E x)) x := by
    intro x hx
    obtain ⟨d, hd, he⟩ := hd x hx
    exact hasDerivAt_sourceBoundary L j hd he
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hb.continuousWithinAt hderiv hint
    (tendsto_sourceBoundary hL j hB)
  simp only [sourceBoundary, zero_pow (by omega : 2*j+1 ≠ 0), zero_mul, sub_zero] at h
  rw [integral_add hi01 hi2, integral_sub hi0 hi1,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  change 2*thetaCuspGaussianApertureGammaShape j*sourceMoment L j H -
    2*L*sourceMoment L (j+1) H + 2*sourceMoment L j E = 0 at h
  rw [sourceAverage, sourceAverage, sourceAverage, coldGaussianHalfMoment_succ hL]
  field_simp [hL.ne', (coldGaussianHalfMoment_pos hL j).ne',
    (thetaCuspGaussianApertureGammaShape_pos j).ne']
  nlinarith


theorem sourceAverage_add {L : ℝ} (hL : 0 < L) (j : ℕ)
    {F H : ℝ → ℝ} (hF : Continuous F) (hH : Continuous H)
    {B C : ℝ} (hB : ∀ x, |F x| ≤ B) (hC : ∀ x, |H x| ≤ C) :
    sourceAverage L j (fun x => F x+H x) = sourceAverage L j F + sourceAverage L j H := by
  unfold sourceAverage sourceMoment
  simp_rw [mul_add]
  rw [integral_add (integrable_sourceMoment hL j hF hB) (integrable_sourceMoment hL j hH hC), add_div]

theorem sourceAverage_const_mul (L : ℝ) (j : ℕ) (c : ℝ) (H : ℝ → ℝ) :
    sourceAverage L j (fun x => c*H x) = c*sourceAverage L j H := by
  unfold sourceAverage sourceMoment
  simp_rw [mul_left_comm (kernel L j _) c]
  rw [integral_const_mul, mul_div_assoc]

/-- Two exact shape differences from the Euler recurrence. -/
theorem falling_euler_difference_two (A b0 b1 b2 c0 c1 d0 : ℝ)
    (h0 : A*(b1-b0)=c0) (h1 : (A+1)*(b2-b1)=c1)
    (hc : A*(c1-c0)=d0+c0) :
    A*(A+1)*(b2-2*b1+b0)=d0 := by
  linear_combination A*h1-(A+1)*h0+hc

/-- Third exact shape difference; no limiting argument is used. -/
theorem falling_euler_difference_three (A b0 b1 b2 b3 d0 d1 e0 : ℝ)
    (h0 : A*(A+1)*(b2-2*b1+b0)=d0)
    (h1 : (A+1)*(A+2)*(b3-2*b2+b1)=d1)
    (hd : A*(d1-d0)=e0+2*d0) :
    A*(A+1)*(A+2)*(b3-3*b2+3*b1-b0)=e0 := by
  linear_combination A*h1-(A+2)*h0+hd

end
end RHTower.ColdGamma
