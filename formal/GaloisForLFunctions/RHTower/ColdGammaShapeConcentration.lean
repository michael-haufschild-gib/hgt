import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureColdWatson
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Exact Gamma shape shift and joint concentration

Normalized Gaussian half-line averages of `f(x²)` realize Gamma shape `j+1/2`.
This file proves their exact centered second moment, a quantitative concentration bound,
convergence when degree and cold aperture grow together, and the integration-by-parts
shape-shift identity. Continuity, boundedness and differentiability hypotheses are explicit.

The literal theta specialization and the three finite differences needed for curvature
are separate obligations. These lemmas alone assert no theta curvature sign.
-/

open Real Set Filter Topology MeasureTheory
namespace RHTower.ColdGamma
noncomputable section

def kernel (L : ℝ) (j : ℕ) (x : ℝ) : ℝ := x^(2*j) * Real.exp (-L*x^2)
def moment (L : ℝ) (j : ℕ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), kernel L j x * f (x^2)
def average (L : ℝ) (j : ℕ) (f : ℝ → ℝ) : ℝ :=
  moment L j f / coldGaussianHalfMoment L j

theorem kernel_nonneg (L : ℝ) (j : ℕ) (x : ℝ) : 0 ≤ kernel L j x := by
  unfold kernel
  exact mul_nonneg (by rw [pow_mul]; positivity) (Real.exp_pos _).le

theorem integrable_kernel {L : ℝ} (hL : 0 < L) (j : ℕ) :
    IntegrableOn (kernel L j) (Ioi 0) := integrableOn_coldGaussianHalfMoment hL j

theorem integral_kernel {L : ℝ} (hL : 0 < L) (j : ℕ) :
    (∫ x in Ioi 0, kernel L j x) = coldGaussianHalfMoment L j :=
  integral_coldGaussianHalfMoment hL j

theorem integrable_moment {L : ℝ} (hL : 0 < L) (j : ℕ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {B : ℝ}
    (hB : ∀ y ≥ 0, |f y| ≤ B) :
    IntegrableOn (fun x => kernel L j x * f (x^2)) (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => f (x^2)) :=
    hf.comp_continuous (continuous_id.pow 2) fun x => sq_nonneg x
  have hk : Continuous (kernel L j) := by unfold kernel; fun_prop
  apply ((integrable_kernel hL j).mul_const B).mono' (hk.mul hc).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_of_nonneg (kernel_nonneg L j x)]
  exact mul_le_mul_of_nonneg_left (hB (x^2) (sq_nonneg x)) (kernel_nonneg L j x)

theorem moment_const {L : ℝ} (hL : 0 < L) (j : ℕ) (c : ℝ) :
    moment L j (fun _ => c) = coldGaussianHalfMoment L j * c := by
  rw [moment, integral_mul_const, integral_kernel hL]

theorem average_const {L : ℝ} (hL : 0 < L) (j : ℕ) (c : ℝ) :
    average L j (fun _ => c) = c := by
  rw [average, moment_const hL]
  field_simp [(coldGaussianHalfMoment_pos hL j).ne']

theorem moment_pow (L : ℝ) (j k : ℕ) :
    moment L j (fun y => y^k) = ∫ x in Ioi 0, kernel L (j+k) x := by
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp [kernel]
  simp only [Nat.mul_add, pow_add, pow_mul]
  ring

theorem average_id {L : ℝ} (hL : 0 < L) (j : ℕ) :
    average L j (fun y => y) = thetaCuspGaussianApertureGammaShape j / L := by
  rw [average, show moment L j (fun y => y) = moment L j (fun y => y^1) by simp]
  rw [moment_pow, integral_kernel hL, coldGaussianHalfMoment_succ hL]
  field_simp [(coldGaussianHalfMoment_pos hL j).ne']

theorem average_sq {L : ℝ} (hL : 0 < L) (j : ℕ) :
    average L j (fun y => y^2) =
      thetaCuspGaussianApertureGammaShape j * (thetaCuspGaussianApertureGammaShape j + 1) / L^2 := by
  rw [average, moment_pow, integral_kernel hL,
    show j+2 = (j+1)+1 by omega, coldGaussianHalfMoment_succ hL,
    coldGaussianHalfMoment_succ hL, thetaCuspGaussianApertureGammaShape_add]
  field_simp [(coldGaussianHalfMoment_pos hL j).ne']
  ring

theorem kernel_mul_pow (L : ℝ) (j k : ℕ) (x : ℝ) :
    kernel L j x * (x^2)^k = kernel L (j+k) x := by
  simp only [kernel, Nat.mul_add, pow_add, pow_mul]
  ring

theorem integrable_moment_pow {L : ℝ} (hL : 0 < L) (j k : ℕ) :
    IntegrableOn (fun x => kernel L j x * (x^2)^k) (Ioi 0) := by
  simpa only [kernel_mul_pow] using integrable_kernel hL (j+k)

theorem integrable_moment_centered {L : ℝ} (hL : 0 < L) (j : ℕ) (u : ℝ) :
    IntegrableOn (fun x => kernel L j x * (x^2-u)^2) (Ioi 0) := by
  have h0 := (integrable_kernel hL j).mul_const (u^2)
  have h1 := (integrable_moment_pow hL j 1).mul_const (2*u)
  have h2 := integrable_moment_pow hL j 2
  convert! h2.sub h1 |>.add h0 using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- Exact centered second moment in the squared coordinate. -/
theorem average_centered {L : ℝ} (hL : 0 < L) (j : ℕ) (u : ℝ) :
    average L j (fun y => (y-u)^2) =
      (thetaCuspGaussianApertureGammaShape j / L - u)^2 +
        thetaCuspGaussianApertureGammaShape j / L^2 := by
  have hid := average_id hL j
  have hsq := average_sq hL j
  have heq : moment L j (fun y => (y-u)^2) = moment L j (fun y => y^2) -
      2*u * moment L j (fun y => y) + coldGaussianHalfMoment L j * u^2 := by
    have hfun : (fun x => kernel L j x * (x^2-u)^2) =
        (fun x => kernel L j x * (x^2)^2 - 2*u*(kernel L j x*x^2) + kernel L j x*u^2) := by
      funext x
      ring
    rw [moment, hfun, integral_add, integral_sub, integral_const_mul, integral_mul_const,
      integral_kernel hL]
    · rfl
    · exact integrable_moment_pow hL j 2
    · simpa only [pow_one] using! (integrable_moment_pow hL j 1).const_mul (2*u)
    · exact (integrable_moment_pow hL j 2).sub (by
        simpa only [pow_one] using! (integrable_moment_pow hL j 1).const_mul (2*u))
    · exact (integrable_kernel hL j).mul_const (u^2)
  rw [average, heq, add_div, sub_div]
  change average L j (fun y => y^2) - _ + _ = _
  rw [hsq]
  have hmul : 2*u * moment L j (fun y => y) / coldGaussianHalfMoment L j =
      2*u * (thetaCuspGaussianApertureGammaShape j / L) := by
    rw [mul_div_assoc, ← hid]; rfl
  rw [hmul]
  field_simp [(coldGaussianHalfMoment_pos hL j).ne']
  ring

/-- Continuity and boundedness give a quadratic error envelope at any nonnegative point. -/
theorem exists_quadratic_error_bound {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {B u : ℝ} (hB : ∀ y ≥ 0, |f y| ≤ B) (hu : 0 ≤ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C ≥ 0, ∀ y ≥ 0, |f y-f u| ≤ ε + C*(y-u)^2 := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp (hf u hu) ε hε
  have hB0 : 0 ≤ B := (abs_nonneg (f u)).trans (hB u hu)
  refine ⟨2*B/δ^2, by positivity, ?_⟩
  intro y hy
  by_cases hnear : |y-u| < δ
  · have hh : |f y-f u| < ε := by
      simpa only [Real.dist_eq] using hclose hy (by simpa only [Real.dist_eq] using hnear)
    exact hh.le.trans (le_add_of_nonneg_right (by positivity))
  · have hfar : δ^2 ≤ (y-u)^2 := by
      have hh := le_of_not_gt hnear
      nlinarith [sq_abs (y-u)]
    have htri : |f y-f u| ≤ 2*B := by
      calc
        _ ≤ |f y| + |f u| := abs_sub _ _
        _ ≤ 2*B := by linarith [hB y hy, hB u hu]
    have hprod := mul_le_mul_of_nonneg_left hfar (show 0 ≤ 2*B/δ^2 by positivity)
    have heq : 2*B/δ^2*δ^2 = 2*B := by field_simp
    rw [heq] at hprod
    linarith

/-- Quantitative concentration bound; the full joint corner remains visible. -/
theorem average_error_le {L : ℝ} (hL : 0 < L) (j : ℕ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) {B u ε C : ℝ}
    (hB : ∀ y ≥ 0, |f y| ≤ B)
    (hbound : ∀ y ≥ 0, |f y-f u| ≤ ε+C*(y-u)^2) :
    |average L j f-f u| ≤ ε+C*((thetaCuspGaussianApertureGammaShape j/L-u)^2+
      thetaCuspGaussianApertureGammaShape j/L^2) := by
  let G := coldGaussianHalfMoment L j
  have hG : 0 < G := coldGaussianHalfMoment_pos hL j
  have hint := integrable_moment hL j hf hB
  have hc := (integrable_kernel hL j).mul_const (f u)
  have he : IntegrableOn (fun x => kernel L j x * (ε+C*(x^2-u)^2)) (Ioi 0) := by
    change Integrable (fun x => kernel L j x * (ε+C*(x^2-u)^2)) (volume.restrict (Ioi 0))
    convert! ((integrable_kernel hL j).mul_const ε).add
      ((integrable_moment_centered hL j u).const_mul C) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  have hn : ‖∫ x in Ioi 0, kernel L j x*(f (x^2)-f u)‖ ≤
      ∫ x in Ioi 0, kernel L j x*(ε+C*(x^2-u)^2) := by
    apply norm_integral_le_of_norm_le he
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg L j x)]
    exact mul_le_mul_of_nonneg_left (hbound (x^2) (sq_nonneg x)) (kernel_nonneg L j x)
  have hlhs : (∫ x in Ioi 0, kernel L j x*(f (x^2)-f u)) =
      moment L j f - G*f u := by
    simp_rw [mul_sub]
    rw [integral_sub hint hc, integral_mul_const, integral_kernel hL]
    rfl
  have hrhs : (∫ x in Ioi 0, kernel L j x*(ε+C*(x^2-u)^2)) =
      G*ε + C*moment L j (fun y => (y-u)^2) := by
    simp_rw [mul_add, mul_left_comm (kernel L j _) C]
    rw [integral_add ((integrable_kernel hL j).mul_const ε)
      ((integrable_moment_centered hL j u).const_mul C), integral_mul_const,
      integral_const_mul, integral_kernel hL]
    rfl
  rw [hlhs, hrhs, Real.norm_eq_abs] at hn
  have h := (div_le_div_of_nonneg_right hn hG.le)
  have heq : |moment L j f-G*f u|/G = |average L j f-f u| := by
    rw [← abs_of_pos hG, ← abs_div]
    congr 1
    rw [abs_of_pos hG]
    dsimp [average, G]
    field_simp [(coldGaussianHalfMoment_pos hL j).ne']
  rw [heq] at h
  have hr : (G*ε+C*moment L j (fun y => (y-u)^2))/G =
      ε+C*((thetaCuspGaussianApertureGammaShape j/L-u)^2+
        thetaCuspGaussianApertureGammaShape j/L^2) := by
    rw [add_div, mul_div_assoc C, show moment L j (fun y => (y-u)^2)/G =
      average L j (fun y => (y-u)^2) by rfl, average_centered hL]
    field_simp
  rwa [hr] at h


/-- Concentration along arbitrary coupled cold-aperture/degree sequences. -/
theorem tendsto_average {f : ℝ → ℝ} (hf : ContinuousOn f (Ici 0))
    {B u : ℝ} (hB : ∀ y ≥ 0, |f y| ≤ B) (hu : 0 ≤ u)
    {L : ℕ → ℝ} {j : ℕ → ℕ} (hL : ∀ n, 0 < L n)
    (hcold : Tendsto (fun n => (L n)⁻¹) atTop (𝓝 0))
    (hratio : Tendsto (fun n => thetaCuspGaussianApertureGammaShape (j n) / L n) atTop (𝓝 u)) :
    Tendsto (fun n => average (L n) (j n) f) atTop (𝓝 (f u)) := by
  have hvariance : Tendsto (fun n =>
      (thetaCuspGaussianApertureGammaShape (j n)/L n-u)^2+
      thetaCuspGaussianApertureGammaShape (j n)/(L n)^2) atTop (𝓝 0) := by
    have h := ((hratio.sub_const u).pow 2).add (hratio.mul hcold)
    convert! h using 1
    · funext n
      field_simp
    · ring
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := exists_quadratic_error_bound hf hB hu (half_pos hε)
  have hz : Tendsto (fun n => C*((thetaCuspGaussianApertureGammaShape (j n)/L n-u)^2+
      thetaCuspGaussianApertureGammaShape (j n)/(L n)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hvariance.const_mul C
  filter_upwards [hz.eventually (gt_mem_nhds (half_pos hε))] with n hn
  rw [Real.dist_eq]
  have hb := average_error_le (hL n) (j n) hf hB hbound
  linarith

/-- Boundary primitive whose integration yields the exact Gamma shape shift. -/
def boundary (L : ℝ) (j : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  x^(2*j+1) * Real.exp (-L*x^2) * f (x^2)

private theorem hasDerivAt_boundary (L : ℝ) (j : ℕ) {f f' : ℝ → ℝ}
    {x : ℝ} (hf : HasDerivAt f (f' (x^2)) (x^2)) :
    HasDerivAt (boundary L j f)
      (2*thetaCuspGaussianApertureGammaShape j * (kernel L j x*f (x^2)) -
        2*L*(kernel L (j+1) x*f (x^2)) + 2*(kernel L (j+1) x*f' (x^2))) x := by
  have hp := (hasDerivAt_id x).pow (2*j+1)
  have hs : HasDerivAt (fun t : ℝ => t^2) (2*x) x := by
    simpa only [id_eq, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, mul_one] using! (hasDerivAt_id x).pow 2
  have he := (hs.const_mul (-L)).exp
  have hh := (hp.mul he).mul (hf.comp x (h := fun t : ℝ => t^2) hs)
  convert! hh using 1
  simp only [kernel, thetaCuspGaussianApertureGammaShape, Function.comp_def,
    Pi.mul_apply, Pi.pow_apply, id_eq, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul,
    Nat.cast_ofNat, Nat.cast_one, mul_one, Nat.mul_add, pow_succ]
  ring

private theorem tendsto_boundary {L : ℝ} (hL : 0 < L) (j : ℕ) {f : ℝ → ℝ}
    {B : ℝ} (hB : ∀ y ≥ 0, |f y| ≤ B) :
    Tendsto (boundary L j f) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => x^(2*j+1)*Real.exp (-L*x^2)) atTop (𝓝 0) := by
    have h := (rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg hL ((2*j+1:ℕ):ℝ)).tendsto_zero_of_tendsto
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg
        (by norm_num : -(1/2:ℝ) < 0)))
    simpa only [Real.rpow_natCast] using h
  have h := bdd_le_mul_tendsto_zero' B (Eventually.of_forall fun x => hB (x^2) (sq_nonneg x)) hg
  convert! h using 1
  funext x
  unfold boundary
  ring

/-- Exact shape shift; differentiability is needed only on the positive half-line. -/
theorem average_shape_shift {L : ℝ} (hL : 0 < L) (j : ℕ)
    {f f' : ℝ → ℝ} (hf : ContinuousOn f (Ici 0)) (hf' : ContinuousOn f' (Ici 0))
    {B B' : ℝ} (hB : ∀ y ≥ 0, |f y| ≤ B) (hB' : ∀ y ≥ 0, |f' y| ≤ B')
    (hd : ∀ y > 0, HasDerivAt f (f' y) y) :
    average L (j+1) f - average L j f = (1/L)*average L (j+1) f' := by
  have hfc : Continuous (fun x : ℝ => f (x^2)) :=
    hf.comp_continuous (continuous_id.pow 2) fun x => sq_nonneg x
  have hb : Continuous (boundary L j f) := by
    unfold boundary
    exact (((continuous_id.pow (2*j+1)).mul
      (((continuous_id.pow 2).const_mul (-L)).rexp)).mul hfc)
  have hi0 := (integrable_moment hL j hf hB).const_mul (2*thetaCuspGaussianApertureGammaShape j)
  have hi1 := (integrable_moment hL (j+1) hf hB).const_mul (2*L)
  have hi2 := (integrable_moment hL (j+1) hf' hB').const_mul 2
  have hint : IntegrableOn (fun x =>
      2*thetaCuspGaussianApertureGammaShape j * (kernel L j x*f (x^2)) -
        2*L*(kernel L (j+1) x*f (x^2)) + 2*(kernel L (j+1) x*f' (x^2))) (Ioi 0) := by
    exact hi0.sub hi1 |>.add hi2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hb.continuousWithinAt
    (fun x hx => hasDerivAt_boundary L j (hd (x^2) (sq_pos_of_pos hx)))
    hint (tendsto_boundary hL j hB)
  simp only [boundary, zero_pow (by omega : 2*j+1 ≠ 0), zero_mul, sub_zero] at h
  have hi01 : Integrable (fun x => 2*thetaCuspGaussianApertureGammaShape j * (kernel L j x*f (x^2)) -
      2*L*(kernel L (j+1) x*f (x^2))) (volume.restrict (Ioi 0)) := hi0.sub hi1
  rw [integral_add hi01 hi2, integral_sub hi0 hi1,
    integral_const_mul, integral_const_mul, integral_const_mul] at h
  change 2*thetaCuspGaussianApertureGammaShape j * moment L j f -
    2*L*moment L (j+1) f + 2*moment L (j+1) f' = 0 at h
  rw [average, average, average, coldGaussianHalfMoment_succ hL]
  field_simp [hL.ne', (coldGaussianHalfMoment_pos hL j).ne',
    (thetaCuspGaussianApertureGammaShape_pos j).ne']
  nlinarith

end
end RHTower.ColdGamma
