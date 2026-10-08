import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorReciprocalCutoff

/-!
# Actual compact upper-tail limits

The second-derivative pairing converges with every product-rule error
controlled by an integrable Mellin weight and a slowly dilated cutoff jet.
The constant term is identified by integration by parts, including its sign.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

/-- A compact test exhausting the smooth upper tail. -/
def mellinTailTest (ψ : ℝ → ℂ) (s : ℂ) (R x : ℝ) : ℂ :=
  ψ x * ((1 - ψ (R⁻¹ * x)) * (x : ℂ) ^ (s - 1))

private lemma tail_first_deriv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x =
      iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 1) +
        ψ x * ((s - 1) * (x : ℂ) ^ (s - 2)) := by
  have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - 1))
      ((s - 1) * (x : ℂ) ^ (s - 2)) x := by
    by_cases hs : s - 1 = 0
    · simp only [hs, Complex.cpow_zero, zero_mul]
      exact hasDerivAt_const x 1
    simpa only [show s - 1 - 1 = s - 2 by ring] using
      hasDerivAt_ofReal_cpow_const hx.ne' hs
  simpa only [iteratedDeriv_one] using
    ((hψ.differentiable (by simp) x).hasDerivAt.fun_mul hp).deriv

private lemma tail_second_product {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    (s : ℂ) (R : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    z * iteratedDeriv 2 (mellinTailTest ψ s R) x =
      z * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x -
      ((z * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x) * ψ (R⁻¹ * x) +
      (2 * (z * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2) +
        (s - 1) * ((x : ℂ) ^ (s - 3) * (z * ψ x)))) *
          ((x : ℂ) * iteratedDeriv 1 (fun y : ℝ => ψ (R⁻¹ * y)) x) +
      ((x : ℂ) ^ (s - 3) * (z * ψ x)) *
        ((x : ℂ) ^ 2 * iteratedDeriv 2 (fun y : ℝ => ψ (R⁻¹ * y)) x)) := by
  let w : ℝ → ℂ := fun y => ψ y * (y : ℂ) ^ (s - 1)
  let η : ℝ → ℂ := fun y => ψ (R⁻¹ * y)
  have hw : ContDiff ℝ ∞ w := hψ.contDiff_mul_cpow (s - 1)
  have hη : ContDiff ℝ ∞ η := hψ.smooth.comp (contDiff_const.mul contDiff_id)
  have he : mellinTailTest ψ s R = w - w * η := by
    funext y
    dsimp only [mellinTailTest, w, η, Pi.sub_apply, Pi.mul_apply]
    ring
  have hs := iteratedDeriv_sub (n := 2) (x := x)
    (hw.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top))
    ((hw.mul hη).contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hp := iteratedDeriv_mul (n := 2) (x := x)
    (hw.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top))
    (hη.contDiffAt.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  have hprod : iteratedDeriv 2 (w * η) x =
      iteratedDeriv 2 w x * η x + 2 * iteratedDeriv 1 w x * iteratedDeriv 1 η x +
        w x * iteratedDeriv 2 η x := by
    simpa [Finset.sum_range_succ, Nat.choose, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using hp
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : (x : ℂ) ^ (s - 2) = (x : ℂ) ^ (s - 3) * (x : ℂ) := by
    simpa only [Complex.cpow_one, show s - 3 + 1 = s - 2 by ring] using
      Complex.cpow_add (s - 3) 1 hxC
  have h2 : (x : ℂ) ^ (s - 1) = (x : ℂ) ^ (s - 3) * (x : ℂ) ^ 2 := by
    simpa only [Complex.cpow_two, show s - 3 + (2 : ℂ) = s - 1 by ring] using
      Complex.cpow_add (s - 3) 2 hxC
  rw [he]
  simp only [Pi.mul_def] at hs hprod ⊢
  rw [hs, hprod]
  dsimp only [w, η]
  rw [tail_first_deriv hψ.smooth s hx, h1, h2]
  ring

private lemma integrable_slow_jet {ψ G : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    (hG : IntegrableOn G (Ioi 0)) (n : ℕ) (R : ℝ) :
    IntegrableOn (fun x : ℝ => G x *
      ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := hψ.dilate_weighted_iteratedDeriv_bounded n
  have hs : ContDiff ℝ ∞ (fun y : ℝ => ψ (R⁻¹ * y)) :=
    hψ.smooth.comp (contDiff_const.mul contDiff_id)
  exact hG.mul_bdd
    (((Complex.continuous_ofReal.pow n).mul
      (hs.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞))))).aestronglyMeasurable)
    (Eventually.of_forall (hC R⁻¹))

/-- The actual compact upper tests converge in both primitive and constant terms. -/
theorem tendsto_mellinTail_primitive_integrals {F ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun R : ℝ => A * (∫ x : ℝ in Ioi 0, mellinTailTest ψ s R x) +
      ∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (mellinTailTest ψ s R) x) atTop
      (𝓝 (A * (∫ x : ℝ in Ioi 0, ψ x * (x : ℂ) ^ (s - 1)) +
        ∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (fun y : ℝ => ψ y * (y : ℂ) ^ (s - 1)) x)) := by
  let w : ℝ → ℂ := fun x => ψ x * (x : ℂ) ^ (s - 1)
  let G0 : ℝ → ℂ := fun x => F x * iteratedDeriv 2 w x
  let G2 : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 3) * (F x * ψ x)
  let G1 : ℝ → ℂ := fun x => 2 * (F x * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2) + (s - 1) * G2 x)
  have hi0 : IntegrableOn G0 (Ioi 0) := (integral_primitive_cutoff_cpow hψ hF hB (by linarith)).1
  have hi2 : IntegrableOn G2 (Ioi 0) := by
    simpa only [G2, MellinConvergent, smul_eq_mul, show s - 2 - 1 = s - 3 by ring] using
      (hψ.mellin_mul hF hB (s := s - 2) (by simpa using (show s.re - 2 < 0 by linarith))).1
  have hiDer : IntegrableOn (fun x : ℝ => F x * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm, show s - 1 - 1 = s - 2 by ring] using
      (hψ.mellin_mul_iteratedDeriv hF (by decide : 1 ≠ 0) (s - 1)).1
  have hi1 : IntegrableOn G1 (Ioi 0) := (hiDer.add (hi2.const_mul (s - 1))).const_mul 2
  let J : ℕ → (ℝ → ℂ) → ℝ → ℂ := fun n G R =>
    ∫ x : ℝ in Ioi 0, G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R⁻¹ * y)) x)
  have hJ0 : Tendsto (J 0 G0) atTop (𝓝 0) := tendsto_integral_slow_weighted_iteratedDeriv hψ hi0 0
  have hJ1 : Tendsto (J 1 G1) atTop (𝓝 0) := tendsto_integral_slow_weighted_iteratedDeriv hψ hi1 1
  have hJ2 : Tendsto (J 2 G2) atTop (𝓝 0) := tendsto_integral_slow_weighted_iteratedDeriv hψ hi2 2
  have he (R : ℝ) : (∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (mellinTailTest ψ s R) x) =
      (∫ x : ℝ in Ioi 0, G0 x) - (J 0 G0 R + J 1 G1 R + J 2 G2 R) := by
    have heq : (fun x : ℝ => F x * iteratedDeriv 2 (mellinTailTest ψ s R) x) =ᵐ[
        volume.restrict (Ioi 0)] fun x => G0 x -
      (G0 x * ((x : ℂ) ^ 0 * iteratedDeriv 0 (fun y : ℝ => ψ (R⁻¹ * y)) x) +
      G1 x * ((x : ℂ) ^ 1 * iteratedDeriv 1 (fun y : ℝ => ψ (R⁻¹ * y)) x) +
      G2 x * ((x : ℂ) ^ 2 * iteratedDeriv 2 (fun y : ℝ => ψ (R⁻¹ * y)) x)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [G0, G1, G2, w, pow_zero, pow_one, one_mul, iteratedDeriv_zero] using
        tail_second_product hψ s R (F x) hx
    have h0 := integrable_slow_jet hψ hi0 0 R
    have h1 := integrable_slow_jet hψ hi1 1 R
    have h2 := integrable_slow_jet hψ hi2 2 R
    have hsub := integral_sub hi0 ((h0.add h1).add h2)
    have hadd := integral_add (h0.add h1) h2
    simp only [Pi.add_apply] at hsub hadd
    rw [integral_congr_ae heq, hsub, hadd, integral_add h0 h1]
  have hsecond : Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0,
      F x * iteratedDeriv 2 (mellinTailTest ψ s R) x) atTop (𝓝 (∫ x : ℝ in Ioi 0, G0 x)) := by
    simp_rw [he]
    simpa only [add_zero, sub_zero] using tendsto_const_nhds.sub ((hJ0.add hJ1).add hJ2)
  have hiw : IntegrableOn w (Ioi 0) := by
    simpa only [w, MellinConvergent, smul_eq_mul, mul_comm, one_mul, mul_one] using
      (hψ.mellin_mul (F := fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ hs).1
  have hconstant : Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0, mellinTailTest ψ s R x) atTop
      (𝓝 (∫ x : ℝ in Ioi 0, w x)) := by
    have hJ := tendsto_integral_slow_weighted_iteratedDeriv hψ hiw 0
    have ht := (tendsto_const_nhds (x := (∫ x : ℝ in Ioi 0, w x))).sub hJ
    simp only [sub_zero] at ht
    apply ht.congr'
    filter_upwards [] with R
    have H := integral_sub hiw (integrable_slow_jet hψ hiw 0 R)
    simp only [pow_zero, one_mul, iteratedDeriv_zero] at H ⊢
    rw [← H]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only [mellinTailTest, w]
    ring
  exact (hconstant.const_mul A).add hsecond
/-- The scalar upper tail retains the exact constant-term sign. -/
theorem integral_mellinCutoff_tail {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    {s : ℂ} (hs : s.re < 0) :
    (∫ x : ℝ in Ioi 0, ψ x * (x : ℂ) ^ (s - 1)) =
      -(∫ x : ℝ in Ioi 0, iteratedDeriv 1 ψ x * (x : ℂ) ^ s) / s := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hi1 := integrable_cutoff_deriv_cpow hψ s
  have hi2 : IntegrableOn (fun x : ℝ => ψ x * (x : ℂ) ^ (s - 1)) (Ioi 0) := by
    simpa only [MellinConvergent, smul_eq_mul, mul_comm, one_mul, mul_one] using
      (hψ.mellin_mul (F := fun _ => 1) continuous_const ⟨1, fun _ => by simp⟩ hs).1
  let f : ℝ → ℂ := fun x => ψ x * (x : ℂ) ^ s
  have hf0 : f 0 = 0 := by
    obtain ⟨a, ha, h0⟩ := hψ.zero_near_origin
    simp [f, h0 0 ha]
  have hp : Tendsto (fun x : ℝ => (x : ℂ) ^ s) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have ht : Tendsto (fun x : ℝ => x ^ s.re) atTop (𝓝 0) := by
      simpa only [neg_neg] using tendsto_rpow_neg_atTop (neg_pos.mpr hs)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (Complex.norm_cpow_eq_rpow_re_of_pos hx s).symm
  have ht : Tendsto f atTop (𝓝 0) := by
    obtain ⟨b, hb⟩ := hψ.one_near_infinity
    apply hp.congr'
    filter_upwards [eventually_gt_atTop b] with x hx
    simp [f, hb x hx]
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt f
      (iteratedDeriv 1 ψ x * (x : ℂ) ^ s + s * (ψ x * (x : ℂ) ^ (s - 1))) x := by
    intro x hx
    have h := (hψ.smooth.differentiable (by simp) x).hasDerivAt.fun_mul
      (hasDerivAt_ofReal_cpow_const hx.ne' hs0)
    convert h using 1 <;> first | rfl | (simp only [iteratedDeriv_one]; ring)
  have hi := hi1.add (hi2.const_mul s)
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    (hψ.contDiff_mul_cpow s).continuous.continuousWithinAt hd hi ht
  dsimp only [f] at hf0
  rw [hf0, sub_self] at H
  have hadd := integral_add hi1 (hi2.const_mul s)
  rw [hadd, integral_const_mul] at H
  apply (eq_div_iff hs0).mpr
  linear_combination H

/-- Identification with the existing holomorphic upper-tail expression. -/
theorem tendsto_mellinTail_primitiveMellinTail {F ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ} (hs : s.re < 0) :
    Tendsto (fun R : ℝ => A * (∫ x : ℝ in Ioi 0, mellinTailTest ψ s R x) +
      ∫ x : ℝ in Ioi 0, F x * iteratedDeriv 2 (mellinTailTest ψ s R) x) atTop
      (𝓝 (primitiveMellinTail F A ψ s)) := by
  have H := tendsto_mellinTail_primitive_integrals hψ hF hB A hs
  rw [primitiveMellinTail_eq_integral hψ hF hB A (by linarith),
    integral_mellinCutoff_tail hψ hs] at *
  convert H using 1
  congr 1
  ring
end RHTower.WeilHigherDenominator
