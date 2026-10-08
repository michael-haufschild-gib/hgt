import GaloisForLFunctions.RHTower.WeilWorkHigherDenominatorCutoffPairing

/-!
# Actual lower Mellin cutoff limit

The three product-rule terms are dominated using the primitive's existing
Mellin weight. Positive derivative jets vanish in the limit, with no stronger
exponent assumption. The final theorem identifies the actual compact-test
Fourier pairing with the regularized Mellin head using only the original
cubic datum. The reciprocal-test limit and defect regularity are separate.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped ContDiff
namespace RHTower.WeilHigherDenominator

private lemma iteratedDeriv_two_product {u v : ℝ → ℂ} {x : ℝ}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) :
    iteratedDeriv 2 (fun y => u y * v y) x =
      iteratedDeriv 2 u x * v x + 2 * iteratedDeriv 1 u x * iteratedDeriv 1 v x +
        u x * iteratedDeriv 2 v x := by
  have H := iteratedDeriv_mul (n := 2) (hu.of_le (by exact WithTop.coe_le_coe.mpr le_top))
    (hv.of_le (by exact WithTop.coe_le_coe.mpr le_top))
  simpa [Pi.mul_def, Finset.sum_range_succ, Nat.choose, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc] using H

private lemma head_first_deriv {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (s : ℂ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv 1 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x =
      -iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 1) +
        (1 - ψ x) * ((s - 1) * (x : ℂ) ^ (s - 2)) := by
  have hp : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (s - 1))
      ((s - 1) * (x : ℂ) ^ (s - 2)) x := by
    by_cases hs : s - 1 = 0
    · simp only [hs, Complex.cpow_zero, zero_mul]
      exact hasDerivAt_const x 1
    simpa only [show s - 1 - 1 = s - 2 by ring] using
      hasDerivAt_ofReal_cpow_const hx.ne' hs
  simpa only [iteratedDeriv_one] using
    (((hψ.differentiable (by simp) x).hasDerivAt.const_sub 1).fun_mul hp).deriv

private lemma head_second_product {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (s : ℂ) (R : ℝ) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    z * iteratedDeriv 2 (mellinHeadTest ψ s R) x =
      (z * iteratedDeriv 2 (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x) * ψ (R * x) +
      (2 * (-(z * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2)) +
        (s - 1) * ((x : ℂ) ^ (s - 3) * (z * (1 - ψ x))))) *
          ((x : ℂ) * iteratedDeriv 1 (fun y : ℝ => ψ (R * y)) x) +
      ((x : ℂ) ^ (s - 3) * (z * (1 - ψ x))) *
        ((x : ℂ) ^ 2 * iteratedDeriv 2 (fun y : ℝ => ψ (R * y)) x) := by
  have hw : ContDiffAt ℝ ∞ (fun y : ℝ => (1 - ψ y) * (y : ℂ) ^ (s - 1)) x :=
    (contDiff_const.sub hψ).contDiffAt.mul (contDiffAt_positive_cpow hx (s - 1))
  have hη : ContDiff ℝ ∞ (fun y : ℝ => ψ (R * y)) :=
    hψ.comp (contDiff_const.mul contDiff_id)
  have he : mellinHeadTest ψ s R = fun y : ℝ =>
      ((1 - ψ y) * (y : ℂ) ^ (s - 1)) * ψ (R * y) := by
    funext y
    dsimp only [mellinHeadTest]
    ring
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have h1 : (x : ℂ) ^ (s - 2) = (x : ℂ) ^ (s - 3) * (x : ℂ) := by
    simpa only [Complex.cpow_one, show s - 3 + 1 = s - 2 by ring] using
      Complex.cpow_add (s - 3) 1 hxC
  have h2 : (x : ℂ) ^ (s - 1) = (x : ℂ) ^ (s - 3) * (x : ℂ) ^ 2 := by
    simpa only [Complex.cpow_two, show s - 3 + (2 : ℂ) = s - 1 by ring] using
      Complex.cpow_add (s - 3) 2 hxC
  rw [he, iteratedDeriv_two_product hw hη.contDiffAt, head_first_deriv hψ s hx, h1, h2]
  ring

private lemma integrable_dilate_jet {ψ G : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ)
    (hG : IntegrableOn G (Ioi 0)) (n : ℕ) (R : ℝ) :
    IntegrableOn (fun x : ℝ => G x *
      ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := hψ.dilate_weighted_iteratedDeriv_bounded n
  have hs : ContDiff ℝ ∞ (fun y : ℝ => ψ (R * y)) :=
    hψ.smooth.comp (contDiff_const.mul contDiff_id)
  exact hG.mul_bdd
    (((Complex.continuous_ofReal.pow n).mul
      (hs.continuous_iteratedDeriv n (by exact_mod_cast le_top (a := (n : ℕ∞))))).aestronglyMeasurable)
    (Eventually.of_forall (hC R))

/-- The cutoff product converges in the actual primitive pairing, including all derivative errors. -/
theorem tendsto_mellinHead_primitive_integrals {F ψ : ℝ → ℂ}
    (hψ : IsMellinTailCutoff ψ) (hF : Continuous F)
    (hB : ∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) (A : ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (hM : MellinConvergent (fun x => F x - F 0) (s - 2)) :
    Tendsto (fun R : ℝ => A * (∫ x : ℝ in Ioi 0, mellinHeadTest ψ s R x) +
      ∫ x : ℝ in Ioi 0, (F x - F 0) * iteratedDeriv 2 (mellinHeadTest ψ s R) x) atTop
      (𝓝 (primitiveMellinHead F A ψ s)) := by
  let f : ℝ → ℂ := fun x => F x - F 0
  let w : ℝ → ℂ := fun x => (1 - ψ x) * (x : ℂ) ^ (s - 1)
  let G0 : ℝ → ℂ := fun x => f x * iteratedDeriv 2 w x
  let G2 : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 3) * (f x * (1 - ψ x))
  let G1 : ℝ → ℂ := fun x => 2 * (-(f x * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2)) + (s - 1) * G2 x)
  have hf : Continuous f := hF.sub continuous_const
  have hBf : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hB
    exact ⟨C + ‖F 0‖, fun x => (norm_sub_le _ _).trans (add_le_add (hC x) (le_refl _))⟩
  have hi0 : IntegrableOn G0 (Ioi 0) :=
    (integrable_mellinHead_and_overlap hψ hF hB A hs0 hs2 hM).1
  have hiFull : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 3) * f x) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, f, smul_eq_mul, show s - 2 - 1 = s - 3 by ring] using hM
  have hiUpper : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 3) * (f x * ψ x)) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, show s - 2 - 1 = s - 3 by ring] using
      (hψ.mellin_mul hf hBf (s := s - 2) (by simpa using hs2)).1
  have hi2 : IntegrableOn G2 (Ioi 0) := by
    apply (hiFull.sub hiUpper).congr
    filter_upwards [] with x
    dsimp only [G2, Pi.sub_apply]
    ring
  have hiDer : IntegrableOn (fun x : ℝ => f x * iteratedDeriv 1 ψ x * (x : ℂ) ^ (s - 2)) (Ioi 0) := by
    simpa only [MellinConvergent, IntegrableOn, smul_eq_mul, mul_comm,
      show s - 1 - 1 = s - 2 by ring] using
      (hψ.mellin_mul_iteratedDeriv hf (by decide : 1 ≠ 0) (s - 1)).1
  have hi1 : IntegrableOn G1 (Ioi 0) := (hiDer.neg.add (hi2.const_mul (s - 1))).const_mul 2
  let J : ℕ → (ℝ → ℂ) → ℝ → ℂ := fun n G R =>
    ∫ x : ℝ in Ioi 0, G x * ((x : ℂ) ^ n * iteratedDeriv n (fun y : ℝ => ψ (R * y)) x)
  have hJ0 : Tendsto (J 0 G0) atTop (𝓝 (∫ x : ℝ in Ioi 0, G0 x)) := by
    simpa [J] using tendsto_integral_dilate_weighted_iteratedDeriv hψ hi0 0
  have hJ1 : Tendsto (J 1 G1) atTop (𝓝 0) := by
    simpa only [J, if_neg (by decide : ¬(1 : ℕ) = 0)] using
      tendsto_integral_dilate_weighted_iteratedDeriv hψ hi1 1
  have hJ2 : Tendsto (J 2 G2) atTop (𝓝 0) := by
    simpa only [J, if_neg (by decide : ¬(2 : ℕ) = 0)] using
      tendsto_integral_dilate_weighted_iteratedDeriv hψ hi2 2
  have he (R : ℝ) : (∫ x : ℝ in Ioi 0, f x * iteratedDeriv 2 (mellinHeadTest ψ s R) x) =
      J 0 G0 R + J 1 G1 R + J 2 G2 R := by
    have heq : (fun x : ℝ => f x * iteratedDeriv 2 (mellinHeadTest ψ s R) x) =ᵐ[
        volume.restrict (Ioi 0)] fun x =>
      G0 x * ((x : ℂ) ^ 0 * iteratedDeriv 0 (fun y : ℝ => ψ (R * y)) x) +
      G1 x * ((x : ℂ) ^ 1 * iteratedDeriv 1 (fun y : ℝ => ψ (R * y)) x) +
      G2 x * ((x : ℂ) ^ 2 * iteratedDeriv 2 (fun y : ℝ => ψ (R * y)) x) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      simpa only [G0, G1, G2, w, pow_zero, pow_one, one_mul, iteratedDeriv_zero] using
        head_second_product hψ.smooth s R (f x) hx
    have hadd := integral_add
      ((integrable_dilate_jet hψ hi0 0 R).add (integrable_dilate_jet hψ hi1 1 R))
      (integrable_dilate_jet hψ hi2 2 R)
    simp only [Pi.add_apply] at hadd
    rw [integral_congr_ae heq, hadd,
      integral_add (integrable_dilate_jet hψ hi0 0 R) (integrable_dilate_jet hψ hi1 1 R)]
  have hsecond : Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0,
      f x * iteratedDeriv 2 (mellinHeadTest ψ s R) x) atTop (𝓝 (∫ x : ℝ in Ioi 0, G0 x)) := by
    simp_rw [he]
    simpa only [add_zero] using (hJ0.add hJ1).add hJ2
  have hiw : IntegrableOn w (Ioi 0) := by
    simpa only [w, MellinConvergent, smul_eq_mul, mul_comm] using hψ.mellin_complement hs0
  have hconstant : Tendsto (fun R : ℝ => ∫ x : ℝ in Ioi 0, mellinHeadTest ψ s R x) atTop
      (𝓝 (mellin (fun x => 1 - ψ x) s)) := by
    have H := tendsto_integral_dilate_weighted_iteratedDeriv hψ hiw 0
    simpa [mellinHeadTest, w, mellin, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using H
  exact (hconstant.const_mul A).add hsecond

/-- The actual compact-test Fourier pairing tends to its absolutely regularized Mellin head. -/
theorem tendsto_fourierBoundaryPairing_mellinHeadTest {q : ℕ → ℂ}
    (hq : Summable fun n : ℕ => ‖q (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2)
    {ψ : ℝ → ℂ} (hψ : IsMellinTailCutoff ψ) (A : ℂ) {s : ℂ}
    (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (hM : MellinConvergent (fun x => fourierBoundaryPrimitive q x - fourierBoundaryPrimitive q 0) (s - 2)) :
    Tendsto (fun R : ℝ => fourierBoundaryPairing q A (mellinHeadTest ψ s R)) atTop
      (𝓝 (primitiveMellinHead (fourierBoundaryPrimitive q) A ψ s)) := by
  have ht := tendsto_mellinHead_primitive_integrals hψ
    (continuous_fourierBoundaryPrimitive hq) ⟨_, norm_fourierBoundaryPrimitive_le hq⟩ A hs0 hs2 hM
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  obtain ⟨hφ, hs, h0⟩ := mellinHeadTest_admissible hψ s hR
  exact (fourierBoundaryPairing_eq_primitive_head hq A hφ hs h0).symm

/-- The original cubic datum pays every hypothesis of the actual lower compact-test limit. -/
theorem degreeTwoQuotient_tendsto_mellinHead_pairing {g : ℕ → ℂ} {E : ℂ → ℂ}
    (hD : WeilZetaPower.ZetaPowerDatum 3 g E) (A : ℂ) {s : ℂ}
    (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    Tendsto (fun R : ℝ => fourierBoundaryPairing (degreeTwoQuotientCoeff g) A
      (mellinHeadTest mellinTailCutoff s R)) atTop
      (𝓝 (primitiveMellinHead (fourierBoundaryPrimitive (degreeTwoQuotientCoeff g)) A mellinTailCutoff s)) :=
  tendsto_fourierBoundaryPairing_mellinHeadTest
    (degreeTwoQuotientCoeff_summable_shift_square hD) isMellinTailCutoff_mellinTailCutoff A
    (by linarith) hs2 (degreeTwoQuotient_primitive_mellinConvergent hD hs1 hs2)
end RHTower.WeilHigherDenominator
