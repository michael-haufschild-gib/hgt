import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations
import GaloisForLFunctions.RHTower.WeilRegularDeviationRigidity

/-!
# Windowed Weil forms are height averages of localized Weil forms

Let `S_ξ f(u) = e^{2πiξu} f(u)` be the height shift, so that `h_{S_ξ f}(z) = h_f(z + 2πξ)`. The
localized Weil form `W(S_ξ f, S_ξ f)` reads the zero configuration through the transform of `f`
recentred at height `-2πξ`.

**Representation** (`windowedW_eq_integral_heightShift`). For every tempered configuration,
`windowedW Z f η = ∫ |h_η(-2πξ)|² · W(S_ξ f, S_ξ f) dξ`.

The proof inverts the Weil kernel of the window, `k_η(v) = ∫ |h_η(-2πξ)|² e^{2πiξv} dξ`
(`RHTower.WeilRegular.weilTest_eq_integral`). It then exchanges the zero sum with the height
integral. The exchange uses the Peetre bound `1 + |x| ≤ (1 + |x + y|)(1 + |y|)`, which moves the
height shift onto the decay of `h_η`.

**Positivity in height windows** (`re_integral_heightShift_nonneg_of_aperture_nonneg`). Let a
tempered configuration be Weil-nonnegative at aperture `r`, and let the window `η` be supported
in `[-r, r]`. Then every height average `∫ |h_η(-2πξ)|² W(S_ξ f, S_ξ f) dξ` has nonnegative
real part, for tests `f` of arbitrary aperture. The off-line lattice pair of spacing `2π/(2r)`
satisfies this at every depth (`re_integral_heightShift_offLineLattice_nonneg`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ### Height shifts -/

/-- The height shift `S_ξ f(u) = e^{2πiξu} f(u)`. -/
def heightShift (ξ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun u => cexp (2 * π * I * ξ * u) * f u

theorem paperFT_heightShift (ξ : ℝ) (f : ℝ → ℂ) (z : ℂ) :
    paperFT (heightShift ξ f) z = paperFT f (z + 2 * π * ξ) := by
  rw [paperFT_def, paperFT_def]
  congr 1 with u
  simp only [heightShift]
  rw [mul_comm (cexp _) (f u), mul_assoc, ← Complex.exp_add]
  congr 2
  ring

theorem heightShift_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (ξ : ℝ) :
    ContDiff ℝ 2 (heightShift ξ f) :=
  (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hf

theorem tsupport_heightShift_subset (ξ : ℝ) (f : ℝ → ℂ) :
    tsupport (heightShift ξ f) ⊆ tsupport f :=
  tsupport_mul_subset_right

theorem Wsummand_heightShift (Z : ZeroConfig) {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ξ : ℝ) (ρ : ℂ) :
    Z.Wsummand (heightShift ξ f) (heightShift ξ f) ρ =
      (Z.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ + 2 * π * ξ) := by
  have hc : conj (gammaOf ρ + 2 * π * ξ) = conj (gammaOf ρ) + 2 * π * ξ := by
    simp [map_ofNat]
  unfold ZeroConfig.Wsummand
  rw [EF.paperFT_weilTest hf hf hfc hfc, paperFT_heightShift, paperFT_heightShift, hc]
  ring

/-! ### Decay bounds -/

/-- **Peetre's inequality** for the weight `1 + |x|`. -/
theorem one_add_abs_le_mul_one_add_abs (x y : ℝ) : 1 + |x| ≤ (1 + |x + y|) * (1 + |y|) := by
  have h := abs_add_le (x + y) (-y)
  rw [abs_neg, show x + y + -y = x by ring] at h
  nlinarith [abs_nonneg (x + y), abs_nonneg y, mul_nonneg (abs_nonneg (x + y)) (abs_nonneg y)]

theorem norm_paperFT_le_of_abs_im_le {c : ℝ → ℂ} (hc : ContDiff ℝ 2 c) {a : ℝ} (ha : 0 ≤ a)
    (hca : ∀ u, c u ≠ 0 → |u| ≤ a) {x : ℂ} (hx : |x.im| ≤ 1 / 2) :
    ‖paperFT c x‖ ≤ Real.exp (a / 2) * (4 * ((∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖)) /
      (1 + |x.re|) ^ 2 := by
  have hN : 0 ≤ (∫ u, ‖c u‖) + ∫ u, ‖deriv (deriv c) u‖ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  refine (norm_paperFT_le_decay hc hca x).trans ?_
  gcongr
  nlinarith [abs_nonneg x.im]

theorem exists_radius_bound {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ a, 0 ≤ a ∧ ∀ u, f u ≠ 0 → |u| ≤ a := by
  obtain ⟨a, ha, hfa⟩ := exists_radius_of_hasCompactSupport hfc
  exact ⟨a, ha, fun u hu => by
    by_contra h
    exact hu (hfa u (not_le.mp h))⟩

/-- The window weight `|h_η(-2πξ)|²` decays like `(1 + |2πξ|)^{-4}`. -/
theorem exists_norm_pairTransform_ofReal_le {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∃ D, 0 ≤ D ∧ ∀ ξ : ℝ, ‖pairTransform η ξ‖ ≤ D ^ 2 / ((1 + |2 * π * ξ|) ^ 2) ^ 2 := by
  obtain ⟨r, hr, hsη⟩ := exists_radius_bound hηc
  set D := Real.exp (r / 2) * (4 * ((∫ u, ‖η u‖) + ∫ u, ‖deriv (deriv η) u‖)) with hD
  have hD0 : 0 ≤ D := by
    have : 0 ≤ (∫ u, ‖η u‖) + ∫ u, ‖deriv (deriv η) u‖ :=
      add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
    positivity
  refine ⟨D, hD0, fun ξ => ?_⟩
  have h := norm_paperFT_le_of_abs_im_le hη hr hsη (x := -(2 * π * (ξ : ℂ))) (by simp)
  have hre : |(-(2 * π * (ξ : ℂ))).re| = |2 * π * ξ| := by simp
  rw [hre] at h
  rw [pairTransform_ofReal hη hηc ξ, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    ← div_pow]
  gcongr

theorem one_add_sq_le_of_abs_le {ξ y : ℝ} (h : |ξ| ≤ |y|) : 1 + ξ ^ 2 ≤ (1 + |y|) ^ 2 := by
  nlinarith [sq_abs ξ, sq_abs y, abs_nonneg ξ, abs_nonneg y, mul_self_le_mul_self (abs_nonneg ξ) h]

theorem abs_le_abs_two_pi_mul (ξ : ℝ) : |ξ| ≤ |2 * π * ξ| := by
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  nlinarith [Real.pi_gt_three, abs_nonneg ξ]

theorem integrable_pairTransform {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable fun ξ : ℝ => pairTransform η ξ := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_pairTransform_ofReal_le hη hηc
  refine (integrable_inv_one_add_sq.const_mul (D ^ 2)).mono'
    ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  refine (hD ξ).trans ?_
  have h1 := one_add_sq_le_of_abs_le (abs_le_abs_two_pi_mul ξ)
  have h2 : (1 + |2 * π * ξ|) ^ 2 ≤ ((1 + |2 * π * ξ|) ^ 2) ^ 2 := by
    have : 1 ≤ (1 + |2 * π * ξ|) ^ 2 := by nlinarith [abs_nonneg (2 * π * ξ)]
    nlinarith
  rw [div_eq_mul_inv]
  gcongr
  linarith

/-- The real inequality behind the zero-side summability. -/
theorem decay_product_le {x y ξ N : ℝ} (hξ : |ξ| ≤ |y|) (hN0 : 0 ≤ N)
    (hN : 1 + N ≤ 5 / 4 * (1 + |x|) ^ 2) :
    (1 + N) * (1 + ξ ^ 2) ≤ 5 / 4 * ((1 + |y|) ^ 2) ^ 2 * ((1 + |x + y|) ^ 2) ^ 2 := by
  have hp : 1 ≤ 1 + |y| := by linarith [abs_nonneg y]
  have hq : 1 ≤ 1 + |x + y| := by linarith [abs_nonneg (x + y)]
  have hs := one_add_abs_le_mul_one_add_abs x y
  have hs0 : 0 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hξ2 := one_add_sq_le_of_abs_le hξ
  have hs2 : (1 + |x|) ^ 2 ≤ (1 + |x + y|) ^ 2 * (1 + |y|) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hs0 hs 2
  have hq2 : (1 + |x + y|) ^ 2 ≤ ((1 + |x + y|) ^ 2) ^ 2 := by
    have : 1 ≤ (1 + |x + y|) ^ 2 := by nlinarith
    nlinarith
  calc (1 + N) * (1 + ξ ^ 2) ≤ 5 / 4 * (1 + |x|) ^ 2 * (1 + |y|) ^ 2 :=
        mul_le_mul hN hξ2 (by positivity) (by positivity)
    _ ≤ 5 / 4 * ((1 + |x + y|) ^ 2 * (1 + |y|) ^ 2) * (1 + |y|) ^ 2 := by gcongr
    _ = 5 / 4 * ((1 + |y|) ^ 2) ^ 2 * (1 + |x + y|) ^ 2 := by ring
    _ ≤ 5 / 4 * ((1 + |y|) ^ 2) ^ 2 * ((1 + |x + y|) ^ 2) ^ 2 := by gcongr

/-! ### The representation -/

/-- **Per-zero representation.** The transform of the windowed kernel is the height average of
the shifted transforms of `k_f`, weighted by `|h_η(-2πξ)|²`. -/
theorem paperFT_windowedKernel_eq_integral_shift {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (z : ℂ) :
    paperFT (windowedKernel f η) z =
      ∫ ξ : ℝ, pairTransform η ξ * paperFT (EF.weilTest f f) (z + 2 * π * ξ) := by
  obtain ⟨r, -, hsη⟩ := exists_radius_bound hηc
  have hPc : Continuous fun ξ : ℝ => pairTransform η ξ :=
    (differentiable_pairTransform hη hηc).continuous.comp Complex.continuous_ofReal
  have hPi := integrable_pairTransform hη hηc
  have hkc : Continuous (EF.weilTest f f) :=
    (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  have hkcs : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hG : Integrable fun v : ℝ => ‖EF.weilTest f f v * cexp (I * z * v)‖ :=
    ((hkc.mul (by fun_prop)).norm).integrable_of_hasCompactSupport hkcs.mul_right.norm
  have hint : Integrable (Function.uncurry fun (v ξ : ℝ) =>
      pairTransform η ξ * (EF.weilTest f f v * cexp (I * (z + 2 * π * ξ) * v)))
      (volume.prod volume) := by
    refine (hG.mul_prod hPi.norm).mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      change Continuous fun p : ℝ × ℝ =>
        pairTransform η p.2 * (EF.weilTest f f p.1 * cexp (I * (z + 2 * π * p.2) * p.1))
      exact (hPc.comp continuous_snd).mul ((hkc.comp continuous_fst).mul (by fun_prop))
    · obtain ⟨v, ξ⟩ := p
      have he : ‖cexp (I * (z + 2 * π * ξ) * v)‖ = ‖cexp (I * z * v)‖ := by
        rw [show I * (z + 2 * π * ξ) * v = I * z * v + ((2 * π * ξ * v : ℝ) : ℂ) * I by
          push_cast; ring, Complex.exp_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      simp only [Function.uncurry_apply_pair, norm_mul, he]
      exact le_of_eq (by ring)
  have hrow : ∀ v : ℝ, windowedKernel f η v * cexp (I * z * v) =
      ∫ ξ : ℝ, pairTransform η ξ * (EF.weilTest f f v * cexp (I * (z + 2 * π * ξ) * v)) := by
    intro v
    simp only [windowedKernel]
    rw [weilTest_eq_integral hη hηc hsη v, ← integral_const_mul, ← integral_mul_const]
    congr 1 with ξ
    rw [show I * (z + 2 * π * ξ) * v = 2 * π * I * ξ * v + I * z * v by ring, Complex.exp_add]
    ring
  rw [paperFT_def, integral_congr_ae (Eventually.of_forall hrow), integral_integral_swap hint]
  congr 1 with ξ
  rw [integral_const_mul, paperFT_def]

/-- **Height-average representation of windowed Weil forms.** For every tempered configuration,
`windowedW Z f η = ∫ |h_η(-2πξ)|² W(S_ξ f, S_ξ f) dξ`. -/
theorem windowedW_eq_integral_heightShift (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    windowedW Z f η =
      ∫ ξ : ℝ, pairTransform η ξ * Z.W (heightShift ξ f) (heightShift ξ f) := by
  haveI : Countable Z.carrier := (countable_carrier Z).to_subtype
  obtain ⟨a, ha, hsf⟩ := exists_radius_bound hfc
  obtain ⟨D, hD0, hD⟩ := exists_norm_pairTransform_ofReal_le hη hηc
  set E := Real.exp (a / 2) * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖)) with hE
  have hE0 : 0 ≤ E := by
    have : 0 ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ :=
      add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
    positivity
  set K : ℝ := D ^ 2 * E ^ 2 * (5 / 4) with hK
  set F : Z.carrier → ℝ → ℂ := fun ρ ξ =>
    pairTransform η ξ * ((Z.mult ρ : ℂ) * paperFT (EF.weilTest f f) (gammaOf ρ + 2 * π * ξ))
    with hF
  have hPc : Continuous fun ξ : ℝ => pairTransform η ξ :=
    (differentiable_pairTransform hη hηc).continuous.comp Complex.continuous_ofReal
  have hkd : Differentiable ℂ (paperFT (EF.weilTest f f)) :=
    WeilEF.differentiable_paperFT (EF.weilTest_contDiff hf hf.continuous hfc).continuous
      (EF.weilTest_hasCompactSupport hfc hfc)
  have hFcont : ∀ ρ, Continuous (F ρ) := fun ρ =>
    hPc.mul (continuous_const.mul (hkd.continuous.comp (by fun_prop)))
  have hper : ∀ ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT (windowedKernel f η) (gammaOf ρ) =
      ∫ ξ, F ρ ξ := by
    intro ρ
    rw [paperFT_windowedKernel_eq_integral_shift hf hfc hη hηc, ← integral_const_mul]
    congr 1 with ξ
    simp only [hF]
    ring
  have hptw : ∀ ρ : Z.carrier, ∀ ξ : ℝ, ‖F ρ ξ‖ ≤
      K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * (1 + ξ ^ 2)⁻¹ := by
    intro ρ ξ
    have him : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := WeilEF.abs_gammaOf_im_le (Z.strip ρ ρ.2)
    set x := (gammaOf (ρ : ℂ)).re with hx
    set y := 2 * π * ξ with hy
    set N := Complex.normSq (gammaOf (ρ : ℂ)) with hNdef
    have hN0 : 0 ≤ N := Complex.normSq_nonneg _
    have hN : 1 + N ≤ 5 / 4 * (1 + |x|) ^ 2 := by
      have him2 : (gammaOf (ρ : ℂ)).im * (gammaOf (ρ : ℂ)).im ≤ 1 / 4 := by
        rw [← abs_mul_abs_self]
        nlinarith [abs_nonneg (gammaOf (ρ : ℂ)).im]
      have hx2 : 1 + x ^ 2 ≤ (1 + |x|) ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      rw [hNdef, Complex.normSq_apply]
      nlinarith
    have hw1 : ‖paperFT f (gammaOf (ρ : ℂ) + 2 * π * ξ)‖ ≤ E / (1 + |x + y|) ^ 2 := by
      have h := norm_paperFT_le_of_abs_im_le hf ha hsf (x := gammaOf (ρ : ℂ) + 2 * π * ξ)
        (by simpa using him)
      have hre : (gammaOf (ρ : ℂ) + 2 * π * ξ).re = x + y := by simp [hx, hy]
      rwa [hre] at h
    have hw2 : ‖paperFT f (conj (gammaOf (ρ : ℂ) + 2 * π * ξ))‖ ≤ E / (1 + |x + y|) ^ 2 := by
      have h := norm_paperFT_le_of_abs_im_le hf ha hsf
        (x := conj (gammaOf (ρ : ℂ) + 2 * π * ξ)) (by simpa using him)
      have hre : (conj (gammaOf (ρ : ℂ) + 2 * π * ξ)).re = x + y := by simp [hx, hy]
      rwa [hre] at h
    have hkey := decay_product_le (abs_le_abs_two_pi_mul ξ) hN0 hN
    rw [← hy] at hkey
    have hm : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    have hp : 0 < (1 + |y|) ^ 2 := by positivity
    have hq : 0 < (1 + |x + y|) ^ 2 := by positivity
    have hinv : 1 / (((1 + |y|) ^ 2) ^ 2 * ((1 + |x + y|) ^ 2) ^ 2) ≤
        5 / 4 / ((1 + N) * (1 + ξ ^ 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    simp only [hF]
    rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, norm_mul, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_natCast]
    set P := (1 + |y|) ^ 2 with hP
    set Q := (1 + |x + y|) ^ 2 with hQ
    set N₁ := 1 + N with hN₁
    set X₁ := 1 + ξ ^ 2 with hX₁
    calc ‖pairTransform η ξ‖ * ((Z.mult ρ : ℝ) * (‖paperFT f (gammaOf (ρ : ℂ) + 2 * π * ξ)‖ *
          ‖paperFT f (conj (gammaOf (ρ : ℂ) + 2 * π * ξ))‖))
        ≤ D ^ 2 / P ^ 2 * ((Z.mult ρ : ℝ) * (E / Q * (E / Q))) := by
          gcongr
          exact hD ξ
      _ = D ^ 2 * E ^ 2 * (Z.mult ρ : ℝ) * (1 / (P ^ 2 * Q ^ 2)) := by ring
      _ ≤ D ^ 2 * E ^ 2 * (Z.mult ρ : ℝ) * (5 / 4 / (N₁ * X₁)) := by gcongr
      _ = K * ((Z.mult ρ : ℝ) / N₁) * X₁⁻¹ := by rw [hK]; ring
  have hbound : ∀ ρ : Z.carrier, Integrable fun ξ : ℝ =>
      K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * (1 + ξ ^ 2)⁻¹ := fun ρ =>
    integrable_inv_one_add_sq.const_mul _
  have hFint : ∀ ρ, Integrable (F ρ) := fun ρ =>
    (hbound ρ).mono' (hFcont ρ).aestronglyMeasurable (Eventually.of_forall (hptw ρ))
  set I₀ : ℝ := ∫ ξ : ℝ, (1 + ξ ^ 2)⁻¹ with hI₀
  have hFsum : Summable fun ρ : Z.carrier => ∫ ξ, ‖F ρ ξ‖ := by
    refine Summable.of_nonneg_of_le (fun ρ => integral_nonneg fun _ => norm_nonneg _)
      (fun ρ => ?_) (hZ.mul_left (K * I₀))
    calc ∫ ξ, ‖F ρ ξ‖
        ≤ ∫ ξ, K * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) * (1 + ξ ^ 2)⁻¹ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hbound ρ)
            (Eventually.of_forall (hptw ρ))
      _ = K * I₀ * ((Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) := by
          rw [integral_const_mul, hI₀]
          ring
  rw [windowedW, tsum_congr hper, integral_tsum_of_summable_integral_norm hFint hFsum]
  congr 1 with ξ
  unfold ZeroConfig.W
  rw [← tsum_mul_left]
  congr 1 with ρ
  simp only [hF]
  rw [Wsummand_heightShift Z hf.continuous hfc]

/-- The representation with the window weight written as `|h_η(-2πξ)|²`. -/
theorem windowedW_eq_integral_normSq_heightShift (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    windowedW Z f η = ∫ ξ : ℝ, ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) *
      Z.W (heightShift ξ f) (heightShift ξ f) := by
  rw [windowedW_eq_integral_heightShift Z hZ hf hfc hη hηc]
  congr 1 with ξ
  rw [pairTransform_ofReal hη hηc ξ]

/-! ### Positivity in height windows -/

/-- **Positivity in height windows.** If a tempered configuration is Weil-nonnegative at aperture
`r`, every height average of localized Weil forms with a window supported in `[-r, r]` has
nonnegative real part, for tests of arbitrary aperture. -/
theorem re_integral_heightShift_nonneg_of_aperture_nonneg (Z : ZeroConfig)
    (hZ : TemperedConfig Z) {r : ℝ}
    (hpos : ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-r) r → 0 ≤ (Z.W g g).re)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) :
    0 ≤ (∫ ξ : ℝ, ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) *
      Z.W (heightShift ξ f) (heightShift ξ f)).re := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  rw [← windowedW_eq_integral_normSq_heightShift Z hZ hf hfc hη hηc]
  exact re_windowedW_nonneg_of_aperture_nonneg Z hZ hpos hf hfc hη hηs

/-- **Off-line lattices pass every height average at resolution `r`.** For every depth
`δ ∈ (0, ½]`, the off-line lattice pair of spacing `2π/(2r)` has
`∫ |h_η(-2πξ)|² W(S_ξ f, S_ξ f) dξ = 4r ‖f‖² ‖η‖²` for windows supported in `[-r, r]` and tests
of arbitrary aperture. -/
theorem integral_heightShift_offLineLattice_eq {δ r : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-r) r) :
    ∫ ξ : ℝ, ((‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 : ℝ) : ℂ) *
        (offLineLatticeConfig (by positivity : (0 : ℝ) < 2 * r) hδ hδ').W
          (heightShift ξ f) (heightShift ξ f) =
      ((2 * (2 * r) * ((∫ t, ‖f t‖ ^ 2) * ∫ t, ‖η t‖ ^ 2) : ℝ) : ℂ) := by
  have hL : (0 : ℝ) < 2 * r := by positivity
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hηs' : tsupport η ⊆ Icc (-(2 * r / 2)) (2 * r / 2) := by
    rwa [show 2 * r / 2 = r by ring]
  rw [← windowedW_eq_integral_normSq_heightShift _ (temperedConfig_offLineLatticeConfig hL hδ hδ')
    hf hfc hη hηc]
  exact windowedW_offLineLatticeConfig_eq_norms hL hδ hδ' hf hfc hη hηs'

end GaloisForLFunctions.SquareRootThreshold
