import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheTuranCameraSeesBoundedClusters
import GaloisForLFunctions.SquareRootThreshold.ZetaUniformTwinRadiusOfNearTopZeros
import GaloisForLFunctions.SquareRootThreshold.CountingInputsDoNotBoundTheLocalCount

/-!
# The near-line zeros cannot block the camera

The Turán camera asks that the zeros outside a bounded cluster carry little weighted mass. This module removes the
near-line zeros from that condition. A zero with `|Re ρ − ½| ≤ A/L` has camera weight at most
`e^A/(1 + δ²(γ − t)²)` at every centre with `y + δ ≤ L` (`sum_near_weight_le`), and by Fubini the Lorentzian mass of all zeros has
first moment `≪ T/c` on `(T, 2T]`: each zero costs `π/δ`, and there are `≪ T L` of them
(`exists_volume_near_mass_ge_le`). So near-line mass of size `Λ` occurs only on measure `≪ e^A T/(cΛ)`.

**Theorem** (`exists_card_zeros_without_deep_companions_le`). Separated zeros of depth `≥ α/L` whose only competitors are at most
`N` zeros in the sector and a small mass of zeros deeper than `A/L` number

`≪_{c,N} T L e^{A − (1−4c)α}`.

With `A = o(α)` and `c → 0` the rate tends to `1`, above the rate `22/25` of the mollified second moment. Every set of
zeros at the corpus rate must therefore be nearly all clustered with **comparably deep** companions at the camera
scale. Near-line zeros, however numerous on average, do not explain the gap.

**What stops at rate one.** The Markov bound on the first moment of the Lorentzian mass. The exponential tail of this mass carries the bound to rate two
in `OnlyComparablyDeepZerosCompete`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23
open RHTower.LocalCountFalsifier (exists_N_window_le)
open GaloisForLFunctions.SquareRootThreshold (sum_mult_le_tsum_copies)

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### The first moment of the Lorentzian mass -/

/-- The Lorentzian mass at scale `1/δ` of the zeros with ordinate in `(T − 1, 2T + 1]`. -/
def windowMass (δ T t : ℝ) : ℝ :=
  ∑ ρ ∈ (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset,
    (zetaZeroConfig.mult ρ : ℝ) / (1 + δ ^ 2 * (ρ.im - t) ^ 2)

theorem windowMass_nonneg (δ T t : ℝ) : 0 ≤ windowMass δ T t :=
  Finset.sum_nonneg fun ρ _ => by positivity

theorem continuous_windowMass (δ T : ℝ) : Continuous (windowMass δ T) := by
  unfold windowMass
  refine continuous_finsetSum _ fun ρ _ => continuous_const.div (by fun_prop) fun t => ?_
  positivity

/-- One zero costs at most `π/δ` of first moment, wherever it is. -/
theorem integral_lorentzian_le {δ : ℝ} (hδ : 0 < δ) (γ T : ℝ) (hT : 0 ≤ T) :
    ∫ t in T..(2 * T), 1 / (1 + δ ^ 2 * (γ - t) ^ 2) ≤ π / δ := by
  set φ : ℝ → ℝ := fun t => (1 + (δ * (t - γ)) ^ 2)⁻¹ with hφ
  have hi : Integrable φ :=
    (integrable_inv_one_add_sq.comp_mul_left' hδ.ne').comp_sub_right γ
  have hall : ∫ t, φ t = π / δ := by
    have h1 : (∫ t : ℝ, φ t) = ∫ t : ℝ, (1 + (δ * t) ^ 2)⁻¹ :=
      integral_sub_right_eq_self (fun x : ℝ => (1 + (δ * x) ^ 2)⁻¹) γ
    rw [h1, Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) δ,
      integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.2 hδ), smul_eq_mul]
    field_simp
  have heq : ∀ t, 1 / (1 + δ ^ 2 * (γ - t) ^ 2) = φ t := by
    intro t
    simp only [hφ]
    rw [one_div]
    congr 1
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_of_le (by linarith), ← hall]
  exact setIntegral_le_integral hi (Eventually.of_forall fun t => by
    simp only [hφ, Pi.zero_apply]
    positivity)

theorem integral_windowMass_le {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in T..(2 * T), windowMass δ T t ≤ π / δ * (zetaZeroConfig.N (T - 1) (2 * T + 1) : ℝ) := by
  classical
  have hcont : ∀ ρ : ℂ, Continuous fun t : ℝ => 1 / (1 + δ ^ 2 * (ρ.im - t) ^ 2) := by
    intro ρ
    refine continuous_const.div (by fun_prop) fun t => ?_
    positivity
  have hN : ∑ ρ ∈ (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset,
      (zetaZeroConfig.mult ρ : ℝ) = zetaZeroConfig.N (T - 1) (2 * T + 1) := by
    rw [ZeroConfig.N, ZeroConfig.window, finsum_mem_eq_finite_toFinset_sum _
      (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)), Nat.cast_sum]
  unfold windowMass
  rw [intervalIntegral.integral_finsetSum (f := fun ρ t =>
    (zetaZeroConfig.mult ρ : ℝ) / (1 + δ ^ 2 * (ρ.im - t) ^ 2)) (fun ρ _ =>
    (continuous_const.div (by fun_prop) fun t => by positivity).intervalIntegrable _ _),
    ← hN, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ _ => ?_
  have e : ∀ t : ℝ, (zetaZeroConfig.mult ρ : ℝ) / (1 + δ ^ 2 * (ρ.im - t) ^ 2) =
      (zetaZeroConfig.mult ρ : ℝ) * (1 / (1 + δ ^ 2 * (ρ.im - t) ^ 2)) := fun t => by ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (integral_lorentzian_le hδ ρ.im T hT) (Nat.cast_nonneg _)

/-- Markov on a dyadic range for a continuous nonnegative function. -/
theorem volume_ge_le_of_integral {f : ℝ → ℝ} (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t) {T B x : ℝ}
    (hT : 0 < T) (hx : 0 < x) (hB : ∫ t in T..(2 * T), f t ≤ B) :
    volume {t | t ∈ Ioc T (2 * T) ∧ x ≤ f t} ≤ ENNReal.ofReal (B / x) := by
  have hle : T ≤ 2 * T := by linarith
  have hMI : Integrable f (volume.restrict (Ioc T (2 * T))) := hf.integrableOn_Ioc
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Ioc T (2 * T)))
    (Eventually.of_forall hf0) hMI x
  rw [← intervalIntegral.integral_of_le hle, measureReal_def] at hmark
  have hfinite : volume.restrict (Ioc T (2 * T)) {t | x ≤ f t} ≠ ⊤ :=
    measure_ne_top_of_subset (Set.subset_univ _) (by
      rw [Measure.restrict_apply_univ, Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top)
  have hsub : {t | t ∈ Ioc T (2 * T) ∧ x ≤ f t} ⊆ {t | x ≤ f t} ∩ Ioc T (2 * T) := fun t ht =>
    ⟨ht.2, ht.1⟩
  calc volume {t | t ∈ Ioc T (2 * T) ∧ x ≤ f t}
      ≤ volume ({t | x ≤ f t} ∩ Ioc T (2 * T)) := measure_mono hsub
    _ = volume.restrict (Ioc T (2 * T)) {t | x ≤ f t} :=
        (Measure.restrict_apply' measurableSet_Ioc).symm
    _ = ENNReal.ofReal ((volume.restrict (Ioc T (2 * T)) {t | x ≤ f t}).toReal) :=
        (ENNReal.ofReal_toReal hfinite).symm
    _ ≤ ENNReal.ofReal (B / x) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [le_div_iff₀ hx]
        linarith

/-! ### The near-line weights -/

/-- A finite family of near-line zeros has mass at most `e^A` times the Lorentzian mass, at every admissible
centre: the window part plus `2/δ²` times the unit-scale mass. -/
theorem sum_near_weight_le {δ y T t A L : ℝ} (hδ1 : 1 ≤ δ) (hy0 : 0 ≤ y) (hyL : y + δ ≤ L)
    (ht : t ∈ Ioc T (2 * T)) (F : Finset zetaZeroConfig.carrier)
    (hnear : ∀ ρ' ∈ F, |(ρ' : ℂ).re - 1 / 2| ≤ A / L) :
    ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t (ρ' : ℂ) ≤
      Real.exp A * (windowMass δ T t + 2 / δ ^ 2 * lorentzMass t) := by
  classical
  have hδ0 : 0 < δ := by linarith
  have hL0 : 0 < L := by linarith
  have hEA : 0 < Real.exp A := Real.exp_pos A
  set e : ℂ → ℝ := fun ρ => (zetaZeroConfig.mult ρ : ℝ) / (1 + δ ^ 2 * (ρ.im - t) ^ 2) with he
  have he0 : ∀ ρ, 0 ≤ e ρ := fun ρ => by
    simp only [he]
    positivity
  -- the weight of one near-line zero
  have hterm : ∀ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ y t (ρ' : ℂ) ≤
      Real.exp A * e (ρ' : ℂ) := by
    intro ρ' hρ'
    have hb := hnear ρ' hρ'
    have hbA : 0 ≤ A / L := (abs_nonneg _).trans hb
    have hexp : Real.exp (((ρ' : ℂ).re - 1 / 2) * y + |(ρ' : ℂ).re - 1 / 2| * δ) ≤ Real.exp A := by
      refine Real.exp_le_exp.2 ?_
      have h1 : ((ρ' : ℂ).re - 1 / 2) * y ≤ |(ρ' : ℂ).re - 1 / 2| * y :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hy0
      have h2 : |(ρ' : ℂ).re - 1 / 2| * (y + δ) ≤ A / L * L :=
        mul_le_mul hb hyL (by linarith) hbA
      have h3 : A / L * L = A := by
        field_simp
      nlinarith
    simp only [he, companionWeight]
    rw [mul_div_assoc', mul_div_assoc', mul_comm (zetaZeroConfig.mult _ : ℝ)]
    have hden : 0 < 1 + δ ^ 2 * ((ρ' : ℂ).im - t) ^ 2 := by positivity
    refine div_le_div_of_nonneg_right ?_ hden.le
    exact mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hEA.le
  -- split at the window
  set inW : zetaZeroConfig.carrier → Prop := fun ρ' => T - 1 < (ρ' : ℂ).im ∧ (ρ' : ℂ).im ≤ 2 * T + 1
    with hinW
  have hinj : Set.InjOn (Subtype.val : zetaZeroConfig.carrier → ℂ) (F : Set zetaZeroConfig.carrier) :=
    Subtype.val_injective.injOn
  rw [← Finset.sum_filter_add_sum_filter_not F inW]
  refine add_le_add ?_ ?_
  · -- inside the window
    unfold windowMass
    have hsub : (F.filter inW).image Subtype.val ⊆
        (zetaZeroConfig.finite_window (T - 1) (2 * T + 1)).toFinset := by
      intro z hz
      obtain ⟨ρ', hρ', rfl⟩ := Finset.mem_image.mp hz
      rw [Set.Finite.mem_toFinset]
      exact ⟨ρ'.2, (Finset.mem_filter.mp hρ').2⟩
    calc ∑ ρ' ∈ F.filter inW, e (ρ' : ℂ) = ∑ z ∈ (F.filter inW).image Subtype.val, e z :=
          (Finset.sum_image (Subtype.val_injective.injOn)).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun z _ _ => he0 z
  · -- outside the window the distance is at least one
    set g : ℂ → ℝ := fun ρ => 1 / (1 + (t - ρ.im) ^ 2) with hg
    have hfar : ∀ ρ' ∈ F.filter (fun ρ' => ¬ inW ρ'), e (ρ' : ℂ) ≤
        2 / δ ^ 2 * ((zetaZeroConfig.mult ρ' : ℝ) * g (ρ' : ℂ)) := by
      intro ρ' hρ'
      have hnot := (Finset.mem_filter.mp hρ').2
      have hd : 1 ≤ ((ρ' : ℂ).im - t) ^ 2 := by
        have h1 : 1 ≤ |(ρ' : ℂ).im - t| := by
          by_cases hlow : T - 1 < (ρ' : ℂ).im
          · have hhigh : 2 * T + 1 < (ρ' : ℂ).im := by
              by_contra h
              exact hnot ⟨hlow, not_lt.mp h⟩
            refine le_trans ?_ (le_abs_self _)
            linarith [ht.2]
          · refine le_trans ?_ (neg_le_abs _)
            linarith [ht.1, not_lt.mp hlow]
        calc (1 : ℝ) ≤ |(ρ' : ℂ).im - t| ^ 2 := one_le_pow₀ h1
          _ = _ := sq_abs _
      simp only [he, hg]
      have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ' := Nat.cast_nonneg _
      have h1 : 1 / (1 + δ ^ 2 * ((ρ' : ℂ).im - t) ^ 2) ≤
          2 / δ ^ 2 * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2)) := by
        have e2 : (t - (ρ' : ℂ).im) ^ 2 = ((ρ' : ℂ).im - t) ^ 2 := by ring
        rw [e2, ← mul_div_assoc, mul_one, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have hδ2 : 0 ≤ δ ^ 2 := by positivity
        nlinarith [mul_nonneg hδ2 (sub_nonneg.2 hd)]
      calc (zetaZeroConfig.mult ρ' : ℝ) / (1 + δ ^ 2 * ((ρ' : ℂ).im - t) ^ 2)
          = (zetaZeroConfig.mult ρ' : ℝ) * (1 / (1 + δ ^ 2 * ((ρ' : ℂ).im - t) ^ 2)) := by ring
        _ ≤ (zetaZeroConfig.mult ρ' : ℝ) * (2 / δ ^ 2 * (1 / (1 + (t - (ρ' : ℂ).im) ^ 2))) :=
            mul_le_mul_of_nonneg_left h1 hm
        _ = _ := by ring
    refine (Finset.sum_le_sum hfar).trans ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hcopies := sum_mult_le_tsum_copies g
      (fun q => by simp only [hg]; positivity)
      (summable_lorentzMassTerm t) ((F.filter fun ρ' => ¬ inW ρ').image Subtype.val)
      (fun ρ hρ => by
        obtain ⟨ρ', -, rfl⟩ := Finset.mem_image.mp hρ
        exact ρ'.2)
    rw [Finset.sum_image (Subtype.val_injective.injOn)] at hcopies
    exact hcopies

/-- **Near-line mass is rare.** Mass of size `Λ` occurs on measure `≤ C E T/(cΛ)` in `(T, 2T]`: each zero costs `π/δ`
of first moment, there are `≤ T L/5` of them, and the unit-scale mass enters with the factor `2/δ²`. -/
theorem exists_volume_near_mass_ge_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ c E Λ : ℝ, 0 < c → c < 1 → 1 / c ≤ Real.log T →
      64 / c ^ 2 ≤ Real.log T → 0 < E → 0 < Λ →
      volume {t | t ∈ Ioc T (2 * T) ∧ Λ ≤ E * (windowMass (c * Real.log T) T t +
          2 / (c * Real.log T) ^ 2 * lorentzMass t)} ≤
        ENNReal.ofReal (C * E * T / (c * Λ)) := by
  obtain ⟨K, hK⟩ := exists_N_window_le riemannVonMangoldt_zeta
  have hCξ := xiLineTwoLogDerivConstant_nonneg
  set Cf := (xiLineTwoLogDerivConstant + 2) / 4 with hCf
  have hCf0 : 0 < Cf := by
    rw [hCf]
    linarith
  refine ⟨2 * π / 5 + 2 * Cf, by positivity, ?_⟩
  filter_upwards [hK, eventually_ge_atTop (30 * |K| + 21), Real.tendsto_log_atTop.eventually_ge_atTop 1]
    with T hNT hT hL1 c E Λ hc0 hc1 hLc hLd hE hΛ
  have hT21 : 21 ≤ T := by linarith [abs_nonneg K]
  have hT0 : 0 < T := by linarith
  set L := Real.log T with hLdef
  have hL0 : 0 < L := by linarith
  set δ := c * L with hδdef
  have hδ0 : 0 < δ := by positivity
  have hNle : (zetaZeroConfig.N (T - 1) (2 * T + 1) : ℝ) ≤ T / 5 * L := by
    have h2π : T / (2 * Real.pi) ≤ T / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.pi_gt_three]
    have hKT : |K| * L ≤ T / 30 * L :=
      mul_le_mul_of_nonneg_right (by linarith) hL0.le
    nlinarith [mul_le_mul_of_nonneg_right h2π hL0.le, le_abs_self K]
  -- the first moment of the window mass
  have hint : ∫ t in T..(2 * T), windowMass δ T t ≤ π * T / (5 * c) := by
    refine (integral_windowMass_le hδ0 hT0.le).trans ?_
    calc π / δ * (zetaZeroConfig.N (T - 1) (2 * T + 1) : ℝ) ≤ π / δ * (T / 5 * L) :=
          mul_le_mul_of_nonneg_left hNle (by positivity)
      _ = π * T / (5 * c) := by
          rw [hδdef]
          field_simp
  -- the unit-scale mass is negligible at the camera scale
  have hfar : ∀ t ∈ Ioc T (2 * T), 2 / δ ^ 2 * lorentzMass t ≤ Cf := by
    intro t ht
    have hM := lorentzMass_le_log t
    have ht0 : 0 ≤ t := by linarith [ht.1]
    rw [abs_of_nonneg ht0] at hM
    have hlog : Real.log (t + 4) ≤ 2 * L := by
      have h1 : t + 4 ≤ T ^ 2 := by nlinarith [ht.2]
      calc Real.log (t + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) h1
        _ = 2 * L := by rw [Real.log_pow, ← hLdef]; norm_num
    have hM2 : lorentzMass t ≤ 8 * (xiLineTwoLogDerivConstant + 2) * L := by
      have : xiLineTwoLogDerivConstant ≤ xiLineTwoLogDerivConstant * L :=
        le_mul_of_one_le_right hCξ hL1
      nlinarith
    have hcL : 64 ≤ c ^ 2 * L := by
      rw [div_le_iff₀ (by positivity)] at hLd
      linarith
    have hδ2 : δ ^ 2 = c ^ 2 * L * L := by
      rw [hδdef]
      ring
    have hδ64 : 64 * L ≤ δ ^ 2 := by
      rw [hδ2]
      exact mul_le_mul_of_nonneg_right hcL hL0.le
    have hδ2pos : 0 < δ ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hδ2pos, hCf]
    have hsum : 0 ≤ xiLineTwoLogDerivConstant + 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hδ64 hsum]
  have hc2 : 0 < c * Λ := by positivity
  have hfinal : ∀ B : ℝ, B ≤ (2 * π / 5 + 2 * Cf) * E * T / (c * Λ) →
      ENNReal.ofReal B ≤ ENNReal.ofReal ((2 * π / 5 + 2 * Cf) * E * T / (c * Λ)) :=
    fun B hB => ENNReal.ofReal_le_ofReal hB
  rcases le_or_gt (2 * E * Cf) Λ with hbig | hsmall
  · have hx : 0 < Λ / (2 * E) := by positivity
    have hvol := volume_ge_le_of_integral (continuous_windowMass δ T) (windowMass_nonneg δ T) hT0 hx hint
    refine (measure_mono ?_).trans (hvol.trans (hfinal _ ?_))
    · rintro t ⟨ht, hlt⟩
      refine ⟨ht, ?_⟩
      have h1 := hfar t ht
      rw [div_le_iff₀ (by positivity)]
      have h2 : E * (2 / δ ^ 2 * lorentzMass t) ≤ E * Cf := mul_le_mul_of_nonneg_left h1 hE.le
      nlinarith
    · have e1 : π * T / (5 * c) / (Λ / (2 * E)) = (2 * π / 5) * E * T / (c * Λ) := by
        field_simp
      rw [e1]
      refine div_le_div_of_nonneg_right ?_ hc2.le
      have h0 : 0 ≤ 2 * Cf * E * T := by positivity
      nlinarith
  · refine (measure_mono fun t ht => ht.1).trans ?_
    rw [Real.volume_Ioc]
    refine hfinal _ ?_
    rw [le_div_iff₀ hc2]
    have e : 2 * T - T = T := by ring
    rw [e]
    have h1 : T * (c * Λ) ≤ T * Λ := by
      have : c * Λ ≤ Λ := by nlinarith
      exact mul_le_mul_of_nonneg_left this hT0.le
    have h2 : T * Λ ≤ T * (2 * E * Cf) := mul_le_mul_of_nonneg_left hsmall.le hT0.le
    have h3 : 0 ≤ 2 * π / 5 * E * T := by positivity
    nlinarith

/-! ### The count -/

theorem lorentzMass_nonneg (t : ℝ) : 0 ≤ lorentzMass t :=
  tsum_nonneg (lorentzMassTerm_nonneg t)

/-- `ρ` sits in a cluster of at most `N` zeros at the camera `(δ, h, M)`, up to zeros deeper than `a`: at every height of
its window some family `s ∋ ρ` of at most `N` zeros lies in the sector, and the other zeros **deeper than `a`** carry
weighted mass at most an eighth of the Turán constant times the amplitude of `ρ`. Near-line zeros are not constrained. -/
def DeepClusterAt (v : ℝ → ℝ) (δ h : ℝ) (M N : ℕ) (a : ℝ) (ρ : zetaZeroConfig.carrier) : Prop :=
  ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * δ) → ∃ s : Finset zetaZeroConfig.carrier, ρ ∈ s ∧ s.card ≤ N ∧
    (∀ ρ' ∈ s, |(ρ' : ℂ).im - t| * δ ≤ 1 / 10) ∧
    ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      (∀ ρ' ∈ F, a < |(ρ' : ℂ).re - 1 / 2|) →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight δ ((ν : ℝ) * h) t ρ' ≤
      1 / 8 * (∫ u, v u) * turanConstant N M *
        Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ))

/-- At a height where the Lorentzian mass is small, the Turán camera sees the cluster: the near-line zeros
outside it are paid by the Lorentzian mass, the deep ones by hypothesis. -/
theorem exists_nu_ge_of_good (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {δ h t T L A Λ A₀ : ℝ} (hδ1 : 1 ≤ δ) (hh : 0 < h) {M N : ℕ}
    (hN : 1 ≤ N) (hy : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → δ < (ν : ℝ) * h)
    (hyL : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → (ν : ℝ) * h + δ ≤ L) (ht : t ∈ Ioc T (2 * T))
    {s : Finset zetaZeroConfig.carrier} (hcard : s.card ≤ N)
    (hsec : ∀ ρ' ∈ s, |(ρ' : ℂ).im - t| * δ ≤ 1 / 10) {ρ : zetaZeroConfig.carrier} (hρ : ρ ∈ s)
    (hb : 1 / 2 ≤ (ρ : ℂ).re)
    (hA₀ : A₀ = Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - δ)))
    (hdeep : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      (∀ ρ' ∈ F, A / L < |(ρ' : ℂ).re - 1 / 2|) →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight δ ((ν : ℝ) * h) t ρ' ≤ 1 / 8 * (∫ u, v u) * turanConstant N M * A₀)
    (hgood : (profileMass v + 1) * Real.exp A *
      (windowMass δ T t + 2 / δ ^ 2 * lorentzMass t) ≤ Λ)
    (hΛ : Λ ≤ 1 / 8 * (∫ u, v u) * turanConstant N M * A₀) :
    ∃ ν : ℕ, M + 1 ≤ ν ∧ ν ≤ M + N ∧
      1 / 4 * (∫ u, v u) * turanConstant N M * A₀ ≤ ‖zeroField v δ ((ν : ℝ) * h) t‖ := by
  classical
  have hδ0 : 0 < δ := by linarith
  have hPM := profileMass_nonneg v
  have hδsq : 0 < δ ^ 2 := by positivity
  have hmass0 : 0 ≤ windowMass δ T t + 2 / δ ^ 2 * lorentzMass t :=
    add_nonneg (windowMass_nonneg _ _ _) (mul_nonneg (by positivity) (lorentzMass_nonneg t))
  have houter : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
      profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight δ ((ν : ℝ) * h) t ρ' ≤ 1 / 4 * (∫ u, v u) * turanConstant N M * A₀ := by
    intro ν h1 h2 F hF
    have hF2 : Disjoint (F.filter fun ρ' : zetaZeroConfig.carrier =>
        ¬ |(ρ' : ℂ).re - 1 / 2| ≤ A / L) s :=
      Finset.disjoint_of_subset_left (Finset.filter_subset _ _) hF
    have hd := hdeep ν h1 h2 _ hF2 (fun ρ' hρ' => not_le.mp (Finset.mem_filter.mp hρ').2)
    have hy0 : 0 ≤ (ν : ℝ) * h := by positivity
    have hnear := sum_near_weight_le (A := A) (L := L) hδ1 hy0 (hyL ν h1 h2) ht
      (F.filter fun ρ' : zetaZeroConfig.carrier => |(ρ' : ℂ).re - 1 / 2| ≤ A / L)
      (fun ρ' hρ' => (Finset.mem_filter.mp hρ').2)
    have hnear2 : profileMass v * ∑ ρ' ∈ F.filter (fun ρ' : zetaZeroConfig.carrier =>
        |(ρ' : ℂ).re - 1 / 2| ≤ A / L),
        (zetaZeroConfig.mult ρ' : ℝ) * companionWeight δ ((ν : ℝ) * h) t ρ' ≤ Λ := by
      refine le_trans (mul_le_mul_of_nonneg_left hnear hPM) (le_trans ?_ hgood)
      have h4 : 0 ≤ Real.exp A * (windowMass δ T t + 2 / δ ^ 2 * lorentzMass t) :=
        mul_nonneg (Real.exp_pos A).le hmass0
      nlinarith
    rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ' : zetaZeroConfig.carrier =>
      |(ρ' : ℂ).re - 1 / 2| ≤ A / L), mul_add]
    have e : 1 / 4 * (∫ u, v u) * turanConstant N M * A₀ =
        1 / 8 * (∫ u, v u) * turanConstant N M * A₀ +
          1 / 8 * (∫ u, v u) * turanConstant N M * A₀ := by ring
    rw [e]
    exact add_le_add (hnear2.trans hΛ) hd
  obtain ⟨ν, hν1, hν2, hν⟩ := exists_nu_norm_zeroField_ge hv hsupp hv0 hI hδ0 hh hN hy hcard hsec
    hρ hb houter
  refine ⟨ν, hν1, hν2, ?_⟩
  rw [← hA₀] at hν
  have e : 1 / 2 * (∫ u, v u) * turanConstant N M * A₀ -
      1 / 4 * (∫ u, v u) * turanConstant N M * A₀ =
      1 / 4 * (∫ u, v u) * turanConstant N M * A₀ := by ring
  linarith

/-- Separated windows inside `Bad ∪ ⋃_ν D_ν` are paid by the measures of these sets. -/
theorem card_le_of_window_cover {ι : Type*} (S : Finset ι) (g : ι → ℝ) {r B₁ B₂ : ℝ} {Bad : Set ℝ}
    {D : ℕ → Set ℝ} (J : Finset ℕ)
    (hsep : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |g ρ - g ρ'|)
    (hsub : ∀ ρ ∈ S, Ioo (g ρ - r) (g ρ + r) ⊆ Bad ∪ ⋃ ν ∈ J, D ν)
    (hBad : volume Bad ≤ ENNReal.ofReal B₁) (hD : ∀ ν ∈ J, volume (D ν) ≤ ENNReal.ofReal B₂)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂) :
    (S.card : ℝ) * (2 * r) ≤ B₁ + (J.card : ℝ) * B₂ := by
  have hunion := volume_biUnion_windows_eq S g hsep
  have hle : volume (⋃ ρ ∈ S, Ioo (g ρ - r) (g ρ + r)) ≤
      ENNReal.ofReal (B₁ + (J.card : ℝ) * B₂) := by
    refine (measure_mono (Set.iUnion₂_subset hsub)).trans ?_
    refine (measure_union_le _ _).trans ?_
    rw [ENNReal.ofReal_add hB₁ (by positivity)]
    refine add_le_add hBad ?_
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum hD).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  rw [hunion] at hle
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hle

/-- The closing arithmetic of the count, with `y = e^x`, `z = e^A`. -/
theorem deep_count_arith {n c L T Iv κ CB Ep C₀ y z Nr : ℝ} (hc : 0 < c) (hL : 0 < L) (hT : 0 < T)
    (hIv : 0 < Iv) (hκ : 0 < κ) (hCB : 0 < CB) (hEp : 0 < Ep) (hC₀ : 0 < C₀) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (hNr : 0 < Nr)
    (hcard : n * (2 * (1 / (10 * (c * L)))) ≤ CB * (Ep * z) * T / (c * (1 / 8 * Iv * κ * y)) +
      Nr * (C₀ / c ^ 2 * T / (1 / 4 * Iv * κ * y) ^ 2)) :
    n ≤ (40 * CB * Ep / (Iv * κ) + 80 * Nr * C₀ / (c * Iv ^ 2 * κ ^ 2)) * T * L * (z * y⁻¹) := by
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hδ : 0 < c * L := by positivity
  have h1 : n = n * (2 * (1 / (10 * (c * L)))) * (5 * (c * L)) := by
    field_simp
    ring
  rw [h1]
  refine (mul_le_mul_of_nonneg_right hcard (by positivity)).trans ?_
  have e1 : CB * (Ep * z) * T / (c * (1 / 8 * Iv * κ * y)) * (5 * (c * L)) =
      40 * CB * Ep / (Iv * κ) * T * L * (z * y⁻¹) := by
    field_simp
    ring
  have e2 : Nr * (C₀ / c ^ 2 * T / (1 / 4 * Iv * κ * y) ^ 2) * (5 * (c * L)) =
      80 * Nr * C₀ / (c * Iv ^ 2 * κ ^ 2) * T * L * (y ^ 2)⁻¹ := by
    field_simp
    ring
  have h3 : (y ^ 2)⁻¹ ≤ z * y⁻¹ := by
    have h4 : (y ^ 2)⁻¹ ≤ y⁻¹ := by
      refine inv_anti₀ hy0 ?_
      nlinarith
    calc (y ^ 2)⁻¹ ≤ y⁻¹ := h4
      _ ≤ z * y⁻¹ := le_mul_of_one_le_left (by positivity) hz
  calc _ = 40 * CB * Ep / (Iv * κ) * T * L * (z * y⁻¹) +
        80 * Nr * C₀ / (c * Iv ^ 2 * κ ^ 2) * T * L * (y ^ 2)⁻¹ := by rw [add_mul, e1, e2]
    _ ≤ 40 * CB * Ep / (Iv * κ) * T * L * (z * y⁻¹) +
        80 * Nr * C₀ / (c * Iv ^ 2 * κ ^ 2) * T * L * (z * y⁻¹) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left h3 (by positivity))
    _ = _ := by ring

/-- **Near-line zeros cannot block the camera.** Separated zeros of depth `≥ α/L` in `[T+1, 2T−1]`, whose competitors are
at most `N` zeros in the sector and a small mass of zeros deeper than `A/L`, number `≪_{c,N} T L e^{A − (1−4c)α}`. -/
theorem exists_card_zeros_without_deep_companions_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 4) {N : ℕ} (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α A : ℝ, 0 ≤ α → 0 ≤ A →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, 1 / 2 + α / Real.log T ≤ (ρ : ℂ).re ∧ T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        DeepClusterAt v (c * Real.log T) (c / N * Real.log T) (turanStart c N) N (A / Real.log T) ρ) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * T * Real.log T * Real.exp (A - (1 - 4 * c) * α) := by
  classical
  obtain ⟨C₀, L₁, hC₀0, hvol⟩ := exists_volume_zeroField_ge_le_uniform hv hsupp
  obtain ⟨CB, hCB0, hBad⟩ := exists_volume_near_mass_ge_le
  obtain ⟨Iv, hIvdef⟩ : ∃ Iv, Iv = ∫ u, v u := ⟨_, rfl⟩
  rw [← hIvdef] at hI
  obtain ⟨M, hMdef⟩ : ∃ M, M = turanStart c N := ⟨_, rfl⟩
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = turanConstant N M := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκdef]
    exact turanConstant_pos hN M
  obtain ⟨hMup, hMlow⟩ := turanStart_bounds hc0 hc hN
  rw [← hMdef] at hMup hMlow
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hPM := profileMass_nonneg v
  obtain ⟨Ep, hEp⟩ : ∃ Ep, Ep = profileMass v + 1 := ⟨_, rfl⟩
  have hEp0 : 0 < Ep := by linarith
  refine ⟨40 * CB * Ep / (Iv * κ) + 80 * N * C₀ / (c * Iv ^ 2 * κ ^ 2), by positivity, ?_⟩
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hBad, eventually_ge_atTop 3, hL.eventually_ge_atTop (max 1 L₁),
    hL.eventually_ge_atTop (1 / c), hL.eventually_ge_atTop (64 / c ^ 2)]
    with T hBadT hT3 hL₀ hLc hLd α A hα hA S hS hsep
  have hL1 : 1 ≤ Real.log T := (le_max_left _ _).trans hL₀
  have hL₁ : L₁ ≤ Real.log T := (le_max_right _ _).trans hL₀
  have hT0 : 0 < T := by linarith
  have hvolT : ∀ y lam : ℝ, c * Real.log T < y → y + c * Real.log T ≤ (1 - c) * Real.log T → 0 < lam →
      volume {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖zeroField v (c * Real.log T) y t‖} ≤
        ENNReal.ofReal (C₀ / c ^ 2 * T / lam ^ 2) := fun y lam h1 h2 h3 =>
    hvol T c y lam hT3 hL₁ hc0 (by linarith) hLc hLd h1 h2 h3
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hL₁ hLc hLd hBadT hvolT hS hsep ⊢
  have hL0 : 0 < L := by linarith
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * L := by linarith
  obtain ⟨h, hhdef⟩ : ∃ h, h = c / N * L := ⟨_, rfl⟩
  rw [← hMdef, ← hhdef] at hS
  have hh0 : 0 < h := by
    rw [hhdef]
    positivity
  obtain ⟨r, hrdef⟩ : ∃ r, r = 1 / (10 * (c * L)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hrdef]
    positivity
  have hr1 : r ≤ 1 := by
    rw [hrdef, div_le_one (by positivity)]
    linarith
  have h14 : 0 < 1 - 4 * c := by linarith
  have hcentre : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N →
      (1 - 3 * c) * L ≤ (ν : ℝ) * h ∧ (ν : ℝ) * h ≤ (1 - 2 * c) * L := by
    intro ν h1 h2
    have h1' : (M : ℝ) + 1 ≤ ν := by exact_mod_cast h1
    have h2' : (ν : ℝ) ≤ (M : ℝ) + N := by exact_mod_cast h2
    have hcN : 0 < c / N := by positivity
    constructor
    · calc (1 - 3 * c) * L ≤ (((M : ℝ) + 1) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right hMlow hL0.le
        _ ≤ ((ν : ℝ) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1' hcN.le) hL0.le
        _ = (ν : ℝ) * h := by
            rw [hhdef]
            ring
    · calc (ν : ℝ) * h = ((ν : ℝ) * (c / N)) * L := by
            rw [hhdef]
            ring
        _ ≤ (((M : ℝ) + N) * (c / N)) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2' hcN.le) hL0.le
        _ ≤ (1 - 2 * c) * L := mul_le_mul_of_nonneg_right hMup hL0.le
  have hyδ : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → c * L < (ν : ℝ) * h := by
    intro ν h1 h2
    have := (hcentre ν h1 h2).1
    nlinarith
  have hyL : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → (ν : ℝ) * h + c * L ≤ (1 - c) * L := by
    intro ν h1 h2
    have := (hcentre ν h1 h2).2
    nlinarith
  have hyL' : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → (ν : ℝ) * h + c * L ≤ L := by
    intro ν h1 h2
    have := hyL ν h1 h2
    nlinarith
  obtain ⟨x, hxdef⟩ : ∃ x, x = (1 - 4 * c) * α := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    positivity
  obtain ⟨y, hydef⟩ : ∃ y, y = Real.exp x := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by
    rw [hydef]
    exact Real.one_le_exp hx0
  obtain ⟨z, hzdef⟩ : ∃ z, z = Real.exp A := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by
    rw [hzdef]
    exact Real.one_le_exp hA
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  obtain ⟨lam, hlamdef⟩ : ∃ lam, lam = 1 / 4 * Iv * κ * y := ⟨_, rfl⟩
  have hlam : 0 < lam := by
    rw [hlamdef]
    positivity
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = 1 / 8 * Iv * κ * y := ⟨_, rfl⟩
  have hΛ0 : 0 < Λ := by
    rw [hΛdef]
    positivity
  have hE0 : 0 < Ep * z := by positivity
  have hBadvol := hBadT c (Ep * z) Λ hc0 (by linarith) hLc hLd hE0 hΛ0
  have hDν : ∀ ν ∈ Finset.Icc (M + 1) (M + N),
      volume {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖zeroField v (c * L) ((ν : ℝ) * h) t‖} ≤
        ENNReal.ofReal (C₀ / c ^ 2 * T / lam ^ 2) := by
    intro ν hν
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hν
    exact hvolT ((ν : ℝ) * h) lam (hyδ ν h1 h2) (hyL ν h1 h2) hlam
  have hsep' : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |(ρ : ℂ).im - (ρ' : ℂ).im| := by
    intro ρ hρ ρ' hρ' hne
    have e : 2 * r = 1 / (5 * (c * L)) := by
      rw [hrdef]
      field_simp
      norm_num
    rw [e]
    exact hsep ρ hρ ρ' hρ' hne
  have hsub : ∀ ρ ∈ S, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆
      {t | t ∈ Ioc T (2 * T) ∧ Λ ≤ (Ep * z) * (windowMass (c * L) T t +
        2 / (c * L) ^ 2 * lorentzMass t)} ∪
      ⋃ ν ∈ Finset.Icc (M + 1) (M + N),
        {t | t ∈ Ioc T (2 * T) ∧ lam ≤ ‖zeroField v (c * L) ((ν : ℝ) * h) t‖} := by
    intro ρ hρ t ht
    obtain ⟨hdepth, hlow, hhigh, hcl⟩ := hS ρ hρ
    have habs : |t - (ρ : ℂ).im| ≤ r := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have htI : t ∈ Ioc T (2 * T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    by_cases hbad : Λ ≤ (Ep * z) * (windowMass (c * L) T t + 2 / (c * L) ^ 2 * lorentzMass t)
    · exact Or.inl ⟨htI, hbad⟩
    refine Or.inr ?_
    have hgood := (not_le.mp hbad).le
    obtain ⟨s, hρs, hcard, hsec, hdeep⟩ := hcl t (by rw [← hrdef]; exact habs)
    have hαL : 0 ≤ α / L := by positivity
    have hb : 1 / 2 ≤ (ρ : ℂ).re := by linarith
    obtain ⟨A₀, hA₀⟩ : ∃ A₀, A₀ = Real.exp (((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L)) :=
      ⟨_, rfl⟩
    have hexp : y ≤ A₀ := by
      rw [hydef, hA₀]
      refine Real.exp_le_exp.2 ?_
      have h1 : α / L ≤ (ρ : ℂ).re - 1 / 2 := by linarith
      have h2 : (1 - 4 * c) * L ≤ ((M : ℝ) + 1) * h - c * L := by
        have := (hcentre (M + 1) le_rfl (by omega)).1
        push_cast at this
        linarith
      have h3 : 0 ≤ (1 - 4 * c) * L := by positivity
      have h4 : α / L * ((1 - 4 * c) * L) = x := by
        rw [hxdef]
        field_simp
      have h5 : α / L * ((1 - 4 * c) * L) ≤
          ((ρ : ℂ).re - 1 / 2) * (((M : ℝ) + 1) * h - c * L) :=
        mul_le_mul h1 h2 h3 (by linarith)
      linarith
    have hcoef : 0 ≤ 1 / 8 * Iv * κ := by positivity
    have hΛA : Λ ≤ 1 / 8 * Iv * κ * A₀ := by
      rw [hΛdef]
      exact mul_le_mul_of_nonneg_left hexp hcoef
    have hgood' : (profileMass v + 1) * Real.exp A *
        (windowMass (c * L) T t + 2 / (c * L) ^ 2 * lorentzMass t) ≤ Λ := by
      rw [← hEp, ← hzdef]
      exact hgood
    have hdeep' : ∀ ν : ℕ, M + 1 ≤ ν → ν ≤ M + N → ∀ F : Finset zetaZeroConfig.carrier, Disjoint F s →
        (∀ ρ' ∈ F, A / L < |(ρ' : ℂ).re - 1 / 2|) →
        profileMass v * ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) *
          companionWeight (c * L) ((ν : ℝ) * h) t ρ' ≤
        1 / 8 * (∫ u, v u) * turanConstant N M * A₀ := by
      intro ν h1 h2 F hF hFd
      have := hdeep ν h1 h2 F hF hFd
      rw [hA₀]
      exact this
    obtain ⟨ν, hν1, hν2, hν⟩ := exists_nu_ge_of_good hv hsupp hv0 (by rw [← hIvdef]; exact hI) hδ1 hh0
      hN hyδ hyL' htI hcard hsec hρs hb hA₀ hdeep' hgood'
      (by rw [← hIvdef, ← hκdef]; exact hΛA)
    rw [← hIvdef, ← hκdef] at hν
    refine Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_Icc.mpr ⟨hν1, hν2⟩)) ?_
    refine ⟨htI, ?_⟩
    have hcoef4 : 0 ≤ 1 / 4 * Iv * κ := by positivity
    have h6 := mul_le_mul_of_nonneg_left hexp hcoef4
    change lam ≤ _
    rw [hlamdef]
    linarith
  have hcover := card_le_of_window_cover S (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im)
    (Finset.Icc (M + 1) (M + N)) hsep' hsub hBadvol hDν (by positivity) (by positivity)
  have hcardJ : ((Finset.Icc (M + 1) (M + N)).card : ℝ) = N := by
    rw [Nat.card_Icc]
    have e : M + N + 1 - (M + 1) = N := by omega
    rw [e]
  rw [hcardJ, hrdef, hΛdef, hlamdef] at hcover
  have hfinal := deep_count_arith (n := (S.card : ℝ)) hc0 hL0 hT0 hI hκ0 hCB0 hEp0 hC₀0 hy1 hz1 hN0 hcover
  have hexpsplit : Real.exp (A - (1 - 4 * c) * α) = z * y⁻¹ := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_neg, hzdef, hydef, hxdef]
  rw [hexpsplit]
  exact hfinal

end GaloisForLFunctions.MultiscaleMollifiedZetaField
