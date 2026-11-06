import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLorentzianMassHasAnExponentialTail

/-!
# Only comparably deep zeros compete

The hyperbolic camera bounds zeros with a large Blaschke factor, given small noise from the zeros outside the family `D`. Here the noise
is removed. Let `ρ` have depth `≈ α/L`, write `x = (1−3c)α` and take `D` to be the zeros deeper than `A/L`, up to a tail
made negligible by summability. On a height where the Lorentzian mass is `≤ Kκ`, which fails only on measure
`≪ T e^{−κ/120000}`:

* a zero shallower than `A/L`, or to the left of the line, has camera weight `≤ e^A` times its Lorentzian weight, at every centre;
* a zero deeper than `A/L` of moderate depth has weight `≤ e^A` times its Lorentzian weight at the low centre.

With `κ = e^{x/8}` and `A ≤ x/2` both are far below the amplitude `e^x`, and the exception is doubly exponentially small. The result is
(`exists_card_hyperbolically_isolated_zeros_le`): separated zeros of depth `≈ α/L` with

* Blaschke factor at least `B₀ ≥ e^{−x/8}` among the zeros deeper than `A/L`, and
* small low-centre mass of the very deep zeros, deeper than `A/(3cL)`,

number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L² T^{1/2}`.

There is no cost in `A`: up to `A = x/2`, all shallower zeros are irrelevant at the Density Hypothesis rate. The conditions left are geometric
and speak only of zeros at least half as deep as `ρ`, hence the title: a zero at the corpus rate must have a comparably deep companion at
hyperbolic distance `O(1)`.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-! ### Weights -/

theorem companionWeight_le_of_exponent {δ y t A : ℝ} {ρ' : ℂ}
    (h : (ρ'.re - 1 / 2) * y + |ρ'.re - 1 / 2| * δ ≤ A) :
    companionWeight δ y t ρ' ≤ Real.exp A * lorentzKernel δ (ρ'.im - t) := by
  unfold companionWeight lorentzKernel
  rw [mul_one_div]
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.2 h) (by positivity)

/-- A zero shallower than `A/L`, or to the left of the line, has exponent `≤ A` at every centre `y ≥ δ` with `y + δ ≤ L`. -/
theorem exponent_le_of_shallow {δ y L A b : ℝ} (hδ : 0 ≤ δ) (hyδ : δ ≤ y) (hyL : y + δ ≤ L) (hL : 0 < L)
    (hA : 0 ≤ A) (hb : b ≤ A / L) : b * y + |b| * δ ≤ A := by
  rcases le_or_gt 0 b with hb0 | hb0
  · rw [abs_of_nonneg hb0]
    have h1 : b * (y + δ) ≤ A / L * L :=
      mul_le_mul hb hyL (by linarith) (by positivity)
    have h2 : A / L * L = A := by
      field_simp
    nlinarith
  · rw [abs_of_neg hb0]
    nlinarith

/-- Every zero of the strip has exponent `≤ L` at a centre with `y + δ ≤ L`. -/
theorem exponent_le_of_strip {δ y L b : ℝ} (hδ : 0 ≤ δ) (hy : 0 ≤ y) (hyL : y + δ ≤ L) (hb : |b| ≤ 1 / 2) :
    b * y + |b| * δ ≤ L := by
  have h1 : b * y ≤ |b| * y := mul_le_mul_of_nonneg_right (le_abs_self b) hy
  have h2 : |b| * (y + δ) ≤ 1 * L := by
    refine mul_le_mul (by linarith) hyL (by positivity) (by norm_num)
  nlinarith

theorem abs_re_sub_half_le (ρ : zetaZeroConfig.carrier) : |(ρ : ℂ).re - 1 / 2| ≤ 1 / 2 := by
  obtain ⟨h1, h2⟩ := zetaZeroConfig.strip ρ ρ.2
  rw [abs_le]
  constructor <;> linarith

/-- The finite Lorentzian masses are summable. -/
theorem summable_mult_lorentzKernel {δ : ℝ} (hδ : 1 ≤ δ) (t : ℝ) :
    Summable fun ρ' : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ' : ℝ) * lorentzKernel δ ((ρ' : ℂ).im - t) := by
  classical
  refine summable_of_sum_le (c := lorentzMass t)
    (fun ρ' => mul_nonneg (Nat.cast_nonneg _) (lorentzKernel_nonneg _ _)) fun F => ?_
  have h2 := sum_mult_unit_le_lorentzMass t (F.image Subtype.val) (fun ρ hρ => by
    obtain ⟨ρ', -, rfl⟩ := Finset.mem_image.mp hρ
    exact ρ'.2)
  rw [Finset.sum_image Subtype.val_injective.injOn] at h2
  refine le_trans (Finset.sum_le_sum fun ρ' _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) h2
  unfold lorentzKernel
  refine one_div_le_one_div_of_le (by positivity) ?_
  have e : (t - (ρ' : ℂ).im) ^ 2 = ((ρ' : ℂ).im - t) ^ 2 := by ring
  rw [e]
  have h1 : 1 ≤ δ ^ 2 := by nlinarith
  nlinarith [sq_nonneg ((ρ' : ℂ).im - t)]

theorem exists_finset_tail_le {ι : Type*} {f : ι → ℝ} (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f) {η : ℝ}
    (hη : 0 < η) : ∃ D₀ : Finset ι, ∀ F : Finset ι, Disjoint F D₀ → ∑ i ∈ F, f i ≤ η := by
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hf η hη
  refine ⟨s, fun F hF => ?_⟩
  have h := hs F hF
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => hf0 i)] at h
  exact h.le

/-! ### One good height -/

/-- At a height of small Lorentzian mass, a zero whose competitors deeper than `A/L` satisfy the two geometric conditions is hyperbolically
isolated. -/
theorem hyperbolicAtHeight_of_good {c L A B₀ Θ K κ α t : ℝ} {ρ : zetaZeroConfig.carrier} (hc0 : 0 < c)
    (hc : c < 1 / 4) (hL : 0 < L) (hδ1 : 1 ≤ c * L) (hA : 1 ≤ A) (hAα : A ≤ α) (hΘ : 0 < Θ)
    (hd : α / L ≤ (ρ : ℂ).re - 1 / 2)
    (hκ : (profileMass v + 1) * Real.exp A * (K * κ) ≤ Θ / 28)
    (hgood : ∀ F : Finset zetaZeroConfig.carrier,
      ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * lorentzKernel (c * L) ((ρ' : ℂ).im - t) ≤ K * κ)
    (hprod : ∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D → (∀ ρ' ∈ D, A / L ≤ (ρ' : ℂ).re - 1 / 2) →
      B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ))
    (hvery : ∀ V : Finset zetaZeroConfig.carrier, (∀ ρ' ∈ V, A / (3 * c * L) < (ρ' : ℂ).re - 1 / 2) →
      profileMass v * ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
        companionWeight (c * L) (2 * (c * L)) t ρ' ≤ Θ / 28) :
    HyperbolicAtHeight v (c * L) (2 * (c * L)) ((1 - 2 * c) * L) (A / L) B₀ (Θ / 14) ρ t := by
  classical
  have hδ0 : 0 < c * L := by linarith
  have hM := profileMass_nonneg v
  have hM1 : 0 < profileMass v + 1 := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hEA : 0 < Real.exp A := Real.exp_pos A
  -- the tail of the zeros
  obtain ⟨η, hη⟩ : ∃ η, η = Θ / (28 * (profileMass v + 1)) := ⟨_, rfl⟩
  have hη0 : 0 < η := by
    rw [hη]
    positivity
  have hsummable := (summable_mult_lorentzKernel hδ1 t).mul_left (Real.exp L)
  obtain ⟨D₀, hD₀⟩ := exists_finset_tail_le
    (fun ρ' => mul_nonneg (Real.exp_pos L).le (mul_nonneg (Nat.cast_nonneg _)
      (lorentzKernel_nonneg _ _))) hsummable hη0
  obtain ⟨D, hD⟩ : ∃ D : Finset zetaZeroConfig.carrier, D = (insert ρ D₀).filter
    (fun ρ' : zetaZeroConfig.carrier => A / L ≤ (ρ' : ℂ).re - 1 / 2) := ⟨_, rfl⟩
  have hdeepρ : A / L ≤ (ρ : ℂ).re - 1 / 2 :=
    (div_le_div_of_nonneg_right hAα hL.le).trans hd
  have hρD : ρ ∈ D := by
    rw [hD]
    exact Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hdeepρ⟩
  have hdeep : ∀ ρ' ∈ D, A / L ≤ (ρ' : ℂ).re - 1 / 2 := fun ρ' h => by
    rw [hD] at h
    exact (Finset.mem_filter.mp h).2
  have hbound : profileMass v * (Real.exp A * (K * κ)) ≤ Θ / 28 := by
    refine le_trans ?_ hκ
    have h0 : 0 ≤ Real.exp A * (K * κ) ∨ Real.exp A * (K * κ) < 0 := le_or_gt 0 _
    rcases h0 with h0 | h0
    · nlinarith
    · exfalso
      have h1 := hgood ∅
      simp only [Finset.sum_empty] at h1
      have h2 : 0 ≤ Real.exp A * (K * κ) := mul_nonneg hEA.le h1
      linarith
  refine ⟨D, hρD, hdeep, hprod D hρD hdeep, ?_, ?_⟩
  · -- the coefficient mass at the low centre
    rw [← Finset.sum_filter_add_sum_filter_not D (fun ρ' : zetaZeroConfig.carrier => (ρ' : ℂ).re - 1 / 2 ≤ A / (3 * c * L)), mul_add]
    have hmod : profileMass v * ∑ ρ' ∈ D.filter (fun ρ' : zetaZeroConfig.carrier => (ρ' : ℂ).re - 1 / 2 ≤ A / (3 * c * L)),
        (zetaZeroConfig.mult ρ' : ℝ) * companionWeight (c * L) (2 * (c * L)) t ρ' ≤ Θ / 28 := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hM) hbound
      refine le_trans (Finset.sum_le_sum (g := fun ρ' : zetaZeroConfig.carrier => Real.exp A * ((zetaZeroConfig.mult ρ' : ℝ) *
        lorentzKernel (c * L) ((ρ' : ℂ).im - t))) fun ρ' hρ' => ?_) ?_
      · obtain ⟨hρ'D, hle⟩ := Finset.mem_filter.mp hρ'
        have hb0 : 0 ≤ (ρ' : ℂ).re - 1 / 2 :=
          le_trans (by positivity) (hdeep ρ' hρ'D)
        have hexp : ((ρ' : ℂ).re - 1 / 2) * (2 * (c * L)) + |(ρ' : ℂ).re - 1 / 2| * (c * L) ≤ A := by
          rw [abs_of_nonneg hb0]
          have h1 := mul_le_mul_of_nonneg_right hle (by positivity : 0 ≤ 3 * c * L)
          have h2 : A / (3 * c * L) * (3 * c * L) = A := by
            field_simp
          nlinarith
        have h3 := companionWeight_le_of_exponent (t := t) hexp
        calc _ ≤ (zetaZeroConfig.mult ρ' : ℝ) *
              (Real.exp A * lorentzKernel (c * L) ((ρ' : ℂ).im - t)) :=
              mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
          _ = _ := by ring
      · rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hgood _) hEA.le
    have hvy := hvery (D.filter fun ρ' : zetaZeroConfig.carrier => ¬ (ρ' : ℂ).re - 1 / 2 ≤ A / (3 * c * L))
      (fun ρ' hρ' => not_le.mp (Finset.mem_filter.mp hρ').2)
    linarith
  · -- the noise of the zeros outside `D`
    intro y hy F hF
    have hyδ : c * L ≤ y := by
      have := hy.1
      linarith
    have hy0 : 0 ≤ y := by linarith
    have hyL : y + c * L ≤ L := by
      have := hy.2
      nlinarith
    rw [← Finset.sum_filter_add_sum_filter_not F (fun ρ' : zetaZeroConfig.carrier => A / L ≤ (ρ' : ℂ).re - 1 / 2), mul_add]
    have hfar : profileMass v * ∑ ρ' ∈ F.filter (fun ρ' : zetaZeroConfig.carrier => A / L ≤ (ρ' : ℂ).re - 1 / 2),
        (zetaZeroConfig.mult ρ' : ℝ) * companionWeight (c * L) y t ρ' ≤ Θ / 28 := by
      have hdis : Disjoint (F.filter fun ρ' : zetaZeroConfig.carrier => A / L ≤ (ρ' : ℂ).re - 1 / 2) D₀ := by
        refine Finset.disjoint_left.2 fun ρ' h1 h2 => ?_
        obtain ⟨h3, h4⟩ := Finset.mem_filter.mp h1
        have hmemD : ρ' ∈ D := by
          rw [hD]
          exact Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem h2, h4⟩
        exact (Finset.disjoint_left.1 hF h3) hmemD
      have htail := hD₀ _ hdis
      have hterm : ∑ ρ' ∈ F.filter (fun ρ' : zetaZeroConfig.carrier => A / L ≤ (ρ' : ℂ).re - 1 / 2),
          (zetaZeroConfig.mult ρ' : ℝ) * companionWeight (c * L) y t ρ' ≤ η := by
        refine le_trans (Finset.sum_le_sum fun ρ' _ => ?_) htail
        have hexp := exponent_le_of_strip hδ0.le hy0 hyL (abs_re_sub_half_le ρ')
        have h3 := companionWeight_le_of_exponent (t := t) hexp
        calc _ ≤ (zetaZeroConfig.mult ρ' : ℝ) *
              (Real.exp L * lorentzKernel (c * L) ((ρ' : ℂ).im - t)) :=
              mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
          _ = _ := by ring
      have h5 : (profileMass v + 1) * η = Θ / 28 := by
        rw [hη]
        field_simp
      have h6 : profileMass v * η ≤ (profileMass v + 1) * η := by nlinarith
      calc _ ≤ profileMass v * η := mul_le_mul_of_nonneg_left hterm hM
        _ ≤ _ := by linarith
    have hnear : profileMass v * ∑ ρ' ∈ F.filter (fun ρ' : zetaZeroConfig.carrier => ¬ A / L ≤ (ρ' : ℂ).re - 1 / 2),
        (zetaZeroConfig.mult ρ' : ℝ) * companionWeight (c * L) y t ρ' ≤ Θ / 28 := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hM) hbound
      refine le_trans (Finset.sum_le_sum (g := fun ρ' : zetaZeroConfig.carrier => Real.exp A * ((zetaZeroConfig.mult ρ' : ℝ) *
        lorentzKernel (c * L) ((ρ' : ℂ).im - t))) fun ρ' hρ' => ?_) ?_
      · have hlt := not_le.mp (Finset.mem_filter.mp hρ').2
        have hexp := exponent_le_of_shallow hδ0.le hyδ hyL hL hA0 hlt.le
        have h3 := companionWeight_le_of_exponent (t := t) hexp
        calc _ ≤ (zetaZeroConfig.mult ρ' : ℝ) *
              (Real.exp A * lorentzKernel (c * L) ((ρ' : ℂ).im - t)) :=
              mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)
          _ = _ := by ring
      · rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hgood _) hEA.le
    linarith

/-! ### The count -/

/-- **Only comparably deep zeros compete, at a given `κ`.** -/
theorem exists_card_zeros_compete_only_with_deep (hv : ContDiff ℝ 2 v) (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1)
    (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 4) :
    ∃ C C₂ K κ₀ : ℝ, 0 < C ∧ 0 < C₂ ∧ 1 ≤ K ∧ 1 ≤ κ₀ ∧ ∀ᶠ T : ℝ in atTop, ∀ α A B₀ κ : ℝ, 0 ≤ α → 1 ≤ A →
      A ≤ α → 0 < B₀ → κ₀ ≤ κ → 1 / c ≤ κ →
      28 * ((profileMass v + 1) * Real.exp A * (K * κ)) ≤
        (∫ u, v u) * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) →
      ∀ Bbad : ℝ, 0 ≤ Bbad → ∀ Bad : Set ℝ, volume Bad ≤ ENNReal.ofReal Bbad →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        (∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D →
          (∀ ρ' ∈ D, A / Real.log T ≤ (ρ' : ℂ).re - 1 / 2) →
          B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) ∧
        ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * (c * Real.log T)) → t ∉ Bad →
        ∀ V : Finset zetaZeroConfig.carrier,
          (∀ ρ' ∈ V, A / (3 * c * Real.log T) < (ρ' : ℂ).re - 1 / 2) →
          profileMass v * ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
            companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤
          (∫ u, v u) * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) / 28) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C₂ * Real.log T * (T * Real.exp (-(κ / 120000)) +
          (Real.log T + 1) * T ^ ((1 : ℝ) / 2)) + Bbad * (5 * (c * Real.log T)) := by
  classical
  obtain ⟨C, hC, hcount⟩ := exists_card_hyperbolic_zeros_le hv hsupp hv0 hI hc0 hc
  obtain ⟨K, C₁, κ₀, hK, hC₁, hκ₀, htail⟩ := exists_volume_lorentz_mass_gt_le
  refine ⟨C, 5 * c * C₁, K, κ₀, hC, by positivity, hK, hκ₀, ?_⟩
  have hL : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hcount, htail, hL.eventually_ge_atTop (1 / c), hL.eventually_ge_atTop (64 / c ^ 2),
    hL.eventually_ge_atTop 1, eventually_ge_atTop 3]
    with T hTcount hTtail hLc hLd hL1 hT3 α A B₀ κ hα hA hAα hB₀ hκκ₀ hκc hΘκ Bbad hBbad0 Bad' hBad' Z hZ hsep
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log T := ⟨_, rfl⟩
  rw [← hLdef] at hTcount hTtail hLc hLd hL1 hZ hsep ⊢
  have hL0 : 0 < L := by linarith
  have hδ1 : 1 ≤ c * L := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  obtain ⟨Θ, hΘdef⟩ : ∃ Θ, Θ = (∫ u, v u) * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) :=
    ⟨_, rfl⟩
  rw [← hΘdef] at hΘκ hZ
  have hα1 : 0 < α + 1 := by linarith
  have hΘ0 : 0 < Θ := by
    rw [hΘdef]
    positivity
  have hBadL := hTtail c κ hc0 hLd hκκ₀ hκc
  have hBbad1 : 0 ≤ C₁ * T * Real.exp (-(κ / 120000)) + C₁ * (L + 1) * T ^ ((1 : ℝ) / 2) := by positivity
  have hBad : volume ({t | t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
      K * κ < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t)} ∪ Bad') ≤
      ENNReal.ofReal (C₁ * T * Real.exp (-(κ / 120000)) + C₁ * (L + 1) * T ^ ((1 : ℝ) / 2) + Bbad) := by
    refine (measure_union_le _ _).trans ?_
    rw [ENNReal.ofReal_add hBbad1 hBbad0]
    exact add_le_add hBadL hBad'
  have hBbad : 0 ≤ C₁ * T * Real.exp (-(κ / 120000)) + C₁ * (L + 1) * T ^ ((1 : ℝ) / 2) + Bbad := by
    positivity
  have hκ' : (profileMass v + 1) * Real.exp A * (K * κ) ≤ Θ / 28 := by
    linarith
  have hmain := hTcount α A B₀ _ hα hA hB₀ hBbad _ hBad Z (fun ρ hρ => by
    obtain ⟨hd1, hd2, h3, h4, hprod, hvery⟩ := hZ ρ hρ
    refine ⟨hd1, hd2, h3, h4, fun t ht htBadU => ?_⟩
    have htBad : ¬ (t ∈ Ioc T (2 * T) ∧ ∃ F : Finset zetaZeroConfig.carrier,
        K * κ < ∑ ρ ∈ F, (zetaZeroConfig.mult ρ : ℝ) * lorentzKernel (c * L) ((ρ : ℂ).im - t)) :=
      fun h => htBadU (Or.inl h)
    have htBad' : t ∉ Bad' := fun h => htBadU (Or.inr h)
    have hr : 1 / (10 * (c * L)) ≤ 1 / 10 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have htI : t ∈ Ioc T (2 * T) := by
      have := abs_le.mp (ht.trans hr)
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hgood : ∀ F : Finset zetaZeroConfig.carrier,
        ∑ ρ' ∈ F, (zetaZeroConfig.mult ρ' : ℝ) * lorentzKernel (c * L) ((ρ' : ℂ).im - t) ≤ K * κ := by
      intro F
      by_contra hF
      exact htBad ⟨htI, F, not_le.mp hF⟩
    rw [← hΘdef]
    exact hyperbolicAtHeight_of_good hc0 hc hL0 hδ1 hA hAα hΘ0 hd1 hκ' hgood hprod (hvery t ht htBad')) hsep
  refine hmain.trans (le_of_eq ?_)
  ring

/-! ### The theorem -/

/-- Polynomial growth is eventually below an exponential. -/
theorem eventually_mul_add_one_le_exp {a : ℝ} (ha : 0 < a) (B : ℝ) :
    ∀ᶠ α : ℝ in atTop, B * (α + 1) ≤ Real.exp (a * α) := by
  filter_upwards [eventually_ge_atTop (max 1 (4 * |B| / a ^ 2))] with α hα
  have h1 : 1 ≤ α := (le_max_left _ _).trans hα
  have h2 : 4 * |B| / a ^ 2 ≤ α := (le_max_right _ _).trans hα
  have h3 := Real.quadratic_le_exp_of_nonneg (x := a * α) (by positivity)
  have h4 : 4 * |B| ≤ α * a ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at h2
  have h5 : B * (α + 1) ≤ |B| * (2 * α) := by
    have h6 : B ≤ |B| := le_abs_self B
    have h7 : 0 ≤ |B| := abs_nonneg B
    nlinarith
  have h8 : |B| * (2 * α) ≤ (a * α) ^ 2 / 2 := by
    have e : (a * α) ^ 2 / 2 = α * a ^ 2 * α / 2 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_right h4 (by linarith : (0 : ℝ) ≤ α)
    linarith
  have h9 : 0 ≤ a * α := by positivity
  linarith

/-- A separated family in the range has at most `5cLT` members. -/
theorem card_le_trivial {ι : Type*} (Z : Finset ι) (g : ι → ℝ) {r T c L : ℝ}
    (h2r : (2 * r)⁻¹ = 5 * (c * L)) (hr0 : 0 < r) (hT : 0 < T)
    (hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * r ≤ |g ρ - g ρ'|)
    (hmem : ∀ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r) ⊆ Ioc T (2 * T)) :
    (Z.card : ℝ) ≤ T * (5 * (c * L)) := by
  have hunion := volume_biUnion_windows_eq Z g hsep
  have hle : volume (⋃ ρ ∈ Z, Ioo (g ρ - r) (g ρ + r)) ≤ ENNReal.ofReal T := by
    refine (measure_mono (Set.iUnion₂_subset hmem)).trans ?_
    rw [Real.volume_Ioc, show 2 * T - T = T by ring]
  rw [hunion] at hle
  have hreal := (ENNReal.ofReal_le_ofReal_iff hT.le).1 hle
  have h2 : 0 < 2 * r := by positivity
  rw [← h2r]
  calc (Z.card : ℝ) = (Z.card : ℝ) * (2 * r) * (2 * r)⁻¹ := by field_simp
    _ ≤ T * (2 * r)⁻¹ := mul_le_mul_of_nonneg_right hreal (by positivity)

/-- The size condition at `κ = e^{x/8}`, `A ≤ x/2`, `B₀ ≥ e^{−x/8}`. -/
theorem size_condition {Iv M K x A B₀ α : ℝ} (hI : 0 < Iv) (hM : 0 ≤ M) (hK : 0 ≤ K) (hα1 : 1 ≤ α + 1)
    (hAx : A ≤ x / 2) (hB₀ : Real.exp (-(x / 8)) ≤ B₀)
    (h4 : 28 * M * K / Iv * (α + 1) ≤ Real.exp (x / 4)) :
    28 * (M * Real.exp A * (K * Real.exp (x / 8))) ≤
      Iv * Real.exp x * B₀ / Real.sqrt (α + 1) := by
  have hα0 : 0 < α + 1 := by linarith
  have hs0 : 0 < Real.sqrt (α + 1) := Real.sqrt_pos.mpr hα0
  have hs1 : Real.sqrt (α + 1) ≤ α + 1 := by
    rw [Real.sqrt_le_left hα0.le]
    nlinarith
  rw [le_div_iff₀ hs0]
  have h7 : Real.exp A ≤ Real.exp (x / 2) := Real.exp_le_exp.2 hAx
  have h8 : 28 * M * K * (α + 1) ≤ Iv * Real.exp (x / 4) := by
    have h := mul_le_mul_of_nonneg_left h4 hI.le
    have e : Iv * (28 * M * K / Iv * (α + 1)) = 28 * M * K * (α + 1) := by
      field_simp
    linarith
  have hexpx : Real.exp x * Real.exp (-(x / 8)) = Real.exp (x / 2) * Real.exp (x / 8) *
      Real.exp (x / 4) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h9 : Real.exp x * Real.exp (-(x / 8)) ≤ Real.exp x * B₀ :=
    mul_le_mul_of_nonneg_left hB₀ (Real.exp_pos _).le
  have hEA : 0 ≤ Real.exp (x / 2) * Real.exp (x / 8) := by positivity
  calc 28 * (M * Real.exp A * (K * Real.exp (x / 8))) * Real.sqrt (α + 1)
      ≤ 28 * (M * Real.exp (x / 2) * (K * Real.exp (x / 8))) * (α + 1) := by
        gcongr
    _ = (28 * M * K * (α + 1)) * (Real.exp (x / 2) * Real.exp (x / 8)) := by ring
    _ ≤ (Iv * Real.exp (x / 4)) * (Real.exp (x / 2) * Real.exp (x / 8)) :=
        mul_le_mul_of_nonneg_right h8 hEA
    _ = Iv * (Real.exp x * Real.exp (-(x / 8))) := by
        rw [hexpx]
        ring
    _ ≤ Iv * (Real.exp x * B₀) := mul_le_mul_of_nonneg_left h9 hI.le
    _ = _ := by ring

/-- The ratio `E ≤ (α+1) E/B₀²` at `B₀ ≤ 1`. -/
theorem le_ratio_of_le_one {α E B₀ : ℝ} (hα : 1 ≤ α + 1) (hE : 0 < E) (hB₀ : 0 < B₀) (hB₀1 : B₀ ≤ 1) :
    E ≤ (α + 1) * E / B₀ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h4 : B₀ ^ 2 ≤ 1 := by nlinarith
  have h5 : E * B₀ ^ 2 ≤ E * 1 := mul_le_mul_of_nonneg_left h4 hE.le
  have h6 : E * 1 ≤ (α + 1) * E := by nlinarith
  linarith

/-- The closing arithmetic in the deep regime. -/
theorem deep_regime_arith {C C₂ X α T L E B₀ E' R : ℝ} (hC : 0 < C) (hC₂ : 0 < C₂) (hX : 0 ≤ X)
    (hα : 1 ≤ α + 1) (hT : 0 < T) (hL : 0 < L) (hE : 0 < E) (hB₀ : 0 < B₀) (hB₀1 : B₀ ≤ 1) (hR : 0 ≤ R)
    (hE' : E' ≤ E) :
    C * (α + 1) * T * L * E / B₀ ^ 2 + C₂ * L * (T * E' + R) ≤
      (C + X + C₂ + C₂) * (α + 1) * T * L * E / B₀ ^ 2 + (C + X + C₂ + C₂) * (L * R) := by
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (α + 1) * E / B₀ ^ 2 := ⟨_, rfl⟩
  have hratio : E ≤ Q := by
    rw [hQ]
    exact le_ratio_of_le_one hα hE hB₀ hB₀1
  have e1 : C * (α + 1) * T * L * E / B₀ ^ 2 = C * (T * L * Q) := by
    rw [hQ]
    ring
  have e2 : (C + X + C₂ + C₂) * (α + 1) * T * L * E / B₀ ^ 2 = (C + X + C₂ + C₂) * (T * L * Q) := by
    rw [hQ]
    ring
  rw [e1, e2]
  have hTL : 0 < T * L := by positivity
  have hQ0 : 0 < Q := by linarith
  have h1 : T * L * E' ≤ T * L * Q := mul_le_mul_of_nonneg_left (hE'.trans hratio) hTL.le
  have h2 : C₂ * (T * L * E') ≤ C₂ * (T * L * Q) := mul_le_mul_of_nonneg_left h1 hC₂.le
  have h3 : 0 ≤ (X + C₂) * (T * L * Q) := by positivity
  have h4 : 0 ≤ (C + X + C₂) * (L * R) := by positivity
  nlinarith

/-- The closing arithmetic in the shallow regime: the trivial count at bounded depth. -/
theorem shallow_regime_arith {C' X α T L E B₀ n R : ℝ} {c : ℝ} (hc : 0 < c) (hC' : 0 ≤ C') (hX : 1 ≤ X * E)
    (hX0 : 0 ≤ X) (hα : 1 ≤ α + 1) (hT : 0 < T) (hL : 0 < L) (hE : 0 < E) (hB₀ : 0 < B₀) (hB₀1 : B₀ ≤ 1)
    (hR : 0 ≤ R) (hn : n ≤ T * (5 * (c * L))) :
    n ≤ (C' + 5 * c * X) * (α + 1) * T * L * E / B₀ ^ 2 + (C' + 5 * c * X) * (L * R) := by
  have h4 : 1 ≤ (α + 1) * (X * E) / B₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity), one_mul]
    have h5 : B₀ ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have hbound : T * (5 * (c * L)) ≤ 5 * c * X * (α + 1) * T * L * E / B₀ ^ 2 := by
    calc T * (5 * (c * L)) = 5 * c * T * L * 1 := by ring
      _ ≤ 5 * c * T * L * ((α + 1) * (X * E) / B₀ ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  have h9 : 0 ≤ C' * (α + 1) * T * L * E / B₀ ^ 2 := by positivity
  have h10 : 0 ≤ (C' + 5 * c * X) * (L * R) := by positivity
  have e1 : (C' + 5 * c * X) * (α + 1) * T * L * E / B₀ ^ 2 =
      5 * c * X * (α + 1) * T * L * E / B₀ ^ 2 + C' * (α + 1) * T * L * E / B₀ ^ 2 := by ring
  rw [e1]
  linarith

/-- The depth beyond which the size conditions hold. -/
theorem exists_depth_threshold {c : ℝ} (hc : c < 1 / 3) (B₁ κ₁ : ℝ) :
    ∃ α₁ : ℝ, 0 ≤ α₁ ∧ ∀ α : ℝ, α₁ ≤ α →
      B₁ * (α + 1) ≤ Real.exp ((1 - 3 * c) * α / 4) ∧ κ₁ ≤ Real.exp ((1 - 3 * c) * α / 8) ∧
        240000 * ((1 - 3 * c) * α) ≤ Real.exp ((1 - 3 * c) * α / 8) := by
  have h13 : 0 < 1 - 3 * c := by linarith
  have ha1 : 0 < (1 - 3 * c) / 4 := by positivity
  have ha2 : 0 < (1 - 3 * c) / 8 := by positivity
  have h1 := eventually_mul_add_one_le_exp ha1 B₁
  have h2 := eventually_mul_add_one_le_exp ha2 (max κ₁ 0)
  have h3 := eventually_mul_add_one_le_exp ha2 (240000 * (1 - 3 * c))
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp (h1.and (h2.and h3))
  refine ⟨max α₀ 0, le_max_right _ _, fun α hα => ?_⟩
  have hα0 : 0 ≤ α := (le_max_right _ _).trans hα
  obtain ⟨h4, h5, h6⟩ := hα₀ α ((le_max_left _ _).trans hα)
  have e1 : (1 - 3 * c) / 4 * α = (1 - 3 * c) * α / 4 := by ring
  have e2 : (1 - 3 * c) / 8 * α = (1 - 3 * c) * α / 8 := by ring
  rw [e1] at h4
  rw [e2] at h5 h6
  refine ⟨h4, ?_, ?_⟩
  · have h7 : max κ₁ 0 ≤ max κ₁ 0 * (α + 1) :=
      le_mul_of_one_le_right (le_max_right _ _) (by linarith)
    linarith [le_max_left κ₁ 0]
  · have h7 : 240000 * (1 - 3 * c) * α ≤ 240000 * (1 - 3 * c) * (α + 1) := by
      have : 0 ≤ 240000 * (1 - 3 * c) := by positivity
      nlinarith
    nlinarith

/-- **Only comparably deep zeros compete.** Separated zeros of depth in `[α/L, (α+1)/L]`, `x = (1−3c)α`, whose Blaschke factor among the zeros deeper
than `A/L`, `A ≤ x/2`, is at least `B₀ ≥ e^{−x/8}`, and near which the zeros deeper than `A/(3cL)` have small mass at the low centre, number
`≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L² T^{1/2}`. -/
theorem exists_card_hyperbolically_isolated_zeros_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α A B₀ : ℝ, 0 ≤ α → 1 ≤ A →
      A ≤ (1 - 3 * c) * α / 2 → Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ Bbad : ℝ, 0 ≤ Bbad → ∀ Bad : Set ℝ, volume Bad ≤ ENNReal.ofReal Bbad →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        (∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D →
          (∀ ρ' ∈ D, A / Real.log T ≤ (ρ' : ℂ).re - 1 / 2) →
          B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) ∧
        ∀ t : ℝ, |t - (ρ : ℂ).im| ≤ 1 / (10 * (c * Real.log T)) → t ∉ Bad →
        ∀ V : Finset zetaZeroConfig.carrier,
          (∀ ρ' ∈ V, A / (3 * c * Real.log T) < (ρ' : ℂ).re - 1 / 2) →
          profileMass v * ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
            companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤
          (∫ u, v u) * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) / 28) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * (Real.log T * ((Real.log T + 1) * T ^ ((1 : ℝ) / 2))) + Bbad * (5 * (c * Real.log T)) := by
  classical
  obtain ⟨C, C₂, K, κ₀, hC, hC₂, hK, hκ₀, hmain⟩ :=
    exists_card_zeros_compete_only_with_deep hv hsupp hv0 hI hc0 hc
  have h13 : 0 < 1 - 3 * c := by linarith
  have hPM := profileMass_nonneg v
  obtain ⟨α₁, hα₁0, hα₁⟩ := exists_depth_threshold (c := c) (by linarith)
    (28 * (profileMass v + 1) * K / ∫ u, v u) (max κ₀ (1 / c))
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = Real.exp (2 * ((1 - 3 * c) * α₁)) := ⟨_, rfl⟩
  have hX₀1 : 0 < X₀ := by
    rw [hX₀]
    exact Real.exp_pos _
  refine ⟨C + 5 * c * X₀ + C₂ + C₂, by positivity, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_ge_atTop (1 / c),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 3]
    with T hT hLc hL1 hT3 α A B₀ hα hA hAx hB₀low hB₀1 Bbad hBbad0 Bad hBad Z hZ hsep
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hδ1 : 1 ≤ c * Real.log T := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hB₀ : 0 < B₀ := lt_of_lt_of_le (Real.exp_pos _) hB₀low
  have hα1 : 1 ≤ α + 1 := by linarith
  have hR0 : 0 ≤ (Real.log T + 1) * T ^ ((1 : ℝ) / 2) := by positivity
  rcases le_or_gt α₁ α with hbig | hsmall
  · obtain ⟨h4, h5, h6⟩ := hα₁ α hbig
    have hAα : A ≤ α := by
      have h7 : (1 - 3 * c) * α / 2 ≤ α := by nlinarith
      linarith
    have hsize := size_condition (x := (1 - 3 * c) * α) (A := A) (B₀ := B₀) (α := α) hI
      (by linarith : 0 ≤ profileMass v + 1) (by linarith : 0 ≤ K) hα1 hAx hB₀low h4
    have hres := hT α A B₀ (Real.exp ((1 - 3 * c) * α / 8)) hα hA hAα hB₀
      ((le_max_left _ _).trans h5) ((le_max_right _ _).trans h5) hsize Bbad hBbad0 Bad hBad Z hZ hsep
    refine hres.trans ?_
    have hE' : Real.exp (-(Real.exp ((1 - 3 * c) * α / 8) / 120000)) ≤
        Real.exp (-(2 * (1 - 3 * c) * α)) := by
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have hfin := deep_regime_arith (C := C) (C₂ := C₂) (X := 5 * c * X₀) hC hC₂ (by positivity) hα1 hT0 hL0
      (Real.exp_pos _) hB₀ hB₀1 hR0 hE'
    refine (add_le_add hfin (le_refl _)).trans (le_of_eq ?_)
    ring
  · obtain ⟨r, hr⟩ : ∃ r, r = 1 / (10 * (c * Real.log T)) := ⟨_, rfl⟩
    have hδ0 : 0 < c * Real.log T := by linarith
    have hr0 : 0 < r := by
      rw [hr]
      positivity
    have hr1 : r ≤ 1 := by
      rw [hr, div_le_one (by positivity)]
      linarith
    have h2r : (2 * r)⁻¹ = 5 * (c * Real.log T) := by
      rw [hr]
      field_simp
      norm_num
    have hsep' : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → 2 * r ≤ |(ρ : ℂ).im - (ρ' : ℂ).im| := by
      intro ρ hρ ρ' hρ' hne
      have e : 2 * r = 1 / (5 * (c * Real.log T)) := by
        rw [hr]
        field_simp
        norm_num
      rw [e]
      exact hsep ρ hρ ρ' hρ' hne
    have hmem : ∀ ρ ∈ Z, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆ Ioc T (2 * T) := by
      intro ρ hρ t ht
      obtain ⟨-, -, hlow, hhigh, -⟩ := hZ ρ hρ
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have htriv := card_le_trivial Z (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) h2r hr0 hT0 hsep' hmem
    have hX : 1 ≤ X₀ * Real.exp (-(2 * (1 - 3 * c) * α)) := by
      rw [hX₀, ← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    have hfin := shallow_regime_arith (C' := C + C₂ + C₂) hc0 (by positivity) hX hX₀1.le hα1 hT0 hL0
      (Real.exp_pos _) hB₀ hB₀1 hR0 htriv
    have hBnn : 0 ≤ Bbad * (5 * (c * Real.log T)) := by positivity
    refine (hfin.trans (le_add_of_nonneg_right hBnn)).trans (le_of_eq ?_)
    ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
