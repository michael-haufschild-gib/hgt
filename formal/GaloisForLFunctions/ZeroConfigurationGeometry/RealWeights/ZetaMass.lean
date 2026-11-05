import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount


/-!
# Sharp local multiplicity mass for ζ

Backlund's explicit rectangle count bounds the total multiplicity of any finite
set of zeros. A central height band of radius three quarters of its height
retains every density coefficient strictly larger than `1/(2π)`.
-/

open Complex MeasureTheory Set
open RHTower Zeta23 Zeta23.RvM

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- A finite set of zeros contributes no more than the full rectangle count. -/
theorem zeta_mass_le_ncount {T₁ T₂ : ℝ} (s : Finset ℂ)
    (hs : ∀ z ∈ s, z ∈ zerosIn T₁ T₂) :
    ∑ z ∈ s, zetaZeroConfig.mult z ≤ Ncount T₁ T₂ := by
  classical
  have hfin := zerosIn_finite T₁ T₂
  rw [Ncount, finsum_mem_eq_finite_toFinset_sum _ hfin]
  change ∑ z ∈ s, zeroMult z ≤ ∑ z ∈ hfin.toFinset, zeroMult z
  exact Finset.sum_le_sum_of_subset fun z hz =>
    (Set.Finite.mem_toFinset hfin).mpr (hs z hz)

/-- The sharp local ζ count with multiplicity, with numerical constants from height ten. -/
theorem zeta_mass_le_sharp_explicit (x y : ℝ) (hx : 10 ≤ x) (hxy : x ≤ y) :
    ∀ s : Finset ℂ, (∀ z ∈ s, IsNontrivialZero z ∧ z.im ∈ Icc x y) →
      (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) ≤ (y - x + 3) * ((Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) /
        (2 * Real.pi)) + 200 * Real.log (y + 2) + 1 := by
  intro s hs
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (x - 2)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight y
  have hT₁a : x - 2 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ x - 1 := by have := hT₁mem.2; linarith
  have hT₂a : y ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ y + 1 := hT₂mem.2
  have h8 : 8 ≤ T₁ := by linarith only [hx, hT₁a]
  have h12 : T₁ < T₂ := by linarith
  have hcount := ncount_le_of_goodHeight (TB := 4) (CB := 100)
    (fun T hT hg => backlund_horizontal_explicit hT hg)
    (by norm_num only [max_eq_right (by norm_num : (4 : ℝ) ≤ 8)]; exact h8) h12 hg1 hg2
  norm_num at hcount
  have hcard : (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) ≤ Ncount T₁ T₂ := by
    exact_mod_cast zeta_mass_le_ncount s fun z hz =>
      ⟨(hs z hz).1, by linarith [(hs z hz).2.1], by linarith [(hs z hz).2.2]⟩
  -- compare the constants
  have hpos : 0 < 2 * Real.pi := by positivity
  have hlogpos : 0 ≤ Real.log ((T₂ + 1) / (2 * Real.pi)) :=
    Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
  have hD1 : (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) ≤
      (Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ hpos.le
    have h1' : Real.log ((T₂ + 1) / (2 * Real.pi)) ≤ Real.log ((y + 2) / (2 * Real.pi)) :=
      Real.log_le_log (div_pos (by linarith) hpos)
        (div_le_div_of_nonneg_right (by linarith) hpos.le)
    have h2' : 6 / T₁ ≤ 6 / (x - 2) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hT₁a
    linarith
  have hD0 : 0 ≤ (Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi) := by
    have : 0 < 6 / T₁ := div_pos (by norm_num) (by linarith)
    exact div_nonneg (by linarith) hpos.le
  have hlen : T₂ - T₁ ≤ y - x + 3 := by linarith
  have hprod : (T₂ - T₁) * ((Real.log ((T₂ + 1) / (2 * Real.pi)) + 6 / T₁) / (2 * Real.pi)) ≤
      (y - x + 3) * ((Real.log ((y + 2) / (2 * Real.pi)) + 6 / (x - 2)) / (2 * Real.pi)) :=
    mul_le_mul hlen hD1 hD0 (by linarith)
  have hl1 : Real.log T₁ ≤ Real.log (y + 2) := Real.log_le_log (by linarith) (by linarith)
  have hl2 : Real.log T₂ ≤ Real.log (y + 2) := Real.log_le_log (by linarith) (by linarith)
  have hlogs : (100 : ℝ) * (Real.log T₁ + Real.log T₂) ≤ 2 * (100 : ℝ) * Real.log (y + 2) := by
    linarith only [hl1, hl2]
  linarith


/-- The multiplicity count in a central height band retains the sharp density. -/
theorem zeta_mass_le_sharp_centred_explicit (X R : ℝ) (hR : 0 ≤ R) (hX : 10 ≤ X - R) :
    ∀ x y : ℝ, x ≤ y → ∀ s : Finset ℂ,
      (∀ z ∈ s, IsNontrivialZero z ∧ |z.im - X| ≤ R ∧ z.im ∈ Icc x y) →
        (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) ≤ (Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) /
            (2 * Real.pi) * (y - x) +
          (3 * ((Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) / (2 * Real.pi)) +
            200 * Real.log (X + R + 2) + 1) := by
  intro x y hxy s hs
  set D := (Real.log ((X + R + 2) / (2 * Real.pi)) + 6 / (X - R - 2)) / (2 * Real.pi) with hD
  have hpos : 0 < 2 * Real.pi := by positivity
  have hD0 : 0 ≤ D := by
    have hl : 0 ≤ Real.log ((X + R + 2) / (2 * Real.pi)) :=
      Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
    have : 0 < 6 / (X - R - 2) := div_pos (by norm_num) (by linarith)
    rw [hD]; exact div_nonneg (by linarith) hpos.le
  -- the effective interval `[x', y'] = [x, y] ∩ [X − R, X + R]`
  set x' := max x (X - R) with hx'
  set y' := min y (X + R) with hy'
  by_cases hne : x' ≤ y'
  · have hsub : ∀ z ∈ s, IsNontrivialZero z ∧ z.im ∈ Icc x' y' := fun z hz => by
      obtain ⟨h1, h2, h3, h4⟩ := hs z hz
      rw [abs_le] at h2
      exact ⟨h1, max_le h3 (by linarith [h2.1]), le_min h4 (by linarith [h2.2])⟩
    have hx'T : 10 ≤ x' := le_trans hX (le_max_right _ _)
    have hc := zeta_mass_le_sharp_explicit x' y' hx'T hne s hsub
    have hDle : (Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) / (2 * Real.pi) ≤ D := by
      rw [hD]
      apply div_le_div_of_nonneg_right _ hpos.le
      have h1 : Real.log ((y' + 2) / (2 * Real.pi)) ≤ Real.log ((X + R + 2) / (2 * Real.pi)) :=
        Real.log_le_log (div_pos (by linarith) hpos)
          (div_le_div_of_nonneg_right (by linarith [min_le_right y (X + R)]) hpos.le)
      have h2 : 6 / (x' - 2) ≤ 6 / (X - R - 2) :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith [le_max_right x (X - R)])
      linarith
    have hlen : y' - x' ≤ y - x := by
      linarith [min_le_left y (X + R), le_max_left x (X - R)]
    have hlog : Real.log (y' + 2) ≤ Real.log (X + R + 2) :=
      Real.log_le_log (by linarith) (by linarith [min_le_right y (X + R)])
    have hDy : 0 ≤ (Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) / (2 * Real.pi) := by
      have hl : 0 ≤ Real.log ((y' + 2) / (2 * Real.pi)) :=
        Real.log_nonneg ((one_le_div hpos).mpr (by linarith [Real.pi_lt_four]))
      have : 0 < 6 / (x' - 2) := div_pos (by norm_num) (by linarith)
      exact div_nonneg (by linarith) hpos.le
    have hprod : (y' - x' + 3) * ((Real.log ((y' + 2) / (2 * Real.pi)) + 6 / (x' - 2)) /
        (2 * Real.pi)) ≤ D * (y - x) + 3 * D := by
      have := mul_le_mul (show y' - x' + 3 ≤ y - x + 3 by linarith) hDle hDy (by linarith)
      linarith
    have hAlog : 200 * Real.log (y' + 2) ≤ 200 * Real.log (X + R + 2) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num)
    linarith
  · -- the effective interval is empty, so is `s`
    have hempty : s = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun z hz => hne ?_
      obtain ⟨_, h2, h3, h4⟩ := hs z hz
      rw [abs_le] at h2
      exact (max_le h3 (by linarith [h2.1])).trans (le_min h4 (by linarith [h2.2]))
    rw [hempty, Finset.sum_empty]
    have hlogp : 0 ≤ Real.log (X + R + 2) := Real.log_nonneg (by linarith)
    have : 0 ≤ D * (y - x) := mul_nonneg hD0 (by linarith)
    have : 0 ≤ 200 * Real.log (X + R + 2) := mul_nonneg (by norm_num) hlogp
    linarith

/-- The actual ζ multiplicity mass satisfies the camera density bound at an explicit height. -/
theorem zeta_mass_wide_camera_band_le {θ T : ℝ} (hθ : 1 < θ)
    (hT : max 40 (zetaCameraCountHeight θ) ≤ T) (s : Finset ℂ) (x y : ℝ) (hxy : x ≤ y)
    (hs : ∀ z ∈ s, IsNontrivialZero z ∧ |z.im - T| ≤ 3 * T / 4 ∧ z.im ∈ Icc x y) :
    (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) ≤ θ / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) * (y - x) +
      zetaCameraCountConstant θ * Real.log (T / (2 * Real.pi)) := by
  have h40 : 40 ≤ T := (le_max_left _ _).trans hT
  have hTc : zetaCameraCountHeight θ ≤ T := (le_max_right _ _).trans hT
  have hT0 : 0 < T := by linarith only [h40]
  have hπ : 0 < 2 * Real.pi := by positivity
  set u := Real.log (T / (2 * Real.pi)) with hu
  have hupper : Real.exp (max 1 (2 / (θ - 1))) ≤ T / (2 * Real.pi) := by
    apply (le_div_iff₀ hπ).mpr
    have h := (le_max_right _ _).trans hTc
    change 2 * Real.pi * Real.exp (max 1 (2 / (θ - 1))) ≤ T at h
    linarith only [h]
  have huMax : max 1 (2 / (θ - 1)) ≤ u := by
    rw [hu, ← Real.log_exp (max 1 (2 / (θ - 1)))]
    exact Real.log_le_log (Real.exp_pos _) hupper
  have hu1 : 1 ≤ u := (le_max_left _ _).trans huMax
  have hgap : 2 ≤ u * (θ - 1) :=
    (div_le_iff₀ (by linarith only [hθ] : 0 < θ - 1)).mp ((le_max_right _ _).trans huMax)
  have hcount := zeta_mass_le_sharp_centred_explicit T (3 * T / 4)
    (by linarith only [h40]) (by linarith only [h40]) x y hxy s hs
  set D := (Real.log ((T + 3 * T / 4 + 2) / (2 * Real.pi)) + 6 / (T - 3 * T / 4 - 2)) /
    (2 * Real.pi) with hD
  change (∑ z ∈ s, (zetaZeroConfig.mult z : ℝ)) ≤ D * (y - x) +
    (3 * D + 200 * Real.log (T + 3 * T / 4 + 2) + 1) at hcount
  have hfrac : 6 / (T - 3 * T / 4 - 2) ≤ 1 :=
    (div_le_one (by linarith only [h40])).mpr (by linarith only [h40])
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hlogshift : Real.log ((T + 3 * T / 4 + 2) / (2 * Real.pi)) ≤ u + 1 := by
    have h := Real.log_le_log (div_pos (by linarith only [h40]) hπ)
      (show (T + 3 * T / 4 + 2) / (2 * Real.pi) ≤ 2 * (T / (2 * Real.pi)) by
        calc
          _ ≤ (2 * T) / (2 * Real.pi) :=
            div_le_div_of_nonneg_right (by linarith only [h40]) hπ.le
          _ = _ := by ring)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (div_pos hT0 hπ).ne', ← hu] at h
    linarith only [h, hlog2]
  have hDθ : D ≤ θ / (2 * Real.pi) * u := by
    rw [hD]
    calc
      _ ≤ (u + 2) / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (by linarith only [hlogshift, hfrac]) hπ.le
      _ ≤ θ * u / (2 * Real.pi) :=
        div_le_div_of_nonneg_right (by nlinarith only [hgap]) hπ.le
      _ = _ := by ring
  have hlog4π : 0 ≤ Real.log (4 * Real.pi) :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three])
  have hlogbase : Real.log (T + 3 * T / 4 + 2) ≤ u + Real.log (4 * Real.pi) := by
    have he : 2 * T = (4 * Real.pi) * (T / (2 * Real.pi)) := by field_simp; ring
    have h := Real.log_le_log (by linarith only [h40] : 0 < T + 3 * T / 4 + 2)
      (show T + 3 * T / 4 + 2 ≤ 2 * T by linarith only [h40])
    rw [he, Real.log_mul (by positivity : (4 * Real.pi) ≠ 0) (div_pos hT0 hπ).ne', ← hu] at h
    linarith only [h]
  have hlogbound : Real.log (T + 3 * T / 4 + 2) ≤ (1 + Real.log (4 * Real.pi)) * u := by
    have hmul := mul_le_mul_of_nonneg_left hu1 hlog4π
    nlinarith only [hlogbase, hmul]
  have hmain := mul_le_mul_of_nonneg_right hDθ (sub_nonneg.mpr hxy)
  have herror : 3 * D + 200 * Real.log (T + 3 * T / 4 + 2) + 1 ≤
      zetaCameraCountConstant θ * u := by
    calc
      _ ≤ 3 * (θ / (2 * Real.pi) * u) +
          200 * ((1 + Real.log (4 * Real.pi)) * u) + u := by
        linarith only [hDθ, hlogbound, hu1]
      _ = _ := by unfold zetaCameraCountConstant; ring
  linarith only [hcount, hmain, herror]

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_mass_le_ncount
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_mass_le_sharp_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_mass_le_sharp_centred_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_mass_wide_camera_band_le
