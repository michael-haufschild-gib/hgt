import GaloisForLFunctions.RHTower.SelbergClass.BarnesFiniteRectangle
import GaloisForLFunctions.HTGeometry.GammaStripSharpDecay

/-!
# Horizontal-edge decay for the finite Barnes rectangle

This module proves only the uniform decay of the two horizontal sides of the
fixed finite Barnes rectangle.  It contains no contour shift, infinite Barnes
identity, or continuation claim.

The negative-real part of the left horizontal edge is handled by a finite
Gamma recurrence, reducing it to the existing positive-strip estimate.
-/

open Complex Filter Set MeasureTheory
open scoped BigOperators Topology Interval

namespace RHTower

noncomputable section

/-- Gamma has the same polynomial-exponential vertical bound on every compact
real strip.  Delegates to the `HTGeometry` layer, which owns the finite
recurrence reducing the strip to the positive half-plane. -/
theorem exists_bound_norm_Gamma_vertical_strip_arbitrary {a b : ℝ} :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ σ t : ℝ, a ≤ σ → σ ≤ b → 1 ≤ |t| →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ C * |t| ^ N * Real.exp (-(Real.pi * |t| / 2)) := by
  obtain ⟨C, N, hC, hbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_sharp_bound_norm_Gamma_strip a b
  refine ⟨C, N, hC, fun σ t hσa hσb ht => ?_⟩
  have hre : ((σ : ℂ) + (t : ℂ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  have hmain := hbound ((σ : ℂ) + (t : ℂ) * Complex.I)
    (by rw [hre]; exact hσa) (by rw [hre]; exact hσb) (by rw [him]; exact ht)
  rwa [him] at hmain

/-- Uniform polynomial-exponential decay of the Barnes integrand across the
horizontal segment of the finite rectangle.  The sign parameter simultaneously
covers `x + T I` and `x - T I`; no limit or contour identity is asserted. -/
theorem exists_bound_norm_barnesJ_horizontal
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    0 < Real.pi - |Complex.arg η| ∧
      ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ ε T x : ℝ,
        |ε| = 1 → |ξ.im| + 1 ≤ T →
        -((m : ℝ) + 1 / 2) ≤ x → x ≤ c →
        ‖barnesJ ξ η ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
          ≤ C * T ^ N * Real.exp (-((Real.pi - |Complex.arg η|) * T)) := by
  refine ⟨sub_pos.mpr harg, ?_⟩
  let L : ℝ := -((m : ℝ) + 1 / 2)
  have hLc : L ≤ c := by
    dsimp [L]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  obtain ⟨C₁, N₁, hC₁, hΓ₁⟩ :=
    exists_bound_norm_Gamma_vertical_strip_arbitrary (a := L) (b := c)
  obtain ⟨C₂, N₂, hC₂, hΓ₂⟩ :=
    GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
      (by linarith : 0 < ξ.re - c) (ξ.re - L)
  have hnormη : ‖η‖ ≠ 0 := norm_ne_zero_iff.mpr hη
  have hcontη : Continuous (fun x : ℝ => ‖η‖ ^ (-x)) :=
    (Real.continuous_const_rpow hnormη).comp continuous_neg
  obtain ⟨Rraw, hRraw⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc L c)).exists_bound_of_continuousOn hcontη.continuousOn
  have hRraw0 : 0 ≤ Rraw :=
    (norm_nonneg _).trans (hRraw L ⟨le_rfl, hLc⟩)
  let R : ℝ := Rraw
  have hR : 0 ≤ R := by simpa [R] using hRraw0
  have hRbound : ∀ x : ℝ, L ≤ x → x ≤ c → ‖η‖ ^ (-x) ≤ R := by
    intro x hxL hxc
    calc
      ‖η‖ ^ (-x) = ‖‖η‖ ^ (-x)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      _ ≤ Rraw := hRraw x ⟨hxL, hxc⟩
      _ = R := rfl
  let B : ℝ := |ξ.im|
  let C : ℝ := C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R
  refine ⟨C, N₁ + N₂, ?_, ?_⟩
  · dsimp [C]
    positivity
  intro ε T x hε hT hxL hxc
  have hxL' : L ≤ x := by simpa [L] using hxL
  have hT0 : 0 ≤ T := by
    have : 0 ≤ |ξ.im| := abs_nonneg _
    linarith
  have hT1 : 1 ≤ T := by linarith [abs_nonneg ξ.im]
  have hεT : |ε * T| = T := by rw [abs_mul, hε, abs_of_nonneg hT0, one_mul]
  have hΓw : ‖Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ C₁ * T ^ N₁ * Real.exp (-(Real.pi * T / 2)) := by
    have h := hΓ₁ x (ε * T) hxL' hxc (by rw [hεT]; exact hT1)
    simpa [hεT] using h
  have hlower : T - B ≤ |ξ.im - ε * T| := by
    have h := abs_sub_le (ε * T) ξ.im 0
    simpa [B, hεT, abs_sub_comm] using h
  have htGamma : 1 ≤ |ξ.im - ε * T| := by linarith
  have hupper0 : |ξ.im - ε * T| ≤ B + T := by
    have h := abs_sub_le ξ.im 0 (ε * T)
    simpa [B, hεT] using h
  have hB : 0 ≤ B := by dsimp [B]; exact abs_nonneg _
  have hupper : |ξ.im - ε * T| ≤ (B + 1) * T := by
    have haux : 0 ≤ B * (T - 1) := mul_nonneg hB (sub_nonneg.mpr hT1)
    linarith
  have hshape : ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I) =
      ((ξ.re - x : ℝ) : ℂ) + ((ξ.im - ε * T : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]
  have hpow₂ : |ξ.im - ε * T| ^ N₂ ≤ ((B + 1) * T) ^ N₂ :=
    pow_le_pow_left₀ (abs_nonneg _) hupper N₂
  have hG₂ : ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ C₂ * ((B + 1) * T) ^ N₂ * Real.exp (-(Real.pi * |ξ.im - ε * T| / 2)) := by
    rw [hshape]
    calc
      ‖Gamma (((ξ.re - x : ℝ) : ℂ) + ((ξ.im - ε * T : ℝ) : ℂ) * I)‖
          ≤ C₂ * |ξ.im - ε * T| ^ N₂ * Real.exp (-(Real.pi * |ξ.im - ε * T| / 2)) :=
            hΓ₂ (ξ.re - x) (ξ.im - ε * T) (by linarith) (by linarith) htGamma
      _ ≤ C₂ * ((B + 1) * T) ^ N₂ * Real.exp (-(Real.pi * |ξ.im - ε * T| / 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow₂ hC₂) (Real.exp_pos _).le
  have hE₂ : Real.exp (-(Real.pi * |ξ.im - ε * T| / 2))
      ≤ Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * T / 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hG₂' : ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ C₂ * ((B + 1) * T) ^ N₂ *
        (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * T / 2))) := by
    have hbase : 0 ≤ (B + 1) * T := mul_nonneg (by linarith) hT0
    have hcoeff : 0 ≤ C₂ * ((B + 1) * T) ^ N₂ :=
      mul_nonneg hC₂ (pow_nonneg hbase _)
    exact hG₂.trans (mul_le_mul_of_nonneg_left hE₂ hcoeff)
  have hΓprod :
      ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)) *
        Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
      ≤ C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * T ^ (N₁ + N₂) *
        Real.exp (-(Real.pi * T)) := by
    calc
      ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)) *
          Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖
        = ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖ *
          ‖Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ := norm_mul _ _
      _ ≤ (C₂ * ((B + 1) * T) ^ N₂ *
            (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * T / 2)))) *
          (C₁ * T ^ N₁ * Real.exp (-(Real.pi * T / 2))) :=
            mul_le_mul hG₂' hΓw (norm_nonneg _) (by positivity)
      _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * T ^ (N₁ + N₂) *
          Real.exp (-(Real.pi * T)) := by
            have hpow : T ^ N₂ * T ^ N₁ = T ^ (N₁ + N₂) := by
              rw [← pow_add, Nat.add_comm]
            have hExp : Real.exp (-(Real.pi * T / 2)) *
                Real.exp (-(Real.pi * T / 2)) = Real.exp (-(Real.pi * T)) := by
              rw [← Real.exp_add]
              congr 1
              ring
            rw [mul_pow]
            calc
              C₂ * ((B + 1) ^ N₂ * T ^ N₂) *
                    (Real.exp (Real.pi * B / 2) * Real.exp (-(Real.pi * T / 2))) *
                  (C₁ * T ^ N₁ * Real.exp (-(Real.pi * T / 2)))
                  = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) *
                      (T ^ N₂ * T ^ N₁) *
                        (Real.exp (-(Real.pi * T / 2)) *
                          Real.exp (-(Real.pi * T / 2))) := by ring
              _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * T ^ (N₁ + N₂) *
                    Real.exp (-(Real.pi * T)) := by rw [hpow, hExp]
  have hηbound : ‖η ^ (-((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      ≤ R * Real.exp (|Complex.arg η| * T) := by
    rw [Complex.norm_cpow_of_ne_zero hη]
    have hre : (-((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)).re = -x := by simp
    have him : (-((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)).im = -(ε * T) := by simp
    rw [hre, him]
    calc
      ‖η‖ ^ (-x) / Real.exp (Complex.arg η * -(ε * T))
          = ‖η‖ ^ (-x) * Real.exp (Complex.arg η * (ε * T)) := by
            rw [show Complex.arg η * -(ε * T) = -(Complex.arg η * (ε * T)) by ring,
              Real.exp_neg, div_inv_eq_mul]
      _ ≤ ‖η‖ ^ (-x) * Real.exp (|Complex.arg η| * T) := by
            apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
              (Real.rpow_nonneg (norm_nonneg _) _)
            calc
              Complex.arg η * (ε * T) ≤ |Complex.arg η * (ε * T)| := le_abs_self _
              _ = |Complex.arg η| * T := by rw [abs_mul, abs_mul, hε, one_mul, abs_of_nonneg hT0]
      _ ≤ R * Real.exp (|Complex.arg η| * T) := by
            exact mul_le_mul_of_nonneg_right (hRbound x hxL' hxc)
              (Real.exp_pos _).le
  unfold barnesJ
  calc
    ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)) *
        Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I) *
          η ^ (-((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖
      = ‖Gamma (ξ - ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)) *
          Gamma ((x : ℂ) + ((ε * T : ℝ) : ℂ) * I)‖ *
          ‖η ^ (-((x : ℂ) + ((ε * T : ℝ) : ℂ) * I))‖ := norm_mul _ _
    _ ≤ (C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * T ^ (N₁ + N₂) *
          Real.exp (-(Real.pi * T))) * (R * Real.exp (|Complex.arg η| * T)) :=
        mul_le_mul hΓprod hηbound (norm_nonneg _) (by positivity)
    _ = C * T ^ (N₁ + N₂) *
        Real.exp (-((Real.pi - |Complex.arg η|) * T)) := by
          have hExp : Real.exp (-(Real.pi * T)) * Real.exp (|Complex.arg η| * T) =
              Real.exp (-((Real.pi - |Complex.arg η|) * T)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          dsimp [C]
          calc
            C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * T ^ (N₁ + N₂) *
                Real.exp (-(Real.pi * T)) * (R * Real.exp (|Complex.arg η| * T))
                = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R * T ^ (N₁ + N₂) *
                    (Real.exp (-(Real.pi * T)) * Real.exp (|Complex.arg η| * T)) := by ring
            _ = C₁ * C₂ * (B + 1) ^ N₂ * Real.exp (Real.pi * B / 2) * R * T ^ (N₁ + N₂) *
                    Real.exp (-((Real.pi - |Complex.arg η|) * T)) := by rw [hExp]

private theorem tendsto_const_mul_pow_mul_exp_neg {δ : ℝ} (hδ : 0 < δ) (N : ℕ) (C : ℝ) :
    Tendsto (fun T : ℝ => C * T ^ N * Real.exp (-(δ * T))) atTop (𝓝 0) := by
  have hbase := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N
  have hscale : Tendsto (fun T : ℝ => δ * T) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hδ tendsto_id
  have hcomp := hbase.comp hscale
  have hmul := hcomp.const_mul ((δ ^ N)⁻¹ * C)
  rw [mul_zero] at hmul
  refine hmul.congr fun T => ?_
  simp only [Function.comp_apply, mul_pow]
  have hδpow : δ ^ N ≠ 0 := pow_ne_zero _ hδ.ne'
  field_simp [hδpow]

/-- The top horizontal integral of the fixed finite Barnes rectangle tends to zero.
This is not an infinite-contour statement. -/
theorem tendsto_barnesJ_top_horizontal_edge
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    Tendsto (fun T : ℝ =>
      ∫ x in -((m : ℝ) + 1 / 2)..c,
        barnesJ ξ η ((x : ℂ) + (T : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨hδ, C, N, _, hbound⟩ := exists_bound_norm_barnesJ_horizontal hc hcξ hη harg
  let L : ℝ := -((m : ℝ) + 1 / 2)
  have hLc : L ≤ c := by
    dsimp [L]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hcore := tendsto_const_mul_pow_mul_exp_neg hδ N C
  have hB : Tendsto (fun T : ℝ =>
      (C * T ^ N * Real.exp (-((Real.pi - |Complex.arg η|) * T))) * |c - L|)
      atTop (𝓝 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcore.mul_const |c - L|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [eventually_ge_atTop (|ξ.im| + 1)] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
    rw [Set.uIoc_of_le hLc] at hx
    have hpoint := hbound 1 T x (by norm_num) hT (by simpa [L] using hx.1.le) hx.2
    simpa using hpoint)

/-- The bottom horizontal integral of the fixed finite Barnes rectangle tends to zero.
This is not an infinite-contour statement. -/
theorem tendsto_barnesJ_bottom_horizontal_edge
    {ξ η : ℂ} {m : ℕ} {c : ℝ} (hc : 0 < c) (hcξ : c < ξ.re)
    (hη : η ≠ 0) (harg : |Complex.arg η| < Real.pi) :
    Tendsto (fun T : ℝ =>
      ∫ x in -((m : ℝ) + 1 / 2)..c,
        barnesJ ξ η ((x : ℂ) - (T : ℂ) * I)) atTop (𝓝 0) := by
  obtain ⟨hδ, C, N, _, hbound⟩ := exists_bound_norm_barnesJ_horizontal hc hcξ hη harg
  let L : ℝ := -((m : ℝ) + 1 / 2)
  have hLc : L ≤ c := by
    dsimp [L]
    have hm : (0 : ℝ) ≤ m := by positivity
    linarith
  have hcore := tendsto_const_mul_pow_mul_exp_neg hδ N C
  have hB : Tendsto (fun T : ℝ =>
      (C * T ^ N * Real.exp (-((Real.pi - |Complex.arg η|) * T))) * |c - L|)
      atTop (𝓝 0) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hcore.mul_const |c - L|
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun T => norm_nonneg _) ?_ hB
  filter_upwards [eventually_ge_atTop (|ξ.im| + 1)] with T hT
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
    rw [Set.uIoc_of_le hLc] at hx
    have hpoint := hbound (-1) T x (by norm_num) hT (by simpa [L] using hx.1.le) hx.2
    simpa [sub_eq_add_neg] using hpoint)

end

end RHTower
