import GaloisForLFunctions.SquareRootThreshold.ZetaHidingNeedsNearTopTwinsAtEveryLag

/-!
# An attained top of `ζ` is visible at an explicit lag

`AttainedDepthIsVisible` shows that a zero of largest real part makes some lag functional negative,
without a bound on the lag. With the uniform twin radius the bound is explicit: an attained top is
`1/V`-near the top for every `V`, so positivity on `[0, V]` would give, at every `V`, a pair of zeros
closer than `(R_w(γ₀) + κ_w)/V`, both in a fixed box near the top; finitely many zeros lie in the box.

* **Separation** (`exists_separation_in_box`). The zeros with `|Im ρ| ≤ H` and `Re ρ ≥ ½ + d` keep a
  positive mutual distance `g`.
* **Explicit lag** (`zeta_attained_top_visible`, `zeta_attained_top_first_negative_lag`). Let
  `½ + z₀` be a zero of largest real part `½ + δ₀` at height `γ₀ ≥ T_w`. The record of the family
  modulated to `γ₀` sits at depth `≥ δ₀/2` and height `≤ Γ`; its twin lies within `(R_w + κ_w)/V`, hence
  in the box `|Im| ≤ Γ + 1`, `Re ≥ ½ + δ₀/4`. So some difference test of the modulated bump is Weil
  negative at a lag
  `v ≤ max(V_w(z₀), (R_w(γ₀) + κ_w) max(1, 1/g, 4/δ₀))`,
  `R_w(γ₀) = 73(κ_w + π log log(180(Γ + 6)) + 4π)`, `V_w(z₀) ≍ (log log γ₀)/δ₀`.

The first negative lag of an attained top is `O_w((1 + log log γ₀)/min(g, δ₀))`: depth, height and
the separation `g` of the zeros near the top are the only data. The same bound fails for a
non-attained top only through `g → 0` along the near-top zeros, which is the twin alternative of
`zeta_hiding_needs_near_top_twins`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **Separation in a box.** The zeros of `ζ` with `|Im ρ| ≤ H` and `Re ρ ≥ ½ + d` keep a positive
mutual distance. -/
theorem exists_separation_in_box (H d : ℝ) :
    ∃ g > 0, ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ H → |ρ'.im| ≤ H → 1 / 2 + d ≤ ρ.re → 1 / 2 + d ≤ ρ'.re → g ≤ ‖ρ - ρ'‖ := by
  classical
  set B := zetaZeroConfig.carrier ∩ {ρ : ℂ | -|H| - 1 < ρ.im ∧ ρ.im ≤ |H|} with hB
  have hBfin : B.Finite := zetaZeroConfig.finite_window _ _
  set P := (hBfin.toFinset ×ˢ hBfin.toFinset).filter fun p => p.1 ≠ p.2 with hP
  by_cases hPe : P.Nonempty
  · set g := (P.image fun p => ‖p.1 - p.2‖).min' (hPe.image _) with hg
    have hg0 : 0 < g := by
      obtain ⟨p, hp, hpg⟩ := Finset.mem_image.mp ((P.image fun p => ‖p.1 - p.2‖).min'_mem
        (hPe.image _))
      rw [hg, ← hpg]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
    refine ⟨g, hg0, fun ρ hρ ρ' hρ' hne h1 h2 _ _ => ?_⟩
    have hmem : ∀ x ∈ zetaZeroConfig.carrier, |x.im| ≤ H → x ∈ hBfin.toFinset := fun x hx hxH => by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hx, ?_, ?_⟩
      · linarith [neg_abs_le x.im, le_abs_self H, abs_nonneg H]
      · exact (le_abs_self x.im).trans (hxH.trans (le_abs_self H))
    exact (P.image fun p => ‖p.1 - p.2‖).min'_le _ (Finset.mem_image.mpr ⟨(ρ, ρ'),
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem ρ hρ h1, hmem ρ' hρ' h2⟩, hne⟩, rfl⟩)
  · refine ⟨1, one_pos, fun ρ hρ ρ' hρ' hne h1 h2 _ _ => ?_⟩
    exfalso
    apply hPe
    have hmem : ∀ x ∈ zetaZeroConfig.carrier, |x.im| ≤ H → x ∈ hBfin.toFinset := fun x hx hxH => by
      rw [Set.Finite.mem_toFinset]
      refine ⟨hx, ?_, ?_⟩
      · linarith [neg_abs_le x.im, le_abs_self H, abs_nonneg H]
      · exact (le_abs_self x.im).trans (hxH.trans (le_abs_self H))
    exact ⟨(ρ, ρ'), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hmem ρ hρ h1, hmem ρ' hρ' h2⟩,
      hne⟩⟩

/-- **An attained top of `ζ` is visible at an explicit lag.** Let `½ + z₀` be a zero of largest real
part, `δ₀ = Re z₀ > 0`, at height `γ₀ = Im z₀ ≥ T_w`, let `Γ = recordHeightEnvelope w γ₀`, and let
`g > 0` separate the zeros with `|Im ρ| ≤ Γ + 1` and `Re ρ ≥ ½ + δ₀/4`. Then for every
`V ≥ max(V_w(z₀), (R_w(γ₀) + κ_w) max(1, 1/g, 4/δ₀))` some difference test of the bump modulated to
`γ₀` is Weil negative at a lag `v ∈ [0, V]`. -/
theorem zeta_attained_top_visible {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ ρ ∈ zetaZeroConfig.carrier, ∀ ρ' ∈ zetaZeroConfig.carrier, ρ ≠ ρ' →
      |ρ.im| ≤ recordHeightEnvelope w z₀.im + 1 → |ρ'.im| ≤ recordHeightEnvelope w z₀.im + 1 →
      1 / 2 + z₀.re / 4 ≤ ρ.re → 1 / 2 + z₀.re / 4 ≤ ρ'.re → g ≤ ‖ρ - ρ'‖)
    {V : ℝ} (hV : hidingLag w z₀ ≤ V)
    (hVg : (twinRadiusNumerator w z₀.im + uniformTwinDepth w) *
      max (max 1 (1 / g)) (4 / z₀.re) ≤ V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  set R := twinRadiusNumerator w z₀.im with hR
  set κ := uniformTwinDepth w with hκ
  set Γ := recordHeightEnvelope w z₀.im with hΓdef
  have hpos₀ : 0 < z₀.im := lt_of_lt_of_le (by unfold nearTopHeight; positivity) hTw
  obtain ⟨hΓ, hsmall⟩ := nearTopHeight_conditions hw hTw
  -- the depth offset and the radius are positive
  have hκ0 : 0 < κ := by
    rw [hκ, uniformTwinDepth]
    refine Real.log_pos ?_
    have : 0 ≤ Real.exp 1 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (xiLineTwoLogDerivConstant + 1)) / (60 * centerAmplitude w ^ 2) := by
      have := xiLineTwoLogDerivConstant_nonneg
      positivity
    linarith
  have hΓ1 : 2 * z₀.im ≤ Γ := le_max_left _ _
  have hℓ : 0 ≤ Real.log (Real.log (180 * (Γ + 6))) := by
    refine Real.log_nonneg ?_
    rw [Real.le_log_iff_exp_le (by nlinarith)]
    have : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    nlinarith
  have hR0 : 0 < R := by rw [hR, twinRadiusNumerator]; positivity
  have hmax1 : 1 ≤ max (max 1 (1 / g)) (4 / z₀.re) := (le_max_left _ _).trans (le_max_left _ _)
  have hV0 : 0 < V := lt_of_lt_of_le (by nlinarith) hVg
  have hRκV1 : (R + κ) / V ≤ 1 := by
    rw [div_le_one hV0]; exact le_trans (le_mul_of_one_le_right (by linarith) hmax1) hVg
  have hRκVg : (R + κ) / V ≤ g := by
    rw [div_le_iff₀ hV0]
    have h := le_trans (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _) :
      1 / g ≤ max (max 1 (1 / g)) (4 / z₀.re)) (by linarith : 0 ≤ R + κ)) hVg
    rw [mul_one_div, div_le_iff₀ hg] at h; linarith
  have hRκVd : (R + κ) / V ≤ z₀.re / 4 := by
    rw [div_le_iff₀ hV0]
    have h := le_trans (mul_le_mul_of_nonneg_left (le_max_right _ _ :
      4 / z₀.re ≤ max (max 1 (1 / g)) (4 / z₀.re)) (by linarith : 0 ≤ R + κ)) hVg
    rw [mul_div_assoc', div_le_iff₀ hre₀] at h; linarith
  -- the uniform twin radius applies
  have htop' : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 →
      z.re ≤ z₀.re + 1 / V := fun z hz => by
    have h1 : 0 < 1 / V := one_div_pos.mpr hV0
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have := htop _ h
      have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      linarith
    · have := htop _ h
      have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
      linarith
  have hV1 : R * max 1 (4 / z₀.re) ≤ V := (le_max_left _ _).trans hV
  have hV2 : 2 * Real.log (160 * Real.log (180 * Γ) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) ≤ z₀.re * V := by
    have := (le_max_right _ _).trans hV
    rw [div_le_iff₀ hre₀] at this; linarith
  obtain ⟨z₁, hz₁, hre₁, -, hup, -, -, z, hz, hDz, hdist⟩ :=
    zeta_uniform_twin_radius hw hV0 hz₀ hre₀ hpos₀ hΓ hsmall htop' hneg hV1 hV2
  -- the twin and the record are two zeros closer than `g`
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hs1 : ‖s - z₁‖ = κ / V := by
    have : s - z₁ = ((-(κ / V) : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hκ0 hV0)]
  have hdist' : ‖z - s‖ < R / V := by rw [hR, twinRadiusNumerator]; exact hdist
  have hzz : ‖z - z₁‖ < (R + κ) / V := by
    calc ‖z - z₁‖ ≤ ‖z - s‖ + ‖s - z₁‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < R / V + κ / V := by rw [hs1]; linarith
      _ = (R + κ) / V := by ring
  have hmem : ∀ x : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) x ≠ 0 →
      (1 / 2 + x) ∈ zetaZeroConfig.carrier := fun x hx => by
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact h
    · have := conj_mem_zetaZeroConfig h
      have e : conj (1 / 2 + conj x) = 1 / 2 + x := by apply Complex.ext <;> simp
      rwa [e] at this
  have him : |z.im| ≤ Γ + 1 := by
    have := (Complex.abs_im_le_norm (z - z₁))
    rw [Complex.sub_im] at this
    have := abs_sub_abs_le_abs_sub z.im z₁.im
    linarith
  have hrez : z₀.re / 4 ≤ z.re := by
    have := Complex.abs_re_le_norm (z - z₁)
    rw [Complex.sub_re] at this
    have := neg_abs_le (z.re - z₁.re)
    linarith
  have hsepz := hsep (1 / 2 + z) (hmem z hDz) (1 / 2 + z₁) (hmem z₁ hz₁)
    (fun h => hz (by simpa using h)) (by simpa using him) (by simpa using hup.trans (by linarith))
    (by simp; linarith) (by simp; linarith)
  rw [show (1 / 2 + z) - (1 / 2 + z₁) = z - z₁ by ring] at hsepz
  linarith

/-- **The first negative lag of an attained top.** For a zero `½ + z₀` of largest real part at height
`Im z₀ ≥ T_w` there is `g > 0`, the separation of the zeros near the top below height `Γ + 1`, such
that the family modulated to `Im z₀` has a Weil-negative difference test at some lag
`v ≤ max(V_w(z₀), (R_w + κ_w) max(1, 1/g, 4/Re z₀))`. -/
theorem zeta_attained_top_first_negative_lag {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeight w ≤ z₀.im)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re) :
    ∃ g > 0, ∃ v ∈ Icc (0 : ℝ) (max (hidingLag w z₀) ((twinRadiusNumerator w z₀.im +
        uniformTwinDepth w) * max (max 1 (1 / g)) (4 / z₀.re))),
      (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
        (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  obtain ⟨g, hg, hsep⟩ := exists_separation_in_box (recordHeightEnvelope w z₀.im + 1) (z₀.re / 4)
  exact ⟨g, hg, zeta_attained_top_visible hw hz₀ hre₀ hTw htop hg hsep (le_max_left _ _)
    (le_max_right _ _)⟩

end GaloisForLFunctions.SquareRootThreshold
