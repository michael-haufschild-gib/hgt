import GaloisForLFunctions.RHTower.WhittakerStreamFunction

/-!
# The Whittaker stream function at the corner `ρ = ½ + i√3/2`

Let `y₀ = √3/2` and `G(c) = Σ a_i (1 − c²) S_{k_i}(c)` be the arc flux of the stream function `ψ`
(`arcStreamFlux`).  Since `sin(k_i/2) = 0`:

* `G'(½) = Σ a_i k_i cos(k_i/2) (y₀ K₁(k_i y₀) − (k_i/2) K₀(k_i y₀))`
  (`hasDerivAt_arcStreamFlux_half`).  Each mode is
  `k c Φ(y(c)) cos(kc) − k(1 − c²) K₀(k y(c)) sin(kc)` near `c = ½`, with `Φ(s) = s K₁(ks)`,
  `Φ' = −k s K₀(ks)` and `y(c) = √(1 − c²)`.
* `ψ_x(ρ) = 2 G(½)` (`whStreamX_half_eq`) and `∂_y ψ_x(ρ) = 2 y₀ (G'(½) − 2 G(½))`
  (`whStreamXY_half_eq`), both from `y₀² = ¾`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

theorem modularArcHeight_half_sq : modularArcHeight (1 / 2) ^ 2 = 3 / 4 := by
  rw [modularArcHeight_sq_of_abs_lt (by rw [abs_of_pos (by norm_num)]; norm_num)]
  norm_num

theorem modularArcHeight_half_pos : 0 < modularArcHeight (1 / 2) :=
  modularArcHeight_pos_of_abs_lt (by rw [abs_of_pos (by norm_num)]; norm_num)

theorem hasDerivAt_modularArcHeight {c : ℝ} (hc : |c| < 1) :
    HasDerivAt modularArcHeight (-(2 * c) / (2 * modularArcHeight c)) c := by
  have h1 : HasDerivAt (fun c : ℝ => 1 - c ^ 2) (-(2 * c)) c := by
    simpa using ((hasDerivAt_pow 2 c).const_sub 1)
  have hne : (1 : ℝ) - c ^ 2 ≠ 0 := by have := abs_lt.mp hc; nlinarith
  exact h1.sqrt hne

/-- One mode of `G'(½)`. -/
theorem hasDerivAt_modeFlux_half {k : ℝ} (hk : 0 < k) (hs : Real.sin (k * (1 / 2)) = 0) :
    HasDerivAt (fun c => (1 - c ^ 2) * arcWhittakerSlope k c)
      (k * Real.cos (k * (1 / 2)) * (modularArcHeight (1 / 2) *
        kMoment 1 (k * modularArcHeight (1 / 2)) -
        k / 2 * kMoment 0 (k * modularArcHeight (1 / 2)))) (1 / 2) := by
  set y₀ := modularArcHeight (1 / 2) with hy₀
  have hy0 : 0 < y₀ := modularArcHeight_half_pos
  have hy02 : y₀ ^ 2 = 3 / 4 := modularArcHeight_half_sq
  have hhalf : |(1 / 2 : ℝ)| < 1 := by rw [abs_of_pos (by norm_num)]; norm_num
  -- the smooth form near `½`
  set g : ℝ → ℝ := fun c => k * c * (modularArcHeight c * kMoment 1 (k * modularArcHeight c)) *
      Real.cos (k * c) - k * (1 - c ^ 2) * kMoment 0 (k * modularArcHeight c) * Real.sin (k * c)
    with hg
  have heq : (fun c => (1 - c ^ 2) * arcWhittakerSlope k c) =ᶠ[𝓝 (1 / 2)] g := by
    have hopen : ∀ᶠ c in 𝓝 (1 / 2 : ℝ), |c| < 1 :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds hhalf
    filter_upwards [hopen] with c hc
    have hyc := modularArcHeight_pos_of_abs_lt hc
    have hyc2 := modularArcHeight_sq_of_abs_lt hc
    simp only [hg, arcWhittakerSlope]
    rw [← hyc2]
    field_simp
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have hY := hasDerivAt_modularArcHeight hhalf
  rw [← hy₀] at hY
  have hΦ := (hasDerivAt_mul_kMoment_one hk hy0).comp (1 / 2 : ℝ) hY
  have hB := (hasDerivAt_kMoment_comp_mul 0 hk hy0).comp (1 / 2 : ℝ) hY
  have hcos : HasDerivAt (fun c : ℝ => Real.cos (k * c)) (-Real.sin (k * (1 / 2)) * k) (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℝ)).const_mul k).cos
  have hsin : HasDerivAt (fun c : ℝ => Real.sin (k * c)) (Real.cos (k * (1 / 2)) * k) (1 / 2) := by
    simpa using ((hasDerivAt_id (1 / 2 : ℝ)).const_mul k).sin
  have hlin : HasDerivAt (fun c : ℝ => k * c) k (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_mul k
  have hpoly : HasDerivAt (fun c : ℝ => k * (1 - c ^ 2)) (k * (-(2 * (1 / 2)))) (1 / 2) := by
    simpa using ((hasDerivAt_pow 2 (1 / 2 : ℝ)).const_sub 1).const_mul k
  have h := ((hlin.mul hΦ).mul hcos).sub ((hpoly.mul hB).mul hsin)
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Function.comp_apply, hs, ← hy₀, zero_add]
  field_simp
  ring

variable {N : ℕ}

/-- `G'(½)` for the whole sum. -/
def arcStreamFluxSlope (a : Fin N → ℝ) : ℝ :=
  ∑ i, a i * (streamFreq i * Real.cos (streamFreq i * (1 / 2)) *
    (modularArcHeight (1 / 2) * kMoment 1 (streamFreq i * modularArcHeight (1 / 2)) -
      streamFreq i / 2 * kMoment 0 (streamFreq i * modularArcHeight (1 / 2))))

theorem hasDerivAt_arcStreamFlux_half (a : Fin N → ℝ) :
    HasDerivAt (arcStreamFlux a) (arcStreamFluxSlope a) (1 / 2) := by
  unfold arcStreamFlux arcStreamFluxSlope
  exact HasDerivAt.fun_sum fun i _ =>
    (hasDerivAt_modeFlux_half (streamFreq_pos i) (sin_streamFreq_half i)).const_mul (a i)

/-- `ψ_x(ρ) = 2 G(½)`. -/
theorem whStreamX_half_eq (a : Fin N → ℝ) :
    whStreamX a (1 / 2) (modularArcHeight (1 / 2)) = 2 * arcStreamFlux a (1 / 2) := by
  have hy0 := modularArcHeight_half_pos
  have hy02 := modularArcHeight_half_sq
  unfold whStreamX arcStreamFlux modeStreamX arcWhittakerSlope
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sin_streamFreq_half, show streamFreq i * (1 / 2) = streamFreq i * (1 / 2) from rfl]
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num]
  field_simp
  rw [show (modularArcHeight (1 / 2)) ^ 2 = 3 / 4 from hy02]
  ring

/-- `∂_y ψ_x(ρ) = 2 y₀ (G'(½) − 2 G(½))`. -/
theorem whStreamXY_half_eq (a : Fin N → ℝ) :
    whStreamXY a (1 / 2) (modularArcHeight (1 / 2)) =
      2 * modularArcHeight (1 / 2) * (arcStreamFluxSlope a - 2 * arcStreamFlux a (1 / 2)) := by
  have hy0 := modularArcHeight_half_pos
  have hy02 := modularArcHeight_half_sq
  unfold whStreamXY arcStreamFluxSlope arcStreamFlux modeStreamXY arcWhittakerSlope
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sin_streamFreq_half]
  rw [show (1 : ℝ) - (1 / 2) ^ 2 = 3 / 4 by norm_num]
  field_simp
  linear_combination (-8 * a i * streamFreq i * Real.cos (streamFreq i / 2) *
    kMoment 1 (streamFreq i * modularArcHeight (1 / 2))) * hy02

end

end RHTower
