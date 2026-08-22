import GaloisForLFunctions.RHTower.ConnesCutoffTraceDecomposition
import GaloisForLFunctions.RHTower.ConnesBesovCutoffDecay
import GaloisForLFunctions.RHTower.ConnesFracConvDecay
import GaloisForLFunctions.RHTower.ConnesLocalTraceCore

/-!
# §VII (33): the error term is `O(Λ^{-N})` for every `N`

§VII (33) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `∑_q ∫ ĝ_q(u) (log|u| − 2 log' Λ)^+ du = O(Λ^{-N})`   for every `N`.               (33)

`ConnesLocalTraceCore.connes_traceCore_tendsto` already shows the remainder of the cut-off trace
*vanishes*, but only at the rate `O(Λ^{-2} log Λ)` that its tail bounds give.  Connes' (33)
demands decay faster than *every* power, which is what Lemma 2 of §VII supplies.  This module
proves that rate at the archimedean place, unconditionally, for every Schwartz `ĝ`:

* `connes_schwartz_polyDecay` - a Schwartz function is `O((1+|x|)^{-k})` for every `k`;
* `connes_schwartz_excess_mass_le` - the explicit bound
  `‖∫ ĝ(u) ε_{log T}(u) du‖ ≤ C · 2 T^{-(k-1)}/(k-1)²`, from
  `ConnesBesovCutoffDecay.connes_excessMajorant_mass_le`;
* `connes_schwartz_error_rapidDecay` - **(33)**, taking `k = N + 3` and `T = Λ²`;
* `connes_cutoffTrace_remainder_rapidDecay` - the same rate for the whole remainder of (30),
  strictly strengthening `connes_traceCore_tendsto`.
-/

open MeasureTheory Real Set Filter Topology
open scoped SchwartzMap Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **The polynomial decay of a Schwartz function.**  Every Schwartz function is `O((1+|x|)^{-k})`
for every `k`. -/
theorem connes_schwartz_polyDecay (G : 𝓢(ℝ, ℂ)) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, ‖G z‖ ≤ C * (1 + |z|) ^ (-(k : ℝ)) := by
  set σ₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 G with hσ₀
  set σₖ : ℝ := SchwartzMap.seminorm ℂ k 0 G with hσₖ
  have hσ₀0 : (0 : ℝ) ≤ σ₀ := apply_nonneg _ G
  have hσₖ0 : (0 : ℝ) ≤ σₖ := apply_nonneg _ G
  refine ⟨2 ^ k * (σ₀ + σₖ), by positivity, fun z => ?_⟩
  have h0 := SchwartzMap.norm_pow_mul_le_seminorm ℂ G 0 z
  have hk := SchwartzMap.norm_pow_mul_le_seminorm ℂ G k z
  rw [Real.norm_eq_abs] at h0 hk
  simp only [pow_zero, one_mul] at h0
  have hpos : (0 : ℝ) < (1 + |z|) ^ k := by positivity
  have hexp : (1 + |z|) ^ (-(k : ℝ)) = ((1 + |z|) ^ k)⁻¹ := by
    rw [← Real.rpow_natCast (1 + |z|) k, ← Real.rpow_neg (by positivity)]
  rw [hexp, le_mul_inv_iff₀ hpos]
  have hgnn : (0 : ℝ) ≤ ‖G z‖ := norm_nonneg _
  have hbase := connes_one_add_abs_pow_le k z
  calc ‖G z‖ * (1 + |z|) ^ k
      ≤ ‖G z‖ * (2 ^ k * (1 + |z| ^ k)) := mul_le_mul_of_nonneg_left hbase hgnn
    _ = 2 ^ k * (‖G z‖ + |z| ^ k * ‖G z‖) := by ring
    _ ≤ 2 ^ k * (σ₀ + σₖ) := by
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **§VII (33), the explicit error bound at the archimedean place.** -/
theorem connes_schwartz_excess_mass_le (G : 𝓢(ℝ, ℂ)) {k : ℕ} (hk : 3 ≤ k) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z : ℝ, ‖G z‖ ≤ C * (1 + |z|) ^ (-(k : ℝ))) {T : ℝ} (hT : 1 < T) :
    ‖∫ u : ℝ, G u * ((connesCutoffExcess (Real.log T) u : ℝ) : ℂ)‖
      ≤ C * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)) := by
  have hLnn : (0 : ℝ) ≤ Real.log T := Real.log_nonneg hT.le
  have hMint : Integrable
      (fun x : ℝ => connesCutoffExcess (Real.log T) x * (1 + |x|) ^ (-(k : ℝ))) volume :=
    connesExcessMajorant_integrable hLnn hk
  have hstep1 : ‖∫ u : ℝ, G u * ((connesCutoffExcess (Real.log T) u : ℝ) : ℂ)‖
      ≤ ∫ u : ℝ, ‖G u * ((connesCutoffExcess (Real.log T) u : ℝ) : ℂ)‖ :=
    norm_integral_le_integral_norm _
  have hstep2 : (∫ u : ℝ, ‖G u * ((connesCutoffExcess (Real.log T) u : ℝ) : ℂ)‖)
      ≤ ∫ u : ℝ, C * (connesCutoffExcess (Real.log T) u * (1 + |u|) ^ (-(k : ℝ))) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => norm_nonneg _) (hMint.const_mul C)
      (Filter.Eventually.of_forall fun u => ?_)
    show ‖G u * ((connesCutoffExcess (Real.log T) u : ℝ) : ℂ)‖
      ≤ C * (connesCutoffExcess (Real.log T) u * (1 + |u|) ^ (-(k : ℝ)))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (connesCutoffExcess_nonneg _ _)]
    have h := mul_le_mul_of_nonneg_right (hC u) (connesCutoffExcess_nonneg (Real.log T) u)
    calc ‖G u‖ * connesCutoffExcess (Real.log T) u
        ≤ C * (1 + |u|) ^ (-(k : ℝ)) * connesCutoffExcess (Real.log T) u := h
      _ = C * (connesCutoffExcess (Real.log T) u * (1 + |u|) ^ (-(k : ℝ))) := by ring
  have hstep3 : (∫ u : ℝ, C * (connesCutoffExcess (Real.log T) u * (1 + |u|) ^ (-(k : ℝ))))
      ≤ C * (2 * (T ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (connes_excessMajorant_mass_le hk hT) hC0
  linarith

/-- **§VII (33).**  The error term of the cut-off trace is `O(Λ^{-N})` for every `N`. -/
theorem connes_schwartz_error_rapidDecay (G : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Tendsto (fun Λ : ℝ => Λ ^ N *
        ‖∫ u : ℝ, G u * ((connesCutoffExcess (2 * Real.log Λ) u : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  set k : ℕ := N + 3 with hkdef
  have hk3 : 3 ≤ k := by omega
  obtain ⟨C, hC0, hC⟩ := connes_schwartz_polyDecay G k
  have hkR : ((k : ℕ) : ℝ) - 1 = (N : ℝ) + 2 := by
    rw [hkdef]
    push_cast
    ring
  set D : ℝ := C * (2 / ((k : ℝ) - 1) ^ 2) with hD
  have hD0 : (0 : ℝ) ≤ D := by
    rw [hD]
    positivity
  have hlim : Tendsto (fun Λ : ℝ => D * Λ ^ (-((N : ℝ) + 4))) atTop (𝓝 0) := by
    have hpos : (0 : ℝ) < (N : ℝ) + 4 := by positivity
    simpa using (tendsto_rpow_neg_atTop hpos).const_mul D
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Λ hΛ
    exact mul_nonneg (pow_nonneg hΛ N) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with Λ hΛ
    have hΛ0 : (0 : ℝ) < Λ := lt_of_lt_of_le (by norm_num) hΛ
    have hT : (1 : ℝ) < Λ ^ 2 := by nlinarith
    have hlogsq : Real.log (Λ ^ 2) = 2 * Real.log Λ := by
      rw [Real.log_pow]
      push_cast
      ring
    have h := connes_schwartz_excess_mass_le G hk3 hC0 hC hT
    rw [hlogsq] at h
    have hstep : Λ ^ N * ‖∫ u : ℝ, G u * ((connesCutoffExcess (2 * Real.log Λ) u : ℝ) : ℂ)‖
        ≤ Λ ^ N * (C * (2 * ((Λ ^ 2) ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2))) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    refine le_trans hstep (le_of_eq ?_)
    have hA : ((Λ ^ 2 : ℝ)) ^ (-((k : ℝ) - 1)) = Λ ^ (-(2 * ((N : ℝ) + 2))) := by
      rw [hkR, ← Real.rpow_natCast Λ 2, ← Real.rpow_mul hΛ0.le]
      congr 1
      push_cast
      ring
    have hprod : (Λ : ℝ) ^ N * Λ ^ (-(2 * ((N : ℝ) + 2))) = Λ ^ (-((N : ℝ) + 4)) := by
      rw [← Real.rpow_natCast Λ N, ← Real.rpow_add hΛ0]
      congr 1
      ring
    calc Λ ^ N * (C * (2 * ((Λ ^ 2) ^ (-((k : ℝ) - 1)) / ((k : ℝ) - 1) ^ 2)))
        = (C * (2 / ((k : ℝ) - 1) ^ 2)) * (Λ ^ N * (Λ ^ 2) ^ (-((k : ℝ) - 1))) := by ring
      _ = D * Λ ^ (-((N : ℝ) + 4)) := by rw [hD, hA, hprod]

/-- **§VII (30)-(33).**  The whole remainder of the cut-off trace decays faster than every power
of the cut-off - strictly stronger than `connes_traceCore_tendsto`, whose tail bounds only give
`O(Λ^{-2} log Λ)`. -/
theorem connes_cutoffTrace_remainder_rapidDecay (G : 𝓢(ℝ, ℂ)) (N : ℕ) :
    Tendsto (fun Λ : ℝ => Λ ^ N *
        ‖(∫ u in {u : ℝ | |u| ≤ Λ ^ 2}, G u * (((2 * Real.log Λ - Real.log |u| : ℝ)) : ℂ))
          - (((2 * Real.log Λ : ℝ) : ℂ) * (∫ u : ℝ, G u)
              - ∫ u : ℝ, G u * ((Real.log |u| : ℝ) : ℂ))‖) atTop (𝓝 0) := by
  refine (connes_schwartz_error_rapidDecay G N).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Λ hΛ
  have hexp := connes_cutoffTrace_expansion ((G : 𝓢(ℝ, ℂ)) : ℝ → ℂ) hΛ G.integrable
    (connes_schwartz_integrable_log G)
  rw [hexp]
  congr 2
  ring

end

end GaloisForLFunctions.RHTower
