import GaloisForLFunctions.HTGeometry.TraceDimensionEigenvalueFloor

/-!
# A power tail forces moment divergence

If an onset time has tail `μ{τ > L} ≥ A L^{-q}` for every large `L`, then Chebyshev's inequality at
level `L^p` gives `∫ τ^p ≥ A L^{p-q}`.  The right-hand side is unbounded in `L` as soon as `p > q`,
and a single quantity dominating an unbounded family is infinite, so every moment of order above the
tail exponent diverges.

No limit theorem is needed beyond the divergence of `L ↦ L^{p-q}`: the estimate holds at each `L`
separately.
-/

open MeasureTheory Filter

namespace GaloisForLFunctions.HTGeometry

section MomentDivergence

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The moment floor.**  A tail bound at level `L` lower-bounds the `p`-th moment by `A L^{p-q}`.
-/
theorem moment_floor {τ : Ω → ℝ} {A q p L : ℝ}
    (hm : AEMeasurable (fun ω => ENNReal.ofReal (τ ω ^ p)) μ)
    (hp : 0 < p) (hL : 0 < L)
    (htail : ENNReal.ofReal (A * L ^ (-q)) ≤ μ {ω | L < τ ω}) :
    ENNReal.ofReal (A * L ^ (p - q)) ≤ ∫⁻ ω, ENNReal.ofReal (τ ω ^ p) ∂μ := by
  have hsub : {ω | L < τ ω} ⊆ {ω | ENNReal.ofReal (L ^ p) ≤ ENNReal.ofReal (τ ω ^ p)} := by
    intro ω hω
    refine ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow (le_of_lt hL) (le_of_lt hω) (le_of_lt hp)
  have hcheb := mul_meas_ge_le_lintegral₀ hm (ENNReal.ofReal (L ^ p))
  have hmono : ENNReal.ofReal (L ^ p) * μ {ω | L < τ ω}
      ≤ ENNReal.ofReal (L ^ p) * μ {ω | ENNReal.ofReal (L ^ p) ≤ ENNReal.ofReal (τ ω ^ p)} :=
    mul_le_mul_right (measure_mono hsub) _
  have hprod : ENNReal.ofReal (L ^ p) * ENNReal.ofReal (A * L ^ (-q))
      = ENNReal.ofReal (A * L ^ (p - q)) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ L ^ p)]
    congr 1
    rw [show A * L ^ (p - q) = A * (L ^ p * L ^ (-q)) from by
      rw [← Real.rpow_add hL]
      ring_nf]
    ring
  calc ENNReal.ofReal (A * L ^ (p - q))
      = ENNReal.ofReal (L ^ p) * ENNReal.ofReal (A * L ^ (-q)) := hprod.symm
    _ ≤ ENNReal.ofReal (L ^ p) * μ {ω | L < τ ω} := mul_le_mul_right htail _
    _ ≤ ENNReal.ofReal (L ^ p)
          * μ {ω | ENNReal.ofReal (L ^ p) ≤ ENNReal.ofReal (τ ω ^ p)} := hmono
    _ ≤ ∫⁻ ω, ENNReal.ofReal (τ ω ^ p) ∂μ := hcheb

/-- **An unbounded family of real lower bounds forces an infinite integral.** -/
theorem lintegral_eq_top_of_unbounded_real {f : Ω → ENNReal} {g : ℝ → ℝ}
    (hb : ∀ L : ℝ, ENNReal.ofReal (g L) ≤ ∫⁻ ω, f ω ∂μ)
    (hg : Tendsto g atTop atTop) :
    ∫⁻ ω, f ω ∂μ = ⊤ := by
  by_contra hne
  set c : ℝ := (∫⁻ ω, f ω ∂μ).toReal with hc
  obtain ⟨L, hL⟩ := (hg.eventually_gt_atTop (c + 1)).exists
  have hle := hb L
  have hlt : ENNReal.ofReal (g L) ≤ ENNReal.ofReal c := by
    refine le_trans hle (le_of_eq ?_)
    rw [hc, ENNReal.ofReal_toReal hne]
  have hgc : g L ≤ c := by
    have hcnn : 0 ≤ c := ENNReal.toReal_nonneg
    exact (ENNReal.ofReal_le_ofReal_iff hcnn).mp hlt
  linarith

/-! ## The boundary exponent -/

open Set

/-- The reciprocal is not integrable at infinity. -/
theorem lintegral_Ioi_rpow_neg_one_eq_top {L : ℝ} (hL : 0 < L) :
    ∫⁻ t in Set.Ioi L, ENNReal.ofReal (t ^ (-1 : ℝ)) = ⊤ := by
  have hni : ¬ IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioi L) volume := by
    rw [integrableOn_Ioi_rpow_iff hL]
    norm_num
  by_contra hne
  refine hni ⟨(Measurable.aestronglyMeasurable (by fun_prop)).restrict, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal]
  · exact lt_top_iff_ne_top.mpr hne
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hL ht)) _

/-- **The boundary case of `(18)`.**  A tail `A L^{-9}` makes the ninth moment infinite, not merely
bounded below: the layer-cake integrand is `A t^{-1}`, which diverges. -/
theorem lintegral_rpow_eq_top_of_boundary_tail {τ : Ω → ℝ} {A L₀ : ℝ} (hA : 0 < A) (hL₀ : 0 < L₀)
    (hτ0 : 0 ≤ᵐ[μ] τ) (hτm : AEMeasurable τ μ)
    (htail : ∀ t : ℝ, L₀ < t → ENNReal.ofReal (A * t ^ (-9 : ℝ)) ≤ μ {ω | t < τ ω}) :
    ∫⁻ ω, ENNReal.ofReal (τ ω ^ (9 : ℝ)) ∂μ = ⊤ := by
  rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hτ0 hτm (by norm_num : (0 : ℝ) < 9)]
  have hinner : ∫⁻ t in Ioi (0 : ℝ),
      μ {ω | t < τ ω} * ENNReal.ofReal (t ^ ((9 : ℝ) - 1)) = ⊤ := by
    refine eq_top_iff.mpr ?_
    have hsub : Ioi L₀ ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi (le_of_lt hL₀)
    refine le_trans ?_ (lintegral_mono_set hsub)
    have hpt : ∀ t ∈ Ioi L₀,
        ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ))
          ≤ μ {ω | t < τ ω} * ENNReal.ofReal (t ^ ((9 : ℝ) - 1)) := by
      intro t ht
      have htpos : 0 < t := lt_trans hL₀ ht
      have hfac : ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ))
          = ENNReal.ofReal (A * t ^ (-9 : ℝ)) * ENNReal.ofReal (t ^ ((9 : ℝ) - 1)) := by
        rw [← ENNReal.ofReal_mul (le_of_lt hA), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [mul_assoc, ← Real.rpow_add htpos]
        norm_num
      rw [hfac]
      gcongr
      exact htail t ht
    calc (⊤ : ENNReal)
        = ENNReal.ofReal A * ∫⁻ t in Ioi L₀, ENNReal.ofReal (t ^ (-1 : ℝ)) := by
          rw [lintegral_Ioi_rpow_neg_one_eq_top hL₀,
            ENNReal.mul_top (by simp [ENNReal.ofReal_eq_zero, not_le, hA])]
      _ = ∫⁻ t in Ioi L₀, ENNReal.ofReal A * ENNReal.ofReal (t ^ (-1 : ℝ)) :=
          (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ ≤ ∫⁻ t in Ioi L₀, μ {ω | t < τ ω} * ENNReal.ofReal (t ^ ((9 : ℝ) - 1)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          exact hpt t ht
  rw [hinner, ENNReal.mul_top (by simp)]


end MomentDivergence

end GaloisForLFunctions.HTGeometry
