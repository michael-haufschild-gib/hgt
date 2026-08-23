import GaloisForLFunctions.RHTower.SoninMellinMultiplier

/-!
# Burnol's Theorem 4.9: `𝓛¹` is dense in `L¹`

Every even vector of the extended Sonine space `L_1` is an `L²`-limit of vectors of `L_1` whose
continued Mellin transform decreases faster than every power of the height on every vertical strip.

The proof is Burnol's.  By Proposition 4.6 the union of the smaller spaces `L_b`, `b > 1`, is dense
in `L_1`; the even projection keeps a vector inside `L_b` and does not increase the distance to an
even vector.  Smoothing a vector of `L_b` by a bump `k` supported in `[-log b, log b]` on the
logarithmic scale keeps it inside `L_1` (a dilation by `e^x` moves the aperture to
`min(b e^{-x}, b e^{x}) ≥ 1`), multiplies its Mellin transform by the entire, rapidly decreasing
multiplier `∫k(x)e^{(s-1/2)x}dx`, and moves the vector by at most the modulus of strong continuity
of the dilation group — which is as small as we please.

## Main results

* `exists_hasRapidMellin_approx`
* `mem_closure_hasRapidMellin` — **Burnol's Theorem 4.9**
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

/-- A vector of a directed union of extended Sonine spaces lies in one of them. -/
theorem exists_mem_of_mem_iSup_extended {a : ℝ} {f : SoninL2}
    (hf : f ∈ ⨆ b : {b : ℝ // a < b}, centralSoninExtendedCarrier b.1) :
    ∃ b : ℝ, a < b ∧ f ∈ centralSoninExtendedCarrier b := by
  haveI : Nonempty {b : ℝ // a < b} := ⟨⟨a + 1, by linarith⟩⟩
  have hdir : Directed (· ≤ ·) (fun b : {b : ℝ // a < b} => centralSoninExtendedCarrier b.1) := by
    intro i j
    refine ⟨⟨min i.1 j.1, lt_min i.2 j.2⟩, ?_, ?_⟩
    · exact centralSoninExtendedCarrier_antitone (min_le_left _ _)
    · exact centralSoninExtendedCarrier_antitone (min_le_right _ _)
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ hdir).1 hf
  exact ⟨i.1, i.2, hi⟩

theorem norm_evenProjection_le (x : SoninL2) : ‖evenProjection x‖ ≤ ‖x‖ := by
  have hrefl : ‖l2Reflection x‖ = ‖x‖ := l2ReflectionIsometry.norm_map x
  rw [evenProjection_apply, norm_smul]
  have h2 : ‖((2 : ℂ))⁻¹‖ = 1 / 2 := by
    rw [norm_inv]
    norm_num
  rw [h2]
  have hadd : ‖x + l2Reflection x‖ ≤ ‖x‖ + ‖x‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [hrefl]
  linarith

theorem evenProjection_fixes {x : SoninL2} (hx : x ∈ evenSubspace) : evenProjection x = x := by
  rw [evenProjection_apply, (mem_evenSubspace_iff x).1 hx]
  rw [show x + x = (2 : ℂ) • x by module, smul_smul]
  norm_num

/-- **Burnol's Theorem 4.9, quantitative form.**  Every even vector of `L_1` is approximated in
`L²` by vectors of `𝓛¹`. -/
theorem exists_hasRapidMellin_approx {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : f ∈ centralSoninExtendedCarrier 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SoninL2, g ∈ evenSubspace ∧ g ∈ centralSoninExtendedCarrier 1 ∧
      HasRapidMellin 1 g ∧ ‖f - g‖ < ε := by
  classical
  -- Step 1: Proposition 4.6 gives a nearby vector of some `L_b`, `b > 1`
  have hclos := topologicalClosure_iSup_centralSoninExtendedCarrier 1 one_pos
  have hfmem : f ∈ closure
      ((⨆ b : {b : ℝ // (1 : ℝ) < b}, centralSoninExtendedCarrier b.1 : Submodule ℂ SoninL2)
        : Set SoninL2) := by
    have : f ∈ (⨆ b : {b : ℝ // (1 : ℝ) < b},
        centralSoninExtendedCarrier b.1).topologicalClosure := by
      rw [hclos]; exact hf
    exact this
  obtain ⟨f₁, hf₁mem, hf₁dist⟩ := Metric.mem_closure_iff.1 hfmem (ε / 2) (by linarith)
  obtain ⟨b, hb1, hbmem⟩ := exists_mem_of_mem_iSup_extended hf₁mem
  have hb0 : (0 : ℝ) < b := by linarith
  -- Step 2: symmetrise
  set f₂ : SoninL2 := evenProjection f₁ with hf₂def
  have hf₂ev : f₂ ∈ evenSubspace := evenProjection_mem_evenSubspace f₁
  have hf₂mem : f₂ ∈ centralSoninExtendedCarrier b :=
    evenProjection_mem_centralSoninExtendedCarrier hbmem
  have hf₂dist : ‖f - f₂‖ < ε / 2 := by
    have hsub : f - f₂ = evenProjection (f - f₁) := by
      rw [map_sub, evenProjection_fixes hev, hf₂def]
    rw [hsub]
    refine lt_of_le_of_lt (norm_evenProjection_le _) ?_
    rw [← dist_eq_norm]
    exact hf₁dist
  -- Step 3: the modulus of strong continuity of the dilation group at `f₂`
  have hcont : Tendsto (fun x : ℝ => ‖rayDilate (Real.exp x) f₂ - f₂‖) (𝓝 0) (𝓝 0) := by
    have h1 := tendsto_norm_rayDilate_sub_self f₂
    have h2 : Tendsto (fun x : ℝ => Real.exp x) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      simpa using (Real.continuous_exp.tendsto (0 : ℝ))
    exact h1.comp h2
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 4) (by linarith)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set δ : ℝ := min (δ₀ / 2) (Real.log b) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (by linarith) hlogb
  have hδlog : δ ≤ Real.log b := by rw [hδdef]; exact min_le_right _ _
  have hexpδ : Real.exp δ ≤ b := by
    have := Real.exp_le_exp.2 hδlog
    rwa [Real.exp_log hb0] at this
  have hmodulus : ∀ x : ℝ, |x| ≤ δ → ‖rayDilate (Real.exp x) f₂ - f₂‖ ≤ ε / 4 := by
    intro x hx
    have hxd : dist x 0 < δ₀ := by
      rw [Real.dist_eq, sub_zero]
      have : δ ≤ δ₀ / 2 := by rw [hδdef]; exact min_le_left _ _
      linarith
    have := hδ₀ hxd
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    linarith
  -- Step 4: the smoothing weight
  set φ : ContDiffBump (0 : ℝ) := ⟨δ / 2, δ, by positivity, by linarith⟩ with hφdef
  set k : ℝ → ℝ := φ.normed (volume : Measure ℝ) with hkdef
  have hkC : ContDiff ℝ (⊤ : ℕ∞) k := φ.contDiff_normed
  have hkcont : Continuous k := hkC.continuous
  have hksupp : ∀ x : ℝ, δ ≤ |x| → k x = 0 := by
    intro x hx
    have hsupp := φ.support_normed_eq (μ := (volume : Measure ℝ))
    have hnot : x ∉ Function.support k := by
      rw [hkdef, hsupp]
      simp only [Metric.mem_ball, Real.dist_eq, sub_zero, not_lt]
      exact hx
    exact Function.notMem_support.1 hnot
  have hks : HasCompactSupport k := hasCompactSupport_of_vanishing hksupp
  have hkint : (∫ x : ℝ, k x) = 1 := φ.integral_normed
  have hkabs : (∫ x : ℝ, |k x|) = 1 := by
    rw [← hkint]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    exact abs_of_nonneg (φ.nonneg_normed x)
  -- Step 5: the smoothed vector
  refine ⟨dilationAverage k f₂, dilationAverage_mem_evenSubspace hkcont hks hf₂ev,
    dilationAverage_mem_extended hkcont hks
      (rayDilate_mem_extended_one hexpδ hksupp hf₂mem),
    hasRapidMellin_dilationAverage hkC hδpos hksupp hexpδ hf₂ev hf₂mem, ?_⟩
  have hmove := norm_dilationAverage_sub_smul_le hkcont hks f₂ hδpos hksupp hmodulus
  rw [hkint, hkabs, Complex.ofReal_one, one_smul, one_mul] at hmove
  calc ‖f - dilationAverage k f₂‖
      = ‖(f - f₂) + (f₂ - dilationAverage k f₂)‖ := by congr 1; abel
    _ ≤ ‖f - f₂‖ + ‖f₂ - dilationAverage k f₂‖ := norm_add_le _ _
    _ = ‖f - f₂‖ + ‖dilationAverage k f₂ - f₂‖ := by rw [norm_sub_rev f₂]
    _ < ε := by linarith

/-- **Burnol's Theorem 4.9.**  `𝓛¹` is dense in `L¹`. -/
theorem mem_closure_hasRapidMellin {f : SoninL2} (hev : f ∈ evenSubspace)
    (hf : f ∈ centralSoninExtendedCarrier 1) :
    f ∈ closure {g : SoninL2 | g ∈ evenSubspace ∧ g ∈ centralSoninExtendedCarrier 1 ∧
      HasRapidMellin 1 g} := by
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨g, hgev, hgmem, hgrapid, hgdist⟩ := exists_hasRapidMellin_approx hev hf hε
  exact ⟨g, ⟨hgev, hgmem, hgrapid⟩, by rw [dist_eq_norm]; exact hgdist⟩

end RHTower

end
