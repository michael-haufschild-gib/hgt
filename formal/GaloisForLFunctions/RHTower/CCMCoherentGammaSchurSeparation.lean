import GaloisForLFunctions.RHTower.CCMCoherentGammaModulationRecurrence
import GaloisForLFunctions.RHTower.CCMCoherentGammaPoleFloor
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurConstrainedEscape

/-!
# Supported coherent cost cannot be paid by prime-edge energy alone

The same genuine, exactly pole-constrained sources have vanishing actual-prime
edge energy and a strictly positive limiting supported coherent cost. The
complete prime-plus-terminal field is kept before every norm and limit.
This excludes a scalar cost-by-edge absorption; it does not exclude a joint
estimate retaining the unbounded archimedean energy and signed current.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology
noncomputable section
namespace RHTower

private theorem constrained_lift (a : SuzukiPositiveAperture)
    (f : ℕ → suzukiApertureHilbert a)
    (hweak : ∀ g, Tendsto (fun n => inner ℂ g (f n)) atTop (𝓝 0)) :
    ∃ u : ℕ → CCMArchimedeanFormDomain a,
      (∀ n, IsPolarConstrained a (u n)) ∧
      Tendsto (fun n => ccmArchimedeanFormToAperture a (u n)-f n) atTop (𝓝 0) := by
  classical
  let J := ccmArchimedeanFormToAperture a
  have hd (n : ℕ) : ∃ v : CCMArchimedeanFormDomain a,
      ‖J v-f n‖ < 1 / (n+1 : ℝ) := by
    obtain ⟨v,hv⟩ := (Metric.denseRange_iff.mp (denseRange_ccmArchimedeanFormToAperture a))
      (f n) (1/(n+1 : ℝ)) (by positivity)
    exact ⟨v, by simpa only [dist_eq_norm, norm_sub_rev] using hv⟩
  choose v hv using hd
  have herrnorm : Tendsto (fun n => ‖J (v n)-f n‖) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => 1/(n+1 : ℝ)) atTop (𝓝 0) := by
      have hi : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
      simpa only [Nat.cast_add, Nat.cast_one, one_div] using hi
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (hv n).le) ht
  have herr : Tendsto (fun n => J (v n)-f n) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr herrnorm
  have hvweak (g : suzukiApertureHilbert a) :
      Tendsto (fun n => inner ℂ g (J (v n))) atTop (𝓝 0) := by
    have h := ((innerSL ℂ g).continuous.tendsto 0).comp herr
    simp only [map_zero] at h
    change Tendsto (fun n => inner ℂ g (J (v n)-f n)) atTop (𝓝 0) at h
    simpa only [zero_add, inner_sub_right, sub_add_cancel] using h.add (hweak g)
  let u : ℕ → CCMArchimedeanFormDomain a := fun n => ccmPolarCoordinateCorrection a (v n)
  let bp := J (ccmPolarCoordinateSection a 1 0)
  let bm := J (ccmPolarCoordinateSection a 0 1)
  have hcorrection : Tendsto (fun n => J (u n)-J (v n)) atTop (𝓝 0) := by
    have hp := (hvweak (ccmPolarApertureVector a (1/2))).smul_const bp
    have hm := (hvweak (ccmPolarApertureVector a (-1/2))).smul_const bm
    have hid : (fun n => J (u n)-J (v n)) =
        fun n => -(inner ℂ (ccmPolarApertureVector a (1/2)) (J (v n)) • bp) -
          inner ℂ (ccmPolarApertureVector a (-1/2)) (J (v n)) • bm := by
      funext n
      simp only [u, ccmPolarCoordinateCorrection, map_sub, map_smul]
      change (J (v n) -
          inner ℂ (ccmPolarApertureVector a (1/2)) (J (v n)) • bp -
          inner ℂ (ccmPolarApertureVector a (-1/2)) (J (v n)) • bm) - J (v n) = _
      module
    rw [hid]
    simpa only [zero_smul, neg_zero, sub_zero] using hp.neg.sub hm
  exact ⟨u, fun n => isPolarConstrained_ccmPolarCoordinateCorrection a (v n),
    by simpa only [zero_add, sub_add_sub_cancel] using hcorrection.add herr⟩

/-- The supported coherent cost survives on genuine exactly pole-constrained
sources even as the complete actual-prime edge energy tends to zero. -/
theorem exists_ccmPolarConstrained_schurEdge_null_supportedGamma_survives
    (a : SuzukiPositiveAperture) :
    ∃ u : ℕ → CCMArchimedeanFormDomain a,
      (∀ n, IsPolarConstrained a (u n)) ∧
      Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u n)‖)
        atTop (𝓝 ‖ccmSchurPoleVector a‖) ∧
      (∀ g : suzukiApertureHilbert a,
        Tendsto (fun n => inner ℂ g (ccmArchimedeanFormToAperture a (u n)))
          atTop (𝓝 0)) ∧
      Tendsto (fun n => ccmPrimePoleSchurEnergy a
        (ccmArchimedeanFormToAperture a (u n)).1) atTop (𝓝 0) ∧
      Tendsto (fun n => ccmActualHeadSupportedCoherentGammaCost a
        (⌊Real.exp (2*a.1)⌋₊+1) (ccmArchimedeanFormToAperture a (u n)).1)
        atTop (𝓝 (ccmActualHeadSupportedCoherentGammaCost a (⌊Real.exp (2*a.1)⌋₊+1)
          (ccmSchurPoleVector a).1)) := by
  obtain ⟨κ,_,hnorm,hweak,henergy,hcost⟩ :=
    exists_ccmSchurPole_recurrence_with_supportedGammaCost a
  let f : ℕ → suzukiApertureHilbert a :=
    fun n => ccmApertureModulation a (κ n) (ccmSchurPoleVector a)
  obtain ⟨u,hu,hclose⟩ := constrained_lift a f hweak
  let J := ccmArchimedeanFormToAperture a
  let N := ⌊Real.exp (2*a.1)⌋₊+1
  have hcloseNorm : Tendsto (fun n => ‖J (u n)-f n‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hclose.norm
  have huNorm : Tendsto (fun n => ‖J (u n)‖) atTop (𝓝 ‖ccmSchurPoleVector a‖) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) _ hcloseNorm
    intro n
    rw [← hnorm n]
    exact dist_norm_norm_le _ _
  have huweak (g : suzukiApertureHilbert a) :
      Tendsto (fun n => inner ℂ g (J (u n))) atTop (𝓝 0) := by
    have h := ((innerSL ℂ g).continuous.tendsto 0).comp hclose
    simp only [map_zero] at h
    change Tendsto (fun n => inner ℂ g (J (u n)-f n)) atTop (𝓝 0) at h
    have hw := hweak g
    change Tendsto (fun n => inner ℂ g (f n)) atTop (𝓝 0) at hw
    simpa only [zero_add, inner_sub_right, sub_add_cancel] using h.add hw
  refine ⟨u,hu,huNorm,huweak,?_,?_⟩
  · have he : Tendsto (fun n => ccmPrimePoleSchurEnergy a (J (u n)-f n).1) atTop (𝓝 0) := by
      have hb := (hcloseNorm.pow 2).const_mul (2*ccmPrimePoleSchurEnvelope a)
      simp only [zero_pow two_ne_zero, mul_zero] at hb
      exact squeeze_zero (fun n => ccmPrimePoleSchurEnergy_nonneg a _)
        (fun n => ccmPrimePoleSchurEnergy_le_two_envelope a _) hb
    have hb := (henergy.const_mul 2).add (he.const_mul 2)
    simp only [mul_zero, zero_add] at hb
    apply squeeze_zero (fun n => ccmPrimePoleSchurEnergy_nonneg a _) _ hb
    intro n
    have h := ccmPrimePoleSchurEnergy_sub_le a (f n) (f n-J (u n))
    rw [sub_sub_cancel] at h
    have hsym : ccmPrimePoleSchurEnergy a (f n-J (u n)).1 =
        ccmPrimePoleSchurEnergy a (J (u n)-f n).1 := by
      have hn := ccmPrimePoleSchurEnergy_neg a (J (u n)-f n).1
      simpa only [Submodule.coe_sub, neg_sub] using hn
    rwa [hsym] at h
  · have hfNorm : Tendsto (fun n => ‖f n‖) atTop (𝓝 ‖ccmSchurPoleVector a‖) := by
      simpa only [f, hnorm] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖ccmSchurPoleVector a‖) atTop
          (𝓝 ‖ccmSchurPoleVector a‖))
    have hb := (hcloseNorm.const_mul (ccmCoherentGammaPhysicalBound (2*a.1) N)).mul
      (huNorm.add hfNorm)
    simp only [mul_zero, zero_mul] at hb
    have hc : Tendsto (fun n =>
        ccmActualHeadSupportedCoherentGammaCost a N (J (u n)).1 -
          ccmActualHeadSupportedCoherentGammaCost a N (f n).1) atTop (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero (fun _ => norm_nonneg _) _ hb
      intro n
      simpa only [Real.norm_eq_abs, ← Submodule.coe_sub, Submodule.norm_coe] using
        abs_ccmActualHeadSupportedCoherentGammaCost_sub_le a N (J (u n)).1 (f n).1
    simpa only [N, f, J, zero_add, sub_add_cancel] using hc.add hcost

/-- No finite scalar can dominate the supported coherent cost by the complete
prime-edge energy on the genuine constrained domain at this fixed aperture. -/
theorem not_exists_ccmPolarConstrained_supportedGammaCost_schurBound
    (a : SuzukiPositiveAperture) (ha : Real.log 2 < 2*a.1) :
    ¬ ∃ C : ℝ, ∀ u : CCMArchimedeanFormDomain a,
      IsPolarConstrained a u →
        ccmActualHeadSupportedCoherentGammaCost a (⌊Real.exp (2*a.1)⌋₊+1)
            (ccmArchimedeanFormToAperture a u).1 ≤
          C * ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u).1 := by
  rintro ⟨C,hbound⟩
  obtain ⟨u,hu,_,_,he,hcost⟩ :=
    exists_ccmPolarConstrained_schurEdge_null_supportedGamma_survives a
  have hle := le_of_tendsto_of_tendsto hcost (he.const_mul C)
    (Eventually.of_forall fun n => hbound (u n) (hu n))
  have hN : 3 ≤ ⌊Real.exp (2*a.1)⌋₊+1 := by
    have h2 : (2 : ℝ) < Real.exp (2*a.1) :=
      (Real.log_lt_iff_lt_exp (by norm_num)).mp ha
    have hf : 2 ≤ ⌊Real.exp (2*a.1)⌋₊ := Nat.le_floor h2.le
    omega
  simp only [mul_zero] at hle
  exact (not_le_of_gt
    (ccmActualHeadSupportedCoherentGammaCost_schurPole_pos a ha _ hN)) hle

end RHTower
