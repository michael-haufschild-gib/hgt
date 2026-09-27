import GaloisForLFunctions.RHTower.CCMPrimePoleSchurRecurrence
import GaloisForLFunctions.RHTower.CCMPrimePoleSchurEnergyBounds
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarSourceCancellation

/-!
# Exact pole constraints do not create a prime-edge gap

Recurrent pole modulations are approximated in physical L2 by genuine form-domain
vectors. The existing two-pole section corrects their moments exactly. Its full
norm tends to zero, so all mixed edge terms are controlled by the edge stability
estimate. The resulting sources have nonvanishing physical mass and vanishing
prime-edge energy. This tests the proposed graph gap on the actual form domain.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct Topology
noncomputable section
namespace RHTower

theorem ccmSchurPoleVector_ne_zero (a : SuzukiPositiveAperture) :
    ccmSchurPoleVector a ≠ 0 := by
  intro hz
  have hh := congrArg (fun f => (inner ℂ (ccmPolarApertureVector a (-1/2)) f).re) hz
  rw [ccmSchurPoleVector, inner_add_right, Complex.add_re, inner_zero_right,
    Complex.zero_re] at hh
  have hc := inner_ccmPolarApertureVector_opposite a (1/2)
  have hself := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
    (ccmPolarApertureVector a (-1/2))
  change ‖ccmPolarApertureVector a (-1/2)‖ ^ 2 =
    (inner ℂ (ccmPolarApertureVector a (-1/2)) (ccmPolarApertureVector a (-1/2))).re at hself
  have hc' : (inner ℂ (ccmPolarApertureVector a (-1/2))
      (ccmPolarApertureVector a (1/2))).re = 2*a.1 := by
    convert congrArg Complex.re hc using 1 <;> norm_num
  nlinarith [sq_nonneg ‖ccmPolarApertureVector a (-1/2)‖, a.property]

/-- Every fixed aperture has genuine exactly pole-constrained sources whose
full prime-edge energy tends to zero while physical mass stays nonzero. -/
theorem exists_ccmPolarConstrained_schurEdge_nullSequence (a : SuzukiPositiveAperture) :
    ∃ u : ℕ → CCMArchimedeanFormDomain a,
      (∀ n, IsPolarConstrained a (u n)) ∧
      Tendsto (fun n => ‖ccmArchimedeanFormToAperture a (u n)‖)
        atTop (𝓝 ‖ccmSchurPoleVector a‖) ∧
      (∀ g : suzukiApertureHilbert a,
        Tendsto (fun n => inner ℂ g (ccmArchimedeanFormToAperture a (u n)))
          atTop (𝓝 0)) ∧
      Tendsto (fun n => ccmPrimePoleSchurEnergy a
        (ccmArchimedeanFormToAperture a (u n)).1) atTop (𝓝 0) := by
  classical
  obtain ⟨κ, _, hnorm, hweak, henergy⟩ := exists_ccmSchurPole_recurrent_modulations a
  let f : ℕ → suzukiApertureHilbert a :=
    fun n => ccmApertureModulation a (κ n) (ccmSchurPoleVector a)
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
    have hw := hweak g
    change Tendsto (fun n => inner ℂ g (f n)) atTop (𝓝 0) at hw
    simpa only [zero_add, inner_sub_right, sub_add_cancel] using h.add hw
  let u : ℕ → CCMArchimedeanFormDomain a := fun n => ccmPolarCoordinateCorrection a (v n)
  let bp := J (ccmPolarCoordinateSection a 1 0)
  let bm := J (ccmPolarCoordinateSection a 0 1)
  have hcorrection : Tendsto (fun n => J (u n)-J (v n)) atTop (𝓝 0) := by
    have hp := (hvweak (ccmPolarApertureVector a (1/2))).smul_const bp
    have hm := (hvweak (ccmPolarApertureVector a (-1/2))).smul_const bm
    have hs := hp.neg.sub hm
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
    simpa only [zero_smul, neg_zero, sub_zero] using hs
  have hclose : Tendsto (fun n => J (u n)-f n) atTop (𝓝 0) := by
    simpa only [zero_add, sub_add_sub_cancel] using hcorrection.add herr
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
  refine ⟨u, fun n => isPolarConstrained_ccmPolarCoordinateCorrection a (v n),
    huNorm, huweak, ?_⟩
  have he : Tendsto (fun n => ccmPrimePoleSchurEnergy a (J (u n)-f n).1) atTop (𝓝 0) := by
    have hb := (hcloseNorm.pow 2).const_mul (2*ccmPrimePoleSchurEnvelope a)
    simp only [zero_pow two_ne_zero, mul_zero] at hb
    exact squeeze_zero (fun n => ccmPrimePoleSchurEnergy_nonneg a _)
      (fun n => ccmPrimePoleSchurEnergy_le_two_envelope a _) hb
  have hb := (henergy.const_mul 2).add (he.const_mul 2)
  simp only [mul_zero, zero_add] at hb
  apply squeeze_zero (fun n => ccmPrimePoleSchurEnergy_nonneg a _) _ hb
  intro n
  have h := ccmPrimePoleSchurEnergy_sub_le a (f n) (f n-J (u n))
  have heq : f n - (f n-J (u n)) = J (u n) := sub_sub_cancel _ _
  rw [heq] at h
  have hsym : ccmPrimePoleSchurEnergy a (f n-J (u n)).1 =
      ccmPrimePoleSchurEnergy a (J (u n)-f n).1 := by
    have hn := ccmPrimePoleSchurEnergy_neg a (J (u n)-f n).1
    simpa only [Submodule.coe_sub, neg_sub] using hn
  rwa [hsym] at h

/-- Pole constraints alone cannot supply any positive physical-norm floor for
the full actual-prime edge energy, even at a single fixed aperture. -/
theorem not_exists_ccmPolarConstrained_schurEdge_gap (a : SuzukiPositiveAperture) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ u : CCMArchimedeanFormDomain a,
      IsPolarConstrained a u →
        c * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ≤
          ccmPrimePoleSchurEnergy a (ccmArchimedeanFormToAperture a u).1 := by
  rintro ⟨c,hc,hgap⟩
  obtain ⟨u,hu,hnorm,_,he⟩ := exists_ccmPolarConstrained_schurEdge_nullSequence a
  have hle := le_of_tendsto_of_tendsto ((hnorm.pow 2).const_mul c) he
    (Eventually.of_forall fun n => hgap (u n) (hu n))
  have hp : 0 < ‖ccmSchurPoleVector a‖ := norm_pos_iff.mpr (ccmSchurPoleVector_ne_zero a)
  nlinarith [sq_pos_of_pos hp]

end RHTower
