import GaloisForLFunctions.HTGeometry.BohrHullCharacter
import GaloisForLFunctions.HTGeometry.CompactAbelianPeterWeyl
import GaloisForLFunctions.HTGeometry.ContinuousCharacterDifferentiable
import GaloisForLFunctions.HTGeometry.BohrApproximation

/-!
# Hull characters separate the carrier

Peter–Weyl gives, for two distinct points of a compact abelian group, a continuous character telling
them apart.  On the Bohr hull that character restricts to a continuous unimodular character of the
line, which is `t ↦ e^{iμt}` for a real `μ`, and `μ` is a frequency of the hull because the character
is uniformly continuous on the compact hull.  So the hull characters `bohrHullChar f μ` — one for each
hull frequency — already separate the points of the carrier.
-/

open Filter Topology

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {f : ℝ →ᵇ ℂ}

/-- **The characters of the hull separate its points.** -/
theorem exists_bohrHullChar_ne (huc : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    [SecondCountableTopology (BohrHull f)] [T2Space (BohrHull f)]
    {x y : BohrHull f} (hxy : x ≠ y) :
    ∃ mu : ℝ, IsBohrHullFrequency f mu ∧ bohrHullChar f mu x ≠ bohrHullChar f mu y := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  obtain ⟨χ, hχcont, hχmul, hχnorm, hχg⟩ := CompactAbelian.exists_character_ne_one hne
  -- the pullback to the line is a continuous unimodular character
  have hψcont : Continuous fun t : ℝ => χ (bohrIota f t) :=
    hχcont.comp (continuous_bohrIota huc)
  have hψmul : ∀ s t : ℝ, χ (bohrIota f (s + t)) = χ (bohrIota f s) * χ (bohrIota f t) := by
    intro s t
    rw [bohrIota_add, hχmul]
  have hne0 : χ (0 : BohrHull f) ≠ 0 := by
    intro h0
    have hn := hχnorm (0 : BohrHull f)
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hχ0 : χ (0 : BohrHull f) = 1 := by
    have h := hχmul 0 0
    rw [add_zero] at h
    have hcancel : χ (0 : BohrHull f) * 1 = χ (0 : BohrHull f) * χ 0 := by
      rw [mul_one]
      exact h
    exact (mul_left_cancel₀ hne0 hcancel).symm
  have hψ0 : χ (bohrIota f 0) = 1 := by
    rw [bohrIota_zero]
    exact hχ0
  have hψnorm : ∀ t : ℝ, ‖χ (bohrIota f t)‖ = 1 := fun t => hχnorm _
  obtain ⟨mu, hmu⟩ := HTGeometry.exists_real_generator_of_continuous_unimodular_character
    hψcont hψmul hψ0 hψnorm
  -- the frequency belongs to the hull
  have hfreq : IsBohrHullFrequency f mu := by
    have huc : UniformContinuous χ := CompactSpace.uniformContinuous_of_continuous hχcont
    have hcoe : UniformContinuous (fun t : BohrLine f => (t : BohrHull f)) :=
      UniformSpace.Completion.uniformContinuous_coe _
    have hcomp : UniformContinuous (fun t : BohrLine f => χ (t : BohrHull f)) := huc.comp hcoe
    have hEq : (fun t : BohrLine f => expChar mu t.val)
        = fun t : BohrLine f => χ (t : BohrHull f) := by
      funext t
      have hcoe : (t : BohrHull f) = bohrIota f t.val := rfl
      rw [hcoe, hmu t.val, expChar]
      congr 1
      push_cast
      ring
    rw [IsBohrHullFrequency, hEq]
    exact hcomp
  -- the hull character is that character
  have hchar : bohrHullChar f mu = χ := by
    refine Continuous.ext_on (denseRange_bohrIota f) (continuous_bohrHullChar f mu) hχcont ?_
    rintro z ⟨t, rfl⟩
    rw [bohrHullChar_bohrIota hfreq, hmu t, expChar]
    congr 1
    push_cast
    ring
  refine ⟨mu, hfreq, ?_⟩
  rw [hchar]
  intro hval
  have hy0 : χ y ≠ 0 := by
    intro h0
    have hn := hχnorm y
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  have hxy' : χ (x - y) * χ y = χ x := by
    rw [← hχmul]
    congr 1
    abel
  rw [hval] at hxy'
  have hone : χ (x - y) * χ y = 1 * χ y := by
    rw [hxy', one_mul]
  exact hχg (mul_right_cancel₀ hy0 hone)

/-- **The approximation theorem with hull frequencies.**  The corpus's trigonometric approximation
carries frequencies that are frequencies *of the hull*: each approximating character extends
continuously to the compact hull, so its generator is a hull frequency. -/
theorem exists_trig_approx_hullFreq (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (lam : Fin n → ℝ),
      (∀ j, IsBohrHullFrequency f (lam j)) ∧
      ∀ t : ℝ, ‖f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I)‖ ≤ ε := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  borelize (BohrHull f)
  set F : C(BohrHull f, ℂ) := ⟨bohrEval f, continuous_bohrEval f⟩ with hF
  obtain ⟨n, c, χ, hχ, hclose⟩ :=
    CompactAbelian.exists_char_combination_approx F (half_pos hε)
  have hpull : ∀ j : Fin n, ∃ lam : ℝ, ∀ t : ℝ,
      χ j (bohrIota f t) = Complex.exp ((lam * t : ℝ) * Complex.I) := by
    intro j
    refine exists_exp_of_continuous_character ?_ ?_ ?_
    · exact (χ j).continuous.comp (continuous_bohrIota hf)
    · intro s t
      rw [bohrIota_add, (hχ j).map_add]
    · intro t
      exact (hχ j).norm_one _
  choose lam hlam using hpull
  have hfreq : ∀ j : Fin n, IsBohrHullFrequency f (lam j) := by
    intro j
    have huc : UniformContinuous (χ j) :=
      CompactSpace.uniformContinuous_of_continuous (χ j).continuous
    have hcoe : UniformContinuous (fun t : BohrLine f => (t : BohrHull f)) :=
      UniformSpace.Completion.uniformContinuous_coe _
    have hEq : (fun t : BohrLine f => expChar (lam j) t.val)
        = fun t : BohrLine f => χ j (t : BohrHull f) := by
      funext t
      have hcoeval : (t : BohrHull f) = bohrIota f t.val := rfl
      rw [hcoeval, hlam j t.val, expChar]
    rw [IsBohrHullFrequency, hEq]
    exact huc.comp hcoe
  refine ⟨n, c, lam, hfreq, fun t => ?_⟩
  have hval : (F - ∑ j, c j • χ j) (bohrIota f t)
      = f t - ∑ j, c j * Complex.exp ((lam j * t : ℝ) * Complex.I) := by
    rw [ContinuousMap.sub_apply]
    congr 1
    · show bohrEval f (bohrIota f t) = f t
      exact bohrEval_bohrIota f t
    · rw [ContinuousMap.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [ContinuousMap.smul_apply, smul_eq_mul, hlam j t]
  rw [← hval]
  calc ‖(F - ∑ j, c j • χ j) (bohrIota f t)‖ ≤ ‖F - ∑ j, c j • χ j‖ :=
        ContinuousMap.norm_coe_le_norm _ _
    _ ≤ ε := by linarith [hclose]

end GaloisForLFunctions
