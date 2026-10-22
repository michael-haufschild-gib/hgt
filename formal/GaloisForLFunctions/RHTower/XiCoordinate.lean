import GaloisForLFunctions.RHTower.CCM.CCMFirstRowEnvelopeTail
import GaloisForLFunctions.RHTower.CCM.CCMFirstRowDunsterModel

/-!
# The Dunster coordinate as a change of variable

Dunster's exterior coordinate `r = xi_s(x)` is used as a substitution: estimates proved in the
`r` variable transfer to the `x` variable and back.  For that the coordinate has to be a
homeomorphism onto its range, which needs three facts absent from the corpus: that the phase is
continuous up to the singular endpoint, that it is strictly increasing, and what its image is.

Continuity at the endpoint is not automatic — the integrand `xi'` blows up there — but the corpus's
two-sided bracket `sqrt(1-s) sqrt(x²-1) <= xi_s(x) <= sqrt(x²-1)` squeezes the phase to zero, which
settles it.  Monotonicity is then the positivity of the speed, and the image follows by the
intermediate value theorem.
-/

noncomputable section

open Set Filter Topology

namespace GaloisForLFunctions.RHTower

@[simp] theorem xiEndpointPhase_one (s : ℝ) : xiEndpointPhase s 1 = 0 := by
  rw [xiEndpointPhase]
  simp

/-- The phase is continuous at the singular endpoint, by the corpus's two-sided bracket. -/
theorem continuousWithinAt_xiEndpointPhase_one {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ContinuousWithinAt (xiEndpointPhase s) (Ici 1) 1 := by
  have hup : Tendsto (fun x : ℝ => Real.sqrt (x ^ (2 : ℕ) - 1)) (nhdsWithin 1 (Ici 1)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => Real.sqrt (x ^ (2 : ℕ) - 1)) 1 := by fun_prop
    have h2 : Tendsto (fun x : ℝ => Real.sqrt (x ^ (2 : ℕ) - 1)) (nhdsWithin 1 (Ici 1))
        (nhds (Real.sqrt ((1 : ℝ) ^ (2 : ℕ) - 1))) := hc.continuousWithinAt
    have hval : Real.sqrt ((1 : ℝ) ^ (2 : ℕ) - 1) = 0 := by norm_num
    rwa [hval] at h2
  have hmem : ∀ᶠ x : ℝ in nhdsWithin 1 (Ici 1), x ∈ Ici (1 : ℝ) := eventually_mem_nhdsWithin
  have hlow : ∀ᶠ x : ℝ in nhdsWithin 1 (Ici 1), (0 : ℝ) ≤ xiEndpointPhase s x := by
    filter_upwards [hmem] with x hx
    have h := (xiEndpointPhase_bounds hs0 hs1 hx).1
    have hnn : (0 : ℝ) ≤ Real.sqrt (1 - s) * Real.sqrt (x ^ (2 : ℕ) - 1) := by positivity
    linarith
  have hhigh : ∀ᶠ x : ℝ in nhdsWithin 1 (Ici 1),
      xiEndpointPhase s x ≤ Real.sqrt (x ^ (2 : ℕ) - 1) := by
    filter_upwards [hmem] with x hx
    exact (xiEndpointPhase_bounds hs0 hs1 hx).2
  have : Tendsto (xiEndpointPhase s) (nhdsWithin 1 (Ici 1)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup hlow hhigh
  simpa [ContinuousWithinAt] using this

theorem continuousOn_xiEndpointPhase_Ici {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ContinuousOn (xiEndpointPhase s) (Ici 1) := by
  intro x hx
  rcases eq_or_lt_of_le (mem_Ici.mp hx) with h | h
  · rw [← h]
    exact continuousWithinAt_xiEndpointPhase_one hs0 hs1
  · exact ((hasDerivAt_xiEndpointPhase hs0 h).continuousAt).continuousWithinAt

/-- **The Dunster coordinate is strictly increasing.** -/
theorem strictMonoOn_xiEndpointPhase {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    StrictMonoOn (xiEndpointPhase s) (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 1)
    (continuousOn_xiEndpointPhase_Ici hs0 (by linarith)) fun x hx => ?_
  rw [interior_Ici] at hx
  have hx1 : (1 : ℝ) < x := hx
  rw [(hasDerivAt_xiEndpointPhase hs0 hx1).deriv]
  exact xiSpeed_pos hs1 hx1

theorem injOn_xiEndpointPhase {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    InjOn (xiEndpointPhase s) (Ici 1) :=
  (strictMonoOn_xiEndpointPhase hs0 hs1).injOn

/-- **The image of a closed exterior interval is the closed phase interval.** -/
theorem image_xiEndpointPhase_Icc {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX : 1 ≤ X) :
    xiEndpointPhase s '' Icc 1 X = Icc 0 (xiEndpointPhase s X) := by
  have hsub : Icc (1 : ℝ) X ⊆ Ici 1 := Icc_subset_Ici_self
  have hcont : ContinuousOn (xiEndpointPhase s) (Icc 1 X) :=
    (continuousOn_xiEndpointPhase_Ici hs0 (by linarith)).mono hsub
  have hmono : StrictMonoOn (xiEndpointPhase s) (Icc 1 X) :=
    (strictMonoOn_xiEndpointPhase hs0 hs1).mono hsub
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← xiEndpointPhase_one s]
      exact hmono.monotoneOn (left_mem_Icc.mpr hX) hx hx.1
    · exact hmono.monotoneOn hx (right_mem_Icc.mpr hX) hx.2
  · have h := intermediate_value_Icc hX hcont
    rwa [xiEndpointPhase_one] at h

/-- The phase of the exterior interval endpoint is below `2`, so the bounded-radius Bessel
estimates apply to the transported integral. -/
theorem xiEndpointPhase_le_two {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hX1 : 1 ≤ X)
    (hX : X ≤ 2) : xiEndpointPhase s X ≤ 2 := by
  have h := (xiEndpointPhase_bounds hs0 hs1 hX1).2
  have hsq : Real.sqrt (X ^ (2 : ℕ) - 1) ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  linarith

/-- The image of an open exterior interval is the open phase interval. -/
theorem image_xiEndpointPhase_Ioo {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX : 1 ≤ X) :
    xiEndpointPhase s '' Ioo 1 X = Ioo 0 (xiEndpointPhase s X) := by
  have hsub : Ioo (1 : ℝ) X ⊆ Ici 1 := fun x hx => le_of_lt hx.1
  have hmono := strictMonoOn_xiEndpointPhase hs0 hs1
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← xiEndpointPhase_one s]
      exact hmono (mem_Ici.mpr le_rfl) (hsub hx) hx.1
    · exact hmono (hsub hx) (mem_Ici.mpr hX) hx.2
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := (image_xiEndpointPhase_Icc hs0 hs1 hX).symm ▸
      (Ioo_subset_Icc_self hy)
    refine ⟨x, ⟨?_, ?_⟩, hxy⟩
    · rcases eq_or_lt_of_le hx.1 with h | h
      · exfalso
        rw [← h, xiEndpointPhase_one] at hxy
        exact absurd hxy.symm (ne_of_gt hy.1)
      · exact h
    · rcases eq_or_lt_of_le hx.2 with h | h
      · exfalso
        rw [h] at hxy
        exact absurd hxy (ne_of_gt hy.2)
      · exact h

/-- **The Dunster substitution.**  An integral in the phase variable equals the integral of the
speed-weighted composite in the exterior variable.  The singular endpoint is excluded from both
sides, which changes neither integral. -/
theorem setIntegral_comp_xiEndpointPhase {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hX : 1 ≤ X)
    (G : ℝ → ℝ) :
    (∫ r in Ioo 0 (xiEndpointPhase s X), G r)
      = ∫ x in Ioo 1 X, xiSpeed s x * G (xiEndpointPhase s x) := by
  have hsub : Ioo (1 : ℝ) X ⊆ Ici 1 := fun x hx => le_of_lt hx.1
  have hderiv : ∀ x ∈ Ioo (1 : ℝ) X,
      HasDerivWithinAt (xiEndpointPhase s) (xiSpeed s x) (Ioo 1 X) x := fun x hx =>
    (hasDerivAt_xiEndpointPhase hs0 hx.1).hasDerivWithinAt
  have hinj : InjOn (xiEndpointPhase s) (Ioo 1 X) :=
    (injOn_xiEndpointPhase hs0 hs1).mono hsub
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hderiv hinj G
  rw [image_xiEndpointPhase_Ioo hs0 hs1 hX] at h
  rw [h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  rw [abs_of_pos (xiSpeed_pos hs1 hx.1), smul_eq_mul]

/-- The substitution in interval-integral form, which is what the bounded-radius estimates
consume. -/
theorem intervalIntegral_comp_xiEndpointPhase {s X : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2)
    (hX : 1 ≤ X) (G : ℝ → ℝ) :
    (∫ r in (0 : ℝ)..(xiEndpointPhase s X), G r)
      = ∫ x in (1 : ℝ)..X, xiSpeed s x * G (xiEndpointPhase s x) := by
  have hphase : 0 ≤ xiEndpointPhase s X := by
    rw [← xiEndpointPhase_one s]
    exact (strictMonoOn_xiEndpointPhase hs0 hs1).monotoneOn (mem_Ici.mpr le_rfl)
      (mem_Ici.mpr hX) hX
  rw [intervalIntegral.integral_of_le hphase, intervalIntegral.integral_of_le hX,
    MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact setIntegral_comp_xiEndpointPhase hs0 hs1 hX G


end GaloisForLFunctions.RHTower
