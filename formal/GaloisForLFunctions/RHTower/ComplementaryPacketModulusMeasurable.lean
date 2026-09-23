import GaloisForLFunctions.RHTower.ComplementaryPacketKernelIntegrability

/-!
# Measurability of the two-point packet modulus

The two-point modulus `a ↦ D(a)` of a boundary packet path splits into a swept branch and a
translation modulus.  The swept branch is monotone in the separation, because its integrand is a
square; the translation modulus is measurable by Fubini, because `(a, r) ↦ (k (r + a) - k r)^(2 : ℕ)` is
jointly measurable.  Hence `D` is measurable, which is what allows the packet energy
`E[D(|H - H'|)]` of `ComplementaryPacketFourUnitEnergy` to be formed against the clock gap law.

Together with the cofinal bound this also gives integrability of `a ↦ D(|a|)` against any
probability measure whose absolute first moment is finite.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

section Measurable

variable {k : ℝ → ℝ} {c : ℝ}

private theorem integrableOn_shifted_sq
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ (2 : ℕ)) (Ioi 0)) (c : ℝ)
    (b : ℝ) : IntegrableOn (fun r => (k r + c) ^ (2 : ℕ)) (Ioc (0 : ℝ) b) := by
  have hsub : Ioc (0 : ℝ) b ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hk : IntegrableOn k (Ioc (0 : ℝ) b) := hint.mono_set hsub
  have hk2 : IntegrableOn (fun r => k r ^ (2 : ℕ)) (Ioc (0 : ℝ) b) := hsq.mono_set hsub
  have hconst : IntegrableOn (fun _ : ℝ => c ^ (2 : ℕ)) (Ioc (0 : ℝ) b) :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  have hsum : IntegrableOn (fun r => k r ^ (2 : ℕ) + 2 * c * k r + c ^ (2 : ℕ)) (Ioc (0 : ℝ) b) := by
    exact (hk2.add (hk.const_mul (2 * c))).add hconst
  refine hsum.congr_fun ?_ measurableSet_Ioc
  intro r _
  ring

/-- The swept branch of the modulus is monotone in the separation. -/
theorem monotone_packetSweptBranch
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ (2 : ℕ)) (Ioi 0)) (c : ℝ) :
    Monotone fun a : ℝ => ∫ r in Ioc (0 : ℝ) a, (k r + c) ^ (2 : ℕ) := by
  intro a b hab
  refine setIntegral_mono_set (integrableOn_shifted_sq hint hsq c b) ?_ ?_
  · filter_upwards with r using sq_nonneg _
  · exact Filter.Eventually.of_forall (Ioc_subset_Ioc_right hab)

/-- The translation branch of the modulus is measurable in the separation. -/
theorem measurable_packetTranslationBranch (hmk : Measurable k) :
    Measurable fun a : ℝ => ∫ r in Ioi (0 : ℝ), (k (r + a) - k r) ^ (2 : ℕ) := by
  have hjoint : StronglyMeasurable fun p : ℝ × ℝ => (k (p.2 + p.1) - k p.2) ^ (2 : ℕ) :=
    (((hmk.comp (measurable_snd.add measurable_fst)).sub
      (hmk.comp measurable_snd)).pow_const 2).stronglyMeasurable
  exact (hjoint.integral_prod_right' (ν := volume.restrict (Ioi 0))).measurable

/-- **The two-point modulus is measurable.** -/
theorem measurable_packetTranslationModulus (hmk : Measurable k)
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ (2 : ℕ)) (Ioi 0)) (c : ℝ) :
    Measurable (packetTranslationModulus k c) :=
  (monotone_packetSweptBranch hint hsq c).measurable.add
    (measurable_packetTranslationBranch hmk)

end Measurable

/-- **The packet modulus is integrable against every clock gap law with a finite first moment.**
This is the hypothesis `Integrable (fun x => D |x|)` of the four-unit transfer, discharged from the
cofinal bound alone. -/
theorem integrable_packetTranslationModulus_abs
    {k : ℝ → ℝ} {A B c : ℝ} (hmk : Measurable k)
    (hint : IntegrableOn k (Ioi 0)) (hsq : IntegrableOn (fun r => k r ^ (2 : ℕ)) (Ioi 0))
    (hA : (∫ r in Ioi (0 : ℝ), |k r|) ≤ A)
    (hB : (∫ r in Ioi (0 : ℝ), k r ^ (2 : ℕ)) ≤ B)
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (habs : Integrable (fun x : ℝ => |x|) μ) :
    Integrable (fun x : ℝ => packetTranslationModulus k c |x|) μ := by
  set C : ℝ := 5 * B + 2 * |c| * A with hCdef
  have hmeas : Measurable fun x : ℝ =>
      packetTranslationModulus k c |x| :=
    (measurable_packetTranslationModulus hmk hint hsq c).comp continuous_abs.measurable
  have hdom : Integrable (fun x : ℝ => c ^ (2 : ℕ) * |x| + C) μ :=
    (habs.const_mul (c ^ (2 : ℕ))).add (integrable_const C)
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  have hbound := abs_packetTranslationModulus_sub_le (c := c) hmk hint hsq hA hB (abs_nonneg x)
  have hnn : (0 : ℝ) ≤ c ^ (2 : ℕ) * |x| := by positivity
  rw [Real.norm_eq_abs, abs_le]
  have h := abs_le.mp hbound
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end

end RHTower
