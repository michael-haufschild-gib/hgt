import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterMixedPtolemyWall
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Radial transport of the theta Ptolemy wall

The reflection-odd four-point wall is nonlinear in the center-mixed density, so linearity of
Hedenmalm's radial integral does not by itself transport its sign.  Polarizing the wall on the
product radial space exposes an exact law-of-total-variance decomposition: fibre defects add,
while variation of the middle-to-first drop ratio contributes a square.  Consequently positive
equispaced Ptolemy walls on all completed-source fibres pass through the continuum mixture, and
every mixed failure descends to a genuine source-fibre failure.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- First equal-step drop of one reflected completed-source fibre. -/
def thetaCuspReflectedSourceFirstDrop (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u t

/-- Middle equal-step drop of one reflected completed-source fibre. -/
def thetaCuspReflectedSourceMiddleDrop (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u t - thetaCuspReflectedSourceProduct u (2 * t)

/-- Full drop across the equispaced four-point fibre. -/
def thetaCuspReflectedSourceFullDrop (u t : ℝ) : ℝ :=
  thetaCuspReflectedSourceProduct u 0 - thetaCuspReflectedSourceProduct u (3 * t)

/-- Reflection-odd wall of one unnormalized completed-source fibre. -/
def thetaCuspReflectedSourceOddParityWall (u t : ℝ) : ℝ :=
  toeplitzFourOddParityWall
    (thetaCuspReflectedSourceProduct u 0)
    (thetaCuspReflectedSourceProduct u t)
    (thetaCuspReflectedSourceProduct u (2 * t))
    (thetaCuspReflectedSourceProduct u (3 * t))

/-- Polarization of two source-fibre odd walls. -/
def thetaCuspReflectedSourcePtolemyPolarization (u v t : ℝ) : ℝ :=
  thetaCuspReflectedSourceFirstDrop u t * thetaCuspReflectedSourceFullDrop v t +
    thetaCuspReflectedSourceFirstDrop v t * thetaCuspReflectedSourceFullDrop u t -
      2 * thetaCuspReflectedSourceMiddleDrop u t *
        thetaCuspReflectedSourceMiddleDrop v t

theorem thetaCuspReflectedSourceOddParityWall_eq_dropProduct
    (u t : ℝ) :
    thetaCuspReflectedSourceOddParityWall u t =
      thetaCuspReflectedSourceFirstDrop u t *
          thetaCuspReflectedSourceFullDrop u t -
        thetaCuspReflectedSourceMiddleDrop u t ^ (2 : ℕ) := by
  unfold thetaCuspReflectedSourceOddParityWall toeplitzFourOddParityWall
    thetaCuspReflectedSourceFirstDrop thetaCuspReflectedSourceMiddleDrop
    thetaCuspReflectedSourceFullDrop
  ring

/-- Every positive displacement gives a strictly positive first fibre drop. -/
theorem thetaCuspReflectedSourceFirstDrop_pos
    (u : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < thetaCuspReflectedSourceFirstDrop u t := by
  unfold thetaCuspReflectedSourceFirstDrop
  exact sub_pos.mpr <|
    strictAntiOn_thetaCuspFullSource_mul_reflect u
      (show 0 ∈ Ici (0 : ℝ) by simp)
      (show t ∈ Ici (0 : ℝ) from ht.le) ht

/-- **Ptolemy law of total variance, pointwise form.**  Polarization of two fibres is the
sum of their normalized odd defects and the square of the discrepancy between their
middle-to-first drop ratios. -/
theorem thetaCuspReflectedSourcePtolemyPolarization_eq_defects_add_ratioSq
    (u v : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaCuspReflectedSourcePtolemyPolarization u v t =
      thetaCuspReflectedSourceFirstDrop v t /
          thetaCuspReflectedSourceFirstDrop u t *
        thetaCuspReflectedSourceOddParityWall u t +
      thetaCuspReflectedSourceFirstDrop u t /
          thetaCuspReflectedSourceFirstDrop v t *
        thetaCuspReflectedSourceOddParityWall v t +
      thetaCuspReflectedSourceFirstDrop u t *
          thetaCuspReflectedSourceFirstDrop v t *
        (thetaCuspReflectedSourceMiddleDrop u t /
              thetaCuspReflectedSourceFirstDrop u t -
            thetaCuspReflectedSourceMiddleDrop v t /
              thetaCuspReflectedSourceFirstDrop v t) ^ (2 : ℕ) := by
  have hu := (thetaCuspReflectedSourceFirstDrop_pos u ht).ne'
  have hv := (thetaCuspReflectedSourceFirstDrop_pos v ht).ne'
  rw [thetaCuspReflectedSourceOddParityWall_eq_dropProduct,
    thetaCuspReflectedSourceOddParityWall_eq_dropProduct]
  unfold thetaCuspReflectedSourcePtolemyPolarization
  field_simp [hu, hv]
  ring

/-- Nonnegative fibre walls make every cross-fibre polarization nonnegative. -/
theorem thetaCuspReflectedSourcePtolemyPolarization_nonneg
    (u v : ℝ) {t : ℝ} (ht : 0 < t)
    (hu : 0 ≤ thetaCuspReflectedSourceOddParityWall u t)
    (hv : 0 ≤ thetaCuspReflectedSourceOddParityWall v t) :
    0 ≤ thetaCuspReflectedSourcePtolemyPolarization u v t := by
  rw [thetaCuspReflectedSourcePtolemyPolarization_eq_defects_add_ratioSq u v ht]
  have hAu := (thetaCuspReflectedSourceFirstDrop_pos u ht).le
  have hAv := (thetaCuspReflectedSourceFirstDrop_pos v ht).le
  positivity

/-- Positive radial weight used by the physical center mixture. -/
def thetaCuspCenterMixedRadialWeight (a r : ℝ) : ℝ :=
  r * Real.sinh (a * r)

/-- Weighted first source-fibre drop. -/
def thetaCuspCenterMixedWeightedFirstDrop (a t r : ℝ) : ℝ :=
  thetaCuspCenterMixedRadialWeight a r *
    thetaCuspReflectedSourceFirstDrop (r / 2) t

/-- Weighted middle source-fibre drop. -/
def thetaCuspCenterMixedWeightedMiddleDrop (a t r : ℝ) : ℝ :=
  thetaCuspCenterMixedRadialWeight a r *
    thetaCuspReflectedSourceMiddleDrop (r / 2) t

/-- Weighted full source-fibre drop. -/
def thetaCuspCenterMixedWeightedFullDrop (a t r : ℝ) : ℝ :=
  thetaCuspCenterMixedRadialWeight a r *
    thetaCuspReflectedSourceFullDrop (r / 2) t

/-- Product-space polarization kernel whose integral is twice the mixed odd wall. -/
def thetaCuspCenterMixedPtolemyPolarizationKernel
    (a t : ℝ) (z : ℝ × ℝ) : ℝ :=
  thetaCuspCenterMixedWeightedFirstDrop a t z.1 *
      thetaCuspCenterMixedWeightedFullDrop a t z.2 +
    thetaCuspCenterMixedWeightedFirstDrop a t z.2 *
      thetaCuspCenterMixedWeightedFullDrop a t z.1 -
    2 * thetaCuspCenterMixedWeightedMiddleDrop a t z.1 *
      thetaCuspCenterMixedWeightedMiddleDrop a t z.2

private theorem integrable_thetaCuspCenterMixedWeightedDrops
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    Integrable (thetaCuspCenterMixedWeightedFirstDrop a t)
        (volume.restrict (Ioi 0)) ∧
      Integrable (thetaCuspCenterMixedWeightedMiddleDrop a t)
        (volume.restrict (Ioi 0)) ∧
      Integrable (thetaCuspCenterMixedWeightedFullDrop a t)
        (volume.restrict (Ioi 0)) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have h0 : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) 0) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha 0
  have ht : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) t) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha t
  have h2t : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) (2 * t)) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha (2 * t)
  have h3t : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) (3 * t)) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha (3 * t)
  constructor
  · change Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        (thetaCuspReflectedSourceProduct (r / 2) 0 -
          thetaCuspReflectedSourceProduct (r / 2) t)) mu
    convert h0.sub ht using 1
    funext r
    simp only [Pi.sub_apply, mul_sub]
  constructor
  · change Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        (thetaCuspReflectedSourceProduct (r / 2) t -
          thetaCuspReflectedSourceProduct (r / 2) (2 * t))) mu
    convert ht.sub h2t using 1
    funext r
    simp only [Pi.sub_apply, mul_sub]
  · change Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        (thetaCuspReflectedSourceProduct (r / 2) 0 -
          thetaCuspReflectedSourceProduct (r / 2) (3 * t))) mu
    convert h0.sub h3t using 1
    funext r
    simp only [Pi.sub_apply, mul_sub]

private theorem integral_thetaCuspCenterMixedWeightedDrops
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedFirstDrop a t r) =
        thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t ∧
      (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedMiddleDrop a t r) =
        thetaCuspCenterMixedDensity a t -
          thetaCuspCenterMixedDensity a (2 * t) ∧
      (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedFullDrop a t r) =
        thetaCuspCenterMixedDensity a 0 -
          thetaCuspCenterMixedDensity a (3 * t) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have h0 : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) 0) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha 0
  have ht : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) t) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha t
  have h2t : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) (2 * t)) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha (2 * t)
  have h3t : Integrable (fun r : ℝ =>
      thetaCuspCenterMixedRadialWeight a r *
        thetaCuspReflectedSourceProduct (r / 2) (3 * t)) mu := by
    simpa [mu, IntegrableOn, thetaCuspCenterMixedRadialWeight,
      thetaCuspReflectedSourceProduct] using
      integrableOn_thetaCuspCenterMixedIntegrand ha0 ha (3 * t)
  have hfirst :
      (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedFirstDrop a t r) =
        thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a t := by
    rw [show thetaCuspCenterMixedWeightedFirstDrop a t = (fun r : ℝ =>
        thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) 0 -
          thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) t) by
      funext r
      unfold thetaCuspCenterMixedWeightedFirstDrop thetaCuspReflectedSourceFirstDrop
      ring]
    rw [integral_sub h0 ht]
    unfold thetaCuspCenterMixedDensity
    simp only [mu, thetaCuspCenterMixedRadialWeight, thetaCuspReflectedSourceProduct]
  have hmiddle :
      (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedMiddleDrop a t r) =
        thetaCuspCenterMixedDensity a t - thetaCuspCenterMixedDensity a (2 * t) := by
    rw [show thetaCuspCenterMixedWeightedMiddleDrop a t = (fun r : ℝ =>
        thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) t -
          thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) (2 * t)) by
      funext r
      unfold thetaCuspCenterMixedWeightedMiddleDrop thetaCuspReflectedSourceMiddleDrop
      ring]
    rw [integral_sub ht h2t]
    unfold thetaCuspCenterMixedDensity
    simp only [mu, thetaCuspCenterMixedRadialWeight, thetaCuspReflectedSourceProduct]
  have hfull :
      (∫ r : ℝ in Ioi 0, thetaCuspCenterMixedWeightedFullDrop a t r) =
        thetaCuspCenterMixedDensity a 0 - thetaCuspCenterMixedDensity a (3 * t) := by
    rw [show thetaCuspCenterMixedWeightedFullDrop a t = (fun r : ℝ =>
        thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) 0 -
          thetaCuspCenterMixedRadialWeight a r *
            thetaCuspReflectedSourceProduct (r / 2) (3 * t)) by
      funext r
      unfold thetaCuspCenterMixedWeightedFullDrop thetaCuspReflectedSourceFullDrop
      ring]
    rw [integral_sub h0 h3t]
    unfold thetaCuspCenterMixedDensity
    simp only [mu, thetaCuspCenterMixedRadialWeight, thetaCuspReflectedSourceProduct]
  exact ⟨hfirst, hmiddle, hfull⟩

/-- **Exact continuum Ptolemy polarization.**  Product-space integration of the radial
polarization kernel is twice the reflection-odd wall of the actual center mixture. -/
theorem integral_thetaCuspCenterMixedPtolemyPolarizationKernel
    {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) (t : ℝ) :
    (∫ z : ℝ × ℝ,
        thetaCuspCenterMixedPtolemyPolarizationKernel a t z
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      2 * thetaCuspCenterMixedOddParityWall a t := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let A := thetaCuspCenterMixedWeightedFirstDrop a t
  let B := thetaCuspCenterMixedWeightedMiddleDrop a t
  let T := thetaCuspCenterMixedWeightedFullDrop a t
  obtain ⟨hA, hB, hT⟩ :=
    integrable_thetaCuspCenterMixedWeightedDrops ha0 ha t
  have hAT : Integrable (fun z : ℝ × ℝ => A z.1 * T z.2) (mu.prod mu) :=
    hA.mul_prod hT
  have hTA : Integrable (fun z : ℝ × ℝ => A z.2 * T z.1) (mu.prod mu) := by
    simpa only [mul_comm] using hT.mul_prod hA
  have hBB : Integrable (fun z : ℝ × ℝ => 2 * B z.1 * B z.2) (mu.prod mu) := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (hB.mul_prod hB).const_mul 2
  obtain ⟨hAint, hBint, hTint⟩ :=
    integral_thetaCuspCenterMixedWeightedDrops ha0 ha t
  let AT : ℝ × ℝ → ℝ := fun z => A z.1 * T z.2
  let TA : ℝ × ℝ → ℝ := fun z => A z.2 * T z.1
  let BB : ℝ × ℝ → ℝ := fun z => 2 * B z.1 * B z.2
  change (∫ z : ℝ × ℝ, (AT + TA - BB) z ∂mu.prod mu) = _
  have hAT' : Integrable AT (mu.prod mu) := hAT
  have hTA' : Integrable TA (mu.prod mu) := hTA
  have hBB' : Integrable BB (mu.prod mu) := hBB
  have hTAint : (∫ z : ℝ × ℝ, A z.2 * T z.1 ∂mu.prod mu) =
      (∫ r, T r ∂mu) * ∫ r, A r ∂mu := by
    simpa only [mul_comm] using integral_prod_mul T A
  rw [integral_sub' (hAT'.add hTA') hBB', integral_add' hAT' hTA']
  dsimp only [AT, TA, BB]
  rw [integral_prod_mul A T, hTAint,
    show (∫ z : ℝ × ℝ, 2 * B z.1 * B z.2 ∂mu.prod mu) =
        2 * ((∫ r, B r ∂mu) * ∫ r, B r ∂mu) by
      calc
        (∫ z : ℝ × ℝ, 2 * B z.1 * B z.2 ∂mu.prod mu) =
            ∫ z : ℝ × ℝ, 2 * (B z.1 * B z.2) ∂mu.prod mu := by
              congr 1
              funext z
              ring
        _ = 2 * ∫ z : ℝ × ℝ, B z.1 * B z.2 ∂mu.prod mu :=
          integral_const_mul 2 (fun z : ℝ × ℝ => B z.1 * B z.2)
        _ = 2 * ((∫ r, B r ∂mu) * ∫ r, B r ∂mu) := by
          rw [integral_prod_mul (μ := mu) (ν := mu) B B]]
  rw [hAint, hBint, hTint]
  unfold thetaCuspCenterMixedOddParityWall toeplitzFourOddParityWall
  ring

/-- Fibrewise Ptolemy positivity passes through the physical radial mixture. -/
theorem thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t)
    (hsource : ∀ u : ℝ, 0 < u →
      0 ≤ thetaCuspReflectedSourceOddParityWall u t) :
    0 ≤ thetaCuspCenterMixedOddParityWall a t := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  have hkernel : ∀ᵐ z : ℝ × ℝ ∂mu.prod mu,
      0 ≤ thetaCuspCenterMixedPtolemyPolarizationKernel a t z := by
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with z hz
    have hr : 0 < z.1 := hz.1
    have hs : 0 < z.2 := hz.2
    have hwr : 0 < thetaCuspCenterMixedRadialWeight a z.1 := by
      exact mul_pos hr (Real.sinh_pos_iff.mpr (mul_pos ha0 hr))
    have hws : 0 < thetaCuspCenterMixedRadialWeight a z.2 := by
      exact mul_pos hs (Real.sinh_pos_iff.mpr (mul_pos ha0 hs))
    have hpol := thetaCuspReflectedSourcePtolemyPolarization_nonneg
      (z.1 / 2) (z.2 / 2) ht
        (hsource _ (half_pos hr)) (hsource _ (half_pos hs))
    rw [show thetaCuspCenterMixedPtolemyPolarizationKernel a t z =
        thetaCuspCenterMixedRadialWeight a z.1 *
            thetaCuspCenterMixedRadialWeight a z.2 *
          thetaCuspReflectedSourcePtolemyPolarization (z.1 / 2) (z.2 / 2) t by
      unfold thetaCuspCenterMixedPtolemyPolarizationKernel
        thetaCuspCenterMixedWeightedFirstDrop thetaCuspCenterMixedWeightedMiddleDrop
        thetaCuspCenterMixedWeightedFullDrop
        thetaCuspReflectedSourcePtolemyPolarization
      ring]
    exact mul_nonneg (mul_nonneg hwr.le hws.le) hpol
  have hint :
      0 ≤ ∫ z : ℝ × ℝ,
        thetaCuspCenterMixedPtolemyPolarizationKernel a t z ∂mu.prod mu :=
    integral_nonneg_of_ae hkernel
  rw [integral_thetaCuspCenterMixedPtolemyPolarizationKernel ha0.le ha t] at hint
  linarith

/-- **Failure descends to a source fibre.**  Positive radial mixing cannot create the first
equispaced Ptolemy defect: every negative mixed odd wall is inherited from at least one literal
completed-source reflected fibre. -/
theorem exists_thetaCuspReflectedSourceOddParityWall_neg_of_centerMixed_neg
    {a t : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) (ht : 0 < t)
    (hneg : thetaCuspCenterMixedOddParityWall a t < 0) :
    ∃ u : ℝ, 0 < u ∧ thetaCuspReflectedSourceOddParityWall u t < 0 := by
  by_contra h
  have hsource : ∀ u : ℝ, 0 < u →
      0 ≤ thetaCuspReflectedSourceOddParityWall u t := by
    intro u hu
    exact le_of_not_gt (fun hwall => h ⟨u, hu, hwall⟩)
  exact (not_lt_of_ge
    (thetaCuspCenterMixedOddParityWall_nonneg_of_sourceFibres ha0 ha ht hsource)) hneg

end

end RHTower
