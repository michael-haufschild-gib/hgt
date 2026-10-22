import GaloisForLFunctions.RHTower.TailMeasureLaplace
import GaloisForLFunctions.RHTower.HeadLaplaceEntire
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueEulerTransform
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTorqueTotalTransform

/-!
# The torque's one-sign tail as a Laplace carrier

Cutting the torque at a height past its last sign change turns it into a nonnegative density; the
reference exponential of abscissa `1/4` is added so the carrier certainly diverges on the left.  The
transform of the carrier is the continuation `(16)` with its head subtracted and the reference pole
restored, which is the identity Landau's theorem is applied to.
-/

open MeasureTheory Set
open scoped ENNReal
open GaloisForLFunctions.RHTower (laplaceReal laplaceMass complexLaplace IsAbscissa tailCarrier
  tailMeasure headLaplace)

noncomputable section

namespace RHTower

theorem continuous_suzukiFreeArchPositionTorque : Continuous suzukiFreeArchPositionTorque := by
  have h : suzukiFreeArchPositionTorque = fun L : ℝ =>
      -(2 * L / 9 - 8 / 27) * Real.exp (3 * L / 2) +
        (2 * L + 8) * Real.exp (-L / 2) +
        (2 * L / 9 + 8 / 27) * Real.exp (-3 * L / 2) +
        2 * L - 232 / 27 := by
    funext L
    exact suzukiFreeArchPositionTorque_closedForm L
  rw [h]
  fun_prop

theorem continuous_suzukiFreePositionTorque : Continuous suzukiFreePositionTorque := by
  have h : suzukiFreePositionTorque
      = fun L : ℝ => suzukiFreeArchPositionTorque L + suzukiFreePrimePositionTorque L := by
    funext L
    rw [suzukiFreePositionTorque]
  rw [h]
  exact continuous_suzukiFreeArchPositionTorque.add continuous_suzukiFreePrimePositionTorque

theorem integrableOn_suzukiFreeArchPositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun L : ℝ => suzukiFreeArchPositionTorque L * Real.exp (-σ * L)) (Ioi 0) := by
  have hcongr : (fun L : ℝ => suzukiFreeArchPositionTorque L * Real.exp (-σ * L))
      = fun L : ℝ =>
          (((-2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((3 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 : ℝ) * L + 8) * Real.exp ((-1 / 2 : ℝ) * L) * Real.exp (-σ * L)
            + ((2 / 9 : ℝ) * L + 8 / 27) * Real.exp ((-3 / 2 : ℝ) * L) * Real.exp (-σ * L))
          + ((2 : ℝ) * L + -(232 / 27)) * Real.exp ((0 : ℝ) * L) * Real.exp (-σ * L) := by
    funext L
    rw [suzukiFreeArchPositionTorque_closedForm]
    have e1 : Real.exp (3 * L / 2) = Real.exp ((3 / 2 : ℝ) * L) := by congr 1; ring
    have e2 : Real.exp (-L / 2) = Real.exp ((-1 / 2 : ℝ) * L) := by congr 1; ring
    have e3 : Real.exp (-3 * L / 2) = Real.exp ((-3 / 2 : ℝ) * L) := by congr 1; ring
    rw [e1, e2, e3, zero_mul, Real.exp_zero]
    ring
  rw [hcongr]
  exact (((integrableOn_affineExp (a := (-2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (3 / 2 : ℝ))
      (σ := σ) hσ).add
    (integrableOn_affineExp (a := (2 : ℝ)) (b := (8 : ℝ)) (c := (-1 / 2 : ℝ)) (σ := σ)
      (by linarith))).add
    (integrableOn_affineExp (a := (2 / 9 : ℝ)) (b := (8 / 27 : ℝ)) (c := (-3 / 2 : ℝ)) (σ := σ)
      (by linarith))).add
    (integrableOn_affineExp (a := (2 : ℝ)) (b := (-(232 / 27) : ℝ)) (c := (0 : ℝ)) (σ := σ)
      (by linarith))

theorem integrableOn_suzukiFreePositionTorque_mul_exp {σ : ℝ} (hσ : 3 / 2 < σ) :
    IntegrableOn (fun L : ℝ => suzukiFreePositionTorque L * Real.exp (-σ * L)) (Ioi 0) := by
  have h := (integrableOn_suzukiFreeArchPositionTorque_mul_exp hσ).add
    (integrableOn_suzukiFreePrimePositionTorque_mul_exp hσ)
  refine h.congr_fun (fun L _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [suzukiFreePositionTorque]
  ring

/-- Shifting the profile past the cut converts the tail integral into a full-ray integral. -/
theorem integral_shift_Ioi (f : ℝ → ℝ) (H : ℝ) :
    (∫ u in Ioi (0 : ℝ), f (H + u)) = ∫ L in Ioi H, f L := by
  have hmp : MeasurePreserving (fun u : ℝ => H + u) volume volume :=
    measurePreserving_add_left volume H
  have hemb : MeasurableEmbedding (fun u : ℝ => H + u) :=
    (Homeomorph.addLeft H).measurableEmbedding
  have hpre : (fun u : ℝ => H + u) ⁻¹' (Ioi H) = Ioi (0 : ℝ) := by
    ext u
    simp
  have h := hmp.setIntegral_preimage_emb hemb f (Ioi H)
  rw [hpre] at h
  exact h

theorem integrableOn_shift_Ioi {f : ℝ → ℝ} {H : ℝ} (hf : IntegrableOn f (Ioi H)) :
    IntegrableOn (fun u : ℝ => f (H + u)) (Ioi (0 : ℝ)) := by
  have hmp : MeasurePreserving (fun u : ℝ => H + u) volume volume :=
    measurePreserving_add_left volume H
  have hemb : MeasurableEmbedding (fun u : ℝ => H + u) :=
    (Homeomorph.addLeft H).measurableEmbedding
  have hpre : (fun u : ℝ => H + u) ⁻¹' (Ioi H) = Ioi (0 : ℝ) := by
    ext u
    simp
  have h := (hmp.integrableOn_comp_preimage hemb (f := f) (s := Ioi H)).mpr hf
  rwa [hpre] at h

/-- The tail piece of the carrier is integrable. -/
theorem integrableOn_tailPiece {g : ℝ → ℝ} {H σ : ℝ} (hH : 0 ≤ H)
    (hgi : IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * g (H + u)) (Ioi (0 : ℝ)) := by
  set F : ℝ → ℝ := fun L : ℝ => Real.exp (σ * H) * (g L * Real.exp (-σ * L)) with hFdef
  have hFint : IntegrableOn F (Ioi H) :=
    (hgi.mono_set (Ioi_subset_Ioi hH)).const_mul _
  have hshift := integrableOn_shift_Ioi hFint
  refine hshift.congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [hFdef]
  simp only
  rw [show Real.exp (σ * H) * (g (H + u) * Real.exp (-σ * (H + u)))
      = g (H + u) * (Real.exp (σ * H) * Real.exp (-σ * (H + u))) by ring,
    ← Real.exp_add, show σ * H + -σ * (H + u) = -σ * u by ring]
  ring

/-- The reference piece of the carrier is integrable. -/
theorem integrableOn_referencePiece {σ : ℝ} (hσ : 1 / 4 < σ) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * Real.exp (u / 4)) (Ioi (0 : ℝ)) := by
  have hr : (0 : ℝ) < σ - 1 / 4 := by linarith
  refine (integrableOn_exp_neg_linear hr).congr_fun (fun u _ => ?_) measurableSet_Ioi
  rw [← Real.exp_add]
  ring

theorem integrableOn_tailCarrier_mul_exp {g : ℝ → ℝ} {H σ : ℝ} (hH : 0 ≤ H) (hσ : 1 / 4 < σ)
    (hgi : IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => Real.exp (-σ * u) * tailCarrier g H u) (Ioi (0 : ℝ)) := by
  have h := (integrableOn_tailPiece hH hgi).add (integrableOn_referencePiece (σ := σ) hσ)
  refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [tailCarrier]
  ring

/-- **The tail transform is the profile transform with its head removed and the reference pole
restored.** -/
theorem laplaceReal_tailMeasure_eq {g : ℝ → ℝ} (hgc : Continuous g) {H σ : ℝ} (hH : 0 ≤ H)
    (hσ : 1 / 4 < σ) (hgi : IntegrableOn (fun L : ℝ => g L * Real.exp (-σ * L)) (Ioi 0))
    (hpos : ∀ u : ℝ, 0 < u → 0 ≤ g (H + u)) :
    laplaceReal (tailMeasure g H) σ
      = Real.exp (σ * H) * ((∫ L in Ioi (0 : ℝ), g L * Real.exp (-σ * L))
          - ∫ L in Ioc (0 : ℝ) H, g L * Real.exp (-σ * L))
        + 1 / (σ - 1 / 4) := by
  rw [GaloisForLFunctions.RHTower.laplaceReal_tailMeasure hgc.measurable hpos σ]
  have hsplit : (∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * tailCarrier g H u)
      = (∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * g (H + u))
        + ∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.exp (u / 4) := by
    rw [← integral_add (integrableOn_tailPiece hH hgi)
      (integrableOn_referencePiece (σ := σ) hσ)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [tailCarrier]
    ring
  rw [hsplit]
  congr 1
  · set F : ℝ → ℝ := fun L : ℝ => Real.exp (σ * H) * (g L * Real.exp (-σ * L)) with hFdef
    have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * g (H + u))
        = ∫ u in Ioi (0 : ℝ), F (H + u) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [hFdef]
      simp only
      rw [show Real.exp (σ * H) * (g (H + u) * Real.exp (-σ * (H + u)))
          = g (H + u) * (Real.exp (σ * H) * Real.exp (-σ * (H + u))) by ring,
        ← Real.exp_add, show σ * H + -σ * (H + u) = -σ * u by ring]
      ring
    rw [hcongr, integral_shift_Ioi F H, hFdef]
    rw [integral_const_mul]
    congr 1
    have hunion : Ioc (0 : ℝ) H ∪ Ioi H = Ioi (0 : ℝ) := Ioc_union_Ioi_eq_Ioi hH
    have hdisj : Disjoint (Ioc (0 : ℝ) H) (Ioi H) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd hx.2 (not_le.mpr hx')
    have h := setIntegral_union hdisj measurableSet_Ioi
      (hgi.mono_set (by rw [← hunion]; exact subset_union_left))
      (hgi.mono_set (by rw [← hunion]; exact subset_union_right))
    rw [hunion] at h
    rw [h]
    ring
  · have hr : (0 : ℝ) < σ - 1 / 4 := by linarith
    have hcongr : (∫ u in Ioi (0 : ℝ), Real.exp (-σ * u) * Real.exp (u / 4))
        = ∫ u in Ioi (0 : ℝ), Real.exp (-(σ - 1 / 4) * u) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hcongr, integral_exp_neg_linear hr]

end RHTower
