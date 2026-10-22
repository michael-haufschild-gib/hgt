import GaloisForLFunctions.RHTower.WallThresholdDatum
import GaloisForLFunctions.RHTower.Suzuki.SuzukiWallTailSplit

/-!
# The forced profile on a terminal ray

Splitting the variation-of-constants profile at the frequency threshold separates the two mechanisms:
what was accumulated below the threshold is a fixed vector propagated onward, and what is accumulated
above it is the moving tail that the integrations by parts act on.  On the ray,

`‖profile‖² ≤ 4(‖propagated datum‖² + ‖moving tail‖²)`,

and the two summands are estimated by entirely different means — the first by the ray decay of the
transport, the second by the four-term expansion.

The splitting needs the transported source to be interval integrable, which is not an extra
hypothesis: the joint integrability already established for the Fubini of the block source gives it
by integrating out the position.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
/-- **The transported block source is interval integrable.** -/
theorem intervalIntegrable_stripPropagatorInv_blockSource
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      volume a b := by
  have hkey : ∀ u v : ℝ, IntegrableOn
      (fun t : ℝ => stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (blockSource g m t))
      (Ioc u v) := by
    intro u v
    have hjoint := integrable_uncurry_wallPhaseMap_apply (T := T) hEdiff hE hEne hσ0 hσ1 hg
      (a := u) (b := v)
    have hright := hjoint.integral_prod_right
    have hscaled : IntegrableOn
        (fun t : ℝ => (-(Complex.I) / 2 : ℂ) • ∫ L in Icc m (m + 1), wallPhaseMap E T σ L t (g L))
        (Ioc u v) := Integrable.smul _ hright
    refine hscaled.congr (Filter.Eventually.of_forall fun t => ?_)
    exact (stripPropagatorInv_blockSource (T := T) hg t).symm
  exact ⟨hkey a b, hkey b a⟩

omit [Nontrivial X] in
/-- **The forced profile on the terminal ray splits into the propagated datum and the moving
tail.** -/
theorem lintegral_sq_forcedProfile_region_le
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (c : X)
    {A : Set ℝ} (hA : MeasurableSet A) (Y : ℝ) :
    (∫⁻ x in A, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
      ≤ 4 * ((∫⁻ x in A, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2)
          + ∫⁻ x in A, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
                  (blockSource g m t))‖ₑ ^ 2) := by
  have hpair : ∀ u v : ℝ≥0∞, (u + v) ^ 2 ≤ 4 * (u ^ 2 + v ^ 2) := by
    intro u v
    have h1 : u + v ≤ 2 * max u v :=
      (add_le_add (le_max_left u v) (le_max_right u v)).trans (by rw [two_mul])
    have h2 : max u v ^ 2 ≤ u ^ 2 + v ^ 2 := by
      rcases max_choice u v with h | h <;> rw [h]
      · exact le_self_add
      · exact le_add_self
    calc (u + v) ^ 2 ≤ (2 * max u v) ^ 2 := pow_le_pow_left' h1 2
      _ = 4 * max u v ^ 2 := by ring
      _ ≤ 4 * (u ^ 2 + v ^ 2) := mul_le_mul' le_rfl h2
  have hpt : ∀ x ∈ A, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2
      ≤ 4 * (‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2
          + ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
                  (blockSource g m t))‖ₑ ^ 2) := by
    intro x _
    have hsplit := forcedProfile_split (E := E) (T := T) (blockSource g m) c
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg 0 Y)
      (intervalIntegrable_stripPropagatorInv_blockSource hEdiff hE hEne hσ0 hσ1 hg Y x)
    rw [hsplit]
    exact le_trans (pow_le_pow_left' (enorm_add_le _ _) 2) (hpair _ _)
  have hmeasA : AEMeasurable (fun x : ℝ =>
      ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
        (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2) (volume.restrict (A)) := by
    have hcont := continuous_stripPropagator_line (T := T) hEdiff hE hEne hσ0 hσ1
    exact ((hcont.aestronglyMeasurable).apply_continuousLinearMap _).enorm.pow_const 2
  refine le_trans (setLIntegral_mono' hA hpt) ?_
  rw [lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  rw [lintegral_add_left' hmeasA]

omit [Nontrivial X] in
/-- **The forced profile on the terminal ray splits into the propagated datum and the moving
tail.** -/
theorem lintegral_sq_forcedProfile_ray_le
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (c : X) :
    (∫⁻ x in Ioi Y, ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
      ≤ 4 * ((∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdDatum E T (blockSource g m) c σ Y)‖ₑ ^ 2)
          + ∫⁻ x in Ioi Y, ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (∫ t in Y..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
                  (blockSource g m t))‖ₑ ^ 2) :=
  lintegral_sq_forcedProfile_region_le hEdiff hE hEne hσ0 hσ1 hg c measurableSet_Ioi Y

omit [Nontrivial X] in
/-- **The forced profile on the inward ray**, split at the reflected threshold. -/
theorem lintegral_sq_forcedProfile_negRay_le
    (hEdiff : DifferentiableOn ℂ E (imStrip (-1) 1))
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z)
    (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    {g : ℝ → X} {m Y : ℝ} (hg : IntegrableOn g (Icc m (m + 1))) (c : X) :
    (∫⁻ x in Iio (-Y), ‖forcedProfile E T (blockSource g m) c σ x‖ₑ ^ 2)
      ≤ 4 * ((∫⁻ x in Iio (-Y), ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (thresholdDatum E T (blockSource g m) c σ (-Y))‖ₑ ^ 2)
          + ∫⁻ x in Iio (-Y), ‖stripPropagator E T ((x : ℂ) + (σ : ℂ) * Complex.I)
                (∫ t in (-Y)..x, stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
                  (blockSource g m t))‖ₑ ^ 2) :=
  lintegral_sq_forcedProfile_region_le hEdiff hE hEne hσ0 hσ1 hg c measurableSet_Iio (-Y)

end GaloisForLFunctions.RHTower
