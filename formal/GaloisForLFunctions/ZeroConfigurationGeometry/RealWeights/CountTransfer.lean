import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.CountMajorant
import GaloisForLFunctions.ZeroConfigurationGeometry.RealWeights.IntervalCount

/-!
# Local weighted counts from a source envelope

An interval count for a finite source passes through a nonnegative
integrable envelope. Integrating diagonal images then transfers the count
to positive on-line weights, with explicit enlargement and tail losses.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23

/-- A nonnegative envelope with an interval mass bound transfers that bound to
positive on-line camera weights. The only losses are central-mass normalization,
the enlargement of the interval, and the integrated image tail. -/
theorem weighted_count_le_of_envelope {w : ℂ → ℝ}
    (hw0 : ∀ z, 0 ≤ w z) (hline : ∀ z, w z ≠ 0 → z.re = 1 / 2)
    (hw : Summable fun z => |w z| / (1 + Complex.normSq (gammaOf z)))
    {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) (hbc : HasCompactSupport b)
    {x y R : ℝ} (hxy : x ≤ y) (hR : 0 ≤ R)
    (hP : 0 < ∫ v in (-R)..R, ‖paperFT b v‖ ^ 2)
    {E : ℝ → ℝ} (hEi : Integrable E) (hE : ∀ v, 0 ≤ E v)
    (p : Finset ℂ) (m : ℂ → ℝ) {D C B : ℝ}
    (hcount : ∀ l r : ℝ, l ≤ r → ∀ s : Finset ℂ, s ⊆ p →
      (∀ z ∈ s, z.im ∈ Icc l r) → (∑ z ∈ s, m z) ≤ D * (r - l) + C)
    (hupper : ∀ X ∈ Icc (x - R) (y + R),
      (weightedImage (fun z => (w z : ℂ)) (localWindow X b) (localWindow X b)).re ≤
        (∑ z ∈ p, m z * E (z.im - X)) + B)
    (s : Finset ℂ) (hs : ∀ z ∈ s, z.im ∈ Icc x y) :
    (∑ z ∈ s, w z) ≤
      ((D * (y - x + 2 * R) + C) * (∫ v, E v) + B * (y - x + 2 * R)) /
        (∫ v in (-R)..R, ‖paperFT b v‖ ^ 2) := by
  have hab : x - R ≤ y + R := by linarith only [hxy, hR]
  have hterm (z : ℂ) : IntervalIntegrable (fun X => m z * E (z.im - X)) volume
      (x - R) (y + R) := by
    have hh := (hEi.intervalIntegrable (a := z.im - (x - R)) (b := z.im - (y + R))).comp_sub_left z.im
    rw [show z.im - (z.im - (x - R)) = x - R by ring,
      show z.im - (z.im - (y + R)) = y + R by ring] at hh
    exact hh.const_mul (m z)
  have hsum : IntervalIntegrable (fun X => ∑ z ∈ p, m z * E (z.im - X)) volume
      (x - R) (y + R) :=
    ⟨integrable_finsetSum p (fun z _ => (hterm z).1),
      integrable_finsetSum p (fun z _ => (hterm z).2)⟩
  have hmain := weighted_count_le_integrated_image_bound hw0 hline hw hb hbc hxy hR hP
    (hsum.add intervalIntegrable_const) hupper s hs
  refine hmain.trans (div_le_div_of_nonneg_right ?_ hP.le)
  rw [intervalIntegral.integral_add hsum intervalIntegrable_const,
    intervalIntegral.integral_finsetSum (fun z _ => hterm z), intervalIntegral.integral_const]
  simp_rw [intervalIntegral.integral_const_mul]
  have hc := finite_interval_convolution_le_of_count p (fun z => z.im) m hEi hE hab hcount
  have hlen : (y + R) - (x - R) = y - x + 2 * R := by ring
  rw [hlen] at hc
  simp only [smul_eq_mul]
  calc _ ≤ (D * (y - x + 2 * R) + C) * (∫ v, E v) + ((y + R) - (x - R)) * B :=
      add_le_add hc le_rfl
    _ = _ := by ring

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.weighted_count_le_of_envelope
