import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenCurvatureGap
import GaloisForLFunctions.RHTower.PrimeArchThetaAtomLikelihoodRatio

/-!
# A score certificate for every theta-atom moment

The exact first-atom curvature gap and atom-index score order combine into a
quadratic pointwise certificate. The Born--Witten Ward identity then turns it
into an all-order upper recurrence for source position moments, including the
eighth moment in the K-RVM four-moment gate.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- Every positive theta atom inherits the dominant atom's quadratic score coercivity. -/
theorem thetaCuspBornWitten_quadraticMomentCertificate
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (303 : ℝ) * x ^ (2 : ℕ) ≤
      1 + 32 * x * thetaCuspBornWittenSuperpotential n x := by
  have hW₁ := thetaCuspFirstBornWittenSuperpotential_affine_lower hx
  have hindex : thetaCuspBornWittenSuperpotential 1 x ≤
      thetaCuspBornWittenSuperpotential n x :=
    thetaCuspBornWittenSuperpotential_mono_nat
      (by norm_num : 0 < 1) (Nat.one_le_iff_ne_zero.mpr hn.ne') hx
  have hW : -(1 / 16 : ℝ) + (19 / 2 : ℝ) * x ≤
      thetaCuspBornWittenSuperpotential n x := hW₁.trans hindex
  have hmul : (32 * x) * (-(1 / 16 : ℝ) + (19 / 2 : ℝ) * x) ≤
      (32 * x) * thetaCuspBornWittenSuperpotential n x :=
    mul_le_mul_of_nonneg_left hW (by positivity)
  nlinarith [sq_nonneg (x - 1)]

/-- The score certificate yields a source-specific upper ratio at every even
position-moment level, without numerical enclosures. -/
theorem thetaCuspMorseBornMoment_succ_le_score
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    (303 : ℝ) * thetaCuspMorseBornMoment (j + 1) n ≤
      (32 * (j : ℝ) + 17) * thetaCuspMorseBornMoment j n := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let χ : ℝ → ℝ := fun x => thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)
  let W : ℝ → ℝ := thetaCuspBornWittenSuperpotential n
  let A : ℝ → ℝ := fun x => 303 * (x ^ (2 * (j + 1)) * χ x)
  let B : ℝ → ℝ := fun x =>
    x ^ (2 * j) * χ x +
      32 * (x ^ (2 * j + 1) * W x * χ x)
  have h0 : Integrable (fun x : ℝ => x ^ (2 * j) * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) hn
  have h1 : Integrable (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * (j + 1)) hn
  have hW : Integrable
      (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) (Ioi 0)
    simpa only [W, χ] using
      integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
        (2 * j + 1) hn
  have hA : Integrable A μ := h1.const_mul 303
  have hB : Integrable B μ := h0.add (hW.const_mul 32)
  have hpoint : ∀ᵐ x : ℝ ∂μ, A x ≤ B x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hcert := thetaCuspBornWitten_quadraticMomentCertificate hn hx.le
    have hweight : 0 ≤ x ^ (2 * j) * χ x := by
      dsimp only [χ]
      exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_right hcert hweight
    have hAform : A x =
        ((303 : ℝ) * x ^ (2 : ℕ)) * (x ^ (2 * j) * χ x) := by
      dsimp only [A]
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add]
      ring
    have hBform : B x =
        (1 + 32 * x * W x) * (x ^ (2 * j) * χ x) := by
      dsimp only [B]
      rw [pow_add]
      simp only [pow_one]
      ring
    rw [hAform, hBform]
    exact hscaled
  have hint : ∫ x, A x ∂μ ≤ ∫ x, B x ∂μ :=
    integral_mono_ae hA hB hpoint
  have hleft : (∫ x, A x ∂μ) =
      303 * thetaCuspMorseBornMoment (j + 1) n := by
    rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
    exact integral_const_mul 303 _
  have hright : (∫ x, B x ∂μ) =
      thetaCuspMorseBornMoment j n +
        32 * thetaCuspBornWittenSuperpotentialMoment j n := by
    rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
    rw [thetaCuspBornWittenSuperpotentialMoment]
    dsimp only [B, χ, W]
    rw [integral_add h0 (hW.const_mul 32), integral_const_mul]
  rw [hleft, hright] at hint
  rw [thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment j hn] at hint
  push_cast at hint ⊢
  nlinarith

/-- Atomwise recurrence in the raw moment coordinates used by the Hankel gate. -/
theorem thetaCuspAtomRawEvenMoment_succ_le_score
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    (303 : ℝ) * thetaCuspAtomRawEvenMoment (j + 1) n ≤
      (32 * (j : ℝ) + 17) * thetaCuspAtomRawEvenMoment j n := by
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
  have h := thetaCuspMorseBornMoment_succ_le_score j hn
  have hscale : 0 ≤ 2 * Real.pi := by positivity
  have hh := mul_le_mul_of_nonneg_left h hscale
  nlinarith

private theorem summable_thetaCuspAtomRawEvenMoment_for_score (j : ℕ) :
    Summable (fun n : ℕ => thetaCuspAtomRawEvenMoment j n) := by
  by_contra h
  have hz : (∑' n : ℕ, thetaCuspAtomRawEvenMoment j n) = 0 :=
    tsum_eq_zero_of_not_summable h
  have heq := thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment j
  have hp := thetaCuspRawEvenMoment_pos j
  linarith

/-- All-order raw theta moment recurrence. In particular `j=3` bounds the
eighth position moment entering the first open K-RVM gate by its sixth moment. -/
theorem thetaCuspRawEvenMoment_succ_le_score (j : ℕ) :
    (303 : ℝ) * thetaCuspRawEvenMoment (j + 1) ≤
      (32 * (j : ℝ) + 17) * thetaCuspRawEvenMoment j := by
  have hterm (n : ℕ) :
      (303 : ℝ) * thetaCuspAtomRawEvenMoment (j + 1) n ≤
        (32 * (j : ℝ) + 17) * thetaCuspAtomRawEvenMoment j n := by
    cases n with
    | zero => simp
    | succ n => exact thetaCuspAtomRawEvenMoment_succ_le_score j (Nat.succ_pos n)
  have hleft := (summable_thetaCuspAtomRawEvenMoment_for_score (j + 1)).mul_left 303
  have hright := (summable_thetaCuspAtomRawEvenMoment_for_score j).mul_left
    (32 * (j : ℝ) + 17)
  have hsum := Summable.tsum_le_tsum hterm hleft hright
  simpa only [tsum_mul_left, ← thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment]
    using hsum

/-- The same recurrence in the normalized source coordinates of the gate. -/
theorem thetaCuspNormalizedEvenMoment_succ_le_score (j : ℕ) :
    (303 : ℝ) * thetaCuspNormalizedEvenMoment (j + 1) ≤
      (32 * (j : ℝ) + 17) * thetaCuspNormalizedEvenMoment j := by
  have h := thetaCuspRawEvenMoment_succ_le_score j
  have hden : 0 < thetaCuspRawEvenMoment 0 := thetaCuspRawEvenMoment_pos 0
  have hscaled := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hden.le)
  simp only [thetaCuspNormalizedEvenMoment, div_eq_mul_inv] at hscaled ⊢
  nlinarith

end
end RHTower
