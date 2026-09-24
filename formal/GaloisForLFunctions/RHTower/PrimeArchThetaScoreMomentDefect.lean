import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence

/-!
# Exact defect retained by the theta score moment recurrence

The all-order moment upper bound drops a positive integral. Here its defect is
identified exactly and bounded below by a weighted square on the actual source.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

/-- The score certificate keeps at least the square used to complete its
affine first-atom lower bound. -/
theorem thetaCuspBornWitten_scoreDefect_ge_square
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (x - 1) ^ (2 : ℕ) ≤
      1 + 32 * x * thetaCuspBornWittenSuperpotential n x -
        303 * x ^ (2 : ℕ) := by
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
  nlinarith

/-- The gap in every atom's moment recurrence is exactly a weighted score
defect, not an unspecified strictness term. -/
theorem thetaCuspMorseBornMoment_scoreGap_eq_integral
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    (32 * (j : ℝ) + 17) * thetaCuspMorseBornMoment j n -
        303 * thetaCuspMorseBornMoment (j + 1) n =
      ∫ x : ℝ in Ioi 0,
        x ^ (2 * j) *
          (1 + 32 * x * thetaCuspBornWittenSuperpotential n x -
            303 * x ^ (2 : ℕ)) *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let χ : ℝ → ℝ := fun x => thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)
  let W : ℝ → ℝ := thetaCuspBornWittenSuperpotential n
  let F₀ : ℝ → ℝ := fun x => x ^ (2 * j) * χ x
  let F₁ : ℝ → ℝ := fun x => x ^ (2 * (j + 1)) * χ x
  let Fw : ℝ → ℝ := fun x => x ^ (2 * j + 1) * W x * χ x
  have h0 : Integrable F₀ μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) hn
  have h1 : Integrable F₁ μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * (j + 1)) hn
  have hw : Integrable Fw μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) (Ioi 0)
    simpa only [W, χ] using
      integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
        (2 * j + 1) hn
  have hfun :
      (fun x : ℝ => x ^ (2 * j) *
        (1 + 32 * x * W x - 303 * x ^ (2 : ℕ)) * χ x) =
      F₀ + (32 : ℝ) • Fw - (303 : ℝ) • F₁ := by
    funext x
    simp only [F₀, F₁, Fw, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, pow_add]
    ring
  have hintegral :
      (∫ x : ℝ in Ioi 0,
        x ^ (2 * j) * (1 + 32 * x * W x - 303 * x ^ (2 : ℕ)) * χ x) =
      (∫ x, F₀ x ∂μ) + 32 * (∫ x, Fw x ∂μ) -
        303 * (∫ x, F₁ x ∂μ) := by
    rw [hfun]
    have hsw : Integrable ((32 : ℝ) • Fw) μ := Integrable.smul (32 : ℝ) hw
    have hs1 : Integrable ((303 : ℝ) • F₁) μ := Integrable.smul (303 : ℝ) h1
    rw [integral_sub' (h0.add hsw) hs1]
    simp only [Pi.add_apply]
    rw [integral_add h0 hsw]
    simp only [Pi.smul_apply]
    rw [integral_smul, integral_smul]
    simp only [smul_eq_mul]
  have hward := thetaCuspBornWittenSuperpotentialMoment_eq_morseBornMoment j hn
  change (∫ x, Fw x ∂μ) =
    (((2 * j + 1 : ℕ) : ℝ) / 2) * thetaCuspMorseBornMoment j n at hward
  have hM₀ : (∫ x, F₀ x ∂μ) = thetaCuspMorseBornMoment j n := by
    simpa only [F₀, χ, μ] using
      (thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq j n).symm
  have hM₁ : (∫ x, F₁ x ∂μ) = thetaCuspMorseBornMoment (j + 1) n := by
    simpa only [F₁, χ, μ] using
      (thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq (j + 1) n).symm
  rw [hintegral, hM₀, hM₁, hward]
  push_cast
  ring

/-- The recurrence defect retains an explicit weighted square of the genuine
theta-atom position. It can be lower-bounded from source mass on any window
away from `x=1`. -/
theorem thetaCuspMorseBornMoment_scoreGap_ge_square
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * (x - 1) ^ (2 : ℕ) *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) ≤
      (32 * (j : ℝ) + 17) * thetaCuspMorseBornMoment j n -
        303 * thetaCuspMorseBornMoment (j + 1) n := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let χ : ℝ → ℝ := fun x => thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)
  let W : ℝ → ℝ := thetaCuspBornWittenSuperpotential n
  have h0 : Integrable (fun x : ℝ => x ^ (2 * j) * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) hn
  have hodd : Integrable (fun x : ℝ => x ^ (2 * j + 1) * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j + 1) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j + 1) hn
  have h1 : Integrable (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) (Ioi 0)
    simpa only [χ] using
      integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * (j + 1)) hn
  have hw : Integrable
      (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) μ := by
    change IntegrableOn (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) (Ioi 0)
    simpa only [W, χ] using
      integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
        (2 * j + 1) hn
  have hsqFun :
      (fun x : ℝ => x ^ (2 * j) * (x - 1) ^ (2 : ℕ) * χ x) =
      (fun x => x ^ (2 * (j + 1)) * χ x) -
        (fun x => 2 * (x ^ (2 * j + 1) * χ x)) +
          (fun x => x ^ (2 * j) * χ x) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, pow_add]
    ring
  have hsq : Integrable
      (fun x : ℝ => x ^ (2 * j) * (x - 1) ^ (2 : ℕ) * χ x) μ := by
    rw [hsqFun]
    exact (h1.sub (hodd.const_mul 2)).add h0
  have hdefFun :
      (fun x : ℝ => x ^ (2 * j) *
        (1 + 32 * x * W x - 303 * x ^ (2 : ℕ)) * χ x) =
      (fun x => x ^ (2 * j) * χ x) +
        (fun x => 32 * (x ^ (2 * j + 1) * W x * χ x)) -
          (fun x => 303 * (x ^ (2 * (j + 1)) * χ x)) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, pow_add]
    ring
  have hdef : Integrable
      (fun x : ℝ => x ^ (2 * j) *
        (1 + 32 * x * W x - 303 * x ^ (2 : ℕ)) * χ x) μ := by
    rw [hdefFun]
    exact (h0.add (hw.const_mul 32)).sub (h1.const_mul 303)
  have hpoint : ∀ᵐ x : ℝ ∂μ,
      x ^ (2 * j) * (x - 1) ^ (2 : ℕ) * χ x ≤
        x ^ (2 * j) *
          (1 + 32 * x * W x - 303 * x ^ (2 : ℕ)) * χ x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hs := thetaCuspBornWitten_scoreDefect_ge_square hn hx.le
    have hweight : 0 ≤ x ^ (2 * j) * χ x := by
      dsimp only [χ]
      exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)
    have hscaled := mul_le_mul_of_nonneg_right hs hweight
    dsimp only [W]
    nlinarith
  have hint := integral_mono_ae hsq hdef hpoint
  calc
    (∫ x : ℝ in Ioi 0,
      x ^ (2 * j) * (x - 1) ^ (2 : ℕ) *
        thetaCuspBornWittenAmplitude n x ^ (2 : ℕ)) ≤
      ∫ x : ℝ in Ioi 0,
        x ^ (2 * j) *
          (1 + 32 * x * thetaCuspBornWittenSuperpotential n x -
            303 * x ^ (2 : ℕ)) *
          thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) := by
            simpa only [μ, χ, W] using hint
    _ = _ := (thetaCuspMorseBornMoment_scoreGap_eq_integral j hn).symm

/-- The complete theta moment recurrence retains, at minimum, the weighted
square from its dominant atom. This supplies a quantitative source margin
without estimating any later atom. -/
theorem thetaCuspRawEvenMoment_scoreGap_ge_firstAtomSquare (j : ℕ) :
    2 * Real.pi *
        (∫ x : ℝ in Ioi 0,
          x ^ (2 * j) * (x - 1) ^ (2 : ℕ) *
            thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) ≤
      (32 * (j : ℝ) + 17) * thetaCuspRawEvenMoment j -
        303 * thetaCuspRawEvenMoment (j + 1) := by
  let c : ℝ := 32 * (j : ℝ) + 17
  let D : ℕ → ℝ := fun n =>
    c * thetaCuspAtomRawEvenMoment j n -
      303 * thetaCuspAtomRawEvenMoment (j + 1) n
  have hsum (k : ℕ) : Summable (fun n : ℕ => thetaCuspAtomRawEvenMoment k n) := by
    by_contra h
    have hz : (∑' n : ℕ, thetaCuspAtomRawEvenMoment k n) = 0 :=
      tsum_eq_zero_of_not_summable h
    have heq := thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment k
    have hp := thetaCuspRawEvenMoment_pos k
    linarith
  have hDsum : Summable D :=
    ((hsum j).mul_left c).sub ((hsum (j + 1)).mul_left 303)
  have hDnonneg (n : ℕ) : 0 ≤ D n := by
    cases n with
    | zero => simp [D]
    | succ n =>
        have h := thetaCuspAtomRawEvenMoment_succ_le_score j (Nat.succ_pos n)
        dsimp only [D, c]
        linarith
  have hfirst : D 1 ≤ ∑' n : ℕ, D n :=
    hDsum.le_tsum 1 (fun n _ => hDnonneg n)
  have hDvalue : (∑' n : ℕ, D n) =
      c * thetaCuspRawEvenMoment j -
        303 * thetaCuspRawEvenMoment (j + 1) := by
    dsimp only [D]
    rw [Summable.tsum_sub ((hsum j).mul_left c)
      ((hsum (j + 1)).mul_left 303), tsum_mul_left, tsum_mul_left,
      ← thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment j,
      ← thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment (j + 1)]
  have hsq := thetaCuspMorseBornMoment_scoreGap_ge_square j
    (n := 1) (by norm_num)
  have hscale : 0 ≤ 2 * Real.pi := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsq hscale
  have hfirstValue :
      2 * Real.pi *
        (∫ x : ℝ in Ioi 0,
          x ^ (2 * j) * (x - 1) ^ (2 : ℕ) *
            thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) ≤ D 1 := by
    dsimp only [D]
    rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
      thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
    dsimp only [c]
    nlinarith
  exact hfirstValue.trans (hfirst.trans (by simpa only [c] using hDvalue.le))

end
end RHTower
