import GaloisForLFunctions.RHTower.FZZCigarParityGradeHermitianization
import GaloisForLFunctions.RHTower.FZZCigarParityMellinCharacterCrossingReflection

/-!
# Sharp Hermitian reflection-detector cone for FZZ Mellin carriers

Functional-equation reflection preserves the phase of the centered dyadic Mellin character and
inverts its radius.  This module classifies every fixed four-parameter Hermitian quadratic reporter
that separates all nonunit radial-phase carriers from their reciprocal-radius reflections.

For the block `[[a,b+ic],[b-ic,d]]`, universal separation holds exactly when

`d != 0` and `b^(2 : ℕ)+c^(2 : ℕ) <= d^(2 : ℕ)`.

This punctured Lorentz cone includes its nonzero lightlike boundary.  The exact reflected defect is

`(r-r⁻¹) * (d(r+r⁻¹)+2(bx-cy))`.

Inside the cone, Cauchy--Schwarz and the strict off-unit inequality `(r+r⁻¹)^(2 : ℕ)>4` forbid phase
cancellation.  Outside it, the proof constructs an explicit unit phase and positive nonunit radius
where cancellation occurs.  Thus chiral-only reporters are necessarily phase-blind, whereas every
cone reporter gives a pointwise critical-line detector on the literal FZZ Mellin carrier.  Matching
one such reporter on all parity-Mellin divisor modes is equivalent to RH; the missing burden remains
to derive that matching from interacting FZZ/GFZZ dynamics.

Targeted searches of FZZ, Mellin-reflection, Hermitian-observable, and Krein literature located no
source-specific cone classification or sharp outside-cone witnesses of this form.
-/

open Complex

namespace RHTower

noncomputable section

/-- Carrier with positive radius `r` and real phase coordinates `(x,y)`. -/
def fzzCigarParityRadialPhaseCarrier (r x y : ℝ) : ℂ × ℂ :=
  (1, ((r * x : ℝ) : ℂ) + Complex.I * (r * y : ℂ))

/-- A fixed Hermitian reporter separates every nonunit radius from its reciprocal at every unit
phase. -/
def FZZCigarParityHermitianUniversalRadialReflectionSeparating
    (a b c d : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → r ≠ 1 → ∀ x y : ℝ, x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 →
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityRadialPhaseCarrier r x y) ≠
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityRadialPhaseCarrier r⁻¹ x y)

/-- Exact radial-reflection defect of an arbitrary Hermitian reporter.  The coefficient `a` cancels
and phase dependence is confined to the linear functional `b*x-c*y`. -/
theorem fzzCigarParityHermitianRadialPhase_reflection_sub
    (a b c d r x y : ℝ) (hphase : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1) :
    fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityRadialPhaseCarrier r x y) -
      fzzCigarParityHermitianQuadraticObservable a b c d
        (fzzCigarParityRadialPhaseCarrier r⁻¹ x y) =
      (((r - r⁻¹) *
        (d * (r + r⁻¹) + 2 * (b * x - c * y)) : ℝ) : ℂ) := by
  simp [fzzCigarParityHermitianQuadraticObservable,
    fzzCigarParityRadialPhaseCarrier]
  ring_nf
  rw [Complex.I_sq]
  have hphaseC : (x : ℂ) ^ (2 : ℕ) + (y : ℂ) ^ (2 : ℕ) = 1 := by
    exact_mod_cast hphase
  linear_combination
    (((r : ℂ) ^ (2 : ℕ) - (r : ℂ)⁻¹ ^ (2 : ℕ)) * (d : ℂ)) * hphaseC

/-- Strict reciprocal-radius inequality away from the unit radius. -/
lemma fzzCigarParity_sq_four_lt_sq_add_inv
    {r : ℝ} (hr : 0 < r) (hrne : r ≠ 1) :
    4 < (r + r⁻¹) ^ (2 : ℕ) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsub : r - r⁻¹ ≠ 0 := by
    intro hzero
    have hmul := congrArg (fun z : ℝ => z * r) hzero
    field_simp [hr0] at hmul
    have hsquare : r ^ (2 : ℕ) = 1 := by nlinarith
    have : r = 1 := by nlinarith
    exact hrne this
  have hsq : 0 < (r - r⁻¹) ^ (2 : ℕ) := sq_pos_of_ne_zero hsub
  have hid : (r + r⁻¹) ^ (2 : ℕ) - 4 = (r - r⁻¹) ^ (2 : ℕ) := by
    field_simp [hr0]
    ring
  nlinarith

/-- Every coefficient quadruple in the punctured Lorentz cone universally separates reciprocal
radial carriers. -/
theorem fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_cone
    (a b c d : ℝ) (hd : d ≠ 0) (hcone : b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ d ^ (2 : ℕ)) :
    FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d := by
  intro r hr hrne x y hphase heq
  have hdef :=
    fzzCigarParityHermitianRadialPhase_reflection_sub a b c d r x y hphase
  rw [heq, sub_self] at hdef
  have hprod :
      (r - r⁻¹) * (d * (r + r⁻¹) + 2 * (b * x - c * y)) = 0 := by
    exact_mod_cast hdef.symm
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hsub : r - r⁻¹ ≠ 0 := by
    intro hzero
    have hmul := congrArg (fun z : ℝ => z * r) hzero
    field_simp [hr0] at hmul
    have hsquare : r ^ (2 : ℕ) = 1 := by nlinarith
    have : r = 1 := by nlinarith
    exact hrne this
  have hbracket : d * (r + r⁻¹) + 2 * (b * x - c * y) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hsub
  have hcauchy : (b * x - c * y) ^ (2 : ℕ) ≤ b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
    have hsquare : 0 ≤ (b * y + c * x) ^ (2 : ℕ) := sq_nonneg _
    nlinarith
  have hs := fzzCigarParity_sq_four_lt_sq_add_inv hr hrne
  have hd2 : 0 < d ^ (2 : ℕ) := sq_pos_of_ne_zero hd
  have hsqeq :
      d ^ (2 : ℕ) * (r + r⁻¹) ^ (2 : ℕ) = 4 * (b * x - c * y) ^ (2 : ℕ) := by
    have heq' : d * (r + r⁻¹) = -2 * (b * x - c * y) := by
      linarith
    calc
      d ^ (2 : ℕ) * (r + r⁻¹) ^ (2 : ℕ) = (d * (r + r⁻¹)) ^ (2 : ℕ) := by ring
      _ = (-2 * (b * x - c * y)) ^ (2 : ℕ) := by rw [heq']
      _ = 4 * (b * x - c * y) ^ (2 : ℕ) := by ring
  have hlower : 4 * d ^ (2 : ℕ) < d ^ (2 : ℕ) * (r + r⁻¹) ^ (2 : ℕ) := by
    have := mul_pos hd2 (sub_pos.mpr hs)
    nlinarith
  have hupper : 4 * (b * x - c * y) ^ (2 : ℕ) ≤ 4 * d ^ (2 : ℕ) := by
    nlinarith
  nlinarith

/-- Every target reciprocal sum strictly above two has a positive nonunit radius. -/
lemma fzzCigarParity_exists_pos_ne_one_add_inv_eq
    {s : ℝ} (hs : 2 < s) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧ r + r⁻¹ = s := by
  let t := Real.sqrt (s ^ (2 : ℕ) - 4)
  have hdisc : 0 < s ^ (2 : ℕ) - 4 := by nlinarith
  have ht : 0 < t := Real.sqrt_pos.2 hdisc
  have htsq : t ^ (2 : ℕ) = s ^ (2 : ℕ) - 4 := Real.sq_sqrt hdisc.le
  let r := (s + t) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrone : 1 < r := by dsimp [r]; nlinarith
  have hquad : r ^ (2 : ℕ) - s * r + 1 = 0 := by
    dsimp [r]
    nlinarith
  refine ⟨r, hr, ne_of_gt hrone, ?_⟩
  have hr0 : r ≠ 0 := ne_of_gt hr
  field_simp [hr0]
  nlinarith

/-- If the radial coefficient vanishes, an explicit unit phase is blind at radius two. -/
theorem not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_d_eq_zero
    (a b c : ℝ) :
    ¬ FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c 0 := by
  intro hsep
  by_cases hbc : b ^ (2 : ℕ) + c ^ (2 : ℕ) = 0
  · have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
    have hne := hsep 2 (by norm_num) (by norm_num) 1 0 (by norm_num)
    apply hne
    rw [← sub_eq_zero,
      fzzCigarParityHermitianRadialPhase_reflection_sub]
    · simp [hb, hc]
    · norm_num
  · have hbcpos : 0 < b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
      exact lt_of_le_of_ne (by positivity) (Ne.symm hbc)
    let B := Real.sqrt (b ^ (2 : ℕ) + c ^ (2 : ℕ))
    have hB : 0 < B := Real.sqrt_pos.2 hbcpos
    have hBsq : B ^ (2 : ℕ) = b ^ (2 : ℕ) + c ^ (2 : ℕ) := Real.sq_sqrt hbcpos.le
    let x := c / B
    let y := b / B
    have hphase : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      nlinarith
    have hcross : b * x - c * y = 0 := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      ring
    have hne := hsep 2 (by norm_num) (by norm_num) x y hphase
    apply hne
    rw [← sub_eq_zero,
      fzzCigarParityHermitianRadialPhase_reflection_sub]
    · simp [hcross]
    · exact hphase

/-- Outside the Lorentz cone and with `d != 0`, an explicit aligned unit phase and quadratic-root
radius give a blind reflected pair. -/
theorem not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_sq_lt
    (a b c d : ℝ) (hd : d ≠ 0) (hout : d ^ (2 : ℕ) < b ^ (2 : ℕ) + c ^ (2 : ℕ)) :
    ¬ FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d := by
  intro hsep
  let B := Real.sqrt (b ^ (2 : ℕ) + c ^ (2 : ℕ))
  have hbcpos : 0 < b ^ (2 : ℕ) + c ^ (2 : ℕ) := by
    nlinarith [sq_nonneg d]
  have hB : 0 < B := Real.sqrt_pos.2 hbcpos
  have hBsq : B ^ (2 : ℕ) = b ^ (2 : ℕ) + c ^ (2 : ℕ) := Real.sq_sqrt hbcpos.le
  rcases lt_or_gt_of_ne hd with hdneg | hdpos
  · let s := -2 * B / d
    have hminusdB : -d < B := by nlinarith
    have hs : 2 < s := by
      dsimp [s]
      have hden : 0 < -d := neg_pos.mpr hdneg
      have hratio : 1 < B / (-d) := by
        rw [lt_div_iff₀ hden]
        simpa using hminusdB
      rw [show -2 * B / d = 2 * (B / (-d)) by field_simp [hd]]
      nlinarith
    obtain ⟨r, hr, hrne, hrs⟩ :=
      fzzCigarParity_exists_pos_ne_one_add_inv_eq hs
    let x := b / B
    let y := -c / B
    have hphase : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      nlinarith
    have hcross : b * x - c * y = B := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      nlinarith
    have hbracket : d * (r + r⁻¹) + 2 * (b * x - c * y) = 0 := by
      rw [hrs, hcross]
      dsimp [s]
      field_simp [hd]
      ring
    have hne := hsep r hr hrne x y hphase
    apply hne
    rw [← sub_eq_zero,
      fzzCigarParityHermitianRadialPhase_reflection_sub]
    · simp [hbracket]
    · exact hphase
  · let s := 2 * B / d
    have hdB : d < B := by nlinarith
    have hs : 2 < s := by
      dsimp [s]
      have hratio : 1 < B / d := by
        rw [lt_div_iff₀ hdpos]
        simpa using hdB
      rw [show 2 * B / d = 2 * (B / d) by ring]
      nlinarith
    obtain ⟨r, hr, hrne, hrs⟩ :=
      fzzCigarParity_exists_pos_ne_one_add_inv_eq hs
    let x := -b / B
    let y := c / B
    have hphase : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      nlinarith
    have hcross : b * x - c * y = -B := by
      dsimp [x, y]
      field_simp [ne_of_gt hB]
      nlinarith
    have hbracket : d * (r + r⁻¹) + 2 * (b * x - c * y) = 0 := by
      rw [hrs, hcross]
      dsimp [s]
      field_simp [hd]
      ring
    have hne := hsep r hr hrne x y hphase
    apply hne
    rw [← sub_eq_zero,
      fzzCigarParityHermitianRadialPhase_reflection_sub]
    · simp [hbracket]
    · exact hphase

/-- **Sharp Hermitian reflection cone.** Universal phase-robust reciprocal-radius separation holds
exactly on `d != 0`, `b^(2 : ℕ)+c^(2 : ℕ) <= d^(2 : ℕ)`. -/
theorem fzzCigarParityHermitianUniversalRadialReflectionSeparating_iff
    (a b c d : ℝ) :
    FZZCigarParityHermitianUniversalRadialReflectionSeparating a b c d ↔
      d ≠ 0 ∧ b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ d ^ (2 : ℕ) := by
  constructor
  · intro hsep
    have hd : d ≠ 0 := by
      intro hd
      subst d
      exact
        (not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_d_eq_zero
          a b c) hsep
    refine ⟨hd, le_of_not_gt ?_⟩
    intro hout
    exact
      (not_fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_sq_lt
        a b c d hd hout) hsep
  · rintro ⟨hd, hcone⟩
    exact
      fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_cone
        a b c d hd hcone

/-- Real coordinate of a nonzero complex number's normalized phase. -/
def fzzCigarParityComplexRadialPhaseRe (z : ℂ) : ℝ := z.re / ‖z‖

/-- Imaginary coordinate of a nonzero complex number's normalized phase. -/
def fzzCigarParityComplexRadialPhaseIm (z : ℂ) : ℝ := z.im / ‖z‖

theorem fzzCigarParityComplexRadialPhase_sq_add_sq
    {z : ℂ} (hz : z ≠ 0) :
    fzzCigarParityComplexRadialPhaseRe z ^ (2 : ℕ) +
        fzzCigarParityComplexRadialPhaseIm z ^ (2 : ℕ) = 1 := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [fzzCigarParityComplexRadialPhaseRe,
    fzzCigarParityComplexRadialPhaseIm]
  field_simp [hn]
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

theorem fzzCigarParityRadialPhaseCarrier_norm
    {z : ℂ} (hz : z ≠ 0) :
    fzzCigarParityRadialPhaseCarrier ‖z‖
        (fzzCigarParityComplexRadialPhaseRe z)
        (fzzCigarParityComplexRadialPhaseIm z) = (1, z) := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  apply Prod.ext
  · simp [fzzCigarParityRadialPhaseCarrier]
  · apply Complex.ext
    · simp [fzzCigarParityRadialPhaseCarrier,
        fzzCigarParityComplexRadialPhaseRe,
        fzzCigarParityComplexRadialPhaseIm]
      field_simp [hn]
    · simp [fzzCigarParityRadialPhaseCarrier,
        fzzCigarParityComplexRadialPhaseRe,
        fzzCigarParityComplexRadialPhaseIm]
      field_simp [hn]

theorem fzzCigarParityComplexRadialPhaseRe_eq_normalized_re
    {z : ℂ} (hz : z ≠ 0) :
    fzzCigarParityComplexRadialPhaseRe z = (z / (‖z‖ : ℂ)).re := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [fzzCigarParityComplexRadialPhaseRe, Complex.div_re,
    Complex.normSq_apply]
  field_simp [hn]

theorem fzzCigarParityComplexRadialPhaseIm_eq_normalized_im
    {z : ℂ} (hz : z ≠ 0) :
    fzzCigarParityComplexRadialPhaseIm z = (z / (‖z‖ : ℂ)).im := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  simp [fzzCigarParityComplexRadialPhaseIm, Complex.div_im,
    Complex.normSq_apply]
  field_simp [hn]

theorem norm_fzzCigarParityDyadicMellinCharacter_reflection_eq_inv
    (rho : ℂ) :
    ‖fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)‖ =
      ‖fzzCigarParityDyadicMellinCharacter rho‖⁻¹ :=
  eq_inv_of_mul_eq_one_left
    (norm_fzzCigarParityDyadicMellinCharacter_reflection_mul rho)

theorem fzzCigarParityComplexRadialPhaseRe_reflection
    (rho : ℂ) :
    fzzCigarParityComplexRadialPhaseRe
        (fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)) =
      fzzCigarParityComplexRadialPhaseRe
        (fzzCigarParityDyadicMellinCharacter rho) := by
  rw [fzzCigarParityComplexRadialPhaseRe_eq_normalized_re
      (fzzCigarParityDyadicMellinCharacter_ne_zero
        (criticalLineReflectionPoint rho)),
    fzzCigarParityComplexRadialPhaseRe_eq_normalized_re
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)]
  exact congrArg Complex.re
    (fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection rho)

theorem fzzCigarParityComplexRadialPhaseIm_reflection
    (rho : ℂ) :
    fzzCigarParityComplexRadialPhaseIm
        (fzzCigarParityDyadicMellinCharacter (criticalLineReflectionPoint rho)) =
      fzzCigarParityComplexRadialPhaseIm
        (fzzCigarParityDyadicMellinCharacter rho) := by
  rw [fzzCigarParityComplexRadialPhaseIm_eq_normalized_im
      (fzzCigarParityDyadicMellinCharacter_ne_zero
        (criticalLineReflectionPoint rho)),
    fzzCigarParityComplexRadialPhaseIm_eq_normalized_im
      (fzzCigarParityDyadicMellinCharacter_ne_zero rho)]
  exact congrArg Complex.im
    (fzzCigarParityDyadicMellinCharacter_normalizedPhase_reflection rho)

theorem fzzCigarParityMellinCharacterCarrier_eq_radialPhase
    (rho : ℂ) :
    fzzCigarParityMellinCharacterCarrier rho =
      fzzCigarParityRadialPhaseCarrier
        ‖fzzCigarParityDyadicMellinCharacter rho‖
        (fzzCigarParityComplexRadialPhaseRe
          (fzzCigarParityDyadicMellinCharacter rho))
        (fzzCigarParityComplexRadialPhaseIm
          (fzzCigarParityDyadicMellinCharacter rho)) := by
  rw [fzzCigarParityMellinCharacterCarrier]
  exact (fzzCigarParityRadialPhaseCarrier_norm
    (fzzCigarParityDyadicMellinCharacter_ne_zero rho)).symm

theorem fzzCigarParityMellinCharacterCarrier_reflection_eq_reciprocalRadialPhase
    (rho : ℂ) :
    fzzCigarParityMellinCharacterCarrier (criticalLineReflectionPoint rho) =
      fzzCigarParityRadialPhaseCarrier
        ‖fzzCigarParityDyadicMellinCharacter rho‖⁻¹
        (fzzCigarParityComplexRadialPhaseRe
          (fzzCigarParityDyadicMellinCharacter rho))
        (fzzCigarParityComplexRadialPhaseIm
          (fzzCigarParityDyadicMellinCharacter rho)) := by
  rw [fzzCigarParityMellinCharacterCarrier_eq_radialPhase,
    norm_fzzCigarParityDyadicMellinCharacter_reflection_eq_inv,
    fzzCigarParityComplexRadialPhaseRe_reflection,
    fzzCigarParityComplexRadialPhaseIm_reflection]

theorem norm_fzzCigarParityDyadicMellinCharacter_eq_one_iff
    (rho : ℂ) :
    ‖fzzCigarParityDyadicMellinCharacter rho‖ = 1 ↔ rho.re = 1 / 2 := by
  rw [norm_fzzCigarParityDyadicMellinCharacter]
  constructor
  · intro h
    have harg := Real.exp_injective (h.trans Real.exp_zero.symm)
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- Fixed Hermitian reading of the literal FZZ dyadic Mellin carrier. -/
def fzzCigarParityMellinCharacterHermitianReading
    (a b c d : ℝ) (rho : ℂ) : ℂ :=
  fzzCigarParityHermitianQuadraticObservable a b c d
    (fzzCigarParityMellinCharacterCarrier rho)

/-- Every cone reporter is an exact pointwise critical-line detector under functional reflection. -/
theorem fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
    (a b c d : ℝ) (hd : d ≠ 0) (hcone : b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ d ^ (2 : ℕ))
    (rho : ℂ) :
    fzzCigarParityMellinCharacterHermitianReading a b c d rho =
        fzzCigarParityMellinCharacterHermitianReading a b c d
          (criticalLineReflectionPoint rho) ↔
      rho.re = 1 / 2 := by
  let z := fzzCigarParityDyadicMellinCharacter rho
  let r := ‖z‖
  let x := fzzCigarParityComplexRadialPhaseRe z
  let y := fzzCigarParityComplexRadialPhaseIm z
  have hz : z ≠ 0 := fzzCigarParityDyadicMellinCharacter_ne_zero rho
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hphase : x ^ (2 : ℕ) + y ^ (2 : ℕ) = 1 :=
    fzzCigarParityComplexRadialPhase_sq_add_sq hz
  have hsep :=
    fzzCigarParityHermitianUniversalRadialReflectionSeparating_of_cone
      a b c d hd hcone
  constructor
  · intro heq
    apply (norm_fzzCigarParityDyadicMellinCharacter_eq_one_iff rho).mp
    by_contra hrne
    apply hsep r hr hrne x y hphase
    rw [fzzCigarParityMellinCharacterHermitianReading,
      fzzCigarParityMellinCharacterHermitianReading,
      fzzCigarParityMellinCharacterCarrier_eq_radialPhase,
      fzzCigarParityMellinCharacterCarrier_reflection_eq_reciprocalRadialPhase]
      at heq
    exact heq
  · intro hre
    have href : criticalLineReflectionPoint rho = rho := by
      apply Complex.ext
      · norm_num [criticalLineReflectionPoint, hre]
      · simp [criticalLineReflectionPoint]
    rw [href]

/-- Universal matching of one cone reporter on all open-strip parity-Mellin divisor modes. -/
def FZZCigarParityMellinHermitianReflectionMatched
    (a b c d : ℝ) : Prop :=
  ∀ rho : ℂ, 0 < rho.re → rho.re < 1 → FZZCigarParityMellinMode rho →
    fzzCigarParityMellinCharacterHermitianReading a b c d rho =
      fzzCigarParityMellinCharacterHermitianReading a b c d
        (criticalLineReflectionPoint rho)

/-- **Hermitian-cone FZZ endpoint.** Matching any fixed cone reporter on every parity-Mellin divisor
mode is equivalent to the Riemann hypothesis. -/
theorem fzzCigarParityMellinHermitianReflectionMatched_iff_riemannHypothesis
    (a b c d : ℝ) (hd : d ≠ 0) (hcone : b ^ (2 : ℕ) + c ^ (2 : ℕ) ≤ d ^ (2 : ℕ)) :
    FZZCigarParityMellinHermitianReflectionMatched a b c d ↔
      RiemannHypothesis := by
  constructor
  · intro hmatch
    apply fzzCigarParityMellinComplete_iff_riemannHypothesis.mp
    intro rho h0 h1 hmode
    have hre :=
      (fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
        a b c d hd hcone rho).mp (hmatch rho h0 h1 hmode)
    refine ⟨rho.im, ?_⟩
    apply Complex.ext
    · rw [fzzPunctureHorizonDilationSpectralParameter_re, hre]
    · rw [fzzPunctureHorizonDilationSpectralParameter_im]
  · intro hRH rho h0 h1 hmode
    apply (fzzCigarParityMellinCharacterHermitianReading_eq_reflection_iff
      a b c d hd hcone rho).mpr
    have hxi : xi rho = 0 :=
      (fzzCigarParityMellin_eq_zero_iff_xi_eq_zero h0 h1).mp hmode
    exact xi_zero_re_eq_half_of_RH hRH hxi

end

end RHTower
