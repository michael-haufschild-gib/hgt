import GaloisForLFunctions.RHTower.SuzukiHalfLogSquareIntegrable
import GaloisForLFunctions.HTGeometry.HalfLogTraceNonIntegrable
import GaloisForLFunctions.RHTower.SuzukiPrimeNormalCoronaComparison

/-!
# The Gamma corona sequence

The half-log trace of a Gamma carrier is the scattering map of its two frequency channels.  That
map is surjective, and — for any profile with the half-log asymptotic — its vanishing is exactly
square integrability on a terminal half-line.  Hence the singular physical quotient of the Gamma
flow is one copy of the trace space, and any profile with the same trace and a better remainder is
a cross-section of the quotient.
-/

open Complex Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **The half-log scattering map is surjective.**  A single positive channel already realises any
prescribed trace. -/
theorem halfLogScatter_surjective (β : X) :
    halfLogScatter
      ((2 * ((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-((Real.pi/4 : ℝ) * I))) • β)
      (0 : X) = β := by
  have hs : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  have hexp : Complex.exp ((Real.pi/4 : ℝ) * I) * Complex.exp (-((Real.pi/4 : ℝ) * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [halfLogScatter, smul_zero, add_zero, smul_smul, smul_smul]
  have hcoef : (1 / (2 * ((Real.sqrt Real.pi : ℝ) : ℂ))) * Complex.exp ((Real.pi/4 : ℝ) * I)
      * (2 * ((Real.sqrt Real.pi : ℝ) : ℂ) * Complex.exp (-((Real.pi/4 : ℝ) * I))) = 1 := by
    field_simp
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [hcoef, one_smul]

/-- The critical weight in the two normalisations agree. -/
theorem rpow_neg_half_eq {L : ℝ} (hL : 0 < L) : L ^ (-(1:ℝ)/2) = 1 / Real.sqrt L := by
  rw [Real.sqrt_eq_rpow, show (-(1:ℝ)/2) = -((1:ℝ)/2) by ring, Real.rpow_neg hL.le]
  exact (one_div _).symm

omit [CompleteSpace X] in
/-- **The corona dichotomy.**  For a profile with the half-log asymptotic, vanishing trace and
square integrability on a terminal half-line are the same condition. -/
theorem halfLog_trace_zero_iff_integrableOn_sq {F : ℝ → X} {β : X} {C L₁ : ℝ}
    (hL₁ : 0 < L₁)
    (hmeas : AEStronglyMeasurable F (volume.restrict (Ioi L₁)))
    (hasymp : ∀ L ∈ Ioi L₁, ‖F L - (1 / Real.sqrt L) • β‖ ≤ C / L) :
    β = 0 ↔ IntegrableOn (fun L => ‖F L‖ ^ 2) (Ioi L₁) volume := by
  constructor
  · intro hβ
    refine integrableOn_sq_of_decay (C := C) hL₁ hmeas fun L hL => ?_
    have h := hasymp L hL
    rw [hβ, smul_zero, sub_zero] at h
    exact h
  · intro hint
    by_contra hβ
    exact not_integrableOn_sq_of_halfLog_trace (F := F) (β := β) hβ hL₁ hasymp hint

omit [CompleteSpace X] in
/-- **The cross-section property.**  A comparison profile with the same trace and a better
remainder differs from the carrier by a square-integrable term. -/
theorem integrableOn_sq_sub_of_halfLog {F P : ℝ → X} {β : X} {C C' L₁ : ℝ}
    (hL₁0 : 0 < L₁)
    (hmeas : AEStronglyMeasurable (fun L => F L - P L) (volume.restrict (Ioi L₁)))
    (hF : ∀ L ∈ Ioi L₁, ‖F L - (1 / Real.sqrt L) • β‖ ≤ C / L)
    (hP : ∀ L ∈ Ioi L₁, ‖P L - (1 / Real.sqrt L) • β‖ ≤ C' / L) :
    IntegrableOn (fun L => ‖F L - P L‖ ^ 2) (Ioi L₁) volume := by
  refine integrableOn_sq_of_decay (C := C + C') hL₁0 hmeas fun L hL => ?_
  have h1 := hF L hL
  have h2 := hP L hL
  have hLpos : 0 < L := lt_trans hL₁0 hL
  have htri : ‖F L - P L‖
      ≤ ‖F L - (1 / Real.sqrt L) • β‖ + ‖P L - (1 / Real.sqrt L) • β‖ := by
    have hsplit : F L - P L
        = (F L - (1 / Real.sqrt L) • β) - (P L - (1 / Real.sqrt L) • β) := by abel
    rw [hsplit]
    exact norm_sub_le _ _
  have hsum : C / L + C' / L = (C + C') / L := by ring
  linarith [htri, h1, h2, hsum]

section Physical

variable [Nontrivial X] {Rint r : ℝ → ℝ} {T : X →L[ℂ] X}

/-- The normalised inverse Fourier profile of a homogeneous Gamma carrier. -/
def gammaProfile (Rint : ℝ → ℝ) (T : X →L[ℂ] X) (cp cm : X) (R L : ℝ) : X :=
  ((1 / (2 * Real.pi) : ℝ)) •
    ((∫ η in (0:ℝ)..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
      + ∫ t in (0:ℝ)..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))

/-- **The physical half-log asymptotic.**  After the `1/2π` normalisation of the inverse Fourier
integral, the carrier is the half-log trace at the critical power plus `O(L^{-1})`. -/
theorem norm_gammaProfile_sub_halfLog_le {r' : ℝ → ℝ} (hT : IsSelfAdjoint T)
    (hR : Rint 0 = 0) {cp cm : X} {A L R B : ℝ}
    (hA : 0 < A) (hAR : A ≤ R) (hTL : ‖T‖ / 2 < L) (hL : 0 < L)
    (hRint : ∀ x : ℝ, HasDerivAt Rint (r x) x)
    (hrnn : ∀ x : ℝ, 0 ≤ r x)
    (hrb : ∀ x : ℝ, |x| ≤ A → |r x| ≤ B)
    (hrc : Continuous r)
    (hr' : ∀ x : ℝ, HasDerivAt r (r' x) x)
    (hr'c : Continuous r')
    (hr'pos : ∀ x : ℝ, 0 ≤ x → 0 ≤ r' x)
    (hr'neg : ∀ x : ℝ, x ≤ 0 → r' x ≤ 0) :
    ‖gammaProfile Rint T cp cm R L - (1 / Real.sqrt L) • halfLogScatter cp cm‖
      ≤ (1 / (2 * Real.pi)) *
        (((‖cp‖ + ‖cm‖) * (2 * A ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)))
            + (4 * ((B / 2 + ‖T‖ / 2) * (‖cp‖ + ‖cm‖)) * A ^ ((1:ℝ)/2)) / L)
          + (3 * A ^ (-(1:ℝ)/2) + R ^ (-(1:ℝ)/2)) * (L - ‖T‖ / 2)⁻¹ * (‖cp‖ + ‖cm‖)) := by
  have hmain := norm_halfLog_scattering_asymptotic (T := T) (r := r) (r' := r') (Rint := Rint)
    hT hR hA hAR hTL hRint hrnn hrb hrc hr' hr'c hr'pos hr'neg (cp := cp) (cm := cm) (B := B)
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  have hlead : ((1 / (2 * Real.pi) : ℝ)) •
      ((((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ)) : ℂ) • halfLogScatter cp cm)
      = (1 / Real.sqrt L) • halfLogScatter cp cm := by
    rw [ofReal_smul_eq, smul_smul]
    congr 1
    rw [rpow_neg_half_eq hL]
    field_simp
  have hsplit : gammaProfile Rint T cp cm R L - (1 / Real.sqrt L) • halfLogScatter cp cm
      = ((1 / (2 * Real.pi) : ℝ)) •
        (((∫ η in (0:ℝ)..R, (η ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T η cp))
            + ∫ t in (0:ℝ)..R, (t ^ (-(1:ℝ)/2)) • (freqPropagator L Rint T (-t) cm))
          - (((2 * Real.pi * L ^ (-(1:ℝ)/2) : ℝ)) : ℂ) • halfLogScatter cp cm) := by
    rw [gammaProfile, smul_sub, hlead]
  rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left hmain (by positivity)

end Physical

section CrossSection

open scoped ContinuousFunctionalCalculus

variable [Nontrivial X] {T : X →L[ℂ] X}

/-- The prime-normal cross-section `P_T(β)(L) = (L - T/2)^{-1/2}β`. -/
def primeNormalSection (T : X →L[ℂ] X) (β : X) (L : ℝ) : X :=
  (L ^ (-(1:ℝ)/2)) • ((cfc (RHTower.binomialSymbol L) T) β)

/-- **The cross-section is the half-log term up to `O(L^{-3/2})`.** -/
theorem norm_primeNormalSection_sub_halfLog_le (hT : IsSelfAdjoint T) {β : X} {L : ℝ}
    (hL : ‖T‖ ≤ L) (hL0 : 0 < L) :
    ‖primeNormalSection T β L - (1 / Real.sqrt L) • β‖
      ≤ (‖T‖ * ‖β‖ / 2) * L ^ (-(3:ℝ)/2) := by
  have hdecomp := RHTower.cfc_binomialSymbol_eq_one_add T hT hL hL0
  have hrem := RHTower.norm_cfc_binomialSymbol_sub_one_le T hL hL0
  have hsplit : primeNormalSection T β L - (1 / Real.sqrt L) • β
      = (L ^ (-(1:ℝ)/2)) • ((cfc (fun t : ℝ => RHTower.binomialSymbol L t - 1) T) β) := by
    rw [primeNormalSection, hdecomp, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply, smul_add, rpow_neg_half_eq hL0]
    abel
  rw [hsplit, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL0 _)]
  have hop : ‖(cfc (fun t : ℝ => RHTower.binomialSymbol L t - 1) T) β‖ ≤ (‖T‖ / (2 * L)) * ‖β‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ β) ?_
    exact mul_le_mul_of_nonneg_right hrem (norm_nonneg β)
  have hpow : (L ^ (-(1:ℝ)/2)) * (‖T‖ / (2 * L) * ‖β‖)
      = (‖T‖ * ‖β‖ / 2) * L ^ (-(3:ℝ)/2) := by
    have hLne : L ≠ 0 := ne_of_gt hL0
    have hsplitpow : L ^ (-(3:ℝ)/2) = L ^ (-(1:ℝ)/2) * L ^ (-(1:ℝ)) := by
      rw [← Real.rpow_add hL0]
      norm_num
    rw [hsplitpow, Real.rpow_neg_one]
    field_simp
    ring
  calc (L ^ (-(1:ℝ)/2)) * ‖(cfc (fun t : ℝ => RHTower.binomialSymbol L t - 1) T) β‖
      ≤ (L ^ (-(1:ℝ)/2)) * ((‖T‖ / (2 * L)) * ‖β‖) :=
        mul_le_mul_of_nonneg_left hop (Real.rpow_nonneg hL0.le _)
    _ = (‖T‖ * ‖β‖ / 2) * L ^ (-(3:ℝ)/2) := hpow

end CrossSection

end

end GaloisForLFunctions.RHTower
