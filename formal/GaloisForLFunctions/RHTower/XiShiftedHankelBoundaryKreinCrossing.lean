import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryKreinCrossing
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryExtensionClass
import GaloisForLFunctions.RHTower.XiShiftedHankelHeatResolventBridge

/-!
# Shifted Xi boundary orientation as a Krein crossing form

This specializes the finite-face null-cone law to shifted reciprocal-Xi moments.  On completed
source incidence, the projective prime--Gamma open core is exactly strict positive crossing type
for multiplication by `X` on the canonical lightlike null polynomial.
-/

open Matrix Polynomial Set

namespace RHTower

noncomputable section

/-- Canonical Krein crossing form at a shifted-Xi Hankel face. -/
def xiShiftedHankelBoundaryNullCrossingForm
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  HTGeometry.finiteHankelBoundaryNullCrossingForm
    (fun k => (xiShiftedReciprocalMoment y k).re) c

/-- The shifted-Xi monic null polynomial is lightlike on every singular face. -/
theorem xiShiftedHankelBoundaryNullSelf_eq_zero
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) = 0 := by
  exact HTGeometry.finiteHankelBoundaryNullSelf_eq_zero c hc hlast

/-- **Shifted-Xi Krein crossing identity.**  The missing monic extension coordinate is exactly
the multiplication-by-`X` crossing form on the canonical lightlike null polynomial. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryNullCrossingForm y c =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryNullCrossingForm_eq_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c hc hlast

/-- The completed-source jet is the oriented Krein crossing form times the terminal coordinate. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_sourceJet
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryNullCrossingForm (w ^ (2 : ℕ)) c =
      (c (Fin.last n))⁻¹ *
        xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast,
    xiShiftedHankelBoundaryMonicRemainder_eq_inv_mul_sourceJet hw c hlast]

/-- **Completed-source Krein orientation law.**  On a shifted-Xi null line, strict positive
crossing type is exactly projective archimedean-over-prime-discrepancy dominance. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_pos_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < xiShiftedHankelBoundaryNullCrossingForm (w ^ (2 : ℕ)) c ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast]
  exact xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
    hw c hlast

/-- At a right-hand first crossing, the canonical Xi null line has nonpositive Krein crossing
type.  Excluding first crossings is therefore a strict positive-type theorem. -/
theorem xiShiftedHankelFirstCrossing_nullCrossingForm_nonpos
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    xiShiftedHankelBoundaryNullCrossingForm y c ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast]
  exact xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    hy n c hhead hcne hc hmin

/-- The boundary heat kernel is exactly the matching rung of the factorial-Volterra flag. -/
theorem xiShiftedHankelBoundaryHeatKernel_eq_factorialVolterraHeatKernel
    (y : ℝ) (r : ℕ) (c : Fin r → ℝ) :
    xiShiftedHankelBoundaryHeatKernel y r c =
      xiFactorialVolterraHeatKernel y r c := by
  funext t
  rw [xiShiftedHankelBoundaryHeatKernel_eq_polynomial_mul_heat]
  rfl

/-- **Krein--heat identity.** The Xi crossing form is the first factorial-Volterra heat rung not
forced to vanish by the current singular face, divided by the terminal null coordinate. -/
theorem xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_nextVolterraIntegral
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryNullCrossingForm y c =
      (c (Fin.last n))⁻¹ *
        (∫ t in Ioi (0 : ℝ),
          xiFactorialVolterraHeatKernel y (n + 1) c t) := by
  rw [← xiShiftedHankelBoundaryHeatKernel_eq_factorialVolterraHeatKernel]
  rw [integral_xiShiftedHankelBoundaryHeatKernel_eq_firstOmittedCoupling hy]
  rw [xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast]
  have hflux :=
    xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast
  have hfactor :
      c (Fin.last n) *
          (xiShiftedHankelFirstOmittedCoupling y (n + 1) c -
            c (Fin.last n) * xiShiftedHankelBoundaryMonicRemainder y c) = 0 := by
    calc
      c (Fin.last n) *
          (xiShiftedHankelFirstOmittedCoupling y (n + 1) c -
            c (Fin.last n) * xiShiftedHankelBoundaryMonicRemainder y c) =
        c (Fin.last n) * xiShiftedHankelFirstOmittedCoupling y (n + 1) c -
          c (Fin.last n) ^ (2 : ℕ) * xiShiftedHankelBoundaryMonicRemainder y c := by ring
      _ = 0 := by rw [hflux]; ring
  have hzero := (mul_eq_zero.mp hfactor).resolve_left hlast
  have hcoupling :
      xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
        c (Fin.last n) * xiShiftedHankelBoundaryMonicRemainder y c :=
    sub_eq_zero.mp hzero
  rw [hcoupling]
  field_simp

/-- **Factorial-Volterra crossing class.** A singular size-`n+1` Xi face annihilates exactly the
visible Volterra flag indexed by `0,...,n`; its oriented affine extension is the next rung. -/
theorem xiShiftedHankelBoundary_kreinVolterraFlag
    {y : ℝ} (hy : 0 < y) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    (∀ i : Fin (n + 1),
      (∫ t in Ioi (0 : ℝ),
        xiFactorialVolterraHeatKernel y (i : ℕ) c t) = 0) ∧
    xiShiftedHankelBoundaryNullCrossingForm y c =
      (c (Fin.last n))⁻¹ *
        (∫ t in Ioi (0 : ℝ),
          xiFactorialVolterraHeatKernel y (n + 1) c t) := by
  exact ⟨fun i =>
      integral_xiFactorialVolterraHeatKernel_eq_zero_of_kernel hy c hc i,
    xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_nextVolterraIntegral
      hy c hc hlast⟩

/-- **Shifted-Xi Krein class.**  Singular incidence is a lightlike polynomial whose crossing
slope simultaneously is the affine extension class and the normalized completed-source jet. -/
theorem xiShiftedHankelBoundary_kreinCrossingClass
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ (2 : ℕ)) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.momentInner
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
        (HTGeometry.finiteHankelNullMonicPolynomial c)
        (HTGeometry.finiteHankelNullMonicPolynomial c) = 0 ∧
      xiShiftedHankelBoundaryNullCrossingForm (w ^ (2 : ℕ)) c =
        xiShiftedHankelBoundaryMonicRemainder (w ^ (2 : ℕ)) c ∧
      xiShiftedHankelBoundaryNullCrossingForm (w ^ (2 : ℕ)) c =
        (c (Fin.last n))⁻¹ *
          xiShiftedHankelBoundarySourceJet w (n + 1) c :=
  ⟨xiShiftedHankelBoundaryNullSelf_eq_zero c hc hlast,
    xiShiftedHankelBoundaryNullCrossingForm_eq_monicRemainder c hc hlast,
    xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_sourceJet hw c hc hlast⟩

end

end RHTower
