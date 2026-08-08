import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass
import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryQuadratureSource
import GaloisForLFunctions.RHTower.XiShiftedHankelFirstCrossing

/-!
# Canonical monic extension class at a shifted Xi Hankel face

This specializes the projective finite-Hankel extension coordinate to the shifted Xi moment
family.  At a right-hand first crossing, the canonical monic remainder is nonpositive.  Thus a
source proof of its strict positivity would contradict every first crossing without choosing an
orientation of the null vector.
-/

open Matrix Polynomial Set

namespace RHTower

noncomputable section

/-- Canonically oriented first extension coordinate of a shifted Xi Hankel boundary. -/
def xiShiftedHankelBoundaryMonicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  HTGeometry.finiteHankelBoundaryMonicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c

/-- The terminal product in the shifted Xi flux is a positive square times the canonical monic
extension class. -/
theorem xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
      c (Fin.last n) ^ 2 * xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.terminal_mul_hankelFirstOmittedCoupling_eq_sq_mul_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c hlast

/-- At a right-hand first crossing with a positive-definite preceding block, the intrinsic monic
extension class is nonpositive. -/
theorem xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    xiShiftedHankelBoundaryMonicRemainder y c ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hcross := xiShiftedHankelFirstCrossing_terminal_product_nonpos
    hy n c hc hmin
  rw [xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast]
    at hcross
  have hsquare : 0 < c (Fin.last n) ^ 2 := sq_pos_of_ne_zero hlast
  nlinarith

/-- The monic extension class is the monic positive-flat-quadrature remainder. -/
theorem xiShiftedHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (y : ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) :
    xiShiftedHankelBoundaryQuadratureError y c
        (X ^ (n + 1) * HTGeometry.finiteHankelNullMonicPolynomial c) =
      xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundaryQuadratureError_monic_eq_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c

/-- **Shifted-square realization.** On a singular shifted-Xi face, the canonical extension class
is the moment of `X` times the square of the monic null polynomial.  It is exactly the first local
Stieltjes defect on the current Hankel kernel. -/
theorem xiShiftedHankelBoundaryMonicRemainder_eq_shiftedSquare
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryMonicRemainder y c =
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c *
          HTGeometry.finiteHankelNullMonicPolynomial c) := by
  exact HTGeometry.finiteHankelBoundaryMonicRemainder_eq_shiftedSquare
    (fun k => (xiShiftedReciprocalMoment y k).re) c hc hlast

/-- **Shifted-Xi Christoffel-port law.**  On a singular shifted face, the forward-minus-backward
affine-multiplier square-energy difference is exactly `4a` times the canonical monic extension
coordinate. -/
theorem xiShiftedHankelBoundary_christoffelPortDifference_eq_monicRemainder
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ) (a : ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X + C a) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) -
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X - C a) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) =
      4 * a * xiShiftedHankelBoundaryMonicRemainder y c := by
  exact HTGeometry.finiteHankelBoundary_christoffelPortDifference_eq_monicRemainder
    (fun k => (xiShiftedReciprocalMoment y k).re) c a hc hlast

/-- Positivity of the shifted-face extension coordinate is exactly strict forward unit-port
dominance over the backward unit port. -/
theorem xiShiftedHankelBoundaryMonicRemainder_pos_iff_christoffelPortOrder
    {y : ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < xiShiftedHankelBoundaryMonicRemainder y c ↔
      HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X - C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) <
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X + C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) := by
  exact HTGeometry.finiteHankelBoundaryMonicRemainder_pos_iff_christoffelPortOrder
    (fun k => (xiShiftedReciprocalMoment y k).re) c hc hlast

/-- **Intrinsic tangent law.** On a minimal singular face, mass-flow velocity is a universal
negative factor times the positive square of the terminal coefficient and the shifted-square
extension energy.  Every orientation-dependent coordinate has disappeared. -/
theorem hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ_shiftedSquare
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HasDerivAt (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c)
      (-(2 * (n : ℝ) + 1) * c (Fin.last n) ^ 2 *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (X * HTGeometry.finiteHankelNullMonicPolynomial c *
            HTGeometry.finiteHankelNullMonicPolynomial c)) y := by
  have hd := hasDerivAt_xiShiftedMomentHankelQuadratic_of_kernel_succ
    hy n c hc
  have hterminal :=
    xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast
  have hshift :=
    xiShiftedHankelBoundaryMonicRemainder_eq_shiftedSquare c hc hlast
  have hvalue :
      -(2 * (n : ℝ) + 1) * c (Fin.last n) *
          xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
        -(2 * (n : ℝ) + 1) * c (Fin.last n) ^ 2 *
          HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment y k).re)
            (X * HTGeometry.finiteHankelNullMonicPolynomial c *
              HTGeometry.finiteHankelNullMonicPolynomial c) := by
    calc
      -(2 * (n : ℝ) + 1) * c (Fin.last n) *
          xiShiftedHankelFirstOmittedCoupling y (n + 1) c =
          -(2 * (n : ℝ) + 1) *
            (c (Fin.last n) *
              xiShiftedHankelFirstOmittedCoupling y (n + 1) c) := by ring
      _ = -(2 * (n : ℝ) + 1) *
          (c (Fin.last n) ^ 2 *
            xiShiftedHankelBoundaryMonicRemainder y c) := by rw [hterminal]
      _ = _ := by rw [hshift]; ring
  rw [← hvalue]
  exact hd

/-- At a right-hand first crossing, the monic null polynomial has nonpositive shifted-square
energy.  This is the local Stieltjes form of the outgoing-flux obstruction. -/
theorem xiShiftedHankelFirstCrossing_shiftedSquare_nonpos
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c *
          HTGeometry.finiteHankelNullMonicPolynomial c) ≤ 0 := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  rw [← xiShiftedHankelBoundaryMonicRemainder_eq_shiftedSquare c hc hlast]
  exact xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    hy n c hhead hcne hc hmin

/-- **First-crossing port reversal.**  At every right-hand first crossing, the forward unit
Christoffel port cannot dominate: its square energy is at most the backward-port energy. -/
theorem xiShiftedHankelFirstCrossing_christoffelForwardPort_le_backwardPort
    {y : ℝ} (hy : 0 < y) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c) (Ici y) y) :
    HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (((X + C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) ≤
      HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment y k).re)
        (((X - C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    y n c hhead hcne hc
  have hnonpos := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    hy n c hhead hcne hc hmin
  have hdiff :=
    xiShiftedHankelBoundary_christoffelPortDifference_eq_monicRemainder
      c 1 hc hlast
  norm_num at hdiff
  have hle :
      HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X + 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) ≤
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (((X - 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) := by
    linarith
  simpa using hle

/-- Completed-source formula for the canonical monic extension class. -/
theorem xiShiftedHankelBoundaryMonicRemainder_eq_inv_mul_sourceJet
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c =
      (c (Fin.last n))⁻¹ * xiShiftedHankelBoundarySourceJet w (n + 1) c := by
  rw [xiShiftedHankelBoundaryMonicRemainder,
    HTGeometry.finiteHankelBoundaryMonicRemainder_eq_inv_mul_raw _ c hlast,
    xiShiftedHankelBoundarySourceJet_eq hw]
  congr 1
  rw [xiShiftedHankelFirstOmittedCoupling,
    GaloisForLFunctions.HTGeometry.hankelFirstOmittedCoupling,
    HTGeometry.momentFunctional_X_pow_mul_finiteHankelNullPolynomial]

/-- Projective form of completed-source transport: multiplication by the terminal coordinate
removes the orientation ambiguity and leaves a positive square times the monic remainder. -/
theorem xiShiftedHankel_terminal_mul_sourceJet_eq_sq_mul_monicRemainder
    {w : ℝ} (hw : 0 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelBoundarySourceJet w (n + 1) c =
      c (Fin.last n) ^ 2 *
        xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c := by
  rw [xiShiftedHankelBoundarySourceJet_eq hw,
    xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder
      (w ^ 2) c hlast]

/-- **Projective prime--Gamma open core.** On the Euler ray, positivity of the canonical monic
extension class is exactly domination of the oriented prime discrepancy by the oriented
archimedean jet.  Both sides are invariant under reversing the null vector. -/
theorem xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < xiShiftedHankelBoundaryMonicRemainder (w ^ 2) c ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  have hsource :=
    xiShiftedHankel_terminal_mul_sourceJet_eq_sq_mul_monicRemainder
      (by linarith : 0 < w) c hlast
  rw [xiShiftedHankelBoundarySourceJet_eq_archimedean_add_discrepancy hw]
    at hsource
  have hsquare : 0 < c (Fin.last n) ^ 2 := sq_pos_of_ne_zero hlast
  constructor <;> intro h <;> nlinarith

/-- **Local Stieltjes/source equivalence.** On an admissible singular face, positivity of the one
shifted-Hankel square not seen by the current face is exactly projective prime--Gamma source
dominance. -/
theorem xiShiftedHankelBoundaryShiftedSquare_pos_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < HTGeometry.momentFunctional
        (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
        (X * HTGeometry.finiteHankelNullMonicPolynomial c *
          HTGeometry.finiteHankelNullMonicPolynomial c) ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  rw [← xiShiftedHankelBoundaryMonicRemainder_eq_shiftedSquare c hc hlast]
  exact xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
    hw c hlast

/-- **Joint source-incidence orientation law.**  On a completed-source null line, strict forward
Christoffel-port dominance is exactly the projective archimedean-over-prime-discrepancy inequality.
This identifies the missing face sign as a source-conditioned two-port orientation, not as
positivity of either diagonal port separately. -/
theorem xiShiftedHankelBoundary_christoffelPortOrder_iff_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (((X - C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) <
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ 2) k).re)
          (((X + C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) ↔
      -(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c := by
  rw [← xiShiftedHankelBoundaryMonicRemainder_pos_iff_christoffelPortOrder
      c hc hlast]
  exact xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
    hw c hlast

/-- In the endpoint convergence window, the source-only negative-binomial prime--Gamma jet is the
projective extension coordinate up to the positive square of the terminal coefficient. -/
theorem xiShiftedHankel_terminal_mul_primeArchJet_eq_sq_mul_monicRemainder
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    c (Fin.last n) * xiShiftedHankelBoundaryPrimeArchJet y (n + 1) c =
      c (Fin.last n) ^ 2 * xiShiftedHankelBoundaryMonicRemainder y c := by
  rw [← xiShiftedHankelBoundaryQuadratureError_eq_primeArchJet hy hymax,
    ← xiShiftedHankelFirstOmittedCoupling_eq_boundaryQuadratureError]
  exact xiShiftedHankel_terminal_mul_coupling_eq_sq_mul_monicRemainder y c hlast

/-- **Zero-free prime--Gamma two-port law.**  In the negative-binomial convergence window, the
source-only forward-minus-backward Christoffel-port imbalance is exactly four times the shifted-Xi
monic extension coordinate. -/
theorem primeArchShifted_christoffelPortDifference_eq_monicRemainder
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re)
          (((X + C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) -
        HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re)
          (((X - C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) =
      4 * xiShiftedHankelBoundaryMonicRemainder y c := by
  have htransport (p : Polynomial ℝ) :
      HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re) p =
        HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re) p := by
    apply HTGeometry.momentFunctional_congr
    intro k
    exact congrArg Complex.re
      (xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment hy hymax k)
  have hdiff :=
    xiShiftedHankelBoundary_christoffelPortDifference_eq_monicRemainder
      c 1 hc hlast
  norm_num at hdiff
  rw [htransport, htransport] at hdiff
  simpa using hdiff

/-- In the source-only endpoint chart, positivity of the exact face-extension coordinate is
equivalent to strict forward prime--Gamma Christoffel-port dominance. -/
theorem xiShiftedHankelBoundaryMonicRemainder_pos_iff_primeArchChristoffelPortOrder
    {y : ℝ} (hy : 0 ≤ y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    0 < xiShiftedHankelBoundaryMonicRemainder y c ↔
      HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re)
          (((X - C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) <
        HTGeometry.momentFunctional
          (fun k => (primeArchShiftedReciprocalMoment y k).re)
          (((X + C 1) * HTGeometry.finiteHankelNullMonicPolynomial c) ^ 2) := by
  have hdiff :=
    primeArchShifted_christoffelPortDifference_eq_monicRemainder
      hy hymax c hc hlast
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **First-crossing source obstruction.** At a right-hand first crossing, projective domination
of the oriented prime discrepancy by the oriented archimedean jet is impossible.  Thus proving
this one source inequality for every admissible singular face excludes every first crossing. -/
theorem xiShiftedHankelFirstCrossing_not_projectiveSourceDominance
    {w : ℝ} (hw : 1 / 2 < w) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix (w ^ 2) n).PosDef)
    (hcne : c ≠ 0)
    (hc : xiShiftedMomentHankelMatrix (w ^ 2) (n + 1) *ᵥ c = 0)
    (hmin : IsLocalMinOn
      (fun t => xiShiftedMomentHankelQuadratic t (n + 1) c)
      (Ici (w ^ 2)) (w ^ 2)) :
    ¬ (-(c (Fin.last n) *
          xiShiftedHankelBoundaryDiscrepancyJet w (n + 1) c) <
        c (Fin.last n) *
          xiShiftedHankelBoundaryArchimedeanJet w (n + 1) c) := by
  have hlast := xiShiftedHankelNullVector_terminal_ne_zero_of_head_posDef
    (w ^ 2) n c hhead hcne hc
  have hnonpos := xiShiftedHankelFirstCrossing_monicRemainder_nonpos
    (sq_pos_of_pos (by linarith : 0 < w)) n c hhead hcne hc hmin
  intro hdominance
  have hpos :=
    (xiShiftedHankelBoundaryMonicRemainder_pos_iff_projectiveSourceDominance
      hw c hlast).2 hdominance
  exact (not_lt_of_ge hnonpos) hpos

end

end RHTower
