import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint
import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.RouteRHarmonicQuantumGapCriterion

/-!
# Parikh--Wilczek reflection-orbit aggregate no-go

The finite-mass Borel recoil holonomy has a physical, gauge-invariant imaginary phase.  Critical-
line reflection sends holonomy to its complex conjugate, hence reverses this phase.  Therefore
every equal-weight linear aggregate over a complete reflection orbit vanishes identically, even
off critical line.  More generally, arbitrary fixed weights `a,b` retain only `a-b`; their zero
locus is symmetric weighting or critical wall.

Strongest positive survivor is quadratic orbit energy.  It is exactly twice squared oriented
phase, is nonnegative and reflection-invariant, and vanishes exactly on critical wall.  Universal
vanishing at any one Borel grade is exactly RH.  Thus signed global averaging cannot be PW-B
producer; viable global law must control nonlinear energy or supply source-derived orientation.

`[NEW] [CLASSIFICATION] [NO-GO] [POSITIVE SURVIVOR] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Critical-line reflection before any divisor selection. -/
def schwarzschildParikhWilczekBorelLineReflection (s : ℂ) : ℂ :=
  1 - (starRingEnd ℂ) s

/-- Reflection sends closed recoil holonomy to its complex conjugate. -/
theorem schwarzschildParikhWilczekBorelRecoilHolonomy_lineReflection
    (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekBorelRecoilHolonomy
        (schwarzschildParikhWilczekBorelLineReflection s) k =
      (starRingEnd ℂ) (schwarzschildParikhWilczekBorelRecoilHolonomy s k) := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy,
    schwarzschildParikhWilczekBorelRecoilHolonomy,
    schwarzschildParikhWilczekBorelRecoilEdge,
    schwarzschildParikhWilczekBorelRecoilEdge,
    schwarzschildParikhWilczekBorelRecoilEdge,
    schwarzschildParikhWilczekBorelRecoilEdge,
    schwarzschildParikhWilczekBorelLineReflection]
  apply Complex.ext <;> norm_num [Complex.mul_re, Complex.mul_im] <;> ring

/-- Gauge-invariant recoil phase is reflection odd. -/
theorem schwarzschildParikhWilczekBorelRecoilHolonomy_im_lineReflection
    (s : ℂ) (k : ℕ) :
    (schwarzschildParikhWilczekBorelRecoilHolonomy
        (schwarzschildParikhWilczekBorelLineReflection s) k).im =
      -(schwarzschildParikhWilczekBorelRecoilHolonomy s k).im := by
  rw [schwarzschildParikhWilczekBorelRecoilHolonomy_lineReflection]
  simp

/-- Most general fixed real-linear aggregate of two members of one reflection orbit. -/
def schwarzschildParikhWilczekBorelLinearOrbitAggregate
    (a b : ℝ) (s : ℂ) (k : ℕ) : ℝ :=
  a * (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im +
    b * (schwarzschildParikhWilczekBorelRecoilHolonomy
      (schwarzschildParikhWilczekBorelLineReflection s) k).im

/-- Every two-copy linear aggregate retains only antisymmetric weight. -/
theorem schwarzschildParikhWilczekBorelLinearOrbitAggregate_eq
    (a b : ℝ) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekBorelLinearOrbitAggregate a b s k =
      (a - b) * (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im := by
  rw [schwarzschildParikhWilczekBorelLinearOrbitAggregate,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_lineReflection]
  ring

/-- Equal source weights make every reflection orbit linearly invisible, with no wall premise. -/
theorem schwarzschildParikhWilczekBorelLinearOrbitAggregate_equalWeights
    (w : ℝ) (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekBorelLinearOrbitAggregate w w s k = 0 := by
  rw [schwarzschildParikhWilczekBorelLinearOrbitAggregate_eq]
  ring

/-- Complete zero-locus classification of fixed linear reflection-orbit aggregation. -/
theorem schwarzschildParikhWilczekBorelLinearOrbitAggregate_eq_zero_iff
    (a b : ℝ) (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekBorelLinearOrbitAggregate a b s k = 0 ↔
      a = b ∨ s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekBorelLinearOrbitAggregate_eq, mul_eq_zero,
    sub_eq_zero,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
      s k hs0 hs1 hsim]

/-- Reflection-orbit quadratic energy of physical recoil holonomy. -/
def schwarzschildParikhWilczekBorelQuadraticOrbitEnergy
    (s : ℂ) (k : ℕ) : ℝ :=
  (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im ^ 2 +
    (schwarzschildParikhWilczekBorelRecoilHolonomy
      (schwarzschildParikhWilczekBorelLineReflection s) k).im ^ 2

/-- Exact survivor: quadratic aggregation retains twice squared oriented phase. -/
theorem schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq
    (s : ℂ) (k : ℕ) :
    schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k =
      2 * (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im ^ 2 := by
  rw [schwarzschildParikhWilczekBorelQuadraticOrbitEnergy,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_lineReflection]
  ring

theorem schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_nonneg
    (s : ℂ) (k : ℕ) :
    0 ≤ schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k := by
  rw [schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq]
  positivity

/-- Unlike signed aggregation, quadratic orbit energy vanishes exactly on critical wall. -/
theorem schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq_zero_iff
    (s : ℂ) (k : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekBorelQuadraticOrbitEnergy s k = 0 ↔
      s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq]
  constructor
  · intro h
    have him : (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im = 0 := by
      nlinarith [sq_nonneg
        (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im]
    exact (schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
      s k hs0 hs1 hsim).mp him
  · intro hs
    have him := (schwarzschildParikhWilczekBorelRecoilHolonomy_im_eq_zero_iff
      s k hs0 hs1 hsim).mpr hs
    rw [him]
    norm_num

/-- At every actual Xi divisor, quadratic recoil-orbit energy is exact wall receiver. -/
theorem schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_zero_at_xiSupport_iff
    (rho : XiDivisorSupport) (k : ℕ) :
    schwarzschildParikhWilczekBorelQuadraticOrbitEnergy (rho : ℂ) k = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit rho
  exact schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_eq_zero_iff
    (rho : ℂ) k h0 h1 (xi_divisor_support_im_ne_zero rho)

/-- Universal quadratic recoil-orbit flatness, at even one Borel grade, is exactly RH. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_zero
    (k : ℕ) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        schwarzschildParikhWilczekBorelQuadraticOrbitEnergy (rho : ℂ) k = 0 := by
  constructor
  · intro hRH rho
    exact
      (schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_zero_at_xiSupport_iff rho k).mpr
        (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (schwarzschildParikhWilczekBorelQuadraticOrbitEnergy_zero_at_xiSupport_iff rho k).mp
        (h rho)

end

end RHTower
