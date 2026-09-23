import GaloisForLFunctions.HTGeometry.FiniteConfluentDarboux
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeAdaptiveSourceTransversality
import GaloisForLFunctions.RHTower.XiShiftedHalfDensityAdjacentConnection

/-!
# Canonical hard-edge worldline/source conservation

For an actual local root branch of the moving inverse-Hankel admission, coefficient transport,
the half-density landing, and finite confluent Christoffel--Darboux combine into

`hard speed * Padé residue * adaptive completed-source capacity = 2 n y x² hₙ`.

This is an admission-sensitive source law, formed before aggregation. It is neither a fixed
linear reporter nor a post-aggregation orientation. Shape normalization removes `hₙ`; after
parabolic reparametrization `y=w²`, the exact forcing becomes `4 n w³ x²`.
-/

open Complex Matrix MeasureTheory Set Polynomial Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Chain rule for evaluation of a finite coefficient polynomial curve along a moving point. -/
theorem hasDerivAt_finitePolynomialCurve_eval {N : ℕ}
    {c : Fin N → ℝ → ℝ} {dc : Fin N → ℝ} {x : ℝ → ℝ} {xdot y : ℝ}
    (hc : ∀ i, HasDerivAt (c i) (dc i) y) (hx : HasDerivAt x xdot y) :
    HasDerivAt (fun v => (finitePolynomialCurve c v).eval (x v))
      ((finitePolynomialVelocity dc).eval (x y) +
        xdot * (finitePolynomialCurve c y).derivative.eval (x y)) y := by
  have hsum : HasDerivAt
      (fun v => ∑ i : Fin N, c i v * x v ^ (i : ℕ))
      (∑ i : Fin N,
        (dc i * x y ^ (i : ℕ) +
          c i y * ((i : ℕ) : ℝ) * x y ^ ((i : ℕ) - 1) * xdot)) y := by
    apply HasDerivAt.fun_sum
    intro i hi
    have hterm := (hc i).mul (hx.pow (i : ℕ))
    change HasDerivAt (fun v => c i v * x v ^ (i : ℕ)) _ y at hterm
    refine hterm.congr_deriv ?_
    simp only [Pi.pow_apply]
    ring
  convert hsum using 1
  · funext v
    rw [finitePolynomialCurve, Polynomial.ofFn_eq_sum_monomial,
      Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial]
  · simp only [finitePolynomialVelocity, finitePolynomialCurve,
      Polynomial.ofFn_eq_sum_monomial]
    rw [Polynomial.eval_finsetSum, map_sum, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_monomial, Polynomial.derivative_monomial]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- Evaluation of source-native monic landing at an admitted root. -/
theorem xiShiftedAdaptiveMonicHalfDensityLanding_eval_root
    (s : ℕ → ℝ) (n : ℕ) {x : ℝ}
    (hroot : (HTGeometry.monicOrtho s n).eval x = 0) :
    (xiShiftedAdaptiveMonicHalfDensityLanding s n).eval x =
      x ^ (2 : ℕ) * (HTGeometry.monicOrtho s n).derivative.eval x -
        ((n : ℝ) + 1 / 2) * (HTGeometry.monicOrtho s (n + 1)).eval x := by
  simp only [xiShiftedAdaptiveMonicHalfDensityLanding,
    xiShiftedAdaptiveHalfDensityLanding,
    xiShiftedMobiusHalfDensityGenerator, xiShiftedMobiusDensityGenerator,
    Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_smul, smul_eq_mul,
    hroot, mul_zero, sub_zero]
  ring

/-- Actual inverse-Hankel admission velocity at a root: source connection plus one Gauss edge. -/
theorem finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ}
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).eval x = 0) :
    (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)).eval x =
      x ^ (2 : ℕ) * (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval x +
      2 * (n : ℝ) * HTGeometry.monicOrthoBeta
        (fun k => (xiShiftedReciprocalMoment y k).re) n *
        (HTGeometry.monicOrtho
          (fun k => (xiShiftedReciprocalMoment y k).re) (n - 1)).eval x := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP := xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hroot' : (HTGeometry.monicOrtho s n).eval x = 0 := by
    simpa only [s, hP] using hroot
  have hlanding := xiShiftedAdaptiveMonicHalfDensityLanding_eval_root s n hroot'
  dsimp only [s] at hroot' hlanding
  have hrecPoly := HTGeometry.X_mul_monicOrtho_below hbelow
    (n := n) (by omega : n + 1 ≤ n + 2)
  have hrec := congrArg (Polynomial.eval x) hrecPoly
  simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_add,
    Polynomial.eval_smul, smul_eq_mul] at hrec
  rw [hroot'] at hrec
  simp only [mul_zero, add_zero] at hrec
  have hvelocity :=
    finitePolynomialVelocity_xiShiftedCanonicalAdmission_eq_monicHalfDensityLanding_add_prev
      hy hn hH
  rw [hvelocity, Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul, hlanding]
  rw [hP]
  nlinarith

/-- Displayed reciprocal hard-root speed is derivative of moving hard coordinate. -/
theorem hasDerivAt_reciprocalHardRoot
    {x : ℝ → ℝ} {xdot y : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0) :
    HasDerivAt (fun v => (x v)⁻¹ - v) (-xdot / (x y) ^ (2 : ℕ) - 1) y := by
  change HasDerivAt (x⁻¹ - id) (-xdot / (x y) ^ (2 : ℕ) - 1) y
  exact (hx.inv hx0).sub (hasDerivAt_id y)

/-- Differentiating an actual local root branch gives exact coefficient/root chain rule. -/
theorem xiShiftedCanonicalAdmission_rootCurve_chain
    {y : ℝ} (hy : 0 < y) (n : ℕ)
    (hdet : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) n).det ≠ 0)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (finitePolynomialVelocity (xiShiftedCanonicalAdmissionVelocity y n)).eval (x y) +
        xdot * (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment y k).re) n).derivative.eval (x y) = 0 := by
  have hcurve := hasDerivAt_finitePolynomialCurve_eval
    (x := x) (xdot := xdot)
    (fun i => hasDerivAt_xiShiftedCanonicalAdmissionCurve hy n hdet i) hx
  rw [finitePolynomialCurve_xiShiftedCanonicalAdmission] at hcurve
  have hzero : HasDerivAt
      (fun v => (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) 0 y :=
    hroot.hasDerivAt_iff.mpr (hasDerivAt_const (x := y) 0)
  exact hcurve.unique hzero

/-- **Actual arithmetic source/worldline conservation.** Reciprocal hard-root speed times Gauss
terminal mass equals current Jacobi norm energy. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_terminalMass_eq_normSq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (-xdot / (x y) ^ (2 : ℕ) - 1) *
        xiShiftedHardEdgeGaussTerminalMass y
          (fun k => (xiShiftedReciprocalMoment y k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) (x y) =
      2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) *
        HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s (m + 1)
  let D := P.derivative.eval (x y)
  let beta := HTGeometry.monicOrthoBeta s (m + 1)
  let Pprev := (HTGeometry.monicOrtho s m).eval (x y)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hroot0 : P.eval (x y) = 0 := hroot.eq_of_nhds
  have hchain := xiShiftedCanonicalAdmission_rootCurve_chain hy (m + 1)
    (xiShiftedMomentHankel_det_ne_zero_of_add_two_posDef hH) hx hroot
  have hvelocity := finitePolynomialVelocity_xiShiftedCanonicalAdmission_eval_root
    hy (by omega : 0 < m + 1) hH hroot0
  have hchain' : (x y) ^ (2 : ℕ) * D +
        2 * (((m + 1 : ℕ) : ℝ)) * beta * Pprev + xdot * D = 0 := by
    rw [hvelocity] at hchain
    simpa only [D, beta, Pprev, P, s, Nat.add_sub_cancel] using hchain
  have hflow : (-xdot / (x y) ^ (2 : ℕ) - 1) * (x y) ^ (2 : ℕ) * D =
      2 * ((m + 1 : ℕ) : ℝ) * beta * Pprev := by
    field_simp [hx0]
    nlinarith [hchain']
  have hP : P = HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hrootOrtho : (HTGeometry.monicOrtho s (m + 1)).eval (x y) = 0 := by
    rw [← hP]
    exact hroot0
  have hgauss :=
    HTGeometry.monicOrthoBeta_mul_christoffel_mul_derivative_mul_prev_eq_normSq_below
      (s := s) hbelow (by omega : m + 2 < m + 3) (x := x y) hrootOrtho
  change (-xdot / (x y) ^ (2 : ℕ) - 1) *
      (y * (x y) ^ (4 : ℕ) * HTGeometry.christoffel s m (x y) * D ^ (2 : ℕ)) =
    2 * (((m + 1 : ℕ) : ℝ)) * y * (x y) ^ (2 : ℕ) *
      HTGeometry.monicOrthoNormSq s (m + 1)
  calc
    _ = y * (x y) ^ (2 : ℕ) * HTGeometry.christoffel s m (x y) * D *
        ((-xdot / (x y) ^ (2 : ℕ) - 1) * (x y) ^ (2 : ℕ) * D) := by ring
    _ = y * (x y) ^ (2 : ℕ) * HTGeometry.christoffel s m (x y) * D *
        (2 * (((m + 1 : ℕ) : ℝ)) * beta * Pprev) := by rw [hflow]
    _ = 2 * (((m + 1 : ℕ) : ℝ)) * y * (x y) ^ (2 : ℕ) *
        (beta * HTGeometry.christoffel s m (x y) * D * Pprev) := by ring
    _ = 2 * (((m + 1 : ℕ) : ℝ)) * y * (x y) ^ (2 : ℕ) *
        HTGeometry.monicOrthoNormSq s (m + 1) := by
      dsimp only [beta, D, Pprev]
      rw [hP, hgauss]

/-- Capacity form: hard speed times Padé residue times adaptive completed `P^sharp` source
capacity equals current canonical norm energy. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_sourceCapacity_eq_normSq
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (-xdot / (x y) ^ (2 : ℕ) - 1) *
        (xiShiftedHardEdgeGaussPadeResidue
          (fun k => (xiShiftedReciprocalMoment y k).re) n (x y) *
          xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity y n
            (HTGeometry.monicMomentAdmissionPolynomial
              (fun k => (xiShiftedReciprocalMoment y k).re) n) (x y)) =
      2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) *
        HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  have hroot0 := hroot.eq_of_nhds
  have hdegree : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).natDegree ≤ n := by
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  rw [xiShiftedHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
    hdegree y hx0 hroot0]
  exact xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_terminalMass_eq_normSq
    hy hn hH hx hx0 hroot

/-- Shape-normalized conservation: only explicit arithmetic forcing remains. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_normalizedTerminalMass
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    (-xdot / (x y) ^ (2 : ℕ) - 1) *
        (xiShiftedHardEdgeGaussTerminalMass y
          (fun k => (xiShiftedReciprocalMoment y k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) (x y) /
          HTGeometry.monicOrthoNormSq
            (fun k => (xiShiftedReciprocalMoment y k).re) n) =
      2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) := by
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hnorm : HTGeometry.monicOrthoNormSq s n ≠ 0 :=
    ne_of_gt (HTGeometry.monicOrthoNorm_pos_below hbelow (by omega))
  have hworld := xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_terminalMass_eq_normSq
    hy hn hH hx hx0 hroot
  dsimp only [s] at hnorm
  calc
    _ = ((-xdot / (x y) ^ (2 : ℕ) - 1) *
        xiShiftedHardEdgeGaussTerminalMass y
          (fun k => (xiShiftedReciprocalMoment y k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) (x y)) /
          HTGeometry.monicOrthoNormSq
            (fun k => (xiShiftedReciprocalMoment y k).re) n := by
      rw [mul_div_assoc]
    _ = (2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) *
        HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n) /
          HTGeometry.monicOrthoNormSq
            (fun k => (xiShiftedReciprocalMoment y k).re) n := by rw [hworld]
    _ = 2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) := mul_div_cancel_right₀ _ hnorm

/-- Parabolic hard-coordinate derivative has forced critical-scale normalized source product. -/
theorem xiShiftedCanonicalAdmissionParabolicHardEdgeWorldline_mul_normalizedTerminalMass
    {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ (2 : ℕ)))
    (hx0 : x (w ^ (2 : ℕ)) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ (2 : ℕ))]
          fun _ => 0) :
    (2 * w * (-xdot / (x (w ^ (2 : ℕ))) ^ (2 : ℕ) - 1)) *
        (xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ))
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n) (x (w ^ (2 : ℕ))) /
          HTGeometry.monicOrthoNormSq
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n) =
      4 * (n : ℝ) * w ^ (3 : ℕ) * (x (w ^ (2 : ℕ))) ^ (2 : ℕ) := by
  have hnormalized :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_normalizedTerminalMass
      (sq_pos_of_pos hw) hn hH hx hx0 hroot
  nlinarith [hnormalized]

/-- Every nonzero canonical Gauss root in a positive chamber has positive shape-normalized hard
terminal mass. This positivity is source-native: finite confluent Darboux prevents its derivative
factor from vanishing. -/
theorem xiShiftedCanonicalAdmissionHardEdgeNormalizedTerminalMass_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ} (hx : x ≠ 0)
    (hroot : (HTGeometry.monicMomentAdmissionPolynomial
      (fun k => (xiShiftedReciprocalMoment y k).re) n).eval x = 0) :
    0 < xiShiftedHardEdgeGaussTerminalMass y
          (fun k => (xiShiftedReciprocalMoment y k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment y k).re) n) x /
        HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment y k).re) n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  let s : ℕ → ℝ := fun k => (xiShiftedReciprocalMoment y k).re
  let P := HTGeometry.monicMomentAdmissionPolynomial s (m + 1)
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  have hP : P = HTGeometry.monicOrtho s (m + 1) :=
    xiShiftedCanonicalAdmissionPolynomial_eq_monicOrtho hH
  have hrootOrtho : (HTGeometry.monicOrtho s (m + 1)).eval x = 0 := by
    rw [← hP]
    exact hroot
  have hgauss :=
    HTGeometry.monicOrthoBeta_mul_christoffel_mul_derivative_mul_prev_eq_normSq_below
      (s := s) hbelow (by omega : m + 2 < m + 3) hrootOrtho
  have hnorm : 0 < HTGeometry.monicOrthoNormSq s (m + 1) :=
    HTGeometry.monicOrthoNorm_pos_below hbelow (by omega)
  have hderiv : (HTGeometry.monicOrtho s (m + 1)).derivative.eval x ≠ 0 := by
    intro hzero
    rw [hzero] at hgauss
    simp only [mul_zero, zero_mul] at hgauss
    linarith
  have hchristoffel : 0 < HTGeometry.christoffel s m x :=
    HTGeometry.christoffel_pos_below hbelow m (by omega) x
  change 0 <
    (y * x ^ (4 : ℕ) * HTGeometry.christoffel s m x * P.derivative.eval x ^ (2 : ℕ)) /
      HTGeometry.monicOrthoNormSq s (m + 1)
  rw [hP]
  positivity

/-- **Exact effectivity interface.** Any positive uniform bound on parabolic hard-root speed
forces an explicit lower bound on shape-normalized terminal mass. Hence terminal-mass extinction
can occur only by velocity nonproperness. -/
theorem xiShiftedCanonicalAdmissionParabolicHardEdgeNormalizedTerminalMass_ge_of_speed_le
    {w : ℝ} (hw : 0 < w) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ (2 : ℕ)))
    (hx0 : x (w ^ (2 : ℕ)) ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds (w ^ (2 : ℕ))]
          fun _ => 0)
    {K : ℝ} (hK : 0 < K)
    (hspeed : 2 * w * (-xdot / (x (w ^ (2 : ℕ))) ^ (2 : ℕ) - 1) ≤ K) :
    (4 * (n : ℝ) * w ^ (3 : ℕ) * (x (w ^ (2 : ℕ))) ^ (2 : ℕ)) / K ≤
      xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ))
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
          (HTGeometry.monicMomentAdmissionPolynomial
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n) (x (w ^ (2 : ℕ))) /
        HTGeometry.monicOrthoNormSq
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n := by
  let V : ℝ := 2 * w * (-xdot / (x (w ^ (2 : ℕ))) ^ (2 : ℕ) - 1)
  let M : ℝ :=
    xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ))
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n) (x (w ^ (2 : ℕ))) /
      HTGeometry.monicOrthoNormSq
        (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) n
  let F : ℝ := 4 * (n : ℝ) * w ^ (3 : ℕ) * (x (w ^ (2 : ℕ))) ^ (2 : ℕ)
  have hroot0 := hroot.eq_of_nhds
  have hM : 0 < M := by
    exact xiShiftedCanonicalAdmissionHardEdgeNormalizedTerminalMass_pos
      (sq_pos_of_pos hw) hn hH hx0 hroot0
  have hVM : V * M = F := by
    exact xiShiftedCanonicalAdmissionParabolicHardEdgeWorldline_mul_normalizedTerminalMass
      hw hn hH hx hx0 hroot
  have hVK : V ≤ K := hspeed
  have hmul : V * M ≤ K * M := mul_le_mul_of_nonneg_right hVK hM.le
  apply (div_le_iff₀ hK).2
  calc
    F = V * M := hVM.symm
    _ ≤ K * M := hmul
    _ = M * K := by ring

/-- On a cofinal parabolic schedule, bounded reciprocal hard displacement leaves a nonzero
worldline forcing. If `n/w → c`, the exact forcing converges to `4c`. -/
theorem tendsto_xiShiftedParabolicHardEdgeWorldlineForcing
    {w u : ℕ → ℝ} {n : ℕ → ℕ} {c : ℝ}
    (hw : ∀ k, w k ≠ 0)
    (hdegree : Tendsto (fun k => (n k : ℝ) / w k) atTop (nhds c))
    (hhard : Tendsto (fun k => u k / (w k) ^ (2 : ℕ)) atTop (nhds 0)) :
    Tendsto
      (fun k => 4 * (n k : ℝ) * (w k) ^ (3 : ℕ) *
        (((w k) ^ (2 : ℕ) + u k)⁻¹) ^ (2 : ℕ))
      atTop (nhds (4 * c)) := by
  have hdenom : Tendsto (fun k => 1 + u k / (w k) ^ (2 : ℕ)) atTop (nhds 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hhard)
  have hinv : Tendsto (fun k => (1 + u k / (w k) ^ (2 : ℕ))⁻¹)
      atTop (nhds 1) := by
    simpa only [inv_one] using hdenom.inv₀ one_ne_zero
  have hnode : Tendsto
      (fun k => (w k) ^ (2 : ℕ) * ((w k) ^ (2 : ℕ) + u k)⁻¹) atTop (nhds 1) := by
    apply hinv.congr'
    filter_upwards with k
    field_simp [hw k]
  have hlimit := (hdegree.mul (hnode.pow 2)).const_mul 4
  have heq : (fun k => 4 * (n k : ℝ) * (w k) ^ (3 : ℕ) *
      (((w k) ^ (2 : ℕ) + u k)⁻¹) ^ (2 : ℕ)) =ᶠ[atTop]
      fun k => 4 * ((n k : ℝ) / w k *
        ((w k) ^ (2 : ℕ) * ((w k) ^ (2 : ℕ) + u k)⁻¹) ^ (2 : ℕ)) := by
    filter_upwards with k
    field_simp [hw k]
  simpa only [one_pow, mul_one] using hlimit.congr' heq.symm

/-- Parabolic coefficient above is derivative of actual square-mass hard coordinate. -/
theorem hasDerivAt_xiShiftedParabolicReciprocalHardRoot
    {w : ℝ} {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot (w ^ (2 : ℕ)))
    (hx0 : x (w ^ (2 : ℕ)) ≠ 0) :
    HasDerivAt (fun v => (x (v ^ (2 : ℕ)))⁻¹ - v ^ (2 : ℕ))
      (2 * w * (-xdot / (x (w ^ (2 : ℕ))) ^ (2 : ℕ) - 1)) w := by
  have hhard := hasDerivAt_reciprocalHardRoot hx hx0
  have hsquare := hasDerivAt_pow 2 w
  have hcomp : HasDerivAt
      ((fun y => (x y)⁻¹ - y) ∘ (fun v : ℝ => v ^ (2 : ℕ)))
      ((-xdot / (x (w ^ (2 : ℕ))) ^ (2 : ℕ) - 1) * ((2 : ℝ) * w ^ (2 - 1))) w :=
    hhard.comp (h := fun v : ℝ => v ^ (2 : ℕ)) w hsquare
  convert hcomp using 1
  · rfl
  · norm_num
    ring

end

end RHTower
