import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCenteredSourceDegreeCapital
import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw

/-!
# Shifted-Xi centered-source saddle flow

Canonical degree renewal and continuous mass transport move the literal centered source in
opposite directions. Outer interlacing raises pre-reporting centered residue at fixed mass, while
hard-root worldline conservation forces that residue to decrease along every positive super-apex
root branch.
-/

open Matrix

namespace RHTower

noncomputable section

/-- Positive normalized terminal mass turns exact worldline conservation into strict forward
motion of reciprocal hard coordinate. -/
theorem xiShiftedCanonicalAdmissionHardEdgeWorldlineVelocity_pos
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) (hx0 : x y ≠ 0)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0) :
    0 < -xdot / (x y) ^ (2 : ℕ) - 1 := by
  let M :=
    xiShiftedHardEdgeGaussTerminalMass y
        (fun k => (xiShiftedReciprocalMoment y k).re) n
        (HTGeometry.monicMomentAdmissionPolynomial
          (fun k => (xiShiftedReciprocalMoment y k).re) n) (x y) /
      HTGeometry.monicOrthoNormSq
        (fun k => (xiShiftedReciprocalMoment y k).re) n
  have hM : 0 < M := by
    exact xiShiftedCanonicalAdmissionHardEdgeNormalizedTerminalMass_pos
      hy hn hH hx0 hroot.eq_of_nhds
  have hworld :=
    xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_normalizedTerminalMass
      hy hn hH hx hx0 hroot
  have hprod : 0 < (-xdot / (x y) ^ (2 : ℕ) - 1) * M := by
    rw [show (-xdot / (x y) ^ (2 : ℕ) - 1) * M =
        2 * (n : ℝ) * y * (x y) ^ (2 : ℕ) by simpa only [M] using hworld]
    positivity
  rcases (mul_pos_iff.mp hprod) with hpositive | hnegative
  · exact hpositive.1
  · exact (not_lt_of_ge hM.le hnegative.2).elim

/-- Exact derivative of moving-apex centered residue along any differentiable root curve. -/
theorem hasDerivAt_movingApexCenteredRootResidue
    {y : ℝ} {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y) :
    HasDerivAt (fun v => (v * x v) ^ (2 : ℕ) - 1)
      (2 * (y * x y) * (x y + y * xdot)) y := by
  have hproduct := (hasDerivAt_id y).mul hx
  have hsquare := hproduct.pow 2
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y :=
    hasDerivAt_const y (1 : ℝ)
  convert hsquare.sub hconst using 1 <;> try rfl
  simp only [Pi.mul_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    one_mul, sub_zero]

/-- **Strict continuous source discharge.** On every positive super-apex canonical root branch,
the moving-apex centered completed-source residue has strictly negative mass derivative. -/
theorem movingApexCenteredRootResidue_deriv_neg_of_superApex
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hxpos : 0 < x y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0)
    (hsuper : 1 < y * x y) :
    2 * (y * x y) * (x y + y * xdot) < 0 := by
  have hvelocity := xiShiftedCanonicalAdmissionHardEdgeWorldlineVelocity_pos
    hy hn hH hx hxpos.ne' hroot
  have hxSq : 0 < (x y) ^ (2 : ℕ) := sq_pos_of_ne_zero hxpos.ne'
  have hratio : 1 < -xdot / (x y) ^ (2 : ℕ) := by linarith
  have hxdotNeg : xdot < -(x y) ^ (2 : ℕ) := by
    have hsquare_lt : (x y) ^ (2 : ℕ) < -xdot := by
      have := (lt_div_iff₀ hxSq).mp hratio
      simpa only [one_mul] using this
    linarith
  have hyxdot : y * xdot < y * (-(x y) ^ (2 : ℕ)) :=
    mul_lt_mul_of_pos_left hxdotNeg hy
  have hqdot : x y + y * xdot < 0 := by
    have hfirst : x y + y * xdot < x y + y * (-(x y) ^ (2 : ℕ)) := by
      simpa only [add_comm] using add_lt_add_left hyxdot (x y)
    have hsecond : x y + y * (-(x y) ^ (2 : ℕ)) < 0 := by
      calc
        x y + y * (-(x y) ^ (2 : ℕ)) = x y * (1 - y * x y) := by ring
        _ < 0 := mul_neg_of_pos_of_neg hxpos (sub_neg.mpr hsuper)
    exact hfirst.trans hsecond
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (mul_pos hy hxpos)) hqdot

/-- The exact centered-residue curve has a negative derivative on a super-apex root worldline. -/
theorem hasDerivAt_movingApexCenteredRootResidue_neg_of_superApex
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hxpos : 0 < x y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0)
    (hsuper : 1 < y * x y) :
    ∃ rdot : ℝ, rdot < 0 ∧
      HasDerivAt (fun v => (v * x v) ^ (2 : ℕ) - 1) rdot y := by
  let rdot := 2 * (y * x y) * (x y + y * xdot)
  exact ⟨rdot,
    movingApexCenteredRootResidue_deriv_neg_of_superApex
      hy hn hH hx hxpos hroot hsuper,
    hasDerivAt_movingApexCenteredRootResidue hx⟩

/-- **Literal source saddle law.** Current de-resisted completed-source value is the moving-apex
residue whose continuous mass derivative is negative on a super-apex root branch. -/
theorem xiShiftedCanonicalAdmissionCenteredSourceResidue_eq_and_hasDerivAt_neg_of_superApex
    {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 0 < n)
    (hH : (HTGeometry.momentHankelMatrix
      (fun k => (xiShiftedReciprocalMoment y k).re) (n + 2)).PosDef)
    {x : ℝ → ℝ} {xdot : ℝ} (hx : HasDerivAt x xdot y)
    (hxpos : 0 < x y)
    (hroot : (fun v =>
      (HTGeometry.monicMomentAdmissionPolynomial
        (fun k => (xiShiftedReciprocalMoment v k).re) n).eval (x v)) =ᶠ[nhds y]
          fun _ => 0)
    (hsuper : 1 < y * x y) :
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue
        (Real.sqrt y) n (x y) = (y * x y) ^ (2 : ℕ) - 1 ∧
      ∃ rdot : ℝ, rdot < 0 ∧
        HasDerivAt (fun v => (v * x v) ^ (2 : ℕ) - 1) rdot y := by
  have hsquare : (Real.sqrt y) ^ (2 : ℕ) = y := Real.sq_sqrt hy.le
  have hs : xiShiftedRealMomentSequence (Real.sqrt y) =
      (fun k => (xiShiftedReciprocalMoment y k).re) := by
    funext k
    simp only [xiShiftedRealMomentSequence, hsquare]
  have hHsqrt : (HTGeometry.momentHankelMatrix
      (xiShiftedRealMomentSequence (Real.sqrt y)) (n + 2)).PosDef := by
    simpa only [hs] using hH
  have hrootSqrt :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence (Real.sqrt y)) n).eval (x y) = 0 := by
    simpa only [hs] using hroot.eq_of_nhds
  have hvalue :=
    xiShiftedCanonicalAdmissionCenteredDeResistedCompletedSourceResidue_eq
      hn (Real.sqrt_ne_zero'.mpr hy) hHsqrt hxpos.ne' hrootSqrt
  refine ⟨?_, hasDerivAt_movingApexCenteredRootResidue_neg_of_superApex
    hy hn hH hx hxpos hroot hsuper⟩
  simpa only [hsquare] using hvalue

end

end RHTower
