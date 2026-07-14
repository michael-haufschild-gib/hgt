import GaloisForLFunctions.RHTower.PrimeArchBernsteinPencil

/-!
# Exponential phase selection for the prime--Gamma Bernstein pencil

The endpoint Bernstein coefficient vector is an entirely source-defined object.  This file
develops the exponential-separation mechanism that distinguishes its RH phase from its off-line
phase.  The geometric input is elementary: every nonreal normalized reciprocal-square coordinate
has a unit-disk direction in which its affine Bernstein base has modulus strictly larger than one.
-/

open Filter Topology Complex
open scoped BigOperators Polynomial

namespace RHTower

noncomputable section

/-- Unit-circle phase aligning `u * w` with `1 - u`. -/
def bernsteinEllipsePhase (u : ℂ) : ℂ :=
  (starRingEnd ℂ u) / (‖u‖ : ℂ) * ((1 - u) / (‖1 - u‖ : ℂ))

lemma bernsteinEllipsePhase_norm_eq_one {u : ℂ} (him : u.im ≠ 0) :
    ‖bernsteinEllipsePhase u‖ = 1 := by
  have hu : u ≠ 0 := by
    intro h
    rw [h] at him
    exact him rfl
  have hsub : 1 - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    rw [hu1] at him
    exact him rfl
  rw [bernsteinEllipsePhase, norm_mul, norm_div, norm_div,
    norm_conj, Complex.norm_real, Complex.norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u), abs_of_nonneg (norm_nonneg (1 - u))]
  field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hsub]

/-- A nonreal point lies strictly outside the degenerate focal segment: the sum of its distances
from `0` and `1` is greater than one. -/
lemma one_lt_norm_add_norm_one_sub {u : ℂ} (him : u.im ≠ 0) :
    1 < ‖u‖ + ‖1 - u‖ := by
  have hnormSq : u.re ^ 2 < ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_pos_of_ne_zero him]
  have hstrict : |u.re| < ‖u‖ := by
    nlinarith [sq_abs u.re, norm_nonneg u, abs_nonneg u.re]
  have hother : |1 - u.re| ≤ ‖1 - u‖ := by
    simpa only [sub_re, one_re] using abs_re_le_norm (1 - u)
  have hone : 1 ≤ |u.re| + |1 - u.re| := by
    have := abs_add_le u.re (1 - u.re)
    norm_num at this ⊢
    linarith
  linarith

/-- **Strict Bernstein ellipse direction.** Every nonreal normalized coordinate admits a unit
phase for which its affine Bernstein base has modulus `‖u‖ + ‖1-u‖ > 1`. -/
theorem exists_unit_bernsteinBase_norm_gt_one_of_im_ne_zero
    {u : ℂ} (him : u.im ≠ 0) :
    ∃ w : ℂ, ‖w‖ = 1 ∧
      ‖1 - u + u * w‖ = ‖1 - u‖ + ‖u‖ ∧
      1 < ‖1 - u + u * w‖ := by
  let w := bernsteinEllipsePhase u
  have hnorm : ‖1 - u + u * w‖ = ‖1 - u‖ + ‖u‖ := by
    have hu : u ≠ 0 := by
      intro h
      rw [h] at him
      exact him rfl
    have hsub : 1 - u ≠ 0 := by
      intro h
      have hu1 : u = 1 := (sub_eq_zero.mp h).symm
      rw [hu1] at him
      exact him rfl
    have halign :
        u * w = ((‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) := by
      dsimp only [w, bernsteinEllipsePhase]
      rw [show u * ((starRingEnd ℂ u / (‖u‖ : ℂ)) *
          ((1 - u) / (‖1 - u‖ : ℂ))) =
          (u * starRingEnd ℂ u / (‖u‖ : ℂ)) *
            ((1 - u) / (‖1 - u‖ : ℂ)) by ring]
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp [norm_ne_zero_iff.mpr hu, norm_ne_zero_iff.mpr hsub]
    rw [halign]
    rw [show 1 - u + ((‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) =
        (((1 : ℝ) + ‖u‖ / ‖1 - u‖ : ℝ) : ℂ) * (1 - u) by
          push_cast
          ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    · field_simp [norm_ne_zero_iff.mpr hsub]
    · have : 0 < ‖1 - u‖ := norm_pos_iff.mpr hsub
      positivity
  refine ⟨w, bernsteinEllipsePhase_norm_eq_one him, hnorm, ?_⟩
  rw [hnorm]
  simpa [add_comm] using one_lt_norm_add_norm_one_sub him

end

end RHTower

namespace RHTower

noncomputable section

/-- A nonnegative sequence is subexponential when it vanishes after normalization by every
strictly exponential scale. This root-free formulation is the one needed by the Bernstein
pencil. -/
def SubexponentialAtNatInfinity (a : ℕ → ℝ) : Prop :=
  ∀ r : ℝ, 1 < r → Tendsto (fun n : ℕ => a n / r ^ n) atTop (nhds 0)

/-- The affine mode attached to one reciprocal-square divisor copy in the Bernstein pencil. -/
def xiBernsteinAffineBase (R : ℝ) (w : ℂ) (q : XiZeroCopy) : ℂ :=
  1 - xiZeroCopyReciprocalSquare q / (R : ℂ) +
    (xiZeroCopyReciprocalSquare q / (R : ℂ)) * w

/-- The affine Bernstein modes converge cofinally to the neutral base `1`. -/
theorem xiBernsteinAffineBase_tendsto_cofinite_one
    (R : ℝ) (w : ℂ) :
    Tendsto (xiBernsteinAffineBase R w) cofinite (nhds 1) := by
  have hzero : Tendsto xiZeroCopyReciprocalSquare cofinite (nhds 0) :=
    summable_xiZeroCopyReciprocalSquare.tendsto_cofinite_zero
  have hscaled : Tendsto
      (fun q : XiZeroCopy => xiZeroCopyReciprocalSquare q / (R : ℂ))
      cofinite (nhds 0) := by
    simpa using hzero.div_const (R : ℂ)
  have hone : Tendsto (fun _ : XiZeroCopy => (1 : ℂ)) cofinite (nhds 1) :=
    tendsto_const_nhds
  have h := (hone.sub hscaled).add (hscaled.mul_const w)
  simpa only [xiBernsteinAffineBase, zero_mul, sub_zero, add_zero] using h

/-- Above every threshold larger than one, only finitely many affine Bernstein modes remain. -/
theorem xiBernsteinAffineBase_finite_norm_ge
    (R : ℝ) (w : ℂ) {a : ℝ} (ha : 1 < a) :
    {q : XiZeroCopy | a ≤ ‖xiBernsteinAffineBase R w q‖}.Finite := by
  have hevent : ∀ᶠ q : XiZeroCopy in cofinite,
      ‖xiBernsteinAffineBase R w q‖ < a :=
    (xiBernsteinAffineBase_tendsto_cofinite_one R w).norm.eventually_lt_const
      (by simpa using ha)
  rw [Filter.eventually_cofinite] at hevent
  simpa only [not_lt] using hevent

/-- At nonzero scale and nontrivial phase, the affine Bernstein base determines its
reciprocal-square coefficient. -/
theorem xiBernsteinAffineBase_eq_iff
    {R : ℝ} (hR : R ≠ 0) {w : ℂ} (hw : w ≠ 1) (q q' : XiZeroCopy) :
    xiBernsteinAffineBase R w q = xiBernsteinAffineBase R w q' ↔
      xiZeroCopyReciprocalSquare q = xiZeroCopyReciprocalSquare q' := by
  constructor
  · intro h
    have hprod :
        (xiZeroCopyReciprocalSquare q - xiZeroCopyReciprocalSquare q') *
          (w - 1) = 0 := by
      dsimp only [xiBernsteinAffineBase] at h
      field_simp [hR] at h
      linear_combination h
    have hdiff := (mul_eq_zero.mp hprod).resolve_right (sub_ne_zero.mpr hw)
    exact sub_eq_zero.mp hdiff
  · intro h
    simp only [xiBernsteinAffineBase, h]

/-- Failure of RH supplies an actual multiplicity copy with nonreal reciprocal-square
coordinate. -/
theorem exists_xiZeroCopyReciprocalSquare_im_ne_zero_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) :
    ∃ q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).im ≠ 0 := by
  have hright : ¬ ∀ s : ℂ, s ∈ rightHalf → xi s ≠ 0 := by
    exact hRH ∘ rh_iff_xi_ne_zero_right.mpr
  push Not at hright
  obtain ⟨s, hs, hzero⟩ := hright
  let ρ : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support ρ
  have hnat : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hnat⟩⟩
  refine ⟨q, ?_⟩
  rw [xiZeroCopyReciprocalSquare_eq]
  intro him
  have hre := (xiCentralReciprocalSquare_im_eq_zero_iff ρ).mp him
  have hgt := mem_rightHalf.mp hs
  dsimp only [ρ] at hre
  linarith

end

end RHTower
