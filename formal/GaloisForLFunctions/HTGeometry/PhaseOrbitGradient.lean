import GaloisForLFunctions.HTGeometry.TorusTranslateDifference
import GaloisForLFunctions.HTGeometry.FiniteMaxGradient

/-!
# The gradient of a phase-orbit overlap score

A phase orbit rotates each component of a fixed family of vectors by its own phase, so the overlap
amplitude with a target is a trigonometric sum whose coordinate derivative is the corresponding
component overlap, scaled by the frequency.  The overlap score is the squared modulus of that
amplitude, so its coordinate derivative is twice the real pairing of the amplitude with the
coordinate derivative of the amplitude.

Consequently the squared gradient of the score is controlled by the amplitude times the sum of the
squared component overlaps, with no dependence on the number of targets.
-/

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section PhaseOrbit

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- The phase-orbit overlap amplitude of a target with a family of vectors. -/
def overlapAmp (u : d → V) (z : V) (x : d → ℝ) : ℂ :=
  ∑ j : d, Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))

/-- The coordinate embedding of the vector model into the complex numbers. -/
def coordCLM (j : d) : (d → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj j)

@[simp] theorem coordCLM_apply (j : d) (v : d → ℝ) : coordCLM j v = (v j : ℂ) := rfl

/-- The derivative of the overlap amplitude. -/
def overlapAmpDeriv (u : d → V) (z : V) (x : d → ℝ) : (d → ℝ) →L[ℝ] ℂ :=
  ∑ j : d, (-(2 * Real.pi * Complex.I) *
    Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))) • coordCLM j

theorem hasFDerivAt_overlapAmp (u : d → V) (z : V) (x : d → ℝ) :
    HasFDerivAt (overlapAmp u z) (overlapAmpDeriv u z x) x := by
  have hterm : ∀ j : d, HasFDerivAt
      (fun y : d → ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * (y j)) * (inner ℂ z (u j)))
      ((-(2 * Real.pi * Complex.I) *
        Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) * (inner ℂ z (u j))) • coordCLM j) x := by
    intro j
    have hlin : HasFDerivAt (fun y : d → ℝ => (-(2 * Real.pi * Complex.I)) * ((y j : ℝ) : ℂ))
        ((-(2 * Real.pi * Complex.I)) • coordCLM j) x :=
      ((coordCLM j).hasFDerivAt).const_mul (-(2 * Real.pi * Complex.I))
    have hexp := hlin.cexp
    have hmul := hexp.mul_const (inner ℂ z (u j))
    refine hmul.congr_fderiv ?_
    ext v
    simp only [smul_apply, coordCLM_apply, smul_eq_mul]
    ring
  have hfun : overlapAmp u z = ∑ i : d, fun y : d → ℝ =>
      Complex.exp (-(2 * Real.pi * Complex.I) * (y i)) * (inner ℂ z (u i)) := by
    funext y
    rw [Finset.sum_apply]
    rfl
  rw [hfun, overlapAmpDeriv]
  exact HasFDerivAt.sum fun j (_ : j ∈ Finset.univ) => hterm j

theorem overlapAmpDeriv_single (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    overlapAmpDeriv u z x (Pi.single j 1) =
      -(2 * Real.pi * Complex.I) * Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) *
        (inner ℂ z (u j)) := by
  rw [overlapAmpDeriv]
  rw [sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [Pi.single_eq_of_ne hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem norm_overlapAmpDeriv_single (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    ‖overlapAmpDeriv u z x (Pi.single j 1)‖ = 2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖ := by
  rw [overlapAmpDeriv_single, norm_mul, norm_mul]
  have hexp : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (x j))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, mul_one]
  congr 1
  simp [abs_of_nonneg Real.pi_pos.le]

/-- The overlap score of a target with the phase orbit. -/
def overlapScore (u : d → V) (z : V) (x : d → ℝ) : ℝ := ‖overlapAmp u z x‖ ^ 2

theorem hasFDerivAt_overlapScore (u : d → V) (z : V) (x : d → ℝ) :
    HasFDerivAt (overlapScore u z)
      ((2 : ℕ) • (innerSL ℝ (overlapAmp u z x)).comp (overlapAmpDeriv u z x)) x :=
  (hasFDerivAt_overlapAmp u z x).norm_sq

theorem differentiable_overlapScore (u : d → V) (z : V) :
    Differentiable ℝ (overlapScore u z) :=
  fun x => (hasFDerivAt_overlapScore u z x).differentiableAt

theorem abs_fderiv_overlapScore_single_le (u : d → V) (z : V) (x : d → ℝ) (j : d) :
    |fderiv ℝ (overlapScore u z) x (Pi.single j 1)| ≤
      2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖) := by
  rw [(hasFDerivAt_overlapScore u z x).fderiv]
  have hval : ((2 : ℕ) • (innerSL ℝ (overlapAmp u z x)).comp (overlapAmpDeriv u z x))
      (Pi.single j 1) =
      2 * (inner ℝ (overlapAmp u z x) (overlapAmpDeriv u z x (Pi.single j 1))) := by
    simp [smul_apply, real_inner_eq_re_inner]
    ring
  rw [hval, abs_mul]
  have hcs : |(inner ℝ (overlapAmp u z x) (overlapAmpDeriv u z x (Pi.single j 1)) : ℝ)| ≤
      ‖overlapAmp u z x‖ * ‖overlapAmpDeriv u z x (Pi.single j 1)‖ :=
    abs_real_inner_le_norm _ _
  rw [norm_overlapAmpDeriv_single] at hcs
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2, mul_assoc]
  exact mul_le_mul_of_nonneg_left hcs (by norm_num)

/-- **Squared gradient of one overlap score.**  The squared coordinate gradient of the score is
controlled by the squared amplitude times the squared component overlaps. -/
theorem sum_sq_fderiv_overlapScore_le (u : d → V) (z : V) (x : d → ℝ) {p : ℝ}
    (hA : ‖overlapAmp u z x‖ ≤ 1)
    (hc : ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 ≤ p) :
    ∑ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
      16 * Real.pi ^ 2 * p := by
  have hterm : ∀ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
      16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := by
    intro j
    have habs := abs_fderiv_overlapScore_single_le u z x j
    have hnn : (0 : ℝ) ≤ 2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖) := by
      have := Real.pi_pos
      positivity
    have hsq : (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2 ≤
        (2 * ‖overlapAmp u z x‖ * (2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    refine le_trans hsq ?_
    have hA0 : (0 : ℝ) ≤ ‖overlapAmp u z x‖ := norm_nonneg _
    have hcj : (0 : ℝ) ≤ ‖(inner ℂ z (u j) : ℂ)‖ := norm_nonneg _
    have hpi : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
    have hA2 : ‖overlapAmp u z x‖ ^ 2 ≤ 1 := by nlinarith [hA0, hA]
    have hprod : 16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 * ‖overlapAmp u z x‖ ^ 2 ≤
        16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hA2 (by positivity)
    nlinarith [hprod]
  calc ∑ j : d, (fderiv ℝ (overlapScore u z) x (Pi.single j 1)) ^ 2
      ≤ ∑ j : d, 16 * Real.pi ^ 2 * ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := Finset.sum_le_sum fun j _ =>
        hterm j
    _ = 16 * Real.pi ^ 2 * ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 16 * Real.pi ^ 2 * p := by
        refine mul_le_mul_of_nonneg_left hc ?_
        have := Real.pi_pos
        positivity

section CompleteScore

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- The complete-dictionary incidence score of a finite target family. -/
def completeScore (u : d → V) (z : Z → V) : (d → ℝ) → ℝ :=
  finiteMax fun w => overlapScore u (z w)

/-- **Squared gradient of the complete incidence score.**  At every point of differentiability the
complete maximum inherits the single-target gradient bound. -/
theorem sum_sq_fderiv_completeScore_le (u : d → V) (z : Z → V) (x : d → ℝ) {p : ℝ}
    (hdiff : DifferentiableAt ℝ (completeScore u z) x)
    (hA : ∀ w : Z, ‖overlapAmp u (z w) x‖ ≤ 1)
    (hc : ∀ w : Z, ∑ j : d, ‖(inner ℂ (z w) (u j) : ℂ)‖ ^ 2 ≤ p) :
    ∑ j : d, (fderiv ℝ (completeScore u z) x (Pi.single j 1)) ^ 2 ≤ 16 * Real.pi ^ 2 * p := by
  obtain ⟨w, hw⟩ := exists_fderiv_finiteMax_eq
    (X := fun w : Z => overlapScore u (z w))
    (fun w => (differentiable_overlapScore u (z w)) x) hdiff
  have hrw : ∀ j : d, fderiv ℝ (completeScore u z) x (Pi.single j 1) =
      fderiv ℝ (overlapScore u (z w)) x (Pi.single j 1) := by
    intro j
    rw [completeScore, hw]
  rw [Finset.sum_congr rfl fun j _ => by rw [hrw j]]
  exact sum_sq_fderiv_overlapScore_le u (z w) x (hA w) (hc w)

/-- **Squared gradient of a Lipschitz reporter of the complete score.** -/
theorem sum_sq_fderiv_reporter_le (u : d → V) (z : Z → V) (x : d → ℝ) {p r : ℝ}
    (hr : 0 ≤ r) {B : ℝ → ℝ} {B' : ℝ}
    (hB : HasDerivAt B B' (completeScore u z x)) (hB' : |B'| ≤ r)
    (hdiff : DifferentiableAt ℝ (completeScore u z) x)
    (hA : ∀ w : Z, ‖overlapAmp u (z w) x‖ ≤ 1)
    (hc : ∀ w : Z, ∑ j : d, ‖(inner ℂ (z w) (u j) : ℂ)‖ ^ 2 ≤ p) :
    ∑ j : d, (fderiv ℝ (fun y => B (completeScore u z y)) x (Pi.single j 1)) ^ 2 ≤
      r ^ 2 * (16 * Real.pi ^ 2 * p) := by
  have hcomp : HasFDerivAt (fun y => B (completeScore u z y))
      (B' • fderiv ℝ (completeScore u z) x) x := by
    exact hB.comp_hasFDerivAt x hdiff.hasFDerivAt
  have hval : ∀ j : d, fderiv ℝ (fun y => B (completeScore u z y)) x (Pi.single j 1) =
      B' * fderiv ℝ (completeScore u z) x (Pi.single j 1) := by
    intro j
    rw [hcomp.fderiv]
    simp [smul_apply]
  have hbase := sum_sq_fderiv_completeScore_le u z x hdiff hA hc
  have hnn : (0 : ℝ) ≤ ∑ j : d, (fderiv ℝ (completeScore u z) x (Pi.single j 1)) ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : ∀ j : d, (fderiv ℝ (fun y => B (completeScore u z y)) x (Pi.single j 1)) ^ 2 =
      B' ^ 2 * (fderiv ℝ (completeScore u z) x (Pi.single j 1)) ^ 2 := by
    intro j
    rw [hval j, mul_pow]
  rw [Finset.sum_congr rfl fun j _ => hsq j, ← Finset.mul_sum]
  have hB2 : B' ^ 2 ≤ r ^ 2 := by
    have := abs_nonneg B'
    nlinarith [hB', sq_abs B']
  calc B' ^ 2 * ∑ j : d, (fderiv ℝ (completeScore u z) x (Pi.single j 1)) ^ 2
      ≤ r ^ 2 * ∑ j : d, (fderiv ℝ (completeScore u z) x (Pi.single j 1)) ^ 2 :=
        mul_le_mul_of_nonneg_right hB2 hnn
    _ ≤ r ^ 2 * (16 * Real.pi ^ 2 * p) := by
        refine mul_le_mul_of_nonneg_left hbase ?_
        positivity

end CompleteScore

section Bessel

/-- **Component-overlap budget.**  For a pairwise orthogonal family with squared norms at most `p`,
the squared component overlaps of a unit target sum to at most `p`. -/
theorem sum_sq_inner_le_of_orthogonal [DecidableEq V] {u : d → V}
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : ∀ j : d, ‖u j‖ ^ 2 ≤ p) (z : V) (hz : ‖z‖ ≤ 1) :
    ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 ≤ p := by
  classical
  set S : Finset d := Finset.univ.filter fun j => u j ≠ 0 with hS
  have hzero : ∀ j ∈ Finset.univ \ S, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 = 0 := by
    intro j hj
    have hj' : ¬ (u j ≠ 0) := by
      have := Finset.mem_sdiff.mp hj
      simpa [hS] using this.2
    have hu : u j = 0 := by
      by_contra hc
      exact hj' hc
    rw [hu]
    simp
  have hsplit : ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 =
      ∑ j ∈ S, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro j _ hj
    have hj' : j ∈ Finset.univ \ S := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    exact hzero j hj'
  have hnorm : ∀ j ∈ S, u j ≠ 0 := by
    intro j hj
    simpa [hS] using (Finset.mem_filter.mp hj).2
  have horthonormal : Orthonormal ℂ fun j : S => ((‖u (j : d)‖⁻¹ : ℝ) : ℂ) • u (j : d) := by
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hij : i = j
    · subst hij
      have hne := hnorm (i : d) i.2
      have hpos : (0 : ℝ) < ‖u (i : d)‖ := norm_pos_iff.mpr hne
      rw [inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ), if_pos rfl,
        Complex.conj_ofReal]
      have hne0 : ((‖u (i : d)‖ : ℝ) : ℂ) ≠ 0 := by
        simpa using hpos.ne'
      push_cast
      field_simp
      norm_cast
    · have hij' : (i : d) ≠ (j : d) := fun hc => hij (Subtype.ext hc)
      rw [inner_smul_left, inner_smul_right, horth _ _ hij', if_neg hij]
      simp
  have hbessel := horthonormal.sum_inner_products_le (s := Finset.univ) (x := z)
  have hterm : ∀ j : S, ‖(inner ℂ z (u (j : d)) : ℂ)‖ ^ 2 ≤
      p * ‖(inner ℂ (((‖u (j : d)‖⁻¹ : ℝ) : ℂ) • u (j : d)) z : ℂ)‖ ^ 2 := by
    intro j
    have hne := hnorm (j : d) j.2
    have hpos : (0 : ℝ) < ‖u (j : d)‖ := norm_pos_iff.mpr hne
    have hval : ‖(inner ℂ (((‖u (j : d)‖⁻¹ : ℝ) : ℂ) • u (j : d)) z : ℂ)‖ =
        ‖u (j : d)‖⁻¹ * ‖(inner ℂ z (u (j : d)) : ℂ)‖ := by
      rw [inner_smul_left, norm_mul, Complex.conj_ofReal, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      congr 1
      rw [← inner_conj_symm, RCLike.norm_conj]
    rw [hval, mul_pow, ← mul_assoc]
    have hsq : ‖u (j : d)‖ ^ 2 ≤ p := hp (j : d)
    have hinv : ((‖u (j : d)‖⁻¹) : ℝ) ^ 2 = (‖u (j : d)‖ ^ 2)⁻¹ := by rw [← inv_pow]
    have hsqpos : (0 : ℝ) < ‖u (j : d)‖ ^ 2 := by positivity
    have hnn : (0 : ℝ) ≤ ‖(inner ℂ z (u (j : d)) : ℂ)‖ ^ 2 := sq_nonneg _
    rw [hinv]
    have hfrac : (1 : ℝ) ≤ p * (‖u (j : d)‖ ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ hsqpos, one_mul]
      exact hsq
    nlinarith [hfrac, hnn]
  have hcoe : ∑ j ∈ S, ‖(inner ℂ z (u j) : ℂ)‖ ^ 2 =
      ∑ j : S, ‖(inner ℂ z (u (j : d)) : ℂ)‖ ^ 2 := (Finset.sum_coe_sort S _).symm
  rw [hsplit, hcoe]
  calc ∑ j : S, ‖(inner ℂ z (u (j : d)) : ℂ)‖ ^ 2
      ≤ ∑ j : S, p * ‖(inner ℂ (((‖u (j : d)‖⁻¹ : ℝ) : ℂ) • u (j : d)) z : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = p * ∑ j : S, ‖(inner ℂ (((‖u (j : d)‖⁻¹ : ℝ) : ℂ) • u (j : d)) z : ℂ)‖ ^ 2 := by
        rw [← Finset.mul_sum]
    _ ≤ p * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel hp0
    _ ≤ p := by
        have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hz]
        nlinarith [hz2, hp0]

end Bessel

end PhaseOrbit

end GaloisForLFunctions.HTGeometry
