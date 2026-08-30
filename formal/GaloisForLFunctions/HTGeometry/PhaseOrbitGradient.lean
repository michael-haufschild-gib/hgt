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

local instance phaseOrbitGradientLocalInst1 : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance phaseOrbitGradientLocalInst2 :
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance phaseOrbitGradientLocalInst3 :
    MeasureTheory.IsProbabilityMeasure (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

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

section Amplitude

/-- The phase orbit of a family of vectors. -/
def phaseOrbit (u : d → V) (x : d → ℝ) : V :=
  ∑ j : d, Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) • u j

theorem overlapAmp_eq_inner (u : d → V) (z : V) (x : d → ℝ) :
    overlapAmp u z x = inner ℂ z (phaseOrbit u x) := by
  rw [phaseOrbit, inner_sum, overlapAmp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_right]

/-- Pythagoras for a pairwise orthogonal finite family. -/
theorem norm_sq_sum_of_orthogonal {v : d → V}
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (v i) (v j) : ℂ) = 0) :
    ‖∑ j : d, v j‖ ^ 2 = ∑ j : d, ‖v j‖ ^ 2 := by
  classical
  have hexpand : (inner ℂ (∑ i : d, v i) (∑ j : d, v j) : ℂ) =
      ∑ i : d, ∑ j : d, (inner ℂ (v i) (v j) : ℂ) := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ => inner_sum _ _ _
  have hdiag : ∀ i : d, (∑ j : d, (inner ℂ (v i) (v j) : ℂ)) = (inner ℂ (v i) (v i) : ℂ) := by
    intro i
    refine Finset.sum_eq_single i (fun j _ hj => horth i j (Ne.symm hj)) ?_
    intro hi
    exact absurd (Finset.mem_univ i) hi
  have hinner : (inner ℂ (∑ i : d, v i) (∑ j : d, v j) : ℂ) =
      ∑ i : d, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hexpand, Finset.sum_congr rfl fun i _ => hdiag i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  have hnorm : ((‖∑ j : d, v j‖ ^ 2 : ℝ) : ℂ) = ∑ i : d, ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hinner, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  have hcast : ((‖∑ j : d, v j‖ ^ 2 : ℝ) : ℂ) = (((∑ i : d, ‖v i‖ ^ 2 : ℝ)) : ℂ) := by
    rw [hnorm]
    push_cast
    rfl
  exact_mod_cast hcast

theorem norm_phaseOrbit_sq (u : d → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) (x : d → ℝ) :
    ‖phaseOrbit u x‖ ^ 2 = ∑ j : d, ‖u j‖ ^ 2 := by
  have horth' : ∀ i j : d, i ≠ j →
      (inner ℂ (Complex.exp (-(2 * Real.pi * Complex.I) * (x i)) • u i)
        (Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) • u j) : ℂ) = 0 := by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, horth i j hij]
    ring
  rw [phaseOrbit, norm_sq_sum_of_orthogonal horth']
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_smul, Complex.norm_exp]
  simp

/-- **The overlap amplitude of a unit target with a subunit orbit is at most one.** -/
theorem norm_overlapAmp_le_one (u : d → V) (z : V) (x : d → ℝ)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖overlapAmp u z x‖ ≤ 1 := by
  rw [overlapAmp_eq_inner]
  refine le_trans (norm_inner_le_norm (𝕜 := ℂ) z (phaseOrbit u x)) ?_
  have hpsi : ‖phaseOrbit u x‖ ^ 2 ≤ 1 := by
    rw [norm_phaseOrbit_sq u horth x]
    exact hu
  have hpsi' : ‖phaseOrbit u x‖ ≤ 1 := by
    nlinarith [norm_nonneg (phaseOrbit u x), hpsi]
  nlinarith [norm_nonneg z, norm_nonneg (phaseOrbit u x), hz, hpsi']

end Amplitude

section Lipschitz

theorem norm_exp_line_sub_le (a b : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I) * a) -
      Complex.exp (-(2 * Real.pi * Complex.I) * b)‖ ≤ 2 * Real.pi * |a - b| := by
  have hderiv : ∀ t ∈ Set.uIcc b a, HasDerivAt
      (fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * s))
      ((-(2 * Real.pi * Complex.I)) * Complex.exp (-(2 * Real.pi * Complex.I) * t)) t := by
    intro t _
    have hlin : HasDerivAt (fun s : ℝ => (-(2 * Real.pi * Complex.I)) * (s : ℂ))
        (-(2 * Real.pi * Complex.I)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul
        (-(2 * Real.pi * Complex.I))
    have := hlin.cexp
    simpa [mul_comm] using this
  have hbound : ∀ t ∈ Set.uIcc b a,
      ‖(-(2 * Real.pi * Complex.I)) * Complex.exp (-(2 * Real.pi * Complex.I) * t)‖ ≤
        2 * Real.pi := by
    intro t _
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(2 * Real.pi * Complex.I) * (t : ℂ)).re = 0 := by
      simp
    rw [hre, Real.exp_zero, mul_one]
    simp [abs_of_nonneg Real.pi_pos.le]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s : ℝ => Complex.exp (-(2 * Real.pi * Complex.I) * s))
    (f' := fun t : ℝ => (-(2 * Real.pi * Complex.I)) * Complex.exp (-(2 * Real.pi * Complex.I) * t))
    (C := 2 * Real.pi) (fun t ht => (hderiv t ht).hasDerivWithinAt) hbound (convex_uIcc b a)
    Set.right_mem_uIcc Set.left_mem_uIcc
  rw [Real.norm_eq_abs] at h
  rw [← norm_neg, ← abs_neg]
  simpa [neg_sub] using h

theorem norm_overlapAmp_sub_le (u : d → V) (z : V) (x y : d → ℝ) :
    ‖overlapAmp u z x - overlapAmp u z y‖ ≤
      2 * Real.pi * (∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖) * ‖x - y‖ := by
  have hsub : overlapAmp u z x - overlapAmp u z y =
      ∑ j : d, (Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) -
        Complex.exp (-(2 * Real.pi * Complex.I) * (y j))) * (inner ℂ z (u j)) := by
    rw [overlapAmp, overlapAmp, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ j : d, ‖(Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) -
      Complex.exp (-(2 * Real.pi * Complex.I) * (y j))) * (inner ℂ z (u j))‖ ≤
      2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖ * ‖x - y‖ := by
    intro j
    rw [norm_mul]
    have hxy : |x j - y j| ≤ ‖x - y‖ := by
      have := norm_le_pi_norm (x - y) j
      simpa [Real.norm_eq_abs] using this
    have hexp := norm_exp_line_sub_le (x j) (y j)
    have hc : (0 : ℝ) ≤ ‖(inner ℂ z (u j) : ℂ)‖ := norm_nonneg _
    have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc ‖Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) -
          Complex.exp (-(2 * Real.pi * Complex.I) * (y j))‖ * ‖(inner ℂ z (u j) : ℂ)‖
        ≤ (2 * Real.pi * |x j - y j|) * ‖(inner ℂ z (u j) : ℂ)‖ :=
          mul_le_mul_of_nonneg_right hexp hc
      _ ≤ (2 * Real.pi * ‖x - y‖) * ‖(inner ℂ z (u j) : ℂ)‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hc
          exact mul_le_mul_of_nonneg_left hxy hpi
      _ = 2 * Real.pi * ‖(inner ℂ z (u j) : ℂ)‖ * ‖x - y‖ := by ring
  refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
  rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem norm_overlapScore_sub_le (u : d → V) (z : V) (x y : d → ℝ)
    (hA : ∀ w : d → ℝ, ‖overlapAmp u z w‖ ≤ 1) :
    |overlapScore u z x - overlapScore u z y| ≤
      4 * Real.pi * (∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖) * ‖x - y‖ := by
  have hamp := norm_overlapAmp_sub_le u z x y
  have hax := hA x
  have hay := hA y
  have hfactor : |overlapScore u z x - overlapScore u z y| ≤
      2 * ‖overlapAmp u z x - overlapAmp u z y‖ := by
    have hid : overlapScore u z x - overlapScore u z y =
        (‖overlapAmp u z x‖ - ‖overlapAmp u z y‖) *
          (‖overlapAmp u z x‖ + ‖overlapAmp u z y‖) := by
      rw [overlapScore, overlapScore]
      ring
    rw [hid, abs_mul]
    have h1 : |‖overlapAmp u z x‖ - ‖overlapAmp u z y‖| ≤
        ‖overlapAmp u z x - overlapAmp u z y‖ := abs_norm_sub_norm_le _ _
    have h2 : |‖overlapAmp u z x‖ + ‖overlapAmp u z y‖| ≤ 2 := by
      rw [abs_of_nonneg (by positivity)]
      linarith
    have h3 : (0 : ℝ) ≤ |‖overlapAmp u z x‖ - ‖overlapAmp u z y‖| := abs_nonneg _
    have h4 : (0 : ℝ) ≤ ‖overlapAmp u z x - overlapAmp u z y‖ := norm_nonneg _
    nlinarith [h1, h2, h3, h4]
  refine le_trans hfactor ?_
  have hc : (0 : ℝ) ≤ ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ :=
    Finset.sum_nonneg fun j _ => norm_nonneg _
  calc 2 * ‖overlapAmp u z x - overlapAmp u z y‖
      ≤ 2 * (2 * Real.pi * (∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖) * ‖x - y‖) := by
        linarith
    _ = 4 * Real.pi * (∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖) * ‖x - y‖ := by ring

theorem lipschitzWith_overlapScore (u : d → V) (z : V)
    (hA : ∀ w : d → ℝ, ‖overlapAmp u z w‖ ≤ 1) :
    LipschitzWith (Real.toNNReal (4 * Real.pi * ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖))
      (overlapScore u z) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hc : (0 : ℝ) ≤ 4 * Real.pi * ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ := by
    have hs : (0 : ℝ) ≤ ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    have := Real.pi_pos
    positivity
  rw [Real.coe_toNNReal _ hc, Real.dist_eq, dist_eq_norm]
  exact norm_overlapScore_sub_le u z x y hA

theorem sum_norm_inner_le (u : d → V) (z : V) (hz : ‖z‖ ≤ 1) :
    ∑ j : d, ‖(inner ℂ z (u j) : ℂ)‖ ≤ ∑ j : d, ‖u j‖ := by
  refine Finset.sum_le_sum fun j _ => ?_
  refine le_trans (norm_inner_le_norm (𝕜 := ℂ) z (u j)) ?_
  have hnn : (0 : ℝ) ≤ ‖u j‖ := norm_nonneg _
  nlinarith [hz, hnn, norm_nonneg z]

theorem lipschitzWith_overlapScore_uniform (u : d → V) (z : V) (hz : ‖z‖ ≤ 1)
    (hA : ∀ w : d → ℝ, ‖overlapAmp u z w‖ ≤ 1) :
    LipschitzWith (Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖)) (overlapScore u z) := by
  refine (lipschitzWith_overlapScore u z hA).weaken ?_
  have hs := sum_norm_inner_le u z hz
  have hpi : (0 : ℝ) ≤ 4 * Real.pi := by positivity
  exact Real.toNNReal_le_toNNReal (mul_le_mul_of_nonneg_left hs hpi)

section CompleteLipschitz

variable {Z : Type*} [Fintype Z] [Nonempty Z]

theorem lipschitzWith_completeScore (u : d → V) (z : Z → V) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (hA : ∀ (w : Z) (y : d → ℝ), ‖overlapAmp u (z w) y‖ ≤ 1) :
    LipschitzWith (Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖)) (completeScore u z) :=
  lipschitzWith_finiteMax fun w => lipschitzWith_overlapScore_uniform u (z w) (hz w) (hA w)

theorem overlapScore_mem_unitInterval (u : d → V) (z : V) (x : d → ℝ)
    (hA : ∀ w : d → ℝ, ‖overlapAmp u z w‖ ≤ 1) :
    0 ≤ overlapScore u z x ∧ overlapScore u z x ≤ 1 := by
  constructor
  · rw [overlapScore]
    positivity
  · rw [overlapScore]
    have := hA x
    nlinarith [norm_nonneg (overlapAmp u z x)]

theorem completeScore_mem_unitInterval (u : d → V) (z : Z → V) (x : d → ℝ)
    (hA : ∀ (w : Z) (y : d → ℝ), ‖overlapAmp u (z w) y‖ ≤ 1) :
    0 ≤ completeScore u z x ∧ completeScore u z x ≤ 1 := by
  constructor
  · obtain ⟨w, hw⟩ := exists_eq_finiteMax (fun w : Z => overlapScore u (z w)) x
    rw [completeScore, ← hw]
    exact (overlapScore_mem_unitInterval u (z w) x (hA w)).1
  · rw [completeScore, finiteMax]
    refine Finset.sup'_le _ _ fun w _ => ?_
    exact (overlapScore_mem_unitInterval u (z w) x (hA w)).2

end CompleteLipschitz

end Lipschitz

section TorusForm

open UnitAddTorus

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- The torus form of the overlap amplitude. -/
def torusOverlapAmp (u : d → V) (z : V) (t : UnitAddTorus d) : ℂ :=
  ∑ j : d, (fourier (-1) (t j)) * (inner ℂ z (u j))

theorem torusOverlapAmp_torusProj (u : d → V) (z : V) (x : d → ℝ) :
    torusOverlapAmp u z (torusProj x) = overlapAmp u z x := by
  rw [torusOverlapAmp, overlapAmp]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [torusProj, fourier_coe_apply]
  push_cast
  ring_nf

theorem continuous_torusOverlapAmp (u : d → V) (z : V) :
    Continuous (torusOverlapAmp u z) := by
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((map_continuous (fourier (-1))).comp (continuous_apply j)).mul continuous_const

/-- The torus form of the overlap score. -/
def torusScore (u : d → V) (z : V) (t : UnitAddTorus d) : ℝ := ‖torusOverlapAmp u z t‖ ^ 2

theorem continuous_torusScore (u : d → V) (z : V) : Continuous (torusScore u z) :=
  ((continuous_torusOverlapAmp u z).norm).pow 2

theorem torusScore_torusProj (u : d → V) (z : V) (x : d → ℝ) :
    torusScore u z (torusProj x) = overlapScore u z x := by
  rw [torusScore, overlapScore, torusOverlapAmp_torusProj]

/-- The torus form of the complete incidence score. -/
def torusCompleteScore (u : d → V) (z : Z → V) (t : UnitAddTorus d) : ℝ :=
  finiteMax (fun w : Z => torusScore u (z w)) t

theorem continuous_torusCompleteScore (u : d → V) (z : Z → V) :
    Continuous (torusCompleteScore u z) := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty fun w _ => ?_
  exact continuous_torusScore u (z w)

theorem torusCompleteScore_torusProj (u : d → V) (z : Z → V) (x : d → ℝ) :
    torusCompleteScore u z (torusProj x) = completeScore u z x := by
  rw [torusCompleteScore, completeScore, finiteMax, finiteMax]
  refine Finset.sup'_congr _ rfl fun w _ => ?_
  exact torusScore_torusProj u (z w) x

/-- The torus form of the bounded replica reporter. -/
def torusReporter (u : d → V) (z : Z → V) (B : ℝ → ℝ) (t : UnitAddTorus d) : ℂ :=
  ((B (torusCompleteScore u z t) : ℝ) : ℂ)

/-- The reporter as a continuous map on the torus. -/
def torusReporterMap (u : d → V) (z : Z → V) {B : ℝ → ℝ} (hB : Continuous B) :
    C(UnitAddTorus d, ℂ) :=
  ⟨torusReporter u z B, by
    refine Complex.continuous_ofReal.comp ?_
    exact hB.comp (continuous_torusCompleteScore u z)⟩

theorem torusLift_torusReporterMap (u : d → V) (z : Z → V) {B : ℝ → ℝ} (hB : Continuous B)
    (x : d → ℝ) :
    torusLift (torusReporterMap u z hB) x = ((B (completeScore u z x) : ℝ) : ℂ) := by
  rw [torusLift, torusReporterMap]
  show ((B (torusCompleteScore u z (torusProj x)) : ℝ) : ℂ) = _
  rw [torusCompleteScore_torusProj]

end TorusForm

section Influence

open UnitAddTorus

variable {Z : Type*} [Fintype Z] [Nonempty Z]

theorem lipschitzWith_torusLift_reporter (u : d → V) (z : Z → V) {B : ℝ → ℝ}
    (hB : Continuous B) {r : ℝ} (hr : 0 ≤ r)
    (hBlip : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |B a - B b| ≤ r * |a - b|)
    (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (hA : ∀ (w : Z) (y : d → ℝ), ‖overlapAmp u (z w) y‖ ≤ 1) :
    LipschitzWith (Real.toNNReal r * Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖))
      (torusLift (torusReporterMap u z hB)) := by
  have hYlip := lipschitzWith_completeScore u z hz hA
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hx := completeScore_mem_unitInterval u z x hA
  have hy := completeScore_mem_unitInterval u z y hA
  have hstep : dist (torusLift (torusReporterMap u z hB) x)
      (torusLift (torusReporterMap u z hB) y) =
      |B (completeScore u z x) - B (completeScore u z y)| := by
    rw [torusLift_torusReporterMap, torusLift_torusReporterMap, dist_eq_norm,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hstep]
  have hB1 := hBlip (completeScore u z x) (completeScore u z y) hx.1 hx.2 hy.1 hy.2
  have hY : |completeScore u z x - completeScore u z y| ≤
      (Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖) : ℝ) * dist x y := by
    have := hYlip.dist_le_mul x y
    rwa [Real.dist_eq] at this
  have hcoe : ((Real.toNNReal r * Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖) : NNReal) : ℝ) =
      (Real.toNNReal r : ℝ) * (Real.toNNReal (4 * Real.pi * ∑ j : d, ‖u j‖) : ℝ) := by
    push_cast
    ring
  rw [hcoe, Real.coe_toNNReal r hr, mul_assoc]
  refine le_trans hB1 ?_
  exact mul_le_mul_of_nonneg_left hY hr

/-- **Low-replica complete-incidence influence.**  The variance of a bounded replica reporter of the
complete incidence score is at most four times the squared replica order times the maximal component
weight, with no dependence on the number of targets. -/
theorem variance_torusReporter_le (u : d → V) (z : Z → V) {B : ℝ → ℝ} (hB : Continuous B)
    {B' : ℝ → ℝ} (hBderiv : ∀ s : ℝ, HasDerivAt B (B' s) s) {r p : ℝ} (hr : 0 ≤ r)
    (hB'bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → |B' s| ≤ r)
    (hBlip : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |B a - B b| ≤ r * |a - b|)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (hp : ∀ w : Z, ∑ j : d, ‖(inner ℂ (z w) (u j) : ℂ)‖ ^ 2 ≤ p) :
    (∫ t : UnitAddTorus d, ‖torusReporterMap u z hB t‖ ^ 2) -
        ‖∫ t : UnitAddTorus d, torusReporterMap u z hB t‖ ^ 2 ≤ 4 * r ^ 2 * p := by
  have hA : ∀ (w : Z) (y : d → ℝ), ‖overlapAmp u (z w) y‖ ≤ 1 := fun w y =>
    norm_overlapAmp_le_one u (z w) y horth hu (hz w)
  have hlip := lipschitzWith_torusLift_reporter u z hB hr hBlip hz hA
  have hYlip := lipschitzWith_completeScore u z hz hA
  have hKae : ∀ᵐ x : d → ℝ,
      ∑ j : d, ‖fderiv ℝ (torusLift (torusReporterMap u z hB)) x (Pi.single j 1)‖ ^ 2 ≤
        r ^ 2 * (16 * Real.pi ^ 2 * p) := by
    filter_upwards [hYlip.ae_differentiableAt] with x hx
    have hlift : torusLift (torusReporterMap u z hB) =
        fun y : d → ℝ => ((B (completeScore u z y) : ℝ) : ℂ) := by
      funext y
      exact torusLift_torusReporterMap u z hB y
    have hreal : HasFDerivAt (fun y : d → ℝ => B (completeScore u z y))
        (fderiv ℝ (fun y : d → ℝ => B (completeScore u z y)) x) x := by
      refine (DifferentiableAt.hasFDerivAt ?_)
      exact ((hBderiv (completeScore u z x)).differentiableAt).comp x hx
    have hcomplex : HasFDerivAt (torusLift (torusReporterMap u z hB))
        (Complex.ofRealCLM.comp (fderiv ℝ (fun y : d → ℝ => B (completeScore u z y)) x)) x := by
      rw [hlift]
      exact Complex.ofRealCLM.hasFDerivAt.comp x hreal
    have hnorm : ∀ j : d,
        ‖fderiv ℝ (torusLift (torusReporterMap u z hB)) x (Pi.single j 1)‖ =
        |fderiv ℝ (fun y : d → ℝ => B (completeScore u z y)) x (Pi.single j 1)| := by
      intro j
      rw [hcomplex.fderiv]
      simp [Complex.norm_real, Real.norm_eq_abs]
    have hsq : ∀ j : d,
        ‖fderiv ℝ (torusLift (torusReporterMap u z hB)) x (Pi.single j 1)‖ ^ 2 =
        (fderiv ℝ (fun y : d → ℝ => B (completeScore u z y)) x (Pi.single j 1)) ^ 2 := by
      intro j
      rw [hnorm j, sq_abs]
    rw [Finset.sum_congr rfl fun j _ => hsq j]
    have hxr := completeScore_mem_unitInterval u z x hA
    exact sum_sq_fderiv_reporter_le u z x hr (hBderiv (completeScore u z x))
      (hB'bound _ hxr.1 hxr.2) hx (fun w => hA w x) hp
  have hvar := variance_le_of_ae_fderiv_bound (torusReporterMap u z hB) hlip hKae
  refine le_trans hvar (le_of_eq ?_)
  have hpi : (4 : ℝ) * Real.pi ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Influence

section LightFiltering

open UnitAddTorus

variable {Z : Type*} [Fintype Z] [Nonempty Z]

/-- The light family retains only the components of weight at most the cutoff. -/
def lightFamily (u : d → V) (τ : ℝ) : d → V := fun j => if ‖u j‖ ^ 2 ≤ τ then u j else 0

theorem norm_lightFamily_sq_le (u : d → V) {τ : ℝ} (hτ : 0 ≤ τ) (j : d) :
    ‖lightFamily u τ j‖ ^ 2 ≤ τ := by
  rw [lightFamily]
  by_cases hj : ‖u j‖ ^ 2 ≤ τ
  · rw [if_pos hj]
    exact hj
  · rw [if_neg hj]
    simpa using hτ

theorem norm_lightFamily_le (u : d → V) (τ : ℝ) (j : d) : ‖lightFamily u τ j‖ ≤ ‖u j‖ := by
  rw [lightFamily]
  by_cases hj : ‖u j‖ ^ 2 ≤ τ
  · rw [if_pos hj]
  · rw [if_neg hj]
    simp

theorem orthogonal_lightFamily (u : d → V) (τ : ℝ)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) (i j : d) (hij : i ≠ j) :
    (inner ℂ (lightFamily u τ i) (lightFamily u τ j) : ℂ) = 0 := by
  rw [lightFamily, lightFamily]
  by_cases hi : ‖u i‖ ^ 2 ≤ τ
  · by_cases hj : ‖u j‖ ^ 2 ≤ τ
    · rw [if_pos hi, if_pos hj]
      exact horth i j hij
    · rw [if_neg hj]
      simp
  · rw [if_neg hi]
    simp

theorem sum_norm_lightFamily_sq_le (u : d → V) (τ : ℝ) (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) :
    ∑ j : d, ‖lightFamily u τ j‖ ^ 2 ≤ 1 := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) hu
  have h := norm_lightFamily_le u τ j
  have h0 : (0 : ℝ) ≤ ‖lightFamily u τ j‖ := norm_nonneg _
  nlinarith [h, h0]

/-- **Discarded weight.**  The light truncation loses at most the total squared weight divided by
the cutoff. -/
theorem norm_sq_phaseOrbit_sub_lightFamily_le (u : d → V)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0) {τ : ℝ} (hτ : 0 < τ)
    (x : d → ℝ) :
    ‖phaseOrbit u x - phaseOrbit (lightFamily u τ) x‖ ^ 2 ≤ (∑ j : d, ‖u j‖ ^ 4) / τ := by
  have hdiff : phaseOrbit u x - phaseOrbit (lightFamily u τ) x =
      ∑ j : d, Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) •
        (u j - lightFamily u τ j) := by
    rw [phaseOrbit, phaseOrbit, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_sub]
  have horth' : ∀ i j : d, i ≠ j →
      (inner ℂ (Complex.exp (-(2 * Real.pi * Complex.I) * (x i)) • (u i - lightFamily u τ i))
        (Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) • (u j - lightFamily u τ j)) : ℂ) = 0 := by
    intro i j hij
    have hsub : ∀ k : d, u k - lightFamily u τ k =
        if ‖u k‖ ^ 2 ≤ τ then 0 else u k := by
      intro k
      rw [lightFamily]
      by_cases hk : ‖u k‖ ^ 2 ≤ τ
      · rw [if_pos hk, if_pos hk, sub_self]
      · rw [if_neg hk, if_neg hk, sub_zero]
    rw [inner_smul_left, inner_smul_right, hsub i, hsub j]
    by_cases hi : ‖u i‖ ^ 2 ≤ τ
    · rw [if_pos hi]
      simp
    · by_cases hj : ‖u j‖ ^ 2 ≤ τ
      · rw [if_pos hj]
        simp
      · rw [if_neg hi, if_neg hj, horth i j hij]
        ring
  rw [hdiff, norm_sq_sum_of_orthogonal horth']
  have hterm : ∀ j : d,
      ‖Complex.exp (-(2 * Real.pi * Complex.I) * (x j)) • (u j - lightFamily u τ j)‖ ^ 2 ≤
      ‖u j‖ ^ 4 / τ := by
    intro j
    rw [norm_smul, Complex.norm_exp]
    have hre : (-(2 * Real.pi * Complex.I) * (x j : ℂ)).re = 0 := by simp
    rw [hre, Real.exp_zero, one_mul]
    rw [lightFamily]
    by_cases hj : ‖u j‖ ^ 2 ≤ τ
    · rw [if_pos hj, sub_self]
      simp
      positivity
    · rw [if_neg hj, sub_zero]
      have hgt : τ < ‖u j‖ ^ 2 := lt_of_not_ge hj
      rw [le_div_iff₀ hτ]
      have h4 : ‖u j‖ ^ 4 = ‖u j‖ ^ 2 * ‖u j‖ ^ 2 := by ring
      rw [h4]
      exact mul_le_mul_of_nonneg_left hgt.le (by positivity)
  refine le_trans (Finset.sum_le_sum fun j _ => hterm j) ?_
  rw [← Finset.sum_div]

/-- **Light-filtered influence.**  The light truncation obeys the same variance law with the cutoff
in place of the maximal weight. -/
theorem variance_lightFamily_reporter_le (u : d → V) (z : Z → V) {B : ℝ → ℝ} (hB : Continuous B)
    {B' : ℝ → ℝ} (hBderiv : ∀ s : ℝ, HasDerivAt B (B' s) s) {r τ : ℝ} (hr : 0 ≤ r)
    (hτ : 0 ≤ τ)
    (hB'bound : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → |B' s| ≤ r)
    (hBlip : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → |B a - B b| ≤ r * |a - b|)
    (horth : ∀ i j : d, i ≠ j → (inner ℂ (u i) (u j) : ℂ) = 0)
    (hu : ∑ j : d, ‖u j‖ ^ 2 ≤ 1) (hz : ∀ w : Z, ‖z w‖ ≤ 1) [DecidableEq V] :
    (∫ t : UnitAddTorus d, ‖torusReporterMap (lightFamily u τ) z hB t‖ ^ 2) -
        ‖∫ t : UnitAddTorus d, torusReporterMap (lightFamily u τ) z hB t‖ ^ 2 ≤
      4 * r ^ 2 * τ := by
  refine variance_torusReporter_le (lightFamily u τ) z hB hBderiv hr hB'bound hBlip
    (orthogonal_lightFamily u τ horth) (sum_norm_lightFamily_sq_le u τ hu) hz ?_
  intro w
  exact sum_sq_inner_le_of_orthogonal (orthogonal_lightFamily u τ horth) hτ
    (norm_lightFamily_sq_le u hτ) (z w) (hz w)

/-- The square root of the overlap score. -/
def sqrtScore (u : d → V) (z : V) (x : d → ℝ) : ℝ := ‖overlapAmp u z x‖

/-- The complete square-root score of a target family. -/
def completeSqrtScore (u : d → V) (z : Z → V) (x : d → ℝ) : ℝ :=
  finiteMax (fun w : Z => sqrtScore u (z w)) x

theorem completeSqrtScore_sq (u : d → V) (z : Z → V) (x : d → ℝ) :
    completeSqrtScore u z x ^ 2 = completeScore u z x := by
  classical
  rw [completeSqrtScore, completeScore, finiteMax, finiteMax]
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Z))
    fun w => sqrtScore u (z w) x
  rw [hw]
  refine le_antisymm ?_ ?_
  · refine le_trans (le_of_eq ?_) (Finset.le_sup' (fun w => overlapScore u (z w) x)
      (Finset.mem_univ w))
    rw [sqrtScore, overlapScore]
  · refine Finset.sup'_le _ _ fun v _ => ?_
    have hle : sqrtScore u (z v) x ≤ sqrtScore u (z w) x := by
      rw [← hw]
      exact Finset.le_sup' (fun w => sqrtScore u (z w) x) (Finset.mem_univ v)
    have hnn : (0 : ℝ) ≤ sqrtScore u (z v) x := norm_nonneg _
    have hnn' : (0 : ℝ) ≤ sqrtScore u (z w) x := norm_nonneg _
    rw [overlapScore, show ‖overlapAmp u (z v) x‖ = sqrtScore u (z v) x from rfl]
    nlinarith [hle, hnn, hnn']

/-- **Filtering is operationally harmless.**  The complete square-root scores of the full and light
orbits differ by at most the discarded weight. -/
theorem abs_completeSqrtScore_sub_le (u : d → V) (z : Z → V) {τ ρ : ℝ}
    (hz : ∀ w : Z, ‖z w‖ ≤ 1)
    (hdiff : ∀ y : d → ℝ, ‖phaseOrbit u y - phaseOrbit (lightFamily u τ) y‖ ≤ ρ) (x : d → ℝ) :
    |completeSqrtScore u z x - completeSqrtScore (lightFamily u τ) z x| ≤ ρ := by
  refine le_trans (abs_finiteMax_sub_finiteMax_le_of_family
    (fun w : Z => sqrtScore u (z w)) (fun w : Z => sqrtScore (lightFamily u τ) (z w)) x) ?_
  refine Finset.sup'_le _ _ fun w _ => ?_
  have hamp : overlapAmp u (z w) x - overlapAmp (lightFamily u τ) (z w) x =
      inner ℂ (z w) (phaseOrbit u x - phaseOrbit (lightFamily u τ) x) := by
    rw [overlapAmp_eq_inner, overlapAmp_eq_inner, ← inner_sub_right]
  have hcs : ‖overlapAmp u (z w) x - overlapAmp (lightFamily u τ) (z w) x‖ ≤
      ‖phaseOrbit u x - phaseOrbit (lightFamily u τ) x‖ := by
    rw [hamp]
    refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
    have h1 := hz w
    have h2 : (0 : ℝ) ≤ ‖phaseOrbit u x - phaseOrbit (lightFamily u τ) x‖ := norm_nonneg _
    nlinarith [h1, h2, norm_nonneg (z w)]
  refine le_trans ?_ (le_trans hcs (hdiff x))
  rw [sqrtScore, sqrtScore]
  exact abs_norm_sub_norm_le _ _

end LightFiltering

end PhaseOrbit

end GaloisForLFunctions.HTGeometry
