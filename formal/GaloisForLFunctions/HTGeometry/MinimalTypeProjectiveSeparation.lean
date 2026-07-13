import GaloisForLFunctions.HTGeometry.MinimalTypeNevanlinnaAperiodicity
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped BigOperators

noncomputable section

/-- The projective cross-difference whose vanishing says that `[-D:C]` takes the same value at
`z + u` and `z + v`. -/
def projectiveShiftCollision (C D : ℂ → ℂ) (u v z : ℂ) : ℂ :=
  D (z + u) * C (z + v) - D (z + v) * C (z + u)

/-- **Projective minimal-type aperiodicity.** A lower Nevanlinna row with no common zero, with a
minimal-type denominator having a zero, admits no nonzero projective translation period. -/
theorem minimalType_projectiveQuotient_aperiodic
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p c : ℂ} (hCp : C p = 0) (hCc : C c ≠ 0) :
    ∀ omega : ℂ, omega ≠ 0 →
      ¬ ∀ z, D (z + omega) * C z = D z * C (z + omega) := by
  intro omega homega hperiod
  have hzero : ∀ n : ℕ, C (p + n • omega) = 0 := by
    intro n
    induction n with
    | zero => simpa using hCp
    | succ n ih =>
        have hD : D (p + n • omega) ≠ 0 := by
          intro hDz
          exact hnoCommon (p + n • omega) ⟨ih, hDz⟩
        have hrel := hperiod (p + n • omega)
        have hnext : C ((p + n • omega) + omega) = 0 := by
          rw [ih, mul_zero] at hrel
          exact (mul_eq_zero.mp hrel.symm).resolve_left hD
        convert hnext using 1
        ring_nf
  exact hCmin.no_arithmeticProgression_zeros hCc homega hzero

/-- Determinant one supplies both the no-common-zero property and a nonzero anchor for `C`. -/
theorem nevanlinnaLowerRow_projective_aperiodic
    {A B C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C)
    (hdet : ∀ z, A z * D z - B z * C z = 1)
    {p c : ℂ} (hCp : C p = 0) (hCc : C c ≠ 0) :
    ∀ omega : ℂ, omega ≠ 0 →
      ¬ ∀ z, D (z + omega) * C z = D z * C (z + omega) := by
  have hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0) := by
    intro z h
    have hz := hdet z
    rw [h.1, h.2] at hz
    norm_num at hz
  exact minimalType_projectiveQuotient_aperiodic hCmin hnoCommon hCp hCc

/-- Distinct shifts give a nonzero projective cross-difference. -/
theorem projectiveShiftCollision_ne_zero
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p c : ℂ} (hCp : C p = 0) (hCc : C c ≠ 0)
    {u v : ℂ} (huv : u ≠ v) :
    (fun z => projectiveShiftCollision C D u v z) ≠ 0 := by
  intro hzero
  have homega : u - v ≠ 0 := sub_ne_zero.mpr huv
  apply minimalType_projectiveQuotient_aperiodic hCmin hnoCommon hCp hCc (u - v) homega
  intro x
  have h := congrFun hzero (x - v)
  dsimp [projectiveShiftCollision] at h
  convert sub_eq_zero.mp h using 1 <;> ring_nf

/-- The product of two nonzero entire scalar functions is nonzero. -/
theorem differentiable_mul_ne_zero
    {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (hfn : f ≠ 0) (hgn : g ≠ 0) :
    (fun z => f z * g z) ≠ 0 := by
  intro hprod
  have hfan : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hgan : AnalyticOnNhd ℂ g Set.univ :=
    hg.differentiableOn.analyticOnNhd isOpen_univ
  have hsplit := hfan.eq_zero_or_eq_zero_of_mul_eq_zero hgan
    (fun z _ => congrFun hprod z) isPreconnected_univ
  rcases hsplit with hfzero | hgzero
  · apply hfn
    funext z
    exact hfzero z (Set.mem_univ z)
  · apply hgn
    funext z
    exact hgzero z (Set.mem_univ z)

/-- A finite pointwise product of nonzero entire functions is nonzero. -/
theorem differentiable_finset_prod_ne_zero
    {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℂ (f i))
    (hne : ∀ i ∈ s, f i ≠ 0) :
    (fun z => ∏ i ∈ s, f i z) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro h
      have := congrFun h 0
      norm_num at this
  | @insert a s ha ih =>
      simp only [Finset.prod_insert, ha, not_false_eq_true]
      apply differentiable_mul_ne_zero (hf a (Finset.mem_insert_self a s))
      · rw [show (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, f i by
          funext z
          simp only [Finset.prod_apply]]
        exact Differentiable.finsetProd fun i hi => hf i (Finset.mem_insert_of_mem hi)
      · exact hne a (Finset.mem_insert_self a s)
      · apply ih
        · intro i hi
          exact hf i (Finset.mem_insert_of_mem hi)
        · intro i hi
          exact hne i (Finset.mem_insert_of_mem hi)

/-- Every projective cross-difference of entire functions is entire. -/
theorem projectiveShiftCollision_differentiable
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (u v : ℂ) :
    Differentiable ℂ (projectiveShiftCollision C D u v) := by
  unfold projectiveShiftCollision
  exact ((hD.comp (differentiable_id.add_const u)).mul
    (hC.comp (differentiable_id.add_const v))).sub
    ((hD.comp (differentiable_id.add_const v)).mul
      (hC.comp (differentiable_id.add_const u)))

/-- The finite product encoding denominator regularity and all pairwise projective separations. -/
def projectiveSeparationProduct
    {ι : Type*} [Fintype ι] [DecidableEq ι]
  (C D : ℂ → ℂ) (shift : ι → ℂ) (z : ℂ) : ℂ :=
  (∏ i, C (z + shift i)) *
    ∏ x : {x : ι × ι // x.1 ≠ x.2},
      projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z

/-- The projective separation product is entire. -/
theorem projectiveSeparationProduct_differentiable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C D : ℂ → ℂ} (hC : Differentiable ℂ C) (hD : Differentiable ℂ D)
    (shift : ι → ℂ) :
    Differentiable ℂ (projectiveSeparationProduct C D shift) := by
  unfold projectiveSeparationProduct
  apply Differentiable.mul
  · rw [show (fun z => ∏ i, C (z + shift i)) =
        ∏ i, (fun z => C (z + shift i)) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun i (_hi : i ∈ (Finset.univ : Finset ι)) => by
      simpa only [Function.comp_apply, id_eq] using
        hC.comp (differentiable_id.add_const (shift i))
  · rw [show (fun z =>
        ∏ x : {x : ι × ι // x.1 ≠ x.2},
          projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) =
        ∏ x : {x : ι × ι // x.1 ≠ x.2},
          projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun x
      (_hx : x ∈ (Finset.univ : Finset {x : ι × ι // x.1 ≠ x.2})) =>
        projectiveShiftCollision_differentiable hC hD (shift x.1.1) (shift x.1.2)

/-- Under minimal-type projective aperiodicity, the finite separation product is nonzero. -/
theorem projectiveSeparationProduct_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift) :
    projectiveSeparationProduct C D shift ≠ 0 := by
  unfold projectiveSeparationProduct
  apply differentiable_mul_ne_zero
  · rw [show (fun z => ∏ i, C (z + shift i)) =
        ∏ i, (fun z => C (z + shift i)) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun i (_hi : i ∈ (Finset.univ : Finset ι)) => by
      simpa only [Function.comp_apply, id_eq] using
        hCmin.1.comp (differentiable_id.add_const (shift i))
  · rw [show (fun z =>
        ∏ x : {x : ι × ι // x.1 ≠ x.2},
          projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) =
        ∏ x : {x : ι × ι // x.1 ≠ x.2},
          projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) by
      funext z
      simp only [Finset.prod_apply]]
    exact Differentiable.finsetProd fun x
      (_hx : x ∈ (Finset.univ : Finset {x : ι × ι // x.1 ≠ x.2})) =>
        projectiveShiftCollision_differentiable hCmin.1 hD (shift x.1.1) (shift x.1.2)
  · apply differentiable_finset_prod_ne_zero Finset.univ
    · intro i hi
      exact hCmin.1.comp (differentiable_id.add_const (shift i))
    · intro i hi hzero
      have := congrFun hzero (c - shift i)
      apply hCc
      simpa using this
  · apply differentiable_finset_prod_ne_zero Finset.univ
    · intro x hx
      exact projectiveShiftCollision_differentiable
        hCmin.1 hD (shift x.1.1) (shift x.1.2)
    · intro x hx
      apply projectiveShiftCollision_ne_zero hCmin hnoCommon hCp hCc
      exact hshift.ne x.2

/-- A nonzero entire function is nonzero somewhere above every horizontal line. -/
theorem exists_upper_ne_zero_of_differentiable_ne_zero
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfn : f ≠ 0) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧ f z ≠ 0 := by
  by_contra h
  push Not at h
  let z₀ : ℂ := (H + 1 : ℂ) * I
  have hz₀ : H < z₀.im := by simp [z₀]
  have hopen : IsOpen {z : ℂ | H < z.im} := isOpen_lt continuous_const continuous_im
  have hevent : f =ᶠ[nhds z₀] 0 := by
    filter_upwards [hopen.mem_nhds hz₀] with z hz
    exact h z hz
  have hfan : AnalyticOnNhd ℂ f Set.univ :=
    hf.differentiableOn.analyticOnNhd isOpen_univ
  have hzero : AnalyticOnNhd ℂ (0 : ℂ → ℂ) Set.univ :=
    differentiable_zero.differentiableOn.analyticOnNhd isOpen_univ
  exact hfn (hfan.eq_of_eventuallyEq hzero hevent)

/-- **Arbitrarily high projective separation rows.** For every finite injective shift packet and
height, one can choose a base point above that height at which every shifted denominator is
nonzero and all shifted projective labels `[-D:C]` are pairwise distinct. -/
theorem exists_upper_projectivelySeparated_shift_row
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧
      (∀ i, C (z + shift i) ≠ 0) ∧
      (∀ i j, i ≠ j →
        projectiveShiftCollision C D (shift i) (shift j) z ≠ 0) := by
  have hdiff := projectiveSeparationProduct_differentiable hCmin.1 hD shift
  have hne := projectiveSeparationProduct_ne_zero
    hCmin hD hnoCommon hCp hCc shift hshift
  obtain ⟨z, hzH, hz⟩ := exists_upper_ne_zero_of_differentiable_ne_zero hdiff hne H
  change
    (∏ i, C (z + shift i)) *
      (∏ x : {x : ι × ι // x.1 ≠ x.2},
        projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) ≠ 0 at hz
  have hleft : (∏ i, C (z + shift i)) ≠ 0 := by
    intro hzero
    exact hz (by rw [hzero, zero_mul])
  have hright :
      (∏ x : {x : ι × ι // x.1 ≠ x.2},
        projectiveShiftCollision C D (shift x.1.1) (shift x.1.2) z) ≠ 0 := by
    intro hzero
    exact hz (by rw [hzero, mul_zero])
  refine ⟨z, hzH, ?_, ?_⟩
  · intro i
    exact (Finset.prod_ne_zero_iff.mp hleft) i (Finset.mem_univ i)
  · intro i j hij
    let x : {x : ι × ι // x.1 ≠ x.2} := ⟨(i, j), hij⟩
    exact (Finset.prod_ne_zero_iff.mp hright) x (Finset.mem_univ x)

/-- A nonzero projective cross-difference at two regular denominator points is exactly inequality
of the corresponding affine projective parameters `-D/C`. -/
theorem quotient_ne_of_projectiveShiftCollision_ne_zero
    {C D : ℂ → ℂ} {z u v : ℂ}
    (hCu : C (z + u) ≠ 0) (hCv : C (z + v) ≠ 0)
    (hcollision : projectiveShiftCollision C D u v z ≠ 0) :
    -D (z + u) / C (z + u) ≠ -D (z + v) / C (z + v) := by
  intro heq
  apply hcollision
  rw [projectiveShiftCollision, sub_eq_zero]
  have hcross := (div_eq_div_iff hCu hCv).mp heq
  simpa only [neg_mul, neg_inj] using hcross

/-- Paper-facing affine form of the arbitrarily high separation law. -/
theorem exists_upper_quotientSeparated_shift_row
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {C D : ℂ → ℂ} (hCmin : HasMinimalExponentialType C) (hD : Differentiable ℂ D)
    (hnoCommon : ∀ z, ¬ (C z = 0 ∧ D z = 0))
    {p : ℂ} (hCp : C p = 0) {c : ℂ} (hCc : C c ≠ 0)
    (shift : ι → ℂ) (hshift : Function.Injective shift) (H : ℝ) :
    ∃ z : ℂ, H < z.im ∧
      (∀ i, C (z + shift i) ≠ 0) ∧
      (∀ i j, i ≠ j →
        -D (z + shift i) / C (z + shift i) ≠
          -D (z + shift j) / C (z + shift j)) := by
  obtain ⟨z, hzH, hregular, hseparated⟩ :=
    exists_upper_projectivelySeparated_shift_row
      hCmin hD hnoCommon hCp hCc shift hshift H
  refine ⟨z, hzH, hregular, ?_⟩
  intro i j hij
  exact quotient_ne_of_projectiveShiftCollision_ne_zero
    (hregular i) (hregular j) (hseparated i j hij)

end
end GaloisForLFunctions.HTGeometry
