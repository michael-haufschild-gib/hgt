import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyTotality
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
open Complex Set
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section GenericFiniteReconstruction
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [DecidableEq I]

private def finiteRebuild (v : I → E) (a : I → E →L[ℂ] ℂ) (s : Finset I) : E →L[ℂ] E :=
  ∑ i ∈ s, (a i).smulRight (v i)

private theorem finiteRebuild_coefficient (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (s : Finset I) (u : E) (i : I) :
    a i (finiteRebuild v a s u) = if i ∈ s then a i u else 0 := by
  classical
  simp only [finiteRebuild, sum_apply, map_sum, ContinuousLinearMap.smulRight_apply,
    map_smul, smul_eq_mul, hd, mul_ite, mul_one, mul_zero]
  simp

private theorem finiteRebuild_eq_self_iff (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hk : Function.Injective (fun u : E => fun i : I => a i u))
    (s : Finset I) (u : E) :
    finiteRebuild v a s u = u ↔ Function.support (fun i => a i u) ⊆ (s : Set I) := by
  classical
  constructor
  · intro h i hi
    by_contra hsi
    change i ∉ s at hsi
    have ha := congrArg (a i) h
    rw [finiteRebuild_coefficient v a hd, if_neg hsi] at ha
    exact hi ha.symm
  · intro hs
    apply hk
    funext i
    change a i (finiteRebuild v a s u) = a i u
    rw [finiteRebuild_coefficient v a hd]
    split_ifs with hi
    · rfl
    · have hz : a i u = 0 := by
        by_contra h
        exact hi (hs h)
      exact hz.symm

private theorem finite_support_on_span (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    {u : E} (hu : u ∈ Submodule.span ℂ (Set.range v)) :
    (Function.support (fun i => a i u)).Finite := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, rfl⟩ := hu
    apply (Set.finite_singleton j).subset
    intro i hi
    change a i (v j) ≠ 0 at hi
    by_contra hij
    have hne : i ≠ j := hij
    exact hi (by rw [hd, if_neg hne])
  | zero =>
    apply (Set.finite_empty : (∅ : Set I).Finite).subset
    intro i hi
    exact False.elim (hi ((a i).map_zero))
  | add u v hu hv ihu ihv =>
    apply (ihu.union ihv).subset
    intro i hi
    change a i (u + v) ≠ 0 at hi
    by_cases hu : a i u = 0
    · right
      change a i v ≠ 0
      intro hv
      exact hi (by rw [map_add, hu, hv, add_zero])
    · exact Or.inl hu
  | smul c u hu ih =>
    apply ih.subset
    intro i hi
    change a i (c • u) ≠ 0 at hi
    change a i u ≠ 0
    intro hz
    exact hi (by rw [map_smul, hz, smul_zero])

omit [DecidableEq I] in
private theorem finiteRebuild_mem_span (v : I → E) (a : I → E →L[ℂ] ℂ)
    (s : Finset I) (u : E) :
    finiteRebuild v a s u ∈ Submodule.span ℂ (v '' (s : Set I)) := by
  classical
  simp only [finiteRebuild, sum_apply, ContinuousLinearMap.smulRight_apply]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

private theorem mem_span_iff_finite_support (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hk : Function.Injective (fun u : E => fun i : I => a i u)) (u : E) :
    u ∈ Submodule.span ℂ (Set.range v) ↔ (Function.support (fun i => a i u)).Finite := by
  classical
  constructor
  · exact finite_support_on_span v a hd
  · intro hs
    let s := hs.toFinset
    have hsub : Function.support (fun i => a i u) ⊆ (s : Set I) := by
      intro i hi
      exact hs.mem_toFinset.mpr hi
    have he := (finiteRebuild_eq_self_iff v a hd hk s u).mpr hsub
    rw [← he]
    apply (Submodule.span_mono (show v '' (s : Set I) ⊆ Set.range v from ?_))
      (finiteRebuild_mem_span v a s u)
    rintro _ ⟨i, hi, rfl⟩
    exact Set.mem_range_self i

private theorem finiteRebuild_fixes_span (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hk : Function.Injective (fun u : E => fun i : I => a i u))
    (s : Finset I) {u : E} (hu : u ∈ Submodule.span ℂ (v '' (s : Set I))) :
    finiteRebuild v a s u = u := by
  classical
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨j, hj, rfl⟩ := hu
    apply (finiteRebuild_eq_self_iff v a hd hk s (v j)).mpr
    intro i hi
    change a i (v j) ≠ 0 at hi
    by_cases hij : i = j
    · exact hij.symm ▸ hj
    · exact False.elim (hi (by rw [hd, if_neg hij]))
  | zero => exact map_zero _
  | add u v hu hv ihu ihv => rw [map_add, ihu, ihv]
  | smul c u hu ih => rw [map_smul, ih]

private theorem finiteRebuild_range (v : I → E) (a : I → E →L[ℂ] ℂ)
    (hd : ∀ i j, a i (v j) = if i = j then 1 else 0)
    (hk : Function.Injective (fun u : E => fun i : I => a i u)) (s : Finset I) :
    LinearMap.range (finiteRebuild v a s).toLinearMap =
      Submodule.span ℂ (v '' (s : Set I)) := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact finiteRebuild_mem_span v a s u
  · intro u hu
    exact ⟨u, finiteRebuild_fixes_span v a hd hk s hu⟩
omit [DecidableEq I] in
private theorem subtype_span_mem (D : Submodule ℂ E) (v : I → D) (u : D) :
    u.val ∈ Submodule.span ℂ (Set.range (fun i => (v i).val)) ↔
      u ∈ Submodule.span ℂ (Set.range v) := by
  have h := Submodule.apply_mem_span_image_iff_mem_span
    (f := D.subtype) (x := u) (s := Set.range v) D.injective_subtype
  have himage : D.subtype '' Set.range v = Set.range (fun i => (v i).val) := by
    ext w
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
      exact Set.mem_range_self i
    · rintro ⟨i, rfl⟩
      exact ⟨v i, Set.mem_range_self i, rfl⟩
  rw [himage] at h
  exact h
end GenericFiniteReconstruction
/-- The finite reconstruction operator formed from the actual scalar amplitudes
and their genuine unit-frequency chains. -/
def causalFrequencyTruncation (b : ℝ) (s : Finset ℝ) :
    causalFrequencySpace b →L[ℂ] causalFrequencySpace b :=
  finiteRebuild (causalFrequencyMode b) (causalFrequencyCoefficient b) s

/-- Finite reconstruction retains exactly the selected actual amplitudes. -/
theorem causalFrequencyCoefficient_truncation (b : ℝ) (s : Finset ℝ)
    (u : causalFrequencySpace b) (ω : ℝ) :
    causalFrequencyCoefficient b ω (causalFrequencyTruncation b s u) =
      if ω ∈ s then causalFrequencyCoefficient b ω u else 0 :=
  finiteRebuild_coefficient (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) s u ω

/-- Exact finite reconstruction holds precisely when the retained frequencies
contain the complete nonzero amplitude support. -/
theorem causalFrequencyTruncation_eq_self_iff (b : ℝ) (s : Finset ℝ)
    (u : causalFrequencySpace b) :
    causalFrequencyTruncation b s u = u ↔
      Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u) ⊆ (s : Set ℝ) :=
  finiteRebuild_eq_self_iff (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyCoefficient_injective b) s u

private theorem core_subtype_span (b : ℝ) (u : causalFrequencySpace b) :
    u.val ∈ causalFrequencyCore b ↔
      u ∈ Submodule.span ℂ (Set.range (causalFrequencyMode b)) :=
  subtype_span_mem (causalFrequencySpace b) (causalFrequencyMode b) u

/-- The original finite core is exactly the set of completed-frequency vectors
whose actual scalar amplitude support is finite. -/
theorem causalFrequencyCore_mem_iff_finite_support (b : ℝ) (u : causalFrequencySpace b) :
    u.val ∈ causalFrequencyCore b ↔
      (Function.support (fun ω : ℝ => causalFrequencyCoefficient b ω u)).Finite :=
  (core_subtype_span b u).trans
    (mem_span_iff_finite_support (causalFrequencyMode b) (causalFrequencyCoefficient b)
      (causalFrequencyCoefficient_mode b) (causalFrequencyCoefficient_injective b) u)

/-- A finite spectral reconstruction has exactly the retained finite mode span
as its range, with no assumed decomposition of the input vector. -/
theorem causalFrequencyTruncation_range (b : ℝ) (s : Finset ℝ) :
    LinearMap.range (causalFrequencyTruncation b s).toLinearMap =
      Submodule.span ℂ (causalFrequencyMode b '' (s : Set ℝ)) :=
  finiteRebuild_range (causalFrequencyMode b) (causalFrequencyCoefficient b)
    (causalFrequencyCoefficient_mode b) (causalFrequencyCoefficient_injective b) s

end RHTower.FokasLenells
