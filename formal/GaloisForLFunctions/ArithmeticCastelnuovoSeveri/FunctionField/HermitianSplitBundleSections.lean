import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianGeometricProductFormula
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# One-fiber rigidity and dimensions of split Hermitian bundles

For two finite sums of degree-normalized divisor lines, the multiplicities
of common divisor classes determine the dimension of the global Hom space.
An endomorphism vanishing on one fiber is zero, as in Kazhdan, Lemma 2.1
(arXiv:2606.23240). The fiber kernel is expressed by adding the actual
point divisor to each source-to-target vanishing condition.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
variable (p : ℕ) [Fact p.Prime] (s : ℕ)
local notation "E" => HermitianGeometricConstants p s
local notation "H" => HermitianGeometricField p s
local notation "Pts" => HermitianGeometricPoint p s
local notation "PD" => Pts →₀ ℤ
local notation "Div" => HermitianGeometricPlaceDivisor p s
local notation "D₀" => hermitianGeometricDegreeZeroPart p s
local notation "divH" => hermitianGeometricPrincipalDivisorHom p s
local notation "cl" => hermitianGeometricClass p s
local notation "S" => hermitianLineHomSections p s

/-- Linear space of rational functions that are global sections of the indicated Hom line. -/
def hermitianGlobalHom (D C : PD) : Submodule E H := Submodule.span E (S D C)

private theorem section_line (g : Hˣ) :
    Set.range (fun c : E => algebraMap E H c * g) = (Submodule.span E {(g:H)} : Set H) := by
  rw [Submodule.span_singleton_eq_range]
  simp only [Algebra.smul_def]

/-- The span recovers exactly the divisor-defined sections, with no extra functions. -/
theorem hermitianGlobalHom_carrier (D C : PD) : (hermitianGlobalHom p s D C : Set H) = S D C := by
  rcases hermitianLineHomSections_classification p s D C with h | ⟨g,h⟩
  · simp [hermitianGlobalHom,h]
  · rw [hermitianGlobalHom,h,section_line,Submodule.span_eq]

private theorem line_class_iff (D C : PD) :
    cl (D₀ D) = cl (D₀ C) ↔ D₀ D - D₀ C ∈ (divH).range := by
  rw [← sub_eq_zero, ← map_sub]
  exact QuotientAddGroup.eq_zero_iff _

private theorem sectionSpace_forms (D C : PD) :
    hermitianGlobalHom p s D C = ⊥ ∨ ∃ g : Hˣ, hermitianGlobalHom p s D C = Submodule.span E {(g:H)} := by
  rcases hermitianLineHomSections_classification p s D C with h | ⟨g,h⟩
  · exact Or.inl (by simp [hermitianGlobalHom,h])
  · exact Or.inr ⟨g,by rw [hermitianGlobalHom,h,section_line,Submodule.span_eq]⟩

instance hermitianGlobalHom_finite (D C : PD) : Module.Finite E (hermitianGlobalHom p s D C) := by
  rcases sectionSpace_forms p s D C with h | ⟨g,h⟩
  · rw [h]; infer_instance
  · rw [h]; infer_instance

open scoped Classical in
/-- A single rational global Hom space has dimension one exactly for equal divisor classes. -/
theorem hermitianGlobalHom_finrank (D C : PD) :
    Module.finrank E (hermitianGlobalHom p s D C) = if cl (D₀ D) = cl (D₀ C) then 1 else 0 := by
  classical
  by_cases h : cl (D₀ D) = cl (D₀ C)
  · rw [if_pos h]
    rcases sectionSpace_forms p s D C with he | ⟨g,hg⟩
    · have hz : S D C = {0} := by rw [← hermitianGlobalHom_carrier,he]; rfl
      exact ((hermitianLineHomSections_trivial_iff p s D C).1 hz ((line_class_iff p s D C).1 h)).elim
    · rw [hg, finrank_span_singleton g.ne_zero]
  · have hz := (hermitianLineHomSections_trivial_iff p s D C).2 (fun hm => h ((line_class_iff p s D C).2 hm))
    rw [if_neg h,hermitianGlobalHom,hz,Submodule.span_zero_singleton,finrank_bot]

/-- The section matrices of a map between two split Hermitian bundles. -/
abbrev HermitianSplitHom {ι κ : Type*} (D : ι → PD) (C : κ → PD) :=
  (i : ι) → (j : κ) → hermitianGlobalHom p s (D i) (C j)

open scoped Classical in
/-- Global Hom dimension is the number of source-target pairs in the same divisor class. -/
theorem hermitianSplitHom_dimension {ι κ : Type*} [Fintype ι] [Fintype κ] (D : ι → PD) (C : κ → PD) :
    Module.finrank E (HermitianSplitHom p s D C) =
      ∑ i, ∑ j, if cl (D₀ (D i)) = cl (D₀ (C j)) then 1 else 0 := by
  classical
  letI (i : ι) (j : κ) : Module.Free E (hermitianGlobalHom p s (D i) (C j)) :=
    Module.Free.of_divisionRing E _
  letI (i : ι) : Module.Free E ((j : κ) → hermitianGlobalHom p s (D i) (C j)) :=
    Module.Free.of_divisionRing E _
  unfold HermitianSplitHom
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl fun j _ => hermitianGlobalHom_finrank p s _ _

/-- A sum of pairwise inequivalent degree-zero lines has one independent endomorphism per summand. -/
theorem hermitianSplitEnd_dimension_of_injective {ι : Type*} [Fintype ι] (D : ι → PD)
    (h : Function.Injective (fun i => cl (D₀ (D i)))) :
    Module.finrank E (HermitianSplitHom p s D D) = Fintype.card ι := by
  classical
  rw [hermitianSplitHom_dimension]
  simp only [h.eq_iff]
  simp

/-- A sum of copies of one divisor line has a full square of independent endomorphisms. -/
theorem hermitianSplitEnd_dimension_constant {ι : Type*} [Fintype ι] (D : PD) :
    Module.finrank E (HermitianSplitHom p s (fun _ : ι => D) (fun _ : ι => D)) = Fintype.card ι^2 := by
  rw [hermitianSplitHom_dimension]
  simp [pow_two]

private theorem point_not_nonpos (P : Pts) : ¬ hermitianGeometricPointDivisor p s P ≤ (0:Div) := by
  cases P with
  | none => exact fun h => (by omega : ¬ (1:ℤ) ≤ 0) h.2
  | some P =>
    intro h
    have ht := h.1 (hermitianGeometricPointPrime p s P)
    change Finsupp.single _ (1:ℤ) _ ≤ 0 at ht
    rw [Finsupp.single_eq_same] at ht
    omega

/-- Factoring a section through the target twisted down by a point forces the section to vanish. -/
theorem hermitianLineHom_fiber_kernel (D C : PD) (P : Pts) :
    {f : H | f = 0 ∨ D₀ D + hermitianGeometricPointDivisor p s P ≤
      hermitianGeometricZeroPoleDivisor p s f + D₀ C} = {0} := by
  ext f
  change (_ ∨ _) ↔ f = 0
  refine ⟨?_, Or.inl⟩
  rintro (hz | h)
  · exact hz
  · by_contra hf
    let u := Additive.ofMul (Units.mk0 f hf)
    have he : D₀ D ≤ divH u + D₀ C :=
      (le_add_of_nonneg_right (hermitianGeometricPointDivisor_nonneg p s P)).trans h
    have hEq := (hermitianLineHom_effective_iff p s D C u).1 he
    change D₀ D + hermitianGeometricPointDivisor p s P ≤ divH u + D₀ C at h
    rw [← hEq] at h
    exact point_not_nonpos p s P (by simpa only [add_le_iff_nonpos_right] using h)

/-- Vanishing on one geometric fiber detects zero for every matrix of maps between equal-degree split bundles. -/
theorem hermitianSplitHom_fiber_kernel {ι κ : Type*} (D : ι → PD) (C : κ → PD) (P : Pts) :
    {f : Matrix κ ι H | ∀ j i, f j i = 0 ∨
      D₀ (D i) + hermitianGeometricPointDivisor p s P ≤
        hermitianGeometricZeroPoleDivisor p s (f j i) + D₀ (C j)} = {0} := by
  ext f
  change (∀ j i, _ ∨ _) ↔ f = 0
  refine ⟨fun h => ?_, by rintro rfl j i; exact Or.inl rfl⟩
  funext j i
  exact (Set.ext_iff.mp (hermitianLineHom_fiber_kernel p s (D i) (C j) P) (f j i)).1 (h j i)

#print axioms hermitianGlobalHom_finite
#print axioms hermitianGlobalHom_carrier
#print axioms hermitianGlobalHom_finrank
#print axioms hermitianSplitHom_dimension
#print axioms hermitianSplitEnd_dimension_of_injective
#print axioms hermitianSplitEnd_dimension_constant
#print axioms hermitianLineHom_fiber_kernel
#print axioms hermitianSplitHom_fiber_kernel

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
