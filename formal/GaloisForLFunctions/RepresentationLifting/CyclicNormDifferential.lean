import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Prod
import GaloisForLFunctions.RepresentationLifting.AcyclicTrace

/-!
# An acyclic square-zero operator from the cyclic norm resolution

For the regular representation of a finite cyclic group, let `N` be the norm and
`Δ = g - 1` for a generator. The doubled operator `d(x,y) = (Ny,Δx)` satisfies
`d² = 0` and `ker d = im d`. Projection onto the first summand satisfies `dh + hd = d`.

This is the acyclic norm-difference operator of Scavia's Lemma 6.2. Its exactness
holds over every commutative coefficient ring and for every finite cyclic group.
-/

noncomputable section

open CategoryTheory

namespace GaloisForLFunctions.RepresentationLifting

universe u

section Ring

variable (k G : Type u) [CommRing k] [CommGroup G] [Fintype G] [IsCyclic G]

/-- A generator chosen once for the cyclic norm-difference construction. -/
def cyclicRegularGenerator : G := Classical.choose (IsCyclic.exists_generator (α := G))

omit [Fintype G] in
theorem cyclicRegularGenerator_generates (x : G) :
    x ∈ Subgroup.zpowers (cyclicRegularGenerator G) :=
  Classical.choose_spec (IsCyclic.exists_generator (α := G)) x

abbrev CyclicRegular := (Rep.leftRegular k G).V

/-- The norm on the regular module. -/
def cyclicRegularNorm : Module.End k (CyclicRegular k G) :=
  (Rep.leftRegular k G).norm.hom.toLinearMap

/-- Translation by a generator minus the identity. -/
def cyclicRegularDelta : Module.End k (CyclicRegular k G) :=
  (Rep.applyAsHom (Rep.leftRegular k G) (cyclicRegularGenerator G) - 𝟙 _).hom.toLinearMap

theorem cyclicRegular_norm_delta_exact :
    LinearMap.range (cyclicRegularNorm k G) = LinearMap.ker (cyclicRegularDelta k G) :=
  Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub k _
    (cyclicRegularGenerator_generates G)

theorem cyclicRegular_delta_norm_exact :
    LinearMap.range (cyclicRegularDelta k G) = LinearMap.ker (cyclicRegularNorm k G) :=
  Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm k _
    (cyclicRegularGenerator_generates G)

abbrev CyclicDetector := CyclicRegular k G × CyclicRegular k G

/-- The doubled norm-difference differential. -/
def cyclicDifferential : Module.End k (CyclicDetector k G) where
  toFun v := (cyclicRegularNorm k G v.2, cyclicRegularDelta k G v.1)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem cyclicDifferential_sq (v : CyclicDetector k G) :
    cyclicDifferential k G (cyclicDifferential k G v) = 0 := by
  have hn : cyclicRegularNorm k G (cyclicRegularDelta k G v.1) = 0 := by
    have h : cyclicRegularDelta k G v.1 ∈ LinearMap.range (cyclicRegularDelta k G) :=
      ⟨v.1, rfl⟩
    rw [cyclicRegular_delta_norm_exact] at h
    exact h
  have hd : cyclicRegularDelta k G (cyclicRegularNorm k G v.2) = 0 := by
    have h : cyclicRegularNorm k G v.2 ∈ LinearMap.range (cyclicRegularNorm k G) :=
      ⟨v.2, rfl⟩
    rw [cyclicRegular_norm_delta_exact] at h
    exact h
  exact Prod.ext hn hd

/-- The doubled operator is acyclic, without a characteristic restriction. -/
theorem cyclicDifferential_exact :
    LinearMap.range (cyclicDifferential k G) = LinearMap.ker (cyclicDifferential k G) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact cyclicDifferential_sq k G w
  · intro h
    have hnorm : cyclicRegularNorm k G v.2 = 0 := congrArg Prod.fst h
    have hdelta : cyclicRegularDelta k G v.1 = 0 := congrArg Prod.snd h
    have hv1 : v.1 ∈ LinearMap.range (cyclicRegularNorm k G) := by
      rw [cyclicRegular_norm_delta_exact]; exact hdelta
    have hv2 : v.2 ∈ LinearMap.range (cyclicRegularDelta k G) := by
      rw [cyclicRegular_delta_norm_exact]; exact hnorm
    obtain ⟨y, hy⟩ := hv1
    obtain ⟨x, hx⟩ := hv2
    exact ⟨(x, y), Prod.ext hy hx⟩

/-- Projection onto the even summand of the doubled regular module. -/
def cyclicEven : Module.End k (CyclicDetector k G) where
  toFun v := (v.1, 0)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

theorem cyclicEven_grading (v : CyclicDetector k G) :
    cyclicDifferential k G (cyclicEven k G v) +
      cyclicEven k G (cyclicDifferential k G v) = cyclicDifferential k G v := by
  simp [cyclicDifferential, cyclicEven]

end Ring

section Field

variable (k G : Type u) [Field k] [CommGroup G] [Fintype G] [IsCyclic G]

/-- Over a field, the doubled cyclic regular module is a free dual-number module. -/
theorem cyclicDifferential_normalForm :
    ∃ e : CyclicDetector k G ≃ₗ[k]
        (LinearMap.ker (cyclicDifferential k G) × LinearMap.ker (cyclicDifferential k G)),
      ∀ v, e (cyclicDifferential k G v) = (0, (e v).1) :=
  acyclic_squareZero_normalForm _ (cyclicDifferential_exact k G)

/-- Every endomorphism commuting with the cyclic differential is traceless in characteristic two. -/
theorem cyclicDifferential_trace_zero [CharP k 2] (T : Module.End k (CyclicDetector k G)) :
    T * cyclicDifferential k G = cyclicDifferential k G * T →
      LinearMap.trace k (CyclicDetector k G) T = 0 :=
  acyclic_squareZero_trace_zero _ T (cyclicDifferential_exact k G)

end Field

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.cyclicDifferential_exact
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicEven_grading
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicDifferential_normalForm
#print axioms GaloisForLFunctions.RepresentationLifting.cyclicDifferential_trace_zero
