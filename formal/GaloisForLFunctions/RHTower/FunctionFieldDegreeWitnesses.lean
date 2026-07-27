import GaloisForLFunctions.RHTower.FunctionFieldDegeneration

/-!
# Degree data that actually exists

The function-field degeneration layer is stated for an abstract `FunctionFieldDegreeData`, but no
such datum is exhibited.  Three are supplied here, spanning the range the corank-one law is meant to
cover:

* the one-place datum, where the relation lattice is trivial;
* the rational model, with countably many places all of degree one;
* a datum carrying places of every positive degree.

Each makes `ffRelationLattice_corank_eq_one` a statement about an existing object, and the last shows
that the law does not secretly assume all places rational.
-/

namespace GaloisForLFunctions

/-- The one-place degree datum. -/
def unitDegreeData : FunctionFieldDegreeData where
  Place := Unit
  degree := fun _ => 1
  degreeOnePlace := ()
  degree_degreeOnePlace := rfl

/-- The rational model: countably many places, each of degree one. -/
def rationalDegreeData : FunctionFieldDegreeData where
  Place := ℕ
  degree := fun _ => 1
  degreeOnePlace := 0
  degree_degreeOnePlace := rfl

/-- A degree datum with a place of every positive degree. -/
def gradedDegreeData : FunctionFieldDegreeData where
  Place := ℕ
  degree := fun n => (n : ℤ) + 1
  degreeOnePlace := 0
  degree_degreeOnePlace := by norm_num

theorem gradedDegreeData_degree_surjective :
    ∀ d : ℕ, ∃ v : gradedDegreeData.Place, gradedDegreeData.degree v = (d : ℤ) + 1 :=
  fun d => ⟨d, rfl⟩

/-- **The corank-one law on the one-place datum.** -/
theorem ffRelationLattice_corank_eq_one_unit :
    Module.rank ℤ ((unitDegreeData.Place →₀ ℤ) ⧸ ffRelationLattice unitDegreeData) = 1 :=
  ffRelationLattice_corank_eq_one unitDegreeData

/-- **The corank-one law on the rational model.** -/
theorem ffRelationLattice_corank_eq_one_rational :
    Module.rank ℤ ((rationalDegreeData.Place →₀ ℤ) ⧸ ffRelationLattice rationalDegreeData) = 1 :=
  ffRelationLattice_corank_eq_one rationalDegreeData

/-- **The corank-one law with places of every degree.** -/
theorem ffRelationLattice_corank_eq_one_graded :
    Module.rank ℤ ((gradedDegreeData.Place →₀ ℤ) ⧸ ffRelationLattice gradedDegreeData) = 1 :=
  ffRelationLattice_corank_eq_one gradedDegreeData

/-- In the rational model the relation lattice is exactly the group of degree-zero divisors: a
finite integer combination of places lies in it precisely when its coefficients sum to zero. -/
theorem mem_ffRelationLattice_rational_iff (m : rationalDegreeData.Place →₀ ℤ) :
    m ∈ ffRelationLattice rationalDegreeData ↔ (m.sum fun _ k => k) = 0 := by
  rw [ffRelationLattice_mem_iff]
  exact Iff.of_eq (congrArg (fun x => x = 0) (Finsupp.sum_congr fun _ _ => mul_one _))

end GaloisForLFunctions
