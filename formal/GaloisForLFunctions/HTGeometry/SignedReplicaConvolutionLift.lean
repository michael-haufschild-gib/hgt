import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The signed replica convolution lift and its return sector

A finitely supported complex measure on an abelian group is an element of the group algebra, and
convolution is its multiplication.  Conjugate reflection — conjugating coefficients and negating the
group label — is a ring endomorphism, so the forward–backward replica lift of order `r` is the
`r`-th convolution power of the order-one lift.

The return sector is the part supported on a fixed subgroup, and it is closed under convolution.
Consequently return excision does not commute with convolution: excising the return sector after
every step loses exactly the cross terms, and the defect is twice the off-return part of the mixed
product.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {G : Type*} [AddCommGroup G]

theorem addMonoidAlgebra_ext {a b : AddMonoidAlgebra ℂ G} (h : a.coeff = b.coeff) : a = b := by
  cases a
  cases b
  simp_all

/-- Negation as an additive endomorphism of an abelian group. -/
def negAddHom (G : Type*) [AddCommGroup G] : G →+ G where
  toFun := fun g => -g
  map_zero' := neg_zero
  map_add' := fun a b => neg_add a b

/-- **Conjugate reflection** of a finitely supported complex measure: conjugate the coefficients
and negate the labels.  It is a ring endomorphism of the group algebra. -/
def conjReflect (G : Type*) [AddCommGroup G] :
    AddMonoidAlgebra ℂ G →+* AddMonoidAlgebra ℂ G :=
  (AddMonoidAlgebra.mapDomainRingHom ℂ (negAddHom G)).comp
    (AddMonoidAlgebra.mapRingHom G (starRingEnd ℂ))

/-- **Theorem D, equations (26)–(27): the atoms of the replica lift.**  The `r`-th convolution
power of an atomic measure is supported on the multiplicity vectors of order `r`, with multinomial
coefficient and observed label the corresponding integer combination of the single-step labels. -/
theorem pow_sum_single {I : Type*} [Fintype I] [DecidableEq I] (c : I → ℂ) (φ : I → G) (r : ℕ) :
    (∑ j, AddMonoidAlgebra.single (φ j) (c j)) ^ r
      = ∑ p ∈ Finset.univ.piAntidiag r,
          AddMonoidAlgebra.single (∑ j, p j • φ j)
            ((Nat.multinomial Finset.univ p : ℂ) * ∏ j, c j ^ p j) := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hprod : (∏ j, AddMonoidAlgebra.single (φ j) (c j) ^ p j) =
      AddMonoidAlgebra.single (∑ j, p j • φ j) (∏ j, c j ^ p j) := by
    rw [Finset.prod_congr rfl fun j _ => AddMonoidAlgebra.single_pow (φ j) (c j) (p j),
      AddMonoidAlgebra.prod_single]
  rw [hprod, ← nsmul_eq_mul, AddMonoidAlgebra.smul_single]
  congr 1
  simp

/-- The order-`r` forward–backward replica lift. -/
def replicaPairLift (μ : AddMonoidAlgebra ℂ G) (r : ℕ) : AddMonoidAlgebra ℂ G :=
  μ ^ r * conjReflect G (μ ^ r)

/-- **Theorem D, equation (25).**  The order-`r` pair lift is the `r`-th convolution power of the
order-one pair lift. -/
theorem replicaPairLift_eq_pow (μ : AddMonoidAlgebra ℂ G) (r : ℕ) :
    replicaPairLift μ r = replicaPairLift μ 1 ^ r := by
  rw [replicaPairLift, replicaPairLift, pow_one, map_pow, ← mul_pow]

section Return

variable (H : AddSubgroup G)

open Classical in
/-- The return sector of a signed lift: the part supported on the subgroup of exact returns. -/
def returnPart (μ : AddMonoidAlgebra ℂ G) : AddMonoidAlgebra ℂ G :=
  AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun g => g ∈ H) μ.coeff)

/-- The off-return sector of a signed lift. -/
def offReturnPart (μ : AddMonoidAlgebra ℂ G) : AddMonoidAlgebra ℂ G :=
  μ - returnPart H μ

open Classical in
theorem coeff_returnPart (μ : AddMonoidAlgebra ℂ G) :
    (returnPart H μ).coeff = Finsupp.filter (fun g => g ∈ H) μ.coeff := rfl

theorem returnPart_add (μ ν : AddMonoidAlgebra ℂ G) :
    returnPart H (μ + ν) = returnPart H μ + returnPart H ν := by
  classical
  refine addMonoidAlgebra_ext ?_
  rw [coeff_returnPart, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_add,
    coeff_returnPart, coeff_returnPart, Finsupp.filter_add]

theorem offReturnPart_add (μ ν : AddMonoidAlgebra ℂ G) :
    offReturnPart H (μ + ν) = offReturnPart H μ + offReturnPart H ν := by
  rw [offReturnPart, offReturnPart, offReturnPart, returnPart_add]
  abel

theorem returnPart_add_offReturnPart (μ : AddMonoidAlgebra ℂ G) :
    returnPart H μ + offReturnPart H μ = μ := by
  rw [offReturnPart]
  abel

theorem returnPart_mem_of_mem_support (μ : AddMonoidAlgebra ℂ G) {g : G}
    (hg : g ∈ (returnPart H μ).coeff.support) : g ∈ H := by
  classical
  rw [coeff_returnPart, Finsupp.support_filter, Finset.mem_filter] at hg
  exact hg.2

/-- The return sector is closed under convolution. -/
theorem offReturnPart_mul_returnPart (μ ν : AddMonoidAlgebra ℂ G) :
    offReturnPart H (returnPart H μ * returnPart H ν) = 0 := by
  classical
  have hsupp : ∀ g : G, (returnPart H μ * returnPart H ν).coeff g ≠ 0 → g ∈ H := by
    intro g hg0
    have hg : g ∈ (returnPart H μ * returnPart H ν).coeff.support := Finsupp.mem_support_iff.mpr hg0
    have hmem := AddMonoidAlgebra.support_coeff_mul_subset (returnPart H μ) (returnPart H ν) hg
    rw [Finset.mem_add] at hmem
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem
    exact AddSubgroup.add_mem H (returnPart_mem_of_mem_support H μ ha)
      (returnPart_mem_of_mem_support H ν hb)
  have hfix : returnPart H (returnPart H μ * returnPart H ν) =
      returnPart H μ * returnPart H ν := by
    refine addMonoidAlgebra_ext ?_
    rw [coeff_returnPart]
    exact (Finsupp.filter_eq_self_iff _ _).mpr hsupp
  rw [offReturnPart, hfix, sub_self]

/-- **Theorem D, equation (28).**  Source-first return excision is a single projection applied to
the `r`-th convolution power of the order-one pair lift. -/
theorem offReturnPart_replicaPairLift (μ : AddMonoidAlgebra ℂ G) (r : ℕ) :
    offReturnPart H (replicaPairLift μ r) = offReturnPart H (replicaPairLift μ 1 ^ r) := by
  rw [replicaPairLift_eq_pow]

/-- **Theorem D, equation (32).**  Return excision does not commute with convolution: the defect of
stepwise excision is exactly twice the off-return part of the mixed product. -/
theorem offReturnPart_mul_defect (μ : AddMonoidAlgebra ℂ G) :
    offReturnPart H (μ * μ) - offReturnPart H (offReturnPart H μ * offReturnPart H μ) =
      2 • offReturnPart H (returnPart H μ * offReturnPart H μ) := by
  classical
  have hsplit : μ * μ =
      returnPart H μ * returnPart H μ +
        (returnPart H μ * offReturnPart H μ + returnPart H μ * offReturnPart H μ) +
        offReturnPart H μ * offReturnPart H μ := by
    conv_lhs => rw [← returnPart_add_offReturnPart H μ]
    ring
  rw [hsplit, offReturnPart_add, offReturnPart_add, offReturnPart_add,
    offReturnPart_mul_returnPart, zero_add, two_smul]
  abel

end Return

end GaloisForLFunctions.HTGeometry
