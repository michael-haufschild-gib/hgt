import GaloisForLFunctions.HTGeometry.SquarefreeVeroneseIdeal
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Characteristic-free independence of the native coface monomials

The exponent transformation sends `d` to the vector whose `i`th coordinate
is the sum of all coordinates except `i`. Its total sum recovers the total
sum of `d`, and then each coordinate is recovered without division in the
coefficient field. This supplies independent generators for the paper's
associated-graded construction.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

/-- The exponent transformation of the native coface substitution. -/
def paperCofaceExponentMap (r : ℕ) :
    (Fin (r + 1 + 1) →₀ ℕ) →+ (Fin (r + 1 + 1) →₀ ℕ) where
  toFun d := Finsupp.equivFunOnFinite.symm fun i => ∑ j ∈ Finset.univ.erase i, d j
  map_zero' := by ext i; simp
  map_add' d e := by ext i; simp [Finset.sum_add_distrib]

/-- Adding the omitted exponent restores the total exponent sum. -/
theorem paperCofaceExponentMap_add_coordinate (r : ℕ)
    (d : Fin (r + 1 + 1) →₀ ℕ) (i : Fin (r + 1 + 1)) :
    paperCofaceExponentMap r d i + d i = ∑ j, d j := by
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

/-- The coface substitution multiplies total exponent sums by `r + 1`. -/
theorem paperCofaceExponentMap_sum (r : ℕ) (d : Fin (r + 1 + 1) →₀ ℕ) :
    (∑ i, paperCofaceExponentMap r d i) = (r + 1) * ∑ i, d i := by
  have h := congrArg (fun f : Fin (r + 1 + 1) → ℕ => ∑ i, f i)
    (funext (paperCofaceExponentMap_add_coordinate r d))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  nlinarith

/-- No distinct exponent vectors collide, in any dimension at least two. -/
theorem paperCofaceExponentMap_injective (r : ℕ) :
    Function.Injective (paperCofaceExponentMap r) := by
  intro d e h
  have hs : (∑ i, d i) = ∑ i, e i := by
    have ht := congrArg (fun f : Fin (r + 1 + 1) →₀ ℕ => ∑ i, f i) h
    rw [paperCofaceExponentMap_sum, paperCofaceExponentMap_sum] at ht
    nlinarith
  ext i
  have hd := paperCofaceExponentMap_add_coordinate r d i
  have he := paperCofaceExponentMap_add_coordinate r e i
  rw [h, hs] at hd
  omega

/-- A single variable becomes the squarefree monomial on its complementary face. -/
theorem paperCofaceExponentMap_single (r : ℕ) (i : Fin (r + 1 + 1)) :
    paperCofaceExponentMap r (Finsupp.single i 1) =
      ∑ j ∈ Finset.univ.erase i, Finsupp.single j 1 := by
  ext j
  simp only [paperCofaceExponentMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finsupp.coe_equivFunOnFinite_symm, Finsupp.finsetSum_apply, Finsupp.single_apply]
  by_cases h : i = j
  · subst j; simp
  · simp [h, Ne.symm h]

variable (K : Type*) [Field K]

/-- Substitute the actual native coface gradient components for all variables. -/
def paperCofaceSubstitution (r : ℕ) :
    MvPolynomial (Fin (r + 1 + 1)) K →ₐ[K] MvPolynomial (Fin (r + 1 + 1)) K :=
  MvPolynomial.aeval (cofaceMonomial (F := K) (r + 1))

/-- The native substitution is exactly the map induced by its exponent transformation. -/
theorem paperCofaceSubstitution_eq_mapDomain (r : ℕ) :
    paperCofaceSubstitution K r =
      AddMonoidAlgebra.mapDomainAlgHom K K (paperCofaceExponentMap r) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [paperCofaceSubstitution, MvPolynomial.aeval_X]
  change cofaceMonomial (F := K) (r + 1) i =
    AddMonoidAlgebra.mapDomain (paperCofaceExponentMap r) (MvPolynomial.X i)
  change cofaceMonomial (F := K) (r + 1) i =
    AddMonoidAlgebra.mapDomain (paperCofaceExponentMap r)
      (AddMonoidAlgebra.single (Finsupp.single i 1) (1 : K))
  rw [AddMonoidAlgebra.mapDomain_single]
  change cofaceMonomial (F := K) (r + 1) i =
    MvPolynomial.monomial (paperCofaceExponentMap r (Finsupp.single i 1)) 1
  rw [paperCofaceExponentMap_single]
  exact prod_X_eq_monomial _

/-- The native coface monomials satisfy no scalar polynomial relation over any field. -/
theorem paperCofaceSubstitution_injective (r : ℕ) :
    Function.Injective (paperCofaceSubstitution K r) := by
  rw [paperCofaceSubstitution_eq_mapDomain]
  exact AddMonoidAlgebra.mapDomain_injective (paperCofaceExponentMap_injective r)

/-- Every coface component has the exact common homogeneous degree. -/
theorem paperCofaceMonomial_homogeneous (r : ℕ) (i : Fin (r + 1 + 1)) :
    (cofaceMonomial (F := K) (r + 1) i).IsHomogeneous (r + 1) := by
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ.erase i)
    (fun j => (MvPolynomial.X j : MvPolynomial (Fin (r + 1 + 1)) K))
    (fun _ => 1) (fun j _ => MvPolynomial.isHomogeneous_X K j)
  simpa [cofaceMonomial] using h

/-- Homogeneous inputs retain their exact scaled degree under the native substitution. -/
theorem paperCofaceSubstitution_homogeneous (r n : ℕ)
    (p : MvPolynomial (Fin (r + 1 + 1)) K) (hp : p.IsHomogeneous n) :
    (paperCofaceSubstitution K r p).IsHomogeneous ((r + 1) * n) :=
  hp.aeval _ (paperCofaceMonomial_homogeneous K r)

end

end GaloisForLFunctions.HTGeometry
