import GaloisForLFunctions.RHTower.FermionicFockIsospectrality
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff


/-!
# Exterior traces of coordinate reflections

A diagonal sign involution lifts to every exterior power. Slater basis
vectors carry the product of their occupied signs, and the sector trace is
the corresponding coefficient of the reflection determinant polynomial.
Its exact factorization is the Krawtchouk character used in Liu–Xu's
return-holonomy argument.
-/

noncomputable section
open Module
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.ExteriorReflection
open _root_.RHTower _root_.RHTower.ParityForecast

/-- A coordinate sign involution in the existing one-particle basis. -/
def signOperator {r : ℕ} (S : Finset (Fin r)) :
    FiniteIndexClockSpace (Fin r) →ₗ[ℂ] FiniteIndexClockSpace (Fin r) :=
  (standardOneParticleBasis r).constr ℂ
    (fun j => (if j ∈ S then (-1 : ℂ) else 1) • standardOneParticleBasis r j)

theorem signOperator_basis {r : ℕ} (S : Finset (Fin r)) (j : Fin r) :
    signOperator S (standardOneParticleBasis r j) =
      (if j ∈ S then (-1 : ℂ) else 1) • standardOneParticleBasis r j :=
  Module.Basis.constr_basis _ _ _ _

/-- The chosen sign pattern defines an exact involution. -/
theorem signOperator_comp_self {r : ℕ} (S : Finset (Fin r)) :
    (signOperator S).comp (signOperator S) = LinearMap.id := by
  apply (standardOneParticleBasis r).ext
  intro j
  simp only [LinearMap.comp_apply, signOperator_basis, map_smul, smul_smul,
    LinearMap.id_apply]
  by_cases h : j ∈ S <;> simp only [h, if_true, if_false, neg_mul_neg, one_mul, one_smul]

/-- Exterior lifting preserves exact involutivity in every particle sector. -/
theorem exterior_signOperator_comp_self {r : ℕ} (S : Finset (Fin r)) (k : ℕ) :
    (exteriorPower.map k (signOperator S)).comp (exteriorPower.map k (signOperator S)) =
      LinearMap.id := by
  rw [← exteriorPower.map_comp, signOperator_comp_self, exteriorPower.map_id]

/-- A Slater basis vector has the product of the occupied reflection signs. -/
theorem exterior_signOperator_basis {r k : ℕ} (S : Finset (Fin r))
    (T : Set.powersetCard (Fin r) k) :
    exteriorPower.map k (signOperator S) (fermionicSectorBasis r k T) =
      (∏ j ∈ T.val, if j ∈ S then (-1 : ℂ) else 1) • fermionicSectorBasis r k T := by
  change exteriorPower.map k (signOperator S)
    ((standardOneParticleBasis r).exteriorPower k T) = _
  rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, exteriorPower.map_apply_ιMulti]
  have he : (signOperator S) ∘
      ((standardOneParticleBasis r) ∘ Set.powersetCard.ofFinEmbEquiv.symm T) =
      (fun i => (if Set.powersetCard.ofFinEmbEquiv.symm T i ∈ S then (-1 : ℂ) else 1) •
        standardOneParticleBasis r (Set.powersetCard.ofFinEmbEquiv.symm T i)) := by
    funext i
    exact signOperator_basis S _
  rw [he, AlternatingMap.map_smul_univ]
  have hp : (∏ i : Fin k,
      if Set.powersetCard.ofFinEmbEquiv.symm T i ∈ S then (-1 : ℂ) else 1) =
      ∏ j ∈ T.val, if j ∈ S then (-1 : ℂ) else 1 := by
    rw [Finset.prod_subtype T.val (fun _ => Iff.rfl)]
    exact Fintype.prod_equiv (powersetOrderEquiv T) _ _ (fun _ => rfl)
  rw [hp]
  rw [fermionicSectorBasis, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  rfl

/-- The signed exterior trace is the exact subset-character sum. -/
theorem exterior_signOperator_trace {r : ℕ} (S : Finset (Fin r)) (k : ℕ) :
    LinearMap.trace ℂ (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r)))
      (exteriorPower.map k (signOperator S)) =
      ∑ T : Set.powersetCard (Fin r) k,
        ∏ j ∈ T.val, if j ∈ S then (-1 : ℂ) else 1 := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (fermionicSectorBasis r k)]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro T _
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, exterior_signOperator_basis,
    map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

/-- The one-particle diagonal reflection in its chosen basis. -/
def signMatrix {r : ℕ} (S : Finset (Fin r)) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.diagonal fun i => if i ∈ S then -1 else 1

private theorem signMatrix_minor_det {r : ℕ} (S T : Finset (Fin r)) :
    ((signMatrix S).submatrix (Subtype.val : T → Fin r) (Subtype.val : T → Fin r)).det =
      ∏ j ∈ T, if j ∈ S then (-1 : ℂ) else 1 := by
  have he : (signMatrix S).submatrix (Subtype.val : T → Fin r) (Subtype.val : T → Fin r) =
      Matrix.diagonal (fun j : T => if j.val ∈ S then (-1 : ℂ) else 1) := by
    ext i j
    simp only [signMatrix, Matrix.submatrix_apply, Matrix.diagonal_apply, Subtype.ext_iff]
  rw [he, Matrix.det_diagonal]
  exact Finset.prod_coe_sort T (fun j : Fin r => if j ∈ S then (-1 : ℂ) else 1)

/-- The character polynomial gathers all exterior-sector traces. -/
def characterPolynomial {r : ℕ} (S : Finset (Fin r)) : Polynomial ℂ :=
  Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (signMatrix S).map Polynomial.C)

/-- Each exterior trace is an actual coefficient of the reflection determinant polynomial. -/
theorem exterior_signOperator_trace_eq_coeff {r : ℕ} (S : Finset (Fin r)) (k : ℕ) :
    LinearMap.trace ℂ (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r)))
      (exteriorPower.map k (signOperator S)) = (characterPolynomial S).coeff k := by
  rw [exterior_signOperator_trace, characterPolynomial,
    Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
  simp_rw [signMatrix_minor_det]
  exact (Finset.sum_subtype (p := fun T => T ∈ Set.powersetCard (Fin r) k)
    (Finset.univ.powersetCard k)
    (fun T => by
      change T ∈ Finset.univ.powersetCard k ↔ T.card = k
      simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and])
    (fun T => ∏ j ∈ T, if j ∈ S then (-1 : ℂ) else 1)).symm

/-- The full exterior character depends only on the number of negative one-particle directions. -/
theorem characterPolynomial_eq {r : ℕ} (S : Finset (Fin r)) :
    characterPolynomial S =
      (1 - Polynomial.X) ^ S.card * (1 + Polynomial.X) ^ (r - S.card) := by
  classical
  have he : (1 + (Polynomial.X : Polynomial ℂ) • (signMatrix S).map Polynomial.C) =
      Matrix.diagonal (fun i : Fin r =>
        if i ∈ S then (1 - Polynomial.X : Polynomial ℂ) else 1 + Polynomial.X) := by
    ext i j
    by_cases h : i = j
    · subst j
      by_cases hi : i ∈ S <;>
        simp [signMatrix, hi, sub_eq_add_neg]
    · simp [signMatrix, h]
  rw [characterPolynomial, he, Matrix.det_diagonal, Finset.prod_ite]
  have hs : Finset.univ.filter (fun i : Fin r => i ∈ S) = S := by ext i; simp
  have hc : Finset.univ.filter (fun i : Fin r => i ∉ S) = Sᶜ := by ext i; simp
  rw [hs, hc]
  simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- Exterior reflection traces are the Krawtchouk coefficients of the exact sign multiplicities. -/
theorem exterior_signOperator_trace_krawtchouk {r : ℕ} (S : Finset (Fin r)) (k : ℕ) :
    LinearMap.trace ℂ (⋀[ℂ]^k (FiniteIndexClockSpace (Fin r)))
      (exteriorPower.map k (signOperator S)) =
      ((1 - Polynomial.X : Polynomial ℂ) ^ S.card *
        (1 + Polynomial.X) ^ (r - S.card)).coeff k := by
  rw [exterior_signOperator_trace_eq_coeff, characterPolynomial_eq]

#print axioms signOperator_comp_self
#print axioms exterior_signOperator_comp_self
#print axioms exterior_signOperator_basis
#print axioms exterior_signOperator_trace
#print axioms exterior_signOperator_trace_eq_coeff
#print axioms characterPolynomial_eq
#print axioms exterior_signOperator_trace_krawtchouk
end GaloisForLFunctions.HilbertMetric.ExteriorReflection
