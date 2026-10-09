import GaloisForLFunctions.HTGeometry.PaperHomogeneousIdealNormalLine
import GaloisForLFunctions.HTGeometry.PaperSquarefreeWeightOrders
import Mathlib.Data.Fin.SuccPred

/-!
# Source Rees normal lines for squarefree Veronese constraint ideals

Apply the paper's weight and coefficient-kernel theorems to the native
squarefree Veronese ideals. A selected face monomial has exact order in
every ideal power and gives an actual polynomial normal-line embedding.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial GaloisForLFunctions.VeroneseIdeal

noncomputable section

variable (K : Type*) [Field K]

/-- A squarefree coordinate product is homogeneous in its support cardinality. -/
theorem paperSquarefreeProduct_homogeneous {σ : Type*} (s : Finset σ) :
    (∏ j ∈ s, (X j : MvPolynomial σ K)).IsHomogeneous s.card :=
  paperSquarefreeProduct_homogeneous_overRing K s

/-- The native Veronese ideal has the exact generator-degree lower bound. -/
theorem paperVeroneseIdeal_weightOrder (σ : Type*) [DecidableEq σ] (q : ℕ) :
    veroneseIdeal K σ q ≤
      paperWeightOrderIdeal (fun _ : σ => (1 : ℤ)) (by intro _; exact zero_le_one) (q : ℤ) :=
  paperVeroneseIdeal_weightOrder_overRing K σ q

/-- A canonical squarefree face in an arbitrarily larger coordinate window. -/
def paperVeroneseFace (r extra : ℕ) : Finset (Fin (r + 1 + extra)) :=
  Finset.univ.image (Fin.castAdd extra : Fin (r + 1) → Fin (r + 1 + extra))

/-- The selected face has exactly the generator degree. -/
theorem paperVeroneseFace_card (r extra : ℕ) : (paperVeroneseFace r extra).card = r + 1 := by
  rw [paperVeroneseFace, Finset.card_image_of_injective _ (Fin.castAdd_injective _ _)]
  simp

/-- The product of the selected independent coordinate variables. -/
def paperVeroneseFaceMonomial (r extra : ℕ) : MvPolynomial (Fin (r + 1 + extra)) K :=
  ∏ j ∈ paperVeroneseFace r extra, X j

/-- Actual Veronese generators satisfy every normal-line condition. -/
def paperVeroneseNormalData (r extra : ℕ) :
    PaperHomogeneousNormalData K (Fin (r + 1 + extra))
      (veroneseIdeal K (Fin (r + 1 + extra)) (r + 1)) where
  generator := paperVeroneseFaceMonomial K r extra
  degree := r + 1
  degree_pos := Nat.succ_pos r
  generator_mem := Ideal.subset_span ⟨paperVeroneseFace r extra, paperVeroneseFace_card r extra, rfl⟩
  generator_ne_zero := by
    rw [paperVeroneseFaceMonomial, Finset.prod_ne_zero_iff]
    exact fun j _ => MvPolynomial.X_ne_zero j
  homogeneous := by
    have hh := paperSquarefreeProduct_homogeneous K (paperVeroneseFace r extra)
    rw [paperVeroneseFace_card] at hh
    exact paperIsWeightedHomogeneous_int hh
  order_bound := paperVeroneseIdeal_weightOrder K _ _

/-- Every power of the chosen face monomial has exactly its expected ideal order. -/
theorem paperVeroneseFaceMonomial_pow_exact (r extra n : ℕ) :
    paperVeroneseFaceMonomial K r extra ^ n ∈
        veroneseIdeal K (Fin (r + 1 + extra)) (r + 1) ^ n ∧
    paperVeroneseFaceMonomial K r extra ^ n ∉
        veroneseIdeal K (Fin (r + 1 + extra)) (r + 1) ^ (n + 1) :=
  ⟨(paperVeroneseNormalData K r extra).pow_mem n, (paperVeroneseNormalData K r extra).pow_not_mem_succ n⟩

/-- The face monomial's degree-one class in the native associated graded ring. -/
def paperVeroneseNormalDirection (r extra : ℕ) :
    PaperIdealAssociatedGraded (veroneseIdeal K (Fin (r + 1 + extra)) (r + 1)) :=
  (paperVeroneseNormalData K r extra).direction

/-- The squarefree source-constraint normal direction is never nilpotent. -/
theorem paperVeroneseNormalDirection_not_isNilpotent (r extra : ℕ) :
    ¬ IsNilpotent (paperVeroneseNormalDirection K r extra) :=
  (paperVeroneseNormalData K r extra).direction_not_isNilpotent

/-- Polynomial substitution into the actual Veronese associated graded ring. -/
def paperVeroneseNormalPolynomialMap (r extra : ℕ) :
    Polynomial K →+* PaperIdealAssociatedGraded (veroneseIdeal K (Fin (r + 1 + extra)) (r + 1)) :=
  (paperVeroneseNormalData K r extra).polynomialMap

/-- The selected face direction has no scalar polynomial relation. -/
theorem paperVeroneseNormalPolynomialMap_eq_zero_iff (r extra : ℕ) (p : Polynomial K) :
    paperVeroneseNormalPolynomialMap K r extra p = 0 ↔ p = 0 :=
  (paperVeroneseNormalData K r extra).polynomialMap_eq_zero_iff p

/-- A polynomial ring embeds into every positive-degree squarefree Veronese associated graded ring. -/
theorem paperVeroneseNormalPolynomialMap_injective (r extra : ℕ) :
    Function.Injective (paperVeroneseNormalPolynomialMap K r extra) :=
  (paperVeroneseNormalData K r extra).polynomialMap_injective

end

end GaloisForLFunctions.HTGeometry
