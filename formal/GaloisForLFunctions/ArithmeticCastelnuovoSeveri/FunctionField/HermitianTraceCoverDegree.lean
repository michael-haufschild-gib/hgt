import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianTraceFieldEmbedding
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.RationalPolynomialSubfields
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalBaseDegree


/-!
# Exact degree of the Hermitian trace cover

The trace-power polynomial has degree `p^((d+1)(r+1)m) R`. Both radical
fields have degree `Q+1` over their rational coordinate subfields.
Comparing these two towers cancels the radical degree and gives the
exact degree of the actual embedded Kummer field in the Hermitian field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial ArithmeticHarmonicAnalysis
open scoped IntermediateField
variable {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : Kˣ) (d r m : ℕ)

/-- Exact degree of the actual field extension defined by the Hermitian trace substitution. -/
theorem hermitianKummerFieldHom_finrank :
    Module.finrank (hermitianKummerFieldHom p c d r m).fieldRange
      (HermitianTraceSourceField p c d r m) =
        p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  let Q := p ^ ((d + 1) * (r + 1) * (m + 1))
  let R := kummerExponent (p ^ (d + 1)) (r + 1)
  let H := HermitianTraceSourceField p c d r m
  let L := KummerBranchField (c ^ R) (p ^ (d + 1) - 2) R Q
  let f := hermitianKummerFieldHom p c d r m
  let x := algebraMap K[X] H X
  let y := hermitianTraceFieldCoordinate p c d r m
  let A := K⟮y⟯
  let B := K⟮x⟯
  let J := f.fieldRange
  let P : K[X] := frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) X ^ R
  have hP : aeval x P = y := by
    change aeval x (frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) X ^ R) =
      frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x ^ R
    simp only [frobeniusTraceSum, map_pow, map_sum, aeval_X]
  have hd : (d + 1) * (r + 1) - 1 + 1 = (d + 1) * (r + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos r))
  have hdeg : P.natDegree = p ^ ((d + 1) * (r + 1) * m) * R := by
    dsimp only [P]
    rw [natDegree_pow]
    have ht := frobeniusTraceSum_polynomial_natDegree (K := K) p ((d + 1) * (r + 1) - 1) m
    rw [hd] at ht
    rw [ht, Nat.mul_comm]
  have hAB : A.relfinrank B = p ^ ((d + 1) * (r + 1) * m) * R := by
    have h := polynomialCoordinate_relfinrank
      (kummerBranchField_coordinate_transcendental c (Q - 2) 1 Q) P
    rw [hP, hdeg] at h
    exact h
  have hB : Module.finrank B H = Q + 1 :=
    kummerBranchField_coordinate_finrank c (Q - 2) 1 Q
  have hAJ : A.relfinrank J = Q + 1 := by
    have h := IntermediateField.relfinrank_map_map
      K⟮algebraMap K[X] L X⟯ (⊤ : IntermediateField K L) f
    rw [IntermediateField.adjoin_map, Set.image_singleton,
      hermitianKummerFieldHom_coordinate, ← AlgHom.fieldRange_eq_map,
      IntermediateField.relfinrank_top_right, kummerBranchField_coordinate_finrank] at h
    exact h
  have hleAB : A ≤ B := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    change (frobeniusTraceSum p ((d + 1) * (r + 1)) (m + 1) x) ^ R ∈ B
    apply pow_mem
    unfold frobeniusTraceSum
    exact sum_mem fun i _ => pow_mem (IntermediateField.mem_adjoin_simple_self K x) _
  have hleAJ : A ≤ J := by
    apply IntermediateField.adjoin_simple_le_iff.mpr
    exact ⟨algebraMap K[X] L X, hermitianKummerFieldHom_coordinate p c d r m⟩
  have h₁ := IntermediateField.relfinrank_mul_finrank_top hleAB
  have h₂ := IntermediateField.relfinrank_mul_finrank_top hleAJ
  rw [hAB, hB] at h₁
  rw [hAJ] at h₂
  apply Nat.eq_of_mul_eq_mul_left (Nat.succ_pos Q)
  calc
    (Q + 1) * Module.finrank J H = Module.finrank A H := h₂
    _ = (p ^ ((d + 1) * (r + 1) * m) * R) * (Q + 1) := h₁.symm
    _ = (Q + 1) * (p ^ ((d + 1) * (r + 1) * m) * R) := Nat.mul_comm _ _

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
