import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoverDeckAutomorphisms
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.HermitianCoverDegree


/-!
# Galoisness of the normalized Hermitian trace cover

The explicit trace-kernel translations and radical scalings give as
many distinct relative automorphisms as the already established field
degree. The equality criterion for Galois extensions then proves that
the constructed Hermitian covering is Galois.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d r m : ℕ)
local notation "H" => HermitianKummerField p (hermitianKummerCoverIndex d r m)
local notation "J" => (normalizedKummerHermitianEmbedding p d r m).fieldRange

/-- The actual Hermitian source is finite-dimensional over the image of the normalized cover. -/
instance normalizedKummerHermitianEmbedding_finiteDimensional : FiniteDimensional J H :=
  FiniteDimensional.of_finrank_pos (by
    rw [normalizedKummerHermitianEmbedding_finrank]
    apply Nat.mul_pos (pow_pos (Fact.out : p.Prime).pos _)
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.range (r + 1)) =>
      Nat.zero_le ((p ^ (d + 1)) ^ i)) (Finset.mem_range.mpr (Nat.succ_pos r))
    exact lt_of_lt_of_le Nat.zero_lt_one (by simpa only [kummerExponent, pow_zero] using h))

/-- The relative automorphism group has exactly the trace-cover degree. -/
theorem normalizedKummerHermitianEmbedding_card_aut :
    Nat.card (H ≃ₐ[J] H) =
      p ^ ((d + 1) * (r + 1) * m) * kummerExponent (p ^ (d + 1)) (r + 1) := by
  apply le_antisymm
  · have h : Nat.card (H ≃ₐ[J] H) ≤ Module.finrank J H := by
      rw [Nat.card_eq_fintype_card]
      exact AlgEquiv.card_le
    exact h.trans_eq (normalizedKummerHermitianEmbedding_finrank p d r m)
  · have h := Nat.card_le_card_of_injective (hermitianCoverRelativeAut p d r m)
      (hermitianCoverRelativeAut_injective p d r m)
    rw [hermitianCoverParameters_card] at h
    exact h

/-- Every normalized Hermitian trace cover is Galois over its actual image field. -/
theorem normalizedKummerHermitianEmbedding_isGalois : IsGalois J H :=
  IsGalois.of_card_aut_eq_finrank J H
    ((normalizedKummerHermitianEmbedding_card_aut p d r m).trans
      (normalizedKummerHermitianEmbedding_finrank p d r m).symm)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
