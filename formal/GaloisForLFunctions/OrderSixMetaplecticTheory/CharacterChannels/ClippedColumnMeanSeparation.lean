import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.ClippedReferenceRecovery
import GaloisForLFunctions.HilbertMetric.Correlation.ClippedColumnMeans

/-!
# Separating signed means from order-six residue fluctuations

For any finite family of actual projected row packets, subtracting the column
means splits the Gram matrix exactly. The mean term has rank at most one, so
the clipped residual bound pays a single cutoff square for all signed means.
These are finite empirical means; no analytic residue or remainder estimate
is assumed.
-/

noncomputable section
open Matrix
open scoped BigOperators Classical
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein
open HilbertMetric.Clipped

local instance : Finite ResidueFour :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
local instance : Fintype ResidueFour := Fintype.ofFinite _

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Columns are finite order-six packets with arbitrary finite supports and weights. -/
def projectedRowMatrix (S : κ → Finset O) (w : κ → O → ℂ) : Matrix ResidueFour κ ℂ :=
  fun r j => projectedRowPacket (S j) (w j) r

theorem projectedRowMatrix_columnMean (S : κ → Finset O) (w : κ → O → ℂ) (j : κ) :
    columnMean (projectedRowMatrix S w) j =
      finiteOrderSixMoment (S j) (w j) / (Fintype.card ResidueFour : ℂ) := by
  unfold columnMean projectedRowMatrix
  rw [sum_projectedRowPacket]

/-- Exact orthogonal separation of finite signed means and centered residue packets. -/
theorem projectedRowMatrix_gram_decomposition (S : κ → Finset O) (w : κ → O → ℂ) :
    (projectedRowMatrix S w)ᴴ * projectedRowMatrix S w =
      (centeredColumns (projectedRowMatrix S w))ᴴ * centeredColumns (projectedRowMatrix S w) +
        (meanColumns (projectedRowMatrix S w))ᴴ * meanColumns (projectedRowMatrix S w) :=
  centeredColumns_gram_decomposition _

theorem projectedRowMatrix_mean_rank_le_one (S : κ → Finset O) (w : κ → O → ℂ) :
    ((meanColumns (projectedRowMatrix S w))ᴴ * meanColumns (projectedRowMatrix S w)).rank ≤ 1 :=
  meanColumns_gram_rank_le_one _

/-- All signed row moments enter one bound with a single rank-one penalty. -/
theorem projectedRowMatrix_centered_clipped_bound
    (S : κ → Finset O) (w : κ → O → ℂ) (c : ℝ) :
    energy c ((centeredColumns (projectedRowMatrix S w))ᴴ *
        centeredColumns (projectedRowMatrix S w)) +
      2 * c * (Fintype.card ResidueFour * (∑ j,
        Complex.normSq (finiteOrderSixMoment (S j) (w j) /
          (Fintype.card ResidueFour : ℂ)))) - c ^ 2 ≤
      (trace (((projectedRowMatrix S w)ᴴ * projectedRowMatrix S w) *
        ((projectedRowMatrix S w)ᴴ * projectedRowMatrix S w))).re := by
  simpa only [projectedRowMatrix_columnMean] using
    centeredColumns_clipped_threshold (projectedRowMatrix S w) c

#print axioms projectedRowMatrix_gram_decomposition
#print axioms projectedRowMatrix_mean_rank_le_one
#print axioms projectedRowMatrix_centered_clipped_bound

end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
