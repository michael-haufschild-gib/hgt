import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverCechRestriction

/-! Restrict weighted cochains along an order embedding of index sets. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.WH

variable {k E : Type*} {ι κ : Type} [CommRing k] [LinearOrder ι] [LinearOrder κ]
  [AddCommGroup E] [Module k E]

/-- An order embedding preserves each sign and each deletion in the
weighted differential. -/
theorem wd_orderEmbedding (e : ι ↪o κ) (w : κ → Module.End k E)
    (c : Finset κ → E) (I : Finset ι) :
    wd (fun i => w (e i)) (fun J => c (J.map e.toEmbedding)) I =
      wd w c (I.map e.toEmbedding) := by
  rw [wd_apply, wd_apply, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsign : cubeSign (I.map e.toEmbedding) (e i) = cubeSign I i := by
    simpa only [Int.cast_id] using
      GlobalTheory.SchemeCohomology.cechSign_orderEmbedding (R := ℤ) e I i
  rw [Finset.map_erase]
  simp only [RelEmbedding.coe_toEmbedding, hsign]

end GlobalTheory.WH
