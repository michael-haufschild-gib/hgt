import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentReduction
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientContinuity

/-!
# Continuous normalization of actual elliptic unipotent streams

The embedded rational projection is the difference between the identity
and the continuous gap projection. Strict triangular recursion therefore
gives continuous embedded corrections and a continuous normalized stream
with values in the actual compact additive domain.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein
noncomputable section

/-- The diagonal rational component is continuous as an adele-valued function. -/
theorem continuous_adeleEmbeddedRationalProjection :
    Continuous fun a : Adeles => adeleEmbedding (adeleRationalProjection a) := by
  have he : (fun a : Adeles => adeleEmbedding (adeleRationalProjection a)) =
      (fun a => a - (adeleGapProjection a : Adeles)) := by
    funext a
    have h := adele_rational_add_gap a
    calc
      adeleEmbedding (adeleRationalProjection a) =
          (adeleEmbedding (adeleRationalProjection a) + (adeleGapProjection a : Adeles)) -
            (adeleGapProjection a : Adeles) := by abel
      _ = a - (adeleGapProjection a : Adeles) := by rw [h]
  rw [he]
  exact continuous_id.sub (continuous_subtype_val.comp continuous_adeleGapProjection)

/-- The current coordinate plus the nonlinear effect of earlier rational corrections. -/
def adeleUnipotentTriangularInput (n : ℕ) (x : ℕ → Adeles) : Adeles :=
  x n + unipotentTriangularCorrection n (fun i => x i.val)
    (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))

/-- Every recursively embedded rational correction depends continuously on the whole stream. -/
theorem continuous_adeleUnipotentCorrectionValue (n : ℕ) :
    Continuous fun x : ℕ → Adeles => adeleEmbedding (adeleUnipotentCorrectionStream x n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hf : Continuous fun x : ℕ → Adeles => (fun i : Fin n => x i.val) :=
      continuous_pi fun i => continuous_apply i.val
    have hg : Continuous fun x : ℕ → Adeles =>
        (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) :=
      continuous_pi fun i => ih i.val i.isLt
    have hp : Continuous fun x : ℕ → Adeles => unipotentTriangularCorrection n
        (fun i => x i.val) (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) :=
      Continuous.comp
        (g := fun p : (Fin n → Adeles) × (Fin n → Adeles) =>
          unipotentTriangularCorrection n p.1 p.2)
        (f := fun x : ℕ → Adeles => ((fun i : Fin n => x i.val),
          (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))))
        (continuous_unipotentTriangularCorrection (R := Adeles) n) (hf.prodMk hg)
    have ha : Continuous (adeleUnipotentTriangularInput n) := (continuous_apply n).add hp
    convert (continuous_adeleEmbeddedRationalProjection.comp ha).neg using 1
    funext x
    exact (congrArg adeleEmbedding (adeleUnipotentCorrectionStream_eq x n)).trans
      (map_neg adeleEmbedding _)

theorem continuous_adeleUnipotentTriangularInput (n : ℕ) :
    Continuous (adeleUnipotentTriangularInput n) := by
  have hf : Continuous fun x : ℕ → Adeles => (fun i : Fin n => x i.val) :=
    continuous_pi fun i => continuous_apply i.val
  have hg : Continuous fun x : ℕ → Adeles =>
      (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) :=
    continuous_pi fun i => continuous_adeleUnipotentCorrectionValue i.val
  have hp : Continuous fun x : ℕ → Adeles => unipotentTriangularCorrection n
      (fun i => x i.val) (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) :=
    Continuous.comp
      (g := fun p : (Fin n → Adeles) × (Fin n → Adeles) =>
        unipotentTriangularCorrection n p.1 p.2)
      (f := fun x : ℕ → Adeles => ((fun i : Fin n => x i.val),
        (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))))
      (continuous_unipotentTriangularCorrection (R := Adeles) n) (hf.prodMk hg)
  exact (continuous_apply n).add hp

/-- Canonical normalization into a stream of actual additive-domain representatives. -/
def adeleUnipotentNormalization (x : ℕ → Adeles) : ℕ → ellipticAdditiveDomain :=
  fun n => adeleGapProjection (adeleUnipotentTriangularInput n x)

/-- Normalizing a stream agrees with right reduction of its actual matrix. -/
theorem adeleUnipotentNormalization_stream (g : unipotentCoefficientGroup Adeles) (n : ℕ) :
    (adeleUnipotentNormalization (unipotentCoefficientStreamEquiv Adeles g) n : Adeles) =
      unipotentCoefficientStreamEquiv Adeles (adeleUnipotentReduced g) n :=
  (adeleUnipotentReduced_stream g n).symm

/-- Actual unipotent normalization is continuous for the product coefficient topologies. -/
theorem continuous_adeleUnipotentNormalization : Continuous adeleUnipotentNormalization :=
  continuous_pi fun n => continuous_adeleGapProjection.comp
    (continuous_adeleUnipotentTriangularInput n)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_adeleEmbeddedRationalProjection
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_adeleUnipotentCorrectionValue
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_adeleUnipotentNormalization
