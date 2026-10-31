import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdditiveSplitting
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientMap
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentTriangularMultiplication

/-!
# Canonical rational reduction of elliptic unipotent matrices

The additive fundamental domain and triangular multiplication determine
one completed rational matrix whose right action reduces every stream
coordinate. Strong induction proves uniqueness. This construction takes
place over the adele ring; uniform integrality is not part of its definition.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein
noncomputable section

/-- Rational coordinates removing the diagonal part of each successive product coefficient. -/
def adeleUnipotentCorrectionStream (x : ℕ → Adeles) (n : ℕ) : K :=
  -adeleRationalProjection (x n + unipotentTriangularCorrection n
    (fun i => x i.val) (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)))
termination_by n
decreasing_by exact i.isLt

theorem adeleUnipotentCorrectionStream_eq (x : ℕ → Adeles) (n : ℕ) :
    adeleUnipotentCorrectionStream x n =
      -adeleRationalProjection (x n + unipotentTriangularCorrection n
        (fun i => x i.val) (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))) := by
  rw [adeleUnipotentCorrectionStream]

/-- The single completed rational matrix determined by the recursive correction stream. -/
def adeleUnipotentRationalCorrection (g : unipotentCoefficientGroup Adeles) :
    unipotentCoefficientGroup K :=
  (unipotentCoefficientStreamEquiv K).symm
    (adeleUnipotentCorrectionStream (unipotentCoefficientStreamEquiv Adeles g))

/-- Right rational reduction of the actual completed unipotent matrix. -/
def adeleUnipotentReduced (g : unipotentCoefficientGroup Adeles) :
    unipotentCoefficientGroup Adeles :=
  g * unipotentCoefficientMap adeleEmbedding (adeleUnipotentRationalCorrection g)

/-- Each reduced coordinate is the additive gap projection of its triangular input. -/
theorem adeleUnipotentReduced_stream (g : unipotentCoefficientGroup Adeles) (n : ℕ) :
    unipotentCoefficientStreamEquiv Adeles (adeleUnipotentReduced g) n =
      (adeleGapProjection (unipotentCoefficientStreamEquiv Adeles g n +
        unipotentTriangularCorrection n
          (fun i => unipotentCoefficientStreamEquiv Adeles g i.val)
          (fun i => adeleEmbedding
            (adeleUnipotentCorrectionStream (unipotentCoefficientStreamEquiv Adeles g) i.val))) : Adeles) := by
  let x := unipotentCoefficientStreamEquiv Adeles g
  let p := unipotentTriangularCorrection n (fun i => x i.val)
    (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))
  have hc := adeleUnipotentCorrectionStream_eq x n
  change adeleUnipotentCorrectionStream x n = -adeleRationalProjection (x n + p) at hc
  simp only [adeleUnipotentReduced, unipotentStream_mul, unipotentStream_map,
    adeleUnipotentRationalCorrection, Equiv.apply_symm_apply]
  change x n + adeleEmbedding (adeleUnipotentCorrectionStream x n) + p =
    (adeleGapProjection (x n + p) : Adeles)
  rw [hc, map_neg]
  have hs := adele_rational_add_gap (x n + p)
  calc
    x n + -adeleEmbedding (adeleRationalProjection (x n + p)) + p =
        (x n + p) - adeleEmbedding (adeleRationalProjection (x n + p)) := by abel
    _ = (adeleGapProjection (x n + p) : Adeles) := by
      rw [← hs]
      abel

/-- Every coordinate of the reduced matrix belongs to the actual compact additive domain. -/
theorem adeleUnipotentReduced_mem (g : unipotentCoefficientGroup Adeles) (n : ℕ) :
    unipotentCoefficientStreamEquiv Adeles (adeleUnipotentReduced g) n ∈ ellipticAdditiveDomain := by
  rw [adeleUnipotentReduced_stream]
  exact (adeleGapProjection _).property

/-- The completed rational correction is forced by membership in the additive domain. -/
theorem adeleUnipotentRationalCorrection_unique (g : unipotentCoefficientGroup Adeles)
    (r : unipotentCoefficientGroup K)
    (hr : ∀ n, unipotentCoefficientStreamEquiv Adeles
      (g * unipotentCoefficientMap adeleEmbedding r) n ∈ ellipticAdditiveDomain) :
    r = adeleUnipotentRationalCorrection g := by
  apply (unipotentCoefficientStreamEquiv K).injective
  change unipotentCoefficientStreamEquiv K r =
    unipotentCoefficientStreamEquiv K ((unipotentCoefficientStreamEquiv K).symm _)
  rw [Equiv.apply_symm_apply]
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let x := unipotentCoefficientStreamEquiv Adeles g
    let p := unipotentTriangularCorrection n (fun i => x i.val)
      (fun i => adeleEmbedding (adeleUnipotentCorrectionStream x i.val))
    have hp : (fun i : Fin n => adeleEmbedding (unipotentCoefficientStreamEquiv K r i.val)) =
        (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) := by
      funext i
      exact congrArg adeleEmbedding (ih i.val i.isLt)
    have hd := adeleRationalProjection_domain
      (⟨unipotentCoefficientStreamEquiv Adeles
        (g * unipotentCoefficientMap adeleEmbedding r) n, hr n⟩ : ellipticAdditiveDomain)
    change adeleRationalProjection (unipotentCoefficientStreamEquiv Adeles
      (g * unipotentCoefficientMap adeleEmbedding r) n) = 0 at hd
    simp only [unipotentStream_mul, unipotentStream_map] at hd
    rw [hp] at hd
    change adeleRationalProjection
      (x n + adeleEmbedding (unipotentCoefficientStreamEquiv K r n) + p) = 0 at hd
    rw [map_add, map_add, adeleRationalProjection_diagonal] at hd
    change unipotentCoefficientStreamEquiv K r n = adeleUnipotentCorrectionStream x n
    rw [adeleUnipotentCorrectionStream_eq]
    change unipotentCoefficientStreamEquiv K r n = -adeleRationalProjection (x n + p)
    calc
      unipotentCoefficientStreamEquiv K r n =
          (adeleRationalProjection (x n) + unipotentCoefficientStreamEquiv K r n +
            adeleRationalProjection p) - adeleRationalProjection (x n + p) := by
        rw [map_add]
        ring
      _ = -adeleRationalProjection (x n + p) := by rw [hd, zero_sub]

/-- Every actual unipotent matrix has exactly one completed rational correction into the domain. -/
theorem existsUnique_adeleUnipotentRationalCorrection (g : unipotentCoefficientGroup Adeles) :
    ∃! r : unipotentCoefficientGroup K, ∀ n,
      unipotentCoefficientStreamEquiv Adeles (g * unipotentCoefficientMap adeleEmbedding r) n ∈
        ellipticAdditiveDomain :=
  ⟨adeleUnipotentRationalCorrection g, adeleUnipotentReduced_mem g,
    fun r hr => adeleUnipotentRationalCorrection_unique g r hr⟩

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentReduced_mem
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentRationalCorrection_unique
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.existsUnique_adeleUnipotentRationalCorrection
