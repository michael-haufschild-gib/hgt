import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentContinuity

/-!
# Rational invariance and triangularity of unipotent normalization

Uniqueness of the rational correction makes normalization constant on
right rational cosets and fixes every domain-valued matrix. Equal earlier
coordinates give equal earlier corrections; an additive-domain increment
at the current coordinate therefore survives normalization unchanged.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein
noncomputable section

private theorem cancel_mapped_correction {G H : Type*} [Group G] [Group H]
    (f : H →* G) (g : G) (r c : H) : (g * f r) * f (r⁻¹ * c) = g * f c := by
  rw [map_mul, map_inv, mul_assoc g (f r) ((f r)⁻¹ * f c),
    ← mul_assoc (f r) (f r)⁻¹ (f c), mul_inv_cancel, one_mul]

/-- Right rational multiplication transforms the unique correction contragrediently. -/
theorem adeleUnipotentRationalCorrection_mul_rational
    (g : unipotentCoefficientGroup Adeles) (r : unipotentCoefficientGroup K) :
    adeleUnipotentRationalCorrection (g * unipotentCoefficientMap adeleEmbedding r) =
      r⁻¹ * adeleUnipotentRationalCorrection g := by
  symm
  apply adeleUnipotentRationalCorrection_unique
  intro n
  rw [cancel_mapped_correction]
  exact adeleUnipotentReduced_mem g n

/-- Reduction is constant on each right completed-rational coset. -/
theorem adeleUnipotentReduced_mul_rational
    (g : unipotentCoefficientGroup Adeles) (r : unipotentCoefficientGroup K) :
    adeleUnipotentReduced (g * unipotentCoefficientMap adeleEmbedding r) =
      adeleUnipotentReduced g := by
  change (g * unipotentCoefficientMap adeleEmbedding r) *
    unipotentCoefficientMap adeleEmbedding
      (adeleUnipotentRationalCorrection (g * unipotentCoefficientMap adeleEmbedding r)) = _
  rw [adeleUnipotentRationalCorrection_mul_rational, cancel_mapped_correction]
  rfl

/-- A domain-valued matrix needs no rational correction. -/
theorem adeleUnipotentRationalCorrection_of_domain (g : unipotentCoefficientGroup Adeles)
    (hg : ∀ n, unipotentCoefficientStreamEquiv Adeles g n ∈ ellipticAdditiveDomain) :
    adeleUnipotentRationalCorrection g = 1 := by
  symm
  apply adeleUnipotentRationalCorrection_unique
  simpa only [map_one, mul_one] using hg

/-- Canonical reduction fixes the actual domain representatives. -/
theorem adeleUnipotentReduced_of_domain (g : unipotentCoefficientGroup Adeles)
    (hg : ∀ n, unipotentCoefficientStreamEquiv Adeles g n ∈ ellipticAdditiveDomain) :
    adeleUnipotentReduced g = g := by
  change g * unipotentCoefficientMap adeleEmbedding (adeleUnipotentRationalCorrection g) = g
  rw [adeleUnipotentRationalCorrection_of_domain g hg, map_one, mul_one]

/-- A correction coordinate depends only on the input through the same index. -/
theorem adeleUnipotentCorrectionStream_prefix_congr (x y : ℕ → Adeles) (n : ℕ)
    (hxy : ∀ k, k ≤ n → x k = y k) :
    adeleUnipotentCorrectionStream x n = adeleUnipotentCorrectionStream y n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hp : (fun i : Fin n => x i.val) = (fun i : Fin n => y i.val) := by
      funext i
      exact hxy i.val i.isLt.le
    have hc : (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) =
        (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream y i.val)) := by
      funext i
      exact congrArg adeleEmbedding (ih i.val i.isLt (fun k hk => hxy k (hk.trans i.isLt.le)))
    rw [adeleUnipotentCorrectionStream_eq x n, adeleUnipotentCorrectionStream_eq y n,
      hxy n le_rfl, hp, hc]

/-- Normalization has coefficient one on a current additive-domain increment. -/
theorem adeleUnipotentNormalization_coordinate_add (x y : ℕ → Adeles) (n : ℕ)
    (d : ellipticAdditiveDomain) (hp : ∀ k, k < n → x k = y k)
    (hn : x n = y n + (d : Adeles)) :
    adeleUnipotentNormalization x n = adeleUnipotentNormalization y n + d := by
  have hx : (fun i : Fin n => x i.val) = (fun i : Fin n => y i.val) := by
    funext i
    exact hp i.val i.isLt
  have hc : (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream x i.val)) =
      (fun i : Fin n => adeleEmbedding (adeleUnipotentCorrectionStream y i.val)) := by
    funext i
    exact congrArg adeleEmbedding (adeleUnipotentCorrectionStream_prefix_congr x y i.val
      (fun k hk => hp k (lt_of_le_of_lt hk i.isLt)))
  have he : adeleUnipotentTriangularInput n x = adeleUnipotentTriangularInput n y + (d : Adeles) := by
    unfold adeleUnipotentTriangularInput
    rw [hn, hx, hc]
    abel
  change adeleGapProjection (adeleUnipotentTriangularInput n x) =
    adeleGapProjection (adeleUnipotentTriangularInput n y) + d
  rw [he, map_add, adeleGapProjection_domain]

/-- Normalization fixes every stream in the actual additive domain. -/
theorem adeleUnipotentNormalization_domain (d : ℕ → ellipticAdditiveDomain) :
    adeleUnipotentNormalization (fun n => (d n : Adeles)) = d := by
  let g := (unipotentCoefficientStreamEquiv Adeles).symm (fun n => (d n : Adeles))
  have hg : ∀ n, unipotentCoefficientStreamEquiv Adeles g n ∈ ellipticAdditiveDomain := by
    intro n
    change unipotentCoefficientStreamEquiv Adeles
      ((unipotentCoefficientStreamEquiv Adeles).symm _) n ∈ ellipticAdditiveDomain
    rw [Equiv.apply_symm_apply]
    exact (d n).property
  funext n
  apply Subtype.ext
  have h := adeleUnipotentNormalization_stream g n
  rw [adeleUnipotentReduced_of_domain g hg] at h
  simpa only [g, Equiv.apply_symm_apply] using h

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentReduced_mul_rational
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentReduced_of_domain
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentNormalization_coordinate_add
