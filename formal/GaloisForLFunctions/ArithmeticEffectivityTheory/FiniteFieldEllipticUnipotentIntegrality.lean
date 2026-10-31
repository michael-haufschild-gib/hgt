import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticUnipotentReduction
import GaloisForLFunctions.HTGeometry.LoopEisenstein.UnipotentCoefficientSubring

/-!
# Uniform finite-place integrality of unipotent reduction

The rational correction preserves each finite place at which the whole
input stream is integral. Thus one finite exceptional-place set suffices
for every coefficient of the completed correction. The reduced stream is
integral at all finite places because it lies in the additive domain.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open HTGeometry.LoopEisenstein Filter
noncomputable section

/-- Adeles integral at one specified finite place. -/
def adeleIntegralAt (v : FinitePlace) : Subring Adeles where
  carrier := {a | a.1 v ∈ v.adicCompletionIntegers K}
  zero_mem' := (v.adicCompletionIntegers K).zero_mem
  one_mem' := (v.adicCompletionIntegers K).one_mem
  add_mem' ha hb := (v.adicCompletionIntegers K).toSubring.add_mem ha hb
  mul_mem' ha hb := (v.adicCompletionIntegers K).toSubring.mul_mem ha hb
  neg_mem' ha := (v.adicCompletionIntegers K).toSubring.neg_mem ha

/-- Completed unipotent matrices with one common finite exceptional-place set. -/
def uniformlyIntegralUnipotent : Subgroup (unipotentCoefficientGroup Adeles) where
  carrier := {g | ∀ᶠ v : FinitePlace in cofinite, g ∈ unipotentCoefficientSubring (adeleIntegralAt v)}
  one_mem' := by
    change ∀ᶠ v : FinitePlace in cofinite, 1 ∈ unipotentCoefficientSubring (adeleIntegralAt v)
    exact Eventually.of_forall fun v => (unipotentCoefficientSubring (adeleIntegralAt v)).one_mem
  mul_mem' := by
    intro g h hg hh
    change ∀ᶠ v : FinitePlace in cofinite, g ∈ unipotentCoefficientSubring (adeleIntegralAt v) at hg
    change ∀ᶠ v : FinitePlace in cofinite, h ∈ unipotentCoefficientSubring (adeleIntegralAt v) at hh
    change ∀ᶠ v : FinitePlace in cofinite, g * h ∈ unipotentCoefficientSubring (adeleIntegralAt v)
    filter_upwards [hg, hh] with v hv hw
    exact (unipotentCoefficientSubring (adeleIntegralAt v)).mul_mem hv hw
  inv_mem' := by
    intro g hg
    change ∀ᶠ v : FinitePlace in cofinite, g ∈ unipotentCoefficientSubring (adeleIntegralAt v) at hg
    change ∀ᶠ v : FinitePlace in cofinite, g⁻¹ ∈ unipotentCoefficientSubring (adeleIntegralAt v)
    exact hg.mono fun v hv => (unipotentCoefficientSubring (adeleIntegralAt v)).inv_mem hv

theorem mem_uniformlyIntegralUnipotent (g : unipotentCoefficientGroup Adeles) :
    g ∈ uniformlyIntegralUnipotent ↔
      ∀ᶠ v : FinitePlace in cofinite, ∀ n,
        unipotentCoefficientStreamEquiv Adeles g n ∈ adeleIntegralAt v := by
  constructor
  · intro h
    change ∀ᶠ v : FinitePlace in cofinite, g ∈ unipotentCoefficientSubring (adeleIntegralAt v) at h
    exact h.mono fun v hv => (mem_unipotentCoefficientSubring (adeleIntegralAt v) g).mp hv
  · intro h
    exact h.mono fun v hv => (mem_unipotentCoefficientSubring (adeleIntegralAt v) g).mpr hv

/-- Rational completed unipotents whose diagonal coefficients have uniform finite-place integrality. -/
def uniformlyIntegralRationalUnipotent : Subgroup (unipotentCoefficientGroup K) :=
  uniformlyIntegralUnipotent.comap (unipotentCoefficientMap adeleEmbedding)

/-- The correction preserves any finite place where every original coefficient is integral. -/
theorem adeleUnipotentCorrectionStream_integral_at (x : ℕ → Adeles) (v : FinitePlace)
    (hx : ∀ n, x n ∈ adeleIntegralAt v) (n : ℕ) :
    adeleEmbedding (adeleUnipotentCorrectionStream x n) ∈ adeleIntegralAt v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [adeleUnipotentCorrectionStream_eq, map_neg]
    apply (adeleIntegralAt v).neg_mem
    apply adeleRationalProjection_integral_at
    exact (adeleIntegralAt v).add_mem (hx n)
      (unipotentTriangularCorrection_mem_subring (adeleIntegralAt v) n _ _
        (fun i => hx i.val) (fun i => ih i.val i.isLt))

/-- The complete rational correction introduces no new finite exceptional place. -/
theorem adeleUnipotentRationalCorrection_uniform (g : unipotentCoefficientGroup Adeles)
    (hg : g ∈ uniformlyIntegralUnipotent) :
    adeleUnipotentRationalCorrection g ∈ uniformlyIntegralRationalUnipotent := by
  apply (mem_uniformlyIntegralUnipotent _).mpr
  filter_upwards [(mem_uniformlyIntegralUnipotent g).mp hg] with v hv
  intro n
  rw [unipotentStream_map]
  change adeleEmbedding (unipotentCoefficientStreamEquiv K
    ((unipotentCoefficientStreamEquiv K).symm
      (adeleUnipotentCorrectionStream (unipotentCoefficientStreamEquiv Adeles g))) n) ∈ adeleIntegralAt v
  rw [Equiv.apply_symm_apply]
  exact adeleUnipotentCorrectionStream_integral_at _ v hv n

/-- Reduced matrices are integral at every finite place, uniformly in all coefficients. -/
theorem adeleUnipotentReduced_uniform (g : unipotentCoefficientGroup Adeles) :
    adeleUnipotentReduced g ∈ uniformlyIntegralUnipotent := by
  apply (mem_uniformlyIntegralUnipotent _).mpr
  apply Eventually.of_forall
  intro v n
  exact (adeleUnipotentReduced_mem g n).1 v

/-- Uniqueness of the canonical representative holds inside the uniformly restricted arithmetic group. -/
theorem existsUnique_uniformlyIntegralUnipotentCorrection (g : uniformlyIntegralUnipotent) :
    ∃! r : uniformlyIntegralRationalUnipotent, ∀ n,
      unipotentCoefficientStreamEquiv Adeles
        ((g : unipotentCoefficientGroup Adeles) * unipotentCoefficientMap adeleEmbedding r) n ∈
          ellipticAdditiveDomain := by
  refine ⟨⟨adeleUnipotentRationalCorrection g, adeleUnipotentRationalCorrection_uniform g g.property⟩,
    adeleUnipotentReduced_mem g, ?_⟩
  intro r hr
  apply Subtype.ext
  exact adeleUnipotentRationalCorrection_unique g r hr

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentCorrectionStream_integral_at
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adeleUnipotentRationalCorrection_uniform
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.existsUnique_uniformlyIntegralUnipotentCorrection
