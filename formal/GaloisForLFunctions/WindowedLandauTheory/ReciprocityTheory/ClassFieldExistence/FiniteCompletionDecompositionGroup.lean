import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionAutomorphisms
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionTensorEquivalence
import Mathlib.FieldTheory.Finite.Basic

/-! The decomposition group is the full Galois group of the local extension. -/

noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

section Decomposition

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]


private theorem adicCompletionRingHomOf_algebraMap_adicCompletion (σ : L ≃ₐ[K] L)
    (hσ : σ • w.asIdeal = w.asIdeal) (c : v.adicCompletion K) :
    adicCompletionRingHomOf w σ hσ (algebraMap (v.adicCompletion K) (w.adicCompletion L) c) =
      algebraMap (v.adicCompletion K) (w.adicCompletion L) c := by
  have h := (denseRange_algebraMap (R := 𝓞 K) (K := K) v).equalizer
    ((continuous_adicCompletionRingHomOf w σ hσ).comp
      (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)))
    (continuous_algebraMap (v.adicCompletion K) (w.adicCompletion L)) (funext fun k ↦ ?_)
  · exact congrFun h c
  · simp only [Function.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      adicCompletionRingHomOf_algebraMap, AlgEquiv.commutes]

omit [NumberField K] [NumberField L] in
private theorem smul_asIdeal_of_mem_stabilizer (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    (σ : Gal(L/K)) • w.asIdeal = w.asIdeal :=
  MulAction.mem_stabilizer_iff.1 σ.2

private def decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    w.adicCompletion L ≃ₐ[v.adicCompletion K] w.adicCompletion L :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))
    (adicCompletionRingHomOf w (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹))
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)).comp
      (continuous_adicCompletionRingHomOf w (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp)
    (ringHom_ext_adicCompletion w
      ((continuous_adicCompletionRingHomOf w (σ⁻¹).1 (smul_asIdeal_of_mem_stabilizer w σ⁻¹)).comp
      (continuous_adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)))
      continuous_id fun x ↦ by
        rw [RingHom.comp_apply, adicCompletionRingHomOf_algebraMap,
          adicCompletionRingHomOf_algebraMap]
        simp))
    (adicCompletionRingHomOf_algebraMap_adicCompletion v w σ.1 (smul_asIdeal_of_mem_stabilizer w σ))

@[simp]
private theorem decompositionAlgEquiv_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionAlgEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  adicCompletionRingHomOf_algebraMap w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) x

private theorem continuous_decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    Continuous (decompositionAlgEquiv v w σ) :=
  continuous_adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ)


private theorem valued_decompositionAlgEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (y : w.adicCompletion L) : Valued.v (decompositionAlgEquiv v w σ y) = Valued.v y :=
  valued_adicCompletionRingHomOf w σ.1 (smul_asIdeal_of_mem_stabilizer w σ) y


private theorem algEquiv_ext_adicCompletion {f g : w.adicCompletion L ≃ₐ[v.adicCompletion K]
    w.adicCompletion L} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : L, f (algebraMap L _ x) = g (algebraMap L _ x)) : f = g :=
  AlgEquiv.ext fun y ↦ congrFun (congrArg DFunLike.coe
    (ringHom_ext_adicCompletion w (f := (f : w.adicCompletion L →+* w.adicCompletion L))
      (g := (g : w.adicCompletion L →+* w.adicCompletion L)) hf hg h)) y

private def decompositionToLocal :
    MulAction.stabilizer Gal(L/K) w.asIdeal →* Gal(w.adicCompletion L/v.adicCompletion K) where
  toFun := decompositionAlgEquiv v w
  map_one' := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w 1)
    continuous_id fun x ↦ by simp
  map_mul' σ τ := algEquiv_ext_adicCompletion v w (continuous_decompositionAlgEquiv v w _)
    ((continuous_decompositionAlgEquiv v w σ).comp (continuous_decompositionAlgEquiv v w τ))
    fun x ↦ by simp

@[simp]
private theorem decompositionToLocal_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionToLocal v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) ((σ : Gal(L/K)) x) :=
  decompositionAlgEquiv_algebraMap v w σ x


private theorem decompositionToLocal_injective : Function.Injective (decompositionToLocal v w) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun f : Gal(w.adicCompletion L/v.adicCompletion K) ↦
    f (algebraMap L (w.adicCompletion L) x)) hσ
  simp only [decompositionToLocal_algebraMap, AlgEquiv.one_apply] at this
  exact (algebraMap L (w.adicCompletion L)).injective this

end Decomposition

section Galois

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]
  (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

include v in

theorem card_decompositionGroup :
    Nat.card (MulAction.stabilizer Gal(L/K) w.asIdeal) =
      w.asIdeal.ramificationIdx (𝓞 K) * w.asIdeal.inertiaDeg (𝓞 K) := by
  letI := v.isMaximal
  letI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  letI : Finite v.asIdeal.ResidueField :=
    Finite.of_surjective _ v.asIdeal.bijective_algebraMap_quotient_residueField.surjective
  rw [Ideal.card_stabilizer_eq v.asIdeal w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal w.asIdeal Gal(L/K),
    Ideal.inertiaDegIn_eq_inertiaDeg v.asIdeal w.asIdeal Gal(L/K)]

private theorem decompositionToLocal_bijective : Function.Bijective (decompositionToLocal v w) := by
  refine (decompositionToLocal_injective v w).bijective_of_nat_card_le ?_
  rw [card_decompositionGroup v w, ← finiteCompletion_finrank_eq_ramification_mul_inertia L v w, Nat.card_eq_fintype_card]
  exact AlgEquiv.card_le

/-- The Galois group of the local extension is the decomposition group. -/
def decompositionMulEquiv :
    MulAction.stabilizer Gal(L/K) w.asIdeal ≃* Gal(w.adicCompletion L/v.adicCompletion K) :=
  MulEquiv.ofBijective (decompositionToLocal v w) (decompositionToLocal_bijective v w)

@[simp]
theorem decompositionMulEquiv_algebraMap (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) (x : L) :
    decompositionMulEquiv v w σ (algebraMap L (w.adicCompletion L) x) =
      algebraMap L (w.adicCompletion L) (σ.val x) :=
  decompositionToLocal_algebraMap v w σ x

theorem continuous_decompositionMulEquiv
    (σ : MulAction.stabilizer Gal(L/K) w.asIdeal) :
    Continuous (decompositionMulEquiv v w σ) :=
  continuous_decompositionAlgEquiv v w σ

theorem valued_decompositionMulEquiv (σ : MulAction.stabilizer Gal(L/K) w.asIdeal)
    (x : w.adicCompletion L) :
    Valued.v (decompositionMulEquiv v w σ x) = Valued.v x :=
  valued_decompositionAlgEquiv v w σ x

instance isGalois_adicCompletion : IsGalois (v.adicCompletion K) (w.adicCompletion L) :=
  IsGalois.of_card_aut_eq_finrank _ _ (by
    rw [← Nat.card_congr (decompositionMulEquiv v w).toEquiv, card_decompositionGroup v w,
      finiteCompletion_finrank_eq_ramification_mul_inertia L v w])

end Galois

end GlobalTheory.Reciprocity
