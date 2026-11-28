import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.MaximalKummerSubextension
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionTower
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup

/-! A character of the local decomposition group of exponent dividing n
kills automorphisms fixing a global subfield whose selected completion
has the full n-th power-class degree. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IntermediateField GlobalTheory.Kummer
open scoped IsMulCommutative Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

variable {K E M : Type} [Field K] [NumberField K] [Field E] [NumberField E]
  [Field M] [NumberField M] [Algebra K E] [Algebra K M] [Algebra E M]
  [IsScalarTower K E M] [IsAbelianGalois K E] [IsGalois K M]
  (v : HeightOneSpectrum (𝓞 K)) (u : HeightOneSpectrum (𝓞 E)) (w : HeightOneSpectrum (𝓞 M))
  [u.asIdeal.LiesOver v.asIdeal] [w.asIdeal.LiesOver u.asIdeal] [w.asIdeal.LiesOver v.asIdeal]

local notation "Fv" => v.adicCompletion K
local notation "Pv" => u.adicCompletion E
local notation "Qv" => w.adicCompletion M

private theorem completedAutomorphism_fixes_completion_of_fixes_base
    (s : MulAction.stabilizer Gal(M/K) w.asIdeal)
    (hs : ∀ x : E, s.val (algebraMap E M x) = algebraMap E M x) :
    ∀ x : Pv, decompositionMulEquiv v w s (AdicLiesOver.completionMap u w x) =
      AdicLiesOver.completionMap u w x := by
  let f := AdicLiesOver.completionMap u w
  have he := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 E) (K := E) u).equalizer
    ((continuous_decompositionMulEquiv v w s).comp (AdicLiesOver.continuous_completionMap u w))
    (AdicLiesOver.continuous_completionMap u w) (funext fun x => by
      change decompositionMulEquiv v w s (f (algebraMap E Pv x)) = f (algebraMap E Pv x)
      rw [show f = AdicLiesOver.completionMap u w from rfl, AdicLiesOver.completionMap_algebraMap,
        decompositionMulEquiv_algebraMap, hs])
  exact congrFun he

theorem decompositionCharacter_eq_one_of_saturated_completion
    {H : Type*} [CommGroup H] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
    [Finite (PowerClasses Fv n)] (hEp : ∀ s : Gal(E/K), s ^ n = 1)
    (hErank : Module.finrank Fv Pv = Nat.card (PowerClasses Fv n))
    (ψ : MulAction.stabilizer Gal(M/K) w.asIdeal →* H) (hψ : ∀ s, ψ s ^ n = 1)
    (s : MulAction.stabilizer Gal(M/K) w.asIdeal)
    (hs : ∀ x : E, s.val (algebraMap E M x) = algebraMap E M x) : ψ s = 1 := by
  letI : IsScalarTower Fv Pv Qv := finiteCompletion_isScalarTower v u w
  letI : CharZero Fv := Algebra.charZero_of_charZero K Fv
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  letI : HasEnoughRootsOfUnity Fv n :=
    ⟨⟨algebraMap K Fv ζ, hζ.map_of_injective (algebraMap K Fv).injective⟩,
      rootsOfUnity.isCyclic Fv n⟩
  let e := decompositionMulEquiv v u
  have hcomm (x y : Gal(Pv/Fv)) : x * y = y * x := by
    apply e.symm.injective
    rw [map_mul e.symm, map_mul e.symm]
    apply Subtype.ext
    exact IsMulCommutative.is_comm.comm _ _
  letI : IsAbelianGalois Fv Pv := { is_comm.comm := hcomm }
  let k := IsScalarTower.toAlgHom Fv Pv Qv
  let R := k.fieldRange
  let eR := k.equivFieldRange
  letI : IsAbelianGalois Fv R := IsAbelianGalois.of_algHom eR.symm.toAlgHom
  have hR (τ : Gal(R/Fv)) : τ ^ n = 1 := by
    obtain ⟨x, rfl⟩ := eR.autCongr.surjective τ
    obtain ⟨z, rfl⟩ := e.surjective x
    rw [← map_pow, ← map_pow, show z ^ n = 1 from Subtype.ext (hEp z.val), map_one, map_one]
  have hrank : Module.finrank Fv R = Nat.card (PowerClasses Fv n) :=
    eR.toLinearEquiv.finrank_eq.symm.trans hErank
  let eQ := decompositionMulEquiv v w
  let χ := ψ.comp eQ.symm.toMonoidHom
  have hfix : eQ s ∈ R.fixingSubgroup := by
    apply (R.mem_fixingSubgroup_iff (eQ s)).mpr
    rintro _ ⟨x, rfl⟩
    exact completedAutomorphism_fixes_completion_of_fixes_base v u w s hs x
  have heq := character_eq_one_of_mem_fixingSubgroup_of_saturation R hR hrank
    χ (fun τ => hψ (eQ.symm τ)) hfix
  change ψ (eQ.symm (eQ s)) = 1 at heq
  rwa [eQ.symm_apply_apply] at heq

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.decompositionCharacter_eq_one_of_saturated_completion
