import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.OpenIdelicSubgroupOfLocalPowers
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeExponentKummerBound
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteIdelicArtinLocalImages

/-! At prime exponent, an Artin factor that detects every local power
class surjects onto decomposition. The group of local power classes
bounds the degree of the completed extension by Kummer theory. -/

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.Kummer
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsAbelianGalois K L]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

theorem finiteIdelicArtin_range_eq_decomposition_of_power_kernel
    {p : ℕ} [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity K p]
    (f : IdeleGroup K →* G) (hf : IsFiniteIdelicArtin f)
    (hd : ∀ a : Kˣ, f (diagonal K a) = 1)
    (hpow : ∀ σ : G, σ ^ p = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (hker : (f.comp (finiteEmbedding v)).ker =
      (powMonoidHom p : (v.adicCompletion K)ˣ →* _).range) :
    (f.comp (finiteEmbedding v)).range = MulAction.stabilizer G w.asIdeal := by
  let F := v.adicCompletion K
  letI : CharZero F := Algebra.charZero_of_charZero K F
  let E := w.adicCompletion L
  let D := MulAction.stabilizer G w.asIdeal
  let r := f.comp (finiteEmbedding v)
  let e := decompositionMulEquiv v w
  letI : IsAbelianGalois F E := {
    is_comm.comm x y := by
      obtain ⟨x, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← map_mul, ← map_mul, mul_comm] }
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  letI : HasEnoughRootsOfUnity F p :=
    ⟨⟨algebraMap K F ζ, hζ.map_of_injective (algebraMap K F).injective⟩,
      rootsOfUnity.isCyclic F p⟩
  letI : Finite (PowerClasses F p) := finite_finiteCompletionPowerClasses (n := p) v
  have hE (σ : Gal(E/F)) : σ ^ p = 1 := by
    obtain ⟨τ, rfl⟩ := e.surjective σ
    have hτ : τ ^ p = 1 := Subtype.ext (hpow τ.val)
    rw [← map_pow, hτ, map_one]
  have hbound := finrank_le_card_powerClasses_of_prime_exponent (F := F) (E := E) hE
  let q := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivRange r)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, rfl⟩
    exact finiteIdelicArtin_finiteEmbedding_mem_decomposition f hf hd v w x
  · change Nat.card D ≤ Nat.card r.range
    rw [← Nat.card_congr q.toEquiv, Nat.card_congr e.toEquiv, IsGalois.card_aut_eq_finrank]
    exact hbound

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_range_eq_decomposition_of_power_kernel
