import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ConjugateLocalRayNormalization
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RelativeAutomorphismConjugation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.RelativeFrobeniusConjugation
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.FixedFieldIdelicKernel

/-! The finite idelic Artin symbol of a local factor commutes with
conjugation. Rational ray normalization reduces the identity to the
conjugation law for arithmetic Frobenius at primes. -/

noncomputable section

open NumberField IsDedekindDomain GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative Pointwise nonZeroDivisors GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay
attribute [local instance] primeMulAction

variable (K L M : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsAbelianGalois K L] [IsAbelianGalois L M]

local notation "G" => Gal(L/K)
local notation "H" => Gal(M/L)
local notation "Γ" => Gal(M/K)
local notation "r" => (AlgEquiv.restrictNormalHom L : Γ →* G)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype H := Fintype.ofFinite _

private theorem smul_algebraMap_ringOfIntegers_conj (t : Γ) (x : 𝓞 L) :
    t • algebraMap (𝓞 L) (𝓞 M) x = algebraMap (𝓞 L) (𝓞 M) (r t • x) :=
  RingOfIntegers.ext (t.restrictNormal_commutes L (x : L)).symm

private theorem frobeniusElement_smul_eq_relativeAutConj (t : Γ)
    {p : HeightOneSpectrum (𝓞 L)} (hp : IsUnramifiedPrime L M H p)
    (hpt : IsUnramifiedPrime L M H (r t • p)) :
    frobeniusElement L M H (r t • p) =
      relativeAutConj K L M t (frobeniusElement L M H p) := by
  let P := primeAbove L M p
  let Q : Ideal (𝓞 M) := t • P
  letI : Q.IsMaximal := by
    rw [show Q = t • P from rfl, Ideal.pointwise_smul_def]
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv Γ (𝓞 M) t)
  letI : Q.LiesOver (r t • p).asIdeal := by
    constructor
    rw [show Q = t • P from rfl, under_smul_eq_map_smul_under r
      (fun z x => (smul_algebraMap_ringOfIntegers_conj K L M z x).symm),
      ← Ideal.over_def P p.asIdeal]
    exact asIdeal_prime_smul L G (r t) p
  let e := restrictionKernelEquiv K L M
  letI : SMulCommClass H (𝓞 L) (𝓞 M) :=
    ⟨fun s a x => RingOfIntegers.ext (by
      change s (algebraMap L M (a : L) * (x : M)) = algebraMap L M (a : L) * s (x : M)
      rw [map_mul, s.commutes])⟩
  letI : SMulCommClass (r).ker (𝓞 L) (𝓞 M) :=
    ⟨fun z a x => smul_comm (e z) a x⟩
  let σ := frobeniusElement L M H p
  have hσ : IsArithFrobAt (𝓞 L) σ P := IsArithFrobAt.arithFrobAt (𝓞 L) H P
  have hσ' : IsArithFrobAt (𝓞 L) (e.symm σ) P := fun x => hσ x
  have hconj := conjugateIn_isArithFrobAt r (smul_algebraMap_ringOfIntegers_conj K L M) hσ' t
  have he : IsArithFrobAt (𝓞 L) (relativeAutConj K L M t σ) Q := fun x => hconj x
  have hi := he.mul_inv_mem_inertia (IsArithFrobAt.arithFrobAt (𝓞 L) H Q)
  rw [hpt Q inferInstance inferInstance, Subgroup.mem_bot,
    arithFrobAt_eq_frobeniusElement hpt Q] at hi
  exact (mul_inv_eq_one.mp hi).symm

theorem finiteIdelicArtin_finiteEmbedding_conjugate
    (f : IdeleGroup L →* H) (hf : IsFiniteIdelicArtin f) (hd : ∀ a : Lˣ, f (diagonal L a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]
    (t : Γ) (ht : r t ∈ MulAction.stabilizer G w.asIdeal) (x : (w.adicCompletion L)ˣ) :
    f (finiteEmbedding w (Units.map (decompositionMulEquiv v w ⟨r t, ht⟩).toMonoidHom x)) =
      relativeAutConj K L M t (f (finiteEmbedding w x)) := by
  classical
  let g : MulAction.stabilizer G w.asIdeal := ⟨r t, ht⟩
  let y := Units.map (decompositionMulEquiv v w g).toMonoidHom x
  obtain ⟨m, hm, he⟩ := hf
  let c := m.fin.absNorm
  letI : NeZero c := ⟨fun h => m.fin_ne_bot (Ideal.absNorm_eq_zero_iff.mp h)⟩
  have hc : (normModulus L c).fin ≤ m.fin := normModulus_fin_le_of_absNorm_dvd L m (dvd_refl c)
  obtain ⟨a, ha⟩ := exists_diagonal_mul_mem_idelesOneMod (normModulus L c) (finiteEmbedding w x)
  let a' := fieldUnitsMap L G (r t) a
  let Y := diagonal L a * finiteEmbedding w x
  let Y' := diagonal L a' * finiteEmbedding w y
  have hY : Y ∈ idelesOneMod (normModulus L c) := ha
  have hY' : Y' ∈ idelesOneMod (normModulus L c) :=
    diagonal_finiteEmbedding_conjugate_mem_idelesOneMod v w g c a x hY
  have heY : f Y = f (finiteEmbedding w x) := by
    change f (diagonal L a * finiteEmbedding w x) = _
    rw [map_mul, hd, one_mul]
  have heY' : f Y' = f (finiteEmbedding w y) := by
    change f (diagonal L a' * finiteEmbedding w y) = _
    rw [map_mul, hd, one_mul]
  have hArt (X : idelesOneMod (normModulus L c)) :
      f X.val = ∏ᶠ p : HeightOneSpectrum (𝓞 L),
        frobeniusOrOne L M H p ^ ord p X.val := by
    rw [he ⟨X.val, idelesOneMod_le_of_refinement hc (Set.subset_univ _) X.2⟩]
    change artinMap L M H (∏ᶠ p, idealUnit p.ne_bot ^ ord p X.val) = _
    rw [(artinMap L M H).map_finprod (finite_mulSupport_primeIdealUnit_zpow_ord X.val)]
    simp only [map_zpow, artinMap_idealUnit_prime]
  let e : HeightOneSpectrum (𝓞 L) ≃ HeightOneSpectrum (𝓞 L) := MulAction.toPerm (r t)
  let F (p : HeightOneSpectrum (𝓞 L)) := frobeniusOrOne L M H p ^ ord p Y'
  have hfin : (Function.mulSupport (fun p : HeightOneSpectrum (𝓞 L) =>
      frobeniusOrOne L M H p ^ ord p Y)).Finite :=
    (Filter.eventually_cofinite.1 (eventually_ord_eq_zero Y)).subset fun p hp h =>
      hp (by
        change frobeniusOrOne L M H p ^ ord p Y = 1
        rw [h, zpow_zero])
  change f (finiteEmbedding w y) = relativeAutConj K L M t (f (finiteEmbedding w x))
  rw [← heY', ← heY, hArt ⟨Y', hY'⟩, hArt ⟨Y, hY⟩,
    (relativeAutConj K L M t).map_finprod hfin]
  change (∏ᶠ p, F p) = _
  rw [← finprod_comp_equiv e (f := F)]
  apply finprod_congr
  intro p
  change frobeniusOrOne L M H (r t • p) ^ ord (r t • p) Y' =
    relativeAutConj K L M t (frobeniusOrOne L M H p ^ ord p Y)
  have hord : ord (r t • p) Y' = ord p Y :=
    ord_diagonal_finiteEmbedding_conjugate v w g a x p
  rw [hord, map_zpow]
  by_cases hp : p.asIdeal ∣ (normModulus L c).fin
  · rw [ord_eq_zero_of_mem_idelesOneMod _ hY hp, zpow_zero, zpow_zero]
  · have hp' := (prime_dvd_normModulus_smul_iff L G c (r t) p).not.mpr hp
    have hu (q : HeightOneSpectrum (𝓞 L)) (hq : ¬ q.asIdeal ∣ (normModulus L c).fin) :
        IsUnramifiedPrime L M H q :=
      not_not.mp fun h => hq (Ideal.dvd_iff_le.mpr (hc.trans (Ideal.dvd_iff_le.mp ((hm q).mpr h))))
    rw [frobeniusOrOne, frobeniusOrOne, if_pos (hu _ hp'), if_pos (hu _ hp),
      frobeniusElement_smul_eq_relativeAutConj K L M t (hu _ hp) (hu _ hp')]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_finiteEmbedding_conjugate
