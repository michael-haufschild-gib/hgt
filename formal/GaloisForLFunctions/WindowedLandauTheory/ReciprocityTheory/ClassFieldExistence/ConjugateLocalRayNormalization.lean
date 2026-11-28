import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.ConjugatePrimeNorm
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.RationalRayRefinement

/-! Conjugating a local coordinate and its diagonal normalizer preserves
rational ray congruences and permutes the ideal divisor. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open GaloisForLFunctions GaloisForLFunctions.HeckeLFunctions
open scoped IsMulCommutative Pointwise GlobalTheory.Reciprocity.AdicLiesOver

namespace GlobalTheory.Reciprocity

open IdeleGroup IdeleRay
attribute [local instance] primeMulAction

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsAbelianGalois K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

local notation "G" => Gal(L/K)

local instance : CommGroup G :=
  { (inferInstance : Group G) with mul_comm := IsMulCommutative.is_comm.comm }

private theorem smul_prime_eq_self_of_mem_stabilizer
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) : g.val • w = w := by
  apply HeightOneSpectrum.ext
  rw [asIdeal_prime_smul L G, MulAction.mem_stabilizer_iff.mp g.2]

private theorem normModulus_exponent_smul (t : G) (c : ℕ) [NeZero c] (p : HeightOneSpectrum (𝓞 L)) :
    exponent (normModulus L c) (t • p) = exponent (normModulus L c) p := by
  have hc : (c : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne c)
  have h : (t • p).valuation L (c : L) = p.valuation L (c : L) := by
    rw [prime_smul_valuation]
    change p.valuation L (t⁻¹ (c : L)) = _
    rw [map_natCast]
  rw [← map_natCast (algebraMap (𝓞 L) L), valuation_of_algebraMap, valuation_of_algebraMap,
    intValuation_eq_exp_neg_multiplicity _ hc, intValuation_eq_exp_neg_multiplicity _ hc,
    WithZero.exp_inj, neg_inj, Nat.cast_inj] at h
  exact h

private theorem coe_fieldUnitsMap_apply (t : G) (a : Lˣ) :
    (fieldUnitsMap L G t a : L) = t • (a : L) := rfl

/-- The completed automorphism on units extends the diagonal action. -/
theorem units_map_decompositionMulEquiv_diag
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) (a : Lˣ) :
    Units.map (decompositionMulEquiv v w g).toMonoidHom (finiteProj w (diagonal L a)) =
      finiteProj w (diagonal L (fieldUnitsMap L G g.val a)) := by
  apply Units.ext
  rw [Units.coe_map, coe_finiteProj_diagonal, coe_finiteProj_diagonal]
  exact decompositionMulEquiv_algebraMap v w g (a : L)

private theorem unitsLevel_of_decompositionMulEquiv
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) (n : ℕ)
    (x : (w.adicCompletion L)ˣ) (hx : x ∈ unitsLevel (K := L) w n) :
    Units.map (decompositionMulEquiv v w g).toMonoidHom x ∈ unitsLevel (K := L) w n := by
  obtain ⟨hx₁, hx₂⟩ := mem_unitsLevel.mp hx
  apply mem_unitsLevel.mpr
  change Valued.v ((decompositionMulEquiv v w g) (x : w.adicCompletion L)) = 1 ∧
    Valued.v ((decompositionMulEquiv v w g) (x : w.adicCompletion L) - 1) ≤ exp (-(n : ℤ))
  rw [← map_one (decompositionMulEquiv v w g), ← map_sub,
    valued_decompositionMulEquiv, valued_decompositionMulEquiv]
  exact ⟨hx₁, hx₂⟩

def completedUnitsAction (g : MulAction.stabilizer Gal(L/K) w.asIdeal) : (w.adicCompletion L)ˣ →* (w.adicCompletion L)ˣ :=
  Units.map (decompositionMulEquiv v w g).toMonoidHom

theorem diagonal_finiteEmbedding_conjugate_mem_idelesOneMod
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) (c : ℕ) [NeZero c] (a : Lˣ) (x : (w.adicCompletion L)ˣ)
    (h : diagonal L a * finiteEmbedding w x ∈ idelesOneMod (normModulus L c)) :
    diagonal L (fieldUnitsMap L G g.val a) * finiteEmbedding w (completedUnitsAction v w g x) ∈
      idelesOneMod (normModulus L c) := by
  obtain ⟨hfin, hinf⟩ := (mem_idelesOneMod _).mp h
  apply (mem_idelesOneMod _).mpr
  constructor
  · intro p hp
    let q := g.val⁻¹ • p
    have he : g.val • q = p := smul_inv_smul _ _
    have hq : q.asIdeal ∣ (normModulus L c).fin :=
      (prime_dvd_normModulus_smul_iff L G c g.val q).mp (he.symm ▸ hp)
    have hn := normModulus_exponent_smul g.val c q
    rw [he] at hn
    by_cases hpw : p = w
    · rw [hpw, map_mul, finiteProj_finiteEmbedding, completedUnitsAction,
        ← units_map_decompositionMulEquiv_diag v w g a, ← map_mul]
      apply unitsLevel_of_decompositionMulEquiv v w g
      simpa only [map_mul, finiteProj_finiteEmbedding] using hfin w (hpw ▸ hp)
    · have hqw : q ≠ w := by
        intro eq
        apply hpw
        rw [← he, eq, smul_prime_eq_self_of_mem_stabilizer w g]
      have hu := hfin q hq
      rw [map_mul, finiteProj_finiteEmbedding_of_ne hqw, mul_one] at hu
      rw [map_mul, finiteProj_finiteEmbedding_of_ne hpw, mul_one]
      rw [mem_unitsLevel_of_one_le ((one_le_exponent_iff _ p).mpr hp),
        coe_finiteProj_diagonal, hn]
      rw [mem_unitsLevel_of_one_le ((one_le_exponent_iff _ q).mpr hq),
        coe_finiteProj_diagonal] at hu
      change Valued.v (algebraMap L (p.adicCompletion L) (fieldUnitsMap L G g.val a : L) - 1) ≤ _
      change Valued.v (algebraMap L (q.adicCompletion L) (a : L) - 1) ≤ _ at hu
      have hvp (z : L) : Valued.v (algebraMap L (p.adicCompletion L) z) = p.valuation L z :=
        valuedAdicCompletion_eq_valuation' p z
      have hvq (z : L) : Valued.v (algebraMap L (q.adicCompletion L) z) = q.valuation L z :=
        valuedAdicCompletion_eq_valuation' q z
      rw [← map_one (algebraMap L (p.adicCompletion L)), ← map_sub,
        coe_fieldUnitsMap_apply, hvp]
      rw [← map_one (algebraMap L (q.adicCompletion L)), ← map_sub, hvq] at hu
      rw [← he, prime_smul_valuation, smul_sub, inv_smul_smul, smul_one]
      exact hu
  · intro p _
    let q : {u : InfinitePlace L // u.IsReal} :=
      ⟨p.1.comap g.val.toRingEquiv.toRingHom, p.2.comap _⟩
    have hu := hinf q (Set.mem_univ q)
    rw [map_mul, infiniteProj_finiteEmbedding, mul_one, coe_infiniteProj_diagonal,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe] at hu ⊢
    rw [coe_fieldUnitsMap_apply]
    have hEq : InfinitePlace.embedding_of_isReal p.2 (g.val • (a : L)) =
        InfinitePlace.embedding_of_isReal q.2 (a : L) := by
      apply Complex.ofReal_injective
      rw [InfinitePlace.embedding_of_isReal_apply, InfinitePlace.embedding_of_isReal_apply]
      change p.1.embedding (g.val (a : L)) = (p.1.comap g.val.toRingEquiv.toRingHom).embedding (a : L)
      rw [InfinitePlace.comap_embedding_of_isReal _ q.2]
      rfl
    change 0 < InfinitePlace.embedding_of_isReal p.2 (g.val • (a : L))
    change 0 < InfinitePlace.embedding_of_isReal q.2 (a : L) at hu
    exact hEq.symm ▸ hu

theorem ord_diagonal_finiteEmbedding_conjugate
    (g : MulAction.stabilizer Gal(L/K) w.asIdeal) (a : Lˣ) (x : (w.adicCompletion L)ˣ)
    (p : HeightOneSpectrum (𝓞 L)) :
    ord (g.val • p) (diagonal L (fieldUnitsMap L G g.val a) * finiteEmbedding w (completedUnitsAction v w g x)) =
      ord p (diagonal L a * finiteEmbedding w x) := by
  rw [ord_mul, ord_mul, ord_diagonal, ord_diagonal, coe_fieldUnitsMap_apply,
    prime_smul_valuation, inv_smul_smul]
  by_cases hp : p = w
  · subst p
    rw [smul_prime_eq_self_of_mem_stabilizer w g, ord_finiteEmbedding_self, ord_finiteEmbedding_self, completedUnitsAction,
      Units.coe_map]
    have hval : Valued.v (((decompositionMulEquiv v w g).toMonoidHom) (x : w.adicCompletion L)) =
        Valued.v (x : w.adicCompletion L) := valued_decompositionMulEquiv v w g _
    rw [hval]
  · have h : g.val • p ≠ w := by
      intro he
      apply hp
      have he' := congrArg (fun q : HeightOneSpectrum (𝓞 L) => g.val⁻¹ • q)
        (he.trans (smul_prime_eq_self_of_mem_stabilizer w g).symm)
      simpa only [inv_smul_smul] using he'
    rw [ord_finiteEmbedding_of_ne h, ord_finiteEmbedding_of_ne hp]

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.diagonal_finiteEmbedding_conjugate_mem_idelesOneMod
#print axioms GlobalTheory.Reciprocity.ord_diagonal_finiteEmbedding_conjugate
