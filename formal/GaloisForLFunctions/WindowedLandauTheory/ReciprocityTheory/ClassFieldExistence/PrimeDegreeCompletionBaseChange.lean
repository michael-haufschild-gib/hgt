import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionDecompositionGroup
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionTower

/-! Local degrees divide the global degree in a Galois extension.
A local degree p survives a base change of degree less than p whenever
the upper extension has degree at most p. -/

noncomputable section

open NumberField IsDedekindDomain Module
open scoped GlobalTheory.Reciprocity.AdicLiesOver Pointwise

namespace GlobalTheory.Reciprocity

theorem finiteCompletion_finrank_dvd {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] :
    finrank (v.adicCompletion K) (w.adicCompletion L) ∣ finrank K L := by
  rw [← IsGalois.card_aut_eq_finrank (v.adicCompletion K) (w.adicCompletion L),
    ← Nat.card_congr (decompositionMulEquiv v w).toEquiv, ← IsGalois.card_aut_eq_finrank K L]
  exact Subgroup.card_subgroup_dvd_card _

variable {K A B L : Type*} [Field K] [NumberField K] [Field A] [NumberField A]
  [Field B] [NumberField B] [Field L] [NumberField L] [Algebra K A] [Algebra K B]
  [Algebra K L] [Algebra A L] [Algebra B L] [IsScalarTower K A L] [IsScalarTower K B L]
  [IsGalois K B] [IsGalois B L]

theorem finiteCompletion_finrank_eq_prime_after_baseChange {p : ℕ} (hp : p.Prime)
    (v : HeightOneSpectrum (𝓞 K)) (a : HeightOneSpectrum (𝓞 A))
    (b : HeightOneSpectrum (𝓞 B)) (w : HeightOneSpectrum (𝓞 L))
    [a.asIdeal.LiesOver v.asIdeal] [b.asIdeal.LiesOver v.asIdeal]
    [w.asIdeal.LiesOver a.asIdeal] [w.asIdeal.LiesOver b.asIdeal] [w.asIdeal.LiesOver v.asIdeal]
    (ha : finrank (v.adicCompletion K) (a.adicCompletion A) = p)
    (hb : finrank K B < p) (hL : finrank B L ≤ p) :
    finrank (b.adicCompletion B) (w.adicCompletion L) = p := by
  letI := finiteCompletion_isScalarTower v a w
  letI := finiteCompletion_isScalarTower v b w
  have h := finrank_mul_finrank (v.adicCompletion K) (a.adicCompletion A) (w.adicCompletion L)
  rw [ha, ← finrank_mul_finrank (v.adicCompletion K) (b.adicCompletion B) (w.adicCompletion L)] at h
  have hdiv : p ∣ finrank (v.adicCompletion K) (b.adicCompletion B) *
      finrank (b.adicCompletion B) (w.adicCompletion L) :=
    ⟨_, h.symm⟩
  have hsmall : finrank (v.adicCompletion K) (b.adicCompletion B) < p :=
    (Nat.le_of_dvd Module.finrank_pos (finiteCompletion_finrank_dvd v b)).trans_lt hb
  have hndvd : ¬ p ∣ finrank (v.adicCompletion K) (b.adicCompletion B) :=
    fun hd => hsmall.not_ge (Nat.le_of_dvd Module.finrank_pos hd)
  have hpdvd := (hp.dvd_mul.mp hdiv).resolve_left hndvd
  exact le_antisymm
    ((Nat.le_of_dvd Module.finrank_pos (finiteCompletion_finrank_dvd b w)).trans hL)
    (Nat.le_of_dvd Module.finrank_pos hpdvd)

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteCompletion_finrank_eq_prime_after_baseChange
