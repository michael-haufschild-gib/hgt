import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeDegreeCompletionBaseChange
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.PrimeDegreeGaloisRestriction
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalArtinPrimeExponent
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.IdelicArtinBaseChange

/-! Local surjectivity in an extension of prime degree descends from a
small base change containing the roots of unity. The local degree and
the image of the upper Galois group are preserved by that base change. -/

noncomputable section

open NumberField IsDedekindDomain Module GaloisForLFunctions
open scoped GlobalTheory.Reciprocity.AdicLiesOver IsMulCommutative Pointwise

namespace GlobalTheory.Reciprocity

open IdeleGroup

variable (K A B M : Type) [Field K] [NumberField K] [Field A] [NumberField A]
  [Field B] [NumberField B] [Field M] [NumberField M] [Algebra K A] [Algebra K B]
  [Algebra K M] [Algebra A M] [Algebra B M] [IsScalarTower K A M] [IsScalarTower K B M]
  [IsAbelianGalois K A] [IsAbelianGalois K B] [IsAbelianGalois K M]
  [IsAbelianGalois B M]

local notation "Γ" => Gal(M/K)
local notation "H" => Gal(M/B)

local instance : CommGroup Γ :=
  { (inferInstance : Group Γ) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : CommGroup H :=
  { (inferInstance : Group H) with mul_comm := IsMulCommutative.is_comm.comm }

local instance : Fintype Γ := Fintype.ofFinite _

local instance : Fintype H := Fintype.ofFinite _

theorem finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree_baseChange
    {p : ℕ} [Fact p.Prime] [NeZero p] [HasEnoughRootsOfUnity B p]
    (hA : finrank K A = p) (hB : finrank K B < p) (hM : finrank B M ≤ p)
    (g : IdeleGroup K →* Gal(A/K)) (hg : IsFiniteIdelicArtin g)
    (hgd : ∀ a : Kˣ, g (diagonal K a) = 1)
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 A)) [w.asIdeal.LiesOver v.asIdeal]
    (hw : MulAction.stabilizer Gal(A/K) w.asIdeal = ⊤) :
    Function.Surjective (g.comp (finiteEmbedding v)) := by
  let W := primeAboveSpec (K := A) (L := M) w
  let u := W.under (𝓞 B)
  letI : W.asIdeal.LiesOver w.asIdeal := primeAbove_liesOver A M w
  letI : W.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans W.asIdeal w.asIdeal v.asIdeal
  letI : W.asIdeal.LiesOver u.asIdeal := ⟨rfl⟩
  letI : u.asIdeal.LiesOver v.asIdeal := by
    constructor
    change v.asIdeal = (W.asIdeal.under (𝓞 B)).under (𝓞 K)
    rw [Ideal.under_under]
    exact Ideal.LiesOver.over (p := v.asIdeal) (P := W.asIdeal)
  have hw' : finrank (v.adicCompletion K) (w.adicCompletion A) = p := by
    rw [← IsGalois.card_aut_eq_finrank (v.adicCompletion K) (w.adicCompletion A),
      ← Nat.card_congr (decompositionMulEquiv v w).toEquiv, hw, Subgroup.card_top,
      IsGalois.card_aut_eq_finrank, hA]
  have hlocal := finiteCompletion_finrank_eq_prime_after_baseChange Fact.out v w u W hw' hB hM
  have hpM : finrank B M = p := by
    apply le_antisymm hM
    have h := finiteCompletion_finrank_dvd u W
    rw [hlocal] at h
    exact Nat.le_of_dvd Module.finrank_pos h
  have hD : MulAction.stabilizer H W.asIdeal = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_congr (decompositionMulEquiv u W).toEquiv, IsGalois.card_aut_eq_finrank,
      hlocal, IsGalois.card_aut_eq_finrank, hpM]
  have hpow (τ : H) : τ ^ p = 1 := by
    rw [← hpM, ← IsGalois.card_aut_eq_finrank]
    exact pow_card_eq_one'
  obtain ⟨m, f, -, -, hfd, hfu, hfm⟩ := exists_finite_idelic_artin K M Γ
  obtain ⟨n, ψ, -, -, hψd, hψu, hψn⟩ := exists_finite_idelic_artin B M H
  have hf : IsFiniteIdelicArtin f := ⟨m, hfu, hfm⟩
  have hψ : IsFiniteIdelicArtin ψ := ⟨n, hψu, hψn⟩
  have hsurj : Function.Surjective (ψ.comp (finiteEmbedding u)) :=
    MonoidHom.range_eq_top.mp
      ((finiteIdelicArtin_range_eq_decomposition_of_prime_exponent ψ hψ hψd hpow u W).trans hD)
  let j : H →* Γ := AlgEquiv.restrictScalarsHom K
  let r : Γ →* Gal(A/K) := AlgEquiv.restrictNormalHom A
  have hj : Function.Surjective (r.comp j) :=
    surjective_restrictNormalHom_comp_restrictScalarsHom_of_prime_degree K A B M Fact.out hA hB
  have hnorm := finiteIdelicArtin_comp_ideleNorm K B M j (fun _ _ => rfl) f ψ hf hψ hfd hψd
  have hrest : r.comp f = g := finiteIdelicArtin_restrict_eq K A M f g hf hg hfd hgd
  intro σ
  obtain ⟨τ, hτ⟩ := hj σ
  obtain ⟨y, hy⟩ := hsurj τ
  let u' : finitePlacesAbove B v := ⟨u, (mem_finitePlacesAbove B v u).mpr inferInstance⟩
  let x := Units.map (Algebra.norm (v.adicCompletion K)) y
  have he := DFunLike.congr_fun hnorm (finiteEmbedding u y)
  change f (ideleNorm (finiteEmbedding u'.val y)) = j ((ψ.comp (finiteEmbedding u)) y) at he
  rw [ideleNorm_finiteEmbedding v u', hy] at he
  refine ⟨x, ?_⟩
  change g (finiteEmbedding v x) = σ
  rw [← hrest]
  change r (f (finiteEmbedding v x)) = σ
  rw [he]
  exact hτ

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.finiteIdelicArtin_surjective_at_full_decomposition_of_prime_degree_baseChange
