import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageResidue
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbsoluteResidueOfNumberField
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.TameResidueArtinFormula

/-! The same uniformizer radical reads inverse Artin at all tame
stages of the same degree. The resulting residue fields are
identified inside the absolute residue field and the inertia
quotients agree under this identification. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField WithZero
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime]

private theorem LocalTameStage.valued_natCast (D : LocalTameStage h p n) :
    Valued.v (p : D.w.adicCompletion D.L) = exp (-1 : ℤ) := by
  let x : 𝓞 D.L := p
  let V := D.w.intValuation
  have hx : x ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hv : V x ≠ 0 := D.w.intValuation_ne_zero x hx
  have he : V x = exp (log (V x)) := (exp_log hv).symm
  have hsmall : V x < 1 := (D.w.intValuation_lt_one_iff_mem _).mpr D.natCast_mem
  have hlarge : ¬ V x ≤ exp (-((2 : ℕ) : ℤ)) :=
    fun hc => D.uniformizer ((D.w.intValuation_le_pow_iff_mem x 2).mp hc)
  rw [he, ← exp_zero, exp_lt_exp] at hsmall
  rw [he, exp_le_exp] at hlarge
  rw [← map_natCast (algebraMap (𝓞 D.L) (D.w.adicCompletion D.L)), valued_algebraMap_int]
  change V x = exp (-1 : ℤ)
  rw [he]
  congr 1
  omega

private theorem LocalTameStage.approximation_matches_uniformizerRadical
    (D : LocalTameStage h p n) {π : Ω} (hπ : π ^ (p ^ n - 1) = p)
    (s : Ine (F := D.L) A) (x : 𝓞 D.L)
    (hx : Valued.v ((D.artin (ineIncl D.hw s) : D.w.adicCompletion D.L) -
      algebraMap D.L (D.w.adicCompletion D.L) (x : D.L)) < 1) :
    A.valuation (s.val π / π - algebraMap D.L Ω (x : D.L)) < 1 := by
  let a : D.Lˣ := Units.mk0 (p : D.L) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have ha : Valued.v (algebraMap D.L (D.w.adicCompletion D.L) (a : D.L)) = exp (-1 : ℤ) := by
    change Valued.v (algebraMap D.L (D.w.adicCompletion D.L) (p : D.L)) = _
    rw [map_natCast, D.valued_natCast]
  have haπ : π ^ (normV D.w - 1) = algebraMap D.L Ω (a : D.L) := by
    rw [D.cardinality, hπ]
    exact (map_natCast (algebraMap D.L Ω) p).symm
  exact residue_inverseArtin_eq_uniformizerRadical D.L Ω D.hw ha π haπ D.artin_law s x hx

theorem exists_residueEquiv_intertwining_inertiaResidue
    (D D' : LocalTameStage h p n) :
    ∃ e : D.residue ≃+* D'.residue, ∀ t,
      D'.inertiaResidue t = Units.map e.toRingHom.toMonoidHom (D.inertiaResidue t) := by
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hn : 0 < n := by
    by_contra! hn
    have hc := one_lt_normV D.w
    rw [D.cardinality, Nat.eq_zero_of_le_zero hn, pow_zero] at hc
    exact lt_irrefl _ hc
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω)
    (Nat.sub_pos_of_lt (Nat.one_lt_pow hn.ne' hp))
  obtain ⟨f, hf⟩ := exists_absoluteResidueEmbedding A D.hw D.reduction
    D.reduction_surjective D.reduction_ker
  obtain ⟨f', hf'⟩ := exists_absoluteResidueEmbedding A D'.hw D'.reduction
    D'.reduction_surjective D'.reduction_ker
  have hcard : Nat.card D.residue = p ^ n :=
    (card_of_residueMap D.reduction D.reduction_surjective D.reduction_ker).trans D.cardinality
  have hcard' : Nat.card D'.residue = p ^ n :=
    (card_of_residueMap D'.reduction D'.reduction_surjective D'.reduction_ker).trans D'.cardinality
  letI : Finite D.residue := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  letI : Finite D'.residue := Nat.finite_of_card_ne_zero (by rw [hcard']; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  obtain ⟨e, he⟩ := exists_ringEquiv_of_same_finite_image_card f f' (hcard.trans hcard'.symm)
  refine ⟨e, fun t => Units.ext (f'.injective ?_)⟩
  obtain ⟨s, x, hs, hx, hz⟩ := D.exists_residue_approximation t
  obtain ⟨s', y, hs', hy, hz'⟩ := D'.exists_residue_approximation t
  have hσ : s.val π = s'.val π := congrArg (fun a : Ine (F := K) A => a.val π) (hs.trans hs'.symm)
  have hx' := D.approximation_matches_uniformizerRadical hπ s x hx
  have hy' := D'.approximation_matches_uniformizerRadical hπ s' y hy
  rw [hσ] at hx'
  have hxy : A.valuation (algebraMap D.L Ω (x : D.L) - algebraMap D'.L Ω (y : D'.L)) < 1 := by
    rw [show algebraMap D.L Ω (x : D.L) - algebraMap D'.L Ω (y : D'.L) =
      (s'.val π / π - algebraMap D'.L Ω (y : D'.L)) - (s'.val π / π - algebraMap D.L Ω (x : D.L)) by ring]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hy' hx')
  change f' ((D'.inertiaResidue t : D'.residueˣ) : D'.residue) =
    f' (e ((D.inertiaResidue t : D.residueˣ) : D.residue))
  rw [he, ← hz, ← hz', hf, hf']
  exact (absoluteIntegerResidue_eq_of_valuation_lt_one A x y hxy).symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.exists_residueEquiv_intertwining_inertiaResidue
