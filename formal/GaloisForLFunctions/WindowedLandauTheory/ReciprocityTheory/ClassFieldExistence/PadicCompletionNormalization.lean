import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.FiniteCompletionPowerIndex
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.GaloisValuations.Global
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Analysis.SpecificLimits.Normed

/-! At a completion topologically isomorphic to the p-adic field, the
rational prime is a uniformizer and the residue field has size p. -/

noncomputable section

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open GaloisForLFunctions.HTGeometry.ABHN
open WindowedLandauTheory.ConjugateSelfDual
open scoped WithZero ValuativeRel

namespace GlobalTheory.Reciprocity

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

private theorem norm_lt_one_of_padicIso_iff (v : NumberField.FinitePlace K)
    (i : ℚ_[p] ≃+* v.maximalIdeal.adicCompletion K) (hi : Continuous i) (x : ℚ_[p]) :
    ‖i x‖ < 1 ↔ ‖x‖ < 1 := by
  have ho : IsOpenMap i :=
    AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hi
  have h_inv : Continuous i.symm :=
    (i.toEquiv.toHomeomorphOfContinuousOpen hi ho).symm.continuous
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  exact ⟨fun h => by
    simpa only [Function.comp_def, ← map_pow, RingEquiv.symm_apply_apply, map_zero] using
      (h_inv.tendsto 0).comp h,
    fun h => by
      simpa only [Function.comp_def, map_pow, map_zero] using (hi.tendsto 0).comp h⟩

private theorem norm_le_one_of_padicIso_iff (v : NumberField.FinitePlace K)
    (i : ℚ_[p] ≃+* v.maximalIdeal.adicCompletion K) (hi : Continuous i) (x : ℚ_[p]) :
    ‖i x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have he := norm_lt_one_of_padicIso_iff v i hi x⁻¹
  rw [map_inv₀, norm_inv, norm_inv,
    inv_lt_one₀ (norm_pos_iff.mpr ((map_ne_zero i).mpr hx)),
    inv_lt_one₀ (norm_pos_iff.mpr hx)] at he
  simpa only [not_lt] using he.not

/-- A continuous p-adic isomorphism restricts to the rings of integers. -/
def padicCompletionIntegersEquiv (u : NumberField.FinitePlace K)
    (i : ℚ_[p] ≃+* u.maximalIdeal.adicCompletion K) (hi : Continuous i) :
    ℤ_[p] ≃+* u.maximalIdeal.adicCompletionIntegers K := by
  let v := u.maximalIdeal
  let F := v.adicCompletion K
  have h (x : ℚ_[p]) : Valued.v (i x) ≤ 1 ↔ ‖x‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.symm.trans (norm_le_one_of_padicIso_iff u i hi x)
  refine
    { toFun := fun x => ⟨i x.val, (h x.val).mpr x.2⟩
      invFun := fun y => ⟨i.symm y.val, (h _).mp (by rw [i.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => Subtype.ext (i.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (i.apply_symm_apply y.val)
      map_mul' := fun x y => Subtype.ext (map_mul i x.val y.val)
      map_add' := fun x y => Subtype.ext (map_add i x.val y.val) }

theorem padicIso_place_normalization (v : HeightOneSpectrum (𝓞 K))
    (i : ℚ_[p] ≃+* v.adicCompletion K) (hi : Continuous i) :
    (p : 𝓞 K) ∈ v.asIdeal ∧ (p : 𝓞 K) ∉ v.asIdeal ^ 2 ∧ normV v = p ∧
      Valued.v (p : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨u, rfl⟩ := (FinitePlace.equivHeightOneSpectrum (K := K)).surjective v
  let v := u.maximalIdeal
  let F := v.adicCompletion K
  let V : Valuation F ℤᵐ⁰ := Valued.v
  let e := padicCompletionIntegersEquiv u i hi
  let e' : ℤ_[p] ≃+* 𝒪[F] := e.trans (RingEquiv.subringCongr (valuationSubring_eq_integer V))
  have hπ : Irreducible (e' (p : ℤ_[p])) := PadicInt.irreducible_p.map e'.toMulEquiv
  have hv := irreducible_intValuation_eq_exp_neg_one V (valuedAdicCompletion_surjective K v) hπ
  have hp : V (p : F) = WithZero.exp (-1 : ℤ) := by
    change V (i ((p : ℤ_[p]) : ℚ_[p])) = _ at hv
    have he : i ((p : ℤ_[p]) : ℚ_[p]) = (p : F) :=
      (congrArg i (PadicInt.coe_natCast p)).trans (map_natCast i p)
    exact (congrArg V he).symm.trans hv
  have hval : v.intValuation (p : 𝓞 K) = WithZero.exp (-1 : ℤ) := by
    have h := valuedAdicCompletion_eq_valuation (K := K) (v := v) (p : 𝓞 K)
    rw [valuation_of_algebraMap] at h
    change V (algebraMap (𝓞 K) F (p : 𝓞 K)) = _ at h
    rw [map_natCast (algebraMap (𝓞 K) F)] at h
    exact h.symm.trans hp
  refine ⟨(v.intValuation_lt_one_iff_mem _).mp ?_, fun hs => ?_, ?_, hp⟩
  · rw [hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · have hl := (v.intValuation_le_pow_iff_mem (p : 𝓞 K) 2).mpr hs
    rw [hval, WithZero.exp_le_exp] at hl
    norm_num at hl
  · have h := WindowedLandauTheory.UG.P.tjcosets_card_residue v
    change Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) = normV v at h
    change normV v = p
    rw [← h]
    exact (Nat.card_congr ((IsLocalRing.ResidueField.mapEquiv e.symm).trans PadicInt.residueField).toEquiv).trans
      (Nat.card_zmod p)

end GlobalTheory.Reciprocity
