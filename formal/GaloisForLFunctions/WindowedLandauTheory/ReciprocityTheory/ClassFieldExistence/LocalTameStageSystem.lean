import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.LocalTameStageResidue
import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.ClassFieldExistence.AbsoluteResidueOfNumberField
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FrobeniusPowerOnTameInertia

/-! Every tame stage gives a finite inertia quotient with open
kernel killing wild inertia. Frobenius acts by the base residue
cardinality power, including for nonnormal number-field stages. -/

noncomputable section

open NumberField IsDedekindDomain IntermediateField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open GlobalTheory.TameKummer

namespace GlobalTheory.Reciprocity

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A v}
  {p n : ℕ} [Fact p.Prime] (D : LocalTameStage h p n)

theorem LocalTameStage.finite_residue : Finite D.residue := by
  letI : Finite (𝓞 D.L ⧸ D.w.asIdeal) := D.w.asIdeal.finiteQuotientOfFreeOfNeBot D.w.ne_bot
  exact Finite.of_equiv _ D.residueEquiv.toEquiv

theorem LocalTameStage.residue_rank : Module.finrank (ZMod p) D.residue = n := by
  letI := D.finite_residue
  letI : Fintype D.residue := Fintype.ofFinite _
  have hc := (card_of_residueMap D.reduction D.reduction_surjective D.reduction_ker).trans D.cardinality
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card] at hc
  exact (pow_right_strictMono₀ (Fact.out : p.Prime).one_lt).injective hc

private theorem LocalTameStage.inertiaResidue_eq_one_iff (t : Ine (F := K) A) :
    D.inertiaResidue t = 1 ↔ D.artin (ineIncl D.hw (D.inertiaEquiv.symm t)) ∈ unitsLevel D.w 1 := by
  let e := Units.mapEquiv D.residueEquiv.toMulEquiv
  let s := D.inertiaEquiv.symm t
  let u := localArtinOnInertia D.artin_law s
  change e (finiteCompletionUnitReduction D.w u) = 1 ↔ _
  rw [← map_one e, e.injective.eq_iff, finiteCompletionUnitReduction_eq_one_iff]
  exact (mem_unitsLevel_one_iff_lt_one D.w _).symm

theorem LocalTameStage.inertiaResidue_open_ker : IsOpen (D.inertiaResidue.ker : Set (Ine (F := K) A)) := by
  have hs : (D.inertiaResidue.ker : Set (Ine (F := K) A)) =
      (fun t => D.artin (ineIncl D.hw (D.inertiaEquiv.symm t))) ⁻¹' (unitsLevel (K := D.L) D.w 1 : Set (D.w.adicCompletion D.L)ˣ) :=
    Set.ext fun t => D.inertiaResidue_eq_one_iff t
  rw [hs]
  exact (isOpen_unitsLevel (K := D.L) D.w 1).preimage
    (D.artin_law.cont.comp D.continuous_inertiaEquiv_symm)

theorem LocalTameStage.inertiaResidue_wild (t : Ine (F := K) A) (ht : t.val ∈ wildInertia A) :
    D.inertiaResidue t = 1 := by
  let s := D.inertiaEquiv.symm t
  have he (x : Ω) : s.val x = t.val x :=
    congrArg (fun u : Ine (F := K) A => u.val x) (D.inertiaEquiv.apply_symm_apply t)
  have hs : s.val ∈ wildInertia A := (mem_wildInertia_iff _ _).mpr fun x hx => by
    rw [he x]
    exact (mem_wildInertia_iff _ _).mp ht x hx
  exact (D.inertiaResidue_eq_one_iff t).mpr
    (artin_mem_unitsLevel_one_of_mem_wildInertia D.artin_law (ineIncl D.hw s) hs)

theorem LocalTameStage.inertiaResidue_conjugation
    (φ : Weil h) (hφ : deg φ = 1) (t t' : Ine (F := K) A)
    (ht : ineIncl h t' = φ * ineIncl h t * φ⁻¹) :
    D.inertiaResidue t' = D.inertiaResidue t ^ normV v := by
  have hp : A.valuation (p : Ω) < 1 := by
    simpa only [map_natCast] using (h (p : 𝓞 K)).mpr D.base_natCast_mem
  obtain ⟨hd, hw⟩ := frobenius_conj_div_wild_of_card A hp t.2 (deg_eq_one_iff.mp hφ)
  let δ : Ine (F := K) A := ⟨_, hd⟩
  have hδ := D.inertiaResidue_wild δ ((mem_wildInertia_iff _ _).mpr hw)
  have he : δ = (t ^ normV v)⁻¹ * t' := by
    apply Subtype.ext
    change (t.val ^ normV v)⁻¹ * (φ.val * t.val * φ.val⁻¹) = _
    rw [← show (t'.val : Gal(Ω/K)) = φ.val * t.val * φ.val⁻¹ from congrArg Subtype.val ht]
    rfl
  rw [he, map_mul, map_inv, map_pow, inv_mul_eq_one] at hδ
  exact hδ.symm

end GlobalTheory.Reciprocity

#print axioms GlobalTheory.Reciprocity.LocalTameStage.residue_rank
#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaResidue_open_ker
#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaResidue_wild
#print axioms GlobalTheory.Reciprocity.LocalTameStage.inertiaResidue_conjugation
