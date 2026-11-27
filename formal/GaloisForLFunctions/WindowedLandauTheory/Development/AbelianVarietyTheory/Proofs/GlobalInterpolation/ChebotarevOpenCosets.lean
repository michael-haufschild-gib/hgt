import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChebotarevDegreeOne
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! Degree-one Chebotarev for a finite quotient of an absolute Galois
group, with the residue prime also unramified in the base field. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DegreeOneFrobenius

private theorem finite_ramified_over_rat (F : Type) [Field F] [NumberField F] :
    {v : HeightOneSpectrum (𝓞 F) | v.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by
  have hD : Ideal.span {(discr F : 𝓞 F)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using discr_ne_zero F
  refine (Ideal.finite_factors hD).subset ?_
  intro v hv
  let q := Ideal.absNorm (v.asIdeal.under ℤ)
  have hq : q.Prime := Nat.absNorm_under_prime v.asIdeal
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hmem := Int.absNorm_under_mem v.asIdeal
  have hd : (q : ℤ) ∣ discr F := by
    by_contra hn
    have hu := (not_dvd_discr_iff_isUnramifiedIn F (𝓞 F) hqZ).mp hn
    have hv' : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
      (Ideal.liesOver_span_iff v.isPrime.ne_top hqZ).mpr (by simpa [q] using hmem)
    exact hv (hu.ramificationIdx_eq_one hv')
  change v.asIdeal ∣ Ideal.span {(discr F : 𝓞 F)}
  rw [Ideal.dvd_span_singleton]
  obtain ⟨a, ha⟩ := hd
  rw [ha, Int.cast_mul]
  exact v.asIdeal.mul_mem_right _ (by simpa [q] using hmem)

/-- An open normal coset is represented by Frobenius outside the given
finite set, at a place of residue degree and absolute ramification index one. -/
theorem exists_frobenius_in_open_coset (F Ω : Type)
    [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (U : Subgroup (G F Ω)) (hU : IsOpen (U : Set (G F Ω))) (hN : U.Normal)
    (g : G F Ω) (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite) :
    ∃ v : HeightOneSpectrum (𝓞 F), v ∉ S ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧
      v.asIdeal.ramificationIdx ℤ = 1 ∧ ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
        Ine (F := F) B ≤ U ∧ ∃ σ : G F Ω, IsFrob B (normV v) σ ∧ σ * g⁻¹ ∈ U := by
  classical
  letI : IsGalois F Ω := {}
  let L := IntermediateField.fixedField U
  have hfix : L.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, U.isClosed_of_isOpen hU⟩
  letI : FiniteDimensional F L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hfix]; exact hU)
  letI : IsGalois F L := (InfiniteGalois.normal_iff_isGalois L).mp (by rw [hfix]; exact hN)
  let T := {v : HeightOneSpectrum (𝓞 F) | v.asIdeal.ramificationIdx ℤ ≠ 1}
  obtain ⟨v, hv, hf, B, hB, hI, σ, hσ, he⟩ := exists_unramified_degree_one_frobenius
    F Ω L (AlgEquiv.restrictNormalHom L g) (S ∪ T) (hS.union (finite_ramified_over_rat F))
  have hv' : v ∉ S ∧ v ∉ T := by simpa only [Set.mem_union, not_or] using hv
  refine ⟨v, hv'.1, hf, not_not.mp hv'.2, B, hB, hfix ▸ hI, σ, hσ, ?_⟩
  rw [← hfix, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, he,
    map_inv, mul_inv_cancel]

end GlobalTheory.DegreeOneFrobenius
