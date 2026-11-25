import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.IntegralPELDatum

/-! Places above the chosen prime that do not meet the characteristic-p Lie factors. -/

noncomputable section

open NumberField

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

/-- The prime avoids the selected Lie characters, and its residual quadratic root agrees with the base. -/
def IsEtPlace (b : Base D R) (w : Ideal (𝓞 D.F)) : Prop :=
  w.IsMaximal ∧ (p : 𝓞 D.F) ∈ w ∧
    (∀ i, Ideal.span ((b.t i) '' (w : Set (𝓞 D.F))) = ⊤) ∧
    ∀ (k : Type) [Field k] [CharP k p] (β : R →+* k) (φ : 𝓞 D.F →+* k),
      RingHom.ker φ = w → φ D.ω = β b.ρ

theorem isEtPlace_of_isUnit (b : Base D R) (hp : IsUnit (p : R))
    (w : Ideal (𝓞 D.F)) (hw : w.IsMaximal) (hpw : (p : 𝓞 D.F) ∈ w) : IsEtPlace b w := by
  refine ⟨hw, hpw, fun i => ?_, fun k _ _ β _ _ => ?_⟩
  · exact Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨(p : 𝓞 D.F), hpw, rfl⟩)
      (by simpa only [map_natCast] using hp)
  · have h := hp.map β
    rw [map_natCast, CharP.cast_eq_zero k p] at h
    exact (not_isUnit_zero h).elim

end GlobalTheory.UPel.HT.EtLev
