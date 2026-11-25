import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.SeesawTrivialityLocus
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TrivialityIdealLocalization

/-! Lifting trivializations through small extensions makes the triviality locus open near
the fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.LineBundleSections

namespace GlobalTheory.AbLaw.Seesaw

variable {R : Type} [CommRing R] {X : Scheme.{0}} {L : LB X}
  {f : X ⟶ Spec (CommRingCat.of R)}

private abbrev Trivial {Z : Scheme.{0}} (M : LB Z) : Prop :=
  ∃ t : M.Gen, t.IsGen

/-- If triviality lifts through small extensions, a trivial fibre with no nonconstant
global functions has a principal neighborhood on which the bundle is trivial. -/
theorem trivial_on_basicOpen_of_small_extension_lifting (hL : L.IsLB)
    [UniversallyClosed f] [Surjective f] (P : PerfectSections f L)
    {K : Type} [Field K] (α₀ : R →+* K)
    {X₀ : Scheme.{0}} {π₀ : X₀ ⟶ X} {f₀ : X₀ ⟶ Spec (CommRingCat.of K)}
    (H₀ : IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom α₀)))
    (hΓ : Function.Surjective f₀.appTop) (ht : Trivial (L.pull π₀))
    (lift_trivialization : ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T) (e : T),
      (∀ a ∈ IsLocalRing.maximalIdeal T, a * e = 0) → e ∈ IsLocalRing.maximalIdeal T →
      let q := Spec.map (CommRingCat.ofHom g)
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))
      Trivial (L.pull (pullback.fst (pullback.snd f q) i ≫ pullback.fst f q)) →
      Trivial (L.pull (pullback.fst f q))) :
    ∃ r : R, α₀ r ≠ 0 ∧ Trivial (L.pull (f ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι) := by
  obtain ⟨r, I, hr, hI, htriv⟩ := triviality_locus_near_fibre hL P α₀ H₀ hΓ ht
  let p := RingHom.ker α₀
  haveI : p.IsPrime := RingHom.ker_isPrime α₀
  have hIp : I ≤ p := (htriv K α₀ X₀ π₀ f₀ H₀ hr.isUnit).1 ht
  obtain ⟨c, hc, hcI⟩ := exists_annihilator_of_small_extensions p I hI hIp
    (fun T _ _ g e hu hann he hle => by
      let q := Spec.map (CommRingCat.ofHom g)
      let i := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))
      have H := IsPullback.of_hasPullback f q
      have H' := (IsPullback.of_hasPullback (pullback.snd f q) i).paste_horiz H
      have hq : i ≫ q =
          Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk (Ideal.span {e})).comp g)) := by
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [hq] at H'
      have ht' := (htriv _ _ _ _ _ H'
        ((hu r hr).map (Ideal.Quotient.mk (Ideal.span {e})))).2 hle
      exact (htriv T g _ _ _ H (hu r hr)).1 (lift_trivialization T g e hann he ht'))
  refine ⟨r * c, by rw [map_mul]; exact mul_ne_zero hr hc, ?_⟩
  let B := Localization.Away (r * c)
  let g := algebraMap R B
  let q := Spec.map (CommRingCat.ofHom g)
  have hu : IsUnit (g (r * c)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul, IsUnit.mul_iff] at hu
  have H := IsPullback.of_hasPullback f q
  obtain ⟨t, ht⟩ := (htriv B g _ _ _ H hu.1).2 fun x hx => by
    rw [RingHom.mem_ker, ← hu.2.mul_right_eq_zero, ← map_mul, hcI x hx, map_zero]
  haveI : IsOpenImmersion q := IsOpenImmersion.of_isLocalization (r * c)
  let V := f ⁻¹ᵁ PrimeSpectrum.basicOpen (r * c)
  have hsub : Set.range (V.ι ≫ f) ⊆ Set.range q := by
    rintro _ ⟨y, rfl⟩
    change _ ∈ Set.range (PrimeSpectrum.comap g)
    rw [PrimeSpectrum.localization_away_comap_range B (r * c)]
    exact y.2
  let l := H.lift V.ι (IsOpenImmersion.lift q (V.ι ≫ f) hsub)
    (IsOpenImmersion.lift_fac q (V.ι ≫ f) hsub).symm
  have hl : l ≫ pullback.fst f q = V.ι := H.lift_fst _ _ _
  rw [← hl]
  exact ⟨_, ht.pullGen (fun _ : PUnit => pullback.fst f q) (fun _ => 1) l⟩

end GlobalTheory.AbLaw.Seesaw
