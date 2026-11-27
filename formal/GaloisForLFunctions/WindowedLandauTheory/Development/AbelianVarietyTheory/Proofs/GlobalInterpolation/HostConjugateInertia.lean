import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateInertia
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AuxiliaryPlaceCover

/-! Complex conjugation preserves residue degree and transports tame
generators between conjugate places of a host. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace GlobalTheory.ConjugateInertia

variable (D : D7)

theorem host_conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [D.host.conjE_apply, D.host.conjE_apply, Complex.conj_conj]

private abbrev conjInt : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv

theorem isConjPl_symm {v w : PlE D.host} (h : IsConjPl D.host v w) :
    IsConjPl D.host w v := by
  intro x y hxy
  exact (h y x (by rw [hxy, host_conj_conj])).symm

theorem mem_placesOver_conj {v w : PlE D.host} (h : IsConjPl D.host v w) {p : ℕ}
    (hp : v ∈ placesOver D.host.E p) : w ∈ placesOver D.host.E p := by
  have he := (h (p : 𝓞 D.host.E) (conjInt D p) rfl).mp hp
  rwa [map_natCast] at he

/-- Conjugating a place preserves the residue-field cardinality and
preserves the property of splitting in the quadratic host. -/
theorem exists_conj_places :
    ∃ bar : PlE D.host → PlE D.host, Function.Injective bar ∧
      ∀ w, IsConjPl D.host w (bar w) ∧ normV (bar w) = normV w ∧
        (IsSplitPl D.host w → IsSplitPl D.host (bar w)) := by
  let c := conjInt D
  let bar := GlobalTheory.TypePlaceCover.conjPl D.host
  refine ⟨bar, bar.injective, fun w => ?_⟩
  have hc := GlobalTheory.TypePlaceCover.isConjPl_conjPl D.host w
  refine ⟨hc, ?_, ?_⟩
  · have hmap : (bar w).asIdeal = w.asIdeal.map c.toRingHom := by
      ext y
      obtain ⟨x, rfl⟩ := c.surjective y
      rw [← hc x (c x) rfl]
      exact (Ideal.apply_mem_of_equiv_iff (f := c)).symm
    exact (Nat.card_congr (Ideal.quotientEquiv _ _ c hmap).toEquiv).symm
  · rintro ⟨x, hx, hn⟩
    refine ⟨c x, (hc x (c x) rfl).1 hx, fun y hy hym => ?_⟩
    exact hn (c x) rfl ((hc (c x) y hy).2 hym)

private theorem cc_algebraMap (x : D.host.E) :
    D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  obtain ⟨j, hj⟩ := D.ntw.cc_cm.1
  apply j.injective
  rw [hj]
  exact (D.host.conjE_apply (j.comp (algebraMap D.host.E D.nd.Om)) x).symm

private theorem cc_symm_algebraMap (x : D.host.E) :
    D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := by
  rw [RingEquiv.symm_apply_eq, cc_algebraMap, host_conj_conj]

/-- The automorphism of the host Galois group induced by complex conjugation. -/
abbrev cConj : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) :=
  conjHom D.ntw.cc (fun x => ⟨_, cc_symm_algebraMap D x⟩)

theorem continuous_cConj : Continuous (cConj D) :=
  continuous_conjHom _ _

theorem isPlaceOver_move_cc {v w : PlE D.host} (h : IsConjPl D.host v w)
    {B : ValuationSubring D.nd.Om} (hB : IsPlaceOver (F := D.host.E) B v) :
    IsPlaceOver (F := D.host.E) (move D.ntw.cc B) w := by
  intro y
  rw [valuation_move_lt_one, cc_symm_algebraMap]
  change B.valuation (algebraMap D.host.E D.nd.Om (conjInt D y : 𝓞 D.host.E)) < 1 ↔ y ∈ w.asIdeal
  rw [hB]
  exact ((isConjPl_symm D h) y (conjInt D y) rfl).symm

theorem isFrob_cConj {B : ValuationSubring D.nd.Om} {q : ℕ} {σ : D.nd.Om ≃ₐ[D.host.E] D.nd.Om}
    (hσ : IsFrob B q σ) : IsFrob (move D.ntw.cc B) q (cConj D σ) :=
  isFrob_conjHom _ _ hσ

/-- After aligning extensions of the same finite place, the conjugate
of a tame generator is a tame generator at the conjugate place. -/
theorem exists_tameGenAt_conj {v w : PlE D.host} (h : IsConjPl D.host v w)
    {γ : D.nd.Om ≃ₐ[D.host.E] D.nd.Om} (hγ : TameGenAt (D.nd.plOm.1 v) γ) :
    ∃ g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om,
      TameGenAt (D.nd.plOm.1 w) (g * cConj D γ * g⁻¹) := by
  letI := D.nd.acOm
  have hv := isPlaceOver_move_cc D h (D.nd.plOm.2 v)
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) hv (D.nd.plOm.2 w)
  have h' : TameGenAt (move D.ntw.cc (D.nd.plOm.1 v)) (cConj D γ) :=
    tameGenAt_move D.ntw.cc (fun x => ⟨_, cc_symm_algebraMap D x⟩)
      (fun x => ⟨_, cc_algebraMap D x⟩) hγ
  have h'' := tameGenAt_move g.toRingEquiv (fun x => ⟨x, g.symm.commutes x⟩)
    (fun x => ⟨x, g.commutes x⟩) h'
  have hm : move g.toRingEquiv (move D.ntw.cc (D.nd.plOm.1 v)) = D.nd.plOm.1 w := by
    rw [← hg]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  rw [hm] at h''
  exact ⟨g, h''⟩

end GlobalTheory.ConjugateInertia
