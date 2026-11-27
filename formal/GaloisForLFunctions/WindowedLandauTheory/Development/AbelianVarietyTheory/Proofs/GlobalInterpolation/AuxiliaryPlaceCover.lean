import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitPlaceOrder
import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.HostCls

/-! At each auxiliary prime the designated places and their complex
conjugates exhaust all places above that prime. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions

namespace GlobalTheory.TypePlaceCover

variable {R : Ranks} (H : Host R)

private def conjInt : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv

/-- Conjugation permutes the finite places of the host. -/
def conjPl : HeightOneSpectrum (𝓞 H.E) ≃ HeightOneSpectrum (𝓞 H.E) :=
  HeightOneSpectrum.equivOfRingEquiv (conjInt H)

theorem isConjPl_conjPl (w : HeightOneSpectrum (𝓞 H.E)) : IsConjPl H w (conjPl H w) := by
  intro x y hxy
  have h : y = conjInt H x := RingOfIntegers.ext hxy
  change x ∈ w.asIdeal ↔ (conjInt H).symm y ∈ w.asIdeal
  rw [h, RingEquiv.symm_apply_apply]

theorem conjPl_mem_placesOver {p : ℕ} {w : HeightOneSpectrum (𝓞 H.E)}
    (hw : w ∈ placesOver H.E p) : conjPl H w ∈ placesOver H.E p := by
  change (conjInt H).symm (p : 𝓞 H.E) ∈ w.asIdeal
  rwa [map_natCast]

/-- The designated places are one representative per conjugation orbit at
each of the two completely split primes. -/
theorem place_cover (D : D7) (k : Fin 2) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    ∃ v : D.nd.PlG k, w = D.naut.plGw k v ∨ IsConjPl D.host (D.naut.plGw k v) w := by
  have hne (v v' : D.nd.PlG k) : D.naut.plGw k v ≠ conjPl D.host (D.naut.plGw k v') := by
    intro h
    apply D.naut.plGw_nconj k v' v
    rw [h]
    exact isConjPl_conjPl D.host _
  let f : D.nd.PlG k ⊕ D.nd.PlG k → placesOver D.host.E (D.host.g k) :=
    Sum.elim (fun v => ⟨D.naut.plGw k v, D.naut.plGw_over k v⟩)
      (fun v => ⟨conjPl D.host (D.naut.plGw k v), conjPl_mem_placesOver D.host (D.naut.plGw_over k v)⟩)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) h <;> have he := congrArg Subtype.val h
    · exact congrArg Sum.inl (D.naut.plGw_inj k he)
    · exact (hne a b he).elim
    · exact (hne b a he.symm).elim
    · exact congrArg Sum.inr (D.naut.plGw_inj k ((conjPl D.host).injective he))
  letI : Finite (placesOver D.host.E (D.host.g k)) :=
    (placesOver_finite_av D.host.E (D.host.g k) (D.host.g_prime k).ne_zero).to_subtype
  have hcard : Nat.card (D.nd.PlG k ⊕ D.nd.PlG k) = Nat.card (placesOver D.host.E (D.host.g k)) := by
    rw [Nat.card_coe_set_eq, D.nd.g_split k, D.host.finrank_E', Nat.card_eq_fintype_card,
      Fintype.card_sum, D.nd.card_PlG k, two_mul]
  obtain ⟨v | v, hv⟩ := ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).surjective ⟨w, hw⟩
  · exact ⟨v, Or.inl (congrArg Subtype.val hv).symm⟩
  · refine ⟨v, Or.inr ?_⟩
    have h : conjPl D.host (D.naut.plGw k v) = w := congrArg Subtype.val hv
    rw [← h]
    exact isConjPl_conjPl D.host _

end GlobalTheory.TypePlaceCover
