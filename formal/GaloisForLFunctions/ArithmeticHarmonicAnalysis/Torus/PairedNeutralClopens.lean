import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralIdempotents
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Connected.Clopen

/-!
# Paired neutral substitution preserves clopen partitions and connectedness

The canonical bijection on idempotents preserves their multiplication order.
The idempotent--clopen correspondence therefore gives an order isomorphism
between the clopen subsets of the neutral and paired quotient spectra.
Its forward map is exactly pullback along the map on prime spectra induced
by the coefficient-ring embedding.

Thus paired substitution preserves and reflects preconnectedness and
connectedness for every neutral ideal, including nonlinear, nonradical,
and unit ideals. The quotient-spectrum embedding identifies these statements
with the corresponding assertions for the original Zariski zero loci.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
open TopologicalSpace (Clopens)
open scoped PairedNeutral

/-- A space is preconnected precisely when its only bundled clopens are bottom and top. -/
private theorem preconnected_iff_clopens (X : Type*) [TopologicalSpace X] :
    PreconnectedSpace X ↔ ∀ s : Clopens X, s = ⊥ ∨ s = ⊤ := by
  rw [preconnectedSpace_iff_clopen]
  constructor
  · intro h s
    rcases h s s.isClopen with hs | hs
    · exact Or.inl (SetLike.coe_injective hs)
    · exact Or.inr (SetLike.coe_injective hs)
  · intro h s hs
    exact (h ⟨s, hs⟩).imp
      (congrArg (fun U : Clopens X => (U : Set X)))
      (congrArg (fun U : Clopens X => (U : Set X)))

/-- An order isomorphism of clopen algebras transports preconnectedness. -/
private theorem preconnected_of_clopenOrderIso {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : Clopens X ≃o Clopens Y)
    (h : PreconnectedSpace X) : PreconnectedSpace Y := by
  apply (preconnected_iff_clopens Y).mpr
  intro s
  rcases (preconnected_iff_clopens X).mp h (e.symm s) with hs | hs
  · left
    calc
      s = e (e.symm s) := (e.apply_symm_apply s).symm
      _ = e ⊥ := congrArg e hs
      _ = ⊥ := e.map_bot
  · right
    calc
      s = e (e.symm s) := (e.apply_symm_apply s).symm
      _ = e ⊤ := congrArg e hs
      _ = ⊤ := e.map_top

variable {ι : Type*} [Fintype ι] (K : Type*) [Field K]

/-- The neutral coefficient embedding preserves and reflects the multiplication order on idempotents. -/
def pairedNeutralIdempotentOrderIso (J : Ideal (MvPolynomial ι K)) :
    {r : MvPolynomial ι K ⧸ J // IsIdempotentElem r} ≃o
      {x : MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K) // IsIdempotentElem x} where
  __ := pairedNeutralIdempotentEquiv K J
  map_rel_iff' := by
    intro r s
    change algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r.1 *
      algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) s.1 =
      algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) r.1 ↔ r.1 * s.1 = r.1
    rw [← map_mul]
    exact (pairedNeutralQuotient_algebraMap_injective K J).eq_iff

/-- Neutral and paired quotient spectra have canonically isomorphic Boolean algebras of clopens. -/
def pairedNeutralClopenOrderIso (J : Ideal (MvPolynomial ι K)) :
    Clopens (PrimeSpectrum (MvPolynomial ι K ⧸ J)) ≃o
      Clopens (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) :=
  (PrimeSpectrum.isIdempotentElemEquivClopens.symm.trans
    (pairedNeutralIdempotentOrderIso K J)).trans PrimeSpectrum.isIdempotentElemEquivClopens

/-- The clopen correspondence is actual pullback along the neutral-coordinate map on spectra. -/
theorem pairedNeutralClopenOrderIso_apply (J : Ideal (MvPolynomial ι K))
    (U : Clopens (PrimeSpectrum (MvPolynomial ι K ⧸ J))) :
    (pairedNeutralClopenOrderIso K J U :
        Set (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))) =
      PrimeSpectrum.comap (algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) ⁻¹' (U : Set _) := by
  obtain ⟨r, rfl⟩ := (PrimeSpectrum.isIdempotentElemEquivClopens
    (R := MvPolynomial ι K ⧸ J)).surjective U
  change (PrimeSpectrum.isIdempotentElemEquivClopens
      (pairedNeutralIdempotentOrderIso K J
        (PrimeSpectrum.isIdempotentElemEquivClopens.symm
          (PrimeSpectrum.isIdempotentElemEquivClopens r))) :
      Set (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)))) = _
  rw [OrderIso.symm_apply_apply]
  rfl

/-- Paired substitution preserves and reflects preconnectedness for every neutral quotient. -/
theorem pairedNeutralSpectrum_isPreconnected_iff (J : Ideal (MvPolynomial ι K)) :
    PreconnectedSpace
      (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) ↔
      PreconnectedSpace (PrimeSpectrum (MvPolynomial ι K ⧸ J)) :=
  ⟨preconnected_of_clopenOrderIso (pairedNeutralClopenOrderIso K J).symm,
    preconnected_of_clopenOrderIso (pairedNeutralClopenOrderIso K J)⟩

/-- The paired quotient is the zero ring exactly when the neutral quotient is. -/
theorem pairedNeutralQuotient_nontrivial_iff (J : Ideal (MvPolynomial ι K)) :
    Nontrivial (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) ↔
      Nontrivial (MvPolynomial ι K ⧸ J) := by
  constructor
  · intro h
    letI := h
    refine ⟨⟨0, 1, ?_⟩⟩
    intro he
    have hm := congrArg (algebraMap (MvPolynomial ι K ⧸ J)
      (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) he
    exact zero_ne_one (by simpa only [map_zero, map_one] using hm)
  · intro h
    letI := h
    refine ⟨⟨algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) 0,
      algebraMap (MvPolynomial ι K ⧸ J)
        (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) 1, ?_⟩⟩
    exact fun he => zero_ne_one (pairedNeutralQuotient_algebraMap_injective K J he)

/-- Paired substitution preserves and reflects connectedness, including nonemptiness. -/
theorem pairedNeutralSpectrum_isConnected_iff (J : Ideal (MvPolynomial ι K)) :
    ConnectedSpace
      (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) ↔
      ConnectedSpace (PrimeSpectrum (MvPolynomial ι K ⧸ J)) := by
  constructor
  · intro h
    letI := h
    haveI : PreconnectedSpace (PrimeSpectrum (MvPolynomial ι K ⧸ J)) :=
      (pairedNeutralSpectrum_isPreconnected_iff K J).mp inferInstance
    haveI : Nontrivial (MvPolynomial ι K ⧸ J) :=
      (pairedNeutralQuotient_nontrivial_iff K J).mp
        (PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance)
    exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }
  · intro h
    letI := h
    haveI : PreconnectedSpace
        (PrimeSpectrum (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K))) :=
      (pairedNeutralSpectrum_isPreconnected_iff K J).mpr inferInstance
    haveI : Nontrivial (MvPolynomial (ι ⊕ ι) K ⧸ J.map (invariantSubstitution K)) :=
      (pairedNeutralQuotient_nontrivial_iff K J).mpr
        (PrimeSpectrum.nonempty_iff_nontrivial.mp inferInstance)
    exact { toPreconnectedSpace := inferInstance, toNonempty := inferInstance }

/-- The quotient-spectrum embedding identifies preconnectedness of the quotient with its zero locus. -/
private theorem zeroLocus_preconnected_iff_quotient {R : Type*} [CommRing R] (I : Ideal R) :
    IsPreconnected (PrimeSpectrum.zeroLocus (I : Set R)) ↔
      PreconnectedSpace (PrimeSpectrum (R ⧸ I)) := by
  have he := (PrimeSpectrum.comap_isInducing_of_surjective (R ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective).isPreconnected_image (s := Set.univ)
  rw [Set.image_univ, range_comap_of_surjective (R ⧸ I)
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, I.mk_ker] at he
  exact he.trans preconnectedSpace_iff_univ.symm

/-- The quotient-spectrum embedding also preserves the nonemptiness required for connectedness. -/
private theorem zeroLocus_connected_iff_quotient {R : Type*} [CommRing R] (I : Ideal R) :
    IsConnected (PrimeSpectrum.zeroLocus (I : Set R)) ↔
      ConnectedSpace (PrimeSpectrum (R ⧸ I)) := by
  have he : PrimeSpectrum.zeroLocus (I : Set R) =
      Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) := by
    rw [range_comap_of_surjective (R ⧸ I)
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, I.mk_ker]
  constructor
  · rintro ⟨hn, hp⟩
    haveI : PreconnectedSpace (PrimeSpectrum (R ⧸ I)) :=
      (zeroLocus_preconnected_iff_quotient I).mp hp
    rw [he] at hn
    obtain ⟨_, p, rfl⟩ := hn
    exact { toPreconnectedSpace := inferInstance, toNonempty := ⟨p⟩ }
  · intro h
    letI := h
    refine ⟨?_, (zeroLocus_preconnected_iff_quotient I).mpr inferInstance⟩
    rw [he]
    obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum (R ⧸ I)))
    exact ⟨_, p, rfl⟩

/-- The original paired and neutral zero loci are preconnected simultaneously. -/
theorem pairedZeroLocus_isPreconnected_iff_neutral (J : Ideal (MvPolynomial ι K)) :
    IsPreconnected (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) ↔
      IsPreconnected (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial ι K))) := by
  rw [zeroLocus_preconnected_iff_quotient, zeroLocus_preconnected_iff_quotient,
    pairedNeutralSpectrum_isPreconnected_iff]

/-- The original paired and neutral zero loci are connected simultaneously. -/
theorem pairedZeroLocus_isConnected_iff_neutral (J : Ideal (MvPolynomial ι K)) :
    IsConnected (PrimeSpectrum.zeroLocus
      ((J.map (invariantSubstitution K)) : Set (MvPolynomial (ι ⊕ ι) K))) ↔
      IsConnected (PrimeSpectrum.zeroLocus (J : Set (MvPolynomial ι K))) := by
  rw [zeroLocus_connected_iff_quotient, zeroLocus_connected_iff_quotient,
    pairedNeutralSpectrum_isConnected_iff]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralClopenOrderIso
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralClopenOrderIso_apply
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralSpectrum_isPreconnected_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedNeutralSpectrum_isConnected_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedZeroLocus_isConnected_iff_neutral
