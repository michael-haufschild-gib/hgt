import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Torus.PairedNeutralConnected

/-!
# Oriented branch intersections preserve neutral incidence

For an arbitrary family of neutral ideals and a separate orientation for each,
the supremum of their branch ideals contracts to the supremum of the neutral
ideals. In particular, the branch equations are inconsistent exactly when the
neutral equations are inconsistent.

At every neutral prime, simultaneous specialization gives a paired prime above
it containing every branch whose neutral ideal lies below it. Consequently
prime contraction maps the intersection of branch zero loci onto the
intersection of the neutral zero loci. All intersection nonemptiness patterns
are therefore independent of the orientations.

Neither the coordinate type nor the ideal family is required to be finite.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
open MvPolynomial Module Classical
variable {ι α : Type*} (K : Type*) [Field K]

/-- Enlarging the neutral ideal enlarges each branch with a fixed orientation. -/
theorem pairedBranchIdeal_mono {J L : Ideal (MvPolynomial ι K)} (h : J ≤ L)
    (ε : ι → Bool) : pairedBranchIdeal K J ε ≤ pairedBranchIdeal K L ε := by
  apply sup_le
  · exact (Ideal.map_mono h).trans (extended_le_pairedBranchIdeal K L ε)
  · rw [Ideal.span_le]
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    exact pairedBranchVariable_mem K L ε i (h hi)

/-- Simultaneous oriented branch equations create exactly the combined neutral relations. -/
theorem iSup_pairedBranchIdeal_comap (J : α → Ideal (MvPolynomial ι K))
    (ε : α → ι → Bool) :
    (⨆ a, pairedBranchIdeal K (J a) (ε a)).comap (invariantSubstitution K) = ⨆ a, J a := by
  -- Specialization in the quotient by all neutral relations annihilates every branch.
  have hk : (⨆ a, pairedBranchIdeal K (J a) (ε a)) ≤
      RingHom.ker (pairedBranchSpecialization K (⨆ a, J a)) := by
    apply iSup_le
    intro a
    exact (pairedBranchIdeal_mono K (le_iSup J a) (ε a)).trans
      (pairedBranchIdeal_le_ker_specialization K (⨆ a, J a) (ε a))
  apply le_antisymm
  · intro f hf
    have hz := RingHom.mem_ker.mp (hk hf)
    rw [pairedBranchSpecialization_invariant] at hz
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz
  · apply iSup_le
    intro a
    apply Ideal.map_le_iff_le_comap.mp
    exact (extended_le_pairedBranchIdeal K (J a) (ε a)).trans
      (le_iSup (fun b => pairedBranchIdeal K (J b) (ε b)) a)

/-- Any family of branch equations is inconsistent exactly when its neutral equations are. -/
theorem iSup_pairedBranchIdeal_eq_top_iff (J : α → Ideal (MvPolynomial ι K))
    (ε : α → ι → Bool) :
    (⨆ a, pairedBranchIdeal K (J a) (ε a)) = ⊤ ↔ (⨆ a, J a) = ⊤ := by
  constructor
  · intro h
    rw [← iSup_pairedBranchIdeal_comap K J ε, h, Ideal.comap_top]
  · intro h
    have hm : (⨆ a, J a).map (invariantSubstitution K) ≤
        ⨆ a, pairedBranchIdeal K (J a) (ε a) :=
      Ideal.map_le_iff_le_comap.mpr (iSup_pairedBranchIdeal_comap K J ε).ge
    rw [h, Ideal.map_top] at hm
    exact top_le_iff.mp hm

/-- A pointwise section of prime contraction chosen to lie in every branch above the neutral prime. -/
def pairedBranchPrimeSection (p : PrimeSpectrum (MvPolynomial ι K)) :
    PrimeSpectrum (MvPolynomial (ι ⊕ ι) K) := pairedBranchCommonPrime K p.asIdeal

/-- The simultaneous branch specialization contracts to the prescribed neutral prime. -/
theorem pairedBranchPrimeSection_comap (p : PrimeSpectrum (MvPolynomial ι K)) :
    PrimeSpectrum.comap (invariantSubstitution K) (pairedBranchPrimeSection K p) = p := by
  apply PrimeSpectrum.ext
  ext f
  change pairedBranchSpecialization K p.asIdeal (invariantSubstitution K f) = 0 ↔ f ∈ p.asIdeal
  rw [pairedBranchSpecialization_invariant, Ideal.Quotient.eq_zero_iff_mem]

/-- The section belongs to every oriented branch whose neutral equations vanish at the point. -/
theorem pairedBranchPrimeSection_mem (J : Ideal (MvPolynomial ι K)) (ε : ι → Bool)
    (p : PrimeSpectrum (MvPolynomial ι K))
    (hp : p ∈ PrimeSpectrum.zeroLocus (J : Set (MvPolynomial ι K))) :
    pairedBranchPrimeSection K p ∈
      PrimeSpectrum.zeroLocus ((pairedBranchIdeal K J ε) : Set (MvPolynomial (ι ⊕ ι) K)) :=
  (pairedBranchIdeal_mono K hp ε).trans (pairedBranchIdeal_le_ker_specialization K p.asIdeal ε)

/-- Contraction maps any intersection of oriented branch loci onto the corresponding neutral locus. -/
theorem pairedBranchIntersections_image (J : α → Ideal (MvPolynomial ι K))
    (ε : α → ι → Bool) :
    PrimeSpectrum.comap (invariantSubstitution K) ''
        (⋂ a, PrimeSpectrum.zeroLocus
          ((pairedBranchIdeal K (J a) (ε a)) : Set (MvPolynomial (ι ⊕ ι) K))) =
      ⋂ a, PrimeSpectrum.zeroLocus ((J a) : Set (MvPolynomial ι K)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    apply Set.mem_iInter.mpr
    intro a
    exact Ideal.map_le_iff_le_comap.mp
      ((extended_le_pairedBranchIdeal K (J a) (ε a)).trans (Set.mem_iInter.mp hq a))
  · intro hp
    refine ⟨pairedBranchPrimeSection K p, ?_, pairedBranchPrimeSection_comap K p⟩
    exact Set.mem_iInter.mpr (fun a => pairedBranchPrimeSection_mem K (J a) (ε a) p
      (Set.mem_iInter.mp hp a))

/-- Branch loci meet simultaneously exactly when their neutral loci meet, for every orientation. -/
theorem pairedBranchIntersections_nonempty_iff (J : α → Ideal (MvPolynomial ι K))
    (ε : α → ι → Bool) :
    (⋂ a, PrimeSpectrum.zeroLocus
      ((pairedBranchIdeal K (J a) (ε a)) : Set (MvPolynomial (ι ⊕ ι) K))).Nonempty ↔
      (⋂ a, PrimeSpectrum.zeroLocus ((J a) : Set (MvPolynomial ι K))).Nonempty := by
  rw [← pairedBranchIntersections_image K J ε, Set.image_nonempty]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iSup_pairedBranchIdeal_comap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.iSup_pairedBranchIdeal_eq_top_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchPrimeSection_comap
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIntersections_image
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.pairedBranchIntersections_nonempty_iff
