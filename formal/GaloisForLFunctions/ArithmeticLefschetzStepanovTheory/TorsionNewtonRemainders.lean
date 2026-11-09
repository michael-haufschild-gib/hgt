import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.TheFilteredTorsionKernelHasAnIntegralBasis

/-!
# Integral torsion remainders minimize arithmetic length

Truncating Newton coordinates below quotient order `r` gives the canonical
representative modulo the `r`th power of the full torsion grid ideal. The
representative minimizes arithmetic length in its congruence class. Thus
universal interpolation at length `N` is equivalent to bounding the weights
of all low-quotient-order indices by `N`.
-/

open MvPolynomial Finset
noncomputable section
namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open ArithmeticHarmonicAnalysis
variable {P : Finset Nat.Primes}

/-- Integral coordinates in the torsion Newton basis. -/
def torsionNewtonCoordinates (q : ℕ) [NeZero q] :
    MvPolynomial P ℤ ≃ₗ[ℤ] ((P →₀ ℕ) →₀ ℤ) := (torsionNewtonEquiv q).symm

theorem synthesis_torsionNewtonCoordinates (q : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    torsionNewtonSynthesis q (torsionNewtonCoordinates q F) = F :=
  (torsionNewtonEquiv q).apply_symm_apply F

theorem torsionNewtonCoordinates_synthesis (q : ℕ) [NeZero q] (c : (P →₀ ℕ) →₀ ℤ) :
    torsionNewtonCoordinates q (torsionNewtonSynthesis q c) = c :=
  (torsionNewtonEquiv q).symm_apply_apply c

theorem torsionNewtonCoordinates_polynomial (q : ℕ) [NeZero q] (a : P →₀ ℕ) :
    torsionNewtonCoordinates q (torsionNewtonPolynomial q a) = Finsupp.single a 1 := by
  simpa only [torsionNewtonSynthesis_single, one_smul] using
    torsionNewtonCoordinates_synthesis q (Finsupp.single a 1)

/-- The largest weight of a nonzero Newton coordinate is the arithmetic length. -/
theorem length_eq_torsionNewtonCoordinates (q : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    length F = (torsionNewtonCoordinates q F).support.sup weight := by
  rw [← length_torsionNewtonSynthesis q, synthesis_torsionNewtonCoordinates]

/-- The integral grid ideal power is a coordinate submodule. -/
theorem mem_gridIdeal_pow_iff_coordinates (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    F ∈ torsionGridIdeal q ^ r ↔
      ∀ a ∈ (torsionNewtonCoordinates q F).support, r ≤ torsionQuotientOrder q a := by
  constructor
  · intro hF
    obtain ⟨c, hc, hcs⟩ := exists_filtered_torsionNewton_expansion q r F (length F) le_rfl
      ((fullTorsionMultiplicity_iff_mem_gridIdeal_pow q r F).mpr hF)
    rw [← hcs, torsionNewtonCoordinates_synthesis]
    exact fun a ha => (hc a ha).2
  · intro hc
    rw [← synthesis_torsionNewtonCoordinates q F]
    exact (fullTorsionMultiplicity_iff_mem_gridIdeal_pow q r _).mp
      (torsionNewtonSynthesis_multiplicity q r _ hc)

/-- Congruence on the full torsion jets fixes precisely the low-order Newton coordinates. -/
theorem sub_mem_gridIdeal_pow_iff_coordinates (q r : ℕ) [NeZero q]
    (F G : MvPolynomial P ℤ) :
    F - G ∈ torsionGridIdeal q ^ r ↔
      ∀ a, torsionQuotientOrder q a < r →
        torsionNewtonCoordinates q F a = torsionNewtonCoordinates q G a := by
  rw [mem_gridIdeal_pow_iff_coordinates, map_sub]
  constructor
  · intro h a ha
    apply sub_eq_zero.mp
    by_contra hne
    have hs : a ∈ (torsionNewtonCoordinates q F - torsionNewtonCoordinates q G).support :=
      Finsupp.mem_support_iff.mpr (by simpa only [Finsupp.sub_apply] using hne)
    exact (not_le_of_gt ha) (h a hs)
  · intro h a ha
    by_contra hnot
    have he := h a (lt_of_not_ge hnot)
    exact (Finsupp.mem_support_iff.mp ha) (by rw [Finsupp.sub_apply, he, sub_self])

/-- Canonical integral representative of the torsion jet class. -/
def torsionRemainder (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) : MvPolynomial P ℤ :=
  torsionNewtonSynthesis q
    ((torsionNewtonCoordinates q F).filter (fun a => torsionQuotientOrder q a < r))

/-- A reduced polynomial has no coordinate in the torsion ideal power. -/
def IsTorsionReduced (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) : Prop :=
  ∀ a ∈ (torsionNewtonCoordinates q F).support, torsionQuotientOrder q a < r

theorem torsionNewtonCoordinates_remainder (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    torsionNewtonCoordinates q (torsionRemainder q r F) =
      (torsionNewtonCoordinates q F).filter (fun a => torsionQuotientOrder q a < r) :=
  torsionNewtonCoordinates_synthesis q _

theorem torsionRemainder_reduced (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    IsTorsionReduced q r (torsionRemainder q r F) := by
  intro a ha
  rw [torsionNewtonCoordinates_remainder, Finsupp.support_filter] at ha
  exact (mem_filter.mp ha).2

theorem sub_torsionRemainder_mem_gridIdeal_pow (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    F - torsionRemainder q r F ∈ torsionGridIdeal q ^ r := by
  apply (sub_mem_gridIdeal_pow_iff_coordinates q r _ _).mpr
  intro a ha
  rw [torsionNewtonCoordinates_remainder, Finsupp.filter_apply, if_pos ha]

/-- A reduced representative is uniquely determined by its full torsion jet class. -/
theorem eq_torsionRemainder_of_reduced (q r : ℕ) [NeZero q] (F G : MvPolynomial P ℤ)
    (hG : IsTorsionReduced q r G) (hcong : F - G ∈ torsionGridIdeal q ^ r) :
    G = torsionRemainder q r F := by
  apply (torsionNewtonCoordinates q).injective
  ext a
  rw [torsionNewtonCoordinates_remainder, Finsupp.filter_apply]
  by_cases ha : torsionQuotientOrder q a < r
  · rw [if_pos ha]
    exact ((sub_mem_gridIdeal_pow_iff_coordinates q r F G).mp hcong a ha).symm
  · rw [if_neg ha]
    by_contra hne
    exact ha (hG a (Finsupp.mem_support_iff.mpr hne))

/-- The canonical torsion remainder is the unique reduced representative. -/
theorem exists_unique_torsionRemainder (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    ∃! G, IsTorsionReduced q r G ∧ F - G ∈ torsionGridIdeal q ^ r := by
  refine ⟨torsionRemainder q r F,
    ⟨torsionRemainder_reduced q r F, sub_torsionRemainder_mem_gridIdeal_pow q r F⟩, ?_⟩
  intro G hG
  exact eq_torsionRemainder_of_reduced q r F G hG.1 hG.2

/-- Retained coordinates occur in every representative, so reduction minimizes length. -/
theorem length_torsionRemainder_le_of_congruent (q r : ℕ) [NeZero q]
    (F G : MvPolynomial P ℤ) (hcong : F - G ∈ torsionGridIdeal q ^ r) :
    length (torsionRemainder q r F) ≤ length G := by
  classical
  rw [length_eq_torsionNewtonCoordinates q, torsionNewtonCoordinates_remainder,
    length_eq_torsionNewtonCoordinates q G]
  apply Finset.sup_mono
  intro a ha
  rw [Finsupp.support_filter] at ha
  obtain ⟨ha, hlow⟩ := mem_filter.mp ha
  rw [Finsupp.mem_support_iff,
    ← (sub_mem_gridIdeal_pow_iff_coordinates q r F G).mp hcong a hlow]
  exact Finsupp.mem_support_iff.mp ha

theorem length_torsionRemainder_le (q r : ℕ) [NeZero q] (F : MvPolynomial P ℤ) :
    length (torsionRemainder q r F) ≤ length F :=
  length_torsionRemainder_le_of_congruent q r F F (by rw [sub_self]; exact Ideal.zero_mem _)

/-- The least possible length in a torsion class is exactly its remainder length. -/
theorem exists_bounded_torsion_representative_iff (q r N : ℕ) [NeZero q]
    (F : MvPolynomial P ℤ) :
    (∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ r) ↔
      length (torsionRemainder q r F) ≤ N := by
  constructor
  · rintro ⟨G, hlen, hcong⟩
    exact (length_torsionRemainder_le_of_congruent q r F G hcong).trans hlen
  · intro hlen
    exact ⟨torsionRemainder q r F, hlen, sub_torsionRemainder_mem_gridIdeal_pow q r F⟩

theorem torsionRemainder_newton (q r : ℕ) [NeZero q] (a : P →₀ ℕ)
    (ha : torsionQuotientOrder q a < r) :
    torsionRemainder q r (torsionNewtonPolynomial q a) = torsionNewtonPolynomial q a := by
  rw [torsionRemainder, torsionNewtonCoordinates_polynomial,
    Finsupp.filter_single_of_pos (fun b : P →₀ ℕ => torsionQuotientOrder q b < r) ha,
    torsionNewtonSynthesis_single, one_smul]

/-- Universal integral interpolation is exactly the weight bound on the quotient basis. -/
theorem universal_torsion_interpolation_iff_index_weights (q r N : ℕ) [NeZero q] :
    (∀ F : MvPolynomial P ℤ, ∃ G, length G ≤ N ∧ F - G ∈ torsionGridIdeal q ^ r) ↔
      ∀ a : P →₀ ℕ, torsionQuotientOrder q a < r → weight a ≤ N := by
  constructor
  · intro h a ha
    obtain ⟨G, hlen, hcong⟩ := h (torsionNewtonPolynomial q a)
    have hle := length_torsionRemainder_le_of_congruent q r (torsionNewtonPolynomial q a) G hcong
    rw [torsionRemainder_newton q r a ha, length_torsionNewtonPolynomial] at hle
    exact hle.trans hlen
  · intro h F
    refine ⟨torsionRemainder q r F, ?_, sub_torsionRemainder_mem_gridIdeal_pow q r F⟩
    apply length_torsionNewtonSynthesis_le
    intro a ha
    rw [Finsupp.support_filter] at ha
    exact h a (mem_filter.mp ha).2

#print axioms exists_unique_torsionRemainder
#print axioms length_torsionRemainder_le_of_congruent
#print axioms universal_torsion_interpolation_iff_index_weights

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
