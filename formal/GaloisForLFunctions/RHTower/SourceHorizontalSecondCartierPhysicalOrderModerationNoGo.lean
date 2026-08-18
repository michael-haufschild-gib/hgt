import GaloisForLFunctions.RHTower.SourceHorizontalBilateralSecondCartierTopology

/-!
# Second-Cartier physical order/moderation firewall

Let `F`, `R`, and `G` be the forward, inverse, and even quadratic classes in the literal
second Cartier neighborhood `ℤ[q,q⁻¹] / (q - 1)³`.  The preceding source-topology module proves
`F + R = G`, `G ≠ 0`, and integral independence of `F` and `R`.

This module closes two conventional attempts to make `G` physically admissible.

* Multiplicative descent to any reduced commutative ring erases `F`, `R`, `G`, and their complete
  integral source lattice: all three classes are nilpotent.
* An additive receiver that sends `F` and `R` to the exact two coefficient-faithful Hardy halves
  must send `G` to their bilateral eigenfamily.  Its image is moderate exactly at unit character
  modulus, hence never on a strict-right Xi fibre.

The theorem is unconditional and scoped.  It does not rule out a genuinely nonreduced,
nonmultiplicative, relation- or Krein-jet-valued physical receiver.  It proves that such an escape
is necessary rather than optional.
-/

open Complex
open GaloisForLFunctions.HTGeometry
open LaurentPolynomial

namespace RHTower

noncomputable section

/-! ## Nilpotent source geometry -/

/-- The forward Cartier class is cubic-nilpotent in the second neighborhood. -/
theorem deningerIntegralCartierSecondForwardClass_pow_three :
    deningerIntegralCartierSecondForwardClass ^ 3 = 0 := by
  rw [deningerIntegralCartierSecondForwardClass, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (show
    deningerIntegralCartierSourceGenerator ∈
      DeningerIntegralCartierSourceIdeal from
        (generator_mem (k := ℤ))) 3

/-- The literal inverse Cartier orientation is also cubic-nilpotent. -/
theorem deningerIntegralCartierSecondInverseClass_pow_three :
    deningerIntegralCartierSecondInverseClass ^ 3 = 0 := by
  rw [deningerIntegralCartierSecondInverseClass, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow (by
    simpa only [deningerIntegralCartierSourceGenerator] using
      (inversion_mem_span (k := ℤ))) 3

/-- The retained nonzero quadratic class is a square-zero second-Cartier infinitesimal. -/
theorem deningerIntegralCartierSecondGhostClass_sq_zero :
    deningerIntegralCartierSecondGhostClass ^ 2 = 0 := by
  rw [deningerIntegralCartierSecondGhostClass, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  have h3 : deningerIntegralCartierSourceGenerator ^ 3 ∈
      DeningerIntegralCartierSourceIdeal ^ 3 :=
    Ideal.pow_mem_pow (show
      deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal from
          (generator_mem (k := ℤ))) 3
  have h4 := Ideal.mul_mem_left (DeningerIntegralCartierSourceIdeal ^ 3)
    deningerIntegralCartierSourceGenerator h3
  simpa [pow_succ, pow_two, mul_assoc] using h4

/-- The square of the forward class is exactly the retained quadratic class. -/
theorem deningerIntegralCartierSecondForwardClass_sq_eq_ghost :
    deningerIntegralCartierSecondForwardClass ^ 2 =
      deningerIntegralCartierSecondGhostClass := by
  rw [deningerIntegralCartierSecondForwardClass,
    deningerIntegralCartierSecondGhostClass, map_pow]

/-- Multiplying the quadratic class by its forward generator enters the discarded third layer. -/
theorem deningerIntegralCartierSecondForwardClass_mul_ghost_eq_zero :
    deningerIntegralCartierSecondForwardClass *
        deningerIntegralCartierSecondGhostClass = 0 := by
  rw [deningerIntegralCartierSecondForwardClass,
    deningerIntegralCartierSecondGhostClass, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  simpa [pow_succ'] using
    (Ideal.pow_mem_pow (show
      deningerIntegralCartierSourceGenerator ∈
        DeningerIntegralCartierSourceIdeal from
          (generator_mem (k := ℤ))) 3)

/-- The literal Gamma Hermitian product has the opposite sign from the retained even class:
`[q - 1] [q⁻¹ - 1] = -[(q - 1)²]` modulo the third Cartier power. -/
theorem deningerIntegralCartierSecondForwardClass_mul_inverse_eq_neg_ghost :
    deningerIntegralCartierSecondForwardClass *
        deningerIntegralCartierSecondInverseClass =
      -deningerIntegralCartierSecondGhostClass := by
  have hR : deningerIntegralCartierSecondInverseClass =
      deningerIntegralCartierSecondGhostClass -
        deningerIntegralCartierSecondForwardClass := by
    linear_combination deningerIntegralCartierSecondForward_add_inverse
  rw [hR, mul_sub, deningerIntegralCartierSecondForwardClass_mul_ghost_eq_zero,
    ← pow_two, deningerIntegralCartierSecondForwardClass_sq_eq_ghost]
  simp

/-- The forward infinitesimal itself is nonzero; reduced descent will therefore be non-faithful. -/
theorem deningerIntegralCartierSecondForwardClass_ne_zero :
    deningerIntegralCartierSecondForwardClass ≠ 0 := by
  intro h
  have hc : deningerIntegralCartierSecondCoordinateMap (1, 0) = 0 := by
    simpa [deningerIntegralCartierSecondCoordinateMap] using h
  have hv := deningerIntegralCartierSecondCoordinateMap_eq_zero hc
  norm_num at hv

/-! ## Source-order incompatibility before reduction -/

/-- Even a nonreduced ordered receiver cannot retain the quadratic class while declaring both
its forward square and its literal Gamma Hermitian mate positive.  Since the two source channels
are `G` and `-G`, antisymmetry forces their common retained class to vanish. -/
theorem deningerIntegralCartierSecondOrderedPhysicalization_ghost_eq_zero_of_bipositive
    {S : Type*} [CommRing S] [PartialOrder S] [IsOrderedAddMonoid S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S)
    (hquadratic : 0 ≤ φ deningerIntegralCartierSecondGhostClass)
    (hHermitian : 0 ≤ φ
      (deningerIntegralCartierSecondForwardClass *
        deningerIntegralCartierSecondInverseClass)) :
    φ deningerIntegralCartierSecondGhostClass = 0 := by
  have hneg : 0 ≤ -φ deningerIntegralCartierSecondGhostClass := by
    rw [← map_neg,
      ← deningerIntegralCartierSecondForwardClass_mul_inverse_eq_neg_ghost]
    exact hHermitian
  exact le_antisymm (neg_nonneg.mp hneg) hquadratic

/-- A receiver that genuinely retains `G` must make one of the two source-derived physical
positivity requirements fail.  This conclusion does not assume the target is reduced. -/
theorem deningerIntegralCartierSecondOrderedPhysicalization_not_bipositive_of_ghost_ne_zero
    {S : Type*} [CommRing S] [PartialOrder S] [IsOrderedAddMonoid S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S)
    (hretain : φ deningerIntegralCartierSecondGhostClass ≠ 0) :
    ¬ (0 ≤ φ deningerIntegralCartierSecondGhostClass ∧
      0 ≤ φ (deningerIntegralCartierSecondForwardClass *
        deningerIntegralCartierSecondInverseClass)) := by
  rintro ⟨hquadratic, hHermitian⟩
  exact hretain
    (deningerIntegralCartierSecondOrderedPhysicalization_ghost_eq_zero_of_bipositive
      φ hquadratic hHermitian)

theorem deningerIntegralCartierSecondForwardClass_isNilpotent :
    IsNilpotent deningerIntegralCartierSecondForwardClass :=
  ⟨3, deningerIntegralCartierSecondForwardClass_pow_three⟩

theorem deningerIntegralCartierSecondInverseClass_isNilpotent :
    IsNilpotent deningerIntegralCartierSecondInverseClass :=
  ⟨3, deningerIntegralCartierSecondInverseClass_pow_three⟩

theorem deningerIntegralCartierSecondGhostClass_isNilpotent :
    IsNilpotent deningerIntegralCartierSecondGhostClass :=
  ⟨2, deningerIntegralCartierSecondGhostClass_sq_zero⟩

/-! ## Reduced multiplicative physicalization erases the source -/

/-- Every reduced multiplicative receiver erases the forward orientation. -/
theorem deningerIntegralCartierSecondReducedPhysicalization_forward_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S) :
    φ deningerIntegralCartierSecondForwardClass = 0 :=
  (deningerIntegralCartierSecondForwardClass_isNilpotent.map φ).eq_zero

/-- Every reduced multiplicative receiver erases the inverse orientation. -/
theorem deningerIntegralCartierSecondReducedPhysicalization_inverse_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S) :
    φ deningerIntegralCartierSecondInverseClass = 0 :=
  (deningerIntegralCartierSecondInverseClass_isNilpotent.map φ).eq_zero

/-- Every reduced multiplicative receiver erases the nonzero quadratic class. -/
theorem deningerIntegralCartierSecondReducedPhysicalization_ghost_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S) :
    φ deningerIntegralCartierSecondGhostClass = 0 :=
  (deningerIntegralCartierSecondGhostClass_isNilpotent.map φ).eq_zero

/-- **Reduced physicalization firewall.** A reduced multiplicative receiver vanishes on every
integral combination of the two literal source orientations, not only on the quadratic class. -/
theorem deningerIntegralCartierSecondReducedPhysicalization_sourceLattice_eq_zero
    {S : Type*} [CommRing S] [IsReduced S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S)
    (z : DeningerIntegralCartierSecondSourceLattice) :
    φ (z : DeningerIntegralCartierSecondNeighborhood) = 0 := by
  rcases z with ⟨z, ⟨⟨a, b⟩, rfl⟩⟩
  simp [deningerIntegralCartierSecondCoordinateMap,
    deningerIntegralCartierSecondReducedPhysicalization_forward_eq_zero φ,
    deningerIntegralCartierSecondReducedPhysicalization_inverse_eq_zero φ]

/-- No multiplicative receiver into a reduced commutative ring can faithfully retain the second
Cartier neighborhood. -/
theorem not_injective_deningerIntegralCartierSecondReducedPhysicalization
    {S : Type*} [CommRing S] [IsReduced S]
    (φ : DeningerIntegralCartierSecondNeighborhood →+* S) :
    ¬ Function.Injective φ := by
  intro hinj
  apply deningerIntegralCartierSecondForwardClass_ne_zero
  apply hinj
  rw [deningerIntegralCartierSecondReducedPhysicalization_forward_eq_zero φ, map_zero]

/-- Ordinary real-valued ordered physicalization is a concrete instance of the reduced firewall. -/
theorem deningerIntegralCartierSecondRealPhysicalization_sourceLattice_eq_zero
    (φ : DeningerIntegralCartierSecondNeighborhood →+* ℝ)
    (z : DeningerIntegralCartierSecondSourceLattice) :
    φ (z : DeningerIntegralCartierSecondNeighborhood) = 0 :=
  deningerIntegralCartierSecondReducedPhysicalization_sourceLattice_eq_zero φ z

/-! ## Additive coefficient fidelity forces nonmoderation off line -/

/-- The literal lattice quadratic class is the sum of its two retained orientation classes. -/
theorem deningerIntegralCartierSecondGhostLatticeClass_eq_forward_add_inverse :
    deningerIntegralCartierSecondGhostLatticeClass =
      deningerIntegralCartierSecondForwardLatticeClass +
        deningerIntegralCartierSecondInverseLatticeClass := by
  apply Subtype.ext
  simp [deningerIntegralCartierSecondForward_add_inverse]

/-- Any additive receiver that is coefficient-faithful on both Hardy orientations is forced by
the source relation to carry the quadratic class to the full bilateral eigenfamily. -/
theorem sourceHorizontalSecondCartierCoefficientFaithful_ghost_eq
    (D : DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ))
    (c lam : ℂ)
    (hforward : D deningerIntegralCartierSecondForwardLatticeClass =
      fun e => c * hardyPositiveHalf lam e)
    (hinverse : D deningerIntegralCartierSecondInverseLatticeClass =
      fun e => c * hardyNegativeHalf lam e) :
    D deningerIntegralCartierSecondGhostLatticeClass =
      fun e => c * bilateralEigenFamily lam e := by
  rw [deningerIntegralCartierSecondGhostLatticeClass_eq_forward_add_inverse,
    map_add, hforward, hinverse]
  funext e
  have hhalf := congrFun (hardyPositiveHalf_add_hardyNegativeHalf lam) e
  simp only [Pi.add_apply] at hhalf ⊢
  rw [← hhalf]
  ring

/-- **Sharp additive firewall.** Nonzero common scaling cannot repair physical moderation:
the coefficient-faithful quadratic image is moderate exactly at unit character modulus. -/
theorem sourceHorizontalSecondCartierCoefficientFaithful_ghost_moderate_iff
    (D : DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ))
    {c lam : ℂ} (hc : c ≠ 0) (hlam : lam ≠ 0)
    (hforward : D deningerIntegralCartierSecondForwardLatticeClass =
      fun e => c * hardyPositiveHalf lam e)
    (hinverse : D deningerIntegralCartierSecondInverseLatticeClass =
      fun e => c * hardyNegativeHalf lam e) :
    bilateralModerate (D deningerIntegralCartierSecondGhostLatticeClass) ↔
      ‖lam‖ = 1 := by
  rw [sourceHorizontalSecondCartierCoefficientFaithful_ghost_eq
      D c lam hforward hinverse,
    bilateralModerate_const_mul_iff hc]
  simpa only [sourceHorizontalBilateralSecondJetHardyDescent_ghost] using
    (sourceHorizontalBilateralSecondJetHardyDescent_ghost_moderate_iff hlam)

/-- No additive receiver preserving both literal source coefficients can moderate the nonzero
quadratic class on a strict-right Xi fibre.  This is unconditional: strict-rightness contradicts
the unit-character condition forced by moderation. -/
theorem sourceHorizontalStrictRightXi_no_coefficientFaithful_secondCartier_moderation
    (q : XiRightZeroCopy) (p : Nat.Primes) {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ D : DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ),
      D deningerIntegralCartierSecondForwardLatticeClass =
          (fun e => c * hardyPositiveHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        D deningerIntegralCartierSecondInverseLatticeClass =
          (fun e => c * hardyNegativeHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        bilateralModerate
          (D deningerIntegralCartierSecondGhostLatticeClass) := by
  rintro ⟨D, hforward, hinverse, hmoderate⟩
  let lam := bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)
  have hp0 : 0 < (p : ℕ) := lt_of_lt_of_le two_pos p.2.two_le
  have hlam : lam ≠ 0 := bilateralHalfDensityCharacter_ne_zero hp0 _
  have hnorm : ‖lam‖ = 1 :=
    (sourceHorizontalSecondCartierCoefficientFaithful_ghost_moderate_iff
      D hc hlam hforward hinverse).1 hmoderate
  have hline := (norm_bilateralHalfDensityCharacter_eq_one_iff p.2.two_le
    (q.1.1 : XiDivisorSupport)).1 hnorm
  have hright : 1 / 2 < ((q.1.1 : XiDivisorSupport) : ℂ).re := by
    have hcenter := xiRightCenteredZero_re_pos q
    rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
    norm_num at hcenter ⊢
    linarith
  linarith

/-- **Two-horn capstone.** For one strict-right Xi copy, reduced multiplicative receivers erase
the full second-Cartier source lattice, while additive coefficient-faithful Hardy receivers cannot
moderate its nonzero quadratic class. -/
theorem sourceHorizontalSecondCartierPhysicalOrderModeration_firewall
    {S : Type*} [CommRing S] [IsReduced S]
    (q : XiRightZeroCopy) (p : Nat.Primes) {c : ℂ} (hc : c ≠ 0) :
    (∀ (φ : DeningerIntegralCartierSecondNeighborhood →+* S)
        (z : DeningerIntegralCartierSecondSourceLattice),
      φ (z : DeningerIntegralCartierSecondNeighborhood) = 0) ∧
    ¬ ∃ D : DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ),
      D deningerIntegralCartierSecondForwardLatticeClass =
          (fun e => c * hardyPositiveHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        D deningerIntegralCartierSecondInverseLatticeClass =
          (fun e => c * hardyNegativeHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        bilateralModerate
          (D deningerIntegralCartierSecondGhostLatticeClass) := by
  exact ⟨fun φ z =>
      deningerIntegralCartierSecondReducedPhysicalization_sourceLattice_eq_zero φ z,
    sourceHorizontalStrictRightXi_no_coefficientFaithful_secondCartier_moderation
      q p hc⟩

/-- **Order/moderation capstone without reducedness.** Any ordered multiplicative receiver that
retains the quadratic class must reject positivity of either its forward-square presentation or
its literal Gamma Hermitian presentation.  Independently, every additive coefficient-faithful
Hardy receiver remains nonmoderate on the same strict-right Xi fibre. -/
theorem sourceHorizontalSecondCartierPhysicalOrderModeration_orderFirewall
    {S : Type*} [CommRing S] [PartialOrder S] [IsOrderedAddMonoid S]
    (q : XiRightZeroCopy) (p : Nat.Primes) {c : ℂ} (hc : c ≠ 0) :
    (∀ φ : DeningerIntegralCartierSecondNeighborhood →+* S,
      φ deningerIntegralCartierSecondGhostClass ≠ 0 →
        ¬ (0 ≤ φ deningerIntegralCartierSecondGhostClass ∧
          0 ≤ φ (deningerIntegralCartierSecondForwardClass *
            deningerIntegralCartierSecondInverseClass))) ∧
    ¬ ∃ D : DeningerIntegralCartierSecondSourceLattice →+ (ℤ → ℂ),
      D deningerIntegralCartierSecondForwardLatticeClass =
          (fun e => c * hardyPositiveHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        D deningerIntegralCartierSecondInverseLatticeClass =
          (fun e => c * hardyNegativeHalf
            (bilateralHalfDensityCharacter p (q.1.1 : XiDivisorSupport)) e) ∧
        bilateralModerate
          (D deningerIntegralCartierSecondGhostLatticeClass) := by
  exact ⟨fun φ hretain =>
      deningerIntegralCartierSecondOrderedPhysicalization_not_bipositive_of_ghost_ne_zero
        φ hretain,
    sourceHorizontalStrictRightXi_no_coefficientFaithful_secondCartier_moderation
      q p hc⟩

end

end RHTower
