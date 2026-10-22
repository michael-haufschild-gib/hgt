import GaloisForLFunctions.HTGeometry.Critical.Sheet.CoordRingResidue
import GaloisForLFunctions.HTGeometry.Critical.Schur.MarkedUnits

/-!
# A sheet with the canonical reduced label cuts out the source Schur place

The source Schur valuation ring is the localization of the Schur coordinate ring at the Schur prime,
so each of its elements is a ratio of coordinate polynomials whose denominator lies outside that
prime.  A sheet is integral on every coordinate polynomial, and it inverts the denominator exactly
when the denominator has nonzero residue — a condition that depends only on the sheet's reduced
label.  So a sheet carrying the canonical label contains the source Schur valuation ring in its
pullback, and since the latter is a one-dimensional valuation ring and the pullback is proper, the
two coincide.

```text
criticalSheetPullbackValuation          the place a sheet cuts out on the source field
criticalSheetPullbackValuation_canonical  the canonical sheet cuts out the source Schur place
criticalSchurAeval_inv_mem_source
isUnit_criticalSheetCanonicalAeval
isUnit_iff_residue_ne_zero
isUnit_criticalSheetAeval               ** the denominators stay invertible along the sheet **
criticalSchurSourceValuationSubring_le_sheet
criticalSheetPullbackValuation_ne_top
criticalSheetPullbackValuation_eq       ** equal labels ⟹ equal places **
```

Properness of the pullback is inherited from the observation field, on which the sheet is the
identity and where the Schur valuation is already known to be nontrivial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open IsLocalRing

set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 3

variable (K : Type*) [Field K] [CharZero K] {m n : ℕ}

/-- The place a sheet cuts out on the source field. -/
def criticalSheetPullbackValuation (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) : ValuationSubring (criticalSourceField K m n) :=
  (criticalNormalClosureSchurValuationSubring K hm hn).comap σ.toRingHom

theorem mem_criticalSheetPullbackValuation (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) (x : criticalSourceField K m n) :
    x ∈ criticalSheetPullbackValuation K hm hn σ ↔
      σ x ∈ criticalNormalClosureSchurValuationSubring K hm hn := Iff.rfl

/-- The canonical sheet cuts out exactly the source Schur place. -/
theorem criticalSheetPullbackValuation_canonical (hm : 0 < m) (hn : 0 < n) :
    criticalSheetPullbackValuation K hm hn (criticalSourceNormalClosureEmbedding K m n)
      = criticalSchurSourceValuationSubring K hm hn :=
  criticalNormalClosureSchurValuationSubring_comap_source K hm hn

/-- The inverse of a coordinate polynomial outside the Schur prime is integral at the source Schur
place. -/
theorem criticalSchurAeval_inv_mem_source (hm : 0 < m) (hn : 0 < n)
    {b : criticalSchurSourceRing K m n} (hb : b ∉ criticalSchurRamificationIdeal K m n) :
    (MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn) b)⁻¹
      ∈ criticalSchurSourceValuationSubring K hm hn := by
  rw [mem_criticalSchurSourceValuationSubring_iff, map_inv₀,
    ← criticalSourceSchurFieldEquiv_algebraMap_apply K hm hn b,
    (criticalSourceSchurFieldEquiv K hm hn).symm_apply_apply]
  exact criticalSchurCoordinateValuationSubring_algebraMap_inv_mem_of_not_mem K hm hn b hb

/-- A coordinate polynomial outside the Schur prime is nonzero in the source field. -/
theorem criticalSchurAeval_ne_zero (hm : 0 < m) (hn : 0 < n)
    {b : criticalSchurSourceRing K m n} (hb : b ∉ criticalSchurRamificationIdeal K m n) :
    MvPolynomial.aeval (criticalSourceSchurCoordinates K hm hn) b ≠ 0 := by
  intro h0
  refine hb ?_
  have hinj := algebraicIndependent_criticalSourceSchurCoordinates K hm hn
  have hb0 : b = 0 := hinj (by simpa using h0)
  rw [hb0]
  exact Ideal.zero_mem _

/-- The canonical sheet sends a coordinate polynomial outside the Schur prime to a unit. -/
theorem isUnit_criticalSheetCanonicalAeval (hm : 1 < m) (hn : 1 < n)
    {b : criticalSchurSourceRing K m n} (hb : b ∉ criticalSchurRamificationIdeal K m n) :
    IsUnit (criticalSheetToUpper K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
      (criticalSourceNormalClosureEmbedding K m n)
      (criticalSheetAevalHom K hm hn (criticalSourceNormalClosureEmbedding K m n) b)) := by
  refine IsUnit.map (criticalSheetToUpper K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
    (criticalSourceNormalClosureEmbedding K m n)) ?_
  have hmemInv : (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) b)⁻¹
      ∈ criticalSheetPullbackSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
        (criticalSourceNormalClosureEmbedding K m n) := by
    have h1 : (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) b)⁻¹
        ∈ criticalSheetPullbackValuation K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
          (criticalSourceNormalClosureEmbedding K m n) := by
      rw [criticalSheetPullbackValuation_canonical K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)]
      exact criticalSchurAeval_inv_mem_source K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn) hb
    exact h1
  refine isUnit_iff_exists_inv.mpr
    ⟨⟨(MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) b)⁻¹, hmemInv⟩, Subtype.ext ?_⟩
  show MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)) b
      * (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) b)⁻¹ = 1
  exact mul_inv_cancel₀ (criticalSchurAeval_ne_zero K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn) hb)

/-- A unit of the upper Schur valuation ring is exactly one with nonzero residue. -/
theorem isUnit_iff_residue_ne_zero (hm : 0 < m) (hn : 0 < n)
    (x : criticalNormalClosureSchurValuationSubring K hm hn) :
    IsUnit x ↔ residue (criticalNormalClosureSchurValuationSubring K hm hn) x ≠ 0 :=
  -- units are the complement of the maximal ideal, and the residue map kills exactly that ideal
  notMem_maximalIdeal.symm.trans (not_congr (Ideal.Quotient.eq_zero_iff_mem).symm)

/-- **A sheet with the canonical reduced label sends every coordinate polynomial outside the Schur
prime to a unit.** -/
theorem isUnit_criticalSheetAeval (hm : 1 < m) (hn : 1 < n)
    {σ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n))
    {b : criticalSchurSourceRing K m n} (hb : b ∉ criticalSchurRamificationIdeal K m n) :
    IsUnit (criticalSheetToUpper K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ
      (criticalSheetAevalHom K hm hn σ b)) := by
  have h0 := isUnit_criticalSheetCanonicalAeval K hm hn hb
  have hres0 : criticalSheetCoordResidue K hm hn
      (criticalSourceNormalClosureEmbedding K m n) b ≠ 0 :=
    (isUnit_iff_residue_ne_zero K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) _).mp h0
  have hres : criticalSheetCoordResidue K hm hn σ b ≠ 0 := by
    rw [criticalSheetCoordResidue_congr K hm hn h]
    exact hres0
  exact (isUnit_iff_residue_ne_zero K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) _).mpr hres

/-- In a valuation subring, a ratio with invertible denominator stays inside: if `x * y = z`,
`y * w = 1` and both `z` and `w` lie in the subring, then so does `x`. -/
private theorem mem_of_mul_eq_of_inv_mem {L : Type*} [Field L] (W : ValuationSubring L)
    {x y z w : L} (hxy : x * y = z) (hyw : y * w = 1) (hz : z ∈ W) (hw : w ∈ W) : x ∈ W := by
  have hx : x = z * w := by rw [← hxy, mul_assoc, hyw, mul_one]
  rw [hx]
  exact W.mul_mem _ _ hz hw

/-- **A sheet with the canonical reduced label cuts out at most the source Schur place.** -/
theorem criticalSchurSourceValuationSubring_le_sheet (hm : 1 < m) (hn : 1 < n)
    {σ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n)) :
    criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)
      ≤ criticalSheetPullbackValuation K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ := by
  intro x hx
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hab⟩ := IsLocalization.surj
    (M := (criticalSchurPrimeDivisor K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn)).1.primeCompl)
    (⟨x, hx⟩ : criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn))
  have hbP : b ∉ criticalSchurRamificationIdeal K m n := hb
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp (isUnit_criticalSheetAeval K hm hn h hbP)
  have hcoe : x * ((algebraMap (criticalSchurSourceRing K m n)
        (criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
          (Nat.zero_lt_of_lt hn)) b :
          criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn)) : criticalSourceField K m n)
      = ((algebraMap (criticalSchurSourceRing K m n)
          (criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn)) a :
          criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
            (Nat.zero_lt_of_lt hn)) : criticalSourceField K m n) :=
    congrArg Subtype.val hab
  rw [coe_algebraMap_criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn) b, coe_algebraMap_criticalSchurSourceValuationSubring K
    (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) a] at hcoe
  have hσ : σ x * σ (MvPolynomial.aeval (criticalSourceSchurCoordinates K
        (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn)) b)
      = σ (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) a) := by
    rw [← map_mul, hcoe]
  have hu' : σ (MvPolynomial.aeval (criticalSourceSchurCoordinates K (Nat.zero_lt_of_lt hm)
        (Nat.zero_lt_of_lt hn)) b) * (u : criticalNormalClosure K m n) = 1 :=
    congrArg Subtype.val hu
  show σ x ∈ criticalNormalClosureSchurValuationSubring K (Nat.zero_lt_of_lt hm)
    (Nat.zero_lt_of_lt hn)
  exact mem_of_mul_eq_of_inv_mem _ hσ hu'
    (criticalSheetAeval_mem_pullback K hm hn σ a) u.2

variable [IsAlgClosed K]

/-- The place a sheet cuts out is a proper valuation ring. -/
theorem criticalSheetPullbackValuation_ne_top (hm : 0 < m) (hn : 0 < n)
    (σ : criticalGeometricSheet K m n) :
    criticalSheetPullbackValuation K hm hn σ ≠ ⊤ := by
  intro htop
  refine criticalSchurObservationValuationSubring_ne_top K hm hn (eq_top_iff.mpr ?_)
  intro y _
  have h1 : algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y
      ∈ criticalSheetPullbackValuation K hm hn σ := by
    rw [htop]
    trivial
  have h2 : σ (algebraMap (criticalObservationField K m n) (criticalSourceField K m n) y)
      ∈ criticalNormalClosureSchurValuationSubring K hm hn := h1
  rw [σ.commutes] at h2
  have h3 := criticalNormalClosureSchurValuationSubring_comap_observation K hm hn
  rw [← h3]
  exact h2

/-- **A sheet with the canonical reduced label cuts out exactly the source Schur place.** -/
theorem criticalSheetPullbackValuation_eq (hm : 1 < m) (hn : 1 < n)
    {σ : criticalGeometricSheet K m n}
    (h : criticalGeometricSheetToSchurReducedFibre K hm hn σ
      = criticalGeometricSheetToSchurReducedFibre K hm hn
        (criticalSourceNormalClosureEmbedding K m n)) :
    criticalSheetPullbackValuation K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) σ
      = criticalSchurSourceValuationSubring K (Nat.zero_lt_of_lt hm) (Nat.zero_lt_of_lt hn) :=
  (ValuationSubring.eq_of_le_of_ne_top _
    (criticalSchurSourceValuationSubring_le_sheet K hm hn h)
    (criticalSheetPullbackValuation_ne_top K (Nat.zero_lt_of_lt hm)
      (Nat.zero_lt_of_lt hn) σ)).symm

end

end GaloisForLFunctions.HTGeometry
