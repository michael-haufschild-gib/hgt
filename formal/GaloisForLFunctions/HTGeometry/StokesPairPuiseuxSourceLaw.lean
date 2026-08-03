import GaloisForLFunctions.HTGeometry.StokesPuiseuxSourceLaw

/-!
# Galois sheet-pair coarea source law

This module derives the two-orbit common-level and fission edge formula from actual complex
root-of-unity phases.  It proves the common cyclic quotient kernel cardinal, simultaneous
least-common-denominator filtration, exact coarea, zero-common and unramified specializations, and
a diagonal/off-diagonal master source law.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Difference of the reductions of two cyclic sheets to a common quotient. -/
def commonDifferenceHom {D R S : ℕ} (hDR : D ∣ R) (hDS : D ∣ S) :
    ZMod R × ZMod S →+ ZMod D :=
  ((ZMod.castHom hDR (ZMod D)).toAddMonoidHom.comp
      (AddMonoidHom.fst (ZMod R) (ZMod S))) -
    ((ZMod.castHom hDS (ZMod D)).toAddMonoidHom.comp
      (AddMonoidHom.snd (ZMod R) (ZMod S)))

@[simp] theorem commonDifferenceHom_apply {D R S : ℕ} (hDR : D ∣ R) (hDS : D ∣ S)
    (a : ZMod R) (b : ZMod S) :
    commonDifferenceHom hDR hDS (a, b) =
      ZMod.castHom hDR (ZMod D) a - ZMod.castHom hDS (ZMod D) b := rfl

theorem commonDifferenceHom_surjective {D R S : ℕ} (hDR : D ∣ R) (hDS : D ∣ S) :
    Function.Surjective (commonDifferenceHom hDR hDS) := by
  intro z
  obtain ⟨a, ha⟩ := ZMod.castHom_surjective hDR z
  refine ⟨(a, 0), ?_⟩
  simp [commonDifferenceHom_apply, ha]

/-- Exact size of the common-congruence locus in two cyclic sheet torsors. -/
theorem commonDifferenceKernel_card {D R S : ℕ} (hD : 0 < D) (_hR : 0 < R) (_hS : 0 < S)
    (hDR : D ∣ R) (hDS : D ∣ S) :
    Nat.card (commonDifferenceHom hDR hDS).ker = R * S / D := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  letI : NeZero R := ⟨Nat.ne_of_gt _hR⟩
  letI : NeZero S := ⟨Nat.ne_of_gt _hS⟩
  let f := commonDifferenceHom hDR hDS
  have hrange : f.range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr (commonDifferenceHom_surjective hDR hDS)
  have hmul := f.ker.card_mul_index
  rw [AddSubgroup.index_ker f] at hmul
  have hrangeCard : Nat.card f.range = D := by
    rw [hrange]
    simp
  rw [hrangeCard, Nat.card_prod, Nat.card_zmod, Nat.card_zmod] at hmul
  exact Nat.eq_div_of_mul_eq_left (Nat.ne_of_gt hD) hmul

theorem mem_commonDifferenceKernel_iff_modEq {D R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hDR : D ∣ R) (hDS : D ∣ S) (a : ZMod R) (b : ZMod S) :
    (a, b) ∈ (commonDifferenceHom hDR hDS).ker ↔ a.val ≡ b.val [MOD D] := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  letI : NeZero S := ⟨Nat.ne_of_gt hS⟩
  rw [AddMonoidHom.mem_ker, commonDifferenceHom_apply, sub_eq_zero,
    ZMod.castHom_apply, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.cast_eq_val]
  exact ZMod.natCast_eq_natCast_iff a.val b.val D

/-- A reduced exponent appearing in both denominators. -/
structure ReducedCommonExponent (R S : ℕ) where
  denominator : ℕ
  numerator : ℕ
  denominator_pos : 0 < denominator
  numerator_pos : 0 < numerator
  denominator_dvd_left : denominator ∣ R
  denominator_dvd_right : denominator ∣ S
  reduced : Nat.gcd denominator numerator = 1

namespace ReducedCommonExponent

def leftNumerator {R S : ℕ} (k : ReducedCommonExponent R S) : ℕ :=
  (R / k.denominator) * k.numerator

def rightNumerator {R S : ℕ} (k : ReducedCommonExponent R S) : ℕ :=
  (S / k.denominator) * k.numerator

theorem sheetRoot_pow_scaled {D R n : ℕ} (hD : 0 < D) (hR : 0 < R) (hDR : D ∣ R)
    (a : ZMod R) :
    sheetRoot R ^ (a.val * ((R / D) * n)) = sheetRoot D ^ (a.val * n) := by
  rw [sheetRoot, sheetRoot, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  congr 1
  have hDn : (D : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hD)
  have hRn : (R : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hR)
  push_cast [Nat.cast_div hDR (by exact_mod_cast (Nat.ne_of_gt hD) : (D : ℂ) ≠ 0)]
  field_simp [hDn, hRn]

theorem phase_eq_iff_modEq {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (k : ReducedCommonExponent R S) (a : ZMod R) (b : ZMod S) :
    sheetRoot R ^ (a.val * k.leftNumerator) =
        sheetRoot S ^ (b.val * k.rightNumerator) ↔
      a.val ≡ b.val [MOD k.denominator] := by
  rw [leftNumerator, rightNumerator,
    sheetRoot_pow_scaled k.denominator_pos hR k.denominator_dvd_left,
    sheetRoot_pow_scaled k.denominator_pos hS k.denominator_dvd_right]
  have hroot := sheetRoot_isPrimitive k.denominator_pos
  rw [(hroot.isOfFinOrder (Nat.ne_of_gt k.denominator_pos)).pow_inj_mod,
    ← hroot.eq_orderOf]
  constructor
  · intro h
    have hmod : a.val * k.numerator ≡ b.val * k.numerator [MOD k.denominator] := h
    exact hmod.cancel_right_of_coprime k.reduced
  · intro h
    have hmod : a.val ≡ b.val [MOD k.denominator] := h
    exact hmod.mul_right k.numerator

theorem phase_eq_iff_mem_commonKernel {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (k : ReducedCommonExponent R S) (a : ZMod R) (b : ZMod S) :
    sheetRoot R ^ (a.val * k.leftNumerator) =
        sheetRoot S ^ (b.val * k.rightNumerator) ↔
      (a, b) ∈ (commonDifferenceHom k.denominator_dvd_left
        k.denominator_dvd_right).ker := by
  rw [k.phase_eq_iff_modEq hR hS,
    mem_commonDifferenceKernel_iff_modEq hR hS]

end ReducedCommonExponent

/-- Common denominator after adjoining a list of reduced common exponents. -/
def accumulatedCommonDenominator {R S : ℕ} :
    ℕ → List (ReducedCommonExponent R S) → ℕ
  | D, [] => D
  | D, k :: rest => accumulatedCommonDenominator (Nat.lcm D k.denominator) rest

theorem accumulatedCommonDenominator_pos {R S D : ℕ}
    (levels : List (ReducedCommonExponent R S)) (hD : 0 < D) :
    0 < accumulatedCommonDenominator D levels := by
  induction levels generalizing D with
  | nil => exact hD
  | cons k rest ih =>
      exact ih (Nat.lcm_pos hD k.denominator_pos)

theorem accumulatedCommonDenominator_dvd_left {R S D : ℕ}
    (levels : List (ReducedCommonExponent R S)) (hDR : D ∣ R) :
    accumulatedCommonDenominator D levels ∣ R := by
  induction levels generalizing D with
  | nil => exact hDR
  | cons k rest ih =>
      exact ih (Nat.lcm_dvd hDR k.denominator_dvd_left)

theorem accumulatedCommonDenominator_dvd_right {R S D : ℕ}
    (levels : List (ReducedCommonExponent R S)) (hDS : D ∣ S) :
    accumulatedCommonDenominator D levels ∣ S := by
  induction levels generalizing D with
  | nil => exact hDS
  | cons k rest ih =>
      exact ih (Nat.lcm_dvd hDS k.denominator_dvd_right)

/-- Simultaneous equality of all actual common phases is one congruence modulo the accumulated
least common denominator. -/
theorem modEq_accumulatedCommonDenominator_iff {R S D : ℕ}
    (hR : 0 < R) (hS : 0 < S) (a : ZMod R) (b : ZMod S)
    (levels : List (ReducedCommonExponent R S)) :
    a.val ≡ b.val [MOD accumulatedCommonDenominator D levels] ↔
      a.val ≡ b.val [MOD D] ∧
        ∀ k ∈ levels,
          sheetRoot R ^ (a.val * k.leftNumerator) =
            sheetRoot S ^ (b.val * k.rightNumerator) := by
  induction levels generalizing D with
  | nil => simp [accumulatedCommonDenominator]
  | cons k rest ih =>
      rw [accumulatedCommonDenominator, ih]
      have hstep :
          (a.val ≡ b.val [MOD Nat.lcm D k.denominator]) ↔
            a.val ≡ b.val [MOD D] ∧
              sheetRoot R ^ (a.val * k.leftNumerator) =
                sheetRoot S ^ (b.val * k.rightNumerator) := by
        rw [k.phase_eq_iff_modEq hR hS]
        constructor
        · intro h
          exact ⟨h.of_dvd (Nat.dvd_lcm_left D k.denominator),
            h.of_dvd (Nat.dvd_lcm_right D k.denominator)⟩
        · rintro ⟨hD, hk⟩
          exact Nat.mod_lcm hD hk
      rw [hstep]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

/-- Pair sheets lost when one reduced common exponent is adjoined. -/
def CommonPairLayer {R S : ℕ} (D : ℕ) (hDR : D ∣ R) (hDS : D ∣ S)
    (k : ReducedCommonExponent R S) : Set (ZMod R × ZMod S) :=
  ((commonDifferenceHom hDR hDS).ker : Set (ZMod R × ZMod S)) \
    ((commonDifferenceHom (Nat.lcm_dvd hDR k.denominator_dvd_left)
      (Nat.lcm_dvd hDS k.denominator_dvd_right)).ker : Set (ZMod R × ZMod S))

theorem commonPairKernel_next_subset {R S D : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hDR : D ∣ R) (hDS : D ∣ S) (k : ReducedCommonExponent R S) :
    ((commonDifferenceHom (Nat.lcm_dvd hDR k.denominator_dvd_left)
      (Nat.lcm_dvd hDS k.denominator_dvd_right)).ker : Set (ZMod R × ZMod S)) ⊆
      ((commonDifferenceHom hDR hDS).ker : Set (ZMod R × ZMod S)) := by
  rintro ⟨a, b⟩ hab
  change (a, b) ∈ (commonDifferenceHom
    (Nat.lcm_dvd hDR k.denominator_dvd_left)
    (Nat.lcm_dvd hDS k.denominator_dvd_right)).ker at hab
  change (a, b) ∈ (commonDifferenceHom hDR hDS).ker
  rw [mem_commonDifferenceKernel_iff_modEq hR hS] at hab ⊢
  exact hab.of_dvd (Nat.dvd_lcm_left D k.denominator)

theorem commonPairLayer_card {R S D : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S) (k : ReducedCommonExponent R S) :
    Nat.card (CommonPairLayer D hDR hDS k) =
      R * S / D - R * S / Nat.lcm D k.denominator := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  letI : NeZero S := ⟨Nat.ne_of_gt hS⟩
  rw [Nat.card_coe_set_eq, CommonPairLayer,
    Set.ncard_sdiff (commonPairKernel_next_subset hR hS hDR hDS k)]
  change Nat.card (commonDifferenceHom hDR hDS).ker -
    Nat.card (commonDifferenceHom (Nat.lcm_dvd hDR k.denominator_dvd_left)
      (Nat.lcm_dvd hDS k.denominator_dvd_right)).ker = _
  rw [commonDifferenceKernel_card hD hR hS,
    commonDifferenceKernel_card (Nat.lcm_pos hD k.denominator_pos) hR hS]

theorem commonPairLayer_card_factored {R S D : ℕ} (hR : 0 < R) (hS : 0 < S)
    (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S) (k : ReducedCommonExponent R S) :
    Nat.card (CommonPairLayer D hDR hDS k) =
      R * (S / D - S / Nat.lcm D k.denominator) := by
  rw [commonPairLayer_card hR hS hD hDR hDS k,
    Nat.mul_div_assoc R hDS,
    Nat.mul_div_assoc R (Nat.lcm_dvd hDS k.denominator_dvd_right),
    Nat.mul_sub_left_distrib]

/-- Actual ordered-pair numerator mass: each common phase-loss layer is weighted by its left
numerator, and all surviving pairs are finally lost at the fission numerator. -/
noncomputable def commonPairNumeratorMass {R S : ℕ} (D : ℕ) (hDR : D ∣ R) (hDS : D ∣ S) :
    List (ReducedCommonExponent R S) → ℕ → ℕ
  | [], fissionNumerator =>
      fissionNumerator * Nat.card (commonDifferenceHom hDR hDS).ker
  | k :: rest, fissionNumerator =>
      k.leftNumerator * Nat.card (CommonPairLayer D hDR hDS k) +
        commonPairNumeratorMass (Nat.lcm D k.denominator)
          (Nat.lcm_dvd hDR k.denominator_dvd_left)
          (Nat.lcm_dvd hDS k.denominator_dvd_right) rest fissionNumerator

/-- Canceled coarea form of the Hom irregularity. -/
def commonPairCoarea {R S : ℕ} (D : ℕ) :
    List (ReducedCommonExponent R S) → ℕ → ℕ
  | [], fissionNumerator => fissionNumerator * (S / D)
  | k :: rest, fissionNumerator =>
      k.leftNumerator * (S / D - S / Nat.lcm D k.denominator) +
        commonPairCoarea (Nat.lcm D k.denominator) rest fissionNumerator

/-- Actual pair-sheet numerator mass is `R` times the canceled edge coarea. -/
theorem commonPairNumeratorMass_eq_ramification_mul {R S D : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    commonPairNumeratorMass D hDR hDS levels fissionNumerator =
      R * commonPairCoarea D levels fissionNumerator := by
  induction levels generalizing D with
  | nil =>
      rw [commonPairNumeratorMass, commonPairCoarea,
        commonDifferenceKernel_card hD hR hS hDR hDS,
        Nat.mul_div_assoc R hDS]
      ring
  | cons k rest ih =>
      rw [commonPairNumeratorMass, commonPairCoarea,
        commonPairLayer_card_factored hR hS hD hDR hDS k,
        ih (Nat.lcm_pos hD k.denominator_pos)
          (Nat.lcm_dvd hDR k.denominator_dvd_left)
          (Nat.lcm_dvd hDS k.denominator_dvd_right)]
      ring

/-- Hom irregularity reconstructed directly from common complex phases and the fission layer. -/
noncomputable def commonPairIrregularityFromSheets {R S : ℕ} (D : ℕ)
    (hDR : D ∣ R) (hDS : D ∣ S) (levels : List (ReducedCommonExponent R S))
    (fissionNumerator : ℕ) : ℕ :=
  commonPairNumeratorMass D hDR hDS levels fissionNumerator / R

/-- Exact two-orbit Galois-sheet coarea law. -/
theorem commonPairIrregularityFromSheets_eq_coarea {R S D : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    commonPairIrregularityFromSheets D hDR hDS levels fissionNumerator =
      commonPairCoarea D levels fissionNumerator := by
  rw [commonPairIrregularityFromSheets,
    commonPairNumeratorMass_eq_ramification_mul hR hS hD hDR hDS]
  exact Nat.mul_div_cancel_left _ hR

/-- Off-diagonal Stokes edge reconstructed from the actual sheet-pair coarea. -/
noncomputable def commonPairEdgeFromSheets {R S : ℕ} (D : ℕ)
    (hDR : D ∣ R) (hDS : D ∣ S) (levels : List (ReducedCommonExponent R S))
    (fissionNumerator : ℕ) : ℤ :=
  (commonPairIrregularityFromSheets D hDR hDS levels fissionNumerator : ℤ) -
    (R : ℤ) * (S : ℤ)

/-- Douçot's common-level/fission edge formula follows from actual cyclic sheet pairs. -/
theorem commonPairEdgeFromSheets_eq_sourceFormula {R S D : ℕ}
    (hR : 0 < R) (hS : 0 < S) (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    commonPairEdgeFromSheets D hDR hDS levels fissionNumerator =
      (commonPairCoarea D levels fissionNumerator : ℤ) - (R : ℤ) * (S : ℤ) := by
  rw [commonPairEdgeFromSheets,
    commonPairIrregularityFromSheets_eq_coarea hR hS hD hDR hDS]

/-- Zero-common-part specialization `B = S (s_d - R)`. -/
theorem zeroCommonPairEdgeFromSheets {R S : ℕ} (hR : 0 < R) (hS : 0 < S)
    (fissionNumerator : ℕ) :
    commonPairEdgeFromSheets 1 (one_dvd R) (one_dvd S) [] fissionNumerator =
      (S : ℤ) * ((fissionNumerator : ℤ) - R) := by
  rw [commonPairEdgeFromSheets_eq_sourceFormula hR hS Nat.zero_lt_one]
  simp [commonPairCoarea]
  ring

/-- Untwisted specialization `B = degree(q-q') - 1`. -/
theorem unramifiedPairEdgeFromSheets (differenceDegree : ℕ) :
    commonPairEdgeFromSheets 1 (dvd_refl 1) (dvd_refl 1) [] differenceDegree =
      (differenceDegree : ℤ) - 1 := by
  simpa using zeroCommonPairEdgeFromSheets Nat.zero_lt_one Nat.zero_lt_one differenceDegree

/-- **Galois sheet-pair coarea master law.**  Diagonal and off-diagonal Stokes source formulas are
the same loss-of-sheet-equality law on one and two cyclic torsors. -/
theorem galois_sheet_pair_coarea_master_law
    {R beta S D : ℕ} (c : Characteristic R beta)
    (hS : 0 < S) (hD : 0 < D) (hDR : D ∣ R) (hDS : D ∣ S)
    (levels : List (ReducedCommonExponent R S)) (fissionNumerator : ℕ) :
    c.endomorphismIrregularityFromSheets = c.weightedIrregularity ∧
    c.diagonalLoopFromSheets = c.diagonalLoop ∧
    commonPairIrregularityFromSheets D hDR hDS levels fissionNumerator =
      commonPairCoarea D levels fissionNumerator ∧
    commonPairEdgeFromSheets D hDR hDS levels fissionNumerator =
      (commonPairCoarea D levels fissionNumerator : ℤ) - (R : ℤ) * (S : ℤ) := by
  have hR : 0 < R := Nat.zero_lt_one.trans c.ramification_gt_one
  exact ⟨c.endomorphismIrregularityFromSheets_eq,
    c.diagonalLoopFromSheets_eq,
    commonPairIrregularityFromSheets_eq_coarea hR hS hD hDR hDS levels fissionNumerator,
    commonPairEdgeFromSheets_eq_sourceFormula hR hS hD hDR hDS levels fissionNumerator⟩

end IrregularStokes
end GaloisForLFunctions
