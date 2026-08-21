/-
# Chen--Gupta--Li Class-I common-prefix fiber separation

Each exact common-prefix Class-I fiber consists of selected zeros of one
primitive character.  This module transfers their pre-existing unit ordinate
separation to the common-coefficient character matrix, packages the original
finite rows as a CGL fibre-separated packet, and specializes the closed
interval second-moment bound to that actual zero fiber.

No RH, GRH, zero-density, large-value, smoothness, or analytic premise is
supplied by a caller.  The only separation used below is certified by the
selected finite primitive-zero carrier.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSecondMoment
import GaloisForLFunctions.RHTower.ChenGuptaLiClassIPrefixFiberLargeValues
import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteSeparatedExtension

open Complex

noncomputable section

namespace RHTower

private theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex_injective
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    Function.Injective (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i) := by
  intro k l hkl
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex at hkl
  apply (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).equivFin.symm.injective
  exact Subtype.ext hkl

private theorem cglPrimitiveClassIWellSpacedClassIPacketIndex_injective
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) :
    Function.Injective (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H) := by
  intro j k hjk
  unfold cglPrimitiveClassIWellSpacedClassIPacketIndex at hjk
  exact (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).equivFin.symm.injective hjk

/-- The literal zero rows underlying one Class-I common-prefix fiber retain
the selected packet's unit separation.  Private because it is implementation
data for the public closed finite certificate below. -/
private theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberRows_separated
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k l : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card)
    (hkl : k ≠ l) :
    (1 : ℝ) ≤
      |(cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k).time -
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i l).time| := by
  have hindex : cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k ≠
      cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l := by
    intro h
    exact hkl (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex_injective X Y n χ τ H i h)
  have hpacket : cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k) ≠
      cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l) := by
    intro h
    exact hindex (cglPrimitiveClassIWellSpacedClassIPacketIndex_injective X Y n χ τ H h)
  have hzero : (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k)).1 ≠
      (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l)).1 := by
    intro h
    exact hpacket (Subtype.ext h)
  have hsep := cglPrimitiveClassIWellSpacedRows_separated n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k)).1
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l)).1 hzero
  let a := (cglPrimitiveClassIWellSpacedRow n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k)).1).time
  let b := (cglPrimitiveClassIWellSpacedRow n χ τ H
    (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l)).1).time
  change (1 : ℝ) ≤ |a - b| at hsep
  have htimeK : (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k).time =
      -(cglPrimitiveClassIWellSpacedRow n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i k)).1).time := by
    simp [cglPrimitiveClassIWellSpacedClassIPrefixFiberRows,
      cglShiftedTailDyadicRow,
      cglPrimitiveClassIWellSpacedClassITailPoint,
      cglPrimitiveClassIWindowZeroRightHalfPlanePoint,
      cglPrimitiveClassIWellSpacedZero_im_eq_row_time]
  have htimeL : (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i l).time =
      -(cglPrimitiveClassIWellSpacedRow n χ τ H
        (cglPrimitiveClassIWellSpacedClassIPacketIndex X Y n χ τ H
          (cglPrimitiveClassIWellSpacedClassIPrefixFiberIndex X Y n χ τ H i l)).1).time := by
    simp [cglPrimitiveClassIWellSpacedClassIPrefixFiberRows,
      cglShiftedTailDyadicRow,
      cglPrimitiveClassIWellSpacedClassITailPoint,
      cglPrimitiveClassIWindowZeroRightHalfPlanePoint,
      cglPrimitiveClassIWellSpacedZero_im_eq_row_time]
  rw [htimeK, htimeL]
  change (1 : ℝ) ≤ |-a - -b|
  rw [show -a - -b = -(a - b) by ring, abs_neg]
  exact hsep

/-- Closed finite same-character separation certificate carried by one literal
common-prefix zero fiber. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedOrdinates
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    CGLFiniteSeparatedOrdinates
      (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card where
  ordinate := fun k => (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k).time
  spacing := 1
  spacing_pos := by norm_num
  separated := fun k l hkl =>
    cglPrimitiveClassIWellSpacedClassIPrefixFiberRows_separated X Y n χ τ H i k l hkl

/-- The literal common-prefix zero fiber as a source-correct CGL fibrewise
separated character packet. -/
noncomputable def cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) :
    CGLFibreSeparatedPacket n
      (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card :=
  (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedOrdinates X Y n χ τ H i).toCGLFibreSeparatedPacket
    χ.1.1

/-- The converted packet retains the exact common-prefix fiber ordinate at
every original finite row label. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket_ordinate
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i).ordinate k =
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k).time := by
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket
  rw [cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_ordinate]
  rfl

/-- The converted packet retains the original primitive character at every
finite row label. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket_character
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i).character k =
      χ.1.1 := by
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket
  rw [cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_character]

/-- The packet matrix rows are definitionally the original common-prefix
fiber rows after the certified CGL re-packaging. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket_rows
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card)
    (k : Fin (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card) :
    cglFibreSeparatedPacketRows
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i) k =
      cglPrimitiveClassIWellSpacedClassIPrefixFiberRows X Y n χ τ H i k := by
  change CGLCharacterDyadicRowData.mk
    ((cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i).ordinate k)
    ((cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i).character k) = _
  rw [cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket_ordinate,
    cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket_character]
  unfold cglPrimitiveClassIWellSpacedClassIPrefixFiberRows
  unfold cglShiftedTailDyadicRow
  rfl

/-- **Chen--Gupta--Li Lemma 9.1, specialized to a literal Class-I
common-prefix zero fiber.**  Its interval character moment has the explicit
diagonal main term and a closed unit-spacing harmonic error budget. -/
theorem cglPrimitiveClassIWellSpacedClassIPrefixFiber_intervalMoment_harmonic
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (i : Fin (cglPrimitiveClassIWellSpacedClassIRows X Y n χ τ H).card) (A B : ℝ) :
    ‖cglFibreSeparatedPacketIntervalMoment
        (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i) A B -
        ((n + 1).totient : ℂ) *
          ((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card : ℂ) *
            ((B - A : ℝ) : ℂ)‖ ≤
      ((n + 1).totient : ℝ) *
        (((cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card : ℝ) *
          (4 * ∑ j ∈ Finset.range
            (cglPrimitiveClassIWellSpacedClassIPrefixFiber X Y n χ τ H i).card,
              1 / ((j : ℝ) + 1))) := by
  have hspacing :
      (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i).spacing = 1 := by
    rfl
  have hbase := norm_cglFibreSeparatedPacketIntervalMoment_sub_diagonal_le_harmonic
    (cglPrimitiveClassIWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H i) A B
  simpa only [hspacing, div_one] using hbase

end RHTower
