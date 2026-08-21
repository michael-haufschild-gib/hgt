/-
# Chen--Gupta--Li coarse Class-I common-prefix fiber separation

Transfers the certified `(K + 1)` separation of the selected primitive-zero
carrier through the exact common-prefix fiber matrix enumeration.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketSecondMoment
import GaloisForLFunctions.RHTower.ChenGuptaLiPrimitiveClassINaturalPrefixFiberLargeValues
import GaloisForLFunctions.RHTower.ChenGuptaLiFiniteSeparatedExtension

open Complex

noncomputable section

namespace RHTower

private theorem cglNaturalFiberIndex_injective
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    Function.Injective (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i) := by
  intro k l hkl
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex at hkl
  apply (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).equivFin.symm.injective
  exact Subtype.ext hkl

private theorem cglNaturalPacketIndex_injective
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ) :
    Function.Injective (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K) := by
  intro j k hjk
  unfold cglPrimitiveClassINaturalWellSpacedClassIPacketIndex at hjk
  exact (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).equivFin.symm.injective hjk

private theorem cglNaturalFiberRows_separated
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k l : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card)
    (hkl : k ≠ l) : (K + 1 : ℕ) ≤
      |(cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i k).time -
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i l).time| := by
  have hindex : cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k ≠
      cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i l := by
    intro h
    exact hkl (cglNaturalFiberIndex_injective X Y n χ τ H K i h)
  have hpacket : cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k) ≠
      cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i l) := by
    intro h
    exact hindex (cglNaturalPacketIndex_injective X Y n χ τ H K h)
  have hzero : (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k)).1 ≠
      (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i l)).1 := by
    intro h
    exact hpacket (Subtype.ext h)
  have hsep := cglPrimitiveClassINaturalWellSpacedRows_separated n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k)).1
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i l)).1 hzero
  let a := (cglPrimitiveClassINaturalWellSpacedRow n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i k)).1).time
  let b := (cglPrimitiveClassINaturalWellSpacedRow n χ τ H K
    (cglPrimitiveClassINaturalWellSpacedClassIPacketIndex X Y n χ τ H K
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberIndex X Y n χ τ H K i l)).1).time
  change (K + 1 : ℕ) ≤ |a - b| at hsep
  have htimeK : (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i k).time = -a := by
    dsimp [a]
    simp [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows, cglShiftedTailDyadicRow,
      cglPrimitiveClassINaturalWellSpacedClassITailPoint, cglPrimitiveClassIWindowZeroRightHalfPlanePoint,
      cglPrimitiveClassINaturalWellSpacedZero_im_eq_row_time]
  have htimeL : (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i l).time = -b := by
    dsimp [b]
    simp [cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows, cglShiftedTailDyadicRow,
      cglPrimitiveClassINaturalWellSpacedClassITailPoint, cglPrimitiveClassIWindowZeroRightHalfPlanePoint,
      cglPrimitiveClassINaturalWellSpacedZero_im_eq_row_time]
  rw [htimeK, htimeL]
  change (K + 1 : ℕ) ≤ |-a - -b|
  rw [show -a - -b = -(a - b) by ring, abs_neg]
  exact hsep

/-- Closed coarse same-character separation certificate for a literal
common-prefix fiber. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedOrdinates
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    CGLFiniteSeparatedOrdinates
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card where
  ordinate := fun k => (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i k).time
  spacing := ((K + 1 : ℕ) : ℝ)
  spacing_pos := by positivity
  separated := fun k l hkl => cglNaturalFiberRows_separated X Y n χ τ H K i k l hkl

/-- The literal coarse common-prefix fiber as a CGL fibre-separated packet. -/
noncomputable def cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) :
    CGLFibreSeparatedPacket n
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card :=
  (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedOrdinates X Y n χ τ H K i).toCGLFibreSeparatedPacket
    χ.1.1

theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket_ordinate
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H K i).ordinate k =
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberRows X Y n χ τ H K i k).time := by
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket
  rw [cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_ordinate]
  rfl

theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket_character
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card)
    (k : Fin (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card) :
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H K i).character k =
      χ.1.1 := by
  unfold cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket
  rw [cglFiniteSeparatedOrdinates_toCGLFibreSeparatedPacket_character]

/-- **Chen--Gupta--Li Lemma 9.1, coarse-spacing specialization.** The exact
interval character moment has the diagonal term and its `(K+1)`-spacing
harmonic error budget. -/
theorem cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber_intervalMoment_harmonic
    (X Y n : ℕ) (χ : PrimitiveNonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal) (K : ℕ)
    (i : Fin (cglPrimitiveClassINaturalWellSpacedClassIRows X Y n χ τ H K).card) (A B : ℝ) :
    ‖cglFibreSeparatedPacketIntervalMoment
        (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H K i) A B -
        ((n + 1).totient : ℂ) *
          ((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card : ℂ) *
            ((B - A : ℝ) : ℂ)‖ ≤
      ((n + 1).totient : ℝ) *
        (((cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card : ℝ) *
          ((4 / ((K + 1 : ℕ) : ℝ)) * ∑ j ∈ Finset.range
            (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiber X Y n χ τ H K i).card,
              1 / ((j : ℝ) + 1))) := by
  have hbase := norm_cglFibreSeparatedPacketIntervalMoment_sub_diagonal_le_harmonic
    (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H K i) A B
  have hspacing :
      (cglPrimitiveClassINaturalWellSpacedClassIPrefixFiberSeparatedPacket X Y n χ τ H K i).spacing =
        ((K + 1 : ℕ) : ℝ) := by rfl
  simpa only [hspacing] using hbase

end RHTower
