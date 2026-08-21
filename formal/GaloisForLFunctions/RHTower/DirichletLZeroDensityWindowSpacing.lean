/-
# Well-spaced multiplicity-copy packets for Dirichlet-L zero windows

Chen--Gupta--Li Section 12 passes from all zeros to a well-spaced saturated
subfamily, with the loss governed by a local zero count.  This module gives
the exact finite combinatorial step for the corpus's multiplicity-copy window
packet.  A local bucket capacity is certified data; the closed theorem returns
a separated subpacket and preserves the full multiplicity-weighted zero count
up to the precise factor `2K`.

No RH, GRH, local zero-density estimate, zero-detection premise, or
large-value bound is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowCopies
import GaloisForLFunctions.RHTower.WellSpacedSubset

open Finset

noncomputable section

namespace RHTower

/-- Finite ordinate data whose every spacing bucket has a certified capacity. -/
structure CGLZeroDensityLocallyBoundedPacket (R : ℕ) where
  ordinate : Fin R → ℝ
  spacing : ℝ
  spacing_pos : 0 < spacing
  capacity : ℕ
  bucket_card_le : ∀ b : ℤ,
    ((Finset.univ : Finset (Fin R)).filter
      (fun r => bucket spacing (ordinate r) = b)).card ≤ capacity

/-- Every locally bucket-bounded finite packet has a separated subpacket whose
cardinality controls the entire packet with loss at most `2K`. -/
theorem exists_cglZeroDensityLocallyBoundedPacket_wellSpaced {R : ℕ}
    (P : CGLZeroDensityLocallyBoundedPacket R) :
    ∃ S : Finset (Fin R), R ≤ 2 * P.capacity * S.card ∧
      ∀ r ∈ S, ∀ s ∈ S, r ≠ s → P.spacing ≤ |P.ordinate r - P.ordinate s| := by
  classical
  by_cases hR : R = 0
  · subst R
    exact ⟨∅, by simp⟩
  let r0 : Fin R := ⟨0, Nat.pos_of_ne_zero hR⟩
  set G : Finset ℤ := (Finset.univ : Finset (Fin R)).image
    (fun r => bucket P.spacing (P.ordinate r)) with hGdef
  have hcardR : R ≤ P.capacity * G.card := by
    have hfib : (Finset.univ : Finset (Fin R)).card =
        ∑ b ∈ G, ((Finset.univ : Finset (Fin R)).filter
          (fun r => bucket P.spacing (P.ordinate r) = b)).card :=
      Finset.card_eq_sum_card_fiberwise fun r hr => Finset.mem_image_of_mem _ hr
    calc
      R = (Finset.univ : Finset (Fin R)).card := by simp
      _ = ∑ b ∈ G, ((Finset.univ : Finset (Fin R)).filter
          (fun r => bucket P.spacing (P.ordinate r) = b)).card := hfib
      _ ≤ ∑ _b ∈ G, P.capacity := Finset.sum_le_sum fun b hb => P.bucket_card_le b
      _ = P.capacity * G.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hrep : ∀ b : ℤ, ∃ r : Fin R, b ∈ G →
      (r ∈ (Finset.univ : Finset (Fin R)) ∧ bucket P.spacing (P.ordinate r) = b) := by
    intro b
    by_cases hb : b ∈ G
    · rw [hGdef, Finset.mem_image] at hb
      obtain ⟨r, hr, hrb⟩ := hb
      exact ⟨r, fun _ => ⟨hr, hrb⟩⟩
    · exact ⟨r0, fun h => absurd h hb⟩
  choose f hf using hrep
  have hbuild : ∀ H : Finset ℤ, H ⊆ G → (∀ m ∈ H, ∀ n ∈ H, Even (m - n)) →
      ∃ S : Finset (Fin R), H.card ≤ S.card ∧
        ∀ r ∈ S, ∀ s ∈ S, r ≠ s → P.spacing ≤ |P.ordinate r - P.ordinate s| := by
    intro H hHG hpar
    refine ⟨H.image f, ?_, ?_⟩
    · have hinj : Set.InjOn f ↑H := by
        intro m hm n hn hfe
        have hbm := (hf m (hHG (Finset.mem_coe.mp hm))).2
        have hbn := (hf n (hHG (Finset.mem_coe.mp hn))).2
        have h := congrArg (fun r => bucket P.spacing (P.ordinate r)) hfe
        rwa [hbm, hbn] at h
      rw [Finset.card_image_of_injOn hinj]
    · intro r hr s hs hrs
      rw [Finset.mem_image] at hr hs
      obtain ⟨m, hm, rfl⟩ := hr
      obtain ⟨n, hn, rfl⟩ := hs
      have hbm := (hf m (hHG hm)).2
      have hbn := (hf n (hHG hn)).2
      have hmn : m ≠ n := by
        intro h
        exact hrs (by rw [h])
      have hgap : 2 ≤ |m - n| := two_le_abs_sub_of_even_sub (hpar m hm n hn) hmn
      exact delta_le_dist_of_two_le_abs_bucket_sub P.spacing_pos (by simpa [hbm, hbn] using hgap)
  set Ge : Finset ℤ := G.filter fun b => Even b with hGe
  set Go : Finset ℤ := G.filter fun b => ¬ Even b with hGo
  have hsplit : Ge.card + Go.card = G.card := Finset.card_filter_add_card_filter_not _
  have hGeG : Ge ⊆ G := Finset.filter_subset _ _
  have hGoG : Go ⊆ G := Finset.filter_subset _ _
  have hpare : ∀ m ∈ Ge, ∀ n ∈ Ge, Even (m - n) := by
    intro m hm n hn
    rw [hGe, Finset.mem_filter] at hm hn
    exact (Int.even_sub).mpr (by simp [hm.2, hn.2])
  have hparo : ∀ m ∈ Go, ∀ n ∈ Go, Even (m - n) := by
    intro m hm n hn
    rw [hGo, Finset.mem_filter] at hm hn
    exact (Int.even_sub).mpr (by simp [hm.2, hn.2])
  have hfinish : ∀ S : Finset (Fin R), G.card ≤ 2 * S.card →
      R ≤ 2 * P.capacity * S.card := by
    intro S hGle
    calc
      R ≤ P.capacity * G.card := hcardR
      _ ≤ P.capacity * (2 * S.card) := Nat.mul_le_mul_left P.capacity hGle
      _ = 2 * P.capacity * S.card := by ring
  rcases le_total Ge.card Go.card with hcmp | hcmp
  · obtain ⟨S, hScard, hSsep⟩ := hbuild Go hGoG hparo
    exact ⟨S, hfinish S (by omega), hSsep⟩
  · obtain ⟨S, hScard, hSsep⟩ := hbuild Ge hGeG hpare
    exact ⟨S, hfinish S (by omega), hSsep⟩

/-- The cardinality of the multiplicity-copy window packet. -/
abbrev cglZeroDensityVerticalWindowCopyCard
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) : ℕ :=
  Fintype.card (CGLZeroDensityVerticalWindowZeroCopy n χ σ τ H)

/-- The underlying distinct zero point of a multiplicity-copy packet label. -/
def cglZeroDensityVerticalWindowCopyPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    CGLZeroDensityVerticalWindowZero n χ σ τ H :=
  ((Fintype.equivFin (CGLZeroDensityVerticalWindowZeroCopy n χ σ τ H)).symm r).1

/-- Every multiplicity-copy packet label retains an actual completed
Dirichlet-L zero. -/
theorem cglZeroDensityVerticalWindowCopyPoint_isZero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) :
    DirichletCharacter.completedLFunction χ.1
      (cglZeroDensityVerticalWindowCopyPoint n χ σ τ H r).1 = 0 :=
  cglZeroDensityVerticalWindowZeroSupportPoint_isZero n χ σ τ H
    (cglZeroDensityVerticalWindowCopyPoint n χ σ τ H r)

/-- The ordinate attached to a multiplicity-copy packet label. -/
def cglZeroDensityVerticalWindowCopyOrdinate
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal)
    (r : Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)) : ℝ :=
  (cglZeroDensityVerticalWindowCopyPoint n χ σ τ H r).1.im

/-- Certified local capacity for the actual multiplicity-copy zero packet. -/
structure CGLZeroDensityVerticalWindowLocalCapacity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) where
  spacing : ℝ
  spacing_pos : 0 < spacing
  capacity : ℕ
  bucket_card_le : ∀ b : ℤ,
    ((Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).filter
      (fun r => bucket spacing (cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r) = b)).card ≤
        capacity

/-- The certified local zero packet as a generic locally bounded packet. -/
def CGLZeroDensityVerticalWindowLocalCapacity.packet
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal}
    (C : CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H) :
    CGLZeroDensityLocallyBoundedPacket (cglZeroDensityVerticalWindowCopyCard n χ σ τ H) where
  ordinate := cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H
  spacing := C.spacing
  spacing_pos := C.spacing_pos
  capacity := C.capacity
  bucket_card_le := C.bucket_card_le

/-- The actual zero-copy packet has a canonical closed unit-spaced local
capacity: use its full finite cardinality as the bucket capacity.  This is a
deliberately unconditional baseline; the source's sharper logarithmic local
bound remains a separate analytic target. -/
def cglZeroDensityVerticalWindowUnitLocalCapacity
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (σ τ : ℝ) (H : NNReal) :
    CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H where
  spacing := 1
  spacing_pos := by norm_num
  capacity := cglZeroDensityVerticalWindowCopyCard n χ σ τ H
  bucket_card_le := by
    intro b
    calc
      ((Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).filter
        (fun r => bucket 1 (cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r) = b)).card ≤
          (Finset.univ : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      _ = cglZeroDensityVerticalWindowCopyCard n χ σ τ H := by simp

/-- A certified local capacity produces a separated subpacket of the actual
multiplicity-copy zero packet. -/
theorem exists_cglZeroDensityVerticalWindowCopy_wellSpaced
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal}
    (C : CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H) :
    ∃ S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)),
      cglZeroDensityVerticalWindowCopyCard n χ σ τ H ≤ 2 * C.capacity * S.card ∧
        ∀ r ∈ S, ∀ s ∈ S, r ≠ s → C.spacing ≤
          |cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r -
            cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H s| := by
  exact exists_cglZeroDensityLocallyBoundedPacket_wellSpaced C.packet

/-- The separated packet controls the literal multiplicity-weighted zero
count with the exact finite `2K` saturation loss. -/
theorem exists_cglZeroDensityVerticalWindowCopy_wellSpaced_count
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal}
    (C : CGLZeroDensityVerticalWindowLocalCapacity n χ σ τ H) :
    ∃ S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)),
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
        (2 * C.capacity * S.card : ℕ) ∧
        ∀ r ∈ S, ∀ s ∈ S, r ≠ s → C.spacing ≤
          |cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r -
            cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H s| := by
  rcases exists_cglZeroDensityVerticalWindowCopy_wellSpaced C with ⟨S, hcard, hsep⟩
  refine ⟨S, ?_, hsep⟩
  rw [← card_cglZeroDensityVerticalWindowZeroCopy_eq_count]
  exact_mod_cast hcard

/-- Every actual centered-window zero-copy packet has a unit-separated
subpacket controlling the literal zero count.  Its explicit capacity is the
packet cardinality, so this closed baseline has no supplied local estimate. -/
theorem exists_cglZeroDensityVerticalWindowCopy_unit_wellSpaced_count
    {n : ℕ} {χ : NonprincipalDirichletCharacter n} {σ τ : ℝ} {H : NNReal} :
    ∃ S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ σ τ H)),
      completedLFunctionZeroDensityVerticalWindowCount n χ σ τ H ≤
        (2 * cglZeroDensityVerticalWindowCopyCard n χ σ τ H * S.card : ℕ) ∧
        ∀ r ∈ S, ∀ s ∈ S, r ≠ s → (1 : ℝ) ≤
          |cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H r -
            cglZeroDensityVerticalWindowCopyOrdinate n χ σ τ H s| := by
  simpa [cglZeroDensityVerticalWindowUnitLocalCapacity] using
    (exists_cglZeroDensityVerticalWindowCopy_wellSpaced_count
      (cglZeroDensityVerticalWindowUnitLocalCapacity n χ σ τ H))

end RHTower
