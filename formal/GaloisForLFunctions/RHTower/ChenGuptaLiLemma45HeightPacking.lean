/-
# Chen--Gupta--Li Lemma 4.5 bounded-height fibre packing

Closes the finite-capacity step behind the source's equal-character spacing
condition.  A height-bounded fibre is packed on the real line, then summed
over the exact finite Dirichlet-character family.  The final constructor turns
literal natural source data into the row-count certificate required by the
Lemma 4.5 source-power estimate.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45NaturalSourceScale
import GaloisForLFunctions.HTGeometry.EuclideanPackingPigeonhole

noncomputable section

namespace RHTower

open scoped BigOperators
open Metric
open MeasureTheory

/-- A finite CGL packet whose ordinates lie in a certified symmetric natural
height window. -/
structure CGLLemma45FibrePacketHeightBounded {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) where
  height : ℕ
  ordinate_bound (r : Fin R) : ‖P.ordinate r‖ ≤ height

/-- A finite CGL packet with certified unit-scale fibre separation. -/
structure CGLLemma45UnitSeparatedPacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) where
  spacing_one : 1 ≤ P.spacing

/-- Rows in one fixed Dirichlet-character fibre. -/
def cglLemma45CharacterFibre {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R)
    (χ : DirichletCharacter ℂ (q + 1)) : Finset (Fin R) :=
  Finset.univ.filter fun r => P.character r = χ

/-- The distinct ordinate values occupied by one character fibre. -/
def cglLemma45CharacterFibreOrdinates {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R)
    (χ : DirichletCharacter ℂ (q + 1)) : Finset ℝ :=
  (cglLemma45CharacterFibre P χ).image P.ordinate

/-- The source height bound transfers to every ordinate in a character fibre. -/
theorem cglLemma45CharacterFibreOrdinates_height
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45FibrePacketHeightBounded P)
    (χ : DirichletCharacter ℂ (q + 1)) :
    ∀ x ∈ cglLemma45CharacterFibreOrdinates P χ, ‖x‖ ≤ H.height := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
  exact H.ordinate_bound r

/-- Different ordinate values in one fibre are separated by half the certified
source spacing. -/
theorem cglLemma45CharacterFibreOrdinates_half_separated
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (χ : DirichletCharacter ℂ (q + 1)) :
    ∀ x ∈ cglLemma45CharacterFibreOrdinates P χ,
      ∀ y ∈ cglLemma45CharacterFibreOrdinates P χ,
        x ≠ y → P.spacing / 2 < dist x y := by
  intro x hx y hy hxy
  rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
  rcases Finset.mem_image.mp hy with ⟨s, hs, rfl⟩
  have hrs : r ≠ s := by
    intro h
    apply hxy
    simp [h]
  have hrχ : P.character r = χ := (Finset.mem_filter.mp hr).2
  have hsχ : P.character s = χ := (Finset.mem_filter.mp hs).2
  have hsep := cglFibreSeparatedPacket_sameCharacter_separation P r s hrs
    (hrχ.trans hsχ.symm)
  rw [dist_eq_norm]
  change P.spacing / 2 < |P.ordinate r - P.ordinate s|
  linarith [P.spacing_pos]

/-- Euclidean packing bound at the packet's native half-spacing scale. -/
theorem cglLemma45CharacterFibreOrdinates_packing
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45FibrePacketHeightBounded P)
    (χ : DirichletCharacter ℂ (q + 1)) :
    ((cglLemma45CharacterFibreOrdinates P χ).card : ℝ) *
        ((P.spacing / 2) / 2) ^ (1 : ℕ) ≤
      (H.height + (P.spacing / 2) / 2) ^ (1 : ℕ) := by
  simpa only [Module.finrank_self, Nat.cast_one] using
    GaloisForLFunctions.HTGeometry.card_mul_pow_le_of_separated (E := ℝ) volume
      (cglLemma45CharacterFibreOrdinates P χ) H.height (P.spacing / 2)
      (by positivity) (by linarith [P.spacing_pos])
      (cglLemma45CharacterFibreOrdinates_height P H χ)
      (fun x hx y hy hxy => by
        have h := cglLemma45CharacterFibreOrdinates_half_separated P χ x hx y hy hxy
        rw [dist_eq_norm] at h
        exact h.le)

/-- Unit-scale Euclidean packing bound, available once the source spacing is
at least one. -/
theorem cglLemma45CharacterFibreOrdinates_unitHalf_packing
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45FibrePacketHeightBounded P)
    (χ : DirichletCharacter ℂ (q + 1))
    (U : CGLLemma45UnitSeparatedPacket P) :
    ((cglLemma45CharacterFibreOrdinates P χ).card : ℝ) *
        (((1 : ℝ) / 2) / 2) ^ (1 : ℕ) ≤
      ((H.height : ℝ) + ((1 : ℝ) / 2) / 2) ^ (1 : ℕ) := by
  simpa only [Module.finrank_self, Nat.cast_one] using
    GaloisForLFunctions.HTGeometry.card_mul_pow_le_of_separated (E := ℝ) volume
      (cglLemma45CharacterFibreOrdinates P χ) H.height ((1 : ℝ) / 2)
      (by positivity) (by norm_num)
      (cglLemma45CharacterFibreOrdinates_height P H χ)
      (fun x hx y hy hxy => by
        have h := cglLemma45CharacterFibreOrdinates_half_separated P χ x hx y hy hxy
        rw [dist_eq_norm] at h
        have hhalf : (1 : ℝ) / 2 ≤ P.spacing / 2 := by
          linarith [U.spacing_one]
        exact hhalf.trans h.le)

/-- On a separated character fibre, ordinates identify packet rows. -/
theorem cglLemma45CharacterFibreOrdinates_card
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (χ : DirichletCharacter ℂ (q + 1)) :
    (cglLemma45CharacterFibreOrdinates P χ).card =
      (cglLemma45CharacterFibre P χ).card := by
  apply Finset.card_image_of_injOn
  intro r hr s hs heq
  by_contra hrs
  have hrχ : P.character r = χ := (Finset.mem_filter.mp hr).2
  have hsχ : P.character s = χ := (Finset.mem_filter.mp hs).2
  have hsep := cglFibreSeparatedPacket_sameCharacter_separation P r s hrs
    (hrχ.trans hsχ.symm)
  rw [heq] at hsep
  simp only [sub_self, abs_zero] at hsep
  linarith [P.spacing_pos]

/-- A character fibre in a height-`H` window has at most `4H + 1` rows when
its source spacing is at least one. -/
theorem cglLemma45CharacterFibre_card_le_four_mul_height_add_one
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45FibrePacketHeightBounded P)
    (χ : DirichletCharacter ℂ (q + 1))
    (U : CGLLemma45UnitSeparatedPacket P) :
    (cglLemma45CharacterFibre P χ).card ≤ 4 * H.height + 1 := by
  have h := cglLemma45CharacterFibreOrdinates_unitHalf_packing P H χ U
  rw [cglLemma45CharacterFibreOrdinates_card] at h
  norm_num at h
  have hreal : ((cglLemma45CharacterFibre P χ).card : ℝ) ≤
      ((4 * H.height + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hreal

/-- Exact decomposition of packet rows into finite Dirichlet-character fibres. -/
theorem cglLemma45RowCard_eq_sum_characterFibres
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R) :
    R = ∑ χ : DirichletCharacter ℂ (q + 1),
      (cglLemma45CharacterFibre P χ).card := by
  classical
  letI : Fintype (DirichletCharacter ℂ (q + 1)) := Fintype.ofFinite _
  simpa [cglLemma45CharacterFibre] using
    (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin R)))
      (t := Finset.univ) (f := P.character)
      (fun r _ => Finset.mem_univ (P.character r)))

/-- Global row capacity obtained by summing the sharp fibrewise packing bound
over the exact `φ(q + 1)` character family. -/
theorem cglLemma45RowCard_le_totient_mul_four_mul_height_add_one
    {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45FibrePacketHeightBounded P)
    (U : CGLLemma45UnitSeparatedPacket P) :
    R ≤ (q + 1).totient * (4 * H.height + 1) := by
  classical
  letI : Fintype (DirichletCharacter ℂ (q + 1)) := Fintype.ofFinite _
  calc
    R = ∑ χ : DirichletCharacter ℂ (q + 1),
        (cglLemma45CharacterFibre P χ).card :=
      cglLemma45RowCard_eq_sum_characterFibres P
    _ ≤ ∑ _χ : DirichletCharacter ℂ (q + 1), (4 * H.height + 1) := by
      gcongr with χ
      exact cglLemma45CharacterFibre_card_le_four_mul_height_add_one P H χ U
    _ = Fintype.card (DirichletCharacter ℂ (q + 1)) * (4 * H.height + 1) := by
      simp [mul_comm]
    _ = Nat.card (DirichletCharacter ℂ (q + 1)) * (4 * H.height + 1) := by
      rw [Nat.card_eq_fintype_card]
    _ = (q + 1).totient * (4 * H.height + 1) := by
      rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q + 1)]

/-- Literal natural source data with bounded height.  The source power
separation forces unit spacing, and packing supplies the row-count exponent
rather than taking it as an additional premise. -/
structure CGLLemma45NaturalHeightSourcePacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (N : CGLPositiveLength) where
  scale : ℕ
  modulus_le : q + 1 ≤ scale
  length_le : N.value ≤ scale
  numerator : ℕ
  numerator_pos : 0 < numerator
  denominator : ℕ
  denominator_pos : 0 < denominator
  spacing_power : (scale : ℝ) ^ numerator ≤ P.spacing ^ denominator
  height : ℕ
  ordinate_bound (r : Fin R) : ‖P.ordinate r‖ ≤ height
  height_le : height ≤ scale
  five_le_scale : 5 ≤ scale

/-- Height-window certificate underlying a natural CGL source packet. -/
def CGLLemma45NaturalHeightSourcePacket.toHeightBounded
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) :
    CGLLemma45FibrePacketHeightBounded P where
  height := S.height
  ordinate_bound := S.ordinate_bound

/-- Power-separated natural source data has spacing at least one. -/
theorem cglLemma45NaturalHeightSourcePacket_spacing_one
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) :
    1 ≤ P.spacing := by
  have hscale_nat : 1 ≤ S.scale :=
    le_trans (Nat.succ_le_succ (Nat.zero_le q)) S.modulus_le
  have hscale : (1 : ℝ) ≤ S.scale := by
    exact_mod_cast hscale_nat
  have hscale_pow : (1 : ℝ) ≤ (S.scale : ℝ) ^ S.numerator :=
    one_le_pow₀ hscale
  have hspacing_pow : (1 : ℝ) ≤ P.spacing ^ S.denominator :=
    hscale_pow.trans S.spacing_power
  exact (one_le_pow_iff_of_nonneg P.spacing_pos.le S.denominator_pos.ne').mp hspacing_pow

/-- Power-separated natural source data packages its forced unit spacing as a
certified packet invariant. -/
theorem CGLLemma45NaturalHeightSourcePacket.toUnitSeparatedPacket
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) : CGLLemma45UnitSeparatedPacket P where
  spacing_one := cglLemma45NaturalHeightSourcePacket_spacing_one S

/-- The bounded-height source data yields cubic row capacity at its natural
source scale. -/
theorem cglLemma45NaturalHeightSourcePacket_rowCount_le_cube
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) :
    R ≤ S.scale ^ (3 : ℕ) := by
  calc
    R ≤ (q + 1).totient * (4 * S.height + 1) :=
      cglLemma45RowCard_le_totient_mul_four_mul_height_add_one P S.toHeightBounded
        S.toUnitSeparatedPacket
    _ ≤ S.scale * (5 * S.scale) := by
      apply Nat.mul_le_mul
      · exact le_trans (Nat.totient_le (q + 1)) S.modulus_le
      · calc
          4 * S.height + 1 ≤ 4 * S.scale + 1 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 4 S.height_le) 1
          _ ≤ 4 * S.scale + S.scale :=
            Nat.add_le_add_left (le_trans (Nat.succ_le_succ (Nat.zero_le q)) S.modulus_le) _
          _ = 5 * S.scale := (Nat.succ_mul 4 S.scale).symm
    _ ≤ S.scale ^ (3 : ℕ) := by
      calc
        S.scale * (5 * S.scale) = (5 * S.scale) * S.scale := Nat.mul_comm _ _
        _ ≤ (S.scale * S.scale) * S.scale :=
          Nat.mul_le_mul_right S.scale (Nat.mul_le_mul_right S.scale S.five_le_scale)
        _ = S.scale ^ (3 : ℕ) := by simp [pow_succ, Nat.mul_assoc]

/-- Convert literal bounded-height source data into the source-scale
certificate consumed by the all-order Lemma 4.5 zero-mode estimate. -/
def CGLLemma45NaturalHeightSourcePacket.toNaturalSourcePacket
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) : CGLLemma45NaturalSourcePacket P N where
  scale := S.scale
  modulus_le := S.modulus_le
  length_le := S.length_le
  numerator := S.numerator
  numerator_pos := S.numerator_pos
  denominator := S.denominator
  denominator_pos := S.denominator_pos
  spacing_power := S.spacing_power
  rowCountExponent := 3
  rowCount_le := cglLemma45NaturalHeightSourcePacket_rowCount_le_cube S

/-- Closed arbitrary-power zero-mode decay from literal bounded-height natural
source data.  The geometric row capacity is derived internally. -/
theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_naturalHeightSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45NaturalHeightSourcePacket P N) (w : CGLRealSmoothBump)
    (targetExponent : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.denominator * (15 + targetExponent)) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          (S.scale : ℝ) ^ targetExponent := by
  simpa [CGLLemma45NaturalHeightSourcePacket.toNaturalSourcePacket] using
    norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_naturalSourcePower
      S.toNaturalSourcePacket w targetExponent

end RHTower
