import GaloisForLFunctions.RHTower.ChenGuptaLiLemma45HeightPacking

noncomputable section

namespace RHTower

open scoped BigOperators
open Metric
open MeasureTheory

structure CGLLemma45RealHeightBounded {q R : ℕ} (P : CGLFibreSeparatedPacket q R) where
  height : ℝ
  height_nonneg : 0 ≤ height
  ordinate_bound (r : Fin R) : ‖P.ordinate r‖ ≤ height

theorem cglLemma45RealHeight_ordinates_bound {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45RealHeightBounded P) (χ : DirichletCharacter ℂ (q + 1)) :
    ∀ x ∈ cglLemma45CharacterFibreOrdinates P χ, ‖x‖ ≤ H.height := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨r, hr, rfl⟩
  exact H.ordinate_bound r

theorem cglLemma45RealHeight_fibre_card_le {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45RealHeightBounded P) (U : CGLLemma45UnitSeparatedPacket P)
    (χ : DirichletCharacter ℂ (q + 1)) :
    ((cglLemma45CharacterFibre P χ).card : ℝ) ≤ 4 * H.height + 1 := by
  have hpack : ((cglLemma45CharacterFibreOrdinates P χ).card : ℝ) *
        (((1 : ℝ) / 2) / 2) ^ 1 ≤ (H.height + ((1 : ℝ) / 2) / 2) ^ 1 := by
    simpa only [Module.finrank_self, Nat.cast_one] using
      GaloisForLFunctions.HTGeometry.card_mul_pow_le_of_separated (E := ℝ) volume
        (cglLemma45CharacterFibreOrdinates P χ) H.height ((1 : ℝ) / 2)
        H.height_nonneg (by norm_num) (cglLemma45RealHeight_ordinates_bound P H χ)
        (fun x hx y hy hxy => by
          have h := cglLemma45CharacterFibreOrdinates_half_separated P χ x hx y hy hxy
          rw [dist_eq_norm] at h
          have hh : (1 : ℝ) / 2 ≤ P.spacing / 2 := by linarith [U.spacing_one]
          exact hh.trans h.le)
  rw [cglLemma45CharacterFibreOrdinates_card] at hpack
  norm_num at hpack
  linarith

theorem cglLemma45RealHeight_row_card_le {q R : ℕ} (P : CGLFibreSeparatedPacket q R)
    (H : CGLLemma45RealHeightBounded P) (U : CGLLemma45UnitSeparatedPacket P) :
    (R : ℝ) ≤ ((q + 1).totient : ℝ) * (4 * H.height + 1) := by
  classical
  letI : Fintype (DirichletCharacter ℂ (q + 1)) := Fintype.ofFinite _
  have hc : (Fintype.card (DirichletCharacter ℂ (q + 1)) : ℝ) = ((q + 1).totient : ℝ) := by
    exact_mod_cast (calc
      Fintype.card (DirichletCharacter ℂ (q + 1)) = Nat.card (DirichletCharacter ℂ (q + 1)) := Nat.card_eq_fintype_card.symm
      _ = (q + 1).totient := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ (q + 1))
  calc
    (R : ℝ) = ∑ χ : DirichletCharacter ℂ (q + 1), ((cglLemma45CharacterFibre P χ).card : ℝ) := by
      exact_mod_cast cglLemma45RowCard_eq_sum_characterFibres P
    _ ≤ ∑ _χ : DirichletCharacter ℂ (q + 1), (4 * H.height + 1) := by
      gcongr with χ
      exact cglLemma45RealHeight_fibre_card_le P H U χ
    _ = (Fintype.card (DirichletCharacter ℂ (q + 1)) : ℝ) * (4 * H.height + 1) := by
      simp [mul_comm]
      ring
    _ = ((q + 1).totient : ℝ) * (4 * H.height + 1) := by rw [hc]

structure CGLLemma45PaperSourcePacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (N : CGLPositiveLength) where
  time : ℝ
  time_one : 1 ≤ time
  base : ℝ
  base_eq_modulus_mul_time : base = (q + 1 : ℝ) * time
  base_five : 5 ≤ base
  length_le : N.value ≤ base
  numerator : ℕ
  numerator_pos : 0 < numerator
  denominator : ℕ
  denominator_pos : 0 < denominator
  spacing_power : base ^ numerator ≤ P.spacing ^ denominator
  ordinate_bound (r : Fin R) : ‖P.ordinate r‖ ≤ time

def CGLLemma45PaperSourcePacket.toRealHeightBounded {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : CGLLemma45RealHeightBounded P where
  height := S.time
  height_nonneg := by linarith [S.time_one]
  ordinate_bound := S.ordinate_bound

theorem cglLemma45PaperSourcePacket_spacing_one {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : 1 ≤ P.spacing := by
  have hb : (1 : ℝ) ≤ S.base := by linarith [S.base_five]
  have hp : (1 : ℝ) ≤ P.spacing ^ S.denominator :=
    (one_le_pow₀ hb).trans S.spacing_power
  exact (one_le_pow_iff_of_nonneg P.spacing_pos.le S.denominator_pos.ne').mp hp

theorem CGLLemma45PaperSourcePacket.toUnitSeparatedPacket {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : CGLLemma45UnitSeparatedPacket P where
  spacing_one := cglLemma45PaperSourcePacket_spacing_one S

theorem cglLemma45PaperSourcePacket_totient_le_base {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : ((q + 1).totient : ℝ) ≤ S.base := by
  calc
    ((q + 1).totient : ℝ) ≤ (q + 1 : ℝ) := by exact_mod_cast Nat.totient_le (q + 1)
    _ ≤ (q + 1 : ℝ) * S.time := by simpa using mul_le_mul_of_nonneg_left S.time_one (by positivity : (0 : ℝ) ≤ q + 1)
    _ = S.base := S.base_eq_modulus_mul_time.symm

theorem cglLemma45PaperSourcePacket_time_le_base {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : S.time ≤ S.base := by
  have ht : 0 ≤ S.time := by linarith [S.time_one]
  have hq : (1 : ℝ) ≤ q + 1 := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
  calc
    S.time = 1 * S.time := by ring
    _ ≤ (q + 1 : ℝ) * S.time := mul_le_mul_of_nonneg_right hq ht
    _ = S.base := S.base_eq_modulus_mul_time.symm

theorem cglLemma45PaperSourcePacket_rowCount_le_cube {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : (R : ℝ) ≤ S.base ^ 3 := by
  have hb0 : 0 ≤ S.base := by linarith [S.base_five]
  have hh := cglLemma45PaperSourcePacket_time_le_base S
  have hphi := cglLemma45PaperSourcePacket_totient_le_base S
  calc
    (R : ℝ) ≤ ((q + 1).totient : ℝ) * (4 * S.time + 1) :=
      cglLemma45RealHeight_row_card_le P S.toRealHeightBounded S.toUnitSeparatedPacket
    _ ≤ S.base * (5 * S.base) := by
      apply mul_le_mul hphi
      · nlinarith [hh, S.base_five]
      · nlinarith [S.time_one]
      · exact hb0
    _ ≤ S.base ^ 3 := by
      have hf : 5 * S.base ≤ S.base * S.base := mul_le_mul_of_nonneg_right S.base_five hb0
      calc
        S.base * (5 * S.base) ≤ S.base * (S.base * S.base) := mul_le_mul_of_nonneg_left hf hb0
        _ = S.base ^ 3 := by ring

def CGLLemma45PaperSourcePacket.toSourceScale {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) : CGLLemma45SourceScale P N where
  separation :=
    { base := S.base
      base_one := by linarith [S.base_five]
      numerator := S.numerator
      numerator_pos := S.numerator_pos
      denominator := S.denominator
      denominator_pos := S.denominator_pos
      spacing_power := S.spacing_power }
  fourierScale_le := by
    unfold cglAffineFourierScale cglLemma45FibreModulus
    calc
      (N.value : ℝ) / ↑(q + 1) ≤ N.value := div_le_self (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le q))
      _ ≤ S.base := S.length_le
  totient_le := cglLemma45PaperSourcePacket_totient_le_base S
  rowCountExponent := 3
  rowCount_le := cglLemma45PaperSourcePacket_rowCount_le_cube S

theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_paperSourcePower {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45PaperSourcePacket P N) (w : CGLRealSmoothBump) (targetExponent : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump (S.denominator * (15 + targetExponent)) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 * cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          S.base ^ targetExponent := by
  simpa [CGLLemma45PaperSourcePacket.toSourceScale] using
    norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_any_sourcePower S.toSourceScale w targetExponent

structure CGLLemma45LiteralEpsilonSourcePacket {q R : ℕ}
    (P : CGLFibreSeparatedPacket q R) (N : CGLPositiveLength)
    extends CGLLemma45PaperSourcePacket P N where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  spacing_epsilon : base ^ epsilon ≤ P.spacing

noncomputable def CGLLemma45LiteralEpsilonSourcePacket.epsilonDenominator
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) : ℕ :=
  (exists_nat_one_div_lt S.epsilon_pos).choose + 1

theorem cglLemma45LiteralEpsilonSourcePacket_epsilonDenominator_pos
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) : 0 < S.epsilonDenominator :=
  Nat.succ_pos _

theorem cglLemma45LiteralEpsilonSourcePacket_epsilonDenominator_inv_lt
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) :
    (1 : ℝ) / S.epsilonDenominator < S.epsilon := by
  simpa [CGLLemma45LiteralEpsilonSourcePacket.epsilonDenominator, Nat.cast_add, Nat.cast_one] using
    (exists_nat_one_div_lt S.epsilon_pos).choose_spec

theorem cglLemma45LiteralEpsilonSourcePacket_spacing_power
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) :
    S.base ^ 1 ≤ P.spacing ^ S.epsilonDenominator := by
  have hb : (1 : ℝ) ≤ S.base := by linarith [S.base_five]
  have hd : 0 < (S.epsilonDenominator : ℝ) := by
    exact_mod_cast cglLemma45LiteralEpsilonSourcePacket_epsilonDenominator_pos S
  have hr : S.base ^ ((1 : ℝ) / S.epsilonDenominator) ≤ P.spacing :=
    (Real.rpow_le_rpow_of_exponent_le hb
      (cglLemma45LiteralEpsilonSourcePacket_epsilonDenominator_inv_lt S).le).trans
      S.spacing_epsilon
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (by linarith [S.base_five]) _) hr hd.le
  rw [← Real.rpow_mul (by linarith [S.base_five])] at hp
  rw [Real.rpow_natCast] at hp
  have hmul : (1 / (S.epsilonDenominator : ℝ)) * S.epsilonDenominator = 1 := by
    field_simp
  rw [hmul, Real.rpow_one] at hp
  simpa using hp

def CGLLemma45LiteralEpsilonSourcePacket.toPaperSourcePacket
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) : CGLLemma45PaperSourcePacket P N where
  time := S.time
  time_one := S.time_one
  base := S.base
  base_eq_modulus_mul_time := S.base_eq_modulus_mul_time
  base_five := S.base_five
  length_le := S.length_le
  numerator := 1
  numerator_pos := Nat.succ_pos _
  denominator := S.epsilonDenominator
  denominator_pos := cglLemma45LiteralEpsilonSourcePacket_epsilonDenominator_pos S
  spacing_power := cglLemma45LiteralEpsilonSourcePacket_spacing_power S
  ordinate_bound := S.ordinate_bound

theorem norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_literalEpsilonSourcePower
    {q R : ℕ} {P : CGLFibreSeparatedPacket q R} {N : CGLPositiveLength}
    (S : CGLLemma45LiteralEpsilonSourcePacket P N) (w : CGLRealSmoothBump)
    (targetExponent : ℕ) :
    ‖cglLemma45OffDiagonalFrequencyTerm w N (cglLemma45FibreModulus q) R
      (cglLemma45FibreRows P) 0‖ ≤
      (cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump
        (S.epsilonDenominator * (15 + targetExponent)) *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0 *
        cglLogFourierAmplitudeAllOrderBudget w.toCGLSmoothBump 0) /
          S.base ^ targetExponent := by
  simpa [CGLLemma45LiteralEpsilonSourcePacket.toPaperSourcePacket] using
    norm_cglLemma45OffDiagonalFrequencyTerm_zero_le_paperSourcePower
      S.toPaperSourcePacket w targetExponent

end RHTower
