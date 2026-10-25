import GaloisForLFunctions.BezoutValuationIncidence.UniformFloorMeansAndMovingVaughanGrams
import GaloisForLFunctions.BezoutValuationIncidence.TheAbsoluteVaughanRemainderBudgetHasTheTrivialExponent
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FiniteKernelsRepairAPositiveDriftOnlyAtItsPole

/-!
# Fixed Vaughan packets and their explicit obstructions

Finite Vaughan packets retain their linear means, smooth-power terms, and the original
interior receiver. Equal coefficients on the two convolution pieces cancel those pieces
exactly, leaving the receiver and three finite floor or pole corrections.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (pronicNorm subHalfZetaCoeff pronicNorm_nonneg pronicNorm_le_of_abs_le
   pronicNorm_add_le pronicNorm_smul pronicNorm_congr pronicNorm_sum_le
   pronicNorm_sawtooth_le abs_natDiv_sub_div_le)
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- A signed linear combination of the five literal Vaughan pieces. -/
def pmPronicVaughanPacket (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) (n : ℕ) : ℝ :=
  ∑ i : Fin 5, w i * pmPronicVaughanPiece ε U V n i

/-- The linear mean of a fixed Vaughan packet. -/
def pmPronicVaughanPacketLinearMean (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) : ℝ :=
  ∑ i : Fin 5, w i * pmPronicVaughanMean ε U V i

/-- The coefficient of the smooth power after removing the linear mean. -/
def pmPronicVaughanPacketSmoothMean (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) : ℝ :=
  subHalfZetaCoeff ε *
    (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
    (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b) * (w 3 - w 2)

/-- Admission of a coefficient vector is bounded pronic norm of its actual packet. -/
def pmPronicVaughanPacketAdmitted (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) : Prop :=
  ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmPronicVaughanPacket ε U V w) T ≤ B

theorem pmPronicVaughanPacket_one (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPacket ε U V (fun _ => 1) n = pmBezoutInteriorPrefix ε n := by
  simpa only [pmPronicVaughanPacket, one_mul] using sum_pmPronicVaughanPiece ε U V n

/-- Subtracting the receiver direction isolates the four remaining coefficient differences. -/
theorem pmPronicVaughanPacket_sub_receiver (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) (n : ℕ) :
    pmPronicVaughanPacket ε U V w n - w 3 * pmBezoutInteriorPrefix ε n =
      (w 0 - w 3) * pmPronicVaughanPiece ε U V n 0 +
        (w 1 - w 3) * pmPronicVaughanPiece ε U V n 1 +
        (w 2 - w 3) * pmPronicVaughanPiece ε U V n 2 +
        (w 4 - w 3) * pmPronicVaughanPiece ε U V n 4 := by
  have hs := sum_pmPronicVaughanPiece ε U V n
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
  change pmPronicVaughanPiece ε U V n 0 +
    (pmPronicVaughanPiece ε U V n 1 + (pmPronicVaughanPiece ε U V n 2 +
      (pmPronicVaughanPiece ε U V n 3 + pmPronicVaughanPiece ε U V n 4))) =
        pmBezoutInteriorPrefix ε n at hs
  simp only [pmPronicVaughanPacket, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (w 0 * pmPronicVaughanPiece ε U V n 0 +
    (w 1 * pmPronicVaughanPiece ε U V n 1 + (w 2 * pmPronicVaughanPiece ε U V n 2 +
      (w 3 * pmPronicVaughanPiece ε U V n 3 + w 4 * pmPronicVaughanPiece ε U V n 4)))) -
        w 3 * pmBezoutInteriorPrefix ε n = _
  linear_combination w 3 * hs

/-- The finite absolute mass controlling a small leg's centered floor errors. -/
def pmPronicVaughanSmallMass (ε : ℝ) (U : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 U, |(moebius d : ℝ)| * (d : ℝ) ^ (-ε)

theorem pmPronicVaughanSmallMass_nonneg (ε : ℝ) (U : ℕ) :
    0 ≤ pmPronicVaughanSmallMass ε U :=
  sum_nonneg fun d _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

private theorem small_piece_eq_finite_floor_sum (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 0 =
      ∑ d ∈ Icc 1 U, (moebius d : ℝ) * (d : ℝ) ^ (-ε) * (n / d : ℕ) := by
  change (∑ d ∈ Icc 1 (min U n), (moebius d : ℝ) * pmPronicFloorWeight ε n d) = _
  simp only [pmPronicFloorWeight, ← mul_assoc]
  apply sum_subset (Icc_subset_Icc_right (min_le_left U n))
  intro d hd hnot
  have hnd : n < d := by
    have := (mem_Icc.mp hd).1
    have := (mem_Icc.mp hd).2
    simp only [mem_Icc] at hnot
    omega
  simp only [Nat.div_eq_of_lt hnd, Nat.cast_zero, mul_zero]

/-- Centering a finite small leg gives exactly its finite sum of floor errors. -/
theorem pmPronicVaughanPiece_small_sub_mean_eq (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 0 - pmPronicVaughanMean ε U V 0 * n =
      ∑ d ∈ Icc 1 U, (moebius d : ℝ) * (d : ℝ) ^ (-ε) *
        (((n / d : ℕ) : ℝ) - (n : ℝ) / d) := by
  change pmPronicVaughanPiece ε U V n 0 - pmPronicVaughanSmallDensity ε U * n = _
  rw [small_piece_eq_finite_floor_sum]
  simp only [pmPronicVaughanSmallDensity, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro d _
  ring

/-- A fixed small leg differs from its linear mean by a bounded floor error. -/
theorem abs_pmPronicVaughanPiece_small_sub_mean_le (ε : ℝ) (U V n : ℕ) :
    |pmPronicVaughanPiece ε U V n 0 - pmPronicVaughanMean ε U V 0 * n| ≤
      pmPronicVaughanSmallMass ε U := by
  rw [pmPronicVaughanPiece_small_sub_mean_eq]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_right (by positivity)
    (abs_natDiv_sub_div_le n d (mem_Icc.mp hd).1)

/-- The small leg's centered norm costs only its critical absolute mass, uniformly in the horizon. -/
theorem pronicNorm_pmPronicVaughanPiece_small_sub_mean_le (ε : ℝ) (U V T : ℕ) :
    pronicNorm (fun n => pmPronicVaughanPiece ε U V n 0 -
      pmPronicVaughanMean ε U V 0 * n) T ≤ Real.sqrt 2 * pmVaughanAtomicAbsoluteMass ε U := by
  have heq : (fun n => pmPronicVaughanPiece ε U V n 0 -
      pmPronicVaughanMean ε U V 0 * n) =
      fun n => ∑ d ∈ Icc 1 U, (moebius d : ℝ) * (d : ℝ) ^ (-ε) *
        (((n / d : ℕ) : ℝ) - (n : ℝ) / d) :=
    funext (pmPronicVaughanPiece_small_sub_mean_eq ε U V)
  rw [heq]
  apply (pronicNorm_sum_le (Icc 1 U) _ T).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 U, |(moebius d : ℝ) * (d : ℝ) ^ (-ε)| *
        (Real.sqrt 2 * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply sum_le_sum
      intro d hd
      rw [pronicNorm_smul]
      exact mul_le_mul_of_nonneg_left (pronicNorm_sawtooth_le (mem_Icc.mp hd).1 T)
        (abs_nonneg _)
    _ = _ := by
      rw [pmVaughanAtomicAbsoluteMass, mul_sum]
      apply sum_congr rfl
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hd0.le _),
        show -(ε + 1 / 2) = -ε + -(1 / 2 : ℝ) by ring, Real.rpow_add hd0]
      ring

/-- The pole correction has uniformly bounded centered size. -/
theorem abs_pmPronicVaughanPiece_pole_sub_mean_le {ε : ℝ} (hε : 0 ≤ ε)
    (U V n : ℕ) :
    |pmPronicVaughanPiece ε U V n 4 - pmPronicVaughanMean ε U V 4 * n| ≤ 1 / 2 := by
  have heq : pmPronicVaughanPiece ε U V n 4 - pmPronicVaughanMean ε U V 4 * n =
      -addDiff (pmActiveSawtoothComponent ε) n := by
    change -(pmPowerDampedDivisorDensity ε).re * n -
      addDiff (pmActiveSawtoothComponent ε) n - (-(pmPowerDampedDivisorDensity ε).re) * n = _
    ring
  rw [heq, abs_neg]
  exact abs_addDiff_pmActiveSawtoothComponent_le_half hε n

/-- Centering commutes exactly with removing the common receiver direction. -/
theorem pmPronicVaughanPacket_sub_receiver_sub_linear (ε : ℝ) (U V : ℕ)
    (w : Fin 5 → ℝ) (n : ℕ) :
    pmPronicVaughanPacket ε U V w n - w 3 * pmBezoutInteriorPrefix ε n -
        pmPronicVaughanPacketLinearMean ε U V w * n =
      ∑ i : Fin 5, (w i - w 3) *
        (pmPronicVaughanPiece ε U V n i - pmPronicVaughanMean ε U V i * n) := by
  have hterm (i : Fin 5) : (w i - w 3) *
      (pmPronicVaughanPiece ε U V n i - pmPronicVaughanMean ε U V i * n) =
      w i * pmPronicVaughanPiece ε U V n i - w 3 * pmPronicVaughanPiece ε U V n i -
        (w i * pmPronicVaughanMean ε U V i) * n +
          (w 3 * pmPronicVaughanMean ε U V i) * n := by ring
  simp only [hterm, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum,
    sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, mul_zero, zero_mul, add_zero,
    pmPronicVaughanPacket, pmPronicVaughanPacketLinearMean]

/-- The explicit error remaining when the two convolution coefficients agree. -/
def pmPronicVaughanPacketFloorBudget (ε : ℝ) (U V : ℕ) (w : Fin 5 → ℝ) : ℝ :=
  |w 0 - w 3| * pmPronicVaughanSmallMass ε U +
    |w 1 - w 3| * pmPronicVaughanSmallMass ε V + |w 4 - w 3| / 2

/-- Cancelling the convolution and linear means leaves a bounded perturbation of the receiver. -/
theorem abs_pmPronicVaughanPacket_sub_receiver_le {ε : ℝ} (hε : 0 ≤ ε)
    (U V : ℕ) (w : Fin 5 → ℝ) (hw : w 2 = w 3)
    (hmean : pmPronicVaughanPacketLinearMean ε U V w = 0) (n : ℕ) :
    |pmPronicVaughanPacket ε U V w n - w 3 * pmBezoutInteriorPrefix ε n| ≤
      pmPronicVaughanPacketFloorBudget ε U V w := by
  have heq := pmPronicVaughanPacket_sub_receiver_sub_linear ε U V w n
  rw [hmean, zero_mul, sub_zero] at heq
  let e : Fin 5 → ℝ := fun i =>
    pmPronicVaughanPiece ε U V n i - pmPronicVaughanMean ε U V i * n
  change _ = ∑ i : Fin 5, (w i - w 3) * e i at heq
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at heq
  change _ = (w 0 - w 3) * e 0 + ((w 1 - w 3) * e 1 +
    ((w 2 - w 3) * e 2 + ((w 3 - w 3) * e 3 + (w 4 - w 3) * e 4))) at heq
  simp only [hw, sub_self, zero_mul, zero_add] at heq
  have h0 : |e 0| ≤ pmPronicVaughanSmallMass ε U :=
    abs_pmPronicVaughanPiece_small_sub_mean_le ε U V n
  have h1 : |e 1| ≤ pmPronicVaughanSmallMass ε V :=
    abs_pmPronicVaughanPiece_small_sub_mean_le ε V U n
  have h4 : |e 4| ≤ 1 / 2 := abs_pmPronicVaughanPiece_pole_sub_mean_le hε U V n
  rw [heq]
  calc
    _ ≤ |(w 0 - w 3) * e 0| +
        (|(w 1 - w 3) * e 1| + |(w 4 - w 3) * e 4|) :=
      (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ = |w 0 - w 3| * |e 0| +
        (|w 1 - w 3| * |e 1| + |w 4 - w 3| * |e 4|) := by simp only [abs_mul]
    _ ≤ |w 0 - w 3| * pmPronicVaughanSmallMass ε U +
        (|w 1 - w 3| * pmPronicVaughanSmallMass ε V + |w 4 - w 3| * (1 / 2)) :=
      add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
        (add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h4 (abs_nonneg _)))
    _ = _ := by unfold pmPronicVaughanPacketFloorBudget; ring

private theorem bounded_pronicNorm_iff_of_bounded_difference {f g : ℕ → ℝ}
    {C : ℝ} (hC : ∀ T : ℕ, pronicNorm (fun n => f n - g n) T ≤ C) :
    (∃ B : ℝ, ∀ T : ℕ, pronicNorm f T ≤ B) ↔
      ∃ B : ℝ, ∀ T : ℕ, pronicNorm g T ≤ B := by
  have hswap (T : ℕ) : pronicNorm (fun n => g n - f n) T ≤ C := by
    have heq : pronicNorm (fun n => g n - f n) T =
        pronicNorm (fun n => (-1) * (f n - g n)) T :=
      pronicNorm_congr fun n _ => by ring
    rw [heq, pronicNorm_smul, abs_neg, abs_one, one_mul]
    exact hC T
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨C + B, fun T => ?_⟩
    have h := pronicNorm_add_le (fun n => g n - f n) f T
    simp only [sub_add_cancel] at h
    exact h.trans (add_le_add (hswap T) (hB T))
  · rintro ⟨B, hB⟩
    refine ⟨C + B, fun T => ?_⟩
    have h := pronicNorm_add_le (fun n => f n - g n) g T
    simp only [sub_add_cancel] at h
    exact h.trans (add_le_add (hC T) (hB T))

private theorem bounded_pronicNorm_smul_iff (a : ℝ) (f : ℕ → ℝ) :
    (∃ B : ℝ, ∀ T : ℕ, pronicNorm (fun n => a * f n) T ≤ B) ↔
      a = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm f T ≤ B := by
  by_cases ha : a = 0
  · simp only [ha, zero_mul, true_or, iff_true]
    exact ⟨0, fun T => by simp [pronicNorm]⟩
  · have ha0 : 0 < |a| := abs_pos.mpr ha
    simp only [ha, false_or]
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨B / |a|, fun T => ?_⟩
      apply (le_div_iff₀ ha0).mpr
      simpa only [pronicNorm_smul, mul_comm] using hB T
    · rintro ⟨B, hB⟩
      exact ⟨|a| * B, fun T => by
        rw [pronicNorm_smul]
        exact mul_le_mul_of_nonneg_left (hB T) ha0.le⟩

private theorem exists_pronicNorm_bound_of_finite_support {f : ℕ → ℝ} {N : ℕ}
    (hf : ∀ n, N < n → f n = 0) :
    ∃ B : ℝ, ∀ T : ℕ, pronicNorm f T ≤ B := by
  let B := ∑ n ∈ range (N + 1), |f n|
  have hB : 0 ≤ B := sum_nonneg fun n _ => abs_nonneg _
  refine ⟨B, fun T => pronicNorm_le_of_abs_le hB (fun n => ?_) T⟩
  by_cases hn : n ≤ N
  · exact single_le_sum (fun i _ => abs_nonneg (f i)) (mem_range.mpr (by omega))
  · rw [hf n (lt_of_not_ge hn), abs_zero]
    exact hB

/-- Beyond the fixed rectangle the partial pole sum is the product of the two harmonic sums. -/
theorem pmVaughanSmallSmallPoleSum_eq_harmonic_product (U V : ℕ) {n : ℕ}
    (hn : U * V ≤ n) :
    pmVaughanSmallSmallPoleSum U V n =
      (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
        (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b) := by
  unfold pmVaughanSmallSmallPoleSum
  rw [sum_mul]
  apply sum_congr rfl
  intro a ha
  rw [mul_sum]
  apply sum_congr rfl
  intro b hb
  have hab : a * b ≤ n :=
    (Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2).trans hn
  rw [if_pos hab, Nat.cast_mul, div_mul_div_comm]

/-- The finite rectangular floor prefix has only a bounded error from its linear mean. -/
theorem abs_pmVaughanSmallSmallFloor_sub_mean_le (ε : ℝ) (U V n : ℕ) :
    |pmVaughanSmallSmallFloor ε U V n -
        pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V * n| ≤
      pmPronicVaughanSmallMass ε U * pmPronicVaughanSmallMass ε V := by
  have heq : pmVaughanSmallSmallFloor ε U V n -
      pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V * n =
        ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
          ((moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)) *
            (((n / (a * b) : ℕ) : ℝ) - (n : ℝ) / (a * b : ℕ)) := by
    simp only [pmVaughanSmallSmallFloor, pmPronicFloorWeight,
      pmPronicVaughanSmallDensity, sum_mul, mul_sum]
    conv_lhs => rhs; rw [sum_comm]
    simp only [← sum_sub_distrib]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
    ring
  rw [heq]
  calc
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        |((moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)) *
          (((n / (a * b) : ℕ) : ℝ) - (n : ℝ) / (a * b : ℕ))| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun a _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        |(moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)| := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _)
        (abs_natDiv_sub_div_le n (a * b)
          (Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1))
    _ = _ := by
      simp only [pmPronicVaughanSmallMass, sum_mul, mul_sum]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      ring

/-- Removing the linear and smooth-power terms from the fixed small-small piece pays its norm. -/
theorem exists_pronicNorm_smallSmall_normal_form_bound {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (U V : ℕ) :
    ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => pmPronicVaughanPiece ε U V n 2 -
        pmPronicVaughanMean ε U V 2 * n +
          subHalfZetaCoeff ε *
            (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
            (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b) * (n : ℝ) ^ (1 - ε)) T ≤ B := by
  let F : ℕ → ℝ := fun n => pmVaughanSmallSmallFloor ε U V n -
    pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V * n
  let P : ℕ → ℝ := fun n => subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) *
    (pmVaughanSmallSmallPoleSum U V n -
      (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
        (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b))
  have hF (T : ℕ) : pronicNorm F T ≤
      pmPronicVaughanSmallMass ε U * pmPronicVaughanSmallMass ε V :=
    pronicNorm_le_of_abs_le (mul_nonneg (pmPronicVaughanSmallMass_nonneg ε U)
      (pmPronicVaughanSmallMass_nonneg ε V))
      (abs_pmVaughanSmallSmallFloor_sub_mean_le ε U V) T
  obtain ⟨BP, hP⟩ := exists_pronicNorm_bound_of_finite_support (N := U * V) (f := P)
    (fun n hn => by
      simp only [P, pmVaughanSmallSmallPoleSum_eq_harmonic_product U V hn.le,
        sub_self, mul_zero])
  refine ⟨|pmPronicPowerDensity ε| *
      (pmPronicVaughanSmallMass ε U * pmPronicVaughanSmallMass ε V) + BP +
        pmVaughanSmoothRemainderConstant ε *
          pmVaughanAtomicAbsoluteMass ε U * pmVaughanAtomicAbsoluteMass ε V,
    fun T => ?_⟩
  have heq : (fun n => pmPronicVaughanPiece ε U V n 2 -
      pmPronicVaughanMean ε U V 2 * n +
        subHalfZetaCoeff ε * (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
          (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b) * (n : ℝ) ^ (1 - ε)) =
      fun n => ((-pmPronicPowerDensity ε) * F n + (-1) * P n) +
        (-1) * pmVaughanSmoothRemainder ε U V n := by
    funext n
    rw [pmPronicVaughanPiece_smallSmall_expansion]
    change -pmPronicPowerDensity ε * pmVaughanSmallSmallFloor ε U V n -
      subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * pmVaughanSmallSmallPoleSum U V n -
      pmVaughanSmoothRemainder ε U V n -
        (-pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
          pmPronicVaughanSmallDensity ε V) * n + _ = _
    dsimp only [F, P]
    ring
  rw [heq]
  have h := (pronicNorm_add_le
    (fun n => (-pmPronicPowerDensity ε) * F n + (-1) * P n)
    (fun n => (-1) * pmVaughanSmoothRemainder ε U V n) T).trans
      (add_le_add (pronicNorm_add_le (fun n => (-pmPronicPowerDensity ε) * F n)
        (fun n => (-1) * P n) T) le_rfl)
  simp only [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
  exact h.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hF T) (abs_nonneg _)) (hP T))
    (pronicNorm_pmVaughanSmoothRemainder_le hε hε1 U V T))

/-- Every fixed packet has precisely its linear drift, smooth power, and receiver, up to paid norm. -/
theorem exists_pronicNorm_pmPronicVaughanPacket_normal_form_bound {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (U V : ℕ) (w : Fin 5 → ℝ) :
    ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => pmPronicVaughanPacket ε U V w n -
        w 3 * pmBezoutInteriorPrefix ε n - pmPronicVaughanPacketLinearMean ε U V w * n -
          pmPronicVaughanPacketSmoothMean ε U V w * (n : ℝ) ^ (1 - ε)) T ≤ B := by
  let e : Fin 5 → ℕ → ℝ := fun i n =>
    pmPronicVaughanPiece ε U V n i - pmPronicVaughanMean ε U V i * n
  let k : ℝ := subHalfZetaCoeff ε * (∑ a ∈ Icc 1 U, (moebius a : ℝ) / a) *
    (∑ b ∈ Icc 1 V, (moebius b : ℝ) / b)
  let r : ℕ → ℝ := fun n => e 2 n + k * (n : ℝ) ^ (1 - ε)
  obtain ⟨B2, h2⟩ := exists_pronicNorm_smallSmall_normal_form_bound hε hε1 U V
  change ∀ T : ℕ, pronicNorm r T ≤ B2 at h2
  have h0 (T : ℕ) : pronicNorm (e 0) T ≤ pmPronicVaughanSmallMass ε U :=
    pronicNorm_le_of_abs_le (pmPronicVaughanSmallMass_nonneg ε U)
      (abs_pmPronicVaughanPiece_small_sub_mean_le ε U V) T
  have h1 (T : ℕ) : pronicNorm (e 1) T ≤ pmPronicVaughanSmallMass ε V :=
    pronicNorm_le_of_abs_le (pmPronicVaughanSmallMass_nonneg ε V)
      (abs_pmPronicVaughanPiece_small_sub_mean_le ε V U) T
  have h4 (T : ℕ) : pronicNorm (e 4) T ≤ 1 / 2 :=
    pronicNorm_le_of_abs_le (by norm_num)
      (abs_pmPronicVaughanPiece_pole_sub_mean_le hε.le U V) T
  refine ⟨|w 0 - w 3| * pmPronicVaughanSmallMass ε U +
    |w 1 - w 3| * pmPronicVaughanSmallMass ε V + |w 2 - w 3| * B2 + |w 4 - w 3| / 2,
    fun T => ?_⟩
  have heq : (fun n => pmPronicVaughanPacket ε U V w n -
      w 3 * pmBezoutInteriorPrefix ε n - pmPronicVaughanPacketLinearMean ε U V w * n -
        pmPronicVaughanPacketSmoothMean ε U V w * (n : ℝ) ^ (1 - ε)) =
      fun n => ((w 0 - w 3) * e 0 n + (w 1 - w 3) * e 1 n) +
        (w 2 - w 3) * r n + (w 4 - w 3) * e 4 n := by
    funext n
    rw [pmPronicVaughanPacket_sub_receiver_sub_linear]
    change (∑ i : Fin 5, (w i - w 3) * e i n) -
      (k * (w 3 - w 2)) * (n : ℝ) ^ (1 - ε) = _
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change (w 0 - w 3) * e 0 n + ((w 1 - w 3) * e 1 n +
      ((w 2 - w 3) * e 2 n + ((w 3 - w 3) * e 3 n + (w 4 - w 3) * e 4 n))) -
        (k * (w 3 - w 2)) * (n : ℝ) ^ (1 - ε) = _
    dsimp only [r]
    ring
  rw [heq]
  have h01 := pronicNorm_add_le (fun n => (w 0 - w 3) * e 0 n)
    (fun n => (w 1 - w 3) * e 1 n) T
  have h012 := pronicNorm_add_le
    (fun n => (w 0 - w 3) * e 0 n + (w 1 - w 3) * e 1 n)
    (fun n => (w 2 - w 3) * r n) T
  have h0124 := pronicNorm_add_le
    (fun n => ((w 0 - w 3) * e 0 n + (w 1 - w 3) * e 1 n) +
      (w 2 - w 3) * r n)
    (fun n => (w 4 - w 3) * e 4 n) T
  simp only [pronicNorm_smul] at h01 h012 h0124
  have h0' := mul_le_mul_of_nonneg_left (h0 T) (abs_nonneg (w 0 - w 3))
  have h1' := mul_le_mul_of_nonneg_left (h1 T) (abs_nonneg (w 1 - w 3))
  have h2' := mul_le_mul_of_nonneg_left (h2 T) (abs_nonneg (w 2 - w 3))
  have h4' := mul_le_mul_of_nonneg_left (h4 T) (abs_nonneg (w 4 - w 3))
  linarith only [h01, h012, h0124, h0', h1', h2', h4']

/-- Vanishing drift coefficients reduce admission exactly to the original receiver direction. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_two_means_zero {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (U V : ℕ) (w : Fin 5 → ℝ)
    (hlinear : pmPronicVaughanPacketLinearMean ε U V w = 0)
    (hsmooth : pmPronicVaughanPacketSmoothMean ε U V w = 0) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  obtain ⟨C, hC⟩ := exists_pronicNorm_pmPronicVaughanPacket_normal_form_bound hε hε1 U V w
  simp only [hlinear, hsmooth, zero_mul, sub_zero] at hC
  exact (bounded_pronicNorm_iff_of_bounded_difference hC).trans
    (bounded_pronicNorm_smul_iff (w 3) (pmBezoutInteriorPrefix ε))

/-- Once the two explicit cancellations hold, admission retains exactly the receiver direction. -/
theorem pmPronicVaughanPacketAdmitted_iff_of_equal_convolution_coefficients {ε : ℝ}
    (hε : 0 ≤ ε) (U V : ℕ) (w : Fin 5 → ℝ) (hw : w 2 = w 3)
    (hmean : pmPronicVaughanPacketLinearMean ε U V w = 0) :
    pmPronicVaughanPacketAdmitted ε U V w ↔
      w 3 = 0 ∨ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (pmBezoutInteriorPrefix ε) T ≤ B := by
  have hb := abs_pmPronicVaughanPacket_sub_receiver_le hε U V w hw hmean
  have hC : 0 ≤ pmPronicVaughanPacketFloorBudget ε U V w :=
    (abs_nonneg _).trans (hb 0)
  have hn := fun T => pronicNorm_le_of_abs_le hC hb T
  exact (bounded_pronicNorm_iff_of_bounded_difference hn).trans
    (bounded_pronicNorm_smul_iff (w 3) (pmBezoutInteriorPrefix ε))

/-- Admission forces the linear mean to vanish at every fixed pair of cutoffs. -/
theorem pmPronicVaughanPacketLinearMean_eq_zero_of_admitted {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (w : Fin 5 → ℝ) (hw : pmPronicVaughanPacketAdmitted ε U V w) :
    pmPronicVaughanPacketLinearMean ε U V w = 0 := by
  obtain ⟨B, hB⟩ := hw
  have heq (T : ℕ) : pronicNorm (pmPronicVaughanPacket ε U V w) T ^ 2 =
      ∑ n ∈ Icc 1 T, pmPronicVaughanPacket ε U V w n ^ 2 / (pronicSeq n : ℝ) := by
    rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hz : Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, pmPronicVaughanPacket ε U V w n ^ 2 / (pronicSeq n : ℝ)) / T)
      atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ (tendsto_const_div_atTop_nhds_zero_nat (B ^ 2))
    · exact Eventually.of_forall fun T => by positivity
    · refine Eventually.of_forall fun T => ?_
      rw [← heq]
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB T) 2) (Nat.cast_nonneg T)
  have hl := tendsto_pmPronicVaughan_combinationEnergy_div_nat hε U V w
  change Tendsto (fun T : ℕ =>
      (∑ n ∈ Icc 1 T, pmPronicVaughanPacket ε U V w n ^ 2 / (pronicSeq n : ℝ)) / T)
      atTop (𝓝 (pmPronicVaughanPacketLinearMean ε U V w ^ 2)) at hl
  have hsq := tendsto_nhds_unique hl hz
  nlinarith only [hsq]

/-- Compensate the first finite floor leg by the pole component. -/
def pmPronicVaughanFirstPaidCoefficients (ε : ℝ) (U : ℕ) : Fin 5 → ℝ :=
  ![1, 0, 0, 0, pmPronicVaughanSmallDensity ε U / (pmPowerDampedDivisorDensity ε).re]

/-- Compensate the second finite floor leg by the pole component. -/
def pmPronicVaughanSecondPaidCoefficients (ε : ℝ) (V : ℕ) : Fin 5 → ℝ :=
  ![0, 1, 0, 0, pmPronicVaughanSmallDensity ε V / (pmPowerDampedDivisorDensity ε).re]

theorem pmPronicVaughanPacketLinearMean_firstPaid {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanPacketLinearMean ε U V (pmPronicVaughanFirstPaidCoefficients ε U) = 0 := by
  have hρ := (pmPowerDampedDivisorDensity_re_pos hε).ne'
  simp [pmPronicVaughanPacketLinearMean, pmPronicVaughanFirstPaidCoefficients,
    pmPronicVaughanMean, Fin.sum_univ_succ, hρ]

theorem pmPronicVaughanPacketLinearMean_secondPaid {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanPacketLinearMean ε U V (pmPronicVaughanSecondPaidCoefficients ε V) = 0 := by
  have hρ := (pmPowerDampedDivisorDensity_re_pos hε).ne'
  simp [pmPronicVaughanPacketLinearMean, pmPronicVaughanSecondPaidCoefficients,
    pmPronicVaughanMean, Fin.sum_univ_succ, hρ]

/-- The compensated first small leg is admitted at every positive damping. -/
theorem pmPronicVaughanPacketAdmitted_firstPaid {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanPacketAdmitted ε U V (pmPronicVaughanFirstPaidCoefficients ε U) := by
  apply (pmPronicVaughanPacketAdmitted_iff_of_equal_convolution_coefficients hε.le U V _ rfl
    (pmPronicVaughanPacketLinearMean_firstPaid hε U V)).mpr
  exact Or.inl rfl

/-- The compensated second small leg is admitted at every positive damping. -/
theorem pmPronicVaughanPacketAdmitted_secondPaid {ε : ℝ} (hε : 0 < ε) (U V : ℕ) :
    pmPronicVaughanPacketAdmitted ε U V (pmPronicVaughanSecondPaidCoefficients ε V) := by
  apply (pmPronicVaughanPacketAdmitted_iff_of_equal_convolution_coefficients hε.le U V _ rfl
    (pmPronicVaughanPacketLinearMean_secondPaid hε U V)).mpr
  exact Or.inl rfl

/-- The three surviving coefficient directions span exactly the two cancellation equations. -/
theorem pmPronicVaughan_coefficients_eq_paid_add_receiver {ε : ℝ} (hε : 0 < ε)
    (U V : ℕ) (w : Fin 5 → ℝ) (hw : w 2 = w 3)
    (hmean : pmPronicVaughanPacketLinearMean ε U V w = 0) (i : Fin 5) :
    w i = (w 0 - w 3) * pmPronicVaughanFirstPaidCoefficients ε U i +
      (w 1 - w 3) * pmPronicVaughanSecondPaidCoefficients ε V i + w 3 := by
  have hρ := (pmPowerDampedDivisorDensity_re_pos hε).ne'
  have hm : w 0 * pmPronicVaughanSmallDensity ε U +
      (w 1 * pmPronicVaughanSmallDensity ε V +
        (w 2 * (-pmPronicPowerDensity ε * pmPronicVaughanSmallDensity ε U *
          pmPronicVaughanSmallDensity ε V) +
          (w 3 * ((pmPowerDampedDivisorDensity ε).re - pmPronicVaughanSmallDensity ε U -
            pmPronicVaughanSmallDensity ε V + pmPronicPowerDensity ε *
              pmPronicVaughanSmallDensity ε U * pmPronicVaughanSmallDensity ε V) +
            w 4 * (-(pmPowerDampedDivisorDensity ε).re)))) = 0 := by
    simp only [pmPronicVaughanPacketLinearMean, Fin.sum_univ_succ, Fin.sum_univ_zero,
      add_zero] at hmean
    change w 0 * pmPronicVaughanMean ε U V 0 +
      (w 1 * pmPronicVaughanMean ε U V 1 + (w 2 * pmPronicVaughanMean ε U V 2 +
        (w 3 * pmPronicVaughanMean ε U V 3 + w 4 * pmPronicVaughanMean ε U V 4))) = 0 at hmean
    exact hmean
  rw [hw] at hm
  fin_cases i
  · change w 0 = (w 0 - w 3) * 1 + (w 1 - w 3) * 0 + w 3
    ring
  · change w 1 = (w 0 - w 3) * 0 + (w 1 - w 3) * 1 + w 3
    ring
  · change w 2 = (w 0 - w 3) * 0 + (w 1 - w 3) * 0 + w 3
    simpa only [mul_zero, zero_add] using hw
  · change w 3 = (w 0 - w 3) * 0 + (w 1 - w 3) * 0 + w 3
    ring
  · change w 4 = (w 0 - w 3) *
      (pmPronicVaughanSmallDensity ε U / (pmPowerDampedDivisorDensity ε).re) +
      (w 1 - w 3) *
        (pmPronicVaughanSmallDensity ε V / (pmPowerDampedDivisorDensity ε).re) + w 3
    field_simp [hρ]
    linear_combination -hm

end GaloisForLFunctions.BezoutValuationIncidence
