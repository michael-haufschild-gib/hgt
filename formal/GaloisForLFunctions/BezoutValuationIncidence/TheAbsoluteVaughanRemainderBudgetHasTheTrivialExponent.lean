import GaloisForLFunctions.BezoutValuationIncidence.TheFixedVaughanGramHasRankOneLeadingTerm
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SubHalfDampingPartialPoleSumsAndLogarithmicMomentIndexLaws
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum
import GaloisForLFunctions.RHTower.FloorTransformWienerClass

/-!
# The absolute budget for the smooth Vaughan remainder

The individual dilated smooth-power remainders have finite pronic norm. Summing their
norms over a Vaughan rectangle costs a product of two critical Wiener partial sums.
Squarefree density forces those absolute partial sums to retain the trivial power.
This lower bound concerns the absolute budget, not the signed remainder itself.
-/

open Finset Filter ArithmeticFunction RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (subHalfDilationRemainder subHalfZetaCoeff floorSumRate pronicNorm pronicNorm_sum_le
   pronicNorm_smul pronicNorm_subHalfDilationRemainder_le subHalfRemainder
   weightCenteredPrefix dampedSignWeight unitSign sum_Icc_sum_divisors_eq_floor)
open scoped BigOperators Topology

noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence

set_option autoImplicit false

/-- Absolute coefficient mass at the exponent charged by the atomic norm estimate. -/
def pmVaughanAtomicAbsoluteMass (ε : ℝ) (U : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, |(moebius a : ℝ)| * (a : ℝ) ^ (-(ε + 1 / 2))

/-- The signed double remainder after the unsigned smooth-power expansion. -/
def pmVaughanSmoothRemainder (ε : ℝ) (U V n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
    ((moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)) *
      (if a * b ≤ n then subHalfDilationRemainder ε n (a * b) else 0)

/-- The existing uniform constant for a single smooth-power remainder. -/
def pmVaughanSmoothRemainderConstant (ε : ℝ) : ℝ :=
  Real.sqrt (1 + 1 / ε) *
    (floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|)

/-- The remaining floor prefix of the two truncated Möbius factors. -/
def pmVaughanSmallSmallFloor (ε : ℝ) (U V n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
    (moebius a : ℝ) * (moebius b : ℝ) * pmPronicFloorWeight ε n (a * b)

/-- The signed partial pole sum retains the product cutoff inside the rectangle. -/
def pmVaughanSmallSmallPoleSum (U V n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
    if a * b ≤ n then (moebius a : ℝ) * (moebius b : ℝ) / (a * b : ℕ) else 0

private theorem unsigned_floor_expansion (ε : ℝ) (n : ℕ) :
    (∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * (n / d : ℕ)) =
      pmPronicPowerDensity ε * n + subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) +
        subHalfRemainder ε n := by
  unfold subHalfRemainder weightCenteredPrefix
  rw [sum_Icc_sum_divisors_eq_floor]
  simp only [dampedSignWeight, unitSign, one_mul]
  change _ = pmPronicPowerDensity ε * n + subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) +
    ((∑ d ∈ Icc 1 n, (d : ℝ) ^ (-ε) * (n / d : ℕ)) -
      pmPronicPowerDensity ε * n - subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε))
  ring

/-- Each product atom retains its floor term, partial pole term, and smooth remainder. -/
theorem pmPronicFloorWeight_multiples_expansion (ε : ℝ) {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (∑ k ∈ Icc 1 (n / m), pmPronicFloorWeight ε n (m * k)) =
      pmPronicPowerDensity ε * pmPronicFloorWeight ε n m +
        (if m ≤ n then subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) / m else 0) +
          (m : ℝ) ^ (-ε) * (if m ≤ n then subHalfDilationRemainder ε n m else 0) := by
  by_cases hmn : m ≤ n
  · simp only [if_pos hmn]
    rw [sum_pmPronicFloorWeight_multiples, unsigned_floor_expansion]
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hcoeff : (m : ℝ) ^ (-ε) * (m : ℝ) ^ (-(1 - ε)) = 1 / m := by
      rw [← Real.rpow_add hmR, show -ε + -(1 - ε) = -1 by ring, Real.rpow_neg_one,
        one_div]
    unfold pmPronicFloorWeight subHalfDilationRemainder
    linear_combination (norm := ring_nf)
      (subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε)) * hcoeff
  · simp [Nat.div_eq_of_lt (lt_of_not_ge hmn), hmn, pmPronicFloorWeight]

private theorem sum_Icc_min_eq_of_zero_above {f : ℕ → ℝ} {U n : ℕ}
    (hf : ∀ a ∈ Icc 1 U, n < a → f a = 0) :
    (∑ a ∈ Icc 1 (min U n), f a) = ∑ a ∈ Icc 1 U, f a := by
  apply sum_subset (Icc_subset_Icc_right (min_le_left U n))
  intro a ha hnot
  apply hf a ha
  have := mem_Icc.mp ha
  simp only [mem_Icc] at hnot
  omega

/-- Terms outside the moving endpoint vanish, so the small-small term uses a full rectangle. -/
theorem pmPronicVaughanPiece_smallSmall_eq_rectangle (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 2 =
      -(∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        (moebius a : ℝ) * (moebius b : ℝ) *
          ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)) := by
  change -(∑ a ∈ Icc 1 (min U n), (moebius a : ℝ) *
    ∑ b ∈ Icc 1 (min V n), (moebius b : ℝ) *
      ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)) = _
  congr 1
  simp only [mul_sum, mul_assoc]
  rw [sum_Icc_min_eq_of_zero_above (U := U) (n := n) (fun a _ hna => ?_)]
  · apply sum_congr rfl
    intro a ha
    apply sum_Icc_min_eq_of_zero_above
    intro b _ hnb
    have hab : b ≤ a * b := by
      simpa only [one_mul] using Nat.mul_le_mul_right b (mem_Icc.mp ha).1
    simp [Nat.div_eq_of_lt (hnb.trans_le hab)]
  · apply sum_eq_zero
    intro b hb
    have hab : a ≤ a * b := by
      simpa only [mul_one] using Nat.mul_le_mul_left a (mem_Icc.mp hb).1
    simp [Nat.div_eq_of_lt (hna.trans_le hab)]

/-- Exact smooth-power extraction from the literal small-small Vaughan piece. -/
theorem pmPronicVaughanPiece_smallSmall_expansion (ε : ℝ) (U V n : ℕ) :
    pmPronicVaughanPiece ε U V n 2 =
      -pmPronicPowerDensity ε * pmVaughanSmallSmallFloor ε U V n -
        subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * pmVaughanSmallSmallPoleSum U V n -
          pmVaughanSmoothRemainder ε U V n := by
  have h : (∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
      (moebius a : ℝ) * (moebius b : ℝ) *
        ∑ k ∈ Icc 1 (n / (a * b)), pmPronicFloorWeight ε n (a * b * k)) =
      pmPronicPowerDensity ε * pmVaughanSmallSmallFloor ε U V n +
        subHalfZetaCoeff ε * (n : ℝ) ^ (1 - ε) * pmVaughanSmallSmallPoleSum U V n +
          pmVaughanSmoothRemainder ε U V n := by
    simp only [pmVaughanSmallSmallFloor, pmVaughanSmallSmallPoleSum,
      pmVaughanSmoothRemainder]
    conv_rhs => simp only [mul_sum]
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    rw [← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro b hb
    rw [pmPronicFloorWeight_multiples_expansion ε
      (Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1)]
    split_ifs <;> ring
  rw [pmPronicVaughanPiece_smallSmall_eq_rectangle, h]
  ring

theorem pmVaughanAtomicAbsoluteMass_nonneg (ε : ℝ) (U : ℕ) :
    0 ≤ pmVaughanAtomicAbsoluteMass ε U :=
  sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg a) _)

private theorem vaughan_atom_mass_factor (ε : ℝ) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |(moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)| *
        ((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      (|(moebius a : ℝ)| * (a : ℝ) ^ (-(ε + 1 / 2))) *
        (|(moebius b : ℝ)| * (b : ℝ) ^ (-(ε + 1 / 2))) := by
  have hab : (0 : ℝ) < (a * b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  rw [mul_assoc (|(moebius a : ℝ)| * |(moebius b : ℝ)|), ← Real.rpow_add hab,
    show -ε + -(1 / 2 : ℝ) = -(ε + 1 / 2) by ring,
    Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
  ring

/-- Finite norm subadditivity gives a completely explicit rectangular budget. -/
theorem pronicNorm_pmVaughanSmoothRemainder_le {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (U V T : ℕ) :
    pronicNorm (pmVaughanSmoothRemainder ε U V) T ≤
      pmVaughanSmoothRemainderConstant ε *
        pmVaughanAtomicAbsoluteMass ε U * pmVaughanAtomicAbsoluteMass ε V := by
  unfold pmVaughanSmoothRemainder
  refine (pronicNorm_sum_le (Icc 1 U) _ T).trans ?_
  calc
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        pronicNorm (fun n =>
          ((moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)) *
            (if a * b ≤ n then subHalfDilationRemainder ε n (a * b) else 0)) T :=
      sum_le_sum fun a _ => pronicNorm_sum_le (Icc 1 V) _ T
    _ ≤ ∑ a ∈ Icc 1 U, ∑ b ∈ Icc 1 V,
        |(moebius a : ℝ) * (moebius b : ℝ) * ((a * b : ℕ) : ℝ) ^ (-ε)| *
          (pmVaughanSmoothRemainderConstant ε * ((a * b : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
      apply sum_le_sum
      intro a ha
      apply sum_le_sum
      intro b hb
      rw [pronicNorm_smul]
      exact mul_le_mul_of_nonneg_left
        (pronicNorm_subHalfDilationRemainder_le hε hε1
          (Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1) T) (abs_nonneg _)
    _ = _ := by
      simp only [pmVaughanAtomicAbsoluteMass, mul_sum, sum_mul]
      conv_rhs => rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      have h := vaughan_atom_mass_factor ε (mem_Icc.mp ha).1 (mem_Icc.mp hb).1
      linear_combination pmVaughanSmoothRemainderConstant ε * h

/-- The absolute mass has the usual subcritical power upper bound. -/
theorem pmVaughanAtomicAbsoluteMass_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (U : ℕ) :
    pmVaughanAtomicAbsoluteMass ε U ≤
      (U : ℝ) ^ (1 / 2 - ε) / (1 / 2 - ε) + 1 := by
  have h := Sieve.sum_rpow_neg_subcritical_le
    (show 0 < ε + 1 / 2 by linarith) (show ε + 1 / 2 < 1 by linarith) U
  rw [show 1 - (ε + 1 / 2) = 1 / 2 - ε by ring] at h
  apply le_trans ?_ h
  apply sum_le_sum
  intro a _
  have hμ : |(moebius a : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg a) _) hμ

/-- The squarefree quarter-density bound gives the lower power at every positive cutoff. -/
theorem pmVaughanAtomicAbsoluteMass_lower {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) :
    (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 - ε) ≤ pmVaughanAtomicAbsoluteMass ε N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hbase := criticalNorm_moebiusPowerWeight_zero_lower hN
  change (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) ≤
    ∑ d ∈ Icc 1 N, |(moebius d : ℝ) * (d : ℝ) ^ (-(0 : ℝ))| *
      (d : ℝ) ^ (-(1 / 2 : ℝ)) at hbase
  simp only [neg_zero, Real.rpow_zero, mul_one] at hbase
  calc
    _ = (N : ℝ) ^ (-ε) * ((1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [mul_left_comm, ← Real.rpow_add hNpos]
      congr 2
      ring
    _ ≤ (N : ℝ) ^ (-ε) *
        ∑ d ∈ Icc 1 N, |(moebius d : ℝ)| * (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hNpos.le _)
    _ ≤ _ := by
      rw [mul_sum]
      apply sum_le_sum
      intro d hd
      have hdpos : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      have hdN : (d : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hd).2
      have hpow := Real.rpow_le_rpow_of_nonpos hdpos hdN (neg_nonpos.mpr hε)
      have h := mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (abs_nonneg (moebius d : ℝ))
          (Real.rpow_nonneg hdpos.le (-(1 / 2 : ℝ))))
      have heq : (d : ℝ) ^ (-ε) *
          (|(moebius d : ℝ)| * (d : ℝ) ^ (-(1 / 2 : ℝ))) =
          |(moebius d : ℝ)| * (d : ℝ) ^ (-(ε + 1 / 2)) := by
        rw [mul_left_comm, ← Real.rpow_add hdpos]
        congr 2
        ring
      exact h.trans_eq heq

private theorem square_budget_power (ε : ℝ) (N : ℕ) :
    ((N : ℝ) ^ (1 / 2 - ε)) ^ 4 = (N : ℝ) ^ (2 - 4 * ε) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  norm_num
  ring

/-- The squared absolute budget at a square-root rectangle has the trivial lower power. -/
theorem pmVaughan_absolute_square_budget_lower {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) :
    (1 / 256 : ℝ) * (N : ℝ) ^ (2 - 4 * ε) ≤
      (pmVaughanAtomicAbsoluteMass ε N * pmVaughanAtomicAbsoluteMass ε N) ^ 2 := by
  have h := pow_le_pow_left₀
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    (pmVaughanAtomicAbsoluteMass_lower hε hN) 4
  rw [mul_pow, square_budget_power] at h
  norm_num at h
  nlinarith only [h]

/-- The same absolute budget has a matching power upper bound below half damping. -/
theorem exists_pmVaughan_absolute_square_budget_upper {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (pmVaughanAtomicAbsoluteMass ε N * pmVaughanAtomicAbsoluteMass ε N) ^ 2 ≤
        C * (N : ℝ) ^ (2 - 4 * ε) := by
  have hq : 0 < 1 / 2 - ε := by linarith
  refine ⟨(1 + 1 / (1 / 2 - ε)) ^ 4, by positivity, fun N hN => ?_⟩
  have hpow : 1 ≤ (N : ℝ) ^ (1 / 2 - ε) :=
    Real.one_le_rpow (by exact_mod_cast hN) hq.le
  have hmass : pmVaughanAtomicAbsoluteMass ε N ≤
      (1 + 1 / (1 / 2 - ε)) * (N : ℝ) ^ (1 / 2 - ε) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 - ε) / (1 / 2 - ε) + 1 :=
        pmVaughanAtomicAbsoluteMass_le hε hε2 N
      _ ≤ (N : ℝ) ^ (1 / 2 - ε) / (1 / 2 - ε) + (N : ℝ) ^ (1 / 2 - ε) :=
        add_le_add le_rfl hpow
      _ = _ := by ring
  have h := pow_le_pow_left₀ (pmVaughanAtomicAbsoluteMass_nonneg ε N) hmass 4
  rw [mul_pow, square_budget_power] at h
  nlinarith only [h]

/-- No fixed power saving is available in this absolute budget, even eventually. -/
theorem not_pmVaughan_absolute_square_budget_power_saving {ε δ : ℝ}
    (hε : 0 ≤ ε) (hδ : 0 < δ) :
    ¬ ∃ C : ℝ, ∀ᶠ N : ℕ in atTop,
      (pmVaughanAtomicAbsoluteMass ε N * pmVaughanAtomicAbsoluteMass ε N) ^ 2 ≤
        C * (N : ℝ) ^ (2 - 4 * ε - δ) := by
  rintro ⟨C, hC⟩
  have hgrow := ((tendsto_rpow_atTop hδ).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_gt_atTop (256 * C)
  obtain ⟨N, hbound, hlarge, hN⟩ :=
    (hC.and (hgrow.and (eventually_ge_atTop 1))).exists
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsplit : (N : ℝ) ^ (2 - 4 * ε) =
      (N : ℝ) ^ δ * (N : ℝ) ^ (2 - 4 * ε - δ) := by
    rw [← Real.rpow_add hNpos]
    congr 1
    ring
  have hchain := (pmVaughan_absolute_square_budget_lower hε hN).trans hbound
  rw [hsplit, ← mul_assoc] at hchain
  have hcancel := le_of_mul_le_mul_right hchain
    (Real.rpow_pos_of_pos hNpos (2 - 4 * ε - δ))
  change 256 * C < (N : ℝ) ^ δ at hlarge
  linarith only [hcancel, hlarge]

end GaloisForLFunctions.BezoutValuationIncidence
