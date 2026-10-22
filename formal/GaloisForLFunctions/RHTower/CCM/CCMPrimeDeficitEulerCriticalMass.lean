import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerResolvent

/-!
# Fixed Euler completion has unbounded positive critical mass

The coprime residual has no coefficient signs left. Its absolute mass at
exponent one half is nevertheless unbounded, witnessed by a single
arithmetic progression. Thus positivity alone cannot supply a uniform
critical norm for a fixed modulus. This does not bound or disprove a
signed estimate for the actual prime deficit.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

def ccmEulerCriticalMass (P U : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 U, ccmEulerRough P n / Real.sqrt n

/-- One surviving residue class already forces arbitrary critical mass. -/
theorem ccmEulerCriticalMass_square_lower (P B : ℕ) :
    (B : ℝ) + 1 ≤ ccmEulerCriticalMass (P + 1) (((P + 2) * (B + 1)) ^ 2) := by
  let K := (P + 2) * (B + 1) ^ 2
  let L := (P + 2) * (B + 1)
  let S := (Finset.Icc 1 K).image (fun j => (P + 1) * j + 1)
  have hK : 1 ≤ K := Nat.one_le_iff_ne_zero.mpr (by dsimp [K]; positivity)
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hKL : (P + 2) * K = L ^ 2 := by dsimp [K, L]; ring
  have hbound {j : ℕ} (hj : j ∈ Finset.Icc 1 K) : (P + 1) * j + 1 ≤ L ^ 2 := by
    calc
      _ ≤ (P + 1) * K + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ (Finset.mem_Icc.mp hj).2) _
      _ ≤ (P + 2) * K := by nlinarith only [hK]
      _ = _ := hKL
  have hsub : S ⊆ Finset.Icc 1 (L ^ 2) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    exact Finset.mem_Icc.mpr ⟨by omega, hbound hj⟩
  have hinj : Set.InjOn (fun j => (P + 1) * j + 1) (Finset.Icc 1 K) := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos P) (Nat.add_right_cancel hab)
  have hterm {j : ℕ} (hj : j ∈ Finset.Icc 1 K) :
      1 / (L : ℝ) ≤ ccmEulerRough (P + 1) ((P + 1) * j + 1) /
        Real.sqrt ((P + 1) * j + 1 : ℕ) := by
    have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
    have hn1 : 1 < (P + 1) * j + 1 := by nlinarith [Nat.mul_pos (Nat.succ_pos P) hjpos]
    have hcop : ((P + 1) * j + 1).Coprime (P + 1) := by
      simpa only [Nat.coprime_mul_left_add_left] using Nat.coprime_one_left (P + 1)
    have hq : ccmEulerRough (P + 1) ((P + 1) * j + 1) = 1 := if_pos ⟨hn1, hcop⟩
    have hspos : 0 < Real.sqrt ((P + 1) * j + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
    have hsle : Real.sqrt ((P + 1) * j + 1 : ℕ) ≤ (L : ℝ) :=
      Real.sqrt_le_iff.mpr ⟨hL.le, by exact_mod_cast hbound hj⟩
    rw [hq]
    exact one_div_le_one_div_of_le hspos hsle
  change (B : ℝ) + 1 ≤ ccmEulerCriticalMass (P + 1) (L ^ 2)
  calc
    (B : ℝ) + 1 = ∑ _j ∈ Finset.Icc 1 K, 1 / (L : ℝ) := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      dsimp [K, L]
      push_cast
      field_simp
    _ ≤ ∑ j ∈ Finset.Icc 1 K, ccmEulerRough (P + 1) ((P + 1) * j + 1) /
        Real.sqrt ((P + 1) * j + 1 : ℕ) := Finset.sum_le_sum fun _ hj => hterm hj
    _ = ∑ n ∈ S, ccmEulerRough (P + 1) n / Real.sqrt n :=
      (Finset.sum_image (f := fun n => ccmEulerRough (P + 1) n / Real.sqrt n) hinj).symm
    _ ≤ ccmEulerCriticalMass (P + 1) (L ^ 2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => div_nonneg (ccmEulerRough_nonneg _ _) (Real.sqrt_nonneg _))

/-- No fixed positive Euler modulus gives a bounded positive critical mass. -/
theorem ccmEulerCriticalMass_unbounded (P : ℕ) :
    ∀ C : ℝ, ∃ U : ℕ, C < ccmEulerCriticalMass (P + 1) U := by
  intro C
  obtain ⟨B, hB⟩ := exists_nat_gt C
  exact ⟨((P + 2) * (B + 1)) ^ 2,
    hB.trans_le ((le_add_of_nonneg_right zero_le_one).trans (ccmEulerCriticalMass_square_lower P B))⟩

def ccmEulerRenewalCriticalMass (P U : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 U, ccmEulerRenewalKernel P n / Real.sqrt n

/-- The quadratic renewal operator contains the entire product square. -/
theorem ccmEulerCriticalMass_sq_le_renewalCriticalMass (P U : ℕ) :
    ccmEulerCriticalMass P U ^ 2 ≤ ccmEulerRenewalCriticalMass P (U ^ 2) := by
  let w := fun n => ccmEulerRough P n / Real.sqrt n
  have hw : ∀ n, 0 ≤ w n := fun n =>
    div_nonneg (ccmEulerRough_nonneg P n) (Real.sqrt_nonneg _)
  have he : ccmEulerRenewalCriticalMass P (U ^ 2) =
      ∑ a ∈ Finset.Icc 1 (U ^ 2), ∑ b ∈ Finset.Icc 1 (U ^ 2 / a), w a * w b := by
    unfold ccmEulerRenewalCriticalMass ccmEulerRenewalKernel
    simp only [pow_two, ArithmeticFunction.mul_apply, Finset.sum_div]
    have hh : (∑ n ∈ Finset.Icc 1 (U * U),
        ∑ ab ∈ n.divisorsAntidiagonal,
          ccmEulerRough P ab.1 * ccmEulerRough P ab.2 / Real.sqrt n) =
        ∑ n ∈ Finset.Icc 1 (U * U),
          ∑ ab ∈ n.divisorsAntidiagonal, w ab.1 * w ab.2 := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro ab hab
      rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul,
        Real.sqrt_mul (Nat.cast_nonneg _)]
      exact (div_mul_div_comm _ _ _ _).symm
    rw [hh]
    exact Sieve.sum_Icc_divisorsAntidiagonal_swap (fun a b => w a * w b) (U * U)
  have hU : U ≤ U ^ 2 := by
    rcases eq_or_ne U 0 with rfl | hU
    · simp
    · have : 1 ≤ U := Nat.one_le_iff_ne_zero.mpr hU
      nlinarith
  have hsub : Finset.Icc 1 U ⊆ Finset.Icc 1 (U ^ 2) :=
    Finset.Icc_subset_Icc le_rfl hU
  calc
    ccmEulerCriticalMass P U ^ 2 = ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 U, w a * w b := by
      rw [ccmEulerCriticalMass, pow_two, Finset.sum_mul_sum]
    _ ≤ ∑ a ∈ Finset.Icc 1 U, ∑ b ∈ Finset.Icc 1 (U ^ 2 / a), w a * w b := by
      apply Finset.sum_le_sum
      intro a ha
      have hUa : U ≤ U ^ 2 / a := by
        rw [Nat.le_div_iff_mul_le (Finset.mem_Icc.mp ha).1, pow_two]
        exact Nat.mul_le_mul_left U (Finset.mem_Icc.mp ha).2
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hUa)
        (fun b _ _ => mul_nonneg (hw a) (hw b))
    _ ≤ ∑ a ∈ Finset.Icc 1 (U ^ 2), ∑ b ∈ Finset.Icc 1 (U ^ 2 / a), w a * w b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun a _ _ => Finset.sum_nonneg fun b _ => mul_nonneg (hw a) (hw b))
    _ = _ := he.symm

/-- Even one renewal step has unbounded mass at the critical exponent
for every fixed positive modulus. A uniform positive contraction is impossible. -/
theorem ccmEulerRenewalCriticalMass_unbounded (P : ℕ) :
    ∀ C : ℝ, ∃ U : ℕ, C < ccmEulerRenewalCriticalMass (P + 1) U := by
  intro C
  obtain ⟨B, hB⟩ := exists_nat_gt C
  let V := ((P + 2) * (B + 1)) ^ 2
  have hm : (B : ℝ) + 1 ≤ ccmEulerCriticalMass (P + 1) V :=
    ccmEulerCriticalMass_square_lower P B
  refine ⟨V ^ 2, hB.trans_le ?_⟩
  calc
    (B : ℝ) ≤ ((B : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) B]
    _ ≤ ccmEulerCriticalMass (P + 1) V ^ 2 := by gcongr
    _ ≤ _ := ccmEulerCriticalMass_sq_le_renewalCriticalMass _ _

end RHTower
