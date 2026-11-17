import GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing

/-!
# Proper-power contacts in a window of fixed multiplicative width

In a window from Q/D² to Q the normalized contact weight Λ(k)/√k of
all proper powers has bounded total mass, uniformly in the top degree Q.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset ArithmeticFunction

/-- A packet may use any subset of the proper powers in the window. -/
theorem properPowerContactWindow_le (S : Finset ℕ) {Q : ℕ} {D : ℝ}
    (hD : 0 ≤ D) (hS : ∀ k ∈ S, 0 < k ∧ k ≤ Q ∧ ¬ k.Prime ∧ (Q : ℝ) ≤ D^2 * k) :
    ∑ k ∈ S, vonMangoldt k / Real.sqrt k ≤ 3 * (Real.log 4 + 4) * D := by
  have hC : 0 ≤ 3 * (Real.log 4 + 4) := by positivity
  by_cases hQ : Q = 0
  · have h : S = ∅ := eq_empty_iff_forall_notMem.mpr fun k hk => by
      obtain ⟨hk0, hkQ, _⟩ := hS k hk
      omega
    simpa [h] using mul_nonneg hC hD
  have hr : 0 < Real.sqrt Q := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hQ))
  have hsub : S ⊆ (Ioc 0 Q).filter (fun k => ¬ k.Prime) := by
    intro k hk
    obtain ⟨hk0, hkQ, hkp, _⟩ := hS k hk
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hk0, hkQ⟩, hkp⟩
  have hmass : ∑ k ∈ S, vonMangoldt k ≤ 3 * (Real.log 4 + 4) * Real.sqrt Q := by
    calc ∑ k ∈ S, vonMangoldt k ≤ ∑ k ∈ (Ioc 0 Q).filter (fun k => ¬ k.Prime), vonMangoldt k :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => vonMangoldt_nonneg
      _ = Chebyshev.psi Q - Chebyshev.theta Q := by
          rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast]
      _ ≤ _ := GreenCalculusOfThePrimeFreeWindow.psi_sub_theta_le_three_mul_sqrt _
  suffices h : Real.sqrt Q * (∑ k ∈ S, vonMangoldt k / Real.sqrt k) ≤
      Real.sqrt Q * (3 * (Real.log 4 + 4) * D) from
    le_of_not_gt fun he => (not_lt_of_ge h) (mul_lt_mul_of_pos_left he hr)
  rw [Finset.mul_sum]
  calc ∑ k ∈ S, Real.sqrt Q * (vonMangoldt k / Real.sqrt k)
      ≤ ∑ k ∈ S, D * vonMangoldt k := by
        apply sum_le_sum
        intro k hk
        obtain ⟨hk0, _, _, hscale⟩ := hS k hk
        have hs := Real.sqrt_le_sqrt hscale
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hD] at hs
        have hk' : 0 < Real.sqrt k := Real.sqrt_pos_of_pos (Nat.cast_pos.mpr hk0)
        rw [← mul_div_assoc, div_le_iff₀ hk']
        calc Real.sqrt Q * vonMangoldt k ≤ (D * Real.sqrt k) * vonMangoldt k :=
              mul_le_mul_of_nonneg_right hs vonMangoldt_nonneg
          _ = _ := by ring
    _ ≤ D * (3 * (Real.log 4 + 4) * Real.sqrt Q) := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left hmass hD
    _ = _ := by ring

/-- Sampling a bounded atom at multiples of a fixed degree does not increase
the proper-power bound, even when its support lies far from that degree. -/
theorem properPowerSample_le (S : Finset ℕ) (j : ℕ) (hj : 0 < j)
    (hS : ∀ k ∈ S, 0 < k ∧ ¬ k.Prime) {g : ℕ → ℝ} {X D : ℝ}
    (hX : 0 < X) (hD : 1 ≤ D) (hg : ∀ t, g t ≤ 1)
    (hw : ∀ t, g t ≠ 0 → X ≤ t ∧ (t : ℝ) ≤ D*X) :
    ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * g (j*k) ≤ 3 * (Real.log 4 + 4) * D := by
  classical
  let T := S.filter (fun k => g (j*k) ≠ 0)
  let Q := ⌊D*X/j⌋₊
  have hj' : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hd : 0 ≤ D := zero_le_one.trans hD
  have hT (k : ℕ) (hk : k ∈ T) :
      0 < k ∧ k ≤ Q ∧ ¬ k.Prime ∧ (Q : ℝ) ≤ D^2*k := by
    obtain ⟨hks, hkg⟩ := mem_filter.mp hk
    obtain ⟨hlo, hhi⟩ := hw _ hkg
    push_cast at hlo hhi
    have hq : (Q : ℝ) ≤ D*X/j := Nat.floor_le (by positivity)
    refine ⟨(hS k hks).1, Nat.le_floor ?_, (hS k hks).2, hq.trans ?_⟩
    · exact (le_div_iff₀ hj').mpr (by linarith only [hhi])
    · apply (div_le_iff₀ hj').mpr
      calc D * X ≤ D * (j*k) := mul_le_mul_of_nonneg_left hlo hd
        _ ≤ D * (D * (j*k)) := le_mul_of_one_le_left (by positivity) hD
        _ = _ := by ring
  calc ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * g (j*k)
      = ∑ k ∈ T, (vonMangoldt k / Real.sqrt k) * g (j*k) := by
        apply (sum_subset (filter_subset _ _) ?_).symm
        intro k hk hkt
        have hz : g (j*k) = 0 := by
          by_contra h
          exact hkt (mem_filter.mpr ⟨hk, h⟩)
        rw [hz, mul_zero]
    _ ≤ ∑ k ∈ T, vonMangoldt k / Real.sqrt k := sum_le_sum fun k _ =>
      mul_le_of_le_one_right (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)) (hg _)
    _ ≤ _ := properPowerContactWindow_le T (Q := Q) hd hT

/-- The logarithmic mesh mass of one bounded atom depends only on its
multiplicative width, uniformly in mesh size and center. -/
theorem harmonicSample_le (S : Finset ℕ) {f : ℕ → ℝ} {X D : ℝ}
    (hX : 0 < X) (hD : 0 ≤ D) (hf : ∀ j, f j ≤ 1)
    (hw : ∀ j, f j ≠ 0 → X ≤ j ∧ (j : ℝ) ≤ D*X) :
    ∑ j ∈ S, f j / j ≤ D := by
  classical
  let T := S.filter (fun j => f j ≠ 0)
  have hsub : T ⊆ Ioc 0 ⌊D*X⌋₊ := by
    intro j hj
    obtain ⟨hl, hu⟩ := hw j (mem_filter.mp hj).2
    exact mem_Ioc.mpr ⟨Nat.cast_pos.mp (hX.trans_le hl), Nat.le_floor hu⟩
  calc ∑ j ∈ S, f j / j = ∑ j ∈ T, f j / j := by
        apply (sum_subset (filter_subset _ _) ?_).symm
        intro j hj hjt
        have hz : f j = 0 := by
          by_contra h
          exact hjt (mem_filter.mpr ⟨hj, h⟩)
        rw [hz, zero_div]
    _ ≤ ∑ j ∈ T, (1 : ℝ) / X := by
        apply sum_le_sum
        intro j hj
        have hl := (hw j (mem_filter.mp hj).2).1
        exact (div_le_div_of_nonneg_right (hf _) (Nat.cast_nonneg _)).trans
          (one_div_le_one_div_of_le hX hl)
    _ ≤ ∑ j ∈ Ioc 0 ⌊D*X⌋₊, (1 : ℝ) / X :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ ≤ D := by
      simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one_div]
      exact (div_le_iff₀ hX).mpr (Nat.floor_le (mul_nonneg hD hX.le))

/-- Sum first over multiples of each lower degree. A uniform contact bound
for each multiple row costs only the logarithmic mass at the lower degrees. -/
theorem properPowerPairing_le (S J : Finset ℕ) (f g : ℕ → ℝ) {B M : ℝ}
    (hB : 0 ≤ B) (hf : ∀ j, 0 ≤ f j)
    (hrow : ∀ j ∈ J, ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * g (j*k) ≤ B)
    (hmass : ∑ j ∈ J, f j / j ≤ M) :
    ∑ k ∈ S, (2 / Real.sqrt k * ∑ j ∈ J, f j * g (j*k) / j) * vonMangoldt k ≤ 2 * M * B := by
  calc ∑ k ∈ S, (2 / Real.sqrt k * ∑ j ∈ J, f j * g (j*k) / j) * vonMangoldt k
      = ∑ k ∈ S, ∑ j ∈ J, (2 * (f j / j)) * ((vonMangoldt k / Real.sqrt k) * g (j*k)) := by
        apply sum_congr rfl
        intro k _
        rw [mul_sum, sum_mul]
        exact sum_congr rfl fun j _ => by ring
    _ = ∑ j ∈ J, (2 * (f j / j)) * ∑ k ∈ S, (vonMangoldt k / Real.sqrt k) * g (j*k) := by
        rw [sum_comm]
        exact sum_congr rfl fun j _ => (mul_sum ..).symm
    _ ≤ ∑ j ∈ J, (2 * (f j / j)) * B := sum_le_sum fun j hj =>
      mul_le_mul_of_nonneg_left (hrow j hj) (mul_nonneg (by norm_num) (div_nonneg (hf j) (Nat.cast_nonneg _)))
    _ ≤ _ := by
      rw [← sum_mul, ← mul_sum]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmass (by norm_num)) hB

#print axioms properPowerContactWindow_le

end GaloisForLFunctions.CountingHolography.Sections
