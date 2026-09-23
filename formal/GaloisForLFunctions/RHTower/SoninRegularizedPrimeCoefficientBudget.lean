import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Literal regularized Euler coefficients: logarithmic head and inverse-linear square tail

Source coefficients and prime/depth labels are not changed. No Xi or RH premise is used.
This module does not assert a determinant weld or an RH conclusion.
-/

namespace RHTower
noncomputable section

theorem norm_soninLogPrimePowerCoefficient_le_geometric (p : Nat.Primes) (k : ℕ) :
    ‖soninLogPrimePowerCoefficient (p, k)‖ ≤
      (3 / 4 : ℝ) ^ k / (2 * (p : ℝ)) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  let r : ℝ := (Real.sqrt (p : ℝ))⁻¹
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ (2 : ℕ) = (p : ℝ)⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hp.le]
  have hi : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  have hr : r ≤ (3 / 4 : ℝ) := by nlinarith
  rw [soninLogPrimePowerCoefficient_eq_sqrtInvPow_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change r ^ (k + 2) / (k + 2 : ℝ) ≤ _
  calc
    _ ≤ r ^ (k + 2) / 2 := by
      exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by
        have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        linarith)
    _ = r ^ k * (p : ℝ)⁻¹ / 2 := by rw [pow_add, hr2]
    _ ≤ (3 / 4 : ℝ) ^ k * (p : ℝ)⁻¹ / 2 := by gcongr
    _ = _ := by ring

theorem norm_soninLogPrimePowerCoefficient_sq_le_geometric (p : Nat.Primes) (k : ℕ) :
    ‖soninLogPrimePowerCoefficient (p, k)‖ ^ (2 : ℕ) ≤
      ((p : ℝ)⁻¹) ^ (2 : ℕ) * (1 / 2 : ℝ) ^ k := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.prop.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hi : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2
  refine (norm_soninLogPrimePowerCoefficient_sq_le (p, k)).trans ?_
  change ((p : ℝ)⁻¹) ^ (k + 2) ≤ _
  rw [pow_add, mul_comm]
  gcongr

end
end RHTower

open scoped BigOperators
namespace RHTower
noncomputable section

def soninPrimeDepthBox (M : ℕ) : Finset (Nat.Primes × ℕ) :=
  ((Finset.Icc 1 M).subtype Nat.Prime) ×ˢ Finset.range M

set_option backward.isDefEq.respectTransparency false in
theorem mem_soninPrimeDepthBox (M : ℕ) (pk : Nat.Primes × ℕ) :
    pk ∈ soninPrimeDepthBox M ↔ (pk.1 : ℕ) ≤ M ∧ pk.2 < M := by
  rcases pk with ⟨⟨p, hp⟩, k⟩
  change (((⟨p, hp⟩ : {n : ℕ // Nat.Prime n}), k) ∈
    ((Finset.Icc 1 M).subtype Nat.Prime).product (Finset.range M)) ↔ p ≤ M ∧ k < M
  have hprod := Finset.mem_product (s := (Finset.Icc 1 M).subtype Nat.Prime)
    (t := Finset.range M) (p := ((⟨p, hp⟩ : {n : ℕ // Nat.Prime n}), k))
  exact hprod.trans (by
    simp only [Finset.mem_subtype, Finset.mem_Icc, Finset.mem_range]
    have hp1 := hp.one_lt
    omega)

theorem sum_depth_norm_soninLogPrimePowerCoefficient_le
    (p : Nat.Primes) (s : Finset ℕ) :
    ∑ k ∈ s, ‖soninLogPrimePowerCoefficient (p, k)‖ ≤ 2 / (p : ℝ) := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).div_const (2 * (p : ℝ))
  calc
    _ ≤ ∑ k ∈ s, (3 / 4 : ℝ) ^ k / (2 * (p : ℝ)) :=
      Finset.sum_le_sum fun k _ => norm_soninLogPrimePowerCoefficient_le_geometric p k
    _ ≤ ∑' k, (3 / 4 : ℝ) ^ k / (2 * (p : ℝ)) :=
      hg.summable.sum_le_tsum s (fun k _ => by positivity)
    _ = 2 / (p : ℝ) := by rw [hg.tsum_eq]; norm_num; ring

set_option backward.isDefEq.respectTransparency false in
theorem sum_norm_soninLogPrimePowerCoefficient_box_le_log (M : ℕ) :
    ∑ pk ∈ soninPrimeDepthBox M, ‖soninLogPrimePowerCoefficient pk‖ ≤
      2 * (1 + Real.log M) := by
  let P : Finset Nat.Primes := (Finset.Icc 1 M).subtype Nat.Prime
  have hp : (∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹) ≤
      ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ := by
    classical
    calc
      _ = ∑ n ∈ P.image (fun p : Nat.Primes => (p : ℕ)), (n : ℝ)⁻¹ := by
        exact (Finset.sum_image (s := P) (f := fun n : ℕ => (n : ℝ)⁻¹)
          (g := fun p : Nat.Primes => (p : ℕ))
          (fun p _ q _ h => Subtype.ext h)).symm
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
          exact Finset.mem_subtype.mp hp
        · intros
          positivity
  have hh : (∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹) ≤ 1 + Real.log M := by
    simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      using harmonic_le_one_add_log M
  calc
    _ = ∑ p ∈ P, ∑ k ∈ Finset.range M,
        ‖soninLogPrimePowerCoefficient (p, k)‖ := Finset.sum_product _ _ _
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) :=
      Finset.sum_le_sum fun p _ => sum_depth_norm_soninLogPrimePowerCoefficient_le p _
    _ = 2 * ∑ p ∈ P, ((p : ℕ) : ℝ)⁻¹ := by rw [Finset.mul_sum]; simp [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hp.trans hh) (by norm_num)

theorem sonin_integer_inverseSquare_tail_le (M : ℕ) (hM : 0 < M) :
    (∑' n : ℕ, if M < n then ((n : ℝ) ^ (2 : ℕ))⁻¹ else 0) ≤ (M : ℝ)⁻¹ := by
  apply Real.tsum_le_of_sum_le
  · intro n
    change 0 ≤ if M < n then ((n : ℝ) ^ (2 : ℕ))⁻¹ else 0
    split_ifs <;> positivity
  · intro s
    let N := max M (s.sup id)
    have hMN : M ≤ N := le_max_left _ _
    calc
      _ = ∑ n ∈ s.filter (M < ·), ((n : ℝ) ^ (2 : ℕ))⁻¹ := (Finset.sum_filter _ _).symm
      _ ≤ ∑ n ∈ Finset.Ioc M N, ((n : ℝ) ^ (2 : ℕ))⁻¹ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hs, hm⟩ := Finset.mem_filter.mp hn
          exact Finset.mem_Ioc.mpr ⟨hm, (Finset.le_sup (f := id) hs).trans (le_max_right _ _)⟩
        · intros
          positivity
      _ ≤ (M : ℝ)⁻¹ - (N : ℝ)⁻¹ := sum_Ioc_inv_sq_le_sub hM.ne' hMN
      _ ≤ _ := sub_le_self _ (by positivity)

end
end RHTower

open scoped BigOperators
namespace RHTower
noncomputable section

theorem sonin_geometricHalf_tail (M : ℕ) :
    (∑' k : ℕ, if M ≤ k then (1 / 2 : ℝ) ^ k else 0) = 2 * (1 / 2 : ℝ) ^ M := by
  have hshift := (show Function.Injective (fun n : ℕ => n + M) from
    fun _ _ h => Nat.add_right_cancel h).tsum_eq
      (f := fun k : ℕ => if M ≤ k then (1 / 2 : ℝ) ^ k else 0) (by
        intro k hk
        have hm : M ≤ k := by
          by_contra h
          simp [Function.mem_support, h] at hk
        exact ⟨k - M, Nat.sub_add_cancel hm⟩)
  rw [← hshift]
  simp only [Nat.le_add_left, ite_true, pow_add, tsum_mul_right]
  rw [hasSum_geometric_two.tsum_eq]

theorem summable_sonin_prime_inverseSquare :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ (2 : ℕ))⁻¹) :=
  (Real.summable_nat_pow_inv.mpr (by omega : 1 < 2)).comp_injective Subtype.val_injective

set_option maxHeartbeats 1200000 in
theorem sonin_prime_inverseSquare_tail_le (M : ℕ) (hM : 0 < M) :
    (∑' p : Nat.Primes, if M < (p : ℕ) then ((p : ℝ) ^ (2 : ℕ))⁻¹ else 0) ≤
      (M : ℝ)⁻¹ := by
  have hn : Summable (fun n : ℕ => if M < n then ((n : ℝ) ^ (2 : ℕ))⁻¹ else 0) := by
    apply ((Real.summable_nat_pow_inv.mpr (by omega : 1 < 2)).indicator {n | M < n}).congr
    intro n
    exact Set.indicator_apply {n : ℕ | M < n} (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) n
  have hp := hn.comp_injective (show Function.Injective (fun p : Nat.Primes => (p : ℕ))
    from Subtype.val_injective)
  exact (hp.tsum_le_tsum_of_inj (fun p : Nat.Primes => (p : ℕ))
    Subtype.val_injective (fun n _ => by split_ifs <;> positivity)
    (fun _ => le_rfl) hn).trans (sonin_integer_inverseSquare_tail_le M hM)

theorem sonin_prime_inverseSquare_mass_le_one :
    (∑' p : Nat.Primes, ((p : ℝ) ^ (2 : ℕ))⁻¹) ≤ 1 := by
  have h := sonin_prime_inverseSquare_tail_le 1 (by omega)
  simpa only [show ∀ p : Nat.Primes, 1 < (p : ℕ) from fun p => p.prop.one_lt,
    ite_true, Nat.cast_one, inv_one] using h

set_option maxHeartbeats 800000 in
theorem sum_sq_soninLogPrimePowerCoefficient_boxTail_le
    (M : ℕ) (hM : 0 < M) :
    (∑' pk : Nat.Primes × ℕ, if pk ∈ soninPrimeDepthBox M then 0 else
      ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ)) ≤ 4 / (M : ℝ) := by
  classical
  let P : Nat.Primes → ℝ := fun p => ((p : ℝ) ^ (2 : ℕ))⁻¹
  let Q : ℕ → ℝ := fun k => (1 / 2 : ℝ) ^ k
  let A : Nat.Primes × ℕ → ℝ := fun pk =>
    (if M < (pk.1 : ℕ) then P pk.1 else 0) * Q pk.2
  let B : Nat.Primes × ℕ → ℝ := fun pk =>
    P pk.1 * (if M ≤ pk.2 then Q pk.2 else 0)
  have hP : Summable P := summable_sonin_prime_inverseSquare
  have hQ : Summable Q := hasSum_geometric_two.summable
  have hPM : Summable (fun p : Nat.Primes => if M < (p : ℕ) then P p else 0) := by
    apply (hP.indicator {p | M < (p : ℕ)}).congr
    intro p
    exact Set.indicator_apply {p : Nat.Primes | M < (p : ℕ)} P p
  have hQM : Summable (fun k : ℕ => if M ≤ k then Q k else 0) := by
    apply (hQ.indicator {k | M ≤ k}).congr
    intro k
    exact Set.indicator_apply {k : ℕ | M ≤ k} Q k
  have hA : Summable A := by
    exact hPM.mul_of_nonneg hQ
      (fun p => by change 0 ≤ if M < (p : ℕ) then P p else 0; split_ifs <;> positivity)
      (fun k => by change 0 ≤ Q k; positivity)
  have hB : Summable B := by
    exact hP.mul_of_nonneg hQM
      (fun p => by change 0 ≤ P p; positivity)
      (fun k => by change 0 ≤ if M ≤ k then Q k else 0; split_ifs <;> positivity)
  have hpoint (pk : Nat.Primes × ℕ) :
      (if pk ∈ soninPrimeDepthBox M then 0 else
        ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ)) ≤ A pk + B pk := by
    have hcoef : ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ) ≤ P pk.1 * Q pk.2 := by
      simpa [P, Q, inv_pow] using norm_soninLogPrimePowerCoefficient_sq_le_geometric pk.1 pk.2
    by_cases hp : (pk.1 : ℕ) ≤ M <;> by_cases hk : pk.2 < M
    · simp [mem_soninPrimeDepthBox, hp, hk, A, B, not_lt.mpr hp, not_le.mpr hk]
    · simpa [mem_soninPrimeDepthBox, hp, hk, A, B, not_lt.mpr hp, Nat.le_of_not_gt hk]
        using hcoef
    · simpa [mem_soninPrimeDepthBox, hp, hk, A, B, Nat.lt_of_not_ge hp, not_le.mpr hk]
        using hcoef
    · have hn : 0 ≤ P pk.1 * Q pk.2 := by dsimp [P, Q]; positivity
      simp only [mem_soninPrimeDepthBox, hp, false_and, ite_false, A, B,
        Nat.lt_of_not_ge hp, Nat.le_of_not_gt hk, ite_true]
      linarith
  have htail : Summable (fun pk : Nat.Primes × ℕ =>
      if pk ∈ soninPrimeDepthBox M then 0 else ‖soninLogPrimePowerCoefficient pk‖ ^ (2 : ℕ)) :=
    (hA.add hB).of_nonneg_of_le (fun pk => by split_ifs <;> positivity) hpoint
  have hsumA : (∑' pk, A pk) ≤ 2 / (M : ℝ) := by
    rw [hA.tsum_prod]
    simp only [A, Q, tsum_mul_left, hasSum_geometric_two.tsum_eq]
    rw [tsum_mul_right]
    exact (mul_le_mul_of_nonneg_right (sonin_prime_inverseSquare_tail_le M hM)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have hsumB : (∑' pk, B pk) ≤ 2 * (1 / 2 : ℝ) ^ M := by
    rw [hB.tsum_prod]
    simp only [B, Q, tsum_mul_left, sonin_geometricHalf_tail, tsum_mul_right]
    exact (mul_le_mul_of_nonneg_right sonin_prime_inverseSquare_mass_le_one
      (by positivity : 0 ≤ 2 * (1 / 2 : ℝ) ^ M)).trans_eq (by ring)
  have hgeom : (1 / 2 : ℝ) ^ M ≤ (M : ℝ)⁻¹ := by
    have hp : (M : ℝ) ≤ (2 : ℝ) ^ M := by
      exact_mod_cast (Nat.lt_two_pow_self (n := M)).le
    simpa [one_div_pow] using one_div_le_one_div_of_le
      (Nat.cast_pos.mpr hM) hp
  calc
    _ ≤ ∑' pk, (A pk + B pk) := htail.tsum_le_tsum hpoint (hA.add hB)
    _ = (∑' pk, A pk) + ∑' pk, B pk := hA.tsum_add hB
    _ ≤ 4 / (M : ℝ) := by
      simp only [div_eq_mul_inv] at hsumA ⊢
      linarith

end
end RHTower

