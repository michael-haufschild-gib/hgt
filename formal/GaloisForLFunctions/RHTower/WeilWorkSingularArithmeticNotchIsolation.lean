import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchRampSign

/-!
# Coefficient isolation with a summable composite tail

The ordinary harmonic sum controls the prime part of each notch tail.
Absolute summability is needed only on nonprime integers. Together with
the harmonic envelope, these two inputs isolate every coefficient.
-/

noncomputable section
open Finset Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa ZetaNotch SmoothNumbers WeilFiniteSupport WeilLogSummable

private theorem nonpos_of_notch_floor {P : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀)
    {ε : ℝ} {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N)
    {Y : ℝ} {T : ℕ}
    (hfloor : ∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * mainWeight P ε n₀ n) k) :
    Y ≤ 0 := by
  let a (n : ℕ) := v n * mainWeight P ε n₀ n
  let T' := max T 1
  let B := (∑ k ∈ range T', |rampPartial a k|) + |Y|
  have hsum : 0 ≤ ∑ k ∈ range T', |rampPartial a k| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hlow (k : ℕ) : -B ≤ rampPartial a k := by
    rcases lt_or_ge k T' with hk | hk
    · have h := Finset.single_le_sum (f := fun j => |rampPartial a j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.mpr hk)
      have := neg_abs_le (rampPartial a k)
      dsimp [B]
      linarith [abs_nonneg Y]
    · have h := hfloor k ((le_max_left T 1).trans hk)
      dsimp [B]
      linarith [neg_abs_le Y]
  obtain ⟨Dr, hDr, hm⟩ := exists_sum_re_weightedMoment_ge_ramp hP (K := 7) (by norm_num) ε hn₀
  obtain ⟨CQ, hCQ, hQb, hqb⟩ := exists_notchWeight_bound P ε n₀
  exact nonpos_of_rampPartial_ge_harmonic (differentiable_notchWeightC P ε n₀) hQb
    (notchWeightC_ofReal P ε n₀) (notchWeight_nonneg P ε n₀) (continuous_notchWeight P ε n₀) hqb
    (eulerProduct_pos hP) (by exact_mod_cast twistBound_pos hP n₀) hDr
    (fun hv N u hu => hm hv N hu) hv0 hA ha hs34 hs1 hPD hharm
    (le_max_right T 1) hlow (fun k hk => hfloor k ((le_max_left T 1).trans hk))

/-- The composite tail is the only absolute tail needed to isolate the notch
coefficients; the full harmonic series need only converge in its natural order. -/
theorem eq_zero_of_harmonic_small_of_nonprime_summable {v : ℕ → ℝ}
    (hv0 : v 0 = 0) (hv1 : v 1 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hs34 : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-(3 / 4 : ℝ)))
    (hs1 : Summable fun n : ℕ => |v n| * (n : ℝ)⁻¹)
    (hPD : PositiveDefiniteOnReal fun y => ((-WeilRegular.nullPotential v y : ℝ) : ℂ))
    (hharm : ∀ η : ℝ, 0 < η → ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |sqrtScaled v n| / n) ≤ B + η * Real.log N)
    (hcomp : Summable fun n : ℕ => if n.Prime then 0 else |v n| * (Real.sqrt n)⁻¹)
    {L : ℝ} (hconv : Tendsto (fun N : ℕ =>
      ∑ n ∈ range (N + 1), v n * (Real.sqrt n)⁻¹) atTop (𝓝 L)) : v = 0 := by
  let c (n : ℕ) := if n.Prime then 0 else |v n| * (Real.sqrt n)⁻¹
  have hc0 (n : ℕ) : 0 ≤ c n := by dsimp [c]; split_ifs <;> positivity
  let tail (y : ℕ) := ∑' i : ℕ, c (i + (y + 1))
  have htail : Tendsto tail atTop (𝓝 0) :=
    (tendsto_sum_nat_add c).comp (tendsto_add_atTop_nat 1)
  have htail_bound (y M : ℕ) : ∑ n ∈ Ico (y + 1) (M + 1), c n ≤ tail y := by
    have hs : Summable fun i : ℕ => c (i + (y + 1)) :=
      (summable_nat_add_iff (y + 1)).mpr hcomp
    rw [Finset.sum_Ico_eq_sum_range]
    have he : ∑ k ∈ range (M + 1 - (y + 1)), c (y + 1 + k) =
        ∑ k ∈ range (M + 1 - (y + 1)), c (k + (y + 1)) :=
      Finset.sum_congr rfl fun _ _ => by rw [add_comm]
    rw [he]
    exact hs.sum_le_tsum _ fun _ _ => hc0 _
  funext n₀
  rw [Pi.zero_apply]
  rcases Nat.lt_or_ge n₀ 2 with hn | hn₀
  · interval_cases n₀
    · exact hv0
    · exact hv1
  have key (δ : ℝ) (hδ : 0 < δ) : |v n₀| ≤ (4 + Real.sqrt n₀) * δ := by
    obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp hconv (δ / 2) (by positivity)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (htail.eventually_le_const hδ)
    let y := n₀ + N₀ + N₁
    have hcau (M : ℕ) (hM : y ≤ M) :
        |∑ n ∈ Ico (y + 1) (M + 1), v n * (Real.sqrt n)⁻¹| ≤ δ := by
      rw [Finset.sum_Ico_eq_sub _ (by omega)]
      have h1 := hN₀ M (by dsimp [y] at hM; omega)
      have h2 := hN₀ y (by dsimp [y]; omega)
      rw [Real.dist_eq] at h1 h2
      have := abs_sub_le (∑ n ∈ range (M + 1), v n * (Real.sqrt n)⁻¹) L
        (∑ n ∈ range (y + 1), v n * (Real.sqrt n)⁻¹)
      rw [abs_sub_comm L] at this
      linarith
    have hsign (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
        ε * v n₀ ≤ (4 + Real.sqrt n₀) * δ := by
      let P := primesUpTo y
      have hy : n₀ ≤ y := by dsimp [y]; omega
      have hn₀s : IsSmoothOver P n₀ := isSmoothOver_primesUpTo hn₀ hy
      let a (n : ℕ) := v n * mainWeight P ε n₀ n
      have herr (M : ℕ) (hM : y ≤ M) :
          |rampPartial a M - ε * v n₀ -
            2 * ∑ n ∈ Ico (y + 1) (M + 1), v n * (Real.sqrt n)⁻¹| ≤
            (2 + Real.sqrt n₀) * δ := by
        have hsplit : rampPartial a M = ε * v n₀ + ∑ n ∈ Ico (y + 1) (M + 1), a n := by
          rw [rampPartial, ← Finset.sum_range_add_sum_Ico _ (by omega : y + 1 ≤ M + 1)]
          congr 1
          exact sum_range_mainWeight_low hn₀ hy hv0 hv1 ε
        rw [hsplit, add_sub_cancel_left, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ n ∈ Ico (y + 1) (M + 1), |a n - 2 * (v n * (Real.sqrt n)⁻¹)|
            ≤ ∑ n ∈ Ico (y + 1) (M + 1), (2 + Real.sqrt n₀) * c n := by
              refine Finset.sum_le_sum fun n hn => ?_
              have hyn : y < n := by have := (Finset.mem_Ico.mp hn).1; omega
              have h := abs_mainWeight_high_sub_le hn₀ hy hyn hε v
              simpa only [a, P, c, mul_ite, mul_zero, mul_one] using h
          _ = (2 + Real.sqrt n₀) * ∑ n ∈ Ico (y + 1) (M + 1), c n := by rw [Finset.mul_sum]
          _ ≤ (2 + Real.sqrt n₀) * δ := mul_le_mul_of_nonneg_left
            ((htail_bound y M).trans (hN₁ y (by dsimp [y]; omega))) (by positivity)
      have hfloor (M : ℕ) (hM : y ≤ M) :
          ε * v n₀ - (4 + Real.sqrt n₀) * δ ≤ rampPartial a M := by
        have h1 := abs_le.mp (herr M hM)
        have h2 := abs_le.mp (hcau M hM)
        linarith
      have h := nonpos_of_notch_floor prime_of_mem_primesUpTo hn₀s hv0 hA ha
        hs34 hs1 hPD hharm hfloor
      linarith
    have hp := hsign 1 (Or.inl rfl)
    have hn := hsign (-1) (Or.inr rfl)
    rw [abs_le]
    constructor <;> linarith
  by_contra hne
  have hpos : 0 < |v n₀| := abs_pos.mpr hne
  have h := key (|v n₀| / (2 * (4 + Real.sqrt n₀))) (by positivity)
  have he : (4 + Real.sqrt n₀) * (|v n₀| / (2 * (4 + Real.sqrt n₀))) = |v n₀| / 2 := by
    field_simp
  rw [he] at h
  linarith

end RHTower.WeilSingularArithmetic
