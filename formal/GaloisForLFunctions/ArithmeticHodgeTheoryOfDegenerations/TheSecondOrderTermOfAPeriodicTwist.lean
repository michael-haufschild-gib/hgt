import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheSecondOrderTermIsDiagonalInTheRamanujanBasis

/-!
# The second-order term of a periodic twist
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Kuzmin–Landau on residue classes -/

/-- **Kuzmin–Landau with a real shift.** For `x₀ > 0`, `0 < τ ≤ π x₀` and `x₀ + k ≤ X`, the partial
sum `Σ_{m≤k} (x₀ + m)^{iτ}` has norm at most `3πX/τ + 1`. -/
theorem norm_partial_cpow_real_le {x₀ X : ℝ} (hx₀ : 0 < x₀) {k : ℕ} (hk : x₀ + k ≤ X) {τ : ℝ}
    (hτ : 0 < τ) (hτn : τ ≤ Real.pi * x₀) :
    ‖∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I)‖ ≤
      3 * Real.pi * X / τ + 1 := by
  have hX0 : 0 < X := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  set φ : ℕ → ℝ := fun m => m - τ * Real.log (x₀ + m) / (2 * Real.pi) with hφ
  have hterm : ∀ m : ℕ, Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    intro m
    have key : (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I) = (m : ℂ) * (2 * Real.pi * Complex.I) +
        (-(((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I)) := by
      simp only [hφ]; push_cast; field_simp; ring
    rw [key, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, one_mul, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, neg_neg]
  have hconj : ∑ m ∈ range (k + 1), Complex.exp (((τ * Real.log (x₀ + m) : ℝ) : ℂ) * Complex.I) =
      (starRingEnd ℂ) (∑ m ∈ range (k + 1),
        Complex.exp (((2 * Real.pi * φ m : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum]
    exact sum_congr rfl fun m _ => hterm m
  rw [hconj, RCLike.norm_conj]
  set δ := τ / (2 * Real.pi * X) with hδ
  have hδ0 : 0 < δ := by positivity
  have hdiff : ∀ m : ℕ, φ (m + 1) - φ m =
      1 - τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
    intro m
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    simp only [hφ]
    push_cast
    rw [Real.log_div (by linarith) h1.ne', show (x₀ + ((m : ℝ) + 1)) = (x₀ + m) + 1 by ring]
    field_simp
    ring
  have hlog_le : ∀ m : ℕ, Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) ≤ 1 / (x₀ + m) := by
    intro m
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have := Real.log_le_sub_one_of_pos (show 0 < ((x₀ + m : ℝ) + 1) / (x₀ + m) by positivity)
    rw [show ((x₀ + m : ℝ) + 1) / (x₀ + m) - 1 = 1 / (x₀ + m) by field_simp; ring] at this
    exact this
  refine (RHTower.Sieve.kuzminLandau_band φ k hδ0 (fun m hm => ?_) (fun m hm => ?_)
    (fun m hm => ?_)).trans ?_
  · rw [hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have hle := hlog_le m
    have : τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) ≤ 1 / 2 := by
      calc τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m))
          ≤ τ / (2 * Real.pi) * (1 / (x₀ + m)) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ ≤ τ / (2 * Real.pi) * (1 / x₀) := by
            gcongr
            linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
        _ ≤ 1 / 2 := by
            rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
            linarith
    have hδle : δ ≤ 1 / 2 := by
      rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
      have hxX : x₀ ≤ X := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
      have := mul_le_mul_of_nonneg_left hxX Real.pi_pos.le
      linarith
    linarith
  · rw [hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have hge := one_div_add_one_le_log h1
    have hmN : (x₀ + m : ℝ) + 1 ≤ X := by
      have : (m : ℝ) + 1 ≤ k := by
        have := Finset.mem_range.mp hm
        exact_mod_cast this
      linarith
    have : δ ≤ τ / (2 * Real.pi) * Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
      calc δ = τ / (2 * Real.pi) * (1 / X) := by rw [hδ]; field_simp
        _ ≤ τ / (2 * Real.pi) * (1 / ((x₀ + m : ℝ) + 1)) := by
            gcongr
        _ ≤ _ := mul_le_mul_of_nonneg_left hge (by positivity)
    linarith
  · rw [hdiff, hdiff]
    have h1 : (0 : ℝ) < x₀ + m := by positivity
    have h2 : Real.log (((x₀ + (m + 1 : ℕ) : ℝ) + 1) / (x₀ + (m + 1 : ℕ))) ≤
        Real.log (((x₀ + m : ℝ) + 1) / (x₀ + m)) := by
      push_cast
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by positivity) h1]
      ring_nf
      linarith
    have : 0 ≤ τ / (2 * Real.pi) := by positivity
    have := mul_le_mul_of_nonneg_left h2 this
    linarith
  · have : 3 / (2 * δ) = 3 * Real.pi * X / τ := by rw [hδ]; field_simp
    rw [this]

/-- **Kuzmin–Landau on a residue class.** For `0 < τ ≤ π n₀/M`, `n₀ + k ≤ N` and `s ≤ M`, the partial
sums of `n^{iτ}` over `n ∈ [n₀, n₀ + k]` with `M ∣ n + s` are at most `3πN/(Mτ) + 1`. -/
theorem norm_partial_shift_dvd_cpow_le {M : ℕ} (hM : 0 < M) {s : ℕ} (hs : s ≤ M) {n₀ N k : ℕ}
    (hn₀ : 1 ≤ n₀) (hk : n₀ + k ≤ N) {τ : ℝ} (hτ : 0 < τ) (hτn : τ ≤ Real.pi * n₀ / M) :
    ‖∑ m ∈ range (k + 1), (if M ∣ n₀ + m + s then
        Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0)‖ ≤
      3 * Real.pi * N / (M * τ) + 1 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set e : ℕ → ℂ := fun t => Complex.exp (((τ * Real.log ((t - s : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
    with he
  have hshift : ∑ m ∈ range (k + 1), (if M ∣ n₀ + m + s then
      Complex.exp (((τ * Real.log ((n₀ + m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) else 0) =
      ∑ m ∈ range (k + 1), (if M ∣ (n₀ + s) + m then e ((n₀ + s) + m) else 0) := by
    refine sum_congr rfl fun m _ => ?_
    rw [show n₀ + m + s = n₀ + s + m by ring]
    simp only [he]
    congr 2
    rw [show n₀ + s + m - s = n₀ + m by omega]
  rw [hshift, sum_range_dvd_eq M (n₀ + s) k hM (by omega) e]
  obtain ⟨a, ha⟩ : ∃ a, a = (n₀ + s - 1) / M := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (n₀ + s + k) / M := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have haM : n₀ + s ≤ (a + 1) * M := by
    have := Nat.lt_div_mul_add (a := n₀ + s - 1) hM
    rw [ha, add_mul, one_mul]
    omega
  have hbM : b * M ≤ n₀ + s + k := by rw [hb]; exact Nat.div_mul_le_self _ _
  rcases Nat.lt_or_ge a b with hab | hab
  · set x₀ : ℝ := ((a + 1 : ℕ) : ℝ) - s / M with hx₀
    have hx₀n : (n₀ : ℝ) / M ≤ x₀ := by
      rw [hx₀, div_le_iff₀ hM0, sub_mul, div_mul_cancel₀ _ hM0.ne']
      have : (n₀ : ℝ) + s ≤ ((a + 1 : ℕ) : ℝ) * M := by exact_mod_cast haM
      linarith
    have hx₀0 : 0 < x₀ := lt_of_lt_of_le (by
      have : (1 : ℝ) ≤ n₀ := by exact_mod_cast hn₀
      positivity) hx₀n
    have hreidx : ∑ c ∈ Finset.Ioc a b, e (M * c) = ∑ j ∈ range (b - (a + 1) + 1),
        Complex.exp (((τ * Real.log M : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((τ * Real.log (x₀ + j) : ℝ) : ℂ) * Complex.I) := by
      rw [show Finset.Ioc a b = Finset.Ico (a + 1) (b + 1) by
          ext x; simp only [Finset.mem_Ioc, Finset.mem_Ico]; omega, Finset.sum_Ico_eq_sum_range,
        show b + 1 - (a + 1) = b - (a + 1) + 1 by omega]
      refine sum_congr rfl fun j _ => ?_
      simp only [he]
      have hj0 : (0 : ℝ) < x₀ + j := by positivity
      rw [← Complex.exp_add]
      congr 1
      have hsub : ((M * (a + 1 + j) - s : ℕ) : ℝ) = (M : ℝ) * (x₀ + j) := by
        have hle : s ≤ M * (a + 1 + j) := le_trans hs (Nat.le_mul_of_pos_right M (by omega))
        rw [Nat.cast_sub hle, hx₀]
        push_cast
        field_simp
        ring
      rw [hsub, Real.log_mul hM0.ne' hj0.ne']
      push_cast
      ring
    rw [hreidx, ← mul_sum, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hτx : τ ≤ Real.pi * x₀ := by
      refine hτn.trans ?_
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hx₀n Real.pi_pos.le
    have hlast : x₀ + ((b - (a + 1) : ℕ) : ℝ) ≤ N / M := by
      rw [hx₀, Nat.cast_sub (by omega), le_div_iff₀ hM0]
      push_cast
      have : ((b : ℕ) : ℝ) * M ≤ (n₀ : ℝ) + s + k := by exact_mod_cast hbM
      have hNk : (n₀ : ℝ) + k ≤ N := by exact_mod_cast hk
      have : (((a : ℝ) + 1 - s / M + (b - (a + 1))) * M) = (b : ℝ) * M - s := by
        field_simp; ring
      rw [this]
      linarith
    have h := norm_partial_cpow_real_le hx₀0 hlast hτ hτx
    refine h.trans (le_of_eq ?_)
    field_simp
  · rw [Finset.Ioc_eq_empty (by omega), sum_empty, norm_zero]; positivity

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
