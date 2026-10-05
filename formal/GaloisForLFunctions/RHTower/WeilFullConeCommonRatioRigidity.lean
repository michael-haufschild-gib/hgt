import GaloisForLFunctions.RHTower.WeilAbscissaRigidity

/-!
# Weil-cone rigidity on finite unions of common-ratio geometric progressions

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_commonRatio`).  Let `b ≥ 2` and let `C` be a
finite set of natural numbers.  If `lam` is full-cone Weil-positive for the archimedean datum of `ζ`
and `lam(n) = Λ(n)` for every `n ≥ 2` outside `S = ⋃_{c ∈ C} {c b^j : j ≥ 0}`, then `lam = Λ`.

The cosets may be arbitrarily close (e.g. `{1000·2^j} ∪ {1001·2^j}`, logarithmic gap `≈ 10⁻³`,
`eq_vonMangoldt_of_weilPositiveFull_of_thousand`), and the deviation on `S` is arbitrary.

**Proof.** `S` is a finite union of geometric progressions, so `Σ_{n ∈ S} n^{−1/4}` is a finite sum
of geometric series (`summable_commonRatioSet_rpow`), and the abscissa rigidity of the Weil cone for
sparse supports (`WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow`, exponent `τ < 1/2`)
applies.
-/

open Classical

noncomputable section

namespace RHTower.WeilCommonRatio

/-- `n` lies in one of the cosets `c·b^ℕ`, `c ∈ C`. -/
def commonRatioSet (b : ℕ) (C : Finset ℕ) (n : ℕ) : Prop := ∃ c ∈ C, ∃ j : ℕ, n = c * b ^ j

/-- The weight `n^{−1/4}` on the single coset `c·b^ℕ`. -/
def cosetWeight (b c n : ℕ) : ℝ := if ∃ j : ℕ, n = c * b ^ j then (n : ℝ) ^ (-(1 / 4 : ℝ)) else 0

theorem cosetWeight_nonneg (b c n : ℕ) : 0 ≤ cosetWeight b c n := by
  unfold cosetWeight
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact le_rfl

/-- A single coset carries a convergent geometric series. -/
theorem summable_cosetWeight {b : ℕ} (hb : 2 ≤ b) (c : ℕ) : Summable (cosetWeight b c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have h0 : cosetWeight b 0 = fun _ => 0 := by
      funext n
      unfold cosetWeight
      split_ifs with h
      · obtain ⟨j, rfl⟩ := h
        simp
      · rfl
    rw [h0]
    exact summable_zero
  · set g : ℕ → ℕ := fun j => c * b ^ j with hg
    have hb1 : 1 < b := by omega
    have hginj : Function.Injective g := by
      intro i j hij
      simp only [hg] at hij
      exact Nat.pow_right_injective hb (Nat.eq_of_mul_eq_mul_left hc hij)
    have hzero : ∀ n ∉ Set.range g, cosetWeight b c n = 0 := by
      intro n hn
      unfold cosetWeight
      rw [if_neg]
      rintro ⟨j, rfl⟩
      exact hn ⟨j, rfl⟩
    refine (hginj.summable_iff hzero).mp ?_
    have hr0 : (0 : ℝ) ≤ (b : ℝ) ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg b) _
    have hr1 : (b : ℝ) ^ (-(1 / 4 : ℝ)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hb1) (by norm_num)
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left ((c : ℝ) ^ (-(1 / 4 : ℝ)))).congr
      fun j => ?_
    simp only [Function.comp, hg, cosetWeight]
    rw [if_pos ⟨j, rfl⟩]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg c) (pow_nonneg (Nat.cast_nonneg b) j),
      ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg b),
      ← Real.rpow_mul (Nat.cast_nonneg b), mul_comm (j : ℝ)]

/-- **Summability on a finite union of common-ratio progressions.** -/
theorem summable_commonRatioSet_rpow {b : ℕ} (hb : 2 ≤ b) (C : Finset ℕ) :
    Summable fun n : ℕ => if commonRatioSet b C n then (n : ℝ) ^ (-(1 / 4 : ℝ)) else 0 := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (summable_sum (s := C) fun c _ => summable_cosetWeight hb c)
  · split_ifs
    · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
    · exact le_rfl
  · split_ifs with h
    · obtain ⟨c, hc, hj⟩ := h
      have hval : cosetWeight b c n = (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
        unfold cosetWeight; rw [if_pos hj]
      rw [← hval]
      exact Finset.single_le_sum (fun c' _ => cosetWeight_nonneg b c' n) hc
    · exact Finset.sum_nonneg fun c' _ => cosetWeight_nonneg b c' n

/-- **Weil-cone rigidity on every finite union of common-ratio geometric progressions.**  A full-cone
Weil-positive `lam` that agrees with `Λ` off `⋃_{c ∈ C} c·b^ℕ` (`b ≥ 2`) equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_commonRatio {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {b : ℕ} (hb : 2 ≤ b) (C : Finset ℕ)
    (hoff : ∀ n, 2 ≤ n → ¬ commonRatioSet b C n → lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n :=
  RHTower.WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow hW (τ := 1 / 4)
    (by norm_num) (summable_commonRatioSet_rpow hb C) hoff

/-- **Instance at logarithmic gap `log(1001/1000)`.**  A full-cone Weil-positive `lam` with
`lam(n) = Λ(n)` off `{1000·2^j} ∪ {1001·2^j}` equals `Λ`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_thousand {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hoff : ∀ n, 2 ≤ n → (¬ ∃ j : ℕ, n = 1000 * 2 ^ j) → (¬ ∃ j : ℕ, n = 1001 * 2 ^ j) →
      lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  refine eq_vonMangoldt_of_weilPositiveFull_of_commonRatio hW (b := 2) le_rfl {1000, 1001}
    fun n hn hS => hoff n hn (fun h => hS ?_) (fun h => hS ?_)
  · exact ⟨1000, by simp, h⟩
  · exact ⟨1001, by simp, h⟩

end RHTower.WeilCommonRatio
