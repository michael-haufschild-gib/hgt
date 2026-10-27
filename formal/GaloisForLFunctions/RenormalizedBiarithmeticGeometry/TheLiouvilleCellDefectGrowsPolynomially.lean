import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheCellHolonomyDefectCountsChargedCells

/-!
# The Liouville cell defect grows polynomially

At the Liouville gauge the charged cells of the dyadic cell dilation are the `a` with
`λ(a) = λ(2a + 1)`.

* **Charged cells are even sign changes** (`mem_liouvilleAgreements_iff`). Since `λ(2a) = −λ(a)`,
  the cell `a` is charged iff `λ(2a) ≠ λ(2a + 1)`.
* **Sign changes give charged cells** (`mem_liouvilleAgreements_of_sign_change`). If
  `λ(u) ≠ λ(u + 1)` then `a = 2u(u + 1)` is charged: `2a + 1 = (2u + 1)²` has `λ = 1`, and
  `λ(a) = λ(2)λ(u)λ(u + 1) = 1`.
* **Squares and twice-squares** (`exists_sign_change_below_twice_square`). `λ(k²) = 1` and
  `λ(2j²) = −1`, so `λ` changes sign between `⌊√(2j²)⌋²` and `2j²`; these windows are disjoint
  (`twice_sq_lt_sqrt_sq`).
* **Fourth-root growth** (`card_liouvilleAgreements_ge`, `hsDefect_liouville_ge`). At least `J`
  cells below `8J⁴` are charged, so the covariance defect of the dyadic cell dilation at the
  Liouville gauge is at least `2J` on the horizon `[1, 8J⁴]`, for every scalar.

Linear growth is the positive lower density of the sign changes `λ(2a) ≠ λ(2a + 1)`, a two-point
correlation of `λ` along `(+1, ×2)`.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedBiarithmeticGeometry

open BiarithmeticGaugeGeometry

/-- The Liouville sign `λ(n)` as a real character. -/
abbrev lam (n : ℕ) : ℝ := realSignChar PrimeGauge.liouvilleGauge n

theorem lam_hω : IsRealSignGauge PrimeGauge.liouvilleGauge :=
  fun hp => isRealSignGauge_liouville hp

theorem lam_mul (m n : ℕ) : lam (m * n) = lam m * lam n := realSignChar_mul lam_hω m n

theorem lam_two : lam 2 = -1 := realSignChar_liouville_prime Nat.prime_two

theorem lam_sq_eq_one {n : ℕ} (hn : n ≠ 0) : lam n * lam n = 1 := by
  rw [← sq]; exact realSignChar_sq_eq_one lam_hω hn

theorem lam_eq_one_or {n : ℕ} (hn : n ≠ 0) : lam n = 1 ∨ lam n = -1 :=
  realSignChar_eq_one_or lam_hω hn

/-- **Charged cells are even sign changes.** -/
theorem mem_liouvilleAgreements_iff {a X : ℕ} :
    a ∈ liouvilleAgreements X ↔ (1 ≤ a ∧ a ≤ X) ∧ lam (2 * a) ≠ lam (2 * a + 1) := by
  simp only [liouvilleAgreements, mem_filter, mem_Icc]
  refine and_congr_right fun ha => ?_
  change lam a * lam (2 * a + 1) = 1 ↔ _
  rw [lam_mul, lam_two]
  rcases lam_eq_one_or (show a ≠ 0 by omega) with h | h <;>
    rcases lam_eq_one_or (show 2 * a + 1 ≠ 0 by omega) with h' | h' <;>
      rw [h, h'] <;> norm_num

/-- **Sign changes give charged cells.** -/
theorem mem_liouvilleAgreements_of_sign_change {u X : ℕ} (hu : 1 ≤ u) (hX : 2 * u * (u + 1) ≤ X)
    (hch : lam u ≠ lam (u + 1)) : 2 * u * (u + 1) ∈ liouvilleAgreements X := by
  have hprod : lam u * lam (u + 1) = -1 := by
    rcases lam_eq_one_or (show u ≠ 0 by omega) with h | h <;>
      rcases lam_eq_one_or (show u + 1 ≠ 0 by omega) with h' | h' <;>
        simp_all
  simp only [liouvilleAgreements, mem_filter, mem_Icc]
  refine ⟨⟨by nlinarith, hX⟩, ?_⟩
  have ha : lam (2 * u * (u + 1)) = 1 := by
    rw [lam_mul, lam_mul, lam_two, mul_assoc, hprod]; norm_num
  have hsq : 2 * (2 * u * (u + 1)) + 1 = (2 * u + 1) * (2 * u + 1) := by ring
  have hb : lam (2 * (2 * u * (u + 1)) + 1) = 1 := by
    rw [hsq, lam_mul, lam_sq_eq_one (by omega)]
  change lam (2 * u * (u + 1)) * lam (2 * (2 * u * (u + 1)) + 1) = 1
  rw [ha, hb, one_mul]

/-- A sequence that differs at `A ≤ B` changes between consecutive points of `[A, B]`. -/
theorem exists_consecutive_ne {f : ℕ → ℝ} {A B : ℕ} (hAB : A ≤ B) (h : f A ≠ f B) :
    ∃ u, A ≤ u ∧ u < B ∧ f u ≠ f (u + 1) := by
  induction B, hAB using Nat.le_induction with
  | base => exact absurd rfl h
  | succ B hAB ih =>
    by_cases hB : f A = f B
    · exact ⟨B, hAB, Nat.lt_succ_self B, fun h' => h (hB.trans h')⟩
    · obtain ⟨u, h1, h2, h3⟩ := ih hB
      exact ⟨u, h1, by omega, h3⟩

/-- **Squares and twice-squares**: `λ` changes sign between `⌊√(2j²)⌋²` and `2j²`. -/
theorem exists_sign_change_below_twice_square {j : ℕ} (hj : 1 ≤ j) :
    ∃ u, Nat.sqrt (2 * j ^ 2) ^ 2 ≤ u ∧ u < 2 * j ^ 2 ∧ lam u ≠ lam (u + 1) := by
  have hk : Nat.sqrt (2 * j ^ 2) ≠ 0 :=
    (Nat.sqrt_pos.mpr (by positivity)).ne'
  refine exists_consecutive_ne (Nat.sqrt_le' _) ?_
  rw [sq, lam_mul, lam_sq_eq_one hk, lam_mul, sq, lam_mul, lam_sq_eq_one (by omega), lam_two]
  norm_num

/-- The square below `2(j + 1)²` exceeds `2j²`, so the windows are disjoint. -/
theorem twice_sq_lt_sqrt_sq (j : ℕ) : 2 * j ^ 2 < Nat.sqrt (2 * (j + 1) ^ 2) ^ 2 := by
  set k := Nat.sqrt (2 * (j + 1) ^ 2)
  have hk : 2 * (j + 1) ^ 2 < (k + 1) ^ 2 := Nat.lt_succ_sqrt' _
  by_contra h
  rw [not_lt] at h
  have h1 : 4 * j + 1 < 2 * k := by nlinarith
  have h2 : 2 * j + 1 ≤ k := by omega
  nlinarith

/-- **At least `J` charged cells below `8J⁴`.** -/
theorem card_liouvilleAgreements_ge (J : ℕ) : J ≤ (liouvilleAgreements (8 * J ^ 4)).card := by
  choose u hu1 hu2 hu3 using fun j : ℕ =>
    exists_sign_change_below_twice_square (j := j + 1) (by omega)
  -- The change points `u_j` are strictly increasing, and so are the cells `2u_j(u_j + 1)`.
  have hmono : StrictMono u := strictMono_nat_of_lt_succ fun j =>
    calc u j < 2 * (j + 1) ^ 2 := hu2 j
      _ < Nat.sqrt (2 * (j + 1 + 1) ^ 2) ^ 2 := twice_sq_lt_sqrt_sq (j + 1)
      _ ≤ u (j + 1) := hu1 (j + 1)
  have hcell : StrictMono fun j => 2 * u j * (u j + 1) := fun i j hij => by
    have := hmono hij
    exact Nat.mul_lt_mul'' (Nat.mul_lt_mul_of_pos_left this (by norm_num)) (by omega)
  have hpos : ∀ j, 1 ≤ u j := fun j =>
    lt_of_le_of_lt (Nat.zero_le _) (lt_of_lt_of_le (twice_sq_lt_sqrt_sq j) (hu1 j))
  have hmaps : ∀ j ∈ range J, 2 * u j * (u j + 1) ∈ liouvilleAgreements (8 * J ^ 4) := by
    intro j hj
    have hjJ : j + 1 ≤ J := mem_range.mp hj
    have h1 : u j + 1 ≤ 2 * J ^ 2 := by
      have := hu2 j
      have : 2 * (j + 1) ^ 2 ≤ 2 * J ^ 2 := by gcongr
      omega
    refine mem_liouvilleAgreements_of_sign_change (hpos j) ?_ (hu3 j)
    calc 2 * u j * (u j + 1) ≤ 2 * (2 * J ^ 2) * (2 * J ^ 2) := by gcongr; omega
      _ = 8 * J ^ 4 := by ring
  calc J = ((range J).image fun j => 2 * u j * (u j + 1)).card := by
        rw [card_image_of_injective _ hcell.injective, card_range]
    _ ≤ (liouvilleAgreements (8 * J ^ 4)).card :=
        card_le_card fun a ha => by
          obtain ⟨j, hj, rfl⟩ := mem_image.mp ha
          exact hmaps j hj

/-- **The Liouville cell defect grows like a fourth root**: on the horizon `[1, 8J⁴]` the
covariance defect of the dyadic cell dilation at the Liouville gauge is at least `2J` for every
scalar. -/
theorem hsDefect_liouville_ge (J : ℕ) (c : ℝ) :
    2 * (J : ℝ) ≤ hsDefect PrimeGauge.liouvilleGauge (8 * J ^ 4) c := by
  have h := (hsDefect_liouville_sandwich (8 * J ^ 4)).1 c
  have hJ : (J : ℝ) ≤ (liouvilleAgreements (8 * J ^ 4)).card := by
    exact_mod_cast card_liouvilleAgreements_ge J
  linarith

end GaloisForLFunctions.RenormalizedBiarithmeticGeometry
