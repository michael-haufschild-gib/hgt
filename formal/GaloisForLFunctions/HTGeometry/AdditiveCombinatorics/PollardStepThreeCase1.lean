import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseThreeOne
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardStepThreePoly
import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardDysonEnergy

/-!
# CASE 3.1 of Grynkiewicz's STEP 3

At `t = 2` the maximal Dyson small part is a single point.  The four combinatorial consequences of
that — the unique-expression count, `T · B = A`, the Sidon property of `B`, and the resulting
upper bound on `#T` — combine with the additive-energy lower bound at `t = k = 1` into a quartic
inequality in `#B` that has no solution with `#B ≥ 3`.  The main result is `case31_false`.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

theorem two_mul_choose_two (m : ℕ) : 2 * (m + 1).choose 2 = m * (m + 1) := by
  induction m with
  | zero => rfl
  | succ k ih =>
    have h : (k + 1 + 1).choose 2 = (k + 1) + (k + 1).choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    rw [h, Nat.mul_add, ih]
    ring

/-- **The terminal inequality of CASE 3.1.**  The two upper bounds on `#(A · B)` and on the number
of full translations are incompatible with the additive-energy lower bound.  The proof is the
identity
`2nX + (m−1)XY − 4n²m = −2(m−3)(m²−3m+1)(n−m) + (−5m⁴+26m³−50m²+40m−15)`
for `X = 2n+3m−5` and `Y = 2n+2m−m²−3`, whose two summands are respectively `≤ 0` and `< 0`. -/
theorem case31_final {n m P S : ℝ} (hm : 3 ≤ m) (hnm : m ≤ n)
    (hP : 0 ≤ P) (hS : 0 ≤ S)
    (h2P : 2 * P ≤ 2 * n + 3 * m - 5)
    (h2S : 2 * S ≤ 2 * n + 2 * m - m ^ 2 - 3)
    (hkey : n ^ 2 * m ≤ P * (n + S * (m - 1))) : False := by
  have hX : (0 : ℝ) ≤ 2 * n + 3 * m - 5 := le_trans (by linarith) h2P
  have hY : (0 : ℝ) ≤ 2 * n + 2 * m - m ^ 2 - 3 := le_trans (by linarith) h2S
  have hm1 : (0 : ℝ) ≤ m - 1 := by linarith
  have hPS : 4 * (P * S) ≤ (2 * n + 3 * m - 5) * (2 * n + 2 * m - m ^ 2 - 3) := by nlinarith
  have hFp : 4 * (n ^ 2 * m)
      ≤ 2 * n * (2 * n + 3 * m - 5)
        + (m - 1) * ((2 * n + 3 * m - 5) * (2 * n + 2 * m - m ^ 2 - 3)) := by
    nlinarith [hkey, hPS, hm1, h2P]
  have hstep : (0 : ℝ)
      ≤ -2 * ((m - 3) * (m ^ 2 - 3 * m + 1) * (n - m))
        + (-5 * m ^ 4 + 26 * m ^ 3 - 50 * m ^ 2 + 40 * m - 15) := by linarith [hFp]
  have hquad : (0 : ℝ) ≤ m ^ 2 - 3 * m + 1 := by nlinarith
  have hprod : (0 : ℝ) ≤ (m - 3) * (m ^ 2 - 3 * m + 1) * (n - m) :=
    mul_nonneg (mul_nonneg (by linarith) hquad) (by linarith)
  have hq := case31_poly hm
  linarith [hstep, hprod, hq]

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

theorem repSum_one (A B : Finset G) : repSum A B 1 = (A * B).card := by
  rw [repSum]
  simp [repSet_one]

theorem repSum_two (A B : Finset G) :
    repSum A B 2 = (A * B).card + (repSet A B 2).card := by
  rw [repSum, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, repSet_one]

/-- **CASE 3.1 of Grynkiewicz's STEP 3 is impossible.**  For `t = 2`, if the maximal Dyson small
part is a single point, `A` has trivial stabiliser, no element of `A` or of `B` admits two
unique-expression products, and `A · B` is not entirely `2`-representable, then the weak Pollard
bound `#(A ·_1 B) + #(A ·_2 B) ≥ 2#A + 2#B − 4` must hold. -/
theorem case31_false {A B : Finset G} {x₀ : G}
    (hA : A.Nonempty) (hB3 : 3 ≤ B.card) (hBA : B.card ≤ A.card)
    (hx0 : (dysonSmall A B x₀).Nonempty)
    (hk : (dysonSmall A B x₀).card + 1 ≤ 2)
    (hmax : ∀ z : G, (dysonSmall A B z).Nonempty → (dysonSmall A B z).card < B.card →
        (dysonSmall A B z).card ≤ (dysonSmall A B x₀).card)
    (hstab : (mulStab A).card ≤ 1)
    (hueA : ∀ a ∈ A, (B.filter (fun b => rep A B (a * b) = 1)).card ≤ 1)
    (hueB : ∀ b ∈ B, (A.filter (fun a => rep A B (a * b) = 1)).card ≤ 1)
    (hAB2 : A * B ≠ repSet A B 2)
    (hweakfail : repSum A B 2 + 5 ≤ 2 * A.card + 2 * B.card) :
    False := by
  classical
  have hBne : B.Nonempty := Finset.card_pos.1 (by omega)
  have hcard1 : (dysonSmall A B x₀).card = 1 := by
    have := Finset.card_pos.2 hx0
    omega
  have h1 : (A * B).card ≤ (repSet A B 2).card + B.card :=
    le_trans (card_mul_le_card_repSet_two_add A B)
      (Nat.add_le_add_left (card_uniqueExpr_le_of_right hueB) _)
  have hsum2 := repSum_two A B
  have h2P : 2 * (A * B).card + 5 ≤ 2 * A.card + 3 * B.card := by omega
  have hTB : dysonFull A B * B = A :=
    dysonFull_mul_eq_of_uniqueExpr hk hmax (by omega) hueA
  have hTne : (dysonFull A B).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (dysonFull A B) with h | h
    · rw [h, Finset.empty_mul] at hTB
      exact absurd hTB.symm (Finset.nonempty_iff_ne_empty.1 hA)
    · exact h
  have hW : (B.card + 1).choose 2 ≤ (B * B).card :=
    card_choose_le_card_mul_self (sidon_of_dysonFull_mul_eq hk hmax hTB hstab)
  have hW2 : B.card * B.card + B.card ≤ 2 * (B * B).card := by
    have h := two_mul_choose_two B.card
    rw [Nat.mul_add, Nat.mul_one] at h
    omega
  have hTW : (dysonFull A B).card + (B * B).card ≤ (A * B).card + 1 :=
    card_dysonFull_add_card_mul_self_le hTne hBne hTB hAB2
  have h2S : 2 * (dysonFull A B).card + B.card * B.card + 3 ≤ 2 * A.card + 2 * B.card := by
    omega
  -- the additive-energy lower bound, with `t = k = 1`
  have hmin := repSum_ge_min_dyson (t := 1) le_rfl hA hBne (by omega) (by omega) hmax
  rw [hcard1, repSum_one] at hmin
  have hm3 : (3 : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hB3
  have hnm : (B.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast hBA
  have hP2 : 2 * ((A * B).card : ℝ) ≤ 2 * (A.card : ℝ) + 3 * (B.card : ℝ) - 5 := by
    have : ((2 * (A * B).card + 5 : ℕ) : ℝ) ≤ ((2 * A.card + 3 * B.card : ℕ) : ℝ) := by
      exact_mod_cast h2P
    push_cast at this
    linarith
  have hS2 : 2 * ((dysonFull A B).card : ℝ)
      ≤ 2 * (A.card : ℝ) + 2 * (B.card : ℝ) - (B.card : ℝ) ^ 2 - 3 := by
    have : ((2 * (dysonFull A B).card + B.card * B.card + 3 : ℕ) : ℝ)
        ≤ ((2 * A.card + 2 * B.card : ℕ) : ℝ) := by exact_mod_cast h2S
    push_cast at this
    nlinarith [this]
  rcases min_le_iff.1 hmin with hcase | hcase
  · simp only [Nat.cast_one, one_mul, sub_self, mul_zero, Real.sqrt_zero, add_zero,
      div_one] at hcase
    nlinarith [hcase, hP2, hm3, hnm]
  · simp only [Nat.cast_one, one_mul] at hcase
    have hden : (0 : ℝ) < (A.card : ℝ) + ((dysonFull A B).card : ℝ) * ((B.card : ℝ) - 1) := by
      have h0 : (0 : ℝ) ≤ ((dysonFull A B).card : ℝ) := Nat.cast_nonneg _
      nlinarith [hm3, hnm, h0]
    rw [div_le_iff₀ hden] at hcase
    exact case31_final hm3 hnm (Nat.cast_nonneg _) (Nat.cast_nonneg _) hP2 hS2 (by nlinarith [hcase])

end GaloisForLFunctions.HTGeometry.AddComb
