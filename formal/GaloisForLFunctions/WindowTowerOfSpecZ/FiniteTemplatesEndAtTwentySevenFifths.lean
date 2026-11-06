import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite rational Hecke templates end at spread `27/5`

A template is a set of rationals in `[1, X)`, closed under the ratio-two, ratio-three and ratio-five
neighbours inside `[1, X)`. Ratios two and three alone produce an infinite orbit from `X = 6`. With
ratio five the threshold drops to `X = 27/5` (`no_finite_hecke_template_at_twentySeven_fifths`).

On `[1, 27/25)` take the moves `q ↦ 81q/80` for `q < 16/15` and `q ↦ 15q/16` for `q ≥ 16/15`. They
preserve the interval, each one is a path of allowed edges inside `[1, 27/5)`, and each one lowers
the two-adic valuation by `4`. So no finite set is closed.

The two moves are the end of the subtractive Euclid algorithm on `(log 2, log 3, log 5)`: the ratios
`3/2, 4/3, 9/8, 10/9` appear in turn, the window shrinks from `X` to `X/5`, and the generators become
`81/80, 16/15, 10/9`. Two generators suffice once their sum fits in the window: `(81/80)(16/15) = 27/25`.
-/

namespace GaloisForLFunctions.WindowTowerOfSpecZ

/-- A set of rationals closed under the ratio-two, three and five neighbours in `[1, X)`. -/
def HeckeClosed (X : ℚ) (T : Finset ℚ) : Prop :=
  ∀ q ∈ T, ∀ s : ℚ, 1 ≤ s → s < X →
    s = 2 * q ∨ q = 2 * s ∨ s = 3 * q ∨ q = 3 * s ∨ s = 5 * q ∨ q = 5 * s → s ∈ T

/-- The move on `[1, 27/25)`. -/
def heckeFifthStep (q : ℚ) : ℚ := if q < 16 / 15 then 81 * q / 80 else 15 * q / 16

theorem heckeFifthStep_bounds {q : ℚ} (h1 : 1 ≤ q) (h2 : q < 27 / 25) :
    1 ≤ heckeFifthStep q ∧ heckeFifthStep q < 27 / 25 := by
  unfold heckeFifthStep
  split_ifs with h
  · constructor <;> linarith only [h1, h]
  · constructor <;> linarith only [h2, not_lt.1 h]

/-- The move is a path of allowed edges. -/
theorem heckeFifthStep_mem {X : ℚ} (hX : 27 / 5 ≤ X) {T : Finset ℚ} (hT : HeckeClosed X T) {q : ℚ}
    (hq : q ∈ T) (h1 : 1 ≤ q) (h2 : q < 27 / 25) : heckeFifthStep q ∈ T := by
  unfold heckeFifthStep
  split_ifs with h
  · have s1 : 3 * q ∈ T := hT q hq _ (by linarith only [h1]) (by linarith only [h, hX])
      (by simp only [true_or, or_true])
    have s2 : 3 * q / 2 ∈ T := hT _ s1 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inl (by ring)))
    have s3 : 9 * q / 2 ∈ T := hT _ s2 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inr (Or.inl (by ring))))
    have s4 : 9 * q / 4 ∈ T := hT _ s3 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inl (by ring)))
    have s5 : 9 * q / 8 ∈ T := hT _ s4 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inl (by ring)))
    have s6 : 27 * q / 8 ∈ T := hT _ s5 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inr (Or.inl (by ring))))
    have s7 : 27 * q / 16 ∈ T := hT _ s6 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inl (by ring)))
    have s8 : 81 * q / 16 ∈ T := hT _ s7 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inr (Or.inl (by ring))))
    exact hT _ s8 _ (by linarith only [h1]) (by linarith only [h, hX])
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by ring))))))
  · have h' := not_lt.1 h
    have s1 : 5 * q ∈ T := hT q hq _ (by linarith only [h1]) (by linarith only [h2, hX])
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have s2 : 5 * q / 2 ∈ T := hT _ s1 _ (by linarith only [h1]) (by linarith only [h2, hX])
      (Or.inr (Or.inl (by ring)))
    have s3 : 5 * q / 4 ∈ T := hT _ s2 _ (by linarith only [h1]) (by linarith only [h2, hX])
      (Or.inr (Or.inl (by ring)))
    have s4 : 15 * q / 4 ∈ T := hT _ s3 _ (by linarith only [h1]) (by linarith only [h2, hX])
      (Or.inr (Or.inr (Or.inl (by ring))))
    have s5 : 15 * q / 8 ∈ T := hT _ s4 _ (by linarith only [h']) (by linarith only [h2, hX])
      (Or.inr (Or.inl (by ring)))
    exact hT _ s5 _ (by linarith only [h']) (by linarith only [h2, hX])
      (Or.inr (Or.inl (by ring)))

/-- Each move lowers the two-adic valuation by `4`. -/
theorem padicValRat_heckeFifthStep {q : ℚ} (h1 : 1 ≤ q) :
    padicValRat 2 (heckeFifthStep q) = padicValRat 2 q - 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq0 : q ≠ 0 := by
    intro h
    rw [h] at h1
    norm_num at h1
  have h16 : padicValRat 2 (16 : ℚ) = 4 := by
    have htwo : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by norm_num)
    have h := padicValRat.pow (p := 2) (q := 2) (k := 4)
    rw [htwo] at h
    norm_num at h
    exact h
  have hodd (n : ℕ) (hn : ¬2 ∣ n) : padicValRat 2 (n : ℚ) = 0 := by
    rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hn]
    rfl
  have h81 : padicValRat 2 (81 / 5 : ℚ) = 0 := by
    rw [padicValRat.div (by norm_num) (by norm_num)]
    have h1 := hodd 81 (by norm_num)
    have h2 := hodd 5 (by norm_num)
    norm_num at h1 h2
    rw [h1, h2]
    norm_num
  have h15 : padicValRat 2 (15 : ℚ) = 0 := by
    have h1 := hodd 15 (by norm_num)
    norm_num at h1
    exact h1
  unfold heckeFifthStep
  split_ifs
  · rw [show 81 * q / 80 = (81 / 5) * q / 16 by ring, padicValRat.div (by positivity) (by norm_num),
      padicValRat.mul (by norm_num) hq0, h81, h16]
    ring
  · rw [padicValRat.div (mul_ne_zero (by norm_num) hq0) (by norm_num),
      padicValRat.mul (by norm_num) hq0, h15, h16]
    ring

/-- **The template boundary.** No finite set contains one and is closed under the ratio-two, three
and five neighbours in `[1, X)`, for any `X ≥ 27/5`. -/
theorem no_finite_hecke_template_at_twentySeven_fifths {X : ℚ} (hX : 27 / 5 ≤ X) :
    ¬ ∃ T : Finset ℚ, 1 ∈ T ∧ HeckeClosed X T := by
  rintro ⟨T, h1, hT⟩
  classical
  let S := T.filter fun q => 1 ≤ q ∧ q < 27 / 25
  have hne : S.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨h1, by norm_num⟩⟩
  obtain ⟨r, hr, hmin⟩ := S.exists_min_image (padicValRat 2) hne
  obtain ⟨hrT, hr1, hr2⟩ := Finset.mem_filter.mp hr
  have hstep := heckeFifthStep_mem hX hT hrT hr1 hr2
  have hb := heckeFifthStep_bounds hr1 hr2
  have hle := hmin _ (Finset.mem_filter.mpr ⟨hstep, hb⟩)
  rw [padicValRat_heckeFifthStep hr1] at hle
  omega

end GaloisForLFunctions.WindowTowerOfSpecZ
