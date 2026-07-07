/-
# The ξ deck charge: the RH ladder as the vanishing of a single `μ_{2^k}`-valued observable

The ladder rung `RHLadder k` is a divisibility condition, one clause per right-half zero.
This file packages that condition into one named function of a point,

  `xiDeckCharge k ρ = exp(2πi · ord_ρ(ξ) / 2^k) ∈ μ_{2^k}`,

the monodromy of the `2^k`-th-root torsor of ξ around ρ.  It is manifestly independent of
any choice of root — it is written directly from the vanishing order — yet it *is* the
deck class of any actual pair of chart roots (`xiDeckCharge_eq_chart_deckClass`), so it is
the realized geometric monodromy, not a bookkeeping surrogate.

The rung is then exactly the vanishing of this observable at every right-half zero
(`rhLadder_iff_xiDeckCharge_one`), and RH is its vanishing at every level and zero
(`rh_iff_xiDeckCharge`).  The charge carries the structure that names it a deck-torsor
object:

* it is a `2^k`-th root of unity (`xiDeckCharge_pow`);
* it descends the dyadic tower, `w_{k+1}² = w_k` (`xiDeckCharge_succ_sq`);
* it is constant on the `V₄` symmetry orbit `{ρ, 1−ρ, ρ̄, 1−ρ̄}` of ξ
  (`xiDeckCharge_conj`, `xiDeckCharge_one_sub`, `xiDeckCharge_quadruple`);
* at a zero, its triviality reads the 2-adic height, `w_k = 1 ↔ k ≤ ladderHeight ρ`.

Everything is read off `exp` and the vanishing order; nothing is integrated.
-/
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.DeckWindow

namespace RHTower

open Complex Metric

/-- The level-`2^k` deck charge of ξ at `ρ`: the monodromy `exp(2πi · ord_ρ(ξ) / 2^k)` of
the `2^k`-th-root torsor around `ρ`.  Written from the vanishing order, so root-choice
independent; equal to the deck class of any pair of chart roots. -/
noncomputable def xiDeckCharge (k : ℕ) (ρ : ℂ) : ℂ :=
  exp (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ).toNat : ℕ) / ((2 ^ k : ℕ) : ℂ))

/-- **Triviality reads divisibility.**  The charge is `1` iff `2^k` divides the vanishing
order — the `toNat` form of the ladder clause. -/
theorem xiDeckCharge_eq_one_iff_toNat_dvd (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ρ = 1 ↔ 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
  unfold xiDeckCharge
  exact exp_two_pi_mul_div_eq_one_iff (pow_pos (by norm_num) k) ((analyticOrderAt xi ρ).toNat)

/-- **The charge is the realized deck class.**  Around any `ρ` there is a scale below which
every pair of analytic `2^k`-th-root chart branches has deck class exactly `xiDeckCharge k ρ`
at the seam ports: the observable is the monodromy of genuine roots. -/
theorem xiDeckCharge_eq_chart_deckClass (k : ℕ) (ρ : ℂ) :
    ∃ R₀ > 0, ∀ {R : ℝ}, 0 < R → R ≤ R₀ → ∀ {G₁ G₂ : ℂ → ℂ},
      AnalyticOnNhd ℂ G₁ (chartR ρ R) → AnalyticOnNhd ℂ G₂ (chartL ρ R) →
      (∀ z ∈ chartR ρ R, G₁ z ^ (2 ^ k) = xi z) →
      (∀ z ∈ chartL ρ R, G₂ z ^ (2 ^ k) = xi z) →
      deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I) (ρ - ((R / 2 : ℝ) : ℂ) * I)
        = xiDeckCharge k ρ := by
  obtain ⟨R₀, hR₀, hclass⟩ := xi_deckClass ρ
  refine ⟨R₀, hR₀, ?_⟩
  intro R hR hRle G₁ G₂ hG₁ hG₂ hpG₁ hpG₂
  simp only [xiDeckCharge]
  rw [hclass hR hRle (pow_pos (by norm_num) k) hG₁ hG₂ hpG₁ hpG₂]

/-- Chart roots realizing the charge exist at every small enough scale. -/
theorem exists_chart_roots_deckClass_eq_xiDeckCharge (k : ℕ) (ρ : ℂ) :
    ∃ R₀ > 0, ∀ R : ℝ, 0 < R → R ≤ R₀ →
      ∃ G₁ G₂, AnalyticOnNhd ℂ G₁ (chartR ρ R) ∧ AnalyticOnNhd ℂ G₂ (chartL ρ R) ∧
        (∀ z ∈ chartR ρ R, G₁ z ^ (2 ^ k) = xi z) ∧
        (∀ z ∈ chartL ρ R, G₂ z ^ (2 ^ k) = xi z) ∧
        deckClass G₁ G₂ (ρ + ((R / 2 : ℝ) : ℂ) * I) (ρ - ((R / 2 : ℝ) : ℂ) * I)
          = xiDeckCharge k ρ := by
  obtain ⟨R₁, hR₁, hroots⟩ := xi_exists_chart_roots ρ
  obtain ⟨R₂, hR₂, hcl⟩ := xiDeckCharge_eq_chart_deckClass k ρ
  refine ⟨min R₁ R₂, lt_min hR₁ hR₂, ?_⟩
  intro R hR hRle
  obtain ⟨⟨G₁, hG₁an, hG₁pow⟩, G₂, hG₂an, hG₂pow⟩ :=
    hroots R hR (le_trans hRle (min_le_left R₁ R₂)) (2 ^ k) (pow_pos (by norm_num) k)
  exact ⟨G₁, G₂, hG₁an, hG₂an, hG₁pow, hG₂pow,
    hcl hR (le_trans hRle (min_le_right R₁ R₂)) hG₁an hG₂an hG₁pow hG₂pow⟩

/-- **Rung `k` = vanishing of the charge.**  `RHLadder k` holds iff the deck charge is
trivial at every right-half ξ-zero. -/
theorem rhLadder_iff_xiDeckCharge_one (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1 := by
  rw [rhLadder_iff_toNat_dvd]
  refine forall₃_congr fun ρ _ _ => ?_
  exact (xiDeckCharge_eq_one_iff_toNat_dvd k ρ).symm

/-- **RH = the charge vanishes at every level and every right-half zero.** -/
theorem rh_iff_xiDeckCharge :
    RiemannHypothesis ↔ ∀ k, ∀ ρ ∈ rightHalf, xi ρ = 0 → xiDeckCharge k ρ = 1 := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' fun k => rhLadder_iff_xiDeckCharge_one k

/-! ## The torsor structure of the charge -/

/-- The charge is a `2^k`-th root of unity: it takes values in `μ_{2^k}`. -/
theorem xiDeckCharge_pow (k : ℕ) (ρ : ℂ) : xiDeckCharge k ρ ^ (2 ^ k) = 1 := by
  unfold xiDeckCharge
  rw [← exp_nat_mul]
  have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (by norm_num) k).ne'
  have harg : ((2 ^ k : ℕ) : ℂ) *
      (2 * (Real.pi : ℂ) * I * ((analyticOrderAt xi ρ).toNat : ℕ) / ((2 ^ k : ℕ) : ℂ))
      = ((analyticOrderAt xi ρ).toNat : ℕ) * (2 * (Real.pi : ℂ) * I) := by
    field_simp
  rw [harg, exp_nat_mul, exp_two_pi_mul_I, one_pow]

/-- **Dyadic coherence.**  Squaring the level-`k+1` charge gives the level-`k` charge:
`w_{k+1}² = w_k`.  This is the tower structure of the deck classes. -/
theorem xiDeckCharge_succ_sq (k : ℕ) (ρ : ℂ) :
    xiDeckCharge (k + 1) ρ ^ 2 = xiDeckCharge k ρ := by
  unfold xiDeckCharge
  rw [← exp_nat_mul]
  congr 1
  have h2 : ((2 : ℕ) : ℂ) ≠ 0 := by norm_num
  have h2k : ((2 ^ k : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (by norm_num) k).ne'
  have e : ((2 ^ (k + 1) : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((2 ^ k : ℕ) : ℂ) := by push_cast; ring
  rw [e]
  field_simp

/-- **Rung 0 is invisible.**  The level-`1` (i.e. `2^0`) charge is always `1`. -/
theorem xiDeckCharge_zero (ρ : ℂ) : xiDeckCharge 0 ρ = 1 := by
  have h := xiDeckCharge_pow 0 ρ
  simpa using h

/-- Off the ξ-divisor the charge is trivial: a non-zero has order `0`, divisible by all. -/
theorem xiDeckCharge_eq_one_of_ne_zero (k : ℕ) {ρ : ℂ} (h : xi ρ ≠ 0) :
    xiDeckCharge k ρ = 1 := by
  rw [xiDeckCharge_eq_one_iff_toNat_dvd]
  have h0 : analyticOrderAt xi ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr h)
  rw [h0]
  simp

/-- The charge is invariant under Schwarz reflection `ρ ↦ ρ̄`. -/
theorem xiDeckCharge_conj (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k ((starRingEnd ℂ) ρ) = xiDeckCharge k ρ := by
  unfold xiDeckCharge
  rw [xi_orderAt_conj]

/-- The charge is invariant under the functional-equation reflection `ρ ↦ 1 − ρ`. -/
theorem xiDeckCharge_one_sub (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k (1 - ρ) = xiDeckCharge k ρ := by
  unfold xiDeckCharge
  rw [xi_orderAt_one_sub]

/-- **`V₄`-invariance.**  The charge is constant on the full symmetry quadruple
`{ρ, 1−ρ, ρ̄, 1−ρ̄}` generated by the functional equation and Schwarz reflection. -/
theorem xiDeckCharge_quadruple (k : ℕ) (ρ : ℂ) :
    xiDeckCharge k (1 - ρ) = xiDeckCharge k ρ ∧
      xiDeckCharge k ((starRingEnd ℂ) ρ) = xiDeckCharge k ρ ∧
      xiDeckCharge k (1 - (starRingEnd ℂ) ρ) = xiDeckCharge k ρ := by
  refine ⟨xiDeckCharge_one_sub k ρ, xiDeckCharge_conj k ρ, ?_⟩
  rw [xiDeckCharge_one_sub, xiDeckCharge_conj]

/-- **The charge reads the 2-adic height.**  At a ξ-zero, the level-`k` charge is trivial
iff the zero survives to rung `k`, i.e. `k ≤ ladderHeight ρ`.  The charge stratifies the
divisor by how many rungs each zero climbs. -/
theorem xiDeckCharge_eq_one_iff_le_ladderHeight (k : ℕ) {ρ : ℂ} (h : xi ρ = 0) :
    xiDeckCharge k ρ = 1 ↔ k ≤ ladderHeight ρ := by
  rw [xiDeckCharge_eq_one_iff_toNat_dvd]
  exact Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (xi_order_toNat_ne_zero h)

/-- **The base level is the parity sign.**  The level-`2` (`k = 1`) charge is exactly
`(−1)^{ord}`: the first rung's monodromy is the classical sign of ξ around the zero, and
it is `1` iff the order is even.  This is the μ₂ face of the μ_{2^k} tower. -/
theorem xiDeckCharge_one_eq_neg_one_pow (ρ : ℂ) :
    xiDeckCharge 1 ρ = (-1) ^ (analyticOrderAt xi ρ).toNat := by
  unfold xiDeckCharge
  have harg : 2 * (Real.pi : ℂ) * I * (((analyticOrderAt xi ρ).toNat : ℕ) : ℂ) / ((2 ^ 1 : ℕ) : ℂ)
      = (((analyticOrderAt xi ρ).toNat : ℕ) : ℂ) * ((Real.pi : ℂ) * I) := by
    push_cast
    ring
  rw [harg, exp_nat_mul, exp_pi_mul_I]

end RHTower
