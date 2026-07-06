import GaloisForLFunctions.RHTower.RiemannTower
import GaloisForLFunctions.RHTower.WeightMismatchRefutation
import GaloisForLFunctions.RHTower.Reflection

/-!
# Structural theory of the RH multiplicity-parity ladder

The ladder `RHLadder k` (every ξ-zero right of the critical line has vanishing order divisible by
`2^k`) is a decreasing family of hypotheses whose intersection is RH.  This file develops its
complete order-theoretic and arithmetic structure: triviality of rung `0`, monotone nesting, the
2-adic valuation (`ladderHeight`) that measures how many rungs a given zero survives, the sharp level
at which a zero collapses the ladder, the cofinal criterion, the analytic root-nesting face, and the
identification of the full ladder with the absence of right-half zeros.
-/

open Complex Set

namespace RHTower

/-- `((2^k : ℕ) : ℕ∞) ∣ ord` is equivalent to the plain-`ℕ` divisibility `2^k ∣ ord.toNat`, since
ξ's vanishing order is finite. -/
theorem rhLadder_iff_toNat_dvd (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → 2 ^ k ∣ (analyticOrderAt xi ρ).toNat := by
  unfold RHLadder
  refine forall₃_congr fun ρ _ _ => ?_
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  constructor
  · intro h
    rw [hcoe] at h
    exact natCast_dvd_natCast_of_enat (pow_ne_zero k two_ne_zero) h
  · intro h
    rw [hcoe]
    exact Nat.cast_dvd_cast h

/-- **Rung 0 is trivial.** Every order is divisible by `2^0 = 1`. -/
theorem rhLadder_zero : RHLadder 0 := by
  intro ρ _ _
  simp only [pow_zero, Nat.cast_one, one_dvd]

/-- **Monotone nesting.** A higher rung implies every lower rung: the ladder is a decreasing family
of hypotheses. -/
theorem rhLadder_of_le {m k : ℕ} (hmk : m ≤ k) (h : RHLadder k) : RHLadder m := by
  intro ρ hρ hzero
  exact dvd_trans (Nat.cast_dvd_cast (pow_dvd_pow 2 hmk)) (h ρ hρ hzero)

/-- The successor case of nesting. -/
theorem rhLadder_of_succ {k : ℕ} (h : RHLadder (k + 1)) : RHLadder k :=
  rhLadder_of_le (Nat.le_succ k) h

/-- Every rung `k ≥ 1` implies the first rung. -/
theorem rhLadder_imp_one {k : ℕ} (hk : 1 ≤ k) (h : RHLadder k) : RHLadder 1 :=
  rhLadder_of_le hk h

/-- The **ladder height** of a point: the 2-adic valuation of ξ's vanishing order there. For a
right-half ξ-zero this is the exact number of ladder rungs its order survives. -/
noncomputable def ladderHeight (ρ : ℂ) : ℕ := (analyticOrderAt xi ρ).toNat.factorization 2

/-- For a ξ-zero the order's `toNat` is nonzero (the order is finite and positive). -/
theorem xi_order_toNat_ne_zero {ρ : ℂ} (hzero : xi ρ = 0) :
    (analyticOrderAt xi ρ).toNat ≠ 0 := by
  have h1 : analyticOrderAt xi ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨xi_analyticOnNhd_univ ρ (Set.mem_univ ρ), hzero⟩
  intro h0
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact h1 h
  · exact xi_order_ne_top ρ h

/-- **Ladder in terms of height.** Rung `k` holds iff every right-half ξ-zero has ladder height at
least `k` — i.e. its order's 2-adic valuation is `≥ k`. -/
theorem rhLadder_iff_ladderHeight_ge (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, xi ρ = 0 → k ≤ ladderHeight ρ := by
  rw [rhLadder_iff_toNat_dvd]
  refine forall₃_congr fun ρ _ hzero => ?_
  exact Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (xi_order_toNat_ne_zero hzero)

/-- **Sharp collapse.** A right-half ξ-zero breaks every rung strictly above its ladder height. -/
theorem not_rhLadder_of_gt_ladderHeight {ρ : ℂ} (hρ : ρ ∈ rightHalf) (hzero : xi ρ = 0)
    {k : ℕ} (hk : ladderHeight ρ < k) : ¬ RHLadder k := by
  intro hlad
  rw [rhLadder_iff_ladderHeight_ge] at hlad
  exact absurd (hlad ρ hρ hzero) (Nat.not_le.mpr hk)

/-- A right-half ξ-zero breaks the rung one above its height — the exact first failing level. -/
theorem not_rhLadder_ladderHeight_succ {ρ : ℂ} (hρ : ρ ∈ rightHalf) (hzero : xi ρ = 0) :
    ¬ RHLadder (ladderHeight ρ + 1) :=
  not_rhLadder_of_gt_ladderHeight hρ hzero (Nat.lt_succ_self _)

/-- **Cofinal criterion.** If the ladder holds at arbitrarily large levels, it holds at every
level — hence RH. Monotone nesting turns a cofinal set of rungs into all rungs. -/
theorem rh_of_rhLadder_cofinal (h : ∀ N, ∃ k, N ≤ k ∧ RHLadder k) : RiemannHypothesis := by
  rw [rh_iff_forall_ladder]
  intro k
  obtain ⟨k', hk', hlad⟩ := h k
  exact rhLadder_of_le hk' hlad

/-- **Full ladder ⟺ no right-half zero.** The intersection of all rungs is exactly RH stated as the
non-vanishing of ξ off the critical line. -/
theorem forall_rhLadder_iff_no_rightHalf_zero :
    (∀ k, RHLadder k) ↔ ∀ ρ ∈ rightHalf, xi ρ ≠ 0 := by
  rw [← rh_iff_forall_ladder, rh_iff_xi_ne_zero_right]

/-- **Root nesting** (analytic face of monotone nesting). A `2^{k+1}`-th analytic root of ξ on the
half-plane yields a `2^k`-th root by squaring. -/
theorem exists_root_of_exists_root_succ {k : ℕ}
    (h : ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ 2 ^ (k + 1) = xi s) :
    ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ 2 ^ k = xi s := by
  obtain ⟨g, hg, hgpow⟩ := h
  refine ⟨fun s => g s ^ 2, hg.pow 2, fun s hs => ?_⟩
  calc (g s ^ 2) ^ 2 ^ k = g s ^ (2 * 2 ^ k) := by rw [← pow_mul]
    _ = g s ^ 2 ^ (k + 1) := by rw [← pow_succ']
    _ = xi s := hgpow s hs

/-- **Rung 1 as a square root.** `RHLadder 1` holds iff ξ admits an analytic square root on the
half-plane `Re s > ½` — the base case of the Kummer tower. -/
theorem rhLadder_one_iff_sqrt_rightHalf :
    RHLadder 1 ↔ ∃ g, AnalyticOnNhd ℂ g rightHalf ∧ ∀ s ∈ rightHalf, g s ^ 2 = xi s := by
  rw [rhLadder_iff_root]
  simp only [pow_one]

/-! ## Regional and conjugation localization of the ladder -/

theorem xi_ne_zero_of_one_le_re {ρ : ℂ} (h : 1 ≤ ρ.re) : xi ρ ≠ 0 := by
  by_cases hρ1 : ρ = 1
  · rw [hρ1, xi_one]; norm_num
  · have hpos : 0 < ρ.re := by linarith
    intro hz
    rw [xi_eq_zero_iff hpos hρ1] at hz
    exact riemannZeta_ne_zero_of_one_le_re h hz

theorem rhLadder_iff_strip (k : ℕ) :
    RHLadder k ↔ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ := by
  unfold RHLadder
  constructor
  · intro h ρ h1 _ hz
    exact h ρ (mem_rightHalf.mpr h1) hz
  · intro h ρ hρ hz
    have h1 := mem_rightHalf.mp hρ
    by_cases h2 : ρ.re < 1
    · exact h ρ h1 h2 hz
    · exact absurd hz (xi_ne_zero_of_one_le_re (not_lt.mp h2))

theorem ladderHeight_conj (ρ : ℂ) : ladderHeight ((starRingEnd ℂ) ρ) = ladderHeight ρ := by
  unfold ladderHeight
  rw [xi_orderAt_conj]

theorem rhLadder_iff_upperHalf (k : ℕ) :
    RHLadder k ↔ ∀ ρ ∈ rightHalf, 0 ≤ ρ.im → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ := by
  constructor
  · intro h ρ hρ _ hz
    exact h ρ hρ hz
  · intro h ρ hρ hz
    by_cases him : 0 ≤ ρ.im
    · exact h ρ hρ him hz
    · have hconj_mem : (starRingEnd ℂ) ρ ∈ rightHalf := by
        rw [mem_rightHalf, Complex.conj_re]; exact mem_rightHalf.mp hρ
      have hconj_im : 0 ≤ ((starRingEnd ℂ) ρ).im := by
        rw [Complex.conj_im]; linarith [not_le.mp him]
      have hconj_z : xi ((starRingEnd ℂ) ρ) = 0 := by rw [xi_conj, hz, map_zero]
      have hres := h ((starRingEnd ℂ) ρ) hconj_mem hconj_im hconj_z
      rwa [xi_orderAt_conj] at hres

theorem rhLadder_iff_openStrip_upper (k : ℕ) :
    RHLadder k ↔ ∀ ρ : ℂ, 1 / 2 < ρ.re → ρ.re < 1 → 0 ≤ ρ.im → xi ρ = 0 →
      ((2 ^ k : ℕ) : ℕ∞) ∣ analyticOrderAt xi ρ := by
  rw [rhLadder_iff_upperHalf]
  constructor
  · intro h ρ h1 _ him hz
    exact h ρ (mem_rightHalf.mpr h1) him hz
  · intro h ρ hρ him hz
    have h1 := mem_rightHalf.mp hρ
    by_cases h2 : ρ.re < 1
    · exact h ρ h1 h2 him hz
    · exact absurd hz (xi_ne_zero_of_one_le_re (not_lt.mp h2))

/-- The ladder height is invariant under the functional-equation reflection `ρ ↦ 1 − ρ`. -/
theorem ladderHeight_one_sub (ρ : ℂ) : ladderHeight (1 - ρ) = ladderHeight ρ := by
  unfold ladderHeight
  rw [xi_orderAt_one_sub]

/-- The ladder height is constant across the full symmetry quadruple
`{ρ, 1 − ρ, ρ̄, 1 − ρ̄}`: the 2-adic valuation of the vanishing order is a genuine invariant of the
orbit generated by the functional equation and Schwarz reflection. -/
theorem ladderHeight_quadruple_eq (ρ : ℂ) :
    ladderHeight (1 - ρ) = ladderHeight ρ ∧
      ladderHeight ((starRingEnd ℂ) ρ) = ladderHeight ρ ∧
      ladderHeight (1 - (starRingEnd ℂ) ρ) = ladderHeight ρ := by
  refine ⟨ladderHeight_one_sub ρ, ladderHeight_conj ρ, ?_⟩
  rw [ladderHeight_one_sub, ladderHeight_conj]

end RHTower
