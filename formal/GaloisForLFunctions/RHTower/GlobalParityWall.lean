import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.RHTower.HardySignFlipOddOrder
import GaloisForLFunctions.RHTower.TwinRigidity

/-!
# The global parity wall: ξ has a critical-line zero of odd order above every height

Hardy's tail argument excludes a one-signed tail of the real detector `Ξ`, in the weak form
`Ξ ≥ 0` or `Ξ ≤ 0` beyond some height.  Hence `Ξ` takes both strict signs above every height,
which is a seam sign flip, and a seam sign flip encloses a critical-line zero of odd order.

Consequences.
* No structure that forces every vanishing order of ξ to be even can exist: any symmetry class
  whose induced pairing doubles all multiplicities is excluded outright.
* A determinant that presents the divisor of ξ through `e` copies, `ξ^e · u` with `u` entire and
  nonvanishing, has all orders even when `e` is even, whatever the orders of ξ are, and has an
  odd-order zero when `e` is odd.  Parity read off such a determinant therefore never constrains
  the orders of ξ: it is void or globally violated.
* A symmetric `2 × 2` matrix with equal diagonal entries factors as `(a − b)(a + b)`: two
  channels exchanged by an involution contribute their common divisor twice.
-/

open Complex Filter Topology Real

namespace RHTower

/-- The real detector is the real part of ξ on the critical line. -/
theorem Xi_eq_re_xi_linePt (t : ℝ) : Xi t = (xi (linePt t)).re := by
  unfold Xi linePt
  push_cast
  ring_nf

/-- A weakly nonnegative tail of `Ξ` is impossible. -/
theorem false_of_Xi_eventually_nonneg {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t : ℝ, T < t → 0 ≤ Xi t) : False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := -1)
    (by positivity) (by norm_num) ?_
  intro w hw
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := hpos (4 * π * |w|) hbig
  rw [habs, hardyXiDensity]
  have hden : (0:ℝ) < (4 * π * |w|) ^ (2 : ℕ) + 1 / 4 := by positivity
  rw [neg_one_mul, neg_nonneg]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hXi]) hden.le

/-- A weakly nonpositive tail of `Ξ` is impossible. -/
theorem false_of_Xi_eventually_nonpos {T : ℝ} (hT : 0 < T)
    (hneg : ∀ t : ℝ, T < t → Xi t ≤ 0) : False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := 1)
    (by positivity) (by norm_num) ?_
  intro w hw
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := hneg (4 * π * |w|) hbig
  rw [habs, hardyXiDensity, one_mul]
  have hden : (0:ℝ) < (4 * π * |w|) ^ (2 : ℕ) + 1 / 4 := by positivity
  exact div_nonneg (by nlinarith [hXi]) hden.le

/-- `Ξ` is strictly negative somewhere above every height. -/
theorem exists_Xi_neg_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ Xi t < 0 := by
  by_contra hcon
  push Not at hcon
  exact false_of_Xi_eventually_nonneg (T := max T 1)
    (lt_of_lt_of_le one_pos (le_max_right T 1))
    (fun t ht => hcon t (lt_of_le_of_lt (le_max_left T 1) ht))

/-- `Ξ` is strictly positive somewhere above every height. -/
theorem exists_Xi_pos_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ 0 < Xi t := by
  by_contra hcon
  push Not at hcon
  exact false_of_Xi_eventually_nonpos (T := max T 1)
    (lt_of_lt_of_le one_pos (le_max_right T 1))
    (fun t ht => hcon t (lt_of_le_of_lt (le_max_left T 1) ht))

/-- **Hardy sign flips above every height.** -/
theorem exists_Xi_sign_flip_gt (T : ℝ) :
    ∃ τ₁ τ₂ : ℝ, T < τ₁ ∧ τ₁ < τ₂ ∧ Xi τ₁ * Xi τ₂ < 0 := by
  obtain ⟨a, ha, hneg⟩ := exists_Xi_neg_gt T
  obtain ⟨b, hb, hpos⟩ := exists_Xi_pos_gt T
  have hab : a ≠ b := fun h => by rw [h] at hneg; linarith
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, ha, h, mul_neg_of_neg_of_pos hneg hpos⟩
  · exact ⟨b, a, hb, h, mul_neg_of_pos_of_neg hpos hneg⟩

/-- **Critical-line zeros of odd order above every height.** -/
theorem exists_odd_order_line_zero_gt (T : ℝ) :
    ∃ τ : ℝ, T < τ ∧ xi (linePt τ) = 0 ∧ Odd (analyticOrderAt xi (linePt τ)).toNat := by
  obtain ⟨τ₁, τ₂, hT, h12, hflip⟩ := exists_Xi_sign_flip_gt T
  have h1 : xi (linePt τ₁) ≠ 0 := by
    intro h
    rw [Xi_eq_re_xi_linePt, h] at hflip
    simp at hflip
  have h2 : xi (linePt τ₂) ≠ 0 := by
    intro h
    rw [Xi_eq_re_xi_linePt τ₂, h] at hflip
    simp at hflip
  rw [Xi_eq_re_xi_linePt, Xi_eq_re_xi_linePt] at hflip
  obtain ⟨τ, hτ, hzero, hodd⟩ := exists_odd_order_line_zero_of_sign_flip h12 h1 h2 hflip
  exact ⟨τ, lt_trans hT hτ.1, hzero, hodd⟩

/-- ξ has a zero of odd order. -/
theorem exists_odd_order_zero_xi :
    ∃ ρ : ℂ, xi ρ = 0 ∧ Odd (analyticOrderAt xi ρ).toNat := by
  obtain ⟨τ, _, hzero, hodd⟩ := exists_odd_order_line_zero_gt 0
  exact ⟨linePt τ, hzero, hodd⟩

/-- **The global parity wall.**  Not every vanishing order of ξ is even. -/
theorem not_forall_even_order_xi : ¬ ∀ ρ : ℂ, Even (analyticOrderAt xi ρ).toNat := by
  intro h
  obtain ⟨ρ, _, hodd⟩ := exists_odd_order_zero_xi
  exact (Nat.not_even_iff_odd.mpr hodd) (h ρ)

/-- The global parity wall in divisibility form: `2` does not divide every order of ξ. -/
theorem not_forall_two_dvd_order_xi : ¬ ∀ ρ : ℂ, (2 : ℕ∞) ∣ analyticOrderAt xi ρ := by
  intro h
  apply not_forall_even_order_xi
  intro ρ
  have hcoe : analyticOrderAt xi ρ = (((analyticOrderAt xi ρ).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat (xi_order_ne_top ρ)).symm
  have h2 := h ρ
  rw [hcoe] at h2
  exact even_iff_two_dvd.mpr (natCast_dvd_natCast_of_enat two_ne_zero h2)

/-! ## Copies of a divisor: parity is void or violated -/

/-- The order of `f^e · u` at a point where `u` does not vanish is `e` times the order of `f`. -/
theorem analyticOrderAt_pow_mul_unit {f u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) (e : ℕ) :
    analyticOrderAt (fun w => f w ^ e * u w) z = e • analyticOrderAt f z := by
  have h1 : analyticOrderAt (fun w => f w ^ e * u w) z
      = analyticOrderAt (f ^ e) z + analyticOrderAt u z :=
    analyticOrderAt_mul (hf.pow e) hu
  rw [h1, analyticOrderAt_pow hf, hu.analyticOrderAt_eq_zero.mpr hu0, add_zero]

/-- The natural-number order of `f^e · u` is `e` times that of `f` when the latter is finite. -/
theorem toNat_analyticOrderAt_pow_mul_unit {f u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0)
    (hfin : analyticOrderAt f z ≠ ⊤) (e : ℕ) :
    (analyticOrderAt (fun w => f w ^ e * u w) z).toNat = e * (analyticOrderAt f z).toNat := by
  rw [analyticOrderAt_pow_mul_unit hf hu hu0 e]
  have hcoe : analyticOrderAt f z = (((analyticOrderAt f z).toNat : ℕ) : ℕ∞) :=
    (ENat.coe_toNat hfin).symm
  rw [hcoe, nsmul_eq_mul]
  norm_cast

/-- **An even number of copies makes every order even, whatever the orders of `f` are.** -/
theorem even_order_of_even_copies {f u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0)
    (hfin : analyticOrderAt f z ≠ ⊤) {e : ℕ} (he : Even e) :
    Even (analyticOrderAt (fun w => f w ^ e * u w) z).toNat := by
  rw [toNat_analyticOrderAt_pow_mul_unit hf hu hu0 hfin e]
  exact he.mul_right _

/-- **An odd number of copies preserves the parity of the order.** -/
theorem odd_order_copies_iff {f u : ℂ → ℂ} {z : ℂ}
    (hf : AnalyticAt ℂ f z) (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0)
    (hfin : analyticOrderAt f z ≠ ⊤) {e : ℕ} (he : Odd e) :
    Odd (analyticOrderAt (fun w => f w ^ e * u w) z).toNat ↔ Odd (analyticOrderAt f z).toNat := by
  rw [toNat_analyticOrderAt_pow_mul_unit hf hu hu0 hfin e, Nat.odd_mul]
  exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

/-- **Parity read off copies of ξ is void or globally violated.**  For every `e` and every entire
nonvanishing `u`, either `e` is even and every order of `ξ^e · u` is even, or `e` is odd and
`ξ^e · u` has a zero of odd order. -/
theorem xi_copies_parity_dichotomy (e : ℕ) {u : ℂ → ℂ} (hu : Differentiable ℂ u)
    (hu0 : ∀ z, u z ≠ 0) :
    (Even e ∧ ∀ z, Even (analyticOrderAt (fun w => xi w ^ e * u w) z).toNat) ∨
    (Odd e ∧ ∃ z, Odd (analyticOrderAt (fun w => xi w ^ e * u w) z).toNat) := by
  rcases Nat.even_or_odd e with he | he
  · left
    refine ⟨he, fun z => even_order_of_even_copies (xi_differentiable.analyticAt z)
      (hu.analyticAt z) (hu0 z) (xi_order_ne_top z) he⟩
  · right
    obtain ⟨ρ, _, hodd⟩ := exists_odd_order_zero_xi
    exact ⟨he, ρ, (odd_order_copies_iff (xi_differentiable.analyticAt ρ) (hu.analyticAt ρ)
      (hu0 ρ) (xi_order_ne_top ρ) he).mpr hodd⟩

/-- Two channels exchanged by an involution: a symmetric `2 × 2` matrix with equal diagonal
entries has determinant `(a − b)(a + b)`. -/
theorem det_involution_symmetric (a b : ℂ) : !![a, b; b, a].det = (a - b) * (a + b) := by
  rw [Matrix.det_fin_two_of]
  ring

end RHTower
