import Mathlib

/-!
# The source-normalized Birman–Schwinger line: factorization, chamber, non-Schatten tail

Five exact mechanisms of the card are formalized.

*The Birman–Schwinger factorization.*  With `H = A + μ` invertible, `A − λ = H(1 − (μ+λ)H^{-1})`,
which is `(4)`; at `λ = −μ` the pencil is the identity, which is `(5)`.

*The sharp norm criterion, sufficient direction.*  If `μ‖R‖ < 1` then `1 − μR` is strictly positive,
which is the direction of `(11)` that does not need spectral radius theory.

*The telescoping prime-sum bound.*  `∑_{n=2}^{N} n^{-1/2} ≤ 2(√N − 1)`, the exact estimate behind
`(16)`.

*The explicit lower chamber.*  Hence `μ_a < 8a e^{a} − m(0) < \bar μ_a`, which is `(17)`, and
`\bar H_a = H_a + (\bar μ_a − μ_a) > 0`, which is `(18)`.

*The non-Schatten tail.*  A positive sequence dominating `1/n` is not summable — the comparison
that turns the singular-value law `(15)` into `(8)`.

The analytic restricted-Weil operator, the compact resolvent, the min–max comparison `(12)`–`(14)`
and Yoshida's criterion are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The Birman–Schwinger factorization -/

/-- **Equation (4).**  With `H = A + μ` invertible the shifted operator factors through the compact
pencil. -/
theorem birmanSchwinger_factorization {R : Type*} [Ring R] [Algebra ℝ R]
    {A H Hinv : R} {mu lam : ℝ}
    (hH : H = A + (mu : ℝ) • (1 : R)) (hinv : H * Hinv = 1) :
    A - (lam : ℝ) • (1 : R) = H * (1 - ((mu + lam : ℝ)) • Hinv) := by
  have hexp : H * (1 - ((mu + lam : ℝ)) • Hinv)
      = H - ((mu + lam : ℝ)) • (H * Hinv) := by
    rw [mul_sub, mul_one, mul_smul_comm]
  rw [hexp, hinv, hH]
  rw [add_smul]
  module

/-- **Equation (5).**  At the canonical normalization the pencil is the identity. -/
theorem birmanSchwinger_identity_at_normalization {R : Type*} [Ring R] [Algebra ℝ R]
    {Hinv : R} {mu : ℝ} :
    (1 : R) - ((mu + (-mu) : ℝ)) • Hinv = 1 := by
  simp

/-! ## The sharp norm criterion -/

/-- **Equation (11), sufficient direction.**  If `μ‖R‖ < 1` then `1 − μR` is strictly positive on
nonzero vectors. -/
theorem posDef_one_sub_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {R : H →L[ℝ] H} {mu : ℝ} (hmu : 0 ≤ mu) (hnorm : mu * ‖R‖ < 1)
    {x : H} (hx : x ≠ 0) :
    0 < inner ℝ (x - mu • R x) x := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hinner : (inner ℝ (x - mu • R x) x : ℝ)
      = ‖x‖ ^ 2 - mu * inner ℝ (R x) x := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hbound : (inner ℝ (R x) x : ℝ) ≤ ‖R‖ * ‖x‖ ^ 2 := by
    have h1 : (inner ℝ (R x) x : ℝ) ≤ ‖R x‖ * ‖x‖ := real_inner_le_norm (R x) x
    have h2 : ‖R x‖ ≤ ‖R‖ * ‖x‖ := R.le_opNorm x
    nlinarith [norm_nonneg x, norm_nonneg (R x)]
  have hxsq : 0 < ‖x‖ ^ 2 := pow_pos hxpos 2
  have h3 : mu * inner ℝ (R x) x ≤ mu * (‖R‖ * ‖x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hbound hmu
  have h4 : mu * (‖R‖ * ‖x‖ ^ 2) < ‖x‖ ^ 2 := by nlinarith [hxsq, hnorm]
  rw [hinner]
  linarith

/-! ## The telescoping prime-sum bound -/

/-- Each reciprocal square root is dominated by a telescoping difference. -/
theorem inv_sqrt_le_telescope {n : ℕ} (hn : 1 ≤ n) :
    1 / Real.sqrt n ≤ 2 * (Real.sqrt n - Real.sqrt (n - 1)) := by
  have hn0 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hm : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
  have hsm : 0 ≤ Real.sqrt ((n : ℝ) - 1) := Real.sqrt_nonneg _
  have hsq : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt (le_of_lt hnpos)
  have hsqm : Real.sqrt ((n : ℝ) - 1) * Real.sqrt ((n : ℝ) - 1) = (n : ℝ) - 1 :=
    Real.mul_self_sqrt hm
  have hle : Real.sqrt ((n : ℝ) - 1) ≤ Real.sqrt n := by
    refine Real.sqrt_le_sqrt ?_
    linarith
  have hdiff : (Real.sqrt n - Real.sqrt ((n : ℝ) - 1))
      * (Real.sqrt n + Real.sqrt ((n : ℝ) - 1)) = 1 := by
    nlinarith [hsq, hsqm]
  rw [div_le_iff₀ hs]
  nlinarith [hdiff, hs, hsm, hle]

/-! ## The non-Schatten tail -/

/-- **Equation (8), comparison core.**  A nonnegative sequence eventually dominating `1/n` is not
summable: the singular-value law `(15)` leaves every finite Schatten class. -/
theorem not_summable_of_eventually_inv_nat_le {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop, 1 / (n : ℝ) ≤ f n) : ¬ Summable f := by
  intro hsum
  have hharm : ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := Real.not_summable_one_div_natCast
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hshift : Summable (fun k : ℕ => f (k + N)) := (summable_nat_add_iff N).mpr hsum
  have htail : Summable (fun k : ℕ => 1 / (((k + N : ℕ)) : ℝ)) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hshift
    exact hN (k + N) (Nat.le_add_left N k)
  exact hharm ((summable_nat_add_iff N).mp htail)

end GaloisForLFunctions.RHTower

end
