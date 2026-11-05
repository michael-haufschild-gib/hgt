import GaloisForLFunctions.ArithmeticDiscreteness.DistinctRootsOfIntegerPolynomialsRepel
import GaloisForLFunctions.ArithmeticDiscreteness.EulerColumnsCollideOrRepelAtPolynomialScale

/-!
# The rank of the frequency module decides repulsion

Why the function-field repulsion does not transfer to `ℤ`: the obstruction is the rank of the
frequency module of the Dirichlet series, not the size or the sign of its coefficients.

* **Rank one: uniform repulsion** (`onePrime_uniform_repulsion`). A one-prime integral carrier
  `s ↦ P(p^{−s})`, `P ∈ ℤ[X]` monic with roots in `|w| ≤ R` (the zeta function of a curve over
  `𝔽_p` has this shape), has its distinct zeros at distance at least
  `min(1, ε/(2R)) / log p`, `ε = (2R)^{−((n−1)²+n−2)}`, uniformly in the height. Distinct zeros
  with the same value of `p^{−s}` differ by a period `2πi m/log p`; distinct values are separated by
  `DistinctRootsOfIntegerPolynomialsRepel`, and `w = p^{−s}` is locally bi-Lipschitz.
* **Rank two: no uniform repulsion** (`twoPrime_no_uniform_repulsion`). The integral carrier
  `(1 − 2^{−s})(1 − 3^{−s}) = 1 − 2^{−s} − 3^{−s} + 6^{−s}` has distinct zeros at every positive
  distance: its two columns interleave with Dirichlet near-coincidences
  (`eulerColumns_near_coincidence`). What survives is repulsion at polynomial scale in the height
  (`eulerCarrier_collide_or_repel`), produced by the effective Baker bound.

Over `𝔽_q` all frequencies are multiples of `log q`; over `ℤ` the frequencies `log p` are
`ℚ`-independent, and the Kronecker flow on the torus they generate brings distinct zeros together
at a rate fixed by Diophantine approximation. Any collide-or-repel law for `ζ` is therefore a
height-dependent transcendence statement about `⊕ ℤ log p`.
-/

open Polynomial Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Rank one: uniform repulsion.** Distinct zeros `s ≠ s'` of `s ↦ P(p^{−s})`, with `P ∈ ℤ[X]`
monic of degree `n`, all complex roots in `|w| ≤ R`, `2R ≥ 1`, satisfy
`‖s − s'‖ ≥ min(1, ε/(2R)) / log p`, `ε = (2R)^{−((n−1)²+n−2)}`, whatever their height. -/
theorem onePrime_uniform_repulsion {P : ℤ[X]} (hP : P.Monic) {R : ℝ} (hR1 : 1 ≤ 2 * R)
    (hR : ∀ z ∈ (toC P).roots, ‖z‖ ≤ R) {p : ℕ} (hp : 1 < p) {s s' : ℂ}
    (hs : (toC P).eval ((p : ℂ) ^ (-s)) = 0) (hs' : (toC P).eval ((p : ℂ) ^ (-s')) = 0)
    (hne : s ≠ s') :
    min 1 (((2 * R) ^ ((P.natDegree - 1) ^ 2 + (P.natDegree - 2)))⁻¹ / (2 * R)) / Real.log p ≤
      ‖s - s'‖ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  set L : ℂ := Complex.log (p : ℂ) with hL
  have hLre : L = ((Real.log p : ℝ) : ℂ) := by rw [hL, Complex.natCast_log]
  have hLnorm : ‖L‖ = Real.log p := by rw [hLre, norm_real, Real.norm_eq_abs, abs_of_pos hlog]
  set w := (p : ℂ) ^ (-s) with hw
  set w' := (p : ℂ) ^ (-s') with hw'
  have hwexp : w = Complex.exp (L * -s) := cpow_def_of_ne_zero hp0 _
  have hw'exp : w' = Complex.exp (L * -s') := cpow_def_of_ne_zero hp0 _
  have hR0 : 0 < 2 * R := by linarith
  set ε := ((2 * R) ^ ((P.natDegree - 1) ^ 2 + (P.natDegree - 2)))⁻¹ with hε
  have hε0 : 0 < ε := by positivity
  have hmem : w ∈ (toC P).roots := (mem_roots (toC_ne_zero hP)).mpr hs
  have hmem' : w' ∈ (toC P).roots := (mem_roots (toC_ne_zero hP)).mpr hs'
  have hsn : 0 < ‖s - s'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- `w = w' · exp(L (s' − s))`
  have hratio : w = w' * Complex.exp (L * (s' - s)) := by
    rw [hwexp, hw'exp, ← Complex.exp_add]; ring_nf
  have hmin1 : min 1 (ε / (2 * R)) ≤ 1 := min_le_left _ _
  by_cases hww : w = w'
  · -- equal values: `s − s'` is a nonzero period
    have hw'0 : w' ≠ 0 := by rw [hw'exp]; exact Complex.exp_ne_zero _
    have h1 : Complex.exp (L * (s' - s)) = 1 := by
      have := hratio; rw [hww] at this
      exact (mul_eq_left₀ hw'0).mp this.symm
    obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp only [Int.cast_zero, zero_mul, mul_eq_zero] at hm
      rcases hm with h | h
      · exact (by rw [hLnorm]; exact hlog.ne' : ‖L‖ ≠ 0) (by rw [h, norm_zero])
      · exact hne (sub_eq_zero.mp h).symm
    have hnorm : ‖L‖ * ‖s - s'‖ = 2 * Real.pi * |(m : ℝ)| := by
      have := congrArg norm hm
      rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Complex.norm_intCast, ← norm_neg (s' - s), neg_sub,
        show ‖(2 : ℂ)‖ = 2 by norm_num] at this
      linarith
    rw [hLnorm] at hnorm
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    rw [div_le_iff₀ hlog]
    nlinarith [Real.pi_gt_three]
  · -- distinct values: separated by integrality
    rcases collide_or_repel_of_monic hP hR1 hR hmem hmem' with h | hsep
    · exact absurd h hww
    by_cases hbig : 1 ≤ ‖L * (s' - s)‖
    · rw [norm_mul, hLnorm, ← norm_neg (s' - s), neg_sub] at hbig
      rw [div_le_iff₀ hlog]
      nlinarith
    · push Not at hbig
      have hexp := Complex.norm_exp_sub_one_le hbig.le
      have hw'R : ‖w'‖ ≤ R := hR w' hmem'
      have hdiff : ‖w - w'‖ ≤ R * (2 * ‖L * (s' - s)‖) := by
        rw [hratio, show w' * Complex.exp (L * (s' - s)) - w' =
          w' * (Complex.exp (L * (s' - s)) - 1) by ring, norm_mul]
        exact mul_le_mul hw'R hexp (norm_nonneg _) (by linarith)
      rw [norm_mul, hLnorm, ← norm_neg (s' - s), neg_sub] at hdiff
      have hkey : ε ≤ 2 * R * (Real.log p * ‖s - s'‖) := by linarith
      have : ε / (2 * R) ≤ Real.log p * ‖s - s'‖ := by rw [div_le_iff₀ hR0]; linarith
      rw [div_le_iff₀ hlog]
      calc min 1 (ε / (2 * R)) ≤ ε / (2 * R) := min_le_right _ _
        _ ≤ Real.log p * ‖s - s'‖ := this
        _ = ‖s - s'‖ * Real.log p := mul_comm _ _

/-- **Rank two: no uniform repulsion.** For every `δ > 0` the integral carrier
`(1 − 2^{−s})(1 − 3^{−s})` has two distinct zeros at distance less than `δ`. -/
theorem twoPrime_no_uniform_repulsion {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ ρ' : ℂ, (1 - (2 : ℂ) ^ (-ρ)) * (1 - (3 : ℂ) ^ (-ρ)) = 0 ∧
      (1 - (2 : ℂ) ^ (-ρ')) * (1 - (3 : ℂ) ^ (-ρ')) = 0 ∧ ρ ≠ ρ' ∧ ‖ρ - ρ'‖ < δ := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * Real.pi / (δ * Real.log 3))
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_trans (by positivity) hn
    exact_mod_cast this
  obtain ⟨k, j, hne, -, hclose⟩ :=
    eulerColumns_near_coincidence Nat.prime_two Nat.prime_three (by norm_num) hn0
  refine ⟨colPt 2 k, colPt 3 j, ?_, ?_, hne, ?_⟩
  · have h := (one_sub_cpow_neg_eq_zero_iff (p := 2) (by norm_num) (colPt 2 k)).mpr ⟨k, rfl⟩
    push_cast at h
    rw [h, zero_mul]
  · have h := (one_sub_cpow_neg_eq_zero_iff (p := 3) (by norm_num) (colPt 3 j)).mpr ⟨j, rfl⟩
    push_cast at h
    rw [h, mul_zero]
  · refine lt_of_le_of_lt hclose ?_
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    push_cast
    nlinarith [Real.pi_pos]

end GaloisForLFunctions.ArithmeticDiscreteness
