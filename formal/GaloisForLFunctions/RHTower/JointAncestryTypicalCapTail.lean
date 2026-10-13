import GaloisForLFunctions.RHTower.JointAncestryTypicalCapBad

/-!
# The high zeros of the coherent model

For a finite set `Low` of zero copies, the high part of the shifted aggregate is controlled by
`H(k) = Σ_{q ∉ Low} |w_q| Σ_j |∏_p g_p(q, k_p + j)|` (`capHigh`).  Averaged over the torus,
`Σ_k H(k) ≤ (Σ_{q ∉ Low} |w_q|) · N · N^{|P|} · exp(C^{2Θ} V)` (`sum_capHigh_le`), by the
product second moment `∏_p (1 + ¼(|A_p|² + |B_p|²)) ≤ exp(2 C^{2Θ} V)` and Cauchy–Schwarz.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- `|∏_p g_p| ≤ 2^{|P|}` when every coefficient has norm `≤ 1`. -/
theorem norm_prod_phaseFactor_le_two_pow {N : ℕ} {P : Finset Nat.Primes} (A B : ↥P → ℂ)
    (hA : ∀ p, ‖A p‖ ≤ 1) (hB : ∀ p, ‖B p‖ ≤ 1) (k : ↥P → Fin N) :
    ‖∏ p : ↥P, phaseFactor N (1 / 2) (A p) (B p) (k p)‖ ≤ 2 ^ P.card := by
  rw [norm_prod]
  calc ∏ p : ↥P, ‖phaseFactor N (1 / 2) (A p) (B p) (k p)‖ ≤ ∏ _p : ↥P, (2 : ℝ) :=
        Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => by
          refine (norm_phaseFactor_le (by norm_num) _ _ _).trans ?_
          linarith [hA p, hB p]
    _ = 2 ^ P.card := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

/-- The high part `H(k)`. -/
def capHigh (σ : ℝ) (N : ℕ) (P : Finset Nat.Primes) (Low : Finset XiZeroCopy)
    (k : ↥P → Fin N) : ℝ :=
  ∑' q : {q : XiZeroCopy // q ∉ Low}, ‖lagWeight q‖ *
    ∑ j : Fin N, ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)‖

theorem norm_capA_le_one {σ Θ : ℝ} (hΘσ : Θ ≤ σ) {q : XiZeroCopy}
    (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (p : Nat.Primes) : ‖typCapA σ q p‖ ≤ 1 := by
  refine (norm_capA_le hq p).trans (Real.exp_le_one_iff.mpr ?_)
  have := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < p)).le
  nlinarith

theorem norm_capB_le_one {σ Θ : ℝ} (hΘσ : Θ ≤ σ) {q : XiZeroCopy}
    (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (p : Nat.Primes) : ‖typCapB σ q p‖ ≤ 1 := by
  refine (norm_capB_le hq p).trans (Real.exp_le_one_iff.mpr ?_)
  have := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < p)).le
  nlinarith

theorem summable_capHigh_term {σ Θ : ℝ} (hΘσ : Θ ≤ σ) (habs : ∀ q : XiZeroCopy,
    |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (N : ℕ) (P : Finset Nat.Primes) (Low : Finset XiZeroCopy)
    (k : ↥P → Fin N) :
    Summable fun q : {q : XiZeroCopy // q ∉ Low} => ‖lagWeight q‖ *
      ∑ j : Fin N, ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)‖ := by
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    ((summable_norm_lagWeight.subtype _).mul_right ((N : ℝ) * 2 ^ P.card))
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ∑ j : Fin N, ‖∏ p : ↥P, phaseFactor N (1 / 2) (typCapA σ q p) (typCapB σ q p) (phaseShift j k p)‖
      ≤ ∑ _j : Fin N, (2 : ℝ) ^ P.card := Finset.sum_le_sum fun j _ =>
        norm_prod_phaseFactor_le_two_pow _ _ (fun p => norm_capA_le_one hΘσ (habs q) p)
          (fun p => norm_capB_le_one hΘσ (habs q) p) _
    _ = (N : ℝ) * 2 ^ P.card := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]

/-- `∏_p (1 + ¼(|A_p|² + |B_p|²)) ≤ exp(2 C^{2Θ} V)` on a window. -/
theorem prod_one_add_sq_le {σ Θ X C : ℝ} {P : Finset Nat.Primes} (hX : 1 ≤ X) (hΘ : 0 ≤ Θ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    {q : XiZeroCopy} (hq : |(q.1 : ℂ).re - 1 / 2| ≤ Θ) :
    ∏ p : ↥P, (1 + (1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2)) ≤
      Real.exp (2 * (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P)) := by
  have hsum := sum_exp_two_mul_le (σ := σ) hX hΘ hP
  have hterm : ∀ p : ↥P, (1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2) ≤
      1 / 2 * Real.exp (2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)) := by
    intro p
    have hA := sq_norm_le_of_le (norm_nonneg _) (norm_capA_le (σ := σ) hq p)
    have hB := sq_norm_le_of_le (norm_nonneg _) (norm_capB_le (σ := σ) hq p)
    have e : 2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) =
        2 * (Θ - σ) * Real.log (((p : Nat.Primes) : ℕ) : ℝ) := rfl
    nlinarith
  calc ∏ p : ↥P, (1 + (1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2))
      ≤ ∏ p : ↥P, Real.exp ((1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2)) :=
        Finset.prod_le_prod (fun p _ => by positivity) fun p _ => by
          have := Real.add_one_le_exp ((1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2))
          linarith
    _ = Real.exp (∑ p : ↥P, (1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2)) :=
        (Real.exp_sum _ _).symm
    _ ≤ Real.exp (2 * (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P)) := by
        refine Real.exp_le_exp.mpr ((Finset.sum_le_sum fun p _ => hterm p).trans ?_)
        rw [← Finset.mul_sum]
        nlinarith

/-- **The averaged high part.** -/
theorem sum_capHigh_le {σ Θ X C : ℝ} {N : ℕ} (hN : 3 ≤ N) {P : Finset Nat.Primes} (hX : 1 ≤ X)
    (hΘ : 0 ≤ Θ) (hΘσ : Θ ≤ σ)
    (hP : ∀ p ∈ P, X < (((p : Nat.Primes) : ℕ) : ℝ) ∧ (((p : Nat.Primes) : ℕ) : ℝ) ≤ C * X)
    (habs : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ Θ) (Low : Finset XiZeroCopy) :
    ∑ k : ↥P → Fin N, capHigh σ N P Low k ≤
      (∑' q : {q : XiZeroCopy // q ∉ Low}, ‖lagWeight q‖) *
        ((N : ℝ) * ((N : ℝ) ^ Fintype.card ↥P *
          Real.exp (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P))) := by
  unfold capHigh
  rw [← Summable.tsum_finsetSum (fun k _ => summable_capHigh_term hΘσ habs N P Low k)]
  have hs : Summable (fun q : {q : XiZeroCopy // q ∉ Low} => ‖lagWeight (q : XiZeroCopy)‖) :=
    summable_norm_lagWeight.subtype _
  rw [← hs.tsum_mul_right]
  refine Summable.tsum_le_tsum (fun q => ?_) ?_ (hs.mul_right _)
  · rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have h := sum_sum_norm_prod_phaseFactor_shift_le (ι := ↥P) hN (1 / 2)
      (fun p => typCapA σ q p) (fun p => typCapB σ q p)
    refine h.trans ?_
    have hprod := prod_one_add_sq_le (σ := σ) hX hΘ hP (habs q)
    have hsq : Real.sqrt (∏ p : ↥P, (1 + (1 / 2 : ℝ) ^ 2 * (‖typCapA σ q p‖ ^ 2 + ‖typCapB σ q p‖ ^ 2))) ≤
        Real.exp (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P) := by
      rw [show Real.exp (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P) =
        Real.sqrt (Real.exp (2 * (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P))) by
          rw [show 2 * (Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P) =
            Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P +
              Real.exp (2 * Θ * Real.log C) * capVar Θ σ X P by ring, Real.exp_add,
            Real.sqrt_mul_self (Real.exp_pos _).le]]
      exact Real.sqrt_le_sqrt hprod
    have hn0 : (0 : ℝ) ≤ (N : ℝ) ^ Fintype.card ↥P := by positivity
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hn0) hN0
  · exact summable_sum fun k _ => summable_capHigh_term hΘσ habs N P Low k

end

end RHTower
