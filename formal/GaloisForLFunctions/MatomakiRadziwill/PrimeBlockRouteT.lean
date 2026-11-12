import GaloisForLFunctions.MatomakiRadziwill.TwistedChebyshevBound
import GaloisForLFunctions.PrimeExponentialSums.PrimeSumsByParts

/-!
# Route T for `χ` on blocks of primes

For a nonprincipal character `χ`, `θ > 2/3` and `A ≥ 0`, for all large `X`
(`exists_primeBlock_le`):

`‖Σ_{P < p ≤ Q} χ(p) p^{-1-iτ}‖ ≤ 1/(log X)^A`   for `|τ| ≤ X`, `P ≤ Q ≤ min(2P, X)`, `log P ≥ (log X)^θ`.

Abel summation against `w(n) = 1/(n log n)` (`PrimeExponentialSums.norm_sum_mul_le_of_partial`)
turns the twisted Chebyshev bound (`exists_twistedChebyshev_le`) into a bound for
`Σ_{P < n ≤ Q} χ(n)Λ(n)n^{-iτ} w(n)`: the bracket `|w(Q)| + Σ|Δw|` telescopes to `w(P)`
(`weight_telescope`).  On primes the summand is `χ(p)p^{-1-iτ}`; the proper prime powers cost
`(ψ(Q) − θ(Q)) w(P) ≤ 9/√P` (`norm_sum_nonprime_le`).
-/

open Complex Finset ArithmeticFunction Filter

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The Abel weight `w(n) = 1/(n log n)`. -/
def primeWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log n)

theorem primeWeight_pos {n : ℕ} (hn : 2 ≤ n) : 0 < primeWeight n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast hn
  have := Real.log_pos h1
  unfold primeWeight
  positivity

theorem primeWeight_anti {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    primeWeight n ≤ primeWeight m := by
  have hm1 : (1 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hlm : 0 < Real.log m := Real.log_pos hm1
  have hl : Real.log m ≤ Real.log n := Real.log_le_log (by linarith) hmn'
  unfold primeWeight
  exact one_div_le_one_div_of_le (by positivity) (mul_le_mul hmn' hl hlm.le (by linarith))

theorem sum_Ico_primeWeight_sub {P Q : ℕ} (hPQ : P ≤ Q) :
    ∑ n ∈ Ico P Q, (primeWeight n - primeWeight (n + 1)) = primeWeight P - primeWeight Q := by
  induction Q, hPQ using Nat.le_induction with
  | base => simp
  | succ Q hQ ih =>
    rw [sum_Ico_succ_top hQ, ih]
    ring

/-- **The Abel bracket telescopes.**  `|w(Q)| + Σ_{P ≤ n < Q} |w(n+1) − w(n)| = w(P)`. -/
theorem weight_telescope {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) :
    ‖((primeWeight Q : ℝ) : ℂ)‖
      + ∑ n ∈ Ico P Q, ‖((primeWeight (n + 1) : ℝ) : ℂ) - ((primeWeight n : ℝ) : ℂ)‖
      = primeWeight P := by
  have hterm : ∀ n ∈ Ico P Q,
      ‖((primeWeight (n + 1) : ℝ) : ℂ) - ((primeWeight n : ℝ) : ℂ)‖
        = primeWeight n - primeWeight (n + 1) := by
    intro n hn
    have hn2 : 2 ≤ n := le_trans hP (mem_Ico.mp hn).1
    have hle := primeWeight_anti hn2 (Nat.le_succ n)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  rw [sum_congr rfl hterm, sum_Ico_primeWeight_sub hPQ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (primeWeight_pos (le_trans hP hPQ))]
  ring

/-- On a prime: `χ(p)Λ(p)p^{-iτ} w(p) = χ(p)p^{-1-iτ}`. -/
theorem twistedVM_mul_primeWeight {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) {p : ℕ}
    (hp : p.Prime) :
    twistedVM χ τ p * ((primeWeight p : ℝ) : ℂ) = χ p * (p : ℂ) ^ (-(1 + (τ : ℂ) * I)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlog : Real.log p ≠ 0 := (Real.log_pos hp1).ne'
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlogC : ((Real.log p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  have hpow : (p : ℂ) ^ (-(1 + (τ : ℂ) * I)) = (p : ℂ) ^ (-((τ : ℂ) * I)) * (p : ℂ)⁻¹ := by
    rw [show -(1 + (τ : ℂ) * I) = -((τ : ℂ) * I) + (-1) by ring, Complex.cpow_add _ _ hp0,
      Complex.cpow_neg_one]
  rw [twistedVM, vonMangoldt_apply_prime hp, hpow, primeWeight]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]
  field_simp

/-- **The proper prime powers.** -/
theorem norm_sum_nonprime_le {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) {P Q : ℕ}
    (hP : 2 ≤ P) :
    ‖∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ)‖
      ≤ (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P := by
  calc ‖∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ)‖
      ≤ ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime),
          ‖twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), vonMangoldt n * primeWeight P := by
        refine sum_le_sum fun n hn => ?_
        have hnP : P < n := (mem_Ioc.mp (mem_filter.mp hn).1).1
        have hw := primeWeight_anti hP hnP.le
        have hw0 : 0 ≤ primeWeight n := (primeWeight_pos (by omega)).le
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
        have h1 := norm_twistedVM_le χ τ n
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg] at h1
        exact mul_le_mul h1 hw hw0 vonMangoldt_nonneg
    _ ≤ ∑ n ∈ (Ioc 0 Q).filter (fun n => ¬ n.Prime), vonMangoldt n * primeWeight P := by
        refine sum_le_sum_of_subset_of_nonneg
          (filter_subset_filter _ (Ioc_subset_Ioc_left (Nat.zero_le P))) fun n _ _ => ?_
        exact mul_nonneg vonMangoldt_nonneg (primeWeight_pos hP).le
    _ = (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P := by
        rw [← sum_mul, PrimeExponentialSums.sum_vonMangoldt_not_prime_eq]

/-- **Prime blocks from von Mangoldt partial sums.**  If `‖Σ_{P < n ≤ t} χ(n)Λ(n)n^{-iτ}‖ ≤ B`
on `[P, Q]`, then `‖Σ_{P < p ≤ Q} χ(p)p^{-1-iτ}‖ ≤ (B + ψ(Q) − θ(Q)) w(P)`. -/
theorem norm_sum_primeBlock_le {q : ℕ} (χ : DirichletCharacter ℂ q) (τ : ℝ) {P Q : ℕ}
    (hP : 2 ≤ P) (hPQ : P ≤ Q) {B : ℝ}
    (hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Ioc P t, twistedVM χ τ m‖ ≤ B) :
    ‖∑ p ∈ (Ioc P Q).filter Nat.Prime, χ p * (p : ℂ) ^ (-(1 + (τ : ℂ) * I))‖
      ≤ (B + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P := by
  have habel := PrimeExponentialSums.norm_sum_mul_le_of_partial (twistedVM χ τ)
    (fun n => ((primeWeight n : ℝ) : ℂ)) hPQ hB
  rw [weight_telescope hP hPQ] at habel
  have hsplit := sum_filter_add_sum_filter_not (Ioc P Q) Nat.Prime
    (fun n => twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ))
  have hprime : ∑ p ∈ (Ioc P Q).filter Nat.Prime, twistedVM χ τ p * ((primeWeight p : ℝ) : ℂ)
      = ∑ p ∈ (Ioc P Q).filter Nat.Prime, χ p * (p : ℂ) ^ (-(1 + (τ : ℂ) * I)) :=
    sum_congr rfl fun p hp => twistedVM_mul_primeWeight χ τ (mem_filter.mp hp).2
  rw [hprime] at hsplit
  have hnon := norm_sum_nonprime_le χ τ (Q := Q) hP
  have htri := norm_sub_le
    (∑ n ∈ Ioc P Q, twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ))
    (∑ n ∈ (Ioc P Q).filter (fun n => ¬ n.Prime), twistedVM χ τ n * ((primeWeight n : ℝ) : ℂ))
  rw [← hsplit, add_sub_cancel_right] at htri
  rw [← hsplit] at habel
  have e : (B + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P
      = B * primeWeight P + (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P := by ring
  rw [e]
  linarith

/-- `(ψ(Q) − θ(Q)) w(P) ≤ 9/√P` for `2 ≤ P ≤ Q ≤ 2P`. -/
theorem psi_sub_theta_mul_primeWeight_le {P Q : ℕ} (hP : 2 ≤ P) (hPQ : P ≤ Q) (hQ : Q ≤ 2 * P) :
    (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P ≤ 9 / Real.sqrt P := by
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPQ' : (P : ℝ) ≤ Q := by exact_mod_cast hPQ
  have hQ' : (Q : ℝ) ≤ 2 * P := by exact_mod_cast hQ
  have hQ1 : 1 ≤ Q := by omega
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := PrimeExponentialSums.psi_sub_theta_div_log_two_le hQ1
  have hpsi0 : 0 ≤ Chebyshev.psi Q - Chebyshev.theta Q := by
    rw [← PrimeExponentialSums.sum_vonMangoldt_not_prime_eq]
    exact sum_nonneg fun n _ => vonMangoldt_nonneg
  have hlogQ : Real.log Q ≤ 2 * Real.log P := by
    have h := Real.log_le_log (by linarith) (le_trans hQ' (by nlinarith : 2 * (P : ℝ) ≤ P ^ 2))
    rw [Real.log_pow] at h
    push_cast at h
    exact h
  have hsqrtQ : Real.sqrt Q ≤ 3 / 2 * Real.sqrt P := by
    rw [show (3 / 2 : ℝ) * Real.sqrt P = Real.sqrt (9 / 4 * P) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt (9 / 4) = 3 / 2 by
        rw [show (9 / 4 : ℝ) = (3 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr (by linarith)
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ1)
  have hpsi : Chebyshev.psi Q - Chebyshev.theta Q ≤ 9 * Real.sqrt P * Real.log P := by
    have h2 : Chebyshev.psi Q - Chebyshev.theta Q ≤ 3 * Real.sqrt Q * Real.log Q * Real.log 2 := by
      rw [div_le_iff₀ hlog20] at h1
      exact h1
    have h3 : 3 * Real.sqrt Q * Real.log Q * Real.log 2 ≤ 3 * Real.sqrt Q * Real.log Q := by
      have : 0 ≤ 3 * Real.sqrt Q * Real.log Q := by positivity
      nlinarith
    have h4 : 3 * Real.sqrt Q * Real.log Q ≤ 3 * (3 / 2 * Real.sqrt P) * (2 * Real.log P) :=
      mul_le_mul (by linarith) hlogQ hlogQ0 (by positivity)
    linarith
  have hsqsq : Real.sqrt P * Real.sqrt P = P := Real.mul_self_sqrt (by linarith)
  calc (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P
      ≤ (9 * Real.sqrt P * Real.log P) * primeWeight P :=
        mul_le_mul_of_nonneg_right hpsi (primeWeight_pos hP).le
    _ = 9 * Real.sqrt P / P := by
        rw [primeWeight]
        field_simp
    _ = 9 / Real.sqrt P := by
        rw [div_eq_div_iff (by linarith) hsP.ne', mul_assoc, hsqsq]

variable {q : ℕ} [NeZero q]

/-- **Route T for `χ` on prime blocks.**  For a nonprincipal character `χ`, `θ > 2/3` and `A ≥ 0`,
for all large `X`, every `|τ| ≤ X` and every `P ≤ Q ≤ min(2P, X)` with `log P ≥ (log X)^θ`:
`‖Σ_{P < p ≤ Q} χ(p)p^{-1-iτ}‖ ≤ 1/(log X)^A`. -/
theorem exists_primeBlock_le (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {θ A : ℝ}
    (hθ : 2 / 3 < θ) (hA : 0 ≤ A) :
    ∃ X₀ : ℝ, ∀ X : ℝ, X₀ ≤ X → ∀ τ : ℝ, |τ| ≤ X → ∀ P Q : ℕ,
      Real.log X ^ θ ≤ Real.log P → P ≤ Q → Q ≤ 2 * P → (Q : ℝ) ≤ X →
        ‖∑ p ∈ (Ioc P Q).filter Nat.Prime, χ p * (p : ℂ) ^ (-(1 + (τ : ℂ) * I))‖
          ≤ 1 / Real.log X ^ A := by
  obtain ⟨X₁, hX₁⟩ := exists_twistedChebyshev_le χ hχ hθ (A := A + 1) (by linarith)
  have hev : ∀ᶠ ℓ : ℝ in atTop, 6 ≤ ℓ ∧
      18 * ℓ ^ A * Real.exp (-((1 / 2) * ℓ ^ θ)) ≤ 1 ∧ 1 ≤ ℓ ^ θ :=
    (eventually_ge_atTop 6).and ((eventually_mul_rpow_mul_exp_le_one (κ := 1 / 2) (η := θ)
      (K := 18) (p := A) (by norm_num) (by linarith) (by norm_num) hA).and
      ((tendsto_rpow_atTop (by linarith : (0 : ℝ) < θ)).eventually_ge_atTop 1))
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (Real.tendsto_log_atTop.eventually hev)
  refine ⟨max (max X₁ X₂) 1, fun X hX τ hτ P Q hlogP hPQ hQP hQX => ?_⟩
  have hX1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X₂ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  obtain ⟨hℓ6, hexp, hℓθ1⟩ := hX₂ X hX2
  set ℓ : ℝ := Real.log X with hℓdef
  have hℓ0 : 0 < ℓ := by linarith
  -- `P ≥ 2`
  have hlogP1 : 1 ≤ Real.log P := le_trans hℓθ1 hlogP
  have hP : 2 ≤ P := by
    by_contra h
    have h01 : P = 0 ∨ P = 1 := by omega
    rcases h01 with h0 | h0 <;> rw [h0] at hlogP1 <;> norm_num at hlogP1
  have hP2 : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hPX : (P : ℝ) ≤ X := le_trans (by exact_mod_cast hPQ) hQX
  -- partial sums on `[P, Q]`
  have hS : ∀ t : ℕ, P ≤ t → t ≤ Q →
      ‖∑ n ∈ Finset.Icc 1 t, twistedVM χ τ n‖ ≤ t / ℓ ^ (A + 1) := by
    intro t hPt htQ
    refine hX₁ X hX1 τ hτ t (le_trans hlogP (Real.log_le_log (by linarith) (by exact_mod_cast hPt)))
      (le_trans (by exact_mod_cast htQ) hQX)
  have hIoc : ∀ t : ℕ, P ≤ t → ∑ m ∈ Ioc P t, twistedVM χ τ m
      = ∑ n ∈ Finset.Icc 1 t, twistedVM χ τ n - ∑ n ∈ Finset.Icc 1 P, twistedVM χ τ n := by
    intro t hPt
    have e1 : Finset.Icc 1 t = Finset.Ioc 0 t := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    have e2 : Finset.Icc 1 P = Finset.Ioc 0 P := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e1, e2, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le P) hPt]
    ring
  have hB : ∀ t, P ≤ t → t ≤ Q → ‖∑ m ∈ Ioc P t, twistedVM χ τ m‖ ≤ (3 * P) / ℓ ^ (A + 1) := by
    intro t hPt htQ
    rw [hIoc t hPt]
    have h1 := hS t hPt htQ
    have h2 := hS P le_rfl hPQ
    have hL : 0 < ℓ ^ (A + 1) := Real.rpow_pos_of_pos hℓ0 _
    have htQ' : (t : ℝ) ≤ 2 * P := by exact_mod_cast le_trans htQ hQP
    calc ‖∑ n ∈ Finset.Icc 1 t, twistedVM χ τ n - ∑ n ∈ Finset.Icc 1 P, twistedVM χ τ n‖
        ≤ t / ℓ ^ (A + 1) + P / ℓ ^ (A + 1) := le_trans (norm_sub_le _ _) (add_le_add h1 h2)
      _ = (t + P) / ℓ ^ (A + 1) := by ring
      _ ≤ (3 * P) / ℓ ^ (A + 1) := div_le_div_of_nonneg_right (by linarith) hL.le
  have hblock := norm_sum_primeBlock_le χ τ hP hPQ hB
  have hpp := psi_sub_theta_mul_primeWeight_le hP hPQ hQP
  -- the Abel term
  have hLA : 0 < ℓ ^ A := Real.rpow_pos_of_pos hℓ0 A
  have hA1 : ℓ ^ (A + 1) = ℓ ^ A * ℓ := Real.rpow_add_one hℓ0.ne' A
  have hw : primeWeight P ≤ 1 / P := by
    unfold primeWeight
    have : (P : ℝ) ≤ P * Real.log P := le_mul_of_one_le_right (by linarith) hlogP1
    exact one_div_le_one_div_of_le (by linarith) this
  have hterm1 : (3 * P) / ℓ ^ (A + 1) * primeWeight P ≤ 1 / (2 * ℓ ^ A) := by
    have h1 : (3 * P) / ℓ ^ (A + 1) * primeWeight P ≤ (3 * P) / ℓ ^ (A + 1) * (1 / P) :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    have h2 : (3 * P) / ℓ ^ (A + 1) * (1 / P) = 3 / (ℓ ^ A * ℓ) := by
      rw [hA1]; field_simp
    have h3 : 3 / (ℓ ^ A * ℓ) ≤ 1 / (2 * ℓ ^ A) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  -- the prime powers
  have hsqrtP : 18 * ℓ ^ A ≤ Real.sqrt P := by
    have hsq : Real.sqrt P = Real.exp (Real.log P / 2) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by linarith)]
      congr 1
      ring
    have h1 : 18 * ℓ ^ A ≤ Real.exp ((1 / 2) * ℓ ^ θ) := by
      have hE := Real.exp_pos ((1 / 2) * ℓ ^ θ)
      have hid : 18 * ℓ ^ A
          = 18 * ℓ ^ A * Real.exp (-((1 / 2) * ℓ ^ θ)) * Real.exp ((1 / 2) * ℓ ^ θ) := by
        rw [mul_assoc (18 * ℓ ^ A), ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      rw [hid]
      calc 18 * ℓ ^ A * Real.exp (-((1 / 2) * ℓ ^ θ)) * Real.exp ((1 / 2) * ℓ ^ θ)
          ≤ 1 * Real.exp ((1 / 2) * ℓ ^ θ) := mul_le_mul_of_nonneg_right hexp hE.le
        _ = Real.exp ((1 / 2) * ℓ ^ θ) := one_mul _
    rw [hsq]
    exact le_trans h1 (Real.exp_le_exp.mpr (by linarith))
  have hterm2 : 9 / Real.sqrt P ≤ 1 / (2 * ℓ ^ A) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have htotal : (3 * P / ℓ ^ (A + 1) + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P
      ≤ 1 / ℓ ^ A := by
    have e : (3 * P / ℓ ^ (A + 1) + (Chebyshev.psi Q - Chebyshev.theta Q)) * primeWeight P
        = 3 * P / ℓ ^ (A + 1) * primeWeight P
          + (Chebyshev.psi Q - Chebyshev.theta Q) * primeWeight P := by ring
    have e2 : 1 / (2 * ℓ ^ A) + 1 / (2 * ℓ ^ A) = 1 / ℓ ^ A := by field_simp; ring
    rw [e]
    linarith
  exact le_trans hblock htotal

end

end GaloisForLFunctions.MatomakiRadziwill
