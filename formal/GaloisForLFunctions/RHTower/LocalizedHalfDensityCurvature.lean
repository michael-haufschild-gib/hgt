import Mathlib

/-!
# The forced half-density normalization of the Möbius boundary germ

For a real parameter `a` the `a`-twisted Möbius boundary germ is `b^{(a)}_σ(n) = n^{aσ} b_σ(n)`
with `b_σ(n) = ∑_{d ∣ n} μ(d) d^{-σ}`.  Its second jet at `σ = 0` is the finite identity

```text
∑_{d ∣ n} μ(d) (a log n − log d)² = (Λ ⍟ Λ)(n) + (2a − 1) Λ(n) log n ,
```

so the pure von Mangoldt self-convolution is reached exactly at the half-density twist `a = 1/2`.
The proof is the Leibniz rule for the logarithmic derivation `D f = f · log` on the Dirichlet
convolution ring, applied twice to `μ ⍟ ζ = 1`.

Unique factorization then classifies every twisted product fibre `C_t = Λ_t ⍟ Λ_{-t}` completely:
a layer with three distinct prime divisors carries no mass, a two-prime layer `p^a q^b` carries
exactly two reinforcing orientations and one real cosine mode, and a one-prime layer `p^k` carries
the Chebyshev polynomial `U_{k-2}` of the second kind in `cos(t log p)`.  Against the centred
triangular fixed-ratio kernel the two-prime layer changes sign exactly at the ratio threshold
`c(1 - c/A)`.
-/

open ArithmeticFunction Finset

open scoped ArithmeticFunction

namespace RHTower

noncomputable section

/-- The logarithmic derivation `D f = f · log` on arithmetic functions. -/
def logDerivation (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul f ArithmeticFunction.log

theorem logDerivation_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    logDerivation f n = f n * Real.log n := by
  rw [logDerivation, ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]

theorem logDerivation_neg (f : ArithmeticFunction ℝ) :
    logDerivation (-f) = -logDerivation f := by
  ext n
  rw [logDerivation_apply, ArithmeticFunction.neg_apply, ArithmeticFunction.neg_apply,
    logDerivation_apply]
  ring

/-- **The Leibniz rule for the logarithmic derivation.** -/
theorem logDerivation_mul (f g : ArithmeticFunction ℝ) :
    logDerivation (f * g) = logDerivation f * g + f * logDerivation g := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : n ≠ 0 := by omega
    rw [logDerivation_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
      ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hpn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : p.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hpn
      exact hn0 hpn.symm
    have hp2 : p.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hpn
      exact hn0 hpn.symm
    rw [logDerivation_apply, logDerivation_apply, ← hpn]
    push_cast
    rw [Real.log_mul (by exact_mod_cast hp1) (by exact_mod_cast hp2)]
    ring

theorem logDerivation_zeta :
    logDerivation ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      = ArithmeticFunction.log := by
  ext n
  rw [logDerivation_apply, ArithmeticFunction.natCoe_apply, ArithmeticFunction.log_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ArithmeticFunction.zeta_apply_ne (by omega)]
    push_cast
    ring

theorem logDerivation_one : logDerivation (1 : ArithmeticFunction ℝ) = 0 := by
  ext n
  rw [logDerivation_apply, ArithmeticFunction.zero_apply]
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · rw [ArithmeticFunction.one_apply_ne hn]
    ring

/-- `μ ⍟ log = Λ`. -/
theorem coe_moebius_mul_log :
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ArithmeticFunction.log = Λ := by
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta, ← mul_assoc,
    mul_comm ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) Λ,
    mul_assoc, ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]

/-- **Equation (2), first jet.**  `(D μ) ⍟ ζ = −Λ`. -/
theorem logDerivation_moebius_mul_zeta :
    logDerivation ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) = -Λ := by
  have h := congrArg logDerivation
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))
  rw [logDerivation_mul, logDerivation_zeta, logDerivation_one] at h
  have h2 : logDerivation
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      = -(((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ArithmeticFunction.log) := by
    linear_combination h
  rw [h2, coe_moebius_mul_log]

/-- **Equation (2), second jet.**  `(D² μ) ⍟ ζ = Λ ⍟ Λ − Λ·log`. -/
theorem logDerivation_sq_moebius_mul_zeta :
    logDerivation (logDerivation
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ))
        * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
      = Λ * Λ - ArithmeticFunction.pmul Λ ArithmeticFunction.log := by
  have h := congrArg logDerivation logDerivation_moebius_mul_zeta
  rw [logDerivation_mul, logDerivation_zeta, logDerivation_neg] at h
  have hcross : logDerivation
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)
        * ArithmeticFunction.log = -(Λ * Λ) := by
    rw [← ArithmeticFunction.vonMangoldt_mul_zeta, ← mul_assoc,
      mul_comm (logDerivation
        ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) Λ,
      mul_assoc, logDerivation_moebius_mul_zeta]
    ring
  rw [hcross] at h
  have hLam : logDerivation Λ = ArithmeticFunction.pmul Λ ArithmeticFunction.log := rfl
  rw [hLam] at h
  linear_combination h


/-! ## Equations (3)--(4): the forced half-density normalization -/

theorem real_mul_coe_zeta_apply (f : ArithmeticFunction ℝ) {n : ℕ} (hn : n ≠ 0) :
    (f * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n
      = ∑ d ∈ n.divisors, f d := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d e => f d
      * ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) e)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hne : n / d ≠ 0 := by
    have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) hd0
    omega
  rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply_ne hne]
  push_cast
  ring

theorem sum_divisors_moebiusCast {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
      = (1 : ArithmeticFunction ℝ) n := by
  have h := real_mul_coe_zeta_apply
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) hn
  rw [ArithmeticFunction.coe_moebius_mul_coe_zeta] at h
  rw [h]
  exact Finset.sum_congr rfl fun d _ => ArithmeticFunction.intCoe_apply.symm

theorem sum_divisors_moebius_mul_log {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d = -Λ n := by
  have h := real_mul_coe_zeta_apply (logDerivation
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ)) hn
  rw [logDerivation_moebius_mul_zeta, ArithmeticFunction.neg_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun d _ => by
    rw [logDerivation_apply, ArithmeticFunction.intCoe_apply]

theorem sum_divisors_moebius_mul_log_sq {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Real.log d) ^ 2
      = (Λ * Λ) n - Λ n * Real.log n := by
  have h := real_mul_coe_zeta_apply (logDerivation (logDerivation
    ((ArithmeticFunction.moebius : ArithmeticFunction ℤ) : ArithmeticFunction ℝ))) hn
  rw [logDerivation_sq_moebius_mul_zeta] at h
  have hval : (Λ * Λ - ArithmeticFunction.pmul Λ ArithmeticFunction.log) n
      = (Λ * Λ) n - Λ n * Real.log n := by
    rw [sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply,
      ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]
    ring
  rw [hval] at h
  rw [h]
  exact Finset.sum_congr rfl fun d _ => by
    rw [logDerivation_apply, logDerivation_apply, ArithmeticFunction.intCoe_apply]
    ring

theorem one_apply_mul_log_sq (n : ℕ) :
    (1 : ArithmeticFunction ℝ) n * (Real.log n) ^ 2 = 0 := by
  rcases eq_or_ne n 1 with rfl | hn
  · simp
  · rw [ArithmeticFunction.one_apply_ne hn]
    ring

/-- **Equation (3).**  The exact second jet of the `a`-twisted Möbius boundary germ. -/
theorem sum_divisors_moebius_twisted_sq (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (a * Real.log n - Real.log d) ^ 2
      = (Λ * Λ) n + (2 * a - 1) * Λ n * Real.log n := by
  have hexp : ∀ d ∈ n.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (a * Real.log n - Real.log d) ^ 2
        = (a * Real.log n) ^ 2 * ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          - 2 * (a * Real.log n) * (((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d)
          + ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Real.log d) ^ 2 := by
    intro d _
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_divisors_moebiusCast hn,
    sum_divisors_moebius_mul_log hn, sum_divisors_moebius_mul_log_sq hn]
  have hzero : (a * Real.log n) ^ 2 * (1 : ArithmeticFunction ℝ) n = 0 := by
    have hone := one_apply_mul_log_sq n
    calc (a * Real.log n) ^ 2 * (1 : ArithmeticFunction ℝ) n
        = a ^ 2 * ((1 : ArithmeticFunction ℝ) n * (Real.log n) ^ 2) := by ring
      _ = 0 := by rw [hone]; ring
  rw [hzero]
  ring

theorem vonMangoldt_selfConv_two : (Λ * Λ) 2 = 0 := by
  rw [ArithmeticFunction.mul_apply]
  rw [show (2 : ℕ).divisorsAntidiagonal = {(1, 2), (2, 1)} by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ArithmeticFunction.vonMangoldt_apply_one]
  ring

/-- **Equation (4).**  The half-density twist `a = 1/2` is the unique normalization whose second
jet is the pure von Mangoldt self-convolution. -/
theorem twisted_second_jet_eq_selfConv_iff (a : ℝ) :
    (∀ n : ℕ, n ≠ 0 → ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (a * Real.log n - Real.log d) ^ 2
      = (Λ * Λ) n) ↔ a = 1 / 2 := by
  constructor
  · intro h
    have h2 := h 2 (by norm_num)
    rw [sum_divisors_moebius_twisted_sq a (by norm_num)] at h2
    have hL : Λ 2 = Real.log 2 := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      norm_num
    have hcast : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
    rw [hL, hcast] at h2
    have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hkey : (2 * a - 1) * (Real.log 2 * Real.log 2) = 0 := by linarith
    have hne : Real.log 2 * Real.log 2 ≠ 0 := by positivity
    rcases mul_eq_zero.mp hkey with h' | h'
    · linarith
    · exact absurd h' hne
  · rintro rfl
    intro n hn
    rw [sum_divisors_moebius_twisted_sq _ hn]
    ring


/-! ## Equations (5)--(7): the half-density jets -/

/-- **Equation (7), first jet.**  `e'_0 = Λ`. -/
theorem sum_divisors_moebius_half {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (Real.log m / 2 - Real.log d) = Λ m := by
  have hexp : ∀ d ∈ m.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Real.log m / 2 - Real.log d)
        = (Real.log m / 2) * ((ArithmeticFunction.moebius d : ℤ) : ℝ)
          - ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log d := by
    intro d _
    ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_divisors_moebiusCast hm, sum_divisors_moebius_mul_log hm]
  have hzero : Real.log m / 2 * (1 : ArithmeticFunction ℝ) m = 0 := by
    rcases eq_or_ne m 1 with rfl | hm1
    · simp
    · rw [ArithmeticFunction.one_apply_ne hm1]
      ring
  rw [hzero]
  ring

/-- **Equation (7), second jet.**  `e''_0 = Λ ⍟ Λ`. -/
theorem sum_divisors_moebius_half_sq {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℝ)
        * (Real.log m / 2 - Real.log d) ^ 2 = (Λ * Λ) m := by
  have h := sum_divisors_moebius_twisted_sq (1 / 2 : ℝ) hm
  have hcongr : ∀ d ∈ m.divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((1 / 2 : ℝ) * Real.log m - Real.log d) ^ 2
        = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * (Real.log m / 2 - Real.log d) ^ 2 := by
    intro d _
    ring
  rw [Finset.sum_congr rfl hcongr] at h
  rw [h]
  ring

/-! ## Equations (8)--(10): the localized boundary curvature -/

/-- The antidiagonal `ε`-collapse: only the factorization `(R, 1)` survives. -/
theorem sum_antidiagonal_one_right {R : ℕ} (hR : R ≠ 0) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ R.divisorsAntidiagonal, f p.1 p.2 * (1 : ArithmeticFunction ℝ) p.2 = f R 1 := by
  classical
  rw [Nat.sum_divisorsAntidiagonal
    (fun d e => f d e * (1 : ArithmeticFunction ℝ) e)]
  rw [Finset.sum_eq_single R]
  · rw [Nat.div_self (Nat.pos_of_ne_zero hR)]
    simp
  · intro d hd hne
    have hdvd : d ∣ R := Nat.dvd_of_mem_divisors hd
    have hRd : R / d ≠ 1 := by
      intro hcon
      apply hne
      have h1 := Nat.div_mul_cancel hdvd
      rw [hcon, one_mul] at h1
      exact h1
    rw [ArithmeticFunction.one_apply_ne hRd, mul_zero]
  · intro hR'
    exact absurd (Nat.mem_divisors_self R hR) hR'

theorem sum_antidiagonal_one_left {R : ℕ} (hR : R ≠ 0) (f : ℕ → ℕ → ℝ) :
    ∑ p ∈ R.divisorsAntidiagonal, (1 : ArithmeticFunction ℝ) p.1 * f p.1 p.2 = f 1 R := by
  classical
  rw [Nat.sum_divisorsAntidiagonal
    (fun d e => (1 : ArithmeticFunction ℝ) d * f d e)]
  rw [Finset.sum_eq_single 1]
  · simp
  · intro d hd hne
    rw [ArithmeticFunction.one_apply_ne hne, zero_mul]
  · intro hR'
    exact absurd (Nat.one_mem_divisors.mpr hR) hR'

/-- **Equation (10).**  The exact localized boundary curvature of the half-density fibre: the
second jet is the localized von Mangoldt pair sum minus the two trivial endpoint
factorizations. -/
theorem fibre_second_jet {R : ℕ} (hR : R ≠ 0) (W : ℝ → ℝ) (hW : ∀ x : ℝ, W (-x) = W x) :
    -(1 / 2 : ℝ) * ∑ p ∈ R.divisorsAntidiagonal,
        (∑ d ∈ p.1.divisors, ∑ e ∈ p.2.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
            * ((Real.log p.1 / 2 - Real.log d) - (Real.log p.2 / 2 - Real.log e)) ^ 2)
          * W (Real.log p.1 - Real.log p.2)
      = (∑ p ∈ R.divisorsAntidiagonal, Λ p.1 * Λ p.2 * W (Real.log p.1 - Real.log p.2))
        - (Λ * Λ) R * W (Real.log R) := by
  classical
  have hinner : ∀ p ∈ R.divisorsAntidiagonal,
      (∑ d ∈ p.1.divisors, ∑ e ∈ p.2.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
            * ((Real.log p.1 / 2 - Real.log d) - (Real.log p.2 / 2 - Real.log e)) ^ 2)
        = (Λ * Λ) p.1 * (1 : ArithmeticFunction ℝ) p.2
          - 2 * (Λ p.1 * Λ p.2)
          + (1 : ArithmeticFunction ℝ) p.1 * (Λ * Λ) p.2 := by
    intro p hp
    obtain ⟨hpR, hR0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : p.1 ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hpR
      exact hR0 hpR.symm
    have hp2 : p.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hpR
      exact hR0 hpR.symm
    have hexp : ∀ d ∈ p.1.divisors, ∀ e ∈ p.2.divisors,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
            * ((Real.log p.1 / 2 - Real.log d) - (Real.log p.2 / 2 - Real.log e)) ^ 2
          = (((ArithmeticFunction.moebius d : ℤ) : ℝ)
                * (Real.log p.1 / 2 - Real.log d) ^ 2)
              * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
            - 2 * (((ArithmeticFunction.moebius d : ℤ) : ℝ)
                * (Real.log p.1 / 2 - Real.log d))
              * (((ArithmeticFunction.moebius e : ℤ) : ℝ)
                * (Real.log p.2 / 2 - Real.log e))
            + ((ArithmeticFunction.moebius d : ℤ) : ℝ)
              * (((ArithmeticFunction.moebius e : ℤ) : ℝ)
                * (Real.log p.2 / 2 - Real.log e) ^ 2) := by
      intro d _ e _
      ring
    calc (∑ d ∈ p.1.divisors, ∑ e ∈ p.2.divisors,
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
              * ((Real.log p.1 / 2 - Real.log d) - (Real.log p.2 / 2 - Real.log e)) ^ 2)
        = ∑ d ∈ p.1.divisors, ∑ e ∈ p.2.divisors,
            ((((ArithmeticFunction.moebius d : ℤ) : ℝ)
                * (Real.log p.1 / 2 - Real.log d) ^ 2)
              * ((ArithmeticFunction.moebius e : ℤ) : ℝ)
            - 2 * (((ArithmeticFunction.moebius d : ℤ) : ℝ)
                * (Real.log p.1 / 2 - Real.log d))
              * (((ArithmeticFunction.moebius e : ℤ) : ℝ)
                * (Real.log p.2 / 2 - Real.log e))
            + ((ArithmeticFunction.moebius d : ℤ) : ℝ)
              * (((ArithmeticFunction.moebius e : ℤ) : ℝ)
                * (Real.log p.2 / 2 - Real.log e) ^ 2)) :=
          Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => hexp d hd e he
      _ = (Λ * Λ) p.1 * (1 : ArithmeticFunction ℝ) p.2 - 2 * (Λ p.1 * Λ p.2)
            + (1 : ArithmeticFunction ℝ) p.1 * (Λ * Λ) p.2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
            ← Finset.mul_sum]
          rw [sum_divisors_moebius_half_sq hp1, sum_divisors_moebius_half_sq hp2,
            sum_divisors_moebius_half hp1, sum_divisors_moebius_half hp2,
            sum_divisors_moebiusCast hp1, sum_divisors_moebiusCast hp2]
          ring
  rw [Finset.sum_congr rfl (fun p hp => by rw [hinner p hp])]
  have hsplit : ∀ p ∈ R.divisorsAntidiagonal,
      ((Λ * Λ) p.1 * (1 : ArithmeticFunction ℝ) p.2 - 2 * (Λ p.1 * Λ p.2)
          + (1 : ArithmeticFunction ℝ) p.1 * (Λ * Λ) p.2)
        * W (Real.log p.1 - Real.log p.2)
      = ((Λ * Λ) p.1 * W (Real.log p.1 - Real.log p.2)) * (1 : ArithmeticFunction ℝ) p.2
        - 2 * (Λ p.1 * Λ p.2 * W (Real.log p.1 - Real.log p.2))
        + (1 : ArithmeticFunction ℝ) p.1
          * ((Λ * Λ) p.2 * W (Real.log p.1 - Real.log p.2)) := by
    intro p _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum,
    sum_antidiagonal_one_right hR (fun m n => (Λ * Λ) m * W (Real.log m - Real.log n)),
    sum_antidiagonal_one_left hR (fun m n => (Λ * Λ) n * W (Real.log m - Real.log n))]
  have hlog1 : Real.log ((1 : ℕ) : ℝ) = 0 := by norm_num
  rw [hlog1]
  have hneg : W (0 - Real.log R) = W (Real.log R) := by
    have := hW (Real.log R)
    rw [zero_sub]
    exact this
  rw [hneg, sub_zero]
  ring


/-! ## Equations (11) and (22)--(23): the fixed-ratio kernel and its sharp sign chambers -/

/-- The triangular fixed-ratio kernel `T_c(x) = (c − |x|)₊`, equation (11). -/
def triangularKernel (c x : ℝ) : ℝ := max (c - |x|) 0

/-- The centred interior kernel `K^int_{A,c}(x) = T_c(x) − c²/A`, equation (11). -/
def centredTriangularKernel (A c x : ℝ) : ℝ := triangularKernel c x - c ^ 2 / A

theorem triangularKernel_even (c x : ℝ) : triangularKernel c (-x) = triangularKernel c x := by
  rw [triangularKernel, triangularKernel, abs_neg]

theorem centredTriangularKernel_even (A c x : ℝ) :
    centredTriangularKernel A c (-x) = centredTriangularKernel A c x := by
  rw [centredTriangularKernel, centredTriangularKernel, triangularKernel_even]

theorem triangularKernel_eq_zero_of_le {c x : ℝ} (h : c ≤ |x|) : triangularKernel c x = 0 := by
  rw [triangularKernel, max_eq_right (by linarith)]

/-- **Equation (23), positive chamber.** -/
theorem centredTriangularKernel_pos_iff {A c x : ℝ} (hc : 0 < c) (hcA : c < A) :
    0 < centredTriangularKernel A c x ↔ |x| < c * (1 - c / A) := by
  have hA : (0 : ℝ) < A := lt_trans hc hcA
  have hquot : c ^ 2 / A > 0 := by positivity
  have hthr : c * (1 - c / A) = c - c ^ 2 / A := by
    field_simp
  rw [centredTriangularKernel, triangularKernel, hthr]
  constructor
  · intro h
    by_cases hx : |x| < c
    · rw [max_eq_left (by linarith)] at h
      linarith
    · rw [max_eq_right (by linarith [not_lt.mp hx])] at h
      linarith
  · intro h
    have hx : |x| < c := by
      have : c ^ 2 / A > 0 := hquot
      linarith
    rw [max_eq_left (by linarith)]
    linarith

/-- **Equation (23), zero chamber.** -/
theorem centredTriangularKernel_eq_zero_iff {A c x : ℝ} (hc : 0 < c) (hcA : c < A) :
    centredTriangularKernel A c x = 0 ↔ |x| = c * (1 - c / A) := by
  have hA : (0 : ℝ) < A := lt_trans hc hcA
  have hquot : c ^ 2 / A > 0 := by positivity
  have hthr : c * (1 - c / A) = c - c ^ 2 / A := by
    field_simp
  rw [centredTriangularKernel, triangularKernel, hthr]
  constructor
  · intro h
    by_cases hx : |x| < c
    · rw [max_eq_left (by linarith)] at h
      linarith
    · rw [max_eq_right (by linarith [not_lt.mp hx])] at h
      linarith
  · intro h
    have hx : |x| < c := by linarith
    rw [max_eq_left (by linarith)]
    linarith

/-- **Equation (23), negative chamber.** -/
theorem centredTriangularKernel_neg_iff {A c x : ℝ} (hc : 0 < c) (hcA : c < A) :
    centredTriangularKernel A c x < 0 ↔ c * (1 - c / A) < |x| := by
  have hpos := centredTriangularKernel_pos_iff (A := A) (c := c) (x := x) hc hcA
  have hzero := centredTriangularKernel_eq_zero_iff (A := A) (c := c) (x := x) hc hcA
  constructor
  · intro h
    rcases lt_trichotomy (c * (1 - c / A)) |x| with h1 | h1 | h1
    · exact h1
    · exact absurd (hzero.mpr h1.symm) (by linarith)
    · exact absurd (hpos.mpr h1) (by linarith)
  · intro h
    rcases lt_trichotomy (centredTriangularKernel A c x) 0 with h1 | h1 | h1
    · exact h1
    · exact absurd (hzero.mp h1) (by linarith)
    · exact absurd (hpos.mp h1) (by linarith)


/-! ## Equations (17)--(18): the twisted product fibre and its three-prime vanishing -/

/-- The twisted von Mangoldt function `Λ_t(n) = Λ(n)·n^{it}`, equation (17). -/
def twistedVonMangoldt (t : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun n => (Λ n : ℂ) * (n : ℂ) ^ (Complex.I * (t : ℂ)), by
    simp⟩

theorem twistedVonMangoldt_apply (t : ℝ) (n : ℕ) :
    twistedVonMangoldt t n = (Λ n : ℂ) * (n : ℂ) ^ (Complex.I * (t : ℂ)) := rfl

theorem twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero {t : ℝ} {n : ℕ} (h : Λ n = 0) :
    twistedVonMangoldt t n = 0 := by
  rw [twistedVonMangoldt_apply, h]
  simp

/-- The twisted product fibre `C_t(R) = (Λ_t ⍟ Λ_{-t})(R)`, equation (17). -/
def twistedFibre (t : ℝ) : ArithmeticFunction ℂ :=
  twistedVonMangoldt t * twistedVonMangoldt (-t)

/-- **Equation (18).**  A product layer with at least three distinct prime divisors carries no
twisted von Mangoldt mass at all. -/
theorem twistedFibre_eq_zero_of_three_le_card_primeFactors {t : ℝ} {R : ℕ}
    (h : 3 ≤ R.primeFactors.card) : twistedFibre t R = 0 := by
  classical
  rw [twistedFibre, ArithmeticFunction.mul_apply]
  refine Finset.sum_eq_zero fun p hp => ?_
  obtain ⟨hpR, hR0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases h1 : Λ p.1 = 0
  · rw [twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero h1, zero_mul]
  by_cases h2 : Λ p.2 = 0
  · rw [twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero h2, mul_zero]
  exfalso
  have hpp1 : IsPrimePow p.1 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1
  have hpp2 : IsPrimePow p.2 := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2
  have hc1 : p.1.primeFactors.card = 1 := isPrimePow_iff_card_primeFactors_eq_one.mp hpp1
  have hc2 : p.2.primeFactors.card = 1 := isPrimePow_iff_card_primeFactors_eq_one.mp hpp2
  have hn1 : p.1 ≠ 0 := by
    rintro hz
    rw [hz, zero_mul] at hpR
    exact hR0 hpR.symm
  have hn2 : p.2 ≠ 0 := by
    rintro hz
    rw [hz, mul_zero] at hpR
    exact hR0 hpR.symm
  have hunion : R.primeFactors = p.1.primeFactors ∪ p.2.primeFactors := by
    rw [← hpR, Nat.primeFactors_mul hn1 hn2]
  have hcard : R.primeFactors.card ≤ 2 := by
    rw [hunion]
    calc (p.1.primeFactors ∪ p.2.primeFactors).card
        ≤ p.1.primeFactors.card + p.2.primeFactors.card := Finset.card_union_le _ _
      _ = 2 := by rw [hc1, hc2]
  omega


/-! ## Equation (19): the two-prime product fibre -/

/-- Unique factorization orients a two-prime product layer: the only factorizations of
`p^a q^b` into two prime powers are the two trivial orientations. -/
theorem primePow_pair_of_semiprimePower {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {d e : ℕ} (hde : d * e = p ^ a * q ^ b)
    (hd : IsPrimePow d) (he : IsPrimePow e) :
    (d = p ^ a ∧ e = q ^ b) ∨ (d = q ^ b ∧ e = p ^ a) := by
  obtain ⟨r, i, hr, hi, hrd⟩ := hd
  obtain ⟨s, j, hs, hj, hse⟩ := he
  have hrp : r.Prime := Nat.prime_iff.mpr hr
  have hsp : s.Prime := Nat.prime_iff.mpr hs
  have hfac : Finsupp.single r i + Finsupp.single s j
      = Finsupp.single p a + Finsupp.single q b := by
    have h1 : (r ^ i * s ^ j).factorization = (p ^ a * q ^ b).factorization := by
      rw [hrd, hse, hde]
    rwa [Nat.factorization_mul (pow_ne_zero _ hrp.ne_zero) (pow_ne_zero _ hsp.ne_zero),
      Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
      hrp.factorization_pow, hsp.factorization_pow, hp.factorization_pow,
      hq.factorization_pow] at h1
  have heval : ∀ t : ℕ, (if r = t then i else 0) + (if s = t then j else 0)
      = (if p = t then a else 0) + (if q = t then b else 0) := by
    intro t
    have := congrArg (fun f : ℕ →₀ ℕ => f t) hfac
    simpa [Finsupp.single_apply] using this
  have hrmem : r = p ∨ r = q := by
    by_contra hcon
    push Not at hcon
    have h := heval r
    have hpr : ¬ (p = r) := fun hx => hcon.1 hx.symm
    have hqr : ¬ (q = r) := fun hx => hcon.2 hx.symm
    rw [if_pos rfl, if_neg hpr, if_neg hqr] at h
    omega
  have hsmem : s = p ∨ s = q := by
    by_contra hcon
    push Not at hcon
    have h := heval s
    have hps : ¬ (p = s) := fun hx => hcon.1 hx.symm
    have hqs : ¬ (q = s) := fun hx => hcon.2 hx.symm
    rw [if_pos rfl, if_neg hps, if_neg hqs] at h
    omega
  rcases hrmem with hrp' | hrq'
  · rcases hsmem with hsp' | hsq'
    · exfalso
      have h := heval q
      have h1 : ¬ (r = q) := by rw [hrp']; exact hpq
      have h2 : ¬ (s = q) := by rw [hsp']; exact hpq
      have h3 : ¬ (p = q) := hpq
      rw [if_neg h1, if_neg h2, if_neg h3, if_pos rfl] at h
      omega
    · left
      have hpa := heval p
      have h2 : ¬ (s = p) := by rw [hsq']; exact Ne.symm hpq
      have h3 : ¬ (q = p) := Ne.symm hpq
      rw [if_pos hrp', if_neg h2, if_pos rfl, if_neg h3] at hpa
      have hqb := heval q
      have h4 : ¬ (r = q) := by rw [hrp']; exact hpq
      have h5 : ¬ (p = q) := hpq
      rw [if_neg h4, if_pos hsq', if_neg h5, if_pos rfl] at hqb
      refine ⟨?_, ?_⟩
      · have hia : i = a := by omega
        rw [← hrd, hrp', hia]
      · have hjb : j = b := by omega
        rw [← hse, hsq', hjb]
  · rcases hsmem with hsp' | hsq'
    · right
      have hqb := heval q
      have h2 : ¬ (s = q) := by rw [hsp']; exact hpq
      have h3 : ¬ (p = q) := hpq
      rw [if_pos hrq', if_neg h2, if_neg h3, if_pos rfl] at hqb
      have hpa := heval p
      have h4 : ¬ (r = p) := by rw [hrq']; exact Ne.symm hpq
      have h5 : ¬ (q = p) := Ne.symm hpq
      rw [if_neg h4, if_pos hsp', if_pos rfl, if_neg h5] at hpa
      refine ⟨?_, ?_⟩
      · have hib : i = b := by omega
        rw [← hrd, hrq', hib]
      · have hja : j = a := by omega
        rw [← hse, hsp', hja]
    · exfalso
      have h := heval p
      have h1 : ¬ (r = p) := by rw [hrq']; exact Ne.symm hpq
      have h2 : ¬ (s = p) := by rw [hsq']; exact Ne.symm hpq
      have h3 : ¬ (q = p) := Ne.symm hpq
      rw [if_neg h1, if_neg h2, if_pos rfl, if_neg h3] at h
      omega

/-- On a prime power the twisted von Mangoldt weight is the log of the prime carried by the
unimodular phase of the layer. -/
theorem twistedVonMangoldt_primePow (t : ℝ) {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : a ≠ 0) :
    twistedVonMangoldt t (p ^ a)
      = (Real.log p : ℂ) * Complex.exp (Complex.I * ((t * ((a : ℝ) * Real.log p) : ℝ) : ℂ)) := by
  have hpos : ((p : ℕ) ^ a : ℕ) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hne : (((p ^ a : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hpos
  have hlog : Real.log ((p ^ a : ℕ) : ℝ) = (a : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_pow]
  rw [twistedVonMangoldt_apply, ArithmeticFunction.vonMangoldt_apply_pow ha,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Complex.cpow_def_of_ne_zero hne,
    ← Complex.natCast_log, hlog]
  congr 1
  push_cast
  ring_nf

/-- **Equation (19).**  On a two-prime product layer `R = p^a q^b` the twisted fibre collapses to a
single cosine: the two orientations of the factorisation contribute conjugate phases. -/
theorem twistedFibre_two_prime {t : ℝ} {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    twistedFibre t (p ^ a * q ^ b)
      = 2 * (Real.log p : ℂ) * (Real.log q : ℂ)
          * (Real.cos (t * ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q)) : ℂ) := by
  classical
  have hR : p ^ a * q ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have hne : p ^ a ≠ q ^ b := by
    intro h
    have hpd : p ∣ q ^ b := h ▸ dvd_pow_self p ha
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd))
  have hsub : ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ))
      ⊆ (p ^ a * q ^ b).divisorsAntidiagonal := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hR⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_comm _ _, hR⟩
  have hzero : ∀ x ∈ (p ^ a * q ^ b).divisorsAntidiagonal,
      x ∉ ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) →
        twistedVonMangoldt t x.1 * twistedVonMangoldt (-t) x.2 = 0 := by
    intro x hx hxT
    obtain ⟨hxR, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    by_cases h1 : Λ x.1 = 0
    · rw [twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero h1, zero_mul]
    by_cases h2 : Λ x.2 = 0
    · rw [twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero h2, mul_zero]
    exfalso
    have horient := primePow_pair_of_semiprimePower hp hq hpq (Nat.pos_of_ne_zero ha)
      (Nat.pos_of_ne_zero hb) hxR (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h1)
      (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h2)
    refine hxT ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases horient with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (Prod.ext_iff.mpr ⟨e1, e2⟩)
    · exact Or.inr (Prod.ext_iff.mpr ⟨e1, e2⟩)
  have hpair : ((p ^ a, q ^ b) : ℕ × ℕ) ≠ (q ^ b, p ^ a) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h
    exact absurd h hne
  have final : ∀ u v L M : ℝ,
      (L : ℂ) * Complex.exp (Complex.I * (u : ℂ))
          * ((M : ℂ) * Complex.exp (Complex.I * ((-v : ℝ) : ℂ)))
        + (M : ℂ) * Complex.exp (Complex.I * (v : ℂ))
          * ((L : ℂ) * Complex.exp (Complex.I * ((-u : ℝ) : ℂ)))
      = 2 * (L : ℂ) * (M : ℂ) * (Real.cos (u - v) : ℂ) := by
    intro u v L M
    have h1 : Complex.exp (Complex.I * (u : ℂ)) * Complex.exp (Complex.I * ((-v : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    have h2 : Complex.exp (Complex.I * (v : ℂ)) * Complex.exp (Complex.I * ((-u : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((-(u - v) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring_nf
    have h3 : Complex.exp (Complex.I * ((u - v : ℝ) : ℂ))
        + Complex.exp (Complex.I * ((-(u - v) : ℝ) : ℂ))
        = 2 * (Real.cos (u - v) : ℂ) := by
      rw [Complex.ofReal_cos, Complex.two_cos]
      congr 1
      · congr 1
        push_cast
        ring_nf
      · congr 1
        push_cast
        ring_nf
    linear_combination (L : ℂ) * (M : ℂ) * h1 + (L : ℂ) * (M : ℂ) * h2 + (L : ℂ) * (M : ℂ) * h3
  rw [twistedFibre, ArithmeticFunction.mul_apply, ← Finset.sum_subset hsub hzero,
    Finset.sum_pair hpair]
  dsimp only
  rw [twistedVonMangoldt_primePow t hp ha, twistedVonMangoldt_primePow (-t) hq hb,
    twistedVonMangoldt_primePow t hq hb, twistedVonMangoldt_primePow (-t) hp ha, neg_mul, neg_mul,
    mul_sub]
  exact final (t * ((a : ℝ) * Real.log p)) (t * ((b : ℝ) * Real.log q)) (Real.log p) (Real.log q)

/-! ## Equations (9) and (22)--(23): the localized pair sum on a two-prime layer -/

/-- Reduction of an antidiagonal sum over a two-prime product layer to its two prime-power
orientations. -/
theorem sum_antidiagonal_two_prime {M : Type*} [AddCommMonoid M]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (F : ℕ → ℕ → M)
    (hF : ∀ x ∈ (p ^ a * q ^ b).divisorsAntidiagonal,
      ¬ (IsPrimePow x.1 ∧ IsPrimePow x.2) → F x.1 x.2 = 0) :
    ∑ x ∈ (p ^ a * q ^ b).divisorsAntidiagonal, F x.1 x.2
      = F (p ^ a) (q ^ b) + F (q ^ b) (p ^ a) := by
  classical
  have hR : p ^ a * q ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero)
  have hne : p ^ a ≠ q ^ b := by
    intro h
    have hpd : p ∣ q ^ b := h ▸ dvd_pow_self p ha
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpd))
  have hsub : ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ))
      ⊆ (p ^ a * q ^ b).divisorsAntidiagonal := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hR⟩
    · exact Nat.mem_divisorsAntidiagonal.mpr ⟨mul_comm _ _, hR⟩
  have hzero : ∀ x ∈ (p ^ a * q ^ b).divisorsAntidiagonal,
      x ∉ ({(p ^ a, q ^ b), (q ^ b, p ^ a)} : Finset (ℕ × ℕ)) → F x.1 x.2 = 0 := by
    intro x hx hxT
    refine hF x hx ?_
    rintro ⟨h1, h2⟩
    obtain ⟨hxR, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have horient := primePow_pair_of_semiprimePower hp hq hpq (Nat.pos_of_ne_zero ha)
      (Nat.pos_of_ne_zero hb) hxR h1 h2
    refine hxT ?_
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases horient with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (Prod.ext_iff.mpr ⟨e1, e2⟩)
    · exact Or.inr (Prod.ext_iff.mpr ⟨e1, e2⟩)
  have hpair : ((p ^ a, q ^ b) : ℕ × ℕ) ≠ (q ^ b, p ^ a) := by
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro h
    exact absurd h hne
  rw [← Finset.sum_subset hsub hzero, Finset.sum_pair hpair]

/-- **Equation (9).**  The localized von Mangoldt pair sum of a product layer. -/
def localizedVonMangoldtPair (W : ℝ → ℝ) (R : ℕ) : ℝ :=
  ∑ x ∈ R.divisorsAntidiagonal, Λ x.1 * Λ x.2 * W (Real.log x.1 - Real.log x.2)

/-- **Equation (22).**  Against an even ratio kernel a two-prime product layer carries exactly one
real mode: the two orientations reinforce. -/
theorem localizedVonMangoldtPair_two_prime (W : ℝ → ℝ) (hW : ∀ x : ℝ, W (-x) = W x)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    localizedVonMangoldtPair W (p ^ a * q ^ b)
      = 2 * Real.log p * Real.log q
          * W ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q) := by
  classical
  have hF : ∀ x ∈ (p ^ a * q ^ b).divisorsAntidiagonal,
      ¬ (IsPrimePow x.1 ∧ IsPrimePow x.2) →
        Λ x.1 * Λ x.2 * W (Real.log x.1 - Real.log x.2) = 0 := by
    intro x _ hx
    rcases not_and_or.mp hx with h | h
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, zero_mul, zero_mul]
    · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h, mul_zero, zero_mul]
  have hred := sum_antidiagonal_two_prime hp hq hpq ha hb
    (fun m n => Λ m * Λ n * W (Real.log m - Real.log n)) hF
  have hlp : Real.log ((p ^ a : ℕ) : ℝ) = (a : ℝ) * Real.log p := by
    push_cast
    rw [Real.log_pow]
  have hlq : Real.log ((q ^ b : ℕ) : ℝ) = (b : ℝ) * Real.log q := by
    push_cast
    rw [Real.log_pow]
  have hWneg : W ((b : ℝ) * Real.log q - (a : ℝ) * Real.log p)
      = W ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q) := by
    rw [show (b : ℝ) * Real.log q - (a : ℝ) * Real.log p
      = -((a : ℝ) * Real.log p - (b : ℝ) * Real.log q) by ring, hW]
  rw [localizedVonMangoldtPair, hred, ArithmeticFunction.vonMangoldt_apply_pow ha,
    ArithmeticFunction.vonMangoldt_apply_pow hb, ArithmeticFunction.vonMangoldt_apply_prime hp,
    ArithmeticFunction.vonMangoldt_apply_prime hq, hlp, hlq, hWneg]
  ring

/-- **Equation (22), fixed-ratio kernel.**  The complete centred product layer of an ordinary
two-prime product. -/
theorem localizedVonMangoldtPair_centredTriangular {A c : ℝ}
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    localizedVonMangoldtPair (centredTriangularKernel A c) (p ^ a * q ^ b)
      = 2 * Real.log p * Real.log q
          * (triangularKernel c ((a : ℝ) * Real.log p - (b : ℝ) * Real.log q) - c ^ 2 / A) :=
  localizedVonMangoldtPair_two_prime _ (centredTriangularKernel_even A c) hp hq hpq ha hb

/-- The positive amplitude of a two-prime product layer. -/
theorem two_prime_amplitude_pos {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    0 < 2 * Real.log p * Real.log q := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  positivity

/-- **Equation (23), positive chamber of a two-prime layer.** -/
theorem localizedVonMangoldtPair_centredTriangular_pos_iff {A c : ℝ} (hc : 0 < c) (hcA : c < A)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    0 < localizedVonMangoldtPair (centredTriangularKernel A c) (p ^ a * q ^ b)
      ↔ |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| < c * (1 - c / A) := by
  have hamp := two_prime_amplitude_pos hp hq
  rw [localizedVonMangoldtPair_centredTriangular hp hq hpq ha hb,
    ← centredTriangularKernel, ← centredTriangularKernel_pos_iff (A := A) (c := c)
      (x := (a : ℝ) * Real.log p - (b : ℝ) * Real.log q) hc hcA]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **Equation (23), zero chamber of a two-prime layer.** -/
theorem localizedVonMangoldtPair_centredTriangular_eq_zero_iff {A c : ℝ} (hc : 0 < c) (hcA : c < A)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    localizedVonMangoldtPair (centredTriangularKernel A c) (p ^ a * q ^ b) = 0
      ↔ |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| = c * (1 - c / A) := by
  have hamp := two_prime_amplitude_pos hp hq
  rw [localizedVonMangoldtPair_centredTriangular hp hq hpq ha hb,
    ← centredTriangularKernel, ← centredTriangularKernel_eq_zero_iff (A := A) (c := c)
      (x := (a : ℝ) * Real.log p - (b : ℝ) * Real.log q) hc hcA]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (by linarith)
    · exact h1
  · intro h
    rw [h, mul_zero]

/-- **Equation (23), negative chamber of a two-prime layer.** -/
theorem localizedVonMangoldtPair_centredTriangular_neg_iff {A c : ℝ} (hc : 0 < c) (hcA : c < A)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    localizedVonMangoldtPair (centredTriangularKernel A c) (p ^ a * q ^ b) < 0
      ↔ c * (1 - c / A) < |(a : ℝ) * Real.log p - (b : ℝ) * Real.log q| := by
  have hamp := two_prime_amplitude_pos hp hq
  rw [localizedVonMangoldtPair_centredTriangular hp hq hpq ha hb,
    ← centredTriangularKernel, ← centredTriangularKernel_neg_iff (A := A) (c := c)
      (x := (a : ℝ) * Real.log p - (b : ℝ) * Real.log q) hc hcA]
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-! ## Equation (20): the prime-power fibre -/

/-- **Equation (20), exponential form.**  A one-prime layer `p^k` carries exactly `k-1` ordered
`Λ`-supported factorizations, with phases `(2j-k) t log p`. -/
theorem twistedFibre_primePow {t : ℝ} {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    twistedFibre t (p ^ k)
      = (Real.log p : ℂ) ^ 2 * ∑ j ∈ Finset.Ico 1 k,
          Complex.exp (Complex.I * (((2 * (j : ℝ) - (k : ℝ)) * (t * Real.log p) : ℝ) : ℂ)) := by
  classical
  have hppos : 0 < p := hp.pos
  have hterm : ∀ j ∈ Finset.Ico 1 k,
      twistedVonMangoldt t (p ^ j) * twistedVonMangoldt (-t) (p ^ k / p ^ j)
        = (Real.log p : ℂ) ^ 2
            * Complex.exp (Complex.I
                * (((2 * (j : ℝ) - (k : ℝ)) * (t * Real.log p) : ℝ) : ℂ)) := by
    intro j hj
    obtain ⟨hj1, hjk⟩ := Finset.mem_Ico.mp hj
    have hj0 : j ≠ 0 := by omega
    have hkj : k - j ≠ 0 := by omega
    have hcast : ((k - j : ℕ) : ℝ) = (k : ℝ) - (j : ℝ) := by
      have hle : j ≤ k := le_of_lt hjk
      exact Nat.cast_sub hle
    rw [Nat.pow_div (le_of_lt hjk) hppos, twistedVonMangoldt_primePow t hp hj0,
      twistedVonMangoldt_primePow (-t) hp hkj, mul_mul_mul_comm, ← Complex.exp_add]
    have hexp : Complex.I * ((t * ((j : ℝ) * Real.log p) : ℝ) : ℂ)
          + Complex.I * ((-t * (((k - j : ℕ) : ℝ) * Real.log p) : ℝ) : ℂ)
        = Complex.I * (((2 * (j : ℝ) - (k : ℝ)) * (t * Real.log p) : ℝ) : ℂ) := by
      rw [hcast]
      push_cast
      ring
    rw [hexp]
    ring
  have hvanish : ∀ j ∈ Finset.range (k + 1), j ∉ Finset.Ico 1 k →
      twistedVonMangoldt t (p ^ j) * twistedVonMangoldt (-t) (p ^ k / p ^ j) = 0 := by
    intro j hj hjn
    have hjk : j ≤ k := by
      have := Finset.mem_range.mp hj
      omega
    have hcase : j = 0 ∨ j = k := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exact Or.inl h
      · right
        by_contra hc
        exact hjn (Finset.mem_Ico.mpr ⟨h, lt_of_le_of_ne hjk hc⟩)
    rcases hcase with rfl | rfl
    · rw [twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero (by simp), zero_mul]
    · rw [Nat.div_self (pow_pos hppos j),
        twistedVonMangoldt_eq_zero_of_vonMangoldt_eq_zero
          (n := 1) (by simp), mul_zero]
  have hsubIco : Finset.Ico 1 k ⊆ Finset.range (k + 1) := by
    intro j hj
    obtain ⟨-, h2⟩ := Finset.mem_Ico.mp hj
    exact Finset.mem_range.mpr (by omega)
  rw [twistedFibre, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun d e => twistedVonMangoldt t d * twistedVonMangoldt (-t) e),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [← Finset.sum_subset hsubIco hvanish, Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-- The symmetric exponential sum `∑_{j=1}^{m-1} e^{i(2j-m)θ}` of a one-prime layer. -/
def symmetricExpSum (θ : ℂ) (m : ℕ) : ℂ :=
  ∑ j ∈ Finset.Ico 1 m, Complex.exp (Complex.I * ((2 * (j : ℂ) - (m : ℂ)) * θ))

theorem symmetricExpSum_one (θ : ℂ) : symmetricExpSum θ 1 = 0 := by
  rw [symmetricExpSum, Finset.Ico_self, Finset.sum_empty]

theorem symmetricExpSum_two (θ : ℂ) : symmetricExpSum θ 2 = 1 := by
  rw [symmetricExpSum, show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton]
  norm_num

/-- The three-term recurrence of the symmetric exponential sums: the Chebyshev recurrence of the
second kind in the variable `cos θ`. -/
theorem symmetricExpSum_recurrence (θ : ℂ) {k : ℕ} (hk : 1 ≤ k) :
    symmetricExpSum θ (k + 2)
      = 2 * Complex.cos θ * symmetricExpSum θ (k + 1) - symmetricExpSum θ k := by
  classical
  set w : ℂ := Complex.I * θ with hw
  have hfac : ∀ m : ℕ, symmetricExpSum θ m
      = Complex.exp (-((m : ℂ) * w))
          * ∑ j ∈ Finset.Ico 1 m, Complex.exp ((2 * (j : ℂ)) * w) := by
    intro m
    rw [symmetricExpSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.exp_add]
    congr 1
    rw [hw]
    ring
  have hP1 : (∑ j ∈ Finset.Ico 1 (k + 1), Complex.exp ((2 * (j : ℂ)) * w))
      = (∑ j ∈ Finset.Ico 1 k, Complex.exp ((2 * (j : ℂ)) * w))
        + Complex.exp ((2 * (k : ℂ)) * w) :=
    Finset.sum_Ico_succ_top hk _
  have hP2 : (∑ j ∈ Finset.Ico 1 (k + 2), Complex.exp ((2 * (j : ℂ)) * w))
      = (∑ j ∈ Finset.Ico 1 (k + 1), Complex.exp ((2 * (j : ℂ)) * w))
        + Complex.exp ((2 * ((k : ℂ) + 1)) * w) := by
    have hstep := Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)
      (fun j : ℕ => Complex.exp ((2 * (j : ℂ)) * w))
    rw [show k + 2 = (k + 1) + 1 from rfl, hstep,
      show ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]
  have hcos : 2 * Complex.cos θ = Complex.exp w + Complex.exp (-w) := by
    rw [hw, Complex.two_cos]
    congr 1
    · congr 1
      ring
    · congr 1
      ring
  have e2 : Complex.exp (-(((k + 2 : ℕ) : ℂ) * w))
      = Complex.exp (-((k : ℂ) * w)) * Complex.exp (-w) * Complex.exp (-w) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e1 : Complex.exp (-(((k + 1 : ℕ) : ℂ) * w))
      = Complex.exp (-((k : ℂ) * w)) * Complex.exp (-w) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e3 : Complex.exp ((2 * (k : ℂ)) * w)
      = Complex.exp ((k : ℂ) * w) * Complex.exp ((k : ℂ) * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have e4 : Complex.exp ((2 * ((k : ℂ) + 1)) * w)
      = Complex.exp ((k : ℂ) * w) * Complex.exp ((k : ℂ) * w) * Complex.exp w * Complex.exp w := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hbc : Complex.exp w * Complex.exp (-w) = 1 := by
    rw [← Complex.exp_add]
    simp
  rw [hfac (k + 2), hfac (k + 1), hfac k, hP2, hP1, hcos, e2, e1, e3, e4]
  set A : ℂ := Complex.exp (-((k : ℂ) * w))
  set B : ℂ := Complex.exp w
  set C : ℂ := Complex.exp (-w)
  set D : ℂ := Complex.exp ((k : ℂ) * w)
  set Q : ℂ := ∑ j ∈ Finset.Ico 1 k, Complex.exp ((2 * (j : ℂ)) * w)
  linear_combination (A * D ^ 2 * B * C - A * Q) * hbc

/-- **Equation (20), Chebyshev form.**  The symmetric exponential sum of a one-prime layer is the
Chebyshev polynomial of the second kind evaluated at `cos θ`. -/
theorem symmetricExpSum_eq_chebyshevU (θ : ℂ) {k : ℕ} (hk : 2 ≤ k) :
    symmetricExpSum θ k
      = Polynomial.eval (Complex.cos θ) (Polynomial.Chebyshev.U ℂ ((k : ℤ) - 2)) := by
  have main : ∀ m : ℕ,
      symmetricExpSum θ (m + 1)
          = Polynomial.eval (Complex.cos θ) (Polynomial.Chebyshev.U ℂ ((m : ℤ) - 1))
        ∧ symmetricExpSum θ (m + 2)
          = Polynomial.eval (Complex.cos θ) (Polynomial.Chebyshev.U ℂ (m : ℤ)) := by
    intro m
    induction m with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [symmetricExpSum_one]
        norm_num [Polynomial.Chebyshev.U_neg_one]
      · rw [symmetricExpSum_two]
        norm_num [Polynomial.Chebyshev.U_zero]
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [show ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) by push_cast; ring,
          show n + 1 + 1 = n + 2 from rfl]
        exact ih.2
      · have hrec := symmetricExpSum_recurrence θ (k := n + 1) (by omega)
        have h1 : symmetricExpSum θ (n + 1 + 1)
            = Polynomial.eval (Complex.cos θ) (Polynomial.Chebyshev.U ℂ (n : ℤ)) := by
          rw [show n + 1 + 1 = n + 2 from rfl]
          exact ih.2
        rw [hrec, h1, ih.1, show ((n + 1 : ℕ) : ℤ) = ((n : ℤ) - 1) + 2 by push_cast; ring,
          Polynomial.Chebyshev.U_add_two ℂ ((n : ℤ) - 1),
          show ((n : ℤ) - 1 + 1) = (n : ℤ) by ring]
        simp [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X]
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  rw [show ((m + 2 : ℕ) : ℤ) - 2 = (m : ℤ) by push_cast; ring]
  exact (main m).2

/-- **Equation (20).**  The prime-power fibre is `(log p)² U_{k-2}(cos(t log p))`. -/
theorem twistedFibre_primePow_chebyshevU {t : ℝ} {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 2 ≤ k) :
    twistedFibre t (p ^ k)
      = (Real.log p : ℂ) ^ 2
          * Polynomial.eval (Complex.cos ((t * Real.log p : ℝ) : ℂ))
              (Polynomial.Chebyshev.U ℂ ((k : ℤ) - 2)) := by
  rw [twistedFibre_primePow hp hk,
    ← symmetricExpSum_eq_chebyshevU ((t * Real.log p : ℝ) : ℂ) hk]
  congr 1
  rw [symmetricExpSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

end

end RHTower
