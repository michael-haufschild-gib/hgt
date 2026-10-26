import GaloisForLFunctions.ArithmeticPositiveDuality.ArithmeticCorrelationGeometry.TheThresholdIsThePriceOfTheArchimedeanLine
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

/-!
# Finite gauge subgroups resolve what the archimedean line cannot

Two families of twists act on a pair `(m, n)` of positive integers.

* **The archimedean line** `χ(k) = k^{2πiξ}` moves the pair by the phase `(m/n)^{2πiξ}`, which
  stays within `2π|ξ| |log(m/n)|` of `1` (`norm_archPair_sub_one_le`). A successor pair
  `(n, n+h)` has `log((n+h)/n) ≤ h/n`: up to height `ξ` the line cannot separate it from a
  coincidence once `n ≫ |ξ| h`. Successor pairs are the most coalescent pairs there are.
* **The Dirichlet subgroup of level `q`.** Every Dirichlet character `χ mod q` is a gauge point,
  with the value at primes dividing `q` reset to one (`dirichletGauge`, `twist_dirichletGauge`).
  Averaging over these `φ(q)` points projects a pair onto congruence
  (`sum_twist_dirichletGauge_mul_conj`): `(1/φ(q)) Σ_χ χ(m) χ̄(n) = [m ≡ n mod q]` for `m, n`
  prime to `q`. A successor pair `(n, n+h)` survives exactly when `q ∣ h`
  (`sum_twist_dirichletGauge_succ`), uniformly in `n`.

So the arithmetic (finite) part of the gauge torus resolves the near-incidences that the
archimedean part cannot, and the **stabilizer** of the shift-`h` successor pairs among the finite
subgroups is the set of levels dividing `h`. The Hardy–Littlewood singular series is an average over
exactly these stabilizers: the main term of a signed prime-pair statistic beyond the threshold is
carried by the levels `q ∣ h`, and its discrepancy by the remaining gauge directions.
-/

open Finset
open scoped ComplexConjugate Real

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry ArithmeticKunnethTheory

/-! ### The archimedean line freezes coalescent pairs -/

theorem norm_cexp_I_sub_one_le (t : ℝ) : ‖Complex.exp ((t : ℂ) * Complex.I) - 1‖ ≤ |t| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := t)
  rw [mul_comm] at h
  simpa [Real.norm_eq_abs] using h

/-- **The archimedean line moves a pair by at most `2π|ξ| |log(m/n)|`.** -/
theorem norm_archPair_sub_one_le (ξ : ℝ) (m n : ℕ) :
    ‖twist (archPoint ξ) m * conj (twist (archPoint ξ) n) - 1‖ ≤
      2 * π * |ξ| * |Real.log m - Real.log n| := by
  rw [twist_archPoint, twist_archPoint, ← Complex.exp_conj, ← Complex.exp_add]
  have harg : 2 * π * Complex.I * ξ * logFreq m + conj (2 * π * Complex.I * ξ * logFreq n) =
      ((2 * π * ξ * (Real.log m - Real.log n) : ℝ) : ℂ) * Complex.I := by
    simp only [logFreq, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [harg]
  refine (norm_cexp_I_sub_one_le _).trans (le_of_eq ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_two]

/-! ### Dirichlet characters as gauge points -/

variable {q : ℕ} [NeZero q]

/-- The gauge point of a Dirichlet character: its phase at primes prime to `q`, zero elsewhere. -/
def dirichletGauge (χ : DirichletCharacter ℂ q) : GaugeTorus := fun p =>
  if Nat.Coprime p q then ((Complex.arg (χ p) / (2 * π) : ℝ) : UnitAddCircle) else 0

omit [NeZero q] in
theorem norm_dirichletCharacter_coprime (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : Nat.Coprime n q) :
    ‖χ n‖ = 1 := by
  have h := χ.unit_norm_eq_one (ZMod.unitOfCoprime n hn)
  rwa [ZMod.coe_unitOfCoprime] at h

omit [NeZero q] in
/-- A Dirichlet character is completely multiplicative on finite products of naturals. -/
theorem prod_dirichletCharacter_pow (χ : DirichletCharacter ℂ q) (s : Finset ℕ) (e : ℕ → ℕ) :
    ∏ p ∈ s, χ p ^ e p = χ ((∏ p ∈ s, p ^ e p : ℕ) : ZMod q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.prod_insert hp, Nat.cast_mul, map_mul, ih, Nat.cast_pow,
      map_pow]

omit [NeZero q] in
/-- **A Dirichlet character is a twist on the integers prime to its modulus.** -/
theorem twist_dirichletGauge (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0)
    (hcop : Nat.Coprime n q) : twist (dirichletGauge χ) n = χ n := by
  classical
  rw [twist, torusCharacter_apply, support_expVec]
  have hprime : ∀ p ∈ n.factorization.support, fourier (expVec n p) (dirichletGauge χ p) =
      χ p ^ n.factorization p := by
    intro p hp
    have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors (Nat.support_factorization n ▸ hp)
    have hpq : Nat.Coprime p q := Nat.Coprime.coprime_dvd_left hpn hcop
    simp only [dirichletGauge, if_pos hpq]
    rw [expVec_apply, fourier_coe_apply]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have hexp : χ p = Complex.exp ((Complex.arg (χ p) : ℂ) * Complex.I) := by
      have h := Complex.norm_mul_exp_arg_mul_I (χ p)
      rw [norm_dirichletCharacter_coprime χ hpq, Complex.ofReal_one, one_mul] at h
      exact h.symm
    conv_rhs => rw [hexp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  rw [Finset.prod_congr rfl hprime, prod_dirichletCharacter_pow]
  congr 2
  exact_mod_cast Nat.prod_factorization_pow_eq_self hn

/-! ### Averaging over a Dirichlet subgroup -/

/-- **Finite gauge orthogonality.** Averaging over the Dirichlet subgroup of level `q` projects a
pair of integers prime to `q` onto congruence modulo `q`. -/
theorem sum_twist_dirichletGauge_mul_conj {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hmq : Nat.Coprime m q) (hnq : Nat.Coprime n q) :
    ∑ χ : DirichletCharacter ℂ q, twist (dirichletGauge χ) m * conj (twist (dirichletGauge χ) n) =
      if (m : ZMod q) = n then (q.totient : ℂ) else 0 := by
  have hunit : IsUnit (n : ZMod q) := (ZMod.unitOfCoprime n hnq).isUnit
  have hconj : ∀ χ : DirichletCharacter ℂ q, conj (χ n) = χ ((n : ZMod q)⁻¹) := by
    intro χ
    have h1 : χ n * χ ((n : ZMod q)⁻¹) = 1 := by
      rw [← map_mul, ZMod.mul_inv_of_unit _ hunit, map_one]
    have h2 : χ n * conj (χ n) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_dirichletCharacter_coprime χ hnq]
      norm_num
    exact mul_left_cancel₀ (fun h0 => by rw [h0, zero_mul] at h2; exact zero_ne_one h2)
      (h2.trans h1.symm)
  simp_rw [twist_dirichletGauge _ hm hmq, twist_dirichletGauge _ hn hnq, hconj]
  rw [show (∑ χ : DirichletCharacter ℂ q, χ m * χ ((n : ZMod q)⁻¹)) =
      ∑ χ : DirichletCharacter ℂ q, χ ((n : ZMod q)⁻¹) * χ m from
    Finset.sum_congr rfl fun χ _ => mul_comm _ _]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hunit]
  by_cases h : (m : ZMod q) = n
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun e => h e.symm), if_neg h]

/-- **The stabilizer of a successor pair.** Over the Dirichlet subgroup of level `q`, the pair
`(n, n+h)` (both prime to `q`) survives averaging iff `q ∣ h`. -/
theorem sum_twist_dirichletGauge_succ {n h : ℕ} (hn : n ≠ 0) (hnq : Nat.Coprime n q)
    (hhq : Nat.Coprime (n + h) q) :
    ∑ χ : DirichletCharacter ℂ q,
        twist (dirichletGauge χ) n * conj (twist (dirichletGauge χ) (n + h)) =
      if q ∣ h then (q.totient : ℂ) else 0 := by
  rw [sum_twist_dirichletGauge_mul_conj hn (by omega) hnq hhq]
  have hiff : ((n : ZMod q) = ((n + h : ℕ) : ZMod q)) ↔ q ∣ h := by
    rw [eq_comm, Nat.cast_add, add_eq_left, ZMod.natCast_eq_zero_iff]
  by_cases hd : q ∣ h
  · rw [if_pos (hiff.mpr hd), if_pos hd]
  · rw [if_neg (fun e => hd (hiff.mp e)), if_neg hd]

/-- **The stabilizer average of a pair form.** Averaging a pair form over the Dirichlet subgroup of
level `q` keeps exactly the pairs congruent modulo `q`. Applied to the coalescent prime pairs this
is the level-`q` part of the singular-series model. -/
theorem sum_pairForm_dirichletGauge {S : Finset (ℕ × ℕ)}
    (hS : ∀ p ∈ S, p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ Nat.Coprime p.1 q ∧ Nat.Coprime p.2 q) (w : ℕ × ℕ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, pairForm S w (dirichletGauge χ) =
      (q.totient : ℂ) * ∑ p ∈ S with (p.1 : ZMod q) = p.2, w p := by
  classical
  simp only [pairForm]
  rw [Finset.sum_comm, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨h1, h2, h3, h4⟩ := hS p hp
  rw [← Finset.mul_sum, sum_twist_dirichletGauge_mul_conj h1 h2 h3 h4]
  split_ifs <;> ring

end GaloisForLFunctions.ArithmeticCorrelationGeometry
