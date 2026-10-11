import GaloisForLFunctions.RHTower.Sieve.ShiftedPerronUniform
import GaloisForLFunctions.RHTower.SelbergPrimePolynomialHighMoments
import GaloisForLFunctions.RHTower.MertensPrimeWindowWeakConvergence

/-!
# Log-weighted prime sums over a window

For `A < B` put `S(z) = Σ_{A < p ≤ B} (log p / p) p^z` and `M = S(0) = Σ_{A<p≤B} log p / p`.
These are the exponents of the log-weight Bernoulli tests: the zero `q` sees `S(ξ − q)` when the
test is centred at `ξ`.

* For `Re z ≤ 0`, `‖S(z)‖ ≤ (A+1)^{Re z} M`, and for `Re z ≥ 0`, `‖S(z)‖ ≤ B^{Re z} M`.
* Mertens: `M ≥ log B − log A − 2C` (`jasLogMass_ge`).
* Right of a Xi frontier (`exists_norm_jasLogWeightSum_sub_le`): `S(z)` is the main term
  `((B+½)^z − (A+½)^z)/z` up to an error `K(x^{σ₁−1+Re z} log²)` at the two half-integer endpoints plus
  the proper prime powers, uniformly in `Im z`.  This is the shifted Perron formula at `s₀ = 1 − z`:
  the two `ζ′/ζ(s₀)` terms cancel in the window.  In particular, for `|Im z| ≥ 1` the prime sum
  decorrelates: `‖S(z)‖ ≤ 2 B^{max(Re z, 0)}/|Im z| + O(1)`.
-/

open Complex ArithmeticFunction
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The primes in `(A, B]`. -/
def jasPrimeWindow (A B : ℕ) : Finset Nat.Primes := (Finset.Ioc A B).subtype Nat.Prime

/-- `S(z) = Σ_{A < p ≤ B} (log p / p) p^z`. -/
def jasLogWeightSum (A B : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ jasPrimeWindow A B, ((Real.log p / p : ℝ) : ℂ) * cexp (z * (Real.log p : ℂ))

/-- The Mertens mass `Σ_{A < p ≤ B} log p / p`. -/
def jasLogMass (A B : ℕ) : ℝ := ∑ p ∈ jasPrimeWindow A B, Real.log p / p

theorem mem_jasPrimeWindow {A B : ℕ} {p : Nat.Primes} :
    p ∈ jasPrimeWindow A B ↔ A < (p : ℕ) ∧ (p : ℕ) ≤ B := by
  unfold jasPrimeWindow
  exact (Finset.mem_subtype (p := Nat.Prime) (a := p)).trans Finset.mem_Ioc

/-- Sums over the prime window are filtered sums over `(A, B]`. -/
theorem sum_jasPrimeWindow {M : Type*} [AddCommMonoid M] (A B : ℕ) (f : ℕ → M) :
    ∑ p ∈ jasPrimeWindow A B, f p = ∑ n ∈ (Finset.Ioc A B).filter Nat.Prime, f n :=
  Finset.sum_subtype_eq_sum_filter f

theorem log_div_nonneg_prime (p : Nat.Primes) : 0 ≤ Real.log p / p :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)) (Nat.cast_nonneg _)

theorem jasLogMass_nonneg (A B : ℕ) : 0 ≤ jasLogMass A B :=
  Finset.sum_nonneg fun p _ => log_div_nonneg_prime p

theorem jasLogWeightSum_zero (A B : ℕ) : jasLogWeightSum A B 0 = (jasLogMass A B : ℂ) := by
  simp [jasLogWeightSum, jasLogMass]

theorem norm_jasLogWeightTerm (p : Nat.Primes) (z : ℂ) :
    ‖((Real.log p / p : ℝ) : ℂ) * cexp (z * (Real.log p : ℂ))‖ =
      Real.log p / p * Real.exp (z.re * Real.log p) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (log_div_nonneg_prime p),
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Left of the centre the window sum is dominated by the mass with the decay of its lowest prime. -/
theorem norm_jasLogWeightSum_le_of_re_nonpos {A B : ℕ} {z : ℂ} (hz : z.re ≤ 0) :
    ‖jasLogWeightSum A B z‖ ≤ Real.exp (z.re * Real.log (A + 1)) * jasLogMass A B := by
  refine (norm_sum_le _ _).trans ?_
  rw [jasLogMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [norm_jasLogWeightTerm, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (log_div_nonneg_prime p)
  have hpA : (A : ℝ) + 1 ≤ p := by
    have := (mem_jasPrimeWindow.mp hp).1
    exact_mod_cast this
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left
    (Real.log_le_log (by positivity) hpA) hz)

/-- Right of the centre the window sum grows at most like its largest prime. -/
theorem norm_jasLogWeightSum_le_of_re_nonneg {A B : ℕ} {z : ℂ} (hz : 0 ≤ z.re) :
    ‖jasLogWeightSum A B z‖ ≤ Real.exp (z.re * Real.log B) * jasLogMass A B := by
  refine (norm_sum_le _ _).trans ?_
  rw [jasLogMass, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [norm_jasLogWeightTerm, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (log_div_nonneg_prime p)
  have hpB : (p : ℝ) ≤ B := by
    have := (mem_jasPrimeWindow.mp hp).2
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Real.log_le_log hp0 hpB) hz)

theorem norm_jasLogWeightSum_le_mass {A B : ℕ} {z : ℂ} (hz : z.re ≤ 0) :
    ‖jasLogWeightSum A B z‖ ≤ jasLogMass A B := by
  refine (norm_jasLogWeightSum_le_of_re_nonpos hz).trans ?_
  have h1 : Real.exp (z.re * Real.log (A + 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hz (Real.log_nonneg (by linarith [(A.cast_nonneg : (0:ℝ) ≤ A)]))
  exact mul_le_of_le_one_left (jasLogMass_nonneg A B) h1

theorem re_jasLogWeightSum_le_mass {A B : ℕ} {z : ℂ} (hz : z.re ≤ 0) :
    (jasLogWeightSum A B z).re ≤ jasLogMass A B :=
  (Complex.re_le_norm _).trans (norm_jasLogWeightSum_le_mass hz)

/-- **Mertens in the window.** -/
theorem jasLogMass_ge {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    Real.log B - Real.log A - 2 * mertensPrimeWindowBound ≤ jasLogMass A B := by
  have hB : 1 ≤ B := le_trans hA hAB
  have h1 := abs_mertensPrimeWeightSum_sub_log_le B hB
  have h2 := abs_mertensPrimeWeightSum_sub_log_le A hA
  have hsplit : mertensPrimeWeightSum B = mertensPrimeWeightSum A + jasLogMass A B := by
    rw [mertensPrimeWeightSum_eq, mertensPrimeWeightSum_eq, jasLogMass,
      sum_jasPrimeWindow A B (fun n : ℕ => Real.log n / (n : ℝ))]
    have hIcc : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := fun N => by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, hIcc, hIcc]
    exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le A) hAB).symm
  rw [abs_le] at h1 h2
  linarith [h1.1, h2.2]

/-! ## The window sum through the shifted Perron formula -/

/-- At a prime the shifted von Mangoldt coefficient at `1 − z` is the log-weight term. -/
theorem shiftedVonMangoldt_prime_eq (z : ℂ) {p : ℕ} (hp : p.Prime) :
    Sieve.shiftedVonMangoldt (1 - z) p =
      ((Real.log p / p : ℝ) : ℂ) * cexp (z * (Real.log p : ℂ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Sieve.shiftedVonMangoldt, vonMangoldt_apply_prime hp, Complex.cpow_def_of_ne_zero hpne]
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_log hp0.le]
  rw [hlog]
  have hinv : ((1 / (p : ℝ) : ℝ) : ℂ) = cexp (-(Real.log p : ℂ)) := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_log hp0, one_div]
  rw [div_eq_mul_one_div, Complex.ofReal_mul, hinv, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The proper prime powers on `Re s ≥ 7/8` carry at most `96`. -/
theorem norm_sum_nonprime_shiftedVonMangoldt_le {s : ℂ} (hs : 7 / 8 ≤ s.re) (A B : ℕ) :
    ‖∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime), Sieve.shiftedVonMangoldt s n‖ ≤ 96 := by
  refine (norm_sum_le _ _).trans ?_
  have hbound := sum_nonprime_vonMangoldt_rpow_le (δ := 3 / 8) (by norm_num) (by norm_num) B
  rw [show (96 : ℝ) = 36 / (3 / 8) by norm_num]
  refine le_trans ?_ hbound
  have hsub : (Finset.Ioc A B).filter (fun n => ¬ n.Prime) ⊆
      (Finset.Icc 1 B).filter (fun n => ¬ n.Prime) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  refine le_trans (Finset.sum_le_sum fun n hn => ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ =>
      mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hn1 : 1 ≤ n := by
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn; omega
  rw [Sieve.norm_shiftedVonMangoldt]
  refine mul_le_mul_of_nonneg_left ?_ vonMangoldt_nonneg
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  exact Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)

/-- **The window sum right of a Xi frontier.**  Uniformly in the height, `S(z)` equals the
main term `((B+½)^z − (A+½)^z)/z` up to the endpoint Perron errors and the proper prime powers. -/
theorem exists_norm_jasLogWeightSum_sub_le {alpha : ℝ} (halpha : 0 ≤ alpha)
    (hXi : XiZeroHalfPlaneBound alpha) {σ₁ η : ℝ} (hσ₁ : 1 / 2 + alpha < σ₁) (hσ₁1 : σ₁ < 1)
    (hη : 0 < η) :
    ∃ K : ℝ, 0 < K ∧ ∀ A B : ℕ, 1 ≤ A → A ≤ B → ∀ z : ℂ, z ≠ 0 → -1 / 8 < z.re →
      z.re ≤ 1 - σ₁ - η → z.re ≤ 1 / 8 →
        ‖jasLogWeightSum A B z -
            (((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z)‖
          ≤ K * (((A : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
                (1 + Real.log ((A : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2 +
              ((B : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
                (1 + Real.log ((B : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2) + 96 := by
  classical
  obtain ⟨K, hK0, hK⟩ :=
    Sieve.exists_norm_shiftedChebyshev_sub_le_uniform halpha hXi hσ₁ hσ₁1 hη
  refine ⟨K, hK0, fun A B hA hAB z hz0 hzlo hzhi hz8 => ?_⟩
  set s₀ : ℂ := 1 - z with hs₀
  have hs₀re : s₀.re = 1 - z.re := by rw [hs₀]; simp
  have hs₀im : |s₀.im| = |z.im| := by rw [hs₀]; simp
  have hs₀1 : s₀ ≠ 1 := by
    intro h; apply hz0; rw [hs₀] at h; linear_combination -h
  have hz1 : 1 - s₀ = z := by rw [hs₀]; ring
  have hB := hK s₀ (by rw [hs₀re]; linarith) (by rw [hs₀re]; linarith) hs₀1 B (le_trans hA hAB)
  have hA' := hK s₀ (by rw [hs₀re]; linarith) (by rw [hs₀re]; linarith) hs₀1 A hA
  rw [hz1, hs₀re, hs₀im] at hB hA'
  -- the window of the Chebyshev sums
  have hwin : (∑ n ∈ Finset.Icc 1 B, Sieve.shiftedVonMangoldt s₀ n) -
      ∑ n ∈ Finset.Icc 1 A, Sieve.shiftedVonMangoldt s₀ n =
        ∑ n ∈ Finset.Ioc A B, Sieve.shiftedVonMangoldt s₀ n := by
    have h := Finset.sum_Ioc_consecutive (fun n => Sieve.shiftedVonMangoldt s₀ n)
      (Nat.zero_le A) hAB
    have hIcc : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := fun N => by
      ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [hIcc, hIcc, ← h]
    ring
  -- primes and proper prime powers
  have hsplit : ∑ n ∈ Finset.Ioc A B, Sieve.shiftedVonMangoldt s₀ n =
      jasLogWeightSum A B z +
        ∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime), Sieve.shiftedVonMangoldt s₀ n := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc A B) Nat.Prime]
    congr 1
    rw [jasLogWeightSum, sum_jasPrimeWindow A B (fun n : ℕ =>
        ((Real.log n / n : ℝ) : ℂ) * cexp (z * (Real.log n : ℂ)))]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [hs₀]
    exact shiftedVonMangoldt_prime_eq z (Finset.mem_filter.mp hn).2
  have hpp := norm_sum_nonprime_shiftedVonMangoldt_le (s := s₀)
    (by rw [hs₀re]; linarith) A B
  -- assemble
  set EB := (∑ n ∈ Finset.Icc 1 B, Sieve.shiftedVonMangoldt s₀ n) -
    ((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z / z + -deriv riemannZeta s₀ / riemannZeta s₀) with hEB
  set EA := (∑ n ∈ Finset.Icc 1 A, Sieve.shiftedVonMangoldt s₀ n) -
    ((((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z / z + -deriv riemannZeta s₀ / riemannZeta s₀) with hEA
  have hid : jasLogWeightSum A B z -
      (((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z) =
        EB - EA - ∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime),
          Sieve.shiftedVonMangoldt s₀ n := by
    have h1 := hwin
    rw [hsplit] at h1
    rw [hEB, hEA, sub_div]
    linear_combination -h1
  rw [hid]
  calc ‖EB - EA - ∑ n ∈ (Finset.Ioc A B).filter (fun n => ¬ n.Prime),
          Sieve.shiftedVonMangoldt s₀ n‖
      ≤ ‖EB‖ + ‖EA‖ + 96 := by
        refine (norm_sub_le _ _).trans ?_
        exact add_le_add ((norm_sub_le _ _)) hpp
    _ ≤ _ := by
        have := add_le_add hB hA'
        nlinarith [this]

end

end RHTower
