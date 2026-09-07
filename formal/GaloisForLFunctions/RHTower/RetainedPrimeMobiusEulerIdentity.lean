import GaloisForLFunctions.RHTower.RetainedPrimeDirichletNumerator
import GaloisForLFunctions.RHTower.SquarefreeMoebiusNormalization
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Tactic

/-!
# The full weighted Möbius series on a finite retained prime field

The literal coefficient is `μ(n) y(primeFactors(n) ∩ P)`. Its complete
L-series is absolutely convergent on `Re s > 1` and equals the exact finite
Möbius subset numerator divided by zeta and the retained Euler denominator.
Prime-free restriction and multiplicative dilation give matching recursions
for the infinite series and the finite numerator. No ordering or growth
bound for the final retained-source energy is assumed.
-/

noncomputable section
namespace RHTower

/-- Multiplicative dilation of a sequence, retaining exactly the divisible indices. -/
def primeSourceDilation (p : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if p ∣ n then f (n / p) else 0

lemma LSeries_primeSourceDilation {p : ℕ} (hp : 0 < p) (f : ℕ → ℂ)
    (hf0 : f 0 = 0) (s : ℂ) :
    LSeries (primeSourceDilation p f) s = (p : ℂ) ^ (-s) * LSeries f s := by
  have hd0 : primeSourceDilation p f 0 = 0 := by simp [primeSourceDilation, hf0]
  have hinj : Function.Injective (fun n : ℕ => p * n) := fun _ _ h => Nat.mul_left_cancel hp h
  have hout : ∀ n, n ∉ Set.range (fun m : ℕ => p * m) →
      LSeries.term (primeSourceDilation p f) s n = 0 := by
    intro n hn
    have hnd : ¬p ∣ n := by
      rintro ⟨m, hm⟩
      exact hn ⟨m, hm.symm⟩
    rw [LSeries.term_def₀ hd0, primeSourceDilation, if_neg hnd, zero_mul]
  unfold LSeries
  rw [← hinj.tsum_eq (Function.support_subset_iff'.mpr hout), ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [LSeries.term_def₀ hd0, LSeries.term_def₀ hf0]
  simp only [primeSourceDilation, dvd_mul_right, if_true, Nat.mul_div_right _ hp]
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [hf0]
  · rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring



/-- Literal Möbius coefficients grouped by intersection with a retained prime field. -/
def retainedPrimeMobiusCoefficient (P : Finset ℕ) (y : Finset ℕ → ℂ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * y (n.primeFactors ∩ P)

@[simp] lemma retainedPrimeMobiusCoefficient_zero (P : Finset ℕ) (y : Finset ℕ → ℂ) :
    retainedPrimeMobiusCoefficient P y 0 = 0 := by simp [retainedPrimeMobiusCoefficient]

/-- Removing the prime-divisible part of any source sequence. -/
def primeFreeSourcePart (p : ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  if p ∣ n then 0 else f n

@[simp] lemma primeFreeSourcePart_zero (p : ℕ) (f : ℕ → ℂ) : primeFreeSourcePart p f 0 = 0 := by
  simp [primeFreeSourcePart]

lemma retainedPrimeMobiusCoefficient_mul_prime (P : Finset ℕ) (y : Finset ℕ → ℂ)
    {p n : ℕ} (hp : p.Prime) (hpP : p ∉ P) (hpn : ¬p ∣ n) :
    retainedPrimeMobiusCoefficient P y (p * n) = -retainedPrimeMobiusCoefficient P y n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hpn (dvd_zero p)
  have hcop : p.Coprime n := hp.coprime_iff_not_dvd.mpr hpn
  have hlab : (p * n).primeFactors ∩ P = n.primeFactors ∩ P := by
    rw [Nat.primeFactors_mul hp.ne_zero hn0, hp.primeFactors]
    ext q
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton]
    constructor
    · rintro ⟨hq | hq, hP⟩
      · exact False.elim (hpP (hq ▸ hP))
      · exact ⟨hq, hP⟩
    · rintro ⟨hq, hP⟩
      exact ⟨Or.inr hq, hP⟩
  rw [retainedPrimeMobiusCoefficient, retainedPrimeMobiusCoefficient,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime hp, hlab]
  push_cast
  ring

lemma retainedPrimeMobiusCoefficient_mul_prime_of_dvd (P : Finset ℕ) (y : Finset ℕ → ℂ)
    {p n : ℕ} (hp : p.Prime) (hpn : p ∣ n) :
    retainedPrimeMobiusCoefficient P y (p * n) = 0 := by
  have hmu : ArithmeticFunction.moebius (p * n) = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (fun h =>
      (hp.coprime_iff_not_dvd.mp (Nat.coprime_of_squarefree_mul h)) hpn)
  simp [retainedPrimeMobiusCoefficient, hmu]

/-- Each unretained prime gives an exact source-minus-dilation relation. -/
lemma retainedPrimeMobiusCoefficient_eq_primeFree_sub_dilation
    (P : Finset ℕ) (y : Finset ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) :
    retainedPrimeMobiusCoefficient P y =
      primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y) -
        primeSourceDilation p (primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y)) := by
  ext n
  by_cases hpn : p ∣ n
  · obtain ⟨r, rfl⟩ := hpn
    by_cases hpr : p ∣ r
    · simp [retainedPrimeMobiusCoefficient_mul_prime_of_dvd P y hp hpr,
        primeFreeSourcePart, primeSourceDilation, hp.ne_zero, hpr]
    · simp [retainedPrimeMobiusCoefficient_mul_prime P y hp hpP hpr,
        primeFreeSourcePart, primeSourceDilation, hp.ne_zero, hpr]
  · simp [primeFreeSourcePart, primeSourceDilation, hpn]

/-- Inserting a retained prime distinguishes its two functional coordinates exactly. -/
lemma retainedPrimeMobiusCoefficient_insert_eq_primeFree_sub_dilation
    (P : Finset ℕ) (y : Finset ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    retainedPrimeMobiusCoefficient (insert p P) y =
      primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y) -
        primeSourceDilation p (primeFreeSourcePart p
          (retainedPrimeMobiusCoefficient P (fun R => y (insert p R)))) := by
  ext n
  by_cases hpn : p ∣ n
  · obtain ⟨r, rfl⟩ := hpn
    by_cases hpr : p ∣ r
    · simp [retainedPrimeMobiusCoefficient_mul_prime_of_dvd (insert p P) y hp hpr,
        primeFreeSourcePart, primeSourceDilation, hp.ne_zero, hpr]
    · have hr0 : r ≠ 0 := by rintro rfl; exact hpr (dvd_zero p)
      have hlab : (p * r).primeFactors ∩ insert p P = insert p (r.primeFactors ∩ P) := by
        rw [Nat.primeFactors_mul hp.ne_zero hr0, hp.primeFactors]
        ext q
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
        tauto
      have hcop := hp.coprime_iff_not_dvd.mpr hpr
      simp only [Pi.sub_apply, primeFreeSourcePart, primeSourceDilation,
        dvd_mul_right, if_true, Nat.mul_div_right _ hp.pos, if_neg hpr, zero_sub]
      rw [retainedPrimeMobiusCoefficient, retainedPrimeMobiusCoefficient,
        ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
        ArithmeticFunction.moebius_apply_prime hp, hlab]
      push_cast
      ring
  · have hpf : p ∉ n.primeFactors := fun h => hpn (Nat.mem_primeFactors.mp h).2.1
    have hlab : n.primeFactors ∩ insert p P = n.primeFactors ∩ P := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hqn, hq | hq⟩
        · exact False.elim (hpf (hq ▸ hqn))
        · exact ⟨hqn, hq⟩
      · rintro ⟨hqn, hq⟩
        exact ⟨hqn, Or.inr hq⟩
    simp [primeFreeSourcePart, primeSourceDilation, hpn, retainedPrimeMobiusCoefficient, hlab]


open scoped BigOperators

/-- A finite retained functional gives a uniform bound for its complete Möbius sequence. -/
lemma norm_retainedPrimeMobiusCoefficient_le (P : Finset ℕ) (y : Finset ℕ → ℂ) (n : ℕ) :
    ‖retainedPrimeMobiusCoefficient P y n‖ ≤ ∑ R ∈ P.powerset, ‖y R‖ := by
  have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  calc
    _ = ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖y (n.primeFactors ∩ P)‖ := by
      rw [retainedPrimeMobiusCoefficient, norm_mul]
    _ ≤ ‖y (n.primeFactors ∩ P)‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (norm_nonneg _)
    _ ≤ _ := Finset.single_le_sum (fun _ _ => norm_nonneg _)
      (Finset.mem_powerset.mpr Finset.inter_subset_right)

/-- The actual weighted Möbius L-series converges absolutely on the Euler half-plane. -/
lemma LSeriesSummable_retainedPrimeMobiusCoefficient (P : Finset ℕ) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (retainedPrimeMobiusCoefficient P y) s :=
  LSeriesSummable_of_bounded_of_one_lt_re (fun n _ => norm_retainedPrimeMobiusCoefficient_le P y n) hs

private lemma LSeriesSummable_retainedPrimeFree (P : Finset ℕ) (y : Finset ℕ → ℂ) (p : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y)) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := ∑ R ∈ P.powerset, ‖y R‖) _ hs
  intro n hn
  by_cases hp : p ∣ n
  · simp only [primeFreeSourcePart, if_pos hp, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  · simpa only [primeFreeSourcePart, if_neg hp] using norm_retainedPrimeMobiusCoefficient_le P y n

private lemma LSeriesSummable_retainedPrimeFree_dilation
    (P : Finset ℕ) (y : Finset ℕ → ℂ) (p : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (primeSourceDilation p (primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y))) s := by
  apply LSeriesSummable_of_bounded_of_one_lt_re (m := ∑ R ∈ P.powerset, ‖y R‖) _ hs
  intro n hn
  by_cases hp : p ∣ n
  · simp only [primeSourceDilation, if_pos hp]
    by_cases hpp : p ∣ n / p
    · simp only [primeFreeSourcePart, if_pos hpp, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    · simpa only [primeFreeSourcePart, if_neg hpp] using
        norm_retainedPrimeMobiusCoefficient_le P y (n / p)
  · simp only [primeSourceDilation, if_neg hp, norm_zero]
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

/-- Removing an unretained prime divides its complete weighted series by exactly one Euler factor. -/
lemma one_sub_cpow_mul_LSeries_retainedPrimeFree
    (P : Finset ℕ) (y : Finset ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    {s : ℂ} (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) *
      LSeries (primeFreeSourcePart p (retainedPrimeMobiusCoefficient P y)) s =
      LSeries (retainedPrimeMobiusCoefficient P y) s := by
  nth_rw 2 [retainedPrimeMobiusCoefficient_eq_primeFree_sub_dilation P y hp hpP]
  rw [LSeries_sub (LSeriesSummable_retainedPrimeFree P y p hs)
    (LSeriesSummable_retainedPrimeFree_dilation P y p hs),
    LSeries_primeSourceDilation hp.pos _ (primeFreeSourcePart_zero p _) s]
  ring

/-- Exact insertion recursion for the full infinite retained-source L-series. -/
lemma one_sub_cpow_mul_LSeries_retainedPrimeMobius_insert
    (P : Finset ℕ) (y : Finset ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P)
    {s : ℂ} (hs : 1 < s.re) :
    (1 - (p : ℂ) ^ (-s)) * LSeries (retainedPrimeMobiusCoefficient (insert p P) y) s =
      LSeries (retainedPrimeMobiusCoefficient P y) s - (p : ℂ) ^ (-s) *
        LSeries (retainedPrimeMobiusCoefficient P (fun R => y (insert p R))) s := by
  rw [retainedPrimeMobiusCoefficient_insert_eq_primeFree_sub_dilation P y hp,
    LSeries_sub (LSeriesSummable_retainedPrimeFree P y p hs)
      (LSeriesSummable_retainedPrimeFree_dilation P (fun R => y (insert p R)) p hs),
    LSeries_primeSourceDilation hp.pos _ (primeFreeSourcePart_zero p _) s]
  have h0 := one_sub_cpow_mul_LSeries_retainedPrimeFree P y hp hpP hs
  have h1 := one_sub_cpow_mul_LSeries_retainedPrimeFree P (fun R => y (insert p R)) hp hpP hs
  linear_combination h0 - (p : ℂ) ^ (-s) * h1


/-- The literal finite Möbius numerator obeys the same retained-prime recursion. -/
lemma retainedPrimeDirichletNumerator_insert (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (y : Finset ℕ → ℂ) {p : ℕ} (hp : p.Prime) (hpP : p ∉ P) (s : ℂ) :
    finiteDirichletPolynomial (retainedPrimeDirichletCoefficients (insert p P) y) s =
      finiteDirichletPolynomial (retainedPrimeDirichletCoefficients P y) s -
        (p : ℂ) ^ (-s) * finiteDirichletPolynomial
          (retainedPrimeDirichletCoefficients P (fun R => y (insert p R))) s := by
  have hi : ∀ q ∈ insert p P, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hP q hq
  rw [finiteDirichletPolynomial_retainedPrime_eq_sum _ hi,
    finiteDirichletPolynomial_retainedPrime_eq_sum _ hP,
    finiteDirichletPolynomial_retainedPrime_eq_sum _ hP,
    Finset.sum_powerset_insert hpP, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  have hRP : R ⊆ P := Finset.mem_powerset.mp hR
  have hpR : p ∉ R := fun h => hpP (hRP h)
  have hRprime : ∀ q ∈ R, q.Prime := fun q hq => hP q (hRP hq)
  have hiR : ∀ q ∈ insert p R, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hRprime q hq
  have hmu : ArithmeticFunction.moebius (∏ q ∈ insert p R, q) =
      -ArithmeticFunction.moebius (∏ q ∈ R, q) := by
    rw [GibbsGas.moebius_prod_primes hiR, GibbsGas.moebius_prod_primes hRprime,
      Finset.card_insert_of_notMem hpR, pow_succ]
    ring
  rw [hmu, Finset.prod_insert hpR, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  push_cast
  ring

/-- Multiplication by the complete retained Euler denominator leaves exactly the
literal finite Möbius numerator times reciprocal zeta. -/
lemma prod_euler_mul_LSeries_retainedPrimeMobiusCoefficient
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    (∏ p ∈ P, (1 - (p : ℂ) ^ (-s))) * LSeries (retainedPrimeMobiusCoefficient P y) s =
      finiteDirichletPolynomial (retainedPrimeDirichletCoefficients P y) s /
        riemannZeta s := by
  classical
  induction P using Finset.induction_on generalizing y with
  | empty =>
    have hf : retainedPrimeMobiusCoefficient ∅ y =
        y ∅ • (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) := by
      ext n
      simp [retainedPrimeMobiusCoefficient, smul_eq_mul, mul_comm]
    rw [Finset.prod_empty, one_mul, hf, LSeries_smul,
      LSeries_moebius_eq_inv_riemannZeta hs,
      finiteDirichletPolynomial_retainedPrime_eq_sum _ (by simp)]
    simp [div_eq_mul_inv]
  | @insert p P hpP ih =>
    have hp := hP p (Finset.mem_insert_self p P)
    have hP' : ∀ q ∈ P, q.Prime := fun q hq => hP q (Finset.mem_insert_of_mem hq)
    rw [Finset.prod_insert hpP, mul_comm (1 - (p : ℂ) ^ (-s)), mul_assoc,
      one_sub_cpow_mul_LSeries_retainedPrimeMobius_insert P y hp hpP hs,
      mul_sub, ← mul_assoc, mul_comm _ ((p : ℂ) ^ (-s)), mul_assoc,
      ih hP' y, ih hP' (fun R => y (insert p R)),
      retainedPrimeDirichletNumerator_insert P hP' y hp hpP]
    ring

/-- Exact Euler decomposition of the complete source weighted by any retained
finite-prime functional, with absolute convergence supplied on `Re s>1`. -/
lemma LSeries_retainedPrimeMobiusCoefficient_eq
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (y : Finset ℕ → ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (retainedPrimeMobiusCoefficient P y) s =
      finiteDirichletPolynomial (retainedPrimeDirichletCoefficients P y) s /
        (riemannZeta s * ∏ p ∈ P, (1 - (p : ℂ) ^ (-s))) := by
  have he : (∏ p ∈ P, (1 - (p : ℂ) ^ (-s))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact one_sub_primeCpow_neg_ne_zero (by linarith : 0 < s.re) ⟨p, hP p hp⟩
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have h := prod_euler_mul_LSeries_retainedPrimeMobiusCoefficient P hP y hs
  apply (eq_div_iff (mul_ne_zero hz he)).mpr
  apply (mul_right_cancel₀ (b := riemannZeta s) hz)
  field_simp at h ⊢
  linear_combination h

end RHTower
