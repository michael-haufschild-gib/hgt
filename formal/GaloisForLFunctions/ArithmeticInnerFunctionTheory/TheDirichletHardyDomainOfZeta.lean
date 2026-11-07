import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Shifted zeta multiplication on the Dirichlet Hardy space

Arithmetic coefficient sequences have their unused coordinate at `0` fixed to zero.
Convolution by `n ↦ n^(-ε)` has trivial square-summable domain for `ε ≤ 1/2` and
dense domain for `ε > 1/2`. The obstruction follows by restricting the divisor sum
to prime multiples of a fixed integer; the positive result follows from square
summability of the weight and density of finite coordinate sums.
-/

noncomputable section
open scoped BigOperators Topology
open Filter

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

/-- Coefficients of multiplication by `ζ(s+ε)` in a Dirichlet series. -/
def shiftedZetaConvolution (ε : ℝ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, ((((n / d : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * a d

private theorem mem_two_iff {ι : Type*} {a : ι → ℂ} :
    Memℓp a 2 ↔ Summable (fun n => ‖a n‖ ^ 2) := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    (memℓp_gen_iff (p := 2) (f := a) (by norm_num))

private theorem mem_two_comp {ι κ : Type*} {a : ι → ℂ} (ha : Memℓp a 2)
    {f : κ → ι} (hf : Function.Injective f) : Memℓp (fun k => a (f k)) 2 := by
  exact mem_two_iff.mpr ((mem_two_iff.mp ha).comp_injective hf)

private theorem sum_divisors_prime_mul (f : ℕ → ℂ) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    (∑ d ∈ (p * m).divisors, f d) =
      (∑ d ∈ m.divisors, f d) + ∑ d ∈ m.divisors, f (p * d) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image]
  · rw [Finset.sum_product]
    simp [hp.divisors, hp.ne_one.symm]
  · intro i hi j hj hij
    exact (hp.coprime_iff_not_dvd.mpr hpm).mul_injOn_divisors hi hj hij

/-- The prime slice of zeta convolution separates into one fixed coefficient and
finitely many dilated input sequences. -/
theorem shiftedZetaConvolution_prime_mul (ε : ℝ) (a : ℕ → ℂ) {p m : ℕ}
    (hp : p.Prime) (hpm : ¬ p ∣ m) :
    shiftedZetaConvolution ε a (p * m) =
      (((p : ℝ) ^ (-ε) : ℝ) : ℂ) * shiftedZetaConvolution ε a m +
        ∑ d ∈ m.divisors, ((((m / d : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * a (p * d) := by
  rw [shiftedZetaConvolution, sum_divisors_prime_mul _ hp hpm,
    shiftedZetaConvolution, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro d hd
    rw [Nat.mul_div_assoc p (Nat.mem_divisors.mp hd).1, Nat.cast_mul,
      Real.mul_rpow (by positivity) (by positivity), Complex.ofReal_mul, mul_assoc]
  · apply Finset.sum_congr rfl
    intro d _
    rw [Nat.mul_div_mul_left _ _ hp.pos]

private theorem mem_two_prime_weight_iff (ε : ℝ) :
    Memℓp (fun p : Nat.Primes => (((p : ℝ) ^ (-ε) : ℝ) : ℂ)) 2 ↔ 1 / 2 < ε := by
  rw [mem_two_iff]
  have heq : (fun p : Nat.Primes => ‖(((p : ℝ) ^ (-ε) : ℝ) : ℂ)‖ ^ 2) =
      (fun p : Nat.Primes => (p : ℝ) ^ (-ε * 2)) := by
    funext p
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  rw [heq, Nat.Primes.summable_rpow]
  constructor <;> intro h <;> linarith

private theorem prime_not_dvd_eventually {m : ℕ} (hm : m ≠ 0) :
    ∀ᶠ p : Nat.Primes in cofinite, ¬ (p : ℕ) ∣ m := by
  have hfinite : {p : Nat.Primes | (p : ℕ) ∣ m}.Finite := by
    have h := (m.divisors.finite_toSet).preimage
      (f := fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn
    apply h.subset
    intro p hp
    exact Nat.mem_divisors.mpr ⟨hp, hm⟩
  exact hfinite.compl_mem_cofinite

private theorem convolution_eq_zero_of_mem_two {ε : ℝ} (hε : ε ≤ 1 / 2)
    {a : ℕ → ℂ} (ha : Memℓp a 2) (hb : Memℓp (shiftedZetaConvolution ε a) 2)
    {m : ℕ} (hm : m ≠ 0) : shiftedZetaConvolution ε a m = 0 := by
  have hdil : ∀ d : ℕ, d ≠ 0 →
      Function.Injective (fun p : Nat.Primes => (p : ℕ) * d) := by
    intro d hd p q hpq
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) hpq)
  have hleft := mem_two_comp hb (hdil m hm)
  have hright : Memℓp (fun p : Nat.Primes =>
      ∑ d ∈ m.divisors, ((((m / d : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * a (p * d)) 2 := by
    apply Memℓp.finsetSum
    intro d hd
    exact (mem_two_comp ha (hdil d (Nat.pos_of_mem_divisors hd).ne')).const_mul _
  have hdiff := mem_two_iff.mp (hleft.sub hright)
  have heq : (fun p : Nat.Primes => ‖shiftedZetaConvolution ε a (p * m) -
      ∑ d ∈ m.divisors, ((((m / d : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * a (p * d)‖ ^ 2)
      =ᶠ[cofinite] (fun p : Nat.Primes =>
        ‖(((p : ℝ) ^ (-ε) : ℝ) : ℂ) * shiftedZetaConvolution ε a m‖ ^ 2) := by
    filter_upwards [prime_not_dvd_eventually hm] with p hp
    rw [shiftedZetaConvolution_prime_mul ε a p.2 hp, add_sub_cancel_right]
  have hprod := mem_two_iff.mpr ((summable_congr_cofinite heq).mp hdiff)
  by_contra hmne
  have hw : Memℓp (fun p : Nat.Primes => (((p : ℝ) ^ (-ε) : ℝ) : ℂ)) 2 := by
    have h := hprod.const_mul (shiftedZetaConvolution ε a m)⁻¹
    simpa only [mul_left_comm (shiftedZetaConvolution ε a m)⁻¹,
      inv_mul_cancel₀ hmne, mul_one] using h
  exact (not_lt_of_ge hε) ((mem_two_prime_weight_iff ε).mp hw)

/-- At and below the half-shift, the maximal square-summable convolution domain
contains only the zero arithmetic sequence. -/
theorem eq_zero_of_shiftedZetaConvolution_mem_two {ε : ℝ} (hε : ε ≤ 1 / 2)
    {a : ℕ → ℂ} (ha0 : a 0 = 0) (ha : Memℓp a 2)
    (hb : Memℓp (shiftedZetaConvolution ε a) 2) : a = 0 := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · simpa only [hn, Pi.zero_apply] using ha0
    have hsum : shiftedZetaConvolution ε a n = a n := by
      rw [shiftedZetaConvolution, Finset.sum_eq_single n]
      · simp [Nat.div_self (Nat.pos_of_ne_zero hn)]
      · intro d hd hdn
        have hdle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.mem_divisors.mp hd).1
        rw [ih d (lt_of_le_of_ne hdle hdn), Pi.zero_apply, mul_zero]
      · intro hnmem
        exact (hnmem (Nat.mem_divisors.mpr ⟨dvd_refl n, hn⟩)).elim
    simpa only [hsum, Pi.zero_apply] using convolution_eq_zero_of_mem_two hε ha hb hn

private theorem mem_two_nat_weight {ε : ℝ} (hε : 1 / 2 < ε) :
    Memℓp (fun n : ℕ => (((n : ℝ) ^ (-ε) : ℝ) : ℂ)) 2 := by
  apply mem_two_iff.mpr
  have h := Real.summable_nat_rpow.mpr (show -ε * 2 < -1 by linarith)
  convert h using 1
  funext n
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul_natCast (by positivity)]
  norm_num

private theorem convolution_single (ε : ℝ) (d : ℕ) (c : ℂ) (n : ℕ) :
    shiftedZetaConvolution ε (Pi.single d c) n =
      if d ∈ n.divisors then ((((n / d : ℕ) : ℝ) ^ (-ε) : ℝ) : ℂ) * c else 0 := by
  classical
  simp [shiftedZetaConvolution, Pi.single_apply, mul_ite]

/-- A coordinate vector is in the convolution domain above the half-shift. -/
theorem shiftedZetaConvolution_single_mem_two {ε : ℝ} (hε : 1 / 2 < ε)
    (d : ℕ) (c : ℂ) : Memℓp (shiftedZetaConvolution ε (Pi.single d c)) 2 := by
  by_cases hd : d = 0
  · subst d
    have hz : shiftedZetaConvolution ε (Pi.single 0 c) = 0 := by
      funext n
      simp [convolution_single]
    rw [hz]
    exact zero_memℓp
  have hcomp : Memℓp (fun n : ℕ =>
      shiftedZetaConvolution ε (Pi.single d c) (d * n)) 2 := by
    apply ((mem_two_nat_weight hε).const_mul c).mono'
    intro n
    by_cases hn : n = 0
    · simp only [hn, mul_zero, shiftedZetaConvolution, Nat.divisors_zero,
        Finset.sum_empty, norm_zero]
      exact norm_nonneg _
    have hmem : d ∈ (d * n).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_mul_right d n, mul_ne_zero hd hn⟩
    have hdiv : d * n / d = n := by
      simpa only [mul_one, Nat.div_one] using
        Nat.mul_div_mul_left n 1 (Nat.pos_of_ne_zero hd)
    rw [convolution_single, if_pos hmem, hdiv, norm_mul, norm_mul, mul_comm]
  have hinj : Function.Injective (fun n : ℕ => d * n) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hd) (by simpa [mul_comm] using hij)
  apply mem_two_iff.mpr
  refine (hinj.summable_iff (f := fun n =>
    ‖shiftedZetaConvolution ε (Pi.single d c) n‖ ^ 2) ?_).mp (mem_two_iff.mp hcomp)
  intro n hn
  have hnot : d ∉ n.divisors := by
    intro hmem
    obtain ⟨k, hk⟩ := (Nat.mem_divisors.mp hmem).1
    exact hn ⟨k, hk.symm⟩
  simp only [convolution_single, if_neg hnot, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow]

private theorem convolution_finset_sum {ι : Type*} (ε : ℝ) (S : Finset ι)
    (a : ι → ℕ → ℂ) :
    shiftedZetaConvolution ε (fun n => ∑ i ∈ S, a i n) =
      fun n => ∑ i ∈ S, shiftedZetaConvolution ε (a i) n := by
  funext n
  simp only [shiftedZetaConvolution, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Every finitely supported coefficient sequence lies in the domain above `1/2`. -/
theorem shiftedZetaConvolution_mem_two_of_finite_support {ε : ℝ} (hε : 1 / 2 < ε)
    {a : ℕ → ℂ} (ha : (Function.support a).Finite) :
    Memℓp (shiftedZetaConvolution ε a) 2 := by
  classical
  have heq : a = fun n => ∑ i ∈ ha.toFinset, Pi.single i (a i) n := by
    funext n
    by_cases hn : n ∈ ha.toFinset
    · simp [Pi.single_apply, hn]
    · have han : a n = 0 := by simpa [Function.support] using hn
      simp [Pi.single_apply, hn, han]
  rw [heq, convolution_finset_sum]
  apply Memℓp.finsetSum
  intro d _
  exact shiftedZetaConvolution_single_mem_two hε d _

/-- The maximal convolution domain in `ℓ²`, with the unused index `0` fixed to zero. -/
def shiftedZetaDomain (ε : ℝ) : Set (lp (fun _ : ℕ => ℂ) 2) :=
  {a | a 0 = 0 ∧ Memℓp (shiftedZetaConvolution ε a) 2}

private theorem zero_mem_shiftedZetaDomain (ε : ℝ) : 0 ∈ shiftedZetaDomain ε := by
  refine ⟨rfl, ?_⟩
  have hzero : shiftedZetaConvolution ε (0 : ℕ → ℂ) = 0 := by
    funext n
    simp [shiftedZetaConvolution]
  change Memℓp (shiftedZetaConvolution ε (0 : ℕ → ℂ)) 2
  rw [hzero]
  exact zero_memℓp

/-- The maximal domain is trivial at and below the critical half-shift. -/
theorem shiftedZetaDomain_eq_singleton {ε : ℝ} (hε : ε ≤ 1 / 2) :
    shiftedZetaDomain ε = {0} := by
  ext a
  constructor
  · intro ha
    exact Set.mem_singleton_iff.mpr (lp.ext
      (eq_zero_of_shiftedZetaConvolution_mem_two hε ha.1 (lp.memℓp a) ha.2))
  · rintro rfl
    exact zero_mem_shiftedZetaDomain ε

private theorem lp_sum_apply {ι : Type*} (S : Finset ι)
    (a : ι → lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (∑ i ∈ S, a i) n = ∑ i ∈ S, a i n :=
  map_sum (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n) a S

/-- Above the half-shift the maximal domain is dense among arithmetic coefficient
sequences. Finite coordinate sums approximate every square-summable sequence. -/
theorem closure_shiftedZetaDomain_of_half_lt {ε : ℝ} (hε : 1 / 2 < ε) :
    closure (shiftedZetaDomain ε) = {a : lp (fun _ : ℕ => ℂ) 2 | a 0 = 0} := by
  apply Set.Subset.antisymm
  · have hclosed : IsClosed {a : lp (fun _ : ℕ => ℂ) 2 | a 0 = 0} :=
      isClosed_eq (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 0).continuous continuous_const
    exact closure_minimal (fun _ ha => ha.1) hclosed
  · intro a ha
    change a 0 = 0 at ha
    apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) a)
    apply Filter.Eventually.of_forall
    intro S
    refine ⟨?_, ?_⟩
    · rw [lp_sum_apply]
      simp [lp.single_apply, Pi.single_apply, ha]
    · apply shiftedZetaConvolution_mem_two_of_finite_support hε
      apply S.finite_toSet.subset
      intro n hn
      by_contra hnS
      change n ∉ S at hnS
      apply hn
      rw [lp_sum_apply]
      simp [lp.single_apply, Pi.single_apply, hnS]

/-- The complete domain-closure classification has a sharp transition at `ε=1/2`. -/
theorem closure_shiftedZetaDomain (ε : ℝ) :
    closure (shiftedZetaDomain ε) =
      if ε ≤ 1 / 2 then {0} else {a : lp (fun _ : ℕ => ℂ) 2 | a 0 = 0} := by
  split_ifs with hε
  · rw [shiftedZetaDomain_eq_singleton hε, isClosed_singleton.closure_eq]
  · exact closure_shiftedZetaDomain_of_half_lt (lt_of_not_ge hε)

/-- A nonzero square-summable sequence and its shifted zeta convolution coexist
exactly above the half-shift. -/
theorem shiftedZetaDomain_nontrivial_iff (ε : ℝ) :
    (∃ a ∈ shiftedZetaDomain ε, a ≠ 0) ↔ 1 / 2 < ε := by
  constructor
  · rintro ⟨a, ha, hane⟩
    by_contra hε
    rw [shiftedZetaDomain_eq_singleton (le_of_not_gt hε)] at ha
    exact hane (Set.mem_singleton_iff.mp ha)
  · intro hε
    refine ⟨lp.single 2 1 (1 : ℂ), ⟨?_, ?_⟩, ?_⟩
    · simp [lp.single_apply]
    · exact shiftedZetaConvolution_single_mem_two hε 1 1
    · intro hzero
      have h := congrArg (fun a : lp (fun _ : ℕ => ℂ) 2 => a 1) hzero
      simp [lp.single_apply] at h

#print axioms shiftedZetaConvolution_prime_mul
#print axioms eq_zero_of_shiftedZetaConvolution_mem_two
#print axioms shiftedZetaConvolution_single_mem_two
#print axioms shiftedZetaConvolution_mem_two_of_finite_support
#print axioms shiftedZetaDomain_eq_singleton
#print axioms closure_shiftedZetaDomain_of_half_lt
#print axioms closure_shiftedZetaDomain
#print axioms shiftedZetaDomain_nontrivial_iff

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
