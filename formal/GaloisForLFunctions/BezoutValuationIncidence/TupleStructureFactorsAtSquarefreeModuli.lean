import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticLargeSieveForSquarefreeModuli
import GaloisForLFunctions.BezoutValuationIncidence.CanonicalPrimitiveSpectralFormAndJordanWindowEnergy

/-!
# Tuple structure factors at squarefree moduli and Hardy–Littlewood admissibility

For a finite set `H` of `k` shifts, the centered tuple response `Σ_{h ∈ H} (s(n + h) - H_c)` is the
exponential sum `Σ_{ζ ≠ 1} Y(ord ζ) (Σ_{h ∈ H} ζ^h) ζ^n`, so by Parseval its period variance is

`Var_H(c) = Σ_{2 ≤ q ≤ N} Y(q)² S_q(H)`,  `S_q(H) = Σ_{ζ primitive of order q} |Σ_{h ∈ H} ζ^h|²`.

The structure factor `S_q(H)` is the Montgomery sum of the set `H`. If `H` occupies `c_p` classes
modulo each prime `p`, Montgomery's inequality gives, for every squarefree `q`,

`S_q(H) ≥ k² Π_{p ∣ q} (p - c_p)/c_p`.

Hence the tuple variance dominates `k² Σ_{q squarefree} h_H(q) Y(q)²`. For a tuple admissible in
the sense of Hardy–Littlewood (each prime misses a class), every `h_H(q)` is at least `1/φ(q)`:
admissibility forces `Var_H(c) ≥ k² Σ_{2 ≤ q ≤ N squarefree} Y(q)²/φ(q)`. At a prime this is the
classical lower bound `S_p(H) ≥ k²/φ(p)`; the multiplicativity over the prime factors of `q` is the
new input.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower.Sieve
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The structure factor `S_q(H) = Σ_{ζ primitive of order q} |Σ_{h ∈ H} ζ^h|²`. -/
def tupleStructureFactor (q : ℕ) (H : Finset ℕ) : ℝ :=
  ∑ ζ ∈ primitiveRoots q ℂ, ‖∑ h ∈ H, ζ ^ h‖ ^ 2

/-- The centered tuple response `Σ_{h ∈ H} (s(n + h) - H_c)`. -/
def tupleResponse (N : ℕ) (c : ℕ → ℝ) (H : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ h ∈ H, (sieveSeq N c (n + h) - finiteHarmonicSum N c)

/-- The period variance of the tuple response. -/
def tupleVariance (N : ℕ) (c : ℕ → ℝ) (H : Finset ℕ) : ℝ :=
  (∑ n ∈ range N.factorial, tupleResponse N c H n ^ 2) / N.factorial

theorem tupleResponse_eq_spectral {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (H : Finset ℕ) (n : ℕ) :
    (tupleResponse N c H n : ℂ) = ∑ ζ ∈ primitiveRoots' N,
      ((selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h) * ζ ^ n := by
  rw [tupleResponse, Complex.ofReal_sum]
  simp_rw [sieveSeq_sub_harmonic_eq_sum_primitiveRoots' hN]
  rw [sum_comm]
  refine sum_congr rfl fun ζ _ => ?_
  rw [mul_sum, sum_mul]
  exact sum_congr rfl fun h _ => by rw [pow_add]; ring

/-- **Spectral form of the tuple variance.** `Var_H(c) = Σ_{2 ≤ q ≤ N} Y(q)² S_q(H)`. -/
theorem tupleVariance_eq_sum_structureFactor {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) (H : Finset ℕ) :
    tupleVariance N c H =
      ∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q ^ 2 * tupleStructureFactor q H := by
  classical
  have hP := Nat.factorial_pos N
  have hPar := sum_range_norm_sq_sum_mul_pow (P := N.factorial) (T := primitiveRoots' N)
    (fun ζ hζ => pow_factorial_eq_one_of_mem_responseRoots (mem_of_mem_erase hζ)) hP
    (fun ζ => (selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h)
  simp only [← tupleResponse_eq_spectral hN, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hPar
  unfold tupleVariance
  rw [hPar]
  have hP' : (N.factorial : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  rw [mul_div_cancel_left₀ _ hP']
  -- regroup the nontrivial frequencies by order
  have hfull' : ∑ ζ ∈ responseRoots N,
      ‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 =
      ∑ q ∈ Icc 1 N, ∑ ζ ∈ primitiveRoots q ℂ,
        ‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 := by
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum]
    exact sum_responseRoots_eq_sum_primitiveRoots N
      (fun ζ => (((‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 : ℝ)) : ℂ))
  have hsplit : ∑ ζ ∈ responseRoots N,
      ‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 =
      ‖(selbergMultiplesCoord N c 1 : ℂ) * (H.card : ℂ)‖ ^ 2 +
        ∑ ζ ∈ primitiveRoots' N,
          ‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 := by
    rw [primitiveRoots', ← add_sum_erase _ _ (one_mem_responseRoots hN), orderOf_one]
    simp
  have hIcc : Icc 1 N = insert 1 (Icc 2 N) := by
    ext q
    simp only [mem_insert, mem_Icc]
    omega
  rw [hIcc, sum_insert (by simp)] at hfull'
  have h1 : ∑ ζ ∈ primitiveRoots 1 ℂ,
      ‖(selbergMultiplesCoord N c (orderOf ζ) : ℂ) * ∑ h ∈ H, ζ ^ h‖ ^ 2 =
      ‖(selbergMultiplesCoord N c 1 : ℂ) * (H.card : ℂ)‖ ^ 2 := by
    simp [IsPrimitiveRoot.primitiveRoots_one]
  rw [hsplit, h1, add_left_cancel_iff] at hfull'
  rw [hfull']
  refine sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
  unfold tupleStructureFactor
  rw [mul_sum]
  refine sum_congr rfl fun ζ hζ => ?_
  rw [← ((mem_primitiveRoots hq0).mp hζ).eq_orderOf, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

/-- **Montgomery's lower bound for structure factors.** For squarefree `q`,
`S_q(H) ≥ k² Π_{p ∣ q} (p - c_p)/c_p`. -/
theorem tupleStructureFactor_ge {q : ℕ} (hq : Squarefree q) {H : Finset ℕ} (hH : H.Nonempty) :
    (H.card : ℝ) ^ 2 * ∏ p ∈ q.primeFactors,
        ((p : ℝ) - (occupiedClasses p H).card) / (occupiedClasses p H).card ≤
      tupleStructureFactor q H := by
  have hm := montgomery_prod_primes_ge hH (fun _ => 1) q.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Nat.prod_primeFactors_of_squarefree hq] at hm
  simp only [one_mul, sum_const, nsmul_eq_mul, mul_one, Complex.norm_natCast] at hm
  unfold tupleStructureFactor
  linarith

/-- **Admissible tuples force variance.** The tuple variance dominates
`k² Σ_{2 ≤ q ≤ N squarefree} h_H(q) Y(q)²`. -/
theorem tupleVariance_ge {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {H : Finset ℕ} (hH : H.Nonempty) :
    (H.card : ℝ) ^ 2 * ∑ q ∈ (Icc 2 N).filter Squarefree,
        (∏ p ∈ q.primeFactors,
          ((p : ℝ) - (occupiedClasses p H).card) / (occupiedClasses p H).card) *
          selbergMultiplesCoord N c q ^ 2 ≤ tupleVariance N c H := by
  rw [tupleVariance_eq_sum_structureFactor hN, mul_sum]
  calc ∑ q ∈ (Icc 2 N).filter Squarefree, (H.card : ℝ) ^ 2 *
        ((∏ p ∈ q.primeFactors,
          ((p : ℝ) - (occupiedClasses p H).card) / (occupiedClasses p H).card) *
          selbergMultiplesCoord N c q ^ 2)
      ≤ ∑ q ∈ (Icc 2 N).filter Squarefree,
          selbergMultiplesCoord N c q ^ 2 * tupleStructureFactor q H :=
        sum_le_sum fun q hq => by
          have := tupleStructureFactor_ge (mem_filter.mp hq).2 hH
          nlinarith [sq_nonneg (selbergMultiplesCoord N c q)]
    _ ≤ ∑ q ∈ Icc 2 N, selbergMultiplesCoord N c q ^ 2 * tupleStructureFactor q H :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun q _ _ =>
          mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)

/-- **Hardy–Littlewood admissibility.** If `H` misses a residue class modulo every prime, the tuple
variance is at least `k² Σ_{2 ≤ q ≤ N squarefree} Y(q)²/φ(q)`. -/
theorem tupleVariance_ge_of_admissible {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℝ) {H : Finset ℕ}
    (hH : H.Nonempty) (hadm : ∀ p, p.Prime → (occupiedClasses p H).card < p) :
    (H.card : ℝ) ^ 2 * ∑ q ∈ (Icc 2 N).filter Squarefree,
        selbergMultiplesCoord N c q ^ 2 / q.totient ≤ tupleVariance N c H := by
  refine le_trans ?_ (tupleVariance_ge hN c hH)
  refine mul_le_mul_of_nonneg_left (sum_le_sum fun q hq => ?_) (sq_nonneg _)
  have hsq := (mem_filter.mp hq).2
  have hq0 : q ≠ 0 := by have := (mem_Icc.mp (mem_filter.mp hq).1).1; omega
  -- each prime factor contributes at least `1/(p-1)`
  have hfac : ∀ p ∈ q.primeFactors, (1 : ℝ) / ((p : ℝ) - 1) ≤
      ((p : ℝ) - (occupiedClasses p H).card) / (occupiedClasses p H).card := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hc := hadm p hpp
    have hc0 : 0 < (occupiedClasses p H).card := occupiedClasses_card_pos hpp.pos hH
    have hcR : ((occupiedClasses p H).card : ℝ) ≤ (p : ℝ) - 1 := by
      have : (occupiedClasses p H).card ≤ p - 1 := by omega
      have h' : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
        rw [Nat.cast_sub hpp.one_lt.le, Nat.cast_one]
      rw [← h']
      exact_mod_cast this
    have hc0R : (0 : ℝ) < (occupiedClasses p H).card := by exact_mod_cast hc0
    have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
      have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      linarith
    rw [div_le_div_iff₀ hp1 hc0R]
    nlinarith
  have hprod : (1 : ℝ) / q.totient ≤ ∏ p ∈ q.primeFactors,
      ((p : ℝ) - (occupiedClasses p H).card) / (occupiedClasses p H).card := by
    have htot : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
      have h := Nat.totient_mul_prod_primeFactors q
      rw [Nat.prod_primeFactors_of_squarefree hsq] at h
      have hq0' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
      have hcast : (q.totient : ℝ) * q = q * ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
        have h' := congrArg (fun n : ℕ => (n : ℝ)) h
        push_cast at h'
        rw [h']
        congr 1
        refine prod_congr rfl fun p hp => ?_
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_lt.le, Nat.cast_one]
      have := mul_right_cancel₀ hq0' (hcast.trans (mul_comm _ _))
      exact this
    rw [htot, one_div, ← prod_inv_distrib]
    refine prod_le_prod (fun p hp => ?_) fun p hp => by rw [← one_div]; exact hfac p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    exact inv_nonneg.mpr (by linarith)
  calc selbergMultiplesCoord N c q ^ 2 / q.totient
      = (1 / (q.totient : ℝ)) * selbergMultiplesCoord N c q ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hprod (sq_nonneg _)

end

end GaloisForLFunctions.BezoutValuationIncidence
