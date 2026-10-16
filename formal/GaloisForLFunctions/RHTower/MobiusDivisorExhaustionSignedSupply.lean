import GaloisForLFunctions.RHTower.MobiusDivisorExhaustionPrimeCapacity

/-!
# History-independent signed capacity

A single proportional cutoff admits enough helpers of both signs to pay its
mandatory prime. The counting margin includes all previously consumed helpers.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower.PaidExhaustion
open GaloisForLFunctions.HTGeometry

private lemma positive_source (b N p : ℕ) (hb : 8 ≤ b)
    (hp : p ∈ primesInIoc (b*N) ((b+1)*N)) :
    mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p} =
      singletonSource (7*(b+1)*N) p := by
  obtain ⟨hpp, hlo, hhi⟩ := mem_primesInIoc hp
  have hN : 1 ≤ N := by have := hpp.pos; nlinarith
  apply singleton_eq_source _ _ hpp
  · intro h
    have hh := mem_range.mp (mem_filter.mp h).1
    nlinarith
  · apply selectionPrimes_mono
    have hq : (7*(b+1)*N)/p < 8 :=
      (Nat.div_lt_iff_lt_mul hpp.pos).mpr (by nlinarith)
    omega

private lemma negative_source (N p : ℕ)
    (hp : p ∈ primesInIoc (2*N) (3*N)) :
    Real.sqrt N/40 ≤ -singletonSource (4*N) p := by
  obtain ⟨hpp, hlo, hhi⟩ := mem_primesInIoc hp
  have hN : 1 ≤ N := by have := hpp.pos; omega
  have hpM : p < 4*N := by omega
  have hMp : 4*N ≤ 2*p := by omega
  have hc : mobiusDivisorSelectionPrimes (4*N/p+1) ⊆ (∅ : Finset ℕ) := by
    intro q hq
    obtain ⟨hqr, hqp⟩ := mem_filter.mp hq
    have hq' := mem_range.mp hqr
    have hd : 4*N/p < 2 := (Nat.div_lt_iff_lt_mul hpp.pos).mpr (by omega)
    have := hqp.two_le
    omega
  rw [← singleton_eq_source (4*N) ∅ hpp (by simp) hc,
    mobiusDivisorSelectionFibre_late_prime hpp hpM hMp ∅ {p} (by simp) (by simp)]
  simp only [if_true, mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime hpp, Int.cast_neg, Int.cast_one,
    neg_one_mul, neg_neg]
  rw [divisorUnsignedDilationChannel_eq_first_block hpp.one_le hpM hMp]
  have hdef : (1/10:ℝ) ≤ primeFreeDivisorDefect 1 := by
    have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
    norm_num [harmonic, Finset.sum_range_succ, Real.log_four_eq] at h
    norm_num [primeFreeDivisorDefect]
    linarith [Real.log_two_lt_d9]
  have hroot : Real.sqrt p ≤ (7/4:ℝ)*Real.sqrt N := by
    have hpSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hpR : (p:ℝ) ≤ 3*N := by exact_mod_cast hhi
    nlinarith [Real.sqrt_nonneg (p:ℝ), Real.sqrt_nonneg (N:ℝ)]
  have h4 : Real.sqrt (4*N:ℕ) = 2*Real.sqrt N := by
    rw [Nat.cast_mul, Real.sqrt_mul (by norm_num)]
    norm_num
  rw [h4]
  have hgap : Real.sqrt N/4 ≤ 2*Real.sqrt N-Real.sqrt p := by linarith only [hroot]
  have h1 := mul_le_mul_of_nonneg_right hgap (show (0:ℝ) ≤ 1/10 by norm_num)
  have h2 := mul_le_mul_of_nonneg_left hdef
    (show 0 ≤ 2*Real.sqrt N-Real.sqrt p from (by positivity : 0 ≤ Real.sqrt N/4).trans hgap)
  linarith only [h1, h2]

/-- A fixed supply certificate. `exists_primeCapacity` below supplies it without
an assumed sign, source-size, or counting hypothesis. -/
structure PrimeCapacity where
  factor : ℕ
  budget : ℕ
  threshold : ℕ
  factor_large : 2 ≤ factor
  budget_pos : 1 ≤ budget
  threshold_large : factor+1 < threshold
  supply : ∀ r : ℕ, threshold ≤ r → ∃ U V : Finset ℕ,
    4*budget*Nat.primeCounting r ≤ U.card ∧
    4*budget*Nat.primeCounting r ≤ V.card ∧
    (∀ q ∈ U, q.Prime ∧ r < q ∧ q < factor*r ∧
      |singletonSource (factor*r) r| ≤ (budget:ℝ)*singletonSource (factor*r) q) ∧
    (∀ q ∈ V, q.Prime ∧ r < q ∧ q < factor*r ∧
      |singletonSource (factor*r) r| ≤ (budget:ℝ)*(-singletonSource (factor*r) q))

/-- The actual divisor source supplies one fixed capacity for an unbounded
inherited prime-processing history. -/
theorem exists_primeCapacity : Nonempty PrimeCapacity := by
  obtain ⟨b, hb, c, hc, hf⟩ := exists_mobiusDivisorPositivePrimeWindow
  let a : ℝ := min c (1/40)
  have ha : 0 < a := lt_min hc (by norm_num)
  let C : ℕ := 448*(b+1)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨n, hn, hsource⟩ := exists_source_scale C hC a ha
  let A := C*n
  let u := 64*b*n
  let v := 64*(b+1)*n
  let j := 112*(b+1)*n
  have hu : 2 ≤ u := by dsimp [u]; nlinarith
  have huv : u < v := by dsimp [u,v]; nlinarith
  have hw : 8*(4*n) ≤ v-u := by
    have hh : 8*(4*n)+u ≤ v := by dsimp [u,v]; nlinarith
    omega
  have hj : 1 ≤ j := by dsimp [j]; nlinarith
  have hcountU := eventually_window_capacity u v (4*n) hu huv hw
  have hcountV := eventually_window_capacity (2*j) (3*j) (4*n)
    (by omega) (by omega) (by
      have hh : 8*(4*n)+2*j ≤ 3*j := by dsimp [j]; nlinarith
      omega)
  obtain ⟨B, hB⟩ := eventually_atTop.mp (hcountU.and hcountV)
  refine ⟨⟨A, n, max B (A+2), ?_, hn, by omega, ?_⟩⟩
  · dsimp [A,C]; nlinarith
  intro r hr
  have hrB : B ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by have := (le_max_right B (A+2)).trans hr; omega
  have hnR : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have htarget : |singletonSource (A*r) r| ≤ (n:ℝ)*a*Real.sqrt (n*r:ℕ) := by
    rw [singletonSource_mul A r hrpos, abs_mul, abs_neg,
      abs_of_nonneg (Real.sqrt_nonneg (r:ℝ))]
    have hh := mul_le_mul_of_nonneg_left hsource (Real.sqrt_nonneg (r:ℝ))
    simpa [A, Nat.cast_mul, Real.sqrt_mul hnR, mul_comm, mul_left_comm, mul_assoc] using hh
  refine ⟨primesInIoc (u*r) (v*r), primesInIoc (2*j*r) (3*j*r),
    (hB r hrB).1, (hB r hrB).2, ?_, ?_⟩
  · intro q hq
    obtain ⟨hqp, hqlo, hqhi⟩ := mem_primesInIoc hq
    have hwin : q ∈ primesInIoc (b*(64*n*r)) ((b+1)*(64*n*r)) := by
      convert hq using 1 <;> dsimp [u,v] <;> congr 1 <;> ring
    have he : A*r = 7*(b+1)*(64*n*r) := by dsimp [A,C]; ring
    have hsign := hf (64*n*r) q hwin
    rw [positive_source b (64*n*r) q hb hwin, ← he] at hsign
    have hroot : Real.sqrt (n*r:ℕ) ≤ Real.sqrt (64*n*r:ℕ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.mul_le_mul_right r (show n ≤ 64*n by omega)
    have hlow : a*Real.sqrt (n*r:ℕ) ≤ singletonSource (A*r) q :=
      (mul_le_mul (min_le_left _ _) hroot (Real.sqrt_nonneg _) hc.le).trans hsign
    refine ⟨hqp, ?_, ?_, htarget.trans ?_⟩
    · have hur : r ≤ u*r := by nlinarith
      omega
    · have hvA : v < A := by dsimp [v,A,C]; nlinarith
      exact hqhi.trans_lt (Nat.mul_lt_mul_of_pos_right hvA hrpos)
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlow hnR
  · intro q hq
    obtain ⟨hqp, hqlo, hqhi⟩ := mem_primesInIoc hq
    have hwin : q ∈ primesInIoc (2*(j*r)) (3*(j*r)) := by simpa only [mul_assoc] using hq
    have he : A*r = 4*(j*r) := by dsimp [A,C,j]; ring
    have hsign := negative_source (j*r) q hwin
    rw [← he] at hsign
    have hroot : Real.sqrt (n*r:ℕ) ≤ Real.sqrt (j*r:ℕ) := by
      apply Real.sqrt_le_sqrt
      exact_mod_cast Nat.mul_le_mul_right r (show n ≤ j by dsimp [j]; nlinarith)
    have hlow : a*Real.sqrt (n*r:ℕ) ≤ -singletonSource (A*r) q := by
      have hh := mul_le_mul (min_le_right c (1/40)) hroot
        (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 1/40)
      exact hh.trans (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hsign)
    refine ⟨hqp, ?_, ?_, htarget.trans ?_⟩
    · have hlowr : r ≤ 2*j*r := by nlinarith
      omega
    · rw [he]
      nlinarith
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlow hnR

end RHTower.PaidExhaustion
