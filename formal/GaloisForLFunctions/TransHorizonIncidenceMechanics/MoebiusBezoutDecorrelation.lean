import GaloisForLFunctions.TransHorizonIncidenceMechanics.SuccessorReserveHorizonLawAndPrimeDissipation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SlidingPeriodPoincareCoercivityAndHarmonicDecomposition
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.DivisorBound
import GaloisForLFunctions.BezoutValuationIncidence.BezoutSelbergDiagonalCoercivityAndHalfDecorrelation

/-!
# Bézout decorrelation of the Möbius observer

Over a full period the unit-shift correlation of a sieve response is `L · Q_Bez(N, c)`, the Bézout
coprime form. For the Möbius weight its Selberg coordinates are
`Y_N(f) = μ(f)/f · m_f(N/f)` with the coprime harmonic Möbius sums
`m_f(x) = Σ_{d ≤ x, (d,f) = 1} μ(d)/d`, so

`Q_Bez(N; μ) = Σ_{f ≤ N} μ(f) Y_N(f)² = Σ_{f ≤ N} μ(f)/f² · m_f(N/f)²`.

Every coprime harmonic sum of a squarefree `f` is bounded by `2^{ω(f)} = τ(f) ≪ f^{1/4}` (each prime
of `f` at most doubles the bound, through the recursion `m_{fp}(n) = m_f(n) + m_{fp}(n/p)/p`), and
tends to zero by the prime number theorem. The weights `f^{-2} τ(f)²` are summable, so dominated
convergence gives

`Q_Bez(N; μ) → 0`:

successive Möbius observations decorrelate completely over a period. The Selberg form
`Q_Sel = Σ φ(f)/f² · m_f(N/f)²` carries the non-summable weights `φ(f)/f²`, outside the reach of
this argument; the two forms differ exactly by the dissipation rate, `R_N = Q_Sel - Q_Bez`, so the
dissipation rate of the Möbius defect and the period mean square of the response become
asymptotically equal.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Bounds for coprime harmonic Möbius sums -/

theorem abs_coprimeHarmonicMoebius_one_le (n : ℕ) : |coprimeHarmonicMoebius 1 n| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [coprimeHarmonicMoebius]
  have h := RHTower.abs_sum_moebius_div_le_one n hn
  have he : coprimeHarmonicMoebius 1 n = ∑ d ∈ Icc 1 n, ((μ d : ℤ) : ℝ) / d := by
    unfold coprimeHarmonicMoebius
    exact sum_congr rfl fun d _ => by rw [if_pos (Nat.coprime_one_right d)]; rfl
  rw [he]; exact h

/-- Each prime of a squarefree modulus at most doubles the coprime harmonic sum:
`|m_{∏ s}(n)| ≤ 2^{|s|}` for every finite set `s` of primes. -/
theorem abs_coprimeHarmonicMoebius_prod_le (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) (n : ℕ) :
    |coprimeHarmonicMoebius (∏ p ∈ s, p) n| ≤ 2 ^ s.card := by
  induction s using Finset.induction generalizing n with
  | empty => simpa using abs_coprimeHarmonicMoebius_one_le n
  | insert p s hps ih =>
    have hp : p.Prime := hs p (mem_insert_self p s)
    have ih' := fun n => ih (fun q hq => hs q (mem_insert_of_mem hq)) n
    rw [prod_insert hps, card_insert_of_notMem hps]
    set f := ∏ q ∈ s, q
    have hpf : ¬ p ∣ f := by
      intro h
      obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp h
      have := (Nat.prime_dvd_prime_iff_eq hp (hs q (mem_insert_of_mem hq))).mp hpq
      exact hps (this ▸ hq)
    -- strong induction along `n ↦ n/p`
    induction n using Nat.strong_induction_on with
    | _ n ihn =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [coprimeHarmonicMoebius]
      have hstep := coprimeHarmonicMoebius_prime_step hp hpf n
      rw [mul_comm p f]
      have hrec : coprimeHarmonicMoebius (f * p) n =
          coprimeHarmonicMoebius f n + coprimeHarmonicMoebius (f * p) (n / p) / p := by linarith
      have hlt : n / p < n := Nat.div_lt_self hn hp.one_lt
      have h1 := ih' n
      have h2 := ihn (n / p) hlt
      rw [mul_comm p f] at h2
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      rw [hrec, pow_succ]
      have hp0 : (0 : ℝ) < p := by linarith
      rw [pow_succ] at h2
      have h2' : |coprimeHarmonicMoebius (f * p) (n / p)| / p ≤ 2 ^ s.card := by
        rw [div_le_iff₀ hp0]
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) s.card]
      calc |coprimeHarmonicMoebius f n + coprimeHarmonicMoebius (f * p) (n / p) / p|
          ≤ |coprimeHarmonicMoebius f n| + |coprimeHarmonicMoebius (f * p) (n / p) / p| :=
            abs_add_le _ _
        _ = |coprimeHarmonicMoebius f n| + |coprimeHarmonicMoebius (f * p) (n / p)| / p := by
            rw [abs_div, abs_of_pos hp0]
        _ ≤ 2 ^ s.card + 2 ^ s.card := add_le_add h1 h2'
        _ = 2 ^ s.card * 2 := by ring

/-- For squarefree `f`, `|m_f(n)| ≤ τ(f)`. -/
theorem abs_coprimeHarmonicMoebius_le_card_divisors {f : ℕ} (hf : Squarefree f) (n : ℕ) :
    |coprimeHarmonicMoebius f n| ≤ (f.divisors.card : ℝ) := by
  have h := abs_coprimeHarmonicMoebius_prod_le f.primeFactors
    (fun p hp => Nat.prime_of_mem_primeFactors hp) n
  rw [Nat.prod_primeFactors_of_squarefree hf] at h
  refine h.trans ?_
  have hcard : f.divisors.card = 2 ^ f.primeFactors.card := by
    rw [Nat.card_divisors hf.ne_zero]
    rw [show (∏ p ∈ f.primeFactors, (f.factorization p + 1)) = ∏ _p ∈ f.primeFactors, 2 from
      prod_congr rfl fun p hp => by
        have h1 := (Nat.squarefree_iff_factorization_le_one hf.ne_zero).mp hf p
        have h2 : f.factorization p ≠ 0 := by
          rw [← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
        omega]
    simp
  rw [hcard]; push_cast; rfl

/-! ### The Selberg coordinates of the Möbius weight -/

private theorem sum_Icc_multiples' (f n : ℕ) (hf : 0 < f) (g : ℕ → ℝ) :
    (∑ d ∈ (Icc 1 n).filter (fun d => f ∣ d), g d) = ∑ e ∈ Icc 1 (n / f), g (f * e) := by
  have hset : (Icc 1 n).filter (fun d => f ∣ d) = (Icc 1 (n / f)).image (fun e => f * e) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le hf).mpr (by linarith [mul_comm f k])⟩, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · rintro ⟨e, ⟨h1, h2⟩, rfl⟩
      have := (Nat.le_div_iff_mul_le hf).mp h2
      exact ⟨⟨by nlinarith, by linarith [mul_comm f e]⟩, dvd_mul_right f e⟩
  rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hf h)]

/-- `Y_N(f) = μ(f)/f · m_f(N/f)` for the Möbius weight. -/
theorem selbergMultiplesCoord_moebiusReal (N : ℕ) {f : ℕ} (hf : 0 < f) :
    selbergMultiplesCoord N moebiusReal f =
      moebiusReal f / (f : ℝ) * coprimeHarmonicMoebius f (N / f) := by
  unfold selbergMultiplesCoord coprimeHarmonicMoebius
  rw [sum_Icc_multiples' f N hf, mul_sum]
  refine sum_congr rfl fun e he => ?_
  have he0 : (0 : ℝ) < e := by exact_mod_cast (mem_Icc.mp he).1
  have hf0 : (0 : ℝ) < f := by exact_mod_cast hf
  by_cases hsq : Squarefree f
  · by_cases hc : Nat.Coprime e f
    · rw [if_pos hc]
      unfold moebiusReal
      rw [isMultiplicative_moebius.map_mul_of_coprime hc.symm]
      push_cast; field_simp
    · rw [if_neg hc]
      have : moebiusReal (f * e) = 0 := by
        apply moebiusReal_eq_zero_of_not_squarefree
        rw [Nat.squarefree_mul_iff]; exact fun h => hc h.1.symm
      rw [this]; simp
  · have h1 : moebiusReal (f * e) = 0 :=
      moebiusReal_eq_zero_of_not_squarefree _ fun h => hsq h.of_mul_left
    have h2 : moebiusReal f = 0 := moebiusReal_eq_zero_of_not_squarefree _ hsq
    rw [h1, h2]; simp

/-- **Diagonal form.** `Q_Bez(N; μ) = Σ_{f ≤ N} μ(f)/f² · m_f(N/f)²`. -/
theorem bezoutCoprimeQuadraticForm_moebius_eq (N : ℕ) :
    bezoutCoprimeQuadraticForm N moebiusReal =
      ∑ f ∈ Icc 1 N, moebiusReal f / (f : ℝ) ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2 := by
  rw [bezoutCoprimeQuadraticForm_eq_moebius_diagonal]
  refine sum_congr rfl fun f hf => ?_
  have hf0 : 0 < f := (mem_Icc.mp hf).1
  rw [selbergMultiplesCoord_moebiusReal N hf0]
  have hμ3 : moebiusReal f * moebiusReal f ^ 2 = moebiusReal f := by
    unfold moebiusReal
    rcases eq_or_ne (μ f) 0 with h | h
    · simp [h]
    · have hsq : Squarefree f := by
        by_contra hs; exact h (moebius_eq_zero_of_not_squarefree hs)
      have h1 : |(μ f : ℝ)| = 1 := by exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
      rw [← sq_abs, h1]; ring
  have hfR : (0 : ℝ) < f := by exact_mod_cast hf0
  calc moebiusReal f * (moebiusReal f / (f : ℝ) * coprimeHarmonicMoebius f (N / f)) ^ 2
      = moebiusReal f * moebiusReal f ^ 2 / (f : ℝ) ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2 := by
        ring
    _ = _ := by rw [hμ3]

/-! ### Decorrelation -/

/-- **Bézout decorrelation of the Möbius observer.** `Q_Bez(N; μ) → 0` as `N → ∞`. -/
theorem tendsto_bezoutCoprimeQuadraticForm_moebius :
    Tendsto (fun N : ℕ => bezoutCoprimeQuadraticForm N moebiusReal) atTop (𝓝 0) := by
  obtain ⟨C, hC, hτ⟩ := RHTower.card_divisors_le_const_mul_rpow (show (0 : ℝ) < 1 / 4 by norm_num)
  set F : ℕ → ℕ → ℝ := fun N f =>
    moebiusReal f / (f : ℝ) ^ 2 * coprimeHarmonicMoebius f (N / f) ^ 2
  -- the finite form is the full series
  have hfin (N : ℕ) : bezoutCoprimeQuadraticForm N moebiusReal = ∑' f, F N f := by
    rw [bezoutCoprimeQuadraticForm_moebius_eq, tsum_eq_sum (s := Icc 1 N)]
    intro f hf
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp [F, moebiusReal]
    · have hNf : N < f := by simp only [mem_Icc, not_and, not_le] at hf; exact hf hf0
      simp [F, Nat.div_eq_of_lt hNf, coprimeHarmonicMoebius]
  simp_rw [hfin]
  have hzero : (∑' _f : ℕ, (0 : ℝ)) = 0 := tsum_zero
  rw [← hzero]
  refine tendsto_tsum_of_dominated_convergence (bound := fun f => C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ)))
    ?_ ?_ ?_
  · exact (Real.summable_nat_rpow.mpr (by norm_num)).mul_left _
  · -- each term tends to zero
    intro f
    by_cases hsq : Squarefree f
    · have hf0 : f ≠ 0 := hsq.ne_zero
      have hm := tendsto_coprimeHarmonicMoebius_prod f.primeFactors
        (fun p hp => Nat.prime_of_mem_primeFactors hp)
      rw [Nat.prod_primeFactors_of_squarefree hsq] at hm
      have hm' := (hm.comp (Nat.tendsto_div_const_atTop hf0)).pow 2
      have := hm'.const_mul (moebiusReal f / (f : ℝ) ^ 2)
      simpa [F] using this
    · have : ∀ N, F N f = 0 := fun N => by
        simp [F, moebiusReal_eq_zero_of_not_squarefree _ hsq]
      simp [this]
  · -- domination by `C² f^{-3/2}`
    filter_upwards with N f
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · simp [F, moebiusReal]
    by_cases hsq : Squarefree f
    · have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf0
      have hm := abs_coprimeHarmonicMoebius_le_card_divisors hsq (N / f)
      have hd := hτ f hf0
      have hμ : |moebiusReal f| ≤ 1 := by
        unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      have hm2 : coprimeHarmonicMoebius f (N / f) ^ 2 ≤ (C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hm.trans hd) 2
      have hpow : (C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (f : ℝ) ^ 2 = C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ)) := by
        have hf : (0 : ℝ) < f := by linarith
        rw [mul_pow, ← Real.rpow_natCast ((f : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hf.le,
          ← Real.rpow_natCast (f : ℝ) 2, mul_div_assoc, ← Real.rpow_sub hf]
        norm_num
      rw [Real.norm_eq_abs]
      calc |F N f| = |moebiusReal f| * (coprimeHarmonicMoebius f (N / f) ^ 2 / (f : ℝ) ^ 2) := by
            simp only [F]; rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (coprimeHarmonicMoebius f (N / f))),
              abs_of_nonneg (by positivity : (0 : ℝ) ≤ (f : ℝ) ^ 2)]; ring
        _ ≤ 1 * ((C * (f : ℝ) ^ (1 / 4 : ℝ)) ^ 2 / (f : ℝ) ^ 2) := by
            apply mul_le_mul hμ _ (by positivity) zero_le_one
            exact div_le_div_of_nonneg_right hm2 (by positivity)
        _ = C ^ 2 * (f : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [one_mul, hpow]
    · simp only [F, moebiusReal_eq_zero_of_not_squarefree _ hsq, zero_div, zero_mul, norm_zero]
      positivity

/-- **Dissipation equals mean square asymptotically.** `R_N(μ) - Q_Sel(N; μ) → 0`. -/
theorem tendsto_sieveSuccessorReserve_sub_selberg_moebius :
    Tendsto (fun N : ℕ => sieveSuccessorReserve N moebiusReal -
      selbergTotientDiagonalForm N moebiusReal) atTop (𝓝 0) := by
  have h := tendsto_bezoutCoprimeQuadraticForm_moebius.neg
  rw [neg_zero] at h
  refine h.congr fun N => ?_
  unfold sieveSuccessorReserve
  ring

/-- **Period decorrelation.** For every `η > 0`, eventually in the horizon, every full period of
the Möbius response has unit-shift correlation at most `η L` in absolute value. -/
theorem eventually_abs_period_correlation_moebius_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, (∀ d ∈ Icc 1 N, d ∣ L) → ∀ M : ℕ,
      |∑ k ∈ Icc (M + 1) (M + L), sieveSeq N moebiusReal k * sieveSeq N moebiusReal (k + 1)| ≤
        η * L := by
  filter_upwards [tendsto_bezoutCoprimeQuadraticForm_moebius.eventually
    (Metric.closedBall_mem_nhds (0 : ℝ) hη)] with N hN L hL M
  rw [sum_sieveSeq_mul_succ_sliding_period_eq hL, abs_mul, Nat.abs_cast]
  simp only [Real.dist_eq, sub_zero] at hN
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg L)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
