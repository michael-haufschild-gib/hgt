import GaloisForLFunctions.RHTower.PrimeLogJumpPacket
import GaloisForLFunctions.RHTower.Sieve.RouteERamareIntegerIncidence

/-!
# Route E: two-prime aperture sign no-go

For primes `p < q < 2p`, the literal Ramaré active set with designated primes `{p,q}` and
cutoff `q` collapses to `{p,q}`.  The physical off-diagonal is therefore one explicit sine mode:

`2 sin (2π W (log q - log p)) / (π (log q - log p))`.

It is positive at its quarter period and negative at its three-quarter period, with exact
linear-in-window magnitude.  Thus the nested-aperture residual has no source-faithful universal
sign, monotonicity, or sublinear-window damping law.  Any surviving Route E argument must exploit
collective many-prime cancellation or nonlocal coupling rather than a sign telescope.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

private theorem eq_of_dvd_of_mem_Icc_of_lt_two_mul
    {N p n : ℕ} (hn : n ∈ Finset.Icc 1 N) (hN : N < 2 * p) (hdvd : p ∣ n) : n = p := by
  obtain ⟨k, rfl⟩ := hdvd
  rw [Finset.mem_Icc] at hn
  obtain ⟨h1, h2⟩ := hn
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk] at h1
    · exact hk
  have hk2 : k < 2 := by
    by_contra hc
    rw [not_lt] at hc
    have htwo : 2 * p ≤ p * k := by
      calc
        2 * p = p * 2 := by ring
        _ ≤ p * k := Nat.mul_le_mul_left p hc
    omega
  have hk : k = 1 := by omega
  rw [hk, mul_one]

/-- Below the first doubled prime, the literal two-prime Ramaré aperture has no composite
activations. -/
theorem ramareActiveSet_pair_eq_pair_of_lt_two_mul
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p) :
    ramareActiveSet {p, q} q = {p, q} := by
  ext n
  constructor
  · intro hn
    have hnI : n ∈ Finset.Icc 1 q := (Finset.mem_filter.mp hn).1
    rcases (Finset.mem_filter.mp hn).2 with ⟨r, hr⟩
    have hr' := mem_primeFactorsIn.mp hr
    have hrpq : r = p ∨ r = q := by simpa using hr'.1
    rcases hrpq with rfl | rfl
    · exact Finset.mem_insert.mpr <| Or.inl
        (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI hq2p hr'.2)
    · exact Finset.mem_insert.mpr <| Or.inr <| Finset.mem_singleton.mpr
        (eq_of_dvd_of_mem_Icc_of_lt_two_mul hnI (by omega) hr'.2)
  · intro hn
    rw [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hnp | hnq
    · subst n
      rw [ramareActiveSet, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨hp.one_le, hpq.le⟩, ⟨p, ?_⟩⟩
      exact mem_primeFactorsIn.mpr ⟨by simp, dvd_rfl⟩
    · subst n
      rw [ramareActiveSet, Finset.mem_filter]
      refine ⟨Finset.mem_Icc.mpr ⟨hq.one_le, le_rfl⟩, ⟨q, ?_⟩⟩
      exact mem_primeFactorsIn.mpr ⟨by simp, dvd_rfl⟩

/-- A physical logarithmic phase pair is the cosine of its log-frequency gap. -/
theorem unitLogPhase_mul_conj_re_eq_cos_logGap (w : ℝ) (n m : ℕ) :
    (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re =
      Real.cos ((2 * Real.pi * (Real.log n - Real.log m)) * w) := by
  rw [unitLogPhase, unitLogPhase, ← Complex.exp_conj, ← Complex.exp_add]
  have hexp :
      ((((2 * Real.pi * (w * Real.log n) : ℝ) : ℂ) * Complex.I) +
          (starRingEnd ℂ)
            (((2 * Real.pi * (w * Real.log m) : ℝ) : ℂ) * Complex.I)) =
        (((2 * Real.pi * (Real.log n - Real.log m) * w : ℝ) : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hexp, Complex.exp_ofReal_mul_I_re]

/-- Exact distinct-frequency Mellin pair kernel. -/
theorem ramareMellinPairKernel_eq_sin_logGap
    {W : ℝ} (hW : 0 ≤ W) {n m : ℕ} (hlog : Real.log n ≠ Real.log m) :
    ramareMellinPairKernel W n m =
      Real.sin (2 * Real.pi * W * (Real.log n - Real.log m)) /
        (Real.pi * (Real.log n - Real.log m)) := by
  have hδ : Real.log n - Real.log m ≠ 0 := sub_ne_zero.mpr hlog
  have hκ : 2 * Real.pi * (Real.log n - Real.log m) ≠ 0 := by
    positivity
  rw [ramareMellinPairKernel]
  have hfun : (fun w : ℝ =>
      (unitLogPhase w n * (starRingEnd ℂ) (unitLogPhase w m)).re) =
      fun w : ℝ => Real.cos ((2 * Real.pi * (Real.log n - Real.log m)) * w) := by
    funext w
    exact unitLogPhase_mul_conj_re_eq_cos_logGap w n m
  rw [hfun, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -W ≤ W),
    GaloisForLFunctions.RHTower.intervalIntegral_cos_mul hκ]
  rw [show 2 * Real.pi * (Real.log n - Real.log m) * -W =
      -(2 * Real.pi * (Real.log n - Real.log m) * W) by ring,
    Real.sin_neg]
  field_simp
  ring

/-- Exact source-faithful off-diagonal law on the smallest nontrivial prime aperture. -/
theorem ramarePrimeOffDiagonal_pair_eq_sin_logGap
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p)
    {W : ℝ} (hW : 0 ≤ W) :
    ramarePrimeOffDiagonal {p, q} q W =
      2 * Real.sin (2 * Real.pi * W * (Real.log q - Real.log p)) /
        (Real.pi * (Real.log q - Real.log p)) := by
  have hpairprime : ∀ r ∈ ({p, q} : Finset ℕ), r.Prime := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp
    · exact hq
  have hqndvd : ¬ q ∣ p := Nat.not_dvd_of_pos_of_lt hp.pos hpq
  have hpndvd : ¬ p ∣ q := by
    intro hdvd
    rcases (Nat.dvd_prime hq).mp hdvd with hp1 | hpq'
    · exact hp.ne_one hp1
    · exact hpq.ne hpq'
  have hFp : primeFactorsIn {p, q} p = {p} := by
    ext r
    simp only [mem_primeFactorsIn, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hrp | hrq, hdiv⟩
      · exact hrp
      · subst r
        exact (hqndvd hdiv).elim
    · intro hr
      subst r
      exact ⟨Or.inl rfl, dvd_rfl⟩
  have hFq : primeFactorsIn {p, q} q = {q} := by
    ext r
    simp only [mem_primeFactorsIn, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hrp | hrq, hdiv⟩
      · subst r
        exact (hpndvd hdiv).elim
      · exact hrq
    · intro hr
      subst r
      exact ⟨Or.inr rfl, dvd_rfl⟩
  have hCpp : ramareIncidenceComplement {p, q} p p = 0 := by
    rw [ramareIncidenceComplement, hFp]
    simp
  have hCqq : ramareIncidenceComplement {p, q} q q = 0 := by
    rw [ramareIncidenceComplement, hFq]
    simp
  have hCpq : ramareIncidenceComplement {p, q} p q = 1 := by
    rw [ramareIncidenceComplement, hFp, hFq]
    simp [hpq.ne]
  have hCqp : ramareIncidenceComplement {p, q} q p = 1 := by
    rw [ramareIncidenceComplement, hFp, hFq]
    simp [hpq.ne]
  rw [ramarePrimeOffDiagonal_eq_integerIncidence hpairprime,
    ramareActiveSet_pair_eq_pair_of_lt_two_mul hp hq hpq hq2p]
  have hlog : Real.log q ≠ Real.log p := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ne_of_gt (Real.strictMonoOn_log hppos hqpos (by exact_mod_cast hpq))
  have hKqp := ramareMellinPairKernel_eq_sin_logGap hW hlog
  have hKpq := ramareMellinPairKernel_eq_sin_logGap hW hlog.symm
  simp [hpq.ne, hCpp, hCqq, hCpq, hCqp,
    ArithmeticFunction.moebius_apply_prime hp,
    ArithmeticFunction.moebius_apply_prime hq]
  rw [hKqp, hKpq]
  rw [show Real.log p - Real.log q = -(Real.log q - Real.log p) by ring,
    show 2 * Real.pi * W * -(Real.log q - Real.log p) =
      -(2 * Real.pi * W * (Real.log q - Real.log p)) by ring,
    Real.sin_neg]
  field_simp
  ring

/-- At the quarter period, the physical off-diagonal has exact positive linear scale. -/
theorem ramarePrimeOffDiagonal_pair_quarterPeriod
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p) :
    ramarePrimeOffDiagonal {p, q} q
        (1 / (4 * (Real.log q - Real.log p))) =
      2 / (Real.pi * (Real.log q - Real.log p)) := by
  have hlog : Real.log p < Real.log q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Real.strictMonoOn_log hppos hqpos (by exact_mod_cast hpq)
  have hdelta : Real.log q - Real.log p ≠ 0 := sub_ne_zero.mpr hlog.ne'
  rw [ramarePrimeOffDiagonal_pair_eq_sin_logGap hp hq hpq hq2p (by positivity)]
  have harg :
      2 * Real.pi * (1 / (4 * (Real.log q - Real.log p))) *
          (Real.log q - Real.log p) = Real.pi / 2 := by
    field_simp
    ring
  rw [harg, Real.sin_pi_div_two]
  ring

/-- At the three-quarter period, the same physical off-diagonal has exact negative linear scale. -/
theorem ramarePrimeOffDiagonal_pair_threeQuarterPeriod
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p) :
    ramarePrimeOffDiagonal {p, q} q
        (3 / (4 * (Real.log q - Real.log p))) =
      -2 / (Real.pi * (Real.log q - Real.log p)) := by
  have hlog : Real.log p < Real.log q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Real.strictMonoOn_log hppos hqpos (by exact_mod_cast hpq)
  have hdelta : Real.log q - Real.log p ≠ 0 := sub_ne_zero.mpr hlog.ne'
  rw [ramarePrimeOffDiagonal_pair_eq_sin_logGap hp hq hpq hq2p (by positivity)]
  have harg :
      2 * Real.pi * (3 / (4 * (Real.log q - Real.log p))) *
          (Real.log q - Real.log p) = Real.pi / 2 + Real.pi := by
    field_simp
    ring
  rw [harg, Real.sin_add_pi, Real.sin_pi_div_two]
  ring

/-- The literal two-prime aperture is positive at its quarter-period window. -/
theorem ramarePrimeOffDiagonal_pair_quarterPeriod_pos
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p) :
    0 < ramarePrimeOffDiagonal {p, q} q
      (1 / (4 * (Real.log q - Real.log p))) := by
  rw [ramarePrimeOffDiagonal_pair_quarterPeriod hp hq hpq hq2p]
  have hlog : Real.log p < Real.log q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Real.strictMonoOn_log hppos hqpos (by exact_mod_cast hpq)
  positivity

/-- The same literal two-prime aperture is negative at its three-quarter-period window. -/
theorem ramarePrimeOffDiagonal_pair_threeQuarterPeriod_neg
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hq2p : q < 2 * p) :
    ramarePrimeOffDiagonal {p, q} q
      (3 / (4 * (Real.log q - Real.log p))) < 0 := by
  rw [ramarePrimeOffDiagonal_pair_threeQuarterPeriod hp hq hpq hq2p]
  have hlog : Real.log p < Real.log q := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact Real.strictMonoOn_log hppos hqpos (by exact_mod_cast hpq)
  exact div_neg_of_neg_of_pos (by norm_num)
    (mul_pos Real.pi_pos (sub_pos.mpr hlog))

end RHTower.Sieve
