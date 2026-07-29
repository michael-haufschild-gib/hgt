import GaloisForLFunctions.HTGeometry.UnitCircleRootRadialOrientation

/-!
# Multiplicative orientation of complete centered divisor packets

The centered divisor phase of a positive integer is the full finite translate packet

`exp (-i log(k) z / 2) * sum_(d|k) exp (i log(d) z)`.

Its arithmetic function is multiplicative.  Prime-power fibres are the centered geometric
packets from `UnitCircleRootRadialOrientation`; hence unique factorization writes every full
divisor packet as a finite product of strictly upper-oriented prime-power packets.  The exact
finite-product current identity then proves strict negative upper current for every `k > 1`.

This theorem is source-arithmetic and finite.  It uses no Xi divisor data or limiting measure.
-/

open Complex Finset
open scoped ArithmeticFunction.zeta


namespace GaloisForLFunctions.HTGeometry

noncomputable section

def positiveNatExponentialPhase (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      Complex.exp (I * (Real.log n : ℂ) * z), by simp⟩

theorem isMultiplicative_positiveNatExponentialPhase (z : ℂ) :
    (positiveNatExponentialPhase z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [positiveNatExponentialPhase]
  · intro m n hm hn _hcop
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hlog : Real.log (((m * n : ℕ) : ℝ)) =
        Real.log (m : ℝ) + Real.log (n : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    simp only [positiveNatExponentialPhase, ArithmeticFunction.coe_mk,
      if_neg hm, if_neg hn, if_neg hmn]
    rw [← Complex.exp_add]
    congr 1
    rw [hlog]
    push_cast
    ring

def divisorExponentialPhase (z : ℂ) : ArithmeticFunction ℂ :=
  (↑ζ : ArithmeticFunction ℂ) * positiveNatExponentialPhase z

theorem isMultiplicative_divisorExponentialPhase (z : ℂ) :
    (divisorExponentialPhase z).IsMultiplicative := by
  exact ArithmeticFunction.isMultiplicative_zeta.natCast.mul
    (isMultiplicative_positiveNatExponentialPhase z)

def centeredDivisorPhaseAF (z : ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else
      Complex.exp (-I * ((Real.log n / 2 : ℝ) : ℂ) * z) *
        divisorExponentialPhase z n, by simp⟩

theorem isMultiplicative_centeredDivisorPhaseAF (z : ℂ) :
    (centeredDivisorPhaseAF z).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [centeredDivisorPhaseAF, divisorExponentialPhase,
      positiveNatExponentialPhase]
  · intro m n hm hn hcop
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hdiv := (isMultiplicative_divisorExponentialPhase z).map_mul_of_coprime hcop
    have hlog : Real.log (((m * n : ℕ) : ℝ)) =
        Real.log (m : ℝ) + Real.log (n : ℝ) := by
      rw [Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    have hcenter :
        Complex.exp (-I * ((Real.log (((m * n : ℕ) : ℝ)) / 2 : ℝ) : ℂ) * z) =
          Complex.exp (-I * ((Real.log (m : ℝ) / 2 : ℝ) : ℂ) * z) *
            Complex.exp (-I * ((Real.log (n : ℝ) / 2 : ℝ) : ℂ) * z) := by
      rw [← Complex.exp_add]
      congr 1
      rw [hlog]
      push_cast
      ring
    simp only [centeredDivisorPhaseAF, ArithmeticFunction.coe_mk,
      if_neg hm, if_neg hn, if_neg hmn]
    rw [hdiv, hcenter]
    ring

theorem centeredDivisorPhaseAF_prime_pow
    {p : ℕ} (hp : p.Prime) (a : ℕ) (z : ℂ) :
    centeredDivisorPhaseAF z (p ^ a) =
      primePowerCenteredDivisorPhase p a z := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp0
  have hloga : Real.log (((p ^ a : ℕ) : ℝ)) =
      (a : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  simp only [centeredDivisorPhaseAF, ArithmeticFunction.coe_mk, if_neg hpa0,
    divisorExponentialPhase, ArithmeticFunction.coe_zeta_mul_apply,
    Nat.sum_divisors_prime_pow hp, Finset.mul_sum]
  unfold primePowerCenteredDivisorPhase centeredGeometricExponentialPacket
  apply Finset.sum_congr rfl
  intro j _hj
  have hpj0 : p ^ j ≠ 0 := pow_ne_zero _ hp0
  have hlogj : Real.log (((p ^ j : ℕ) : ℝ)) =
      (j : ℝ) * Real.log (p : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
  simp only [positiveNatExponentialPhase, ArithmeticFunction.coe_mk, if_neg hpj0]
  rw [← Complex.exp_add]
  congr 1
  rw [hloga, hlogj]
  push_cast
  ring

def factorizedCenteredDivisorPhase (k : ℕ) (z : ℂ) : ℂ :=
  ∏ p ∈ k.primeFactors,
    primePowerCenteredDivisorPhase p (k.factorization p) z

theorem centeredDivisorPhaseAF_eq_factorized
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    centeredDivisorPhaseAF z k = factorizedCenteredDivisorPhase k z := by
  rw [(isMultiplicative_centeredDivisorPhaseAF z).multiplicative_factorization
    (centeredDivisorPhaseAF z) hk]
  unfold factorizedCenteredDivisorPhase
  apply Finset.prod_congr rfl
  intro p hp
  exact centeredDivisorPhaseAF_prime_pow
    (Nat.prime_of_mem_primeFactors hp) (k.factorization p) z

theorem centeredDivisorPhaseAF_eq_divisor_sum
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    centeredDivisorPhaseAF z k =
      Complex.exp (-I * ((Real.log k / 2 : ℝ) : ℂ) * z) *
        ∑ d ∈ k.divisors,
          Complex.exp (I * (Real.log d : ℂ) * z) := by
  simp only [centeredDivisorPhaseAF, ArithmeticFunction.coe_mk, if_neg hk,
    divisorExponentialPhase, ArithmeticFunction.coe_zeta_mul_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [positiveNatExponentialPhase, hd0]

theorem orientedPhaseCurrent_mul_identity
    (F F' G G' : ℂ) :
    (((F' * G + F * G') * (starRingEnd ℂ) (F * G)).im) =
      Complex.normSq G * (F' * (starRingEnd ℂ) F).im +
        Complex.normSq F * (G' * (starRingEnd ℂ) G).im := by
  rw [map_mul]
  rw [show
      (F' * G + F * G') *
          ((starRingEnd ℂ) F * (starRingEnd ℂ) G) =
        (G * (starRingEnd ℂ) G) *
            (F' * (starRingEnd ℂ) F) +
          (F * (starRingEnd ℂ) F) *
            (G' * (starRingEnd ℂ) G) by ring]
  rw [mul_conj, mul_conj]
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero]

theorem orientedPhaseCurrent_finsetProduct_identity
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (F F' : ι → ℂ) :
    (((∑ i ∈ s, (∏ j ∈ s.erase i, F j) * F' i) *
        (starRingEnd ℂ) (∏ i ∈ s, F i)).im) =
      ∑ i ∈ s,
        Complex.normSq (∏ j ∈ s.erase i, F j) *
          (F' i * (starRingEnd ℂ) (F i)).im := by
  rw [Finset.sum_mul, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hprod : F i * ∏ j ∈ s.erase i, F j = ∏ j ∈ s, F j :=
    Finset.mul_prod_erase s F hi
  rw [← hprod, map_mul]
  rw [show
      ((∏ j ∈ s.erase i, F j) * F' i) *
          ((starRingEnd ℂ) (F i) *
            (starRingEnd ℂ) (∏ j ∈ s.erase i, F j)) =
        ((∏ j ∈ s.erase i, F j) *
          (starRingEnd ℂ) (∏ j ∈ s.erase i, F j)) *
            (F' i * (starRingEnd ℂ) (F i)) by ring]
  rw [mul_conj]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero]

theorem orientedPhaseCurrent_finsetProduct_lt_zero
    {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty)
    (F F' : ι → ℂ)
    (hcurrent : ∀ i ∈ s,
      (F' i * (starRingEnd ℂ) (F i)).im < 0) :
    (((∑ i ∈ s, (∏ j ∈ s.erase i, F j) * F' i) *
        (starRingEnd ℂ) (∏ i ∈ s, F i)).im) < 0 := by
  rw [orientedPhaseCurrent_finsetProduct_identity]
  have hvalue : ∀ i ∈ s, F i ≠ 0 := by
    intro i hi hzero
    have h := hcurrent i hi
    simp [hzero] at h
  have hterm : ∀ i ∈ s,
      Complex.normSq (∏ j ∈ s.erase i, F j) *
          (F' i * (starRingEnd ℂ) (F i)).im < 0 := by
    intro i hi
    have hprod : ∏ j ∈ s.erase i, F j ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j hj =>
        hvalue j (Finset.mem_of_mem_erase hj)
    exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hprod)
      (hcurrent i hi)
  apply Finset.sum_neg'
  · intro i hi
    exact (hterm i hi).le
  · rcases hs with ⟨i, hi⟩
    exact ⟨i, hi, hterm i hi⟩

def factorizedCenteredDivisorPhaseDerivative (k : ℕ) (z : ℂ) : ℂ :=
  ∑ p ∈ k.primeFactors,
    (∏ q ∈ k.primeFactors.erase p,
      primePowerCenteredDivisorPhase q (k.factorization q) z) *
        primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z

theorem hasDerivAt_factorizedCenteredDivisorPhase
    (k : ℕ) (z : ℂ) :
    HasDerivAt (factorizedCenteredDivisorPhase k)
      (factorizedCenteredDivisorPhaseDerivative k z) z := by
  have h := HasDerivAt.fun_finsetProd
    (u := k.primeFactors)
    (f := fun p u =>
      primePowerCenteredDivisorPhase p (k.factorization p) u)
    (f' := fun p =>
      primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z)
    (fun p _hp => by
      exact hasDerivAt_centeredGeometricExponentialPacket
        (k.factorization p + 1) (Real.log p) z)
  simpa only [factorizedCenteredDivisorPhase,
    factorizedCenteredDivisorPhaseDerivative, Finset.smul_sum,
    smul_eq_mul, mul_comm] using! h

/-- Exact arithmetic polarization of the complete divisor-packet current into its prime-power
currents.  Every coefficient is the norm square of the complementary Euler packet. -/
theorem factorizedCenteredDivisorPhase_current_eq_sum_primeFactors
    (k : ℕ) (z : ℂ) :
    (factorizedCenteredDivisorPhaseDerivative k z *
      (starRingEnd ℂ) (factorizedCenteredDivisorPhase k z)).im =
      ∑ p ∈ k.primeFactors,
        Complex.normSq
            (∏ q ∈ k.primeFactors.erase p,
              primePowerCenteredDivisorPhase q (k.factorization q) z) *
          (primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z *
            (starRingEnd ℂ)
              (primePowerCenteredDivisorPhase p (k.factorization p) z)).im := by
  exact orientedPhaseCurrent_finsetProduct_identity k.primeFactors
    (fun p => primePowerCenteredDivisorPhase p (k.factorization p) z)
    (fun p => primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z)

theorem factorizedCenteredDivisorPhase_current_lt_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    (factorizedCenteredDivisorPhaseDerivative k z *
      (starRingEnd ℂ) (factorizedCenteredDivisorPhase k z)).im < 0 := by
  apply orientedPhaseCurrent_finsetProduct_lt_zero
    ((Nat.nonempty_primeFactors).2 hk)
  intro p hp
  have hpmem := (Nat.mem_primeFactors.mp hp)
  have hpprime : p.Prime := hpmem.1
  have hk0 : k ≠ 0 := by omega
  have ha : 0 < k.factorization p :=
    hpprime.factorization_pos_of_dvd hk0 hpmem.2.1
  exact primePowerCenteredDivisorPhase_current_lt_zero
    hpprime.one_lt ha hz

/-- The centered phase of the complete divisor packet of `k`. -/
def centeredDivisorPhase (k : ℕ) (z : ℂ) : ℂ :=
  centeredDivisorPhaseAF z k

/-- Spectral derivative of the complete centered divisor packet. -/
def centeredDivisorPhaseDerivative (k : ℕ) (z : ℂ) : ℂ :=
  deriv (centeredDivisorPhase k) z

theorem centeredDivisorPhase_eq_factorized
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    centeredDivisorPhase k z = factorizedCenteredDivisorPhase k z :=
  centeredDivisorPhaseAF_eq_factorized hk z

theorem hasDerivAt_centeredDivisorPhase
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    HasDerivAt (centeredDivisorPhase k)
      (factorizedCenteredDivisorPhaseDerivative k z) z := by
  have hfun : centeredDivisorPhase k = factorizedCenteredDivisorPhase k := by
    funext u
    exact centeredDivisorPhase_eq_factorized hk u
  rw [hfun]
  exact hasDerivAt_factorizedCenteredDivisorPhase k z

theorem centeredDivisorPhaseDerivative_eq_factorized
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    centeredDivisorPhaseDerivative k z =
      factorizedCenteredDivisorPhaseDerivative k z := by
  unfold centeredDivisorPhaseDerivative
  exact (hasDerivAt_centeredDivisorPhase hk z).deriv

/-- Exact prime-factor polarization of the arithmetic divisor phase itself. -/
theorem centeredDivisorPhase_current_eq_sum_primeFactors
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    (centeredDivisorPhaseDerivative k z *
      (starRingEnd ℂ) (centeredDivisorPhase k z)).im =
      ∑ p ∈ k.primeFactors,
        Complex.normSq
            (∏ q ∈ k.primeFactors.erase p,
              primePowerCenteredDivisorPhase q (k.factorization q) z) *
          (primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z *
            (starRingEnd ℂ)
              (primePowerCenteredDivisorPhase p (k.factorization p) z)).im := by
  rw [centeredDivisorPhaseDerivative_eq_factorized hk,
    centeredDivisorPhase_eq_factorized hk]
  exact factorizedCenteredDivisorPhase_current_eq_sum_primeFactors k z

/-- Every nontrivial full divisor packet has strict negative upper oriented current. -/
theorem centeredDivisorPhase_current_lt_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    (centeredDivisorPhaseDerivative k z *
      (starRingEnd ℂ) (centeredDivisorPhase k z)).im < 0 := by
  rw [centeredDivisorPhaseDerivative_eq_factorized (by omega),
    centeredDivisorPhase_eq_factorized (by omega)]
  exact factorizedCenteredDivisorPhase_current_lt_zero hk hz

end

end GaloisForLFunctions.HTGeometry
