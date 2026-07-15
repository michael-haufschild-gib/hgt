import GaloisForLFunctions.RHTower.SoninSemilocalAllEvenJacobiResidue

/-!
# Exact one-prime Poisson expansion for the semilocal Sonin source

This module proves the absolutely convergent bilateral Poisson expansion of one inverse Euler
factor.  It supplies the exact analytic bridge between the integer-lattice coefficients used by
the all-even residue tower and the norm-square local factor appearing in the paper statement.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

/-- The bilateral Poisson Fourier term with radius `r`, unit phase `z`, and frequency `m`. -/
def semilocalBilateralPoissonTerm (r : ℝ) (z : ℂ) (m : ℤ) : ℂ :=
  (r : ℂ) ^ m.natAbs * z ^ m

/-- The bilateral Poisson Fourier series is absolutely summable for every radius in `[0,1)`. -/
theorem summable_semilocalBilateralPoissonTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Summable fun m : ℤ => semilocalBilateralPoissonTerm r z m := by
  have hmajor := summable_int_pow_natAbs hr0 hr1
  refine hmajor.of_norm_bounded ?_
  intro m
  simp [semilocalBilateralPoissonTerm, norm_pow, norm_zpow, hz,
    abs_of_nonneg hr0]

/-- Absolute summability, explicitly expressed as summability of the term norms. -/
theorem summable_norm_semilocalBilateralPoissonTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    Summable fun m : ℤ => ‖semilocalBilateralPoissonTerm r z m‖ := by
  simpa [semilocalBilateralPoissonTerm, norm_pow, norm_zpow, hz,
    abs_of_nonneg hr0] using summable_int_pow_natAbs hr0 hr1

/-- Splitting the bilateral series into its nonnegative and negative geometric tails. -/
theorem tsum_semilocalBilateralPoissonTerm
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ∑' m : ℤ, semilocalBilateralPoissonTerm r z m =
      (1 - (r : ℂ) * z)⁻¹ +
        ((r : ℂ) * z⁻¹) * (1 - (r : ℂ) * z⁻¹)⁻¹ := by
  have hposNorm : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, hz, mul_one]
    exact hr1
  have hnegNorm : ‖(r : ℂ) * z⁻¹‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, norm_inv, hz, inv_one, mul_one]
    exact hr1
  have hposTerm (n : ℕ) :
      semilocalBilateralPoissonTerm r z n = ((r : ℂ) * z) ^ n := by
    simp [semilocalBilateralPoissonTerm, mul_pow]
  have hnegTerm (n : ℕ) :
      semilocalBilateralPoissonTerm r z (-(n + 1)) =
        ((r : ℂ) * z⁻¹) ^ (n + 1) := by
    unfold semilocalBilateralPoissonTerm
    rw [Int.natAbs_neg]
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by simp]
    rw [Int.natAbs_natCast, zpow_neg]
    rw [mul_pow, inv_pow]
    congr 2
  have hpos : Summable fun n : ℕ => semilocalBilateralPoissonTerm r z n := by
    simpa only [hposTerm] using
      summable_geometric_of_norm_lt_one hposNorm
  have hneg : Summable fun n : ℕ =>
      semilocalBilateralPoissonTerm r z (-(n + 1)) := by
    have hgeom := summable_geometric_of_norm_lt_one hnegNorm
    have hshift : Summable fun n : ℕ => ((r : ℂ) * z⁻¹) ^ (n + 1) := by
      apply (hgeom.mul_left ((r : ℂ) * z⁻¹)).congr
      intro n
      rw [pow_succ']
    simpa only [hnegTerm] using hshift
  rw [tsum_of_nat_of_neg_add_one hpos hneg]
  congr 1
  · simpa [semilocalBilateralPoissonTerm, mul_pow] using
      tsum_geometric_of_norm_lt_one hposNorm
  · rw [tsum_congr hnegTerm]
    rw [show (∑' n : ℕ, ((r : ℂ) * z⁻¹) ^ (n + 1)) =
        ((r : ℂ) * z⁻¹) * ∑' n : ℕ, ((r : ℂ) * z⁻¹) ^ n by
      calc
        (∑' n : ℕ, ((r : ℂ) * z⁻¹) ^ (n + 1)) =
            ∑' n : ℕ, ((r : ℂ) * z⁻¹) * ((r : ℂ) * z⁻¹) ^ n := by
          apply tsum_congr
          intro n
          rw [pow_succ']
        _ = ((r : ℂ) * z⁻¹) * ∑' n : ℕ, ((r : ℂ) * z⁻¹) ^ n :=
          tsum_mul_left]
    rw [tsum_geometric_of_norm_lt_one hnegNorm]

/-- The bilateral series is the classical Poisson kernel in algebraic unit-circle form. -/
theorem tsum_semilocalBilateralPoissonTerm_eq_kernel
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ∑' m : ℤ, semilocalBilateralPoissonTerm r z m =
      (1 - (r : ℂ) ^ 2) /
        ((1 - (r : ℂ) * z) * (1 - (r : ℂ) * z⁻¹)) := by
  rw [tsum_semilocalBilateralPoissonTerm hr0 hr1 hz]
  generalize hw : z⁻¹ = w
  have hz0 : z ≠ 0 := by
    intro hzero
    simp [hzero] at hz
  have hzw : z * w = 1 := by
    rw [← hw]
    exact Complex.mul_inv_cancel hz0
  have hwz : w * z = 1 := by
    rw [mul_comm]
    exact hzw
  have hwNorm : ‖w‖ = 1 := by
    rw [← hw, norm_inv, hz, inv_one]
  have hposNorm : ‖(r : ℂ) * z‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, hz, mul_one]
    exact hr1
  have hnegNorm : ‖(r : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, hwNorm, mul_one]
    exact hr1
  have hposNe : 1 - (r : ℂ) * z ≠ 0 := by
    intro hzero
    have hone : (r : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
    rw [hone] at hposNorm
    simp at hposNorm
  have hnegNe : 1 - (r : ℂ) * w ≠ 0 := by
    intro hzero
    have hone : (r : ℂ) * w = 1 := (sub_eq_zero.mp hzero).symm
    rw [hone] at hnegNorm
    simp at hnegNorm
  field_simp [hposNe, hnegNe]
  ring_nf
  rw [show (r : ℂ) ^ 2 * w * z = (r : ℂ) ^ 2 * (w * z) by ring,
    hwz, mul_one]

/-- On the unit circle, the algebraic Poisson denominator is the Euler-factor norm square. -/
theorem tsum_semilocalBilateralPoissonTerm_eq_normSq
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ∑' m : ℤ, semilocalBilateralPoissonTerm r z m =
      (1 - (r : ℂ) ^ 2) /
        (Complex.normSq (1 - (r : ℂ) * z) : ℂ) := by
  rw [tsum_semilocalBilateralPoissonTerm_eq_kernel hr0 hr1 hz]
  congr 1
  have hnormSq : Complex.normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]
    norm_num
  have hzinv : z⁻¹ = (starRingEnd ℂ) z := by
    rw [Complex.inv_def, hnormSq]
    simp
  rw [hzinv, Complex.normSq_eq_conj_mul_self]
  simp
  ring

/-- **Exact one-prime Poisson expansion.**  The inverse Euler norm square equals the common
local prefactor `(1-r²)⁻¹` times the absolutely convergent bilateral Fourier series. -/
theorem semilocalOnePrimePoissonExpansion
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (Complex.normSq (1 - (r : ℂ) * z) : ℂ)⁻¹ =
      (1 - (r : ℂ) ^ 2)⁻¹ *
        ∑' m : ℤ, semilocalBilateralPoissonTerm r z m := by
  rw [tsum_semilocalBilateralPoissonTerm_eq_normSq hr0 hr1 hz]
  have hnumPos : 0 < 1 - r ^ 2 := by
    have hleft : 0 < 1 - r := sub_pos.mpr hr1
    have hright : 0 < 1 + r := by linarith
    nlinarith [mul_pos hleft hright]
  have hnum : 1 - (r : ℂ) ^ 2 ≠ 0 := by
    norm_cast
    exact hnumPos.ne'
  have hfactor : 1 - (r : ℂ) * z ≠ 0 := by
    intro hzero
    have hone : (r : ℂ) * z = 1 := (sub_eq_zero.mp hzero).symm
    have hnorm := congrArg norm hone
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0, hz, mul_one,
      norm_one] at hnorm
    linarith
  have hdenReal : Complex.normSq (1 - (r : ℂ) * z) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp hfactor
  have hden : (Complex.normSq (1 - (r : ℂ) * z) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr hdenReal
  field_simp [hnum, hden]

/-- The unit complex phase at the logarithmic frequency of a prime. -/
def semilocalPrimePhase (p : ℕ) (s : ℝ) : ℂ :=
  Complex.exp (((Real.log p * s : ℝ) : ℂ) * Complex.I)

theorem norm_semilocalPrimePhase (p : ℕ) (s : ℝ) :
    ‖semilocalPrimePhase p s‖ = 1 := by
  rw [semilocalPrimePhase, Complex.norm_exp]
  rw [show ((((Real.log p * s : ℝ) : ℂ) * Complex.I).re) = 0 by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, zero_mul, sub_zero]]
  exact Real.exp_zero

/-- The full complex Fourier term of an integer packet on a finite prime family. -/
def semilocalFinitePrimePoissonFourierTerm {n : ℕ}
    (p : Fin n → ℕ) (s : ℝ) (m : Fin n → ℤ) : ℂ :=
  ∏ i, semilocalBilateralPoissonTerm
    (semilocalPrimePoissonRatio (p i)) (semilocalPrimePhase (p i) s) (m i)

/-- Its norm is exactly the positive finite-prime Poisson weight used by the residue tower. -/
theorem norm_semilocalFinitePrimePoissonFourierTerm
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime)
    (s : ℝ) (m : Fin n → ℤ) :
    ‖semilocalFinitePrimePoissonFourierTerm p s m‖ =
      semilocalFinitePrimePoissonWeight p m := by
  simp [semilocalFinitePrimePoissonFourierTerm,
    semilocalFinitePrimePoissonWeight, semilocalBilateralPoissonTerm,
    norm_pow, norm_zpow, norm_semilocalPrimePhase,
    abs_of_pos (semilocalPrimePoissonRatio_pos (hprime _))]

/-- Absolute summability on the full finite integer lattice. -/
theorem summable_norm_semilocalFinitePrimePoissonFourierTerm
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    Summable fun m : Fin n → ℤ =>
      ‖semilocalFinitePrimePoissonFourierTerm p s m‖ := by
  simpa only [norm_semilocalFinitePrimePoissonFourierTerm p hprime s] using
    summable_semilocalFinitePrimePoissonWeight p hprime

theorem summable_semilocalFinitePrimePoissonFourierTerm
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    Summable fun m : Fin n → ℤ =>
      semilocalFinitePrimePoissonFourierTerm p s m :=
  (summable_norm_semilocalFinitePrimePoissonFourierTerm p hprime s).of_norm

/-- Finite Fubini assembly: the product of the local bilateral sums is the single sum over the
finite integer lattice. -/
theorem prod_tsum_semilocalBilateralPoissonTerm_eq_tsum_finitePrime
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    (∏ i, ∑' m : ℤ,
        semilocalBilateralPoissonTerm
          (semilocalPrimePoissonRatio (p i)) (semilocalPrimePhase (p i) s) m) =
      ∑' m : Fin n → ℤ, semilocalFinitePrimePoissonFourierTerm p s m := by
  induction n with
  | zero =>
      simp [semilocalFinitePrimePoissonFourierTerm]
  | succ n ih =>
      let e : ℤ × (Fin n → ℤ) ≃ (Fin (n + 1) → ℤ) :=
        Fin.consEquiv fun _ => ℤ
      rw [Fin.prod_univ_succ]
      rw [ih (fun i => p i.succ) (fun i => hprime i.succ)]
      have hheadNorm : Summable fun z : ℤ =>
          ‖semilocalBilateralPoissonTerm
            (semilocalPrimePoissonRatio (p 0)) (semilocalPrimePhase (p 0) s) z‖ :=
        summable_norm_semilocalBilateralPoissonTerm
          (semilocalPrimePoissonRatio_pos (hprime 0)).le
          (semilocalPrimePoissonRatio_lt_one (hprime 0))
          (norm_semilocalPrimePhase (p 0) s)
      have htailNorm : Summable fun m : Fin n → ℤ =>
          ‖semilocalFinitePrimePoissonFourierTerm (fun i => p i.succ) s m‖ :=
        summable_norm_semilocalFinitePrimePoissonFourierTerm
          (fun i => p i.succ) (fun i => hprime i.succ) s
      rw [tsum_mul_tsum_of_summable_norm hheadNorm htailNorm]
      calc
        (∑' x : ℤ × (Fin n → ℤ),
            semilocalBilateralPoissonTerm
                (semilocalPrimePoissonRatio (p 0))
                (semilocalPrimePhase (p 0) s) x.1 *
              semilocalFinitePrimePoissonFourierTerm
                (fun i => p i.succ) s x.2) =
            ∑' x : ℤ × (Fin n → ℤ),
              semilocalFinitePrimePoissonFourierTerm p s (e x) := by
          apply tsum_congr
          intro x
          simp [e, semilocalFinitePrimePoissonFourierTerm, Fin.prod_univ_succ]
        _ = ∑' m : Fin (n + 1) → ℤ,
              semilocalFinitePrimePoissonFourierTerm p s m :=
          e.tsum_eq _

/-- Prime-specialized inverse Euler-factor Poisson expansion. -/
theorem semilocalPrimePoissonExpansion
    {p : ℕ} (hp : p.Prime) (s : ℝ) :
    (Complex.normSq
        (1 - (semilocalPrimePoissonRatio p : ℂ) * semilocalPrimePhase p s) : ℂ)⁻¹ =
      (1 - (semilocalPrimePoissonRatio p : ℂ) ^ 2)⁻¹ *
        ∑' m : ℤ,
          semilocalBilateralPoissonTerm
            (semilocalPrimePoissonRatio p) (semilocalPrimePhase p s) m := by
  exact semilocalOnePrimePoissonExpansion
    (semilocalPrimePoissonRatio_pos hp).le
    (semilocalPrimePoissonRatio_lt_one hp)
    (norm_semilocalPrimePhase p s)

/-- Factored finite-prime Poisson expansion before the finite Fubini identification with `ℤ^P`. -/
theorem semilocalFinitePrimePoissonExpansion_factored
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    (∏ i, (Complex.normSq
        (1 - (semilocalPrimePoissonRatio (p i) : ℂ) *
          semilocalPrimePhase (p i) s) : ℂ)⁻¹) =
      (∏ i, (1 - (semilocalPrimePoissonRatio (p i) : ℂ) ^ 2)⁻¹) *
        ∏ i, ∑' m : ℤ,
          semilocalBilateralPoissonTerm
            (semilocalPrimePoissonRatio (p i)) (semilocalPrimePhase (p i) s) m := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _hi
  exact semilocalPrimePoissonExpansion (hprime i) s

/-- **Exact finite-prime Poisson expansion.**  The product inverse Euler density is the common
finite local prefactor times one absolutely convergent sum over `ℤ^P`. -/
theorem semilocalFinitePrimePoissonExpansion
    {n : ℕ} (p : Fin n → ℕ) (hprime : ∀ i, (p i).Prime) (s : ℝ) :
    (∏ i, (Complex.normSq
        (1 - (semilocalPrimePoissonRatio (p i) : ℂ) *
          semilocalPrimePhase (p i) s) : ℂ)⁻¹) =
      (∏ i, (1 - (semilocalPrimePoissonRatio (p i) : ℂ) ^ 2)⁻¹) *
        ∑' m : Fin n → ℤ, semilocalFinitePrimePoissonFourierTerm p s m := by
  rw [semilocalFinitePrimePoissonExpansion_factored p hprime s]
  rw [prod_tsum_semilocalBilateralPoissonTerm_eq_tsum_finitePrime p hprime s]

end RHTower
