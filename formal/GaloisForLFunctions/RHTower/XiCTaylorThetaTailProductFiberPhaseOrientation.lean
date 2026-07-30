import GaloisForLFunctions.HTGeometry.MultiplicativeCenteredDivisorOrientation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation

/-!
# Orientation of the complete square-index product-fibre phase

The zero-based theta factor pairs with product `k` are exactly the positive divisor
antidiagonal after adding one to both indices.  Hence their centered logarithmic phase packet is
the complete centered divisor packet.  Unique factorization then supplies an exact product of
prime-power geometric packets and strict negative upper oriented current for every `k > 1`.

This is the full finite arithmetic sign before positive-half-line endpoint polarization.  It does
not by itself sign the integrated Taylor core: that later operation introduces the swept-window
seam isolated in `XiCTaylorThetaTailArithmeticPhaseSeam`.
-/

open Complex Real Finset


namespace RHTower
noncomputable section

open GaloisForLFunctions.HTGeometry

def thetaProductFiberCenteredPhase (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    Complex.exp (I * (thetaFactorPairLogDisplacement q : ℂ) * z)

def thetaProductFiberCenteredPhaseDerivative (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (I * (thetaFactorPairLogDisplacement q : ℂ)) *
      Complex.exp (I * (thetaFactorPairLogDisplacement q : ℂ) * z)

theorem hasDerivAt_thetaProductFiberCenteredPhase (k : ℕ) (z : ℂ) :
    HasDerivAt (thetaProductFiberCenteredPhase k)
      (thetaProductFiberCenteredPhaseDerivative k z) z := by
  unfold thetaProductFiberCenteredPhase thetaProductFiberCenteredPhaseDerivative
  have hsum := HasDerivAt.fun_sum (u := thetaPositiveFactorPairs k) (x := z)
    (A := fun q (u : ℂ) =>
      Complex.exp (I * (thetaFactorPairLogDisplacement q : ℂ) * u))
    (A' := fun q =>
      (I * (thetaFactorPairLogDisplacement q : ℂ)) *
        Complex.exp (I * (thetaFactorPairLogDisplacement q : ℂ) * z))
    (fun q _hq => by
      let a : ℂ := I * (thetaFactorPairLogDisplacement q : ℂ)
      have hinner : HasDerivAt (fun u : ℂ => a * u) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      have hcomp := (Complex.hasDerivAt_exp (a * z)).comp z hinner
      simpa only [a] using! hcomp.congr_deriv (by ring))
  exact hsum

def thetaPositiveFactorPairSuccEmbedding : (ℕ × ℕ) ↪ (ℕ × ℕ) :=
  ⟨fun q => (q.1 + 1, q.2 + 1), by
    intro a b h
    ext <;> simp_all⟩

theorem thetaPositiveFactorPairs_map_succ
    {k : ℕ} (hk : k ≠ 0) :
    (thetaPositiveFactorPairs k).map thetaPositiveFactorPairSuccEmbedding =
      k.divisorsAntidiagonal := by
  ext r
  constructor
  · intro hr
    rw [Finset.mem_map] at hr
    obtain ⟨q, hq, rfl⟩ := hr
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨(Finset.mem_filter.mp hq).2, hk⟩
  · intro hr
    have hdata := (Nat.mem_divisorsAntidiagonal.mp hr)
    have hrprod : r.1 * r.2 = k := hdata.1
    have hrne : r.1 ≠ 0 ∧ r.2 ≠ 0 := by
      have hprodne : r.1 * r.2 ≠ 0 := by
        rw [hrprod]
        exact hk
      exact ⟨left_ne_zero_of_mul hprodne, right_ne_zero_of_mul hprodne⟩
    let q : ℕ × ℕ := (r.1 - 1, r.2 - 1)
    have hq1 : q.1 + 1 = r.1 := by
      dsimp only [q]
      omega
    have hq2 : q.2 + 1 = r.2 := by
      dsimp only [q]
      omega
    rw [Finset.mem_map]
    refine ⟨q, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        constructor
        · dsimp only [q]
          have hr1le : r.1 ≤ k := by
            rw [← hrprod]
            exact Nat.le_mul_of_pos_right r.1 (Nat.pos_of_ne_zero hrne.2)
          exact Finset.mem_range.mpr (by omega)
        · dsimp only [q]
          have hr2le : r.2 ≤ k := by
            rw [← hrprod]
            exact Nat.le_mul_of_pos_left r.2 (Nat.pos_of_ne_zero hrne.1)
          exact Finset.mem_range.mpr (by omega)
      · rw [hq1, hq2, hrprod]
    · ext <;> simp [thetaPositiveFactorPairSuccEmbedding, hq1, hq2]

theorem thetaProductFiberCenteredPhase_eq_antidiagonal
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    thetaProductFiberCenteredPhase k z =
      ∑ r ∈ k.divisorsAntidiagonal,
        Complex.exp
          (I * (((Real.log r.1 - Real.log r.2) / 2 : ℝ) : ℂ) * z) := by
  unfold thetaProductFiberCenteredPhase
  rw [← thetaPositiveFactorPairs_map_succ hk, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro q _hq
  rfl

theorem centeredDivisorPhase_eq_antidiagonal
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    centeredDivisorPhase k z =
      ∑ r ∈ k.divisorsAntidiagonal,
        Complex.exp
          (I * (((Real.log r.1 - Real.log r.2) / 2 : ℝ) : ℂ) * z) := by
  rw [centeredDivisorPhase, centeredDivisorPhaseAF_eq_divisor_sum hk]
  have hanti := Nat.sum_divisorsAntidiagonal
    (n := k) (fun a b : ℕ =>
      Complex.exp
        (I * (((Real.log a - Real.log b) / 2 : ℝ) : ℂ) * z))
  rw [hanti]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hmul : d * (k / d) = k := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  have hkd0 : k / d ≠ 0 := by
    intro hzero
    apply hk
    simpa [hzero] using hmul.symm
  have hkdpos : 0 < k / d := Nat.pos_of_ne_zero hkd0
  have hlog : Real.log (k : ℝ) =
      Real.log (d : ℝ) + Real.log ((k / d : ℕ) : ℝ) := by
    have hcast : (k : ℝ) = (d : ℝ) * ((k / d : ℕ) : ℝ) := by
      exact_mod_cast hmul.symm
    rw [hcast, Real.log_mul (by positivity) (by positivity)]
  have hreal :
      -Real.log (k : ℝ) / 2 + Real.log (d : ℝ) =
        (Real.log (d : ℝ) - Real.log ((k / d : ℕ) : ℝ)) / 2 := by
    rw [hlog]
    ring
  rw [← Complex.exp_add]
  congr 1
  calc
    -I * ((Real.log (k : ℝ) / 2 : ℝ) : ℂ) * z +
          I * (Real.log (d : ℝ) : ℂ) * z =
        I * ((-Real.log (k : ℝ) / 2 + Real.log (d : ℝ) : ℝ) : ℂ) * z := by
          push_cast
          ring
    _ = I * (((Real.log (d : ℝ) -
          Real.log ((k / d : ℕ) : ℝ)) / 2 : ℝ) : ℂ) * z := by
      rw [hreal]

theorem thetaProductFiberCenteredPhase_eq_centeredDivisorPhase
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    thetaProductFiberCenteredPhase k z = centeredDivisorPhase k z := by
  rw [thetaProductFiberCenteredPhase_eq_antidiagonal hk,
    centeredDivisorPhase_eq_antidiagonal hk]

theorem thetaProductFiberCenteredPhaseDerivative_eq_centeredDivisorPhaseDerivative
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    thetaProductFiberCenteredPhaseDerivative k z =
      centeredDivisorPhaseDerivative k z := by
  have hleft := hasDerivAt_thetaProductFiberCenteredPhase k z
  have hfun : thetaProductFiberCenteredPhase k = centeredDivisorPhase k := by
    funext u
    exact thetaProductFiberCenteredPhase_eq_centeredDivisorPhase hk u
  rw [hfun] at hleft
  have hright : HasDerivAt (centeredDivisorPhase k)
      (centeredDivisorPhaseDerivative k z) z := by
    rw [centeredDivisorPhaseDerivative_eq_factorized hk]
    exact hasDerivAt_centeredDivisorPhase hk z
  exact hleft.unique hright

/-- Exact prime-factor signed polarization of the complete square-index translate fibre. -/
theorem thetaProductFiberCenteredPhase_current_eq_sum_primeFactors
    {k : ℕ} (hk : k ≠ 0) (z : ℂ) :
    (thetaProductFiberCenteredPhaseDerivative k z *
      (starRingEnd ℂ) (thetaProductFiberCenteredPhase k z)).im =
      ∑ p ∈ k.primeFactors,
        Complex.normSq
            (∏ q ∈ k.primeFactors.erase p,
              primePowerCenteredDivisorPhase q (k.factorization q) z) *
          (primePowerCenteredDivisorPhaseDerivative p (k.factorization p) z *
            (starRingEnd ℂ)
              (primePowerCenteredDivisorPhase p (k.factorization p) z)).im := by
  rw [thetaProductFiberCenteredPhaseDerivative_eq_centeredDivisorPhaseDerivative hk,
    thetaProductFiberCenteredPhase_eq_centeredDivisorPhase hk]
  exact centeredDivisorPhase_current_eq_sum_primeFactors hk z

/-- Strict upper orientation of the complete square-index product fibre before its phase is
conjugate-polarized with the positive-half-line seam. -/
theorem thetaProductFiberCenteredPhase_current_lt_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    (thetaProductFiberCenteredPhaseDerivative k z *
      (starRingEnd ℂ) (thetaProductFiberCenteredPhase k z)).im < 0 := by
  rw [thetaProductFiberCenteredPhaseDerivative_eq_centeredDivisorPhaseDerivative
      (by omega),
    thetaProductFiberCenteredPhase_eq_centeredDivisorPhase (by omega)]
  exact centeredDivisorPhase_current_lt_zero hk hz

/-- A nontrivial complete square-index product fibre has no upper-half-plane zero. -/
theorem thetaProductFiberCenteredPhase_ne_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    thetaProductFiberCenteredPhase k z ≠ 0 := by
  intro hzero
  have h := thetaProductFiberCenteredPhase_current_lt_zero hk hz
  simp [hzero] at h

end
end RHTower
