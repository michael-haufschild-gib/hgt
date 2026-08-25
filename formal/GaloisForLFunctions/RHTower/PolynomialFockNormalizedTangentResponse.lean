import GaloisForLFunctions.RHTower.CriticalPrimeFockScaledAdaptedCellMass
import GaloisForLFunctions.RHTower.PolynomialFockSharpPhaseTransition
import GaloisForLFunctions.RHTower.CriticalPrimeSamplingQuadraticForm
import GaloisForLFunctions.HTGeometry.NormalizeApply

open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

theorem polynomialFockInnerWindowFactor_le_one
    {m : ℝ} (hm : 4 ≤ m) : polynomialFockInnerWindowFactor m ≤ 1 := by
  have he : 0 ≤ m / 2 - 1 := by linarith
  have hp : (1 : ℝ) ≤ 2 ^ (m / 2 - 1) :=
    Real.one_le_rpow (by norm_num) he
  have hprod : (1 : ℝ) ≤ m * 2 ^ (m / 2 - 1) := by
    calc
      (1 : ℝ) ≤ 4 * 1 := by norm_num
      _ ≤ m * 2 ^ (m / 2 - 1) :=
        mul_le_mul hm hp (by norm_num) (by linarith)
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (m * 2 ^ (m / 2 - 1)) :=
    Real.one_le_sqrt.2 hprod
  unfold polynomialFockInnerWindowFactor
  exact (inv_le_one₀ (Real.sqrt_pos.2 (lt_of_lt_of_le zero_lt_one hprod))).2 hsqrt

theorem polynomialMomentFockTangentVector_ne_zero_of_two_le
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) :
    polynomialMomentFockTangentVector m hm x ≠ 0 := by
  intro hzero
  have hbase := polynomialMomentFockEvaluation_tangentVector_base m hm x
  rw [hzero, map_zero] at hbase
  norm_num at hbase

def polynomialMomentFockNormalizedTangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) : MomentFock :=
  ((‖polynomialMomentFockTangentVector m hm x‖ : ℂ))⁻¹ •
    polynomialMomentFockTangentVector m hm x

theorem norm_polynomialMomentFockNormalizedTangentVector
    (m : ℝ) (hm : 2 ≤ m) (x : ℝ) :
    ‖polynomialMomentFockNormalizedTangentVector m hm x‖ = 1 := by
  have hv := polynomialMomentFockTangentVector_ne_zero_of_two_le m hm x
  have hvpos : 0 < ‖polynomialMomentFockTangentVector m hm x‖ := norm_pos_iff.mpr hv
  rw [polynomialMomentFockNormalizedTangentVector, norm_smul, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvpos]
  exact inv_mul_cancel₀ hvpos.ne'

theorem scaledWindow_tangentVector_incidence_response_lower
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        ‖polynomialMomentFockTangentVector m (by linarith) x‖ ^ 2 *
        primeLogWindowMass x
          (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x) ≤
      3 ^ (m / 2 - 1) *
        (inner ℂ
          (polynomialCriticalPrimeSamplingIncidence m hm
            (polynomialMomentFockTangentVector m (by linarith) x))
          (polynomialMomentFockTangentVector m (by linarith) x)).re := by
  let hm2 : 2 ≤ m := by linarith
  let v : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let r : ℝ := polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x
  let T : Finset Nat.Primes := criticalPrimeWindowPrimes x r
  have henergy := scaledWindow_tangentVector_energy_lower hm hx
  have hsamp0 := summable_normSq_criticalPrimeKernelRestriction_polynomial hm v
  have hsamp : Summable fun p : Nat.Primes =>
      criticalPrimeSamplingWeight p *
        ‖inner ℂ
          (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
            ((Real.log (p : ℝ) : ℝ) : ℂ)) v‖ ^ 2 := by
    refine hsamp0.congr ?_
    intro p
    rw [Real.rpow_two, normSq_criticalPrimeKernelRestriction_eq]
    rfl
  have hfin :
      ∑ p ∈ T, criticalPrimeSamplingWeight p *
          ‖inner ℂ
            (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
              ((Real.log (p : ℝ) : ℝ) : ℂ)) v‖ ^ 2 ≤
        ∑' p : Nat.Primes, criticalPrimeSamplingWeight p *
          ‖inner ℂ
            (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
              ((Real.log (p : ℝ) : ℝ) : ℂ)) v‖ ^ 2 :=
    hsamp.sum_le_tsum T (fun p _ => mul_nonneg
      (criticalPrimeSamplingWeight_pos p).le (sq_nonneg _))
  have hQ : 0 ≤ (3 : ℝ) ^ (m / 2 - 1) := Real.rpow_nonneg (by norm_num) _
  have hresponse :=
    re_inner_polynomialCriticalPrimeSamplingIncidence_apply_eq_tsum m hm v
  change Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        ‖v‖ ^ 2 * primeLogWindowMass x r ≤
      3 ^ (m / 2 - 1) *
        (inner ℂ (polynomialCriticalPrimeSamplingIncidence m hm v) v).re
  calc
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
          ‖v‖ ^ 2 * primeLogWindowMass x r
        ≤ 3 ^ (m / 2 - 1) *
          ∑ p ∈ T, criticalPrimeSamplingWeight p *
            ‖inner ℂ
              (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
                ((Real.log (p : ℝ) : ℝ) : ℂ)) v‖ ^ 2 := by
          simpa [v, r, T, hm2] using henergy
    _ ≤ 3 ^ (m / 2 - 1) *
        ∑' p : Nat.Primes, criticalPrimeSamplingWeight p *
          ‖inner ℂ
            (normalizedMomentFockKernel (polynomialMomentFockData m hm2)
              ((Real.log (p : ℝ) : ℝ) : ℂ)) v‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hfin hQ
    _ = 3 ^ (m / 2 - 1) *
        (inner ℂ (polynomialCriticalPrimeSamplingIncidence m hm v) v).re := by
      rw [hresponse]
      rfl

theorem re_inner_criticalPrimeSamplingIncidence_apply_eq_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] CriticalPrimeEllTwo) (f : H) :
    (inner ℂ (criticalPrimeSamplingIncidence S f) f).re = ‖S f‖ ^ 2 := by
  rw [criticalPrimeSamplingIncidence, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, inner_self_eq_norm_sq_to_K]
  have hcast : ((↑‖S f‖ ^ 2 : ℂ)).re = ‖S f‖ ^ 2 := by
    rw [← Complex.ofReal_pow]
    rfl
  exact hcast

theorem re_inner_criticalPrimeSamplingIncidence_normalize_mul_norm_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : H →L[ℂ] CriticalPrimeEllTwo) {v : H} (hv : v ≠ 0) :
    (inner ℂ
        (criticalPrimeSamplingIncidence S (((‖v‖ : ℂ))⁻¹ • v))
        (((‖v‖ : ℂ))⁻¹ • v)).re * ‖v‖ ^ 2 =
      (inner ℂ (criticalPrimeSamplingIncidence S v) v).re := by
  rw [re_inner_criticalPrimeSamplingIncidence_apply_eq_norm_sq,
    re_inner_criticalPrimeSamplingIncidence_apply_eq_norm_sq,
    ContinuousLinearMap.map_smul, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [abs_of_pos hvpos]
  field_simp

theorem scaledWindow_normalizedTangentVector_incidence_response_lower
    {m x : ℝ} (hm : 4 ≤ m) (hx : 1 ≤ x) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        primeLogWindowMass x
          (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x) ≤
      3 ^ (m / 2 - 1) *
        (inner ℂ
          (polynomialCriticalPrimeSamplingIncidence m hm
            (polynomialMomentFockNormalizedTangentVector m (by linarith) x))
          (polynomialMomentFockNormalizedTangentVector m (by linarith) x)).re := by
  let hm2 : 2 ≤ m := by linarith
  let v : MomentFock := polynomialMomentFockTangentVector m hm2 x
  let u : MomentFock := polynomialMomentFockNormalizedTangentVector m hm2 x
  let S : MomentFock →L[ℂ] CriticalPrimeEllTwo :=
    polynomialCriticalPrimeSamplingOperator m hm
  have hv : v ≠ 0 := polynomialMomentFockTangentVector_ne_zero_of_two_le m hm2 x
  have hvnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have henergy := scaledWindow_tangentVector_incidence_response_lower hm hx
  have hscale :=
    re_inner_criticalPrimeSamplingIncidence_normalize_mul_norm_sq S hv
  change Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        primeLogWindowMass x
          (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x) ≤
      3 ^ (m / 2 - 1) *
        (inner ℂ (criticalPrimeSamplingIncidence S u) u).re
  have hmul :
      (Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
          primeLogWindowMass x
            (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x)) *
          ‖v‖ ^ 2 ≤
        (3 ^ (m / 2 - 1) *
          (inner ℂ (criticalPrimeSamplingIncidence S u) u).re) * ‖v‖ ^ 2 := by
    calc
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
          primeLogWindowMass x
            (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x) * ‖v‖ ^ 2
        = Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
            ‖v‖ ^ 2 * primeLogWindowMass x
              (polynomialFockInnerWindowFactor m * criticalPrimeFockRadius m x) := by ring
    _ ≤ 3 ^ (m / 2 - 1) *
        (inner ℂ (criticalPrimeSamplingIncidence S v) v).re := by
      simpa [S, v, hm2, polynomialCriticalPrimeSamplingIncidence] using henergy
    _ = 3 ^ (m / 2 - 1) *
        ((inner ℂ (criticalPrimeSamplingIncidence S u) u).re * ‖v‖ ^ 2) := by
      rw [← hscale]
      rfl
    _ = (3 ^ (m / 2 - 1) *
        (inner ℂ (criticalPrimeSamplingIncidence S u) u).re) * ‖v‖ ^ 2 := by ring
  exact le_of_mul_le_mul_right hmul hvnorm

theorem re_inner_comm_complex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x y : H) :
    (inner ℂ x y).re = (inner ℂ y x).re := by
  have h := congrArg Complex.re (inner_conj_symm x y)
  simpa only [Complex.conj_re] using h.symm

def polynomialFockAdaptedNormalizedTangentPacket
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) : MomentFock :=
  polynomialMomentFockNormalizedTangentVector m (by linarith)
    (criticalPrimeFockAdaptedCellCenter m n)

theorem norm_polynomialFockAdaptedNormalizedTangentPacket
    (m : ℝ) (hm : 4 ≤ m) (n : ℕ) :
    ‖polynomialFockAdaptedNormalizedTangentPacket m hm n‖ = 1 := by
  exact norm_polynomialMomentFockNormalizedTangentVector m (by linarith)
    (criticalPrimeFockAdaptedCellCenter m n)

theorem adaptedCell_normalizedTangentPacket_incidence_response_lower
    {m : ℝ} (hm : 4 ≤ m) {n : ℕ}
    (hn : 1 ≤ criticalPrimeFockAdaptedCellCenter m n) :
    Real.exp (-4 * (polynomialFockLocalBregmanConstant m / m)) *
        criticalPrimeFockScaledAdaptedCellMass m
          (polynomialFockInnerWindowFactor m) n ≤
      3 ^ (m / 2 - 1) *
        (inner ℂ (polynomialFockAdaptedNormalizedTangentPacket m hm n)
          (polynomialCriticalPrimeSamplingIncidence m hm
            (polynomialFockAdaptedNormalizedTangentPacket m hm n))).re := by
  have h := scaledWindow_normalizedTangentVector_incidence_response_lower
    (m := m) (x := criticalPrimeFockAdaptedCellCenter m n) hm hn
  rw [← re_inner_comm_complex] at h
  simpa [criticalPrimeFockScaledAdaptedCellMass,
    polynomialFockAdaptedNormalizedTangentPacket] using h

theorem summable_rpow_criticalPrimeFockInnerWindowAdaptedCellMass_iff
    {m q : ℝ} (hm : 4 < m) (hq : 0 < q) :
    Summable (fun n : ℕ =>
      criticalPrimeFockScaledAdaptedCellMass m
        (polynomialFockInnerWindowFactor m) n ^ q) ↔
      criticalPrimeFockSchattenThreshold m < q := by
  exact summable_rpow_criticalPrimeFockScaledAdaptedCellMass_iff hm
    (polynomialFockInnerWindowFactor_pos hm.le)
    (polynomialFockInnerWindowFactor_le_one hm.le) hq

end

end RHTower

