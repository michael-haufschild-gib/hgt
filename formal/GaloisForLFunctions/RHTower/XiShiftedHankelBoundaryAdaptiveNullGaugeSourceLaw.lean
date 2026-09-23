import GaloisForLFunctions.RHTower.XiShiftedHankelBoundaryAdaptiveShearRayIntegral
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Adaptive null-gauge source law

The completed adaptive `P^sharp` packet is the second coefficient of one source-first normal
germ.  For a monic amplitude `A` of degree `N`, its null-root gauge is

`kappa_A(u) = sum_j A_j (-u)^(N-j)`.

Writing `K = 2N+1`, divide the full Padé mass-shift germ by `kappa_A`.  At a flat null flag,
the Cauchy coefficient at order two is exactly `K` times the adaptive shear.  The linear gauge
coefficient supplies the null-root barycenter term; the raw contact coefficient supplies the
first even successor defect.  The single inverse is the one-factor monic normalization forced by
the mixed bilinear amplitude; the squared energy would carry two inverse gauges.  Thus neither
term is a chosen reporter.  Away from contact an explicit degree-`<2N+1` residual records the
lower flag, so the transported source is coefficient minus residual rather than the raw
coefficient alone.
-/

open Matrix Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Polynomial null-root gauge.  Its value at `u` is
`sum_j A_j (-u)^(N-j)`, the leading coefficient of the degree-`N` Mobius transport of `A`. -/
def xiShiftedAdaptiveNullRootGaugePolynomial
    (A : Polynomial ℝ) (N : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    monomial (N - j) ((-1 : ℝ) ^ (N - j) * A.coeff j)

/-- The null-root gauge is not an auxiliary reporter: at every shift it is literally the leading
coefficient of the Möbius-transported amplitude.  Thus one inverse gauge normalizes exactly one
factor in the mixed amplitude. -/
theorem coeff_mobiusTransportedNullPolynomial_eq_eval_adaptiveNullRootGauge
    (A : Polynomial ℝ) (N : ℕ) (u : ℝ) :
    (mobiusTransportedNullPolynomial A N u).coeff N =
      (xiShiftedAdaptiveNullRootGaugePolynomial A N).eval u := by
  rw [mobiusTransportedNullPolynomial,
    xiShiftedAdaptiveNullRootGaugePolynomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < N + 1 := Finset.mem_range.mp hj
  have hjle : j ≤ N := by omega
  have hleftDeg : (C (A.coeff j) * X ^ j : Polynomial ℝ).natDegree ≤ j := by
    exact (natDegree_mul_le.trans (by simp))
  have hbaseDeg : (1 - C u * X : Polynomial ℝ).natDegree ≤ 1 := by
    have hCuX : (C u * X : Polynomial ℝ).natDegree ≤ 1 := by
      calc
        (C u * X : Polynomial ℝ).natDegree ≤
            (C u).natDegree + X.natDegree := natDegree_mul_le
        _ ≤ 1 := by simp
    exact (natDegree_sub_le _ _).trans (max_le (by simp) hCuX)
  have hrightDeg : ((1 - C u * X : Polynomial ℝ) ^ (N - j)).natDegree ≤ N - j := by
    calc
      ((1 - C u * X : Polynomial ℝ) ^ (N - j)).natDegree ≤
          (N - j) * (1 - C u * X : Polynomial ℝ).natDegree := natDegree_pow_le
      _ ≤ (N - j) * 1 := Nat.mul_le_mul_left _ hbaseDeg
      _ = N - j := by simp
  have hNsum : N = j + (N - j) := by omega
  rw [hNsum]
  simp only [Nat.add_sub_cancel_left]
  rw [coeff_mul_add_eq_of_natDegree_le hleftDeg hrightDeg]
  rw [coeff_C_mul, coeff_X_pow_self, mul_one]
  have hpowCoeff :
      ((1 - C u * X : Polynomial ℝ) ^ (N - j)).coeff (N - j) =
        (1 - C u * X : Polynomial ℝ).coeff 1 ^ (N - j) := by
    simpa using (coeff_pow_of_natDegree_le (m := N - j) hbaseDeg)
  rw [hpowCoeff, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X,
    Polynomial.coeff_one]
  norm_num
  rw [neg_pow]
  ring

/-- Full admission-sensitive normal source series: inverse null-root gauge times the actual Padé defect
germ, before any scalar reflection aggregation. -/
def xiShiftedAdaptiveNullGaugeSourceSeries
    (a : ℕ → ℝ) (A : Polynomial ℝ) (N : ℕ) : PowerSeries ℝ :=
  (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ *
    HTGeometry.mobiusPadeContactSeries a A N

private theorem powerSeries_coeff_two_mul (f g : PowerSeries ℝ) :
    PowerSeries.coeff 2 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
          PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
  rw [PowerSeries.coeff_mul]
  norm_num [Finset.HasAntidiagonal.antidiagonal]
  ring

theorem coeff_zero_xiShiftedAdaptiveNullRootGaugePolynomial
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedAdaptiveNullRootGaugePolynomial A N).coeff 0 = 1 := by
  rw [xiShiftedAdaptiveNullRootGaugePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single N]
  · simp [← hAdeg, hA.coeff_natDegree]
  · intro j hj hjne
    have hjle : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjlt : j < N := lt_of_le_of_ne hjle hjne
    simp [Polynomial.coeff_monomial, show N - j ≠ 0 by omega]
  · simp

theorem coeff_one_xiShiftedAdaptiveNullRootGaugePolynomial
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedAdaptiveNullRootGaugePolynomial A N).coeff 1 = -A.nextCoeff := by
  by_cases hN : N = 0
  · have hAdeg0 : A.natDegree = 0 := hAdeg.trans hN
    have hAone := Polynomial.eq_one_of_monic_natDegree_zero hA hAdeg0
    subst A
    subst N
    norm_num [xiShiftedAdaptiveNullRootGaugePolynomial, Polynomial.nextCoeff]
    rw [Polynomial.coeff_one]
    norm_num
  · rw [xiShiftedAdaptiveNullRootGaugePolynomial, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (N - 1)]
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      have hsub : N - (N - 1) = 1 := by omega
      rw [Polynomial.coeff_monomial, if_pos hsub]
      rw [Polynomial.nextCoeff_of_natDegree_pos (by omega : 0 < A.natDegree), hAdeg]
      rw [hsub]
      norm_num
    · intro j hj hjne
      have hjle : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [Polynomial.coeff_monomial]
      split_ifs with heq
      · have : j = N - 1 := by omega
        exact (hjne this).elim
      · rfl
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
      simp

theorem coeff_zero_inv_xiShiftedAdaptiveNullRootGaugePolynomial
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    PowerSeries.coeff 0
        (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ = 1 := by
  rw [PowerSeries.coeff_inv]
  norm_num
  exact coeff_zero_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg

theorem coeff_one_inv_xiShiftedAdaptiveNullRootGaugePolynomial
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    PowerSeries.coeff 1
        (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ = A.nextCoeff := by
  have hconst : PowerSeries.constantCoeff
      (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg]
  rw [PowerSeries.coeff_inv]
  norm_num [Finset.HasAntidiagonal.antidiagonal,
    PowerSeries.constantCoeff, coeff_zero_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg,
    coeff_one_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg,
    coeff_zero_inv_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg]
  change (PowerSeries.constantCoeff
      (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ))⁻¹ *
        A.nextCoeff = A.nextCoeff
  rw [hconst]
  norm_num

/-- Exact lower-contact memory discarded by the associated-graded adaptive source law.  It is the
difference between the full second null-gauged coefficient polynomial and `2N+1` times the
adaptive shear.  Unlike the shear, this term is supported strictly below odd contact. -/
def xiShiftedAdaptiveNullGaugeLowerResidualPolynomial
    (A : Polynomial ℝ) (N : ℕ) : Polynomial ℝ :=
  (((((2 * N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ)) • (A ^ (2 : ℕ) * X ^ (2 : ℕ)) -
      (((2 * N + 1 : ℕ) : ℝ) * A.nextCoeff) • (A ^ (2 : ℕ) * X)) +
    PowerSeries.coeff 2
      (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ • (A ^ (2 : ℕ))) -
    ((2 * N + 1 : ℕ) : ℝ) • xiShiftedBoundaryAdaptiveShearPolynomial A

/-- **Associated-graded support theorem.** One inverse null gauge cancels both degrees above the
odd contact: the full correction to adaptive shear has degree strictly below `2N+1`.  This is the
precise algebraic reason flat admission, rather than a chosen reporter, produces the shear. -/
theorem degree_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_lt_contact
    {A : Polynomial ℝ} {N : ℕ} (hA : A.Monic) (hAdeg : A.natDegree = N) :
    (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N).degree <
      ((2 * N + 1 : ℕ) : WithBot ℕ) := by
  have hA2 : (A ^ (2 : ℕ)).Monic := hA.pow 2
  have hA2deg : (A ^ (2 : ℕ)).natDegree = 2 * N := by
    rw [Polynomial.natDegree_pow, hAdeg]
  have hA2X : (A ^ (2 : ℕ) * X).Monic := hA2.mul Polynomial.monic_X
  have hA2Xdeg : (A ^ (2 : ℕ) * X).natDegree = 2 * N + 1 := by
    rw [hA2.natDegree_mul Polynomial.monic_X, hA2deg]
    simp
  have hA2X2 : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).Monic := hA2.mul (Polynomial.monic_X_pow 2)
  have hA2X2deg : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).natDegree = 2 * N + 2 := by
    rw [hA2.natDegree_mul (Polynomial.monic_X_pow 2), hA2deg,
      Polynomial.natDegree_X_pow]
  have hdeg : (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N).natDegree ≤
      2 * N + 2 := by
    rw [xiShiftedAdaptiveNullGaugeLowerResidualPolynomial]
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · exact (Polynomial.natDegree_smul_le _ _).trans_eq hA2X2deg
        · exact (Polynomial.natDegree_smul_le _ _).trans
            (hA2Xdeg.le.trans (by omega))
      · exact (Polynomial.natDegree_smul_le _ _).trans
          (hA2deg.le.trans (by omega))
    · exact (Polynomial.natDegree_smul_le _ _).trans
        (natDegree_xiShiftedBoundaryAdaptiveShearPolynomial_le hA hAdeg)
  have hcoeffA2X2top : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).coeff (2 * N + 2) = 1 := by
    rw [← hA2X2deg]
    exact hA2X2.coeff_natDegree
  have hcoeffA2Xtop : (A ^ (2 : ℕ) * X).coeff (2 * N + 1) = 1 := by
    rw [← hA2Xdeg]
    exact hA2X.coeff_natDegree
  have hcoeffA2X2next : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).coeff (2 * N + 1) =
      2 * A.nextCoeff := by
    by_cases hN : N = 0
    · have hAone := Polynomial.eq_one_of_monic_natDegree_zero hA (hAdeg.trans hN)
      subst A
      subst N
      norm_num [Polynomial.nextCoeff]
    · have hA2pos : 0 < (A ^ (2 : ℕ)).natDegree := by rw [hA2deg]; omega
      have hnext : (A ^ (2 : ℕ)).nextCoeff = 2 * A.nextCoeff := by
        rw [hA.nextCoeff_pow]
        norm_num
      have hcoeff : (A ^ (2 : ℕ)).coeff (2 * N - 1) = 2 * A.nextCoeff := by
        rw [← hnext, Polynomial.nextCoeff_of_natDegree_pos hA2pos, hA2deg]
      have hindex : 2 * N - 1 + 2 = 2 * N + 1 := by omega
      rw [← hindex, Polynomial.coeff_mul_X_pow, hcoeff]
  have htop : (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N).coeff
      (2 * N + 2) = 0 := by
    have hA2Xzero : (A ^ (2 : ℕ) * X).coeff (2 * N + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hA2Xdeg]; omega)
    have hA2zero : (A ^ (2 : ℕ)).coeff (2 * N + 2) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hA2deg]; omega)
    simp only [xiShiftedAdaptiveNullGaugeLowerResidualPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
    rw [hcoeffA2X2top, hA2Xzero, hA2zero,
      coeff_xiShiftedBoundaryAdaptiveShearPolynomial_top hA hAdeg]
    push_cast
    ring
  have hnext : (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N).coeff
      (2 * N + 1) = 0 := by
    have hA2zero : (A ^ (2 : ℕ)).coeff (2 * N + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hA2deg]; omega)
    simp only [xiShiftedAdaptiveNullGaugeLowerResidualPolynomial, Polynomial.coeff_sub,
      Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
    rw [hcoeffA2X2next, hcoeffA2Xtop, hA2zero,
      coeff_xiShiftedBoundaryAdaptiveShearPolynomial_next hA hAdeg]
    push_cast
    ring
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  by_cases hk0 : k = 2 * N + 1
  · simpa [hk0] using hnext
  by_cases hk1 : k = 2 * N + 2
  · simpa [hk1] using htop
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (by omega))

/-- **Full moving-flag producer.** Without a flatness assumption, the second null-gauged source
coefficient is adaptive shear plus one explicit lower-contact memory term.  This is the exact
formula needed away from the contact point, where reusing the contact identity would be invalid. -/
theorem coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_shear_add_lowerResidual
    {a : ℕ → ℝ} {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N) :
    PowerSeries.coeff 2 (xiShiftedAdaptiveNullGaugeSourceSeries a A N) =
      ((2 * N + 1 : ℕ) : ℝ) *
          HTGeometry.momentFunctional a (xiShiftedBoundaryAdaptiveShearPolynomial A) +
        HTGeometry.momentFunctional a
          (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N) := by
  have hg0 := coeff_zero_inv_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg
  have hg1 := coeff_one_inv_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg
  have hchoose : Nat.choose (2 * N + 2) 2 = (2 * N + 1) * (N + 1) := by
    rw [Nat.choose_two_right]
    rw [show 2 * N + 2 = 2 * (N + 1) by omega,
      show 2 * (N + 1) - 1 = 2 * N + 1 by omega]
    rw [show 2 * (N + 1) * (2 * N + 1) =
      2 * ((N + 1) * (2 * N + 1)) by ring,
      Nat.mul_div_right _ (by omega : 0 < 2)]
    exact Nat.mul_comm _ _
  rw [xiShiftedAdaptiveNullGaugeSourceSeries, powerSeries_coeff_two_mul]
  rw [hg0, hg1]
  simp only [HTGeometry.coeff_mobiusPadeContactSeries, pow_zero, one_mul,
    Nat.choose_zero_right, Nat.cast_one, pow_one, Nat.choose_one_right,
    hchoose, xiShiftedAdaptiveNullGaugeLowerResidualPolynomial,
    HTGeometry.momentFunctional_sub, HTGeometry.momentFunctional_add,
    HTGeometry.momentFunctional_smul]
  push_cast
  ring

/-- Flat admission annihilates the complete moving-flag memory term because its degree lies below
the odd contact. -/
theorem momentFunctional_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_eq_zero_of_flat
    {a : ℕ → ℝ} {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N)
    (hzero : ∀ k < 2 * N + 1, a k = 0) :
    HTGeometry.momentFunctional a
      (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N) = 0 := by
  by_cases hR : xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N = 0
  · simp [hR]
  apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
  exact (Polynomial.natDegree_lt_iff_degree_lt hR).mpr
    (degree_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_lt_contact hA hAdeg)

/-- At flat contact the lower memory vanishes, leaving exactly the adaptive shear. -/
theorem coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_adaptiveShear_of_flat
    {a : ℕ → ℝ} {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N)
    (hzero : ∀ k < 2 * N + 1, a k = 0) :
    PowerSeries.coeff 2 (xiShiftedAdaptiveNullGaugeSourceSeries a A N) =
      ((2 * N + 1 : ℕ) : ℝ) *
        HTGeometry.momentFunctional a (xiShiftedBoundaryAdaptiveShearPolynomial A) := by
  rw [coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_shear_add_lowerResidual hA hAdeg,
    momentFunctional_xiShiftedAdaptiveNullGaugeLowerResidualPolynomial_eq_zero_of_flat
      hA hAdeg hzero,
    add_zero]

/-- **Corrected completed moving-flag source law.** For the actual shifted moment tower at every
positive mass, subtracting the explicit lower-contact memory from the full null-gauged coefficient
recovers the completed adaptive `P^sharp` packet.  No flatness premise is used. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_completedPacket
    {y : ℝ} (hy : 0 < y) {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N) :
    2 * PowerSeries.coeff 2
          (xiShiftedAdaptiveNullGaugeSourceSeries
            (fun k => (xiShiftedReciprocalMoment y k).re) A N) -
        2 * HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A N) =
      ((2 * N + 1 : ℕ) : ℝ) *
        xiShiftedCompletedMomentAggregate y 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket A)) := by
  rw [coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_shear_add_lowerResidual
      hA hAdeg,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hy]
  simp only [HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial]
  ring

/-- **Outgoing arithmetic producer for an admitted amplitude.** Keep the null amplitude chosen at
the original face, but evaluate the actual moment tower at any Euler-ray point.  The corrected
null-gauged coefficient is exactly the literal Archimedean plus Chebyshev-discrepancy completed
packet before reflection aggregation; no claim that the old flag remains flat is made. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_arch_add_discrepancy
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    2 * PowerSeries.coeff 2
          (xiShiftedAdaptiveNullGaugeSourceSeries
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) A (n + m)) -
        2 * HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
          (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        (xiShiftedBoundaryArchimedeanAggregate w 2
            (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
              (xiShiftedOddCrossingCoefficientPacket A)) +
          xiShiftedHankelBoundaryRadialDiscrepancy w 2
            (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
              (xiShiftedOddCrossingCoefficientPacket A))) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  rw [two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_completedPacket
      (sq_pos_of_pos (by linarith : 0 < w)) hA hAdeg,
    xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy hw]

/-- **Null-gauge coefficient producer.** At ordinary contact for a monic degree-`N` amplitude,
the second coefficient of the full gauged normal germ is `K` times the adjacent odd/even defect
shear, where `K=2N+1`. -/
theorem coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_adaptiveShear
    {a : ℕ → ℝ} {A : Polynomial ℝ} {N : ℕ}
    (hA : A.Monic) (hAdeg : A.natDegree = N)
    (hzero : ∀ k < 2 * N + 1, a k = 0) :
    PowerSeries.coeff 2 (xiShiftedAdaptiveNullGaugeSourceSeries a A N) =
      ((2 * N + 1 : ℕ) : ℝ) *
        (((2 * N + 1 : ℕ) : ℝ) * A.nextCoeff * a (2 * N + 1) +
          ((N + 1 : ℕ) : ℝ) * a (2 * N + 2)) := by
  have hA2deg : (A ^ (2 : ℕ)).natDegree = 2 * N := by
    rw [pow_two, hA.natDegree_mul hA, hAdeg]
    omega
  have hzero0 : HTGeometry.momentFunctional a (A ^ (2 : ℕ)) = 0 := by
    apply HTGeometry.momentFunctional_eq_zero_of_sequence_eq_zero_below hzero
    omega
  have hfirst : HTGeometry.momentFunctional a (A ^ (2 : ℕ) * X) = a (2 * N + 1) := by
    simpa using HTGeometry.momentFunctional_monic_first_contact
      (d := 1) hA hAdeg (by omega) hzero
  have hsecond : HTGeometry.momentFunctional a (A ^ (2 : ℕ) * X ^ (2 : ℕ)) =
      A.nextCoeff * 2 * a (2 * N + 1) + a (2 * N + 2) := by
    rw [momentFunctional_eq_two_top_of_sequence_eq_zero_below hzero]
    · by_cases hN : N = 0
      · have hAdeg0 : A.natDegree = 0 := hAdeg.trans hN
        have hAone := Polynomial.eq_one_of_monic_natDegree_zero hA hAdeg0
        subst A
        subst N
        norm_num [Polynomial.nextCoeff]
      · have hA2 : (A ^ (2 : ℕ)).Monic := hA.pow 2
        have hA2pos : 0 < (A ^ (2 : ℕ)).natDegree := by rw [hA2deg]; omega
        have hnext : (A ^ (2 : ℕ)).coeff (2 * N - 1) = 2 * A.nextCoeff := by
          rw [← hA2deg, ← Polynomial.nextCoeff_of_natDegree_pos hA2pos,
            hA.nextCoeff_pow]
          simp
        have hsub : 2 * N - 1 + 2 = 2 * N + 1 := by omega
        have htop : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).coeff (2 * N + 2) = 1 := by
          rw [Polynomial.coeff_mul_X_pow, ← hA2deg,
            hA2.coeff_natDegree]
        have hnextShift : (A ^ (2 : ℕ) * X ^ (2 : ℕ)).coeff (2 * N + 1) =
            2 * A.nextCoeff := by
          rw [← hsub, Polynomial.coeff_mul_X_pow, hnext]
        rw [hnextShift, htop]
        ring
    · calc
        (A ^ (2 : ℕ) * X ^ (2 : ℕ)).natDegree = 2 * N + 2 := by
          rw [(hA.pow 2).natDegree_mul (Polynomial.monic_X_pow 2),
            Polynomial.natDegree_pow, hAdeg, Polynomial.natDegree_X_pow]
        _ ≤ (2 * N + 1) + 1 := by omega
  have hg0 : PowerSeries.coeff 0
      (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ = 1 :=
    coeff_zero_inv_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg
  have hg1 : PowerSeries.coeff 1
      (xiShiftedAdaptiveNullRootGaugePolynomial A N : PowerSeries ℝ)⁻¹ = A.nextCoeff :=
    coeff_one_inv_xiShiftedAdaptiveNullRootGaugePolynomial hA hAdeg
  have hc0 : PowerSeries.coeff 0
      (HTGeometry.mobiusPadeContactSeries a A N) = 0 := by
    rw [HTGeometry.coeff_mobiusPadeContactSeries]
    norm_num [hzero0]
  have hc1 : PowerSeries.coeff 1
      (HTGeometry.mobiusPadeContactSeries a A N) =
        -((2 * N + 1 : ℕ) : ℝ) * a (2 * N + 1) := by
    rw [HTGeometry.coeff_mobiusPadeContactSeries]
    norm_num [hfirst, Nat.choose_one_right]
  have hchoose : Nat.choose (2 * N + 2) 2 = (2 * N + 1) * (N + 1) := by
    rw [Nat.choose_two_right]
    rw [show 2 * N + 2 = 2 * (N + 1) by omega,
      show 2 * (N + 1) - 1 = 2 * N + 1 by omega]
    rw [show 2 * (N + 1) * (2 * N + 1) =
      2 * ((N + 1) * (2 * N + 1)) by ring,
      Nat.mul_div_right _ (by omega : 0 < 2)]
    exact Nat.mul_comm _ _
  have hc2 : PowerSeries.coeff 2
      (HTGeometry.mobiusPadeContactSeries a A N) =
        ((2 * N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) *
          (A.nextCoeff * 2 * a (2 * N + 1) + a (2 * N + 2)) := by
    rw [HTGeometry.coeff_mobiusPadeContactSeries, hsecond, hchoose]
    push_cast
    ring
  rw [xiShiftedAdaptiveNullGaugeSourceSeries, powerSeries_coeff_two_mul]
  rw [hg0, hg1, hc0, hc1, hc2]
  push_cast
  ring

/-- **Admission-sensitive bilinear landing.** For the amplitude selected by an actual flat null
flag, the second null-gauged source coefficient is the odd-contact factor `2N+1` times the even
adaptive shear.  The null polynomial and its parity lift are arguments of the source series, not
chosen after aggregation. -/
theorem coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_nullAmplitude_eq_shear
    {y : ℝ} {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    PowerSeries.coeff 2
        (xiShiftedAdaptiveNullGaugeSourceSeries
          (xiShiftedHankelBoundaryPadeDefect y c) A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        HTGeometry.momentFunctional
          (fun k => (xiShiftedReciprocalMoment y k).re)
          (xiShiftedBoundaryAdaptiveShearPolynomial A) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  have hP : P.Monic := HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast
  have hPdeg : P.natDegree = n :=
    HTGeometry.finiteHankelNullMonicPolynomial_natDegree c hlast
  have hA : A.Monic := hP.mul (Polynomial.monic_X_pow m)
  have hAdeg : A.natDegree = n + m := by
    dsimp only [A]
    rw [hP.natDegree_mul (Polynomial.monic_X_pow m), hPdeg,
      Polynomial.natDegree_X_pow]
  have hzero' : ∀ k < 2 * (n + m) + 1,
      xiShiftedHankelBoundaryPadeDefect y c k = 0 := by
    intro k hk
    apply hzero k
    omega
  have hcoeff :=
    coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_adaptiveShear
      hA hAdeg hzero'
  have hclass := xiShiftedHankelBoundary_adaptiveShear_eq_adjacentDefects
    c hlast hzero
  dsimp only at hclass
  dsimp only [P, A] at hcoeff ⊢
  rw [hcoeff, hclass,
    nextCoeff_mul_X_pow_of_monic
      (HTGeometry.finiteHankelNullMonicPolynomial_monic c hlast) m]
  rw [show 2 * (n + m) + 1 = 2 * n + (2 * m + 1) by omega,
    show 2 * (n + m) + 2 = 2 * n + (2 * m + 1) + 1 by omega]

/-- **Completed adaptive `P^sharp` source law.** Twice the second coefficient of the full
null-gauged source series is exactly the odd-contact factor times the completed adaptive successor
packet.  This is the requested mixed-amplitude producer, before source channels are aggregated. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_completedPacket
    {y : ℝ} (hy : 0 < y) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect y c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    2 * PowerSeries.coeff 2
        (xiShiftedAdaptiveNullGaugeSourceSeries
          (xiShiftedHankelBoundaryPadeDefect y c) A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        xiShiftedCompletedMomentAggregate y 2
          (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
            (xiShiftedOddCrossingCoefficientPacket A)) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  rw [coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_nullAmplitude_eq_shear
      c hlast hzero,
    xiShiftedCompletedMomentAggregate_adaptiveOddPacket_eq_two_shear hy]
  simp only [HTGeometry.momentInner_def, xiShiftedBoundaryAdaptiveShearPolynomial]
  ring

/-- **Literal pre-aggregation arithmetic source law.** On the Euler ray, the same admitted
null-gauge coefficient is exactly the completed archimedean plus Chebyshev-discrepancy adaptive
`P^sharp` packet.  No divisor orientation map or fixed linear reporter occurs. -/
theorem two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_arch_add_discrepancy
    {w : ℝ} (hw : 1 / 2 < w) {n m : ℕ} (c : Fin (n + 1) → ℝ)
    (hlast : c (Fin.last n) ≠ 0)
    (hzero : ∀ k < 2 * n + (2 * m + 1),
      xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c k = 0) :
    let P := HTGeometry.finiteHankelNullMonicPolynomial c
    let A := P * X ^ m
    2 * PowerSeries.coeff 2
        (xiShiftedAdaptiveNullGaugeSourceSeries
          (xiShiftedHankelBoundaryPadeDefect (w ^ (2 : ℕ)) c) A (n + m)) =
      ((2 * (n + m) + 1 : ℕ) : ℝ) *
        (xiShiftedBoundaryArchimedeanAggregate w 2
            (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
              (xiShiftedOddCrossingCoefficientPacket A)) +
          xiShiftedHankelBoundaryRadialDiscrepancy w 2
            (xiShiftedBoundaryAdaptiveMidpointCoefficients 1
              (xiShiftedOddCrossingCoefficientPacket A))) := by
  dsimp only
  let P := HTGeometry.finiteHankelNullMonicPolynomial c
  let A := P * X ^ m
  rw [two_mul_coeff_two_xiShiftedAdaptiveNullGaugeSourceSeries_eq_completedPacket
      (sq_pos_of_pos (by linarith : 0 < w)) c hlast hzero,
    xiShiftedCompletedMomentAggregate_sq_eq_boundaryCompletedAggregate
      (by linarith : 0 < w),
    xiShiftedBoundaryCompletedAggregate_eq_archimedean_add_radialDiscrepancy hw]

/-- **Corrected-source crossing obstruction.** Every genuine Hankel crossing forces the actual
null-gauged source coefficient, after subtracting its explicit lower-contact flag memory, to be
strictly negative at a later Euler aperture.  This is the source-side form of the obstruction:
the old flat flag is not assumed to remain flat downstream. -/
theorem exists_xiShiftedAdaptiveNullGaugeCorrectedSource_neg_on_outgoingRay_of_genuine_crossing
    {y : ℝ} (hyquarter : 1 / 4 < y) (hymax : y < 41 / 2)
    {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (xiShiftedMomentHankelMatrix y n).PosDef)
    (hc : xiShiftedMomentHankelMatrix y (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0)
    (hright : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (xiShiftedMomentHankelMatrix (y + u) (n + 1)).PosSemidef)
    (hleft : ∀ᶠ u in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ¬ (xiShiftedMomentHankelMatrix (y - u) (n + 1)).PosSemidef) :
    ∃ m : ℕ, ∃ w : ℝ,
      1 / 2 < w ∧ y < w ^ (2 : ℕ) ∧
      let P := HTGeometry.finiteHankelNullMonicPolynomial c
      let A := P * X ^ m
      2 * PowerSeries.coeff 2
            (xiShiftedAdaptiveNullGaugeSourceSeries
              (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re) A (n + m)) -
          2 * HTGeometry.momentFunctional
            (fun k => (xiShiftedReciprocalMoment (w ^ (2 : ℕ)) k).re)
            (xiShiftedAdaptiveNullGaugeLowerResidualPolynomial A (n + m)) < 0 := by
  obtain ⟨m, w, hw, hyw, hsource⟩ :=
    exists_xiShiftedCompletedAdaptiveSource_neg_on_outgoingRay_of_genuine_crossing
      hyquarter hymax c hhead hc hlast hright hleft
  refine ⟨m, w, hw, hyw, ?_⟩
  dsimp only
  have heq :=
    two_mul_coeff_two_xiShiftedAdaptiveNullGaugeMomentSourceSeries_sub_lowerResidual_eq_arch_add_discrepancy
      hw c hlast (m := m)
  dsimp only at heq hsource
  rw [heq]
  exact mul_neg_of_pos_of_neg (by positivity) hsource

end

end RHTower
