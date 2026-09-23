import GaloisForLFunctions.RHTower.VisibleCoprimeMellinSymbol
import GaloisForLFunctions.RHTower.DivisorStationaryKernelPositivity
import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.PositiveDiagonalCompletionDirichletJet
import GaloisForLFunctions.HTGeometry.RealBaseCpowPolar
import GaloisForLFunctions.RHTower.BurnolPrimeLogSummability

/-!
# Infinite divisor-stationary Mellin symbols and critical energy

This leaf closes the infinite-series part of the divisor-stationary kernel law `(V18)`.  For

`H_c(a,b) = sum_{d | a, d | b} c(d)`

it proves absolute summability on the natural convergence data and the exact identity

`sum_{a,b >= 1} H_c(a,b) a^(-s) b^(-t) = zeta(s) zeta(t) C(s+t)`.

For nonzero nonnegative coefficients with finite critical energy, it identifies `C(sigma0)` with
the positive zeroth logarithmic moment and proves strict positivity.

The file also audits the card's claimed boundary step `(V21)`.  Finite critical mass alone does
not imply a finite second logarithmic moment: the explicit coefficients
`c(n) = 1 / log(n)^(2 : ℕ)` have summable `c(n)/n` but divergent
`c(n) log(n)^(2 : ℕ) / n`.  The final closed theorem records that obstruction, so the unqualified paper
boundary inference cannot be formalized as stated.
-/

open Complex Real Set Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- A positive Dirichlet atom restricted to multiples of `d`. -/
def positiveDivisibleDirichletTerm (d : ℕ+) (s : ℂ) (a : ℕ+) : ℂ :=
  {a : ℕ+ | d ∣ a}.indicator (positiveDirichletTerm s) a

theorem summable_positiveDivisibleDirichletTerm
    (d : ℕ+) {s : ℂ} (hs : 1 < s.re) :
    Summable (positiveDivisibleDirichletTerm d s) := by
  exact (summable_positiveDirichletTerm hs).indicator {a : ℕ+ | d ∣ a}

theorem positiveDirichletTerm_mul
    (s : ℂ) (a d : ℕ+) :
    positiveDirichletTerm s (a * d) =
      positiveDirichletTerm s a * positiveDirichletTerm s d := by
  have ha : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hd : (0 : ℝ) ≤ (d : ℝ) := by positivity
  unfold positiveDirichletTerm
  change ((((a * d : ℕ+) : ℕ) : ℂ)) ^ (-s) =
    (((a : ℕ) : ℂ)) ^ (-s) * (((d : ℕ) : ℂ)) ^ (-s)
  have hcast : ((((a * d : ℕ+) : ℕ) : ℂ)) =
      (((a : ℕ) : ℂ)) * (((d : ℕ) : ℂ)) := by
    push_cast
    rfl
  rw [hcast]
  simpa using Complex.mul_cpow_ofReal_nonneg ha hd (-s)

theorem positiveDirichletTerm_mul_add
    (s t : ℂ) (d : ℕ+) :
    positiveDirichletTerm s d * positiveDirichletTerm t d =
      positiveDirichletTerm (s + t) d := by
  have hdne : (((d : ℕ) : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr d.ne_zero
  unfold positiveDirichletTerm
  rw [← Complex.cpow_add _ _ hdne]
  congr 1
  ring

theorem tsum_positiveDivisibleDirichletTerm_eq
    (d : ℕ+) (s : ℂ) (hs : 1 < s.re) :
    (∑' a : ℕ+, positiveDivisibleDirichletTerm d s a) =
      positiveDirichletTerm s d * riemannZeta s := by
  change (∑' a : ℕ+, {a : ℕ+ | d ∣ a}.indicator
    (positiveDirichletTerm s) a) = _
  rw [← tsum_subtype]
  calc
    (∑' a : {a : ℕ+ // d ∣ a}, positiveDirichletTerm s a.1) =
        ∑' k : ℕ+, positiveDirichletTerm s (d * k) := by
      exact (Equiv.tsum_eq (pnatMulEquivDvd d)
        (fun a : {a : ℕ+ // d ∣ a} => positiveDirichletTerm s a.1)).symm
    _ = ∑' k : ℕ+,
        positiveDirichletTerm s d * positiveDirichletTerm s k := by
      apply tsum_congr
      intro k
      rw [positiveDirichletTerm_mul]
    _ = positiveDirichletTerm s d *
        (∑' k : ℕ+, positiveDirichletTerm s k) := tsum_mul_left
    _ = positiveDirichletTerm s d * riemannZeta s := by
      rw [tsum_positiveDirichletTerm_eq_riemannZeta s hs]

theorem tsum_norm_positiveDivisibleDirichletTerm_eq
    (d : ℕ+) (s : ℂ) :
    (∑' a : ℕ+, ‖positiveDivisibleDirichletTerm d s a‖) =
      ‖positiveDirichletTerm s d‖ *
        (∑' a : ℕ+, ‖positiveDirichletTerm s a‖) := by
  calc
    (∑' a : ℕ+, ‖positiveDivisibleDirichletTerm d s a‖) =
        ∑' a : ℕ+, {a : ℕ+ | d ∣ a}.indicator
          (fun a => ‖positiveDirichletTerm s a‖) a := by
      apply tsum_congr
      intro a
      by_cases h : d ∣ a <;> simp [positiveDivisibleDirichletTerm, Set.indicator, h]
    _ = ∑' a : {a : ℕ+ // d ∣ a}, ‖positiveDirichletTerm s a.1‖ := by
      exact (tsum_subtype {a : ℕ+ | d ∣ a}
        (fun a => ‖positiveDirichletTerm s a‖)).symm
    _ = ∑' k : ℕ+, ‖positiveDirichletTerm s (d * k)‖ := by
      exact (Equiv.tsum_eq (pnatMulEquivDvd d)
        (fun a : {a : ℕ+ // d ∣ a} => ‖positiveDirichletTerm s a.1‖)).symm
    _ = ∑' k : ℕ+,
        ‖positiveDirichletTerm s d‖ * ‖positiveDirichletTerm s k‖ := by
      apply tsum_congr
      intro k
      rw [positiveDirichletTerm_mul, norm_mul]
    _ = ‖positiveDirichletTerm s d‖ *
        (∑' k : ℕ+, ‖positiveDirichletTerm s k‖) := tsum_mul_left

/-- Absolute-convergence data for the divisor-stationary Mellin identity. -/
structure DivisorStationaryMellinData
    (c : ℕ+ → ℂ) (s t : ℂ) where
  s_re_gt_one : 1 < s.re
  t_re_gt_one : 1 < t.re
  coefficientSummable : Summable
    (fun d : ℕ+ => c d * positiveDirichletTerm (s + t) d)

/-- One coefficient restricted to common divisors of a positive pair. -/
noncomputable def commonDivisorCoefficient
    (c : ℕ+ → ℂ) (a b d : ℕ+) : ℂ := by
  classical
  exact if d ∣ a ∧ d ∣ b then c d else 0

/-- Infinite divisor-stationary kernel `sum_{d | gcd(a,b)} c(d)`. -/
def divisorStationaryKernel (c : ℕ+ → ℂ) (a b : ℕ+) : ℂ :=
  ∑' d : ℕ+, commonDivisorCoefficient c a b d

/-- The apparently infinite definition of the kernel is the literal finite
sum over common positive divisors. -/
theorem divisorStationaryKernel_eq_sum_commonDivisors
    (c : ℕ+ → ℂ) (a b : ℕ+) :
    divisorStationaryKernel c a b =
      ∑ d ∈ Finset.Icc (1 : ℕ+) a,
        commonDivisorCoefficient c a b d := by
  classical
  unfold divisorStationaryKernel
  apply tsum_eq_sum
  intro d hd
  by_cases hcommon : d ∣ a ∧ d ∣ b
  · exfalso
    apply hd
    exact Finset.mem_Icc.mpr
      ⟨(show (1 : ℕ+) ≤ d from one_le), PNat.le_of_dvd hcommon.1⟩
  · simp [commonDivisorCoefficient, hcommon]

/-- Dirichlet series of the stationary divisor coefficients. -/
def divisorStationaryCoefficientSeries (c : ℕ+ → ℂ) (u : ℂ) : ℂ :=
  ∑' d : ℕ+, c d * positiveDirichletTerm u d

/-- Mellin atom of the infinite divisor-stationary kernel. -/
def divisorStationaryMellinTerm
    (c : ℕ+ → ℂ) (s t : ℂ) (p : ℕ+ × ℕ+) : ℂ :=
  divisorStationaryKernel c p.1 p.2 *
    positiveDirichletTerm s p.1 * positiveDirichletTerm t p.2

/-- Two-variable Mellin symbol of the infinite divisor-stationary kernel. -/
def divisorStationaryMellinSymbol
    (c : ℕ+ → ℂ) (s t : ℂ) : ℂ :=
  ∑' p : ℕ+ × ℕ+, divisorStationaryMellinTerm c s t p

private def divisorStationaryIncidenceMellinTerm
    (c : ℕ+ → ℂ) (s t : ℂ) (d : ℕ+) (p : ℕ+ × ℕ+) : ℂ :=
  c d * (positiveDivisibleDirichletTerm d s p.1 *
    positiveDivisibleDirichletTerm d t p.2)

private theorem summable_divisorStationaryIncidenceMellinTerm_row
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t)
    (d : ℕ+) :
    Summable (divisorStationaryIncidenceMellinTerm c s t d) := by
  have hs := summable_positiveDivisibleDirichletTerm d D.s_re_gt_one
  have ht := summable_positiveDivisibleDirichletTerm d D.t_re_gt_one
  have hpair : Summable (fun p : ℕ+ × ℕ+ =>
      positiveDivisibleDirichletTerm d s p.1 *
        positiveDivisibleDirichletTerm d t p.2) := by
    apply Summable.of_norm
    simpa only [norm_mul] using
      hs.norm.mul_of_nonneg ht.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  exact hpair.mul_left (c d)

private theorem tsum_divisorStationaryIncidenceMellinTerm_row
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t)
    (d : ℕ+) :
    (∑' p : ℕ+ × ℕ+, divisorStationaryIncidenceMellinTerm c s t d p) =
      (c d * positiveDirichletTerm (s + t) d) *
        (riemannZeta s * riemannZeta t) := by
  have hs := summable_positiveDivisibleDirichletTerm d D.s_re_gt_one
  have ht := summable_positiveDivisibleDirichletTerm d D.t_re_gt_one
  have hpair : Summable (fun p : ℕ+ × ℕ+ =>
      positiveDivisibleDirichletTerm d s p.1 *
        positiveDivisibleDirichletTerm d t p.2) := by
    apply Summable.of_norm
    simpa only [norm_mul] using
      hs.norm.mul_of_nonneg ht.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  calc
    (∑' p : ℕ+ × ℕ+, divisorStationaryIncidenceMellinTerm c s t d p) =
        c d * ∑' p : ℕ+ × ℕ+,
          positiveDivisibleDirichletTerm d s p.1 *
            positiveDivisibleDirichletTerm d t p.2 := by
      rw [← tsum_mul_left]
      rfl
    _ = c d * ((∑' a : ℕ+, positiveDivisibleDirichletTerm d s a) *
        (∑' b : ℕ+, positiveDivisibleDirichletTerm d t b)) := by
      rw [hs.tsum_mul_tsum ht hpair]
    _ = c d * (positiveDirichletTerm s d * riemannZeta s *
        (positiveDirichletTerm t d * riemannZeta t)) := by
      rw [tsum_positiveDivisibleDirichletTerm_eq d s D.s_re_gt_one,
        tsum_positiveDivisibleDirichletTerm_eq d t D.t_re_gt_one]
    _ = (c d * positiveDirichletTerm (s + t) d) *
        (riemannZeta s * riemannZeta t) := by
      rw [← positiveDirichletTerm_mul_add s t d]
      ring

private theorem tsum_norm_divisorStationaryIncidenceMellinTerm_row
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t)
    (d : ℕ+) :
    (∑' p : ℕ+ × ℕ+, ‖divisorStationaryIncidenceMellinTerm c s t d p‖) =
      ‖c d * positiveDirichletTerm (s + t) d‖ *
        ((∑' a : ℕ+, ‖positiveDirichletTerm s a‖) *
          (∑' b : ℕ+, ‖positiveDirichletTerm t b‖)) := by
  have hs := (summable_positiveDivisibleDirichletTerm d D.s_re_gt_one).norm
  have ht := (summable_positiveDivisibleDirichletTerm d D.t_re_gt_one).norm
  have hpair : Summable (fun p : ℕ+ × ℕ+ =>
      ‖positiveDivisibleDirichletTerm d s p.1‖ *
        ‖positiveDivisibleDirichletTerm d t p.2‖) :=
    hs.mul_of_nonneg ht (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  calc
    (∑' p : ℕ+ × ℕ+, ‖divisorStationaryIncidenceMellinTerm c s t d p‖) =
        ‖c d‖ * ∑' p : ℕ+ × ℕ+,
          ‖positiveDivisibleDirichletTerm d s p.1‖ *
            ‖positiveDivisibleDirichletTerm d t p.2‖ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro p
      simp [divisorStationaryIncidenceMellinTerm]
    _ = ‖c d‖ * ((∑' a : ℕ+, ‖positiveDivisibleDirichletTerm d s a‖) *
        (∑' b : ℕ+, ‖positiveDivisibleDirichletTerm d t b‖)) := by
      rw [hs.tsum_mul_tsum ht hpair]
    _ = ‖c d‖ *
        (‖positiveDirichletTerm s d‖ *
            (∑' a : ℕ+, ‖positiveDirichletTerm s a‖) *
          (‖positiveDirichletTerm t d‖ *
            (∑' b : ℕ+, ‖positiveDirichletTerm t b‖))) := by
      rw [tsum_norm_positiveDivisibleDirichletTerm_eq,
        tsum_norm_positiveDivisibleDirichletTerm_eq]
    _ = ‖c d * positiveDirichletTerm (s + t) d‖ *
        ((∑' a : ℕ+, ‖positiveDirichletTerm s a‖) *
          (∑' b : ℕ+, ‖positiveDirichletTerm t b‖)) := by
      rw [norm_mul, ← positiveDirichletTerm_mul_add s t d, norm_mul]
      ring

private theorem summable_divisorStationaryIncidenceMellinTerm
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t) :
    Summable (Function.uncurry (divisorStationaryIncidenceMellinTerm c s t)) := by
  apply Summable.of_norm
  refine (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2 ⟨?_, ?_⟩
  · exact fun d => (summable_divisorStationaryIncidenceMellinTerm_row D d).norm
  · let Z : ℝ :=
      (∑' a : ℕ+, ‖positiveDirichletTerm s a‖) *
        (∑' b : ℕ+, ‖positiveDirichletTerm t b‖)
    have hc := D.coefficientSummable.norm.mul_right Z
    refine hc.congr (fun d => ?_)
    exact (tsum_norm_divisorStationaryIncidenceMellinTerm_row D d).symm

private theorem divisorStationaryMellinTerm_eq_incidence_tsum
    (c : ℕ+ → ℂ) (s t : ℂ) (p : ℕ+ × ℕ+) :
    divisorStationaryMellinTerm c s t p =
      ∑' d : ℕ+, divisorStationaryIncidenceMellinTerm c s t d p := by
  unfold divisorStationaryMellinTerm divisorStationaryKernel
  rw [← tsum_mul_right, ← tsum_mul_right]
  apply tsum_congr
  intro d
  by_cases hda : d ∣ p.1
  · by_cases hdb : d ∣ p.2
    · simp [commonDivisorCoefficient, divisorStationaryIncidenceMellinTerm,
        positiveDivisibleDirichletTerm, Set.indicator, hda, hdb]
      ring
    · simp [commonDivisorCoefficient, divisorStationaryIncidenceMellinTerm,
        positiveDivisibleDirichletTerm, Set.indicator, hda, hdb]
  · simp [commonDivisorCoefficient, divisorStationaryIncidenceMellinTerm,
      positiveDivisibleDirichletTerm, Set.indicator, hda]

/-- The infinite divisor-stationary Mellin family is absolutely summable on
the domain carried by `D`. -/
theorem summable_divisorStationaryMellinTerm
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t) :
    Summable (divisorStationaryMellinTerm c s t) := by
  have h := summable_divisorStationaryIncidenceMellinTerm D
  have hswap : Summable (fun q : (ℕ+ × ℕ+) × ℕ+ =>
      divisorStationaryIncidenceMellinTerm c s t q.2 q.1) :=
    ((Equiv.prodComm (ℕ+ × ℕ+) ℕ+).summable_iff).2 h
  exact hswap.prod.congr (fun p =>
    (divisorStationaryMellinTerm_eq_incidence_tsum c s t p).symm)

/-- Exact infinite divisor-stationary Mellin law `(V18)`. -/
theorem divisorStationaryMellinSymbol_eq
    {c : ℕ+ → ℂ} {s t : ℂ} (D : DivisorStationaryMellinData c s t) :
    divisorStationaryMellinSymbol c s t =
      riemannZeta s * riemannZeta t *
        divisorStationaryCoefficientSeries c (s + t) := by
  have h := summable_divisorStationaryIncidenceMellinTerm D
  unfold divisorStationaryMellinSymbol divisorStationaryCoefficientSeries
  calc
    (∑' p : ℕ+ × ℕ+, divisorStationaryMellinTerm c s t p) =
        ∑' p : ℕ+ × ℕ+, ∑' d : ℕ+,
          divisorStationaryIncidenceMellinTerm c s t d p := by
      apply tsum_congr
      exact divisorStationaryMellinTerm_eq_incidence_tsum c s t
    _ = ∑' d : ℕ+, ∑' p : ℕ+ × ℕ+,
          divisorStationaryIncidenceMellinTerm c s t d p := h.tsum_comm
    _ = ∑' d : ℕ+, (c d * positiveDirichletTerm (s + t) d) *
          (riemannZeta s * riemannZeta t) := by
      apply tsum_congr
      exact tsum_divisorStationaryIncidenceMellinTerm_row D
    _ = (∑' d : ℕ+, c d * positiveDirichletTerm (s + t) d) *
          (riemannZeta s * riemannZeta t) := by
      rw [tsum_mul_right]
    _ = riemannZeta s * riemannZeta t *
          (∑' d : ℕ+, c d * positiveDirichletTerm (s + t) d) := by ring

/-- Positive diagonal data viewed as complex divisor-stationary coefficients. -/
def positiveDiagonalDivisorCoefficient
    {sigma0 : ℝ} (D : PositiveDiagonalCompletionDirichletData sigma0)
    (d : ℕ+) : ℂ := D.coeff d.1

private theorem positiveDirichletTerm_eq_exp_log (s : ℂ) (d : ℕ+) :
    positiveDirichletTerm s d =
      Complex.exp (-(s * (Real.log (d : ℝ) : ℂ))) := by
  have hd : 0 < (d : ℝ) := by exact_mod_cast d.property
  unfold positiveDirichletTerm
  change (((d : ℝ) : ℂ) ^ (-s)) = _
  rw [ofReal_cpow_eq_exp hd]
  congr 1
  ring

/-- The general Dirichlet series used by the positive-completion leaf is
literally the divisor coefficient series in `(V18)`. -/
theorem positiveDiagonal_series_eq_divisorStationaryCoefficientSeries
    {sigma0 : ℝ} (D : PositiveDiagonalCompletionDirichletData sigma0)
    (s : ℂ) :
    D.series s =
      divisorStationaryCoefficientSeries
        (positiveDiagonalDivisorCoefficient D) s := by
  unfold PositiveDiagonalCompletionDirichletData.series gdSeries
  unfold divisorStationaryCoefficientSeries positiveDiagonalDivisorCoefficient
  apply tsum_congr
  intro d
  rw [positiveDirichletTerm_eq_exp_log]
  unfold PositiveDiagonalCompletionDirichletData.positiveCoeff
  unfold positiveDirichletLogFrequency
  rfl

/-- At the finite critical abscissa, the divisor coefficient series is the
nonnegative zeroth frequency moment. -/
theorem positiveDiagonal_divisorStationaryCoefficientSeries_critical_eq
    {sigma0 : ℝ} (D : PositiveDiagonalCompletionDirichletData sigma0) :
    divisorStationaryCoefficientSeries
        (positiveDiagonalDivisorCoefficient D) (sigma0 : ℂ) =
      ((gdMoment D.positiveCoeff positiveDirichletLogFrequency
        sigma0 0 : ℝ) : ℂ) := by
  have hcx := Complex.ofRealCLM.hasSum D.summable_at.hasSum
  calc
    divisorStationaryCoefficientSeries
        (positiveDiagonalDivisorCoefficient D) (sigma0 : ℂ) =
        ∑' d : ℕ+,
          ((gdTwistTerm D.positiveCoeff positiveDirichletLogFrequency
            sigma0 0 d : ℝ) : ℂ) := by
      unfold divisorStationaryCoefficientSeries positiveDiagonalDivisorCoefficient
      apply tsum_congr
      intro d
      rw [positiveDirichletTerm_eq_exp_log]
      unfold gdTwistTerm PositiveDiagonalCompletionDirichletData.positiveCoeff
      unfold positiveDirichletLogFrequency
      rw [pow_zero, mul_one, Complex.ofReal_mul, Complex.ofReal_exp]
      congr 2
      push_cast
      rfl
    _ = ((gdMoment D.positiveCoeff positiveDirichletLogFrequency
        sigma0 0 : ℝ) : ℂ) := by
      rw [gdMoment]
      exact hcx.tsum_eq

/-- Finite critical energy of a nonzero positive divisor-stationary kernel is
strictly positive, the critical-energy conclusion of `(V18)`. -/
theorem re_positiveDiagonal_divisorStationaryCoefficientSeries_critical_pos
    {sigma0 : ℝ} (D : PositiveDiagonalCompletionDirichletData sigma0) :
    0 < (divisorStationaryCoefficientSeries
      (positiveDiagonalDivisorCoefficient D) (sigma0 : ℂ)).re := by
  rw [positiveDiagonal_divisorStationaryCoefficientSeries_critical_eq]
  exact D.criticalValue_pos

/-! ## The claimed critical-boundary derivative does not follow from finite energy -/

/-- Nonnegative coefficients with finite critical mass but divergent second
logarithmic moment. -/
def v21BoundaryCounterexampleCoeff (n : ℕ) : ℝ :=
  1 / Real.log (n : ℝ) ^ 2

private theorem v21BoundaryCounterexampleCoeff_nonneg (n : ℕ) :
    0 ≤ v21BoundaryCounterexampleCoeff n := by
  unfold v21BoundaryCounterexampleCoeff
  positivity

private theorem v21BoundaryCounterexample_criticalTerm_eq
    (n : positiveDirichletCoordinate) :
    gdTwistTerm
        (fun k : positiveDirichletCoordinate =>
          v21BoundaryCounterexampleCoeff k.1)
        positiveDirichletLogFrequency 1 0 n =
      1 / ((n.1 : ℝ) * Real.log (n.1 : ℝ) ^ 2) := by
  have hn : 0 < (n.1 : ℝ) := by exact_mod_cast n.2
  unfold gdTwistTerm v21BoundaryCounterexampleCoeff
  unfold positiveDirichletLogFrequency
  rw [pow_zero, mul_one, one_mul, Real.exp_neg, Real.exp_log hn]
  ring

/-- A closed positive Dirichlet datum satisfying exactly finite critical
energy at abscissa `1`. -/
def v21BoundaryCounterexampleData :
    PositiveDiagonalCompletionDirichletData 1 where
  coeff := v21BoundaryCounterexampleCoeff
  coeff_nonneg := fun n hn => v21BoundaryCounterexampleCoeff_nonneg n
  summable_at := by
    have h : Summable (fun n : positiveDirichletCoordinate =>
        1 / ((n.1 : ℝ) * Real.log (n.1 : ℝ) ^ 2)) :=
      burnolSummable_one_div_mul_log_sq.comp_injective Subtype.val_injective
    exact h.congr (fun n => (v21BoundaryCounterexample_criticalTerm_eq n).symm)
  positiveAtom := by
    refine ⟨2, by norm_num, ?_⟩
    unfold v21BoundaryCounterexampleCoeff
    have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity

private theorem v21BoundaryCounterexample_secondTerm_eq_shiftedHarmonic
    (n : ℕ) :
    gdTwistTerm v21BoundaryCounterexampleData.positiveCoeff
        positiveDirichletLogFrequency 1 2
        ⟨n + 2, by omega⟩ =
      1 / ((n + 2 : ℕ) : ℝ) := by
  have hn : (1 : ℝ) < (n + 2 : ℕ) := by
    exact_mod_cast (show 1 < n + 2 by omega)
  have hn0 : 0 < ((n + 2 : ℕ) : ℝ) := lt_trans zero_lt_one hn
  have hlog : Real.log ((n + 2 : ℕ) : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hn)
  unfold gdTwistTerm PositiveDiagonalCompletionDirichletData.positiveCoeff
  unfold v21BoundaryCounterexampleData v21BoundaryCounterexampleCoeff
  unfold positiveDirichletLogFrequency
  rw [one_mul, Real.exp_neg, Real.exp_log hn0]
  field_simp

/-- The second logarithmic moment of the finite-critical-energy example
diverges. -/
theorem not_summable_v21BoundaryCounterexample_secondMoment :
    ¬ Summable (gdTwistTerm v21BoundaryCounterexampleData.positiveCoeff
      positiveDirichletLogFrequency 1 2) := by
  intro hsum
  let e : ℕ → positiveDirichletCoordinate := fun n => ⟨n + 2, by omega⟩
  have he : Function.Injective e := by
    intro a b hab
    exact Nat.add_right_cancel (congrArg Subtype.val hab)
  have hsub := hsum.comp_injective he
  have hshift : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) :=
    hsub.congr v21BoundaryCounterexample_secondTerm_eq_shiftedHarmonic
  have hall : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    exact (summable_nat_add_iff 2).mp (by simpa using hshift)
  exact Real.not_summable_one_div_natCast hall

/-- Closed counterexample to the paper card's unqualified V21 boundary
inference: critical mass is finite while the second logarithmic moment is not. -/
theorem finiteCriticalEnergy_not_imply_secondLogMoment :
    Summable (gdTwistTerm v21BoundaryCounterexampleData.positiveCoeff
        positiveDirichletLogFrequency 1 0) ∧
      ¬ Summable (gdTwistTerm v21BoundaryCounterexampleData.positiveCoeff
        positiveDirichletLogFrequency 1 2) := by
  exact ⟨v21BoundaryCounterexampleData.summable_at,
    not_summable_v21BoundaryCounterexample_secondMoment⟩

end

end RHTower
