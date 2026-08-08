import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.RHTower.HeatApertureEchoLadder

/-!
# Heat-Aperture Echo Tomography

This module turns the strict heat-aperture echo ladder into two exact coefficient-recovery
procedures. The integer ladder peels the shifted zeta Dirichlet series one coefficient at a
time. The canonical Euler-log ladder does the same on the prime-power support and recovers
`Λ(N) / log N`, hence `1 / (r + 1)` at `N = p^(r+1)` and zero away from prime powers.

Only analytic `LSeries` convergence and limits are used; no numerical computation enters the
formalization.
-/

namespace GaloisForLFunctions

open Complex Filter Topology LSeries

noncomputable section

/-- Coefficients `n^(conj s - 1)` of the integer echo moment sequence. -/
def heatApertureIntegerCoeff (s : ℂ) : ℕ → ℂ :=
  lseriesPowerTwistCoeff (1 : ℕ → ℂ) ((starRingEnd ℂ) s - 1)

/-- The neutral atoms `n=0,1` deleted from the integer echo moment sequence. -/
def heatApertureIntegerTailCoeff (s : ℂ) : ℕ → ℂ :=
  lseriesPeeledCoeff (heatApertureIntegerCoeff s) 1

/-- Integer moment carried by the normalized strict echo tail. -/
def heatApertureIntegerMoment (s : ℂ) (k : ℕ) : ℂ :=
  LSeries (heatApertureIntegerTailCoeff s) (k : ℂ)

private theorem heatApertureIntegerCoeff_summable
    {s : ℂ} (hshi : s.re < 1) {k : ℕ} (hk : 1 ≤ k) :
    LSeriesSummable (heatApertureIntegerCoeff s) (k : ℂ) := by
  rw [heatApertureIntegerCoeff, LSeriesSummable_powerTwist]
  apply LSeriesSummable_one_iff.mpr
  simp only [Complex.sub_re, Complex.natCast_re, Complex.conj_re, Complex.one_re]
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  linarith

/-- The integer echo moments are exactly the forward zeta tail minus its neutral atom. -/
theorem heatApertureIntegerMoment_eq_forward_sub_one
    {s : ℂ} (hshi : s.re < 1) {k : ℕ} (hk : 1 ≤ k) :
    heatApertureIntegerMoment s k = heatApertureForwardZetaValue s k - 1 := by
  have hs := heatApertureIntegerCoeff_summable hshi hk
  rw [heatApertureIntegerMoment, heatApertureIntegerTailCoeff,
    LSeries_peeled_eq_sub_sum hs 1]
  rw [heatApertureIntegerCoeff, LSeries_powerTwist,
    LSeries_one_eq_riemannZeta]
  · rw [show (k : ℂ) - ((starRingEnd ℂ) s - 1) =
        1 - (starRingEnd ℂ) s + k by ring]
    norm_num [heatApertureForwardZetaValue, Finset.sum_range_succ,
      LSeries.term, lseriesPowerTwistCoeff]
  · simp only [Complex.sub_re, Complex.natCast_re, Complex.conj_re, Complex.one_re]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith

/-- Delete every integer coefficient strictly before `N`. -/
def heatApertureIntegerPeeledCoeff (s : ℂ) (N : ℕ) : ℕ → ℂ :=
  lseriesPeeledCoeff (heatApertureIntegerCoeff s) (N - 1)

/-- Peeled integer echo value at a real depth. -/
def heatApertureIntegerPeeledValue (s : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  LSeries (heatApertureIntegerPeeledCoeff s N) (x : ℂ)

private theorem heatApertureIntegerCoeff_abscissa_lt_top (s : ℂ) :
    LSeries.abscissaOfAbsConv (heatApertureIntegerCoeff s) < ⊤ := by
  let a : ℂ := (starRingEnd ℂ) s - 1
  have hs : LSeriesSummable (heatApertureIntegerCoeff s) (a + 2) := by
    rw [heatApertureIntegerCoeff, show (starRingEnd ℂ) s - 1 = a from rfl,
      LSeriesSummable_powerTwist]
    simpa using (LSeriesSummable_one_iff.mpr (by norm_num : (1 : ℝ) < (2 : ℂ).re))
  exact hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)

/-- All-index integer coefficient peeling. -/
theorem tendsto_heatApertureIntegerPeeledValue
    (s : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto
      (fun x : ℝ => (N : ℂ) ^ (x : ℂ) * heatApertureIntegerPeeledValue s N x)
      atTop (nhds ((N : ℂ) ^ ((starRingEnd ℂ) s - 1))) := by
  have h := tendsto_cpow_mul_LSeries_peeled (f := heatApertureIntegerCoeff s) (N - 1)
    (heatApertureIntegerCoeff_abscissa_lt_top s)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  simpa [heatApertureIntegerPeeledValue, heatApertureIntegerPeeledCoeff,
    heatApertureIntegerCoeff, lseriesPowerTwistCoeff, Nat.sub_add_cancel hN1] using h

/-- The peeled integer value is the full shifted zeta series minus its explicit finite prefix. -/
theorem heatApertureIntegerPeeledValue_eq_zeta_sub_prefix
    {s : ℂ} {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : s.re < x) :
    heatApertureIntegerPeeledValue s N x =
      riemannZeta (1 - (starRingEnd ℂ) s + (x : ℂ)) -
        ∑ m ∈ Finset.range N, LSeries.term (heatApertureIntegerCoeff s) (x : ℂ) m := by
  have hs : LSeriesSummable (heatApertureIntegerCoeff s) (x : ℂ) := by
    rw [heatApertureIntegerCoeff, LSeriesSummable_powerTwist]
    apply LSeriesSummable_one_iff.mpr
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, Complex.one_re]
    linarith
  rw [heatApertureIntegerPeeledValue, heatApertureIntegerPeeledCoeff,
    LSeries_peeled_eq_sub_sum hs (N - 1), heatApertureIntegerCoeff,
    LSeries_powerTwist]
  rw [LSeries_one_eq_riemannZeta]
  · congr 2
    · ring
    · rw [Nat.sub_add_cancel hN]
  · simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, Complex.one_re]
    linarith

/-- Natural-depth form of all-index integer coefficient peeling. -/
theorem tendsto_heatApertureIntegerPeeledValue_nat
    (s : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto
      (fun k : ℕ => (N : ℂ) ^ (k : ℂ) * heatApertureIntegerPeeledValue s N k)
      atTop (nhds ((N : ℂ) ^ ((starRingEnd ℂ) s - 1))) := by
  simpa [Function.comp_def] using
    (tendsto_heatApertureIntegerPeeledValue s hN).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Prime-power Euler-log coefficients twisted by the strip parameter. -/
def heatAperturePrimePowerCoeff (s : ℂ) : ℕ → ℂ :=
  lseriesPowerTwistCoeff RHTower.eulerLogDirichletCoeff ((starRingEnd ℂ) s - 1)

/-- Canonical Euler logarithm of the forward strict echo. -/
def heatApertureLogEchoValue (s : ℂ) (k : ℕ) : ℂ :=
  RHTower.canonicalEulerLogZeta (1 - (starRingEnd ℂ) s + k)

/-- The log echo is exactly the shifted prime-power coefficient `LSeries`. -/
theorem heatApertureLogEchoValue_eq_LSeries (s : ℂ) (k : ℕ) :
    heatApertureLogEchoValue s k = LSeries (heatAperturePrimePowerCoeff s) (k : ℂ) := by
  rw [heatApertureLogEchoValue, RHTower.canonicalEulerLogZeta,
    heatAperturePrimePowerCoeff, LSeries_powerTwist]
  congr 1
  ring

/-- The canonical log echo exponentiates to the forward zeta value. -/
theorem exp_heatApertureLogEchoValue_eq_forward
    {s : ℂ} (hshi : s.re < 1) {k : ℕ} (hk : 1 ≤ k) :
    Complex.exp (heatApertureLogEchoValue s k) = heatApertureForwardZetaValue s k := by
  have hre : 1 < (1 - (starRingEnd ℂ) s + k).re := by
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.conj_re,
      Complex.natCast_re]
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  exact RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hre

/-- Delete every prime-power log coefficient strictly before `N`. -/
def heatAperturePrimePowerPeeledCoeff (s : ℂ) (N : ℕ) : ℕ → ℂ :=
  lseriesPeeledCoeff (heatAperturePrimePowerCoeff s) (N - 1)

/-- Peeled prime-power log echo at real depth. -/
def heatAperturePrimePowerPeeledValue (s : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  LSeries (heatAperturePrimePowerPeeledCoeff s N) (x : ℂ)

private theorem heatAperturePrimePowerCoeff_abscissa_lt_top (s : ℂ) :
    LSeries.abscissaOfAbsConv (heatAperturePrimePowerCoeff s) < ⊤ := by
  let a : ℂ := (starRingEnd ℂ) s - 1
  have hs : LSeriesSummable (heatAperturePrimePowerCoeff s) (a + 2) := by
    rw [heatAperturePrimePowerCoeff, show (starRingEnd ℂ) s - 1 = a from rfl,
      LSeriesSummable_powerTwist]
    simpa using RHTower.canonicalEulerLogZeta_summable
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)
  exact hs.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)

/-- All-index prime-power coefficient peeling. -/
theorem tendsto_heatAperturePrimePowerPeeledValue
    (s : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto
      (fun x : ℝ => (N : ℂ) ^ (x : ℂ) * heatAperturePrimePowerPeeledValue s N x)
      atTop (nhds (RHTower.eulerLogDirichletCoeff N *
        (N : ℂ) ^ ((starRingEnd ℂ) s - 1))) := by
  have h := tendsto_cpow_mul_LSeries_peeled (f := heatAperturePrimePowerCoeff s) (N - 1)
    (heatAperturePrimePowerCoeff_abscissa_lt_top s)
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  simpa [heatAperturePrimePowerPeeledValue, heatAperturePrimePowerPeeledCoeff,
    heatAperturePrimePowerCoeff, lseriesPowerTwistCoeff, Nat.sub_add_cancel hN1] using h

/-- The peeled log echo is the full canonical Euler log minus its explicit finite prefix. -/
theorem heatAperturePrimePowerPeeledValue_eq_logEcho_sub_prefix
    {s : ℂ} {N : ℕ} {x : ℝ} (hN : 1 ≤ N) (hx : s.re < x) :
    heatAperturePrimePowerPeeledValue s N x =
      RHTower.canonicalEulerLogZeta (1 - (starRingEnd ℂ) s + (x : ℂ)) -
        ∑ m ∈ Finset.range N, LSeries.term (heatAperturePrimePowerCoeff s) (x : ℂ) m := by
  have hs : LSeriesSummable (heatAperturePrimePowerCoeff s) (x : ℂ) := by
    rw [heatAperturePrimePowerCoeff, LSeriesSummable_powerTwist]
    apply RHTower.canonicalEulerLogZeta_summable
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re, Complex.one_re]
    linarith
  rw [heatAperturePrimePowerPeeledValue, heatAperturePrimePowerPeeledCoeff,
    LSeries_peeled_eq_sub_sum hs (N - 1), heatAperturePrimePowerCoeff,
    LSeries_powerTwist, ← RHTower.canonicalEulerLogZeta]
  congr 2
  · ring
  · rw [Nat.sub_add_cancel hN]

/-- Rescale the peeled log echo so its limit is the bare Euler-log coefficient. -/
def heatAperturePrimePowerRecoveredValue (s : ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (N : ℂ) ^ (1 - (starRingEnd ℂ) s) *
    ((N : ℂ) ^ (x : ℂ) * heatAperturePrimePowerPeeledValue s N x)

/-- Exact recovery of `Λ(N)/log N` from the peeled log-echo tail. -/
theorem tendsto_heatAperturePrimePowerRecoveredValue
    (s : ℂ) {N : ℕ} (hN : 2 ≤ N) :
    Tendsto (heatAperturePrimePowerRecoveredValue s N)
      atTop (nhds (RHTower.eulerLogDirichletCoeff N)) := by
  have h := (tendsto_heatAperturePrimePowerPeeledValue s hN).const_mul
    ((N : ℂ) ^ (1 - (starRingEnd ℂ) s))
  have hlimit :
      (N : ℂ) ^ (1 - (starRingEnd ℂ) s) *
          (RHTower.eulerLogDirichletCoeff N *
            (N : ℂ) ^ ((starRingEnd ℂ) s - 1)) =
        RHTower.eulerLogDirichletCoeff N := by
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num) hN))
    rw [show (N : ℂ) ^ (1 - (starRingEnd ℂ) s) *
          (RHTower.eulerLogDirichletCoeff N *
            (N : ℂ) ^ ((starRingEnd ℂ) s - 1)) =
        RHTower.eulerLogDirichletCoeff N *
          ((N : ℂ) ^ (1 - (starRingEnd ℂ) s) *
            (N : ℂ) ^ ((starRingEnd ℂ) s - 1)) by ring]
    rw [← Complex.cpow_add _ _ hN0]
    norm_num
  rw [hlimit] at h
  simpa [heatAperturePrimePowerRecoveredValue] using! h

/-- At `N = p^(r+1)`, the recovered value is exactly `1/(r+1)`. -/
theorem tendsto_heatAperturePrimePowerRecoveredValue_prime_pow
    (s : ℂ) (p r : ℕ) (hp : p.Prime) :
    Tendsto (heatAperturePrimePowerRecoveredValue s (p ^ (r + 1)))
      atTop (nhds (1 / (r + 1 : ℂ))) := by
  have hN : 2 ≤ p ^ (r + 1) :=
    hp.two_le.trans (Nat.le_pow (by omega : 0 < r + 1))
  simpa [RHTower.eulerLogDirichletCoeff_prime_pow_succ p r hp] using
    tendsto_heatAperturePrimePowerRecoveredValue s hN

/-- At every non-prime-power `N ≥ 2`, the recovered value is zero. -/
theorem tendsto_heatAperturePrimePowerRecoveredValue_eq_zero
    (s : ℂ) {N : ℕ} (hN : 2 ≤ N) (hnpp : ¬ IsPrimePow N) :
    Tendsto (heatAperturePrimePowerRecoveredValue s N) atTop (nhds 0) := by
  simpa [RHTower.eulerLogDirichletCoeff_eq_zero_of_not_primePower hnpp] using
    tendsto_heatAperturePrimePowerRecoveredValue s hN

end
end GaloisForLFunctions
