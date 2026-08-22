import GaloisForLFunctions.RHTower.PrimeSquareSuperessentialScale
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential

/-!
# Prime-square superessential versus Wold first-trace scale rigidity

The critically normalized prime-square reflection channel has logarithmic growth of order `c N`
at every positive horizontal drift `c`, whereas the reciprocal Wold boundary volume is only
polylogarithmic.  This module turns that asymptotic separation into an exact order firewall:
domination by any fixed nonnegative multiple of the Wold scale holds exactly at zero drift.

The prime-square drift and the coefficient-faithful Wold connection use the same literal centered
horizontal coordinate.  Specializing the firewall to the Xi divisor therefore makes universal
Wold-scale domination equivalent to RH.  This is a no-go for a first-trace comparison producer:
a viable fusion must renormalize at exponential type or retain signed cancellation rather than
bound the prime-square signal by the Wold anomaly scale.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Eventual domination of the prime-square logarithmic reflection product by a fixed multiple of
the reciprocal Wold boundary volume. -/
def PrimeSquareWoldScaleDominated (c : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
    (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) ≤
      K * (primeEulerVolume N)⁻¹

/-- Every positive admissible drift escapes every fixed Wold first-trace budget. -/
theorem not_primeSquareWoldScaleDominated_of_pos
    {c : ℝ} (hc : 0 < c) (hc2 : 2 * c ≤ 1) :
    ¬ PrimeSquareWoldScaleDominated c := by
  rintro ⟨K, hK, hdom⟩
  have hratio := tendsto_inv_primeEulerVolume_div_logProd hc hc2
  have hscaled :
      Tendsto (fun N : ℕ => K * ((primeEulerVolume N)⁻¹ /
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))))
        atTop (nhds 0) := by
    simpa using hratio.const_mul K
  have hsmall : ∀ᶠ N : ℕ in atTop,
      K * ((primeEulerVolume N)⁻¹ /
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))) < 1 :=
    hscaled.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hrate := tendsto_log_prod_criticalNormalizedReflection_div_natCast hc.le hc2
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp hrate (c / 2) (by linarith)
  have hsumpos : ∀ᶠ N : ℕ in atTop,
      0 < ∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c) := by
    filter_upwards [eventually_ge_atTop M, eventually_gt_atTop 0] with N hNM hN0
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
    have hd := hM N hNM
    rw [Real.dist_eq, abs_lt] at hd
    have hratioPos : c / 2 <
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) /
          (N : ℝ) := by
      linarith [hd.1]
    have hquotpos : 0 <
        (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) /
          (N : ℝ) := lt_trans (by linarith : 0 < c / 2) hratioPos
    rw [div_pos_iff] at hquotpos
    rcases hquotpos with hpos | hneg
    · exact hpos.1
    · exact (not_lt_of_ge hNpos.le hneg.2).elim
  obtain ⟨N, hdomN, hsmallN, hsumN⟩ :=
    (hdom.and (hsmall.and hsumpos)).exists
  have hone : (1 : ℝ) ≤ K * ((primeEulerVolume N)⁻¹ /
      (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))) := by
    calc
      (1 : ℝ) =
          (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) /
            (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) :=
        (div_self hsumN.ne').symm
      _ ≤ (K * (primeEulerVolume N)⁻¹) /
            (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c)) :=
        (div_le_div_iff_of_pos_right hsumN).2 hdomN
      _ = K * ((primeEulerVolume N)⁻¹ /
            (∑ p ∈ Nat.primesBelow N, Real.log (criticalNormalizedReflection p c))) := by ring
  linarith

/-- Neutral drift is Wold-scale dominated with zero budget. -/
theorem primeSquareWoldScaleDominated_zero :
    PrimeSquareWoldScaleDominated 0 := by
  refine ⟨0, le_rfl, Filter.Eventually.of_forall fun N => ?_⟩
  have hterm : ∀ p ∈ Nat.primesBelow N,
      Real.log (criticalNormalizedReflection p 0) = 0 := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [(criticalNormalizedReflection_eq_one_iff hp.2.one_lt 0).2 rfl,
      Real.log_one]
  rw [Finset.sum_eq_zero hterm]
  simp

/-- **Scale-rigidity classification.** On the admissible strip, Wold-scale domination is exactly
neutral horizontal drift. -/
theorem primeSquareWoldScaleDominated_iff
    {c : ℝ} (hc0 : 0 ≤ c) (hc2 : 2 * c ≤ 1) :
    PrimeSquareWoldScaleDominated c ↔ c = 0 := by
  constructor
  · intro hdom
    by_contra hcne
    exact not_primeSquareWoldScaleDominated_of_pos (lt_of_le_of_ne hc0 (Ne.symm hcne)) hc2 hdom
  · rintro rfl
    exact primeSquareWoldScaleDominated_zero

/-- Absolute prime-square drift attached to the same centered horizontal coordinate as the
coefficient-faithful Wold connection. -/
def primeSquareXiHorizontalDrift (rho : XiDivisorSupport) : ℝ :=
  |primeDepthBVWoldXiCenteredRate rho| / 2

theorem primeSquareXiHorizontalDrift_nonneg (rho : XiDivisorSupport) :
    0 ≤ primeSquareXiHorizontalDrift rho := by
  rw [primeSquareXiHorizontalDrift]
  positivity

theorem two_mul_primeSquareXiHorizontalDrift_le_one (rho : XiDivisorSupport) :
    2 * primeSquareXiHorizontalDrift rho ≤ 1 := by
  obtain ⟨hzero, hone⟩ :=
    xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support rho)
  have habs : |2 * (rho : ℂ).re - 1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [primeSquareXiHorizontalDrift, primeDepthBVWoldXiCenteredRate]
  linarith

theorem primeSquareXiHorizontalDrift_eq_zero_iff (rho : XiDivisorSupport) :
    primeSquareXiHorizontalDrift rho = 0 ↔ (rho : ℂ).re = 1 / 2 := by
  rw [primeSquareXiHorizontalDrift, div_eq_zero_iff]
  simp only [OfNat.ofNat_ne_zero, or_false, abs_eq_zero]
  exact primeDepthBVWoldXiCenteredRate_eq_zero_iff rho

/-- Universal Xi-copy specialization of Wold-scale domination. -/
def EveryXiPrimeSquareWoldScaleDominated : Prop :=
  ∀ rho : XiDivisorSupport,
    PrimeSquareWoldScaleDominated (primeSquareXiHorizontalDrift rho)

/-- The tempting completed Wold cap on the prime-square signal is already exactly RH-strength. -/
theorem everyXiPrimeSquareWoldScaleDominated_iff_riemannHypothesis :
    EveryXiPrimeSquareWoldScaleDominated ↔ RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro z hz
    let rho : XiDivisorSupport := ⟨z, mem_xi_divisor_support_of_eq_zero hz⟩
    have hzero := (primeSquareWoldScaleDominated_iff
      (primeSquareXiHorizontalDrift_nonneg rho)
      (two_mul_primeSquareXiHorizontalDrift_le_one rho)).mp (hall rho)
    exact (primeSquareXiHorizontalDrift_eq_zero_iff rho).mp hzero
  · intro hRH rho
    have hline := xi_zero_re_eq_half_of_RH hRH
      (xi_eq_zero_of_mem_divisor_support rho)
    have hzero := (primeSquareXiHorizontalDrift_eq_zero_iff rho).2 hline
    rw [hzero]
    exact primeSquareWoldScaleDominated_zero

end

end RHTower
