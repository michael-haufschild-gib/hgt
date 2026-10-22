import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheSignedWorkChangesSignOnce
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensationNeedsItsCrossTerms

/-!
# The second damping tangent and convexity of the critical energy

Differentiating the damped row twice in the damping gives the weight

`Λ⁽²⁾_η(k) = Σ_{d ∣ k} μ(d) (log d)² d^{-η}`,

whose centred prefix `F_η(n) = Σ_{k ≤ n} Λ⁽²⁾_η(k) − n m'(η)` is the **second damping tangent** of
the source (`hasDerivAt_dampedChebyshevError`); its density is the damping derivative of the
readout, obtained from the second derivative of `ζ` at `1 + η`
(`hasDerivAt_dampedReadout`).

With it the second damping derivative of the critical energy is explicit: differentiating the
signed work cell by cell gives

`W'_T(ε) = ‖E_ε‖_T² + ⟪A_ε, F_ε⟫_T`  (`hasDerivAt_signedDampingWork`),

so `E''_T = 2(‖E_ε‖_T² + ⟪A_ε, F_ε⟫_T)`.  Since both ends of the damping range are paid, convexity
of the energy already closes the problem, and convexity is exactly the inequality

`−‖E_ε‖_T² ≤ ⟪A_ε, F_ε⟫_T`.

This is a demand of a new type for the layer: **no constant and no uniformity in the horizon
appear**.  It asks only that the source never be anti-aligned with its own second tangent by more
than the energy of the first tangent, one inequality per damping and horizon
(`riemannHypothesis_of_second_tangent_pairing_ge`).  By Cauchy–Schwarz it holds whenever
`‖F_ε‖_T ≤ ‖E_ε‖_T²/√(E_T(ε))`, but the point is that the signed pairing — not the size of the
second tangent — is what has to be controlled.
-/

open Set Filter Finset Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The second damped von Mangoldt weight -/

/-- The second damped von Mangoldt weight `Λ⁽²⁾_η(k) = Σ_{d ∣ k} μ(d)(log d)² d^{-η}`: the damping
derivative of `Λ_η`. -/
def dampedVonMangoldtSecond (η : ℝ) (k : ℕ) : ℝ :=
  ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d ^ 2 * (d : ℝ) ^ (-η)

theorem hasDerivAt_dampedVonMangoldt (η : ℝ) (k : ℕ) :
    HasDerivAt (fun x => dampedVonMangoldt x k) (dampedVonMangoldtSecond η k) η := by
  unfold dampedVonMangoldt dampedVonMangoldtSecond
  have h := HasDerivAt.fun_sum (u := k.divisors)
    (A := fun d x => (ArithmeticFunction.moebius d : ℝ) * Real.log d * (d : ℝ) ^ (-x))
    (A' := fun d => (ArithmeticFunction.moebius d : ℝ) * Real.log d *
      -(Real.log d * (d : ℝ) ^ (-η)))
    (fun d hd => (hasDerivAt_natCast_rpow_neg (Nat.pos_of_mem_divisors hd) η).const_mul _)
  refine (h.neg).congr_deriv ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

/-! ## §2. The damping derivative of the readout -/

/-- The damping derivative of the readout `m(η) = Re(−ζ'(1+η)/ζ(1+η)²)`. -/
def dampedReadoutSecond (η : ℝ) : ℝ :=
  (2 * deriv riemannZeta (1 + (η : ℂ)) ^ 2 / riemannZeta (1 + (η : ℂ)) ^ 3 -
    deriv (deriv riemannZeta) (1 + (η : ℂ)) / riemannZeta (1 + (η : ℂ)) ^ 2).re

theorem hasDerivAt_dampedReadout {η : ℝ} (hη : 0 < η) :
    HasDerivAt dampedReadout (dampedReadoutSecond η) η := by
  have hne : riemannZeta (1 + (η : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (one_lt_re_one_add_ofReal hη)
  have han : AnalyticAt ℂ riemannZeta (1 + (η : ℂ)) :=
    DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds (one_add_ofReal_ne_one hη))
  have hc : HasDerivAt (fun z : ℂ => 1 + z) 1 (η : ℂ) := (hasDerivAt_id _).const_add 1
  have hζ : HasDerivAt (fun z : ℂ => riemannZeta (1 + z))
      (deriv riemannZeta (1 + (η : ℂ))) (η : ℂ) := by
    have h3 := (han.differentiableAt.hasDerivAt).comp (η : ℂ) hc
    rw [mul_one] at h3
    exact h3
  have hζ2 : HasDerivAt (fun z : ℂ => deriv riemannZeta (1 + z))
      (deriv (deriv riemannZeta) (1 + (η : ℂ))) (η : ℂ) := by
    have h3 := (han.deriv.differentiableAt.hasDerivAt).comp (η : ℂ) hc
    rw [mul_one] at h3
    exact h3
  have hden : HasDerivAt (fun z : ℂ => riemannZeta (1 + z) ^ 2)
      (2 * riemannZeta (1 + (η : ℂ)) * deriv riemannZeta (1 + (η : ℂ))) (η : ℂ) := by
    refine (hζ.pow 2).congr_deriv ?_
    push_cast
    ring
  have hdiv : HasDerivAt (fun z : ℂ => -deriv riemannZeta (1 + z) / riemannZeta (1 + z) ^ 2)
      ((-(deriv (deriv riemannZeta) (1 + (η : ℂ))) * riemannZeta (1 + (η : ℂ)) ^ 2 -
          -deriv riemannZeta (1 + (η : ℂ)) *
            (2 * riemannZeta (1 + (η : ℂ)) * deriv riemannZeta (1 + (η : ℂ)))) /
        (riemannZeta (1 + (η : ℂ)) ^ 2) ^ 2) (η : ℂ) :=
    (hζ2.neg).div hden (pow_ne_zero 2 hne)
  have hre := hdiv.real_of_complex
  refine hre.congr_deriv ?_
  rw [dampedReadoutSecond]
  congr 1
  field_simp
  ring

/-! ## §3. The second damping tangent of the source -/

/-- **The second damping tangent** `F_η(n) = Σ_{k ≤ n} Λ⁽²⁾_η(k) − n m'(η)`. -/
def dampedChebyshevSecond (η : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 n, dampedVonMangoldtSecond η k - dampedReadoutSecond η * n

/-- The centred damped Chebyshev function has the second tangent as its damping derivative. -/
theorem hasDerivAt_dampedChebyshevError {η : ℝ} (hη : 0 < η) (n : ℕ) :
    HasDerivAt (fun x => dampedChebyshevError x n) (dampedChebyshevSecond η n) η := by
  unfold dampedChebyshevError dampedChebyshevSecond
  exact (HasDerivAt.fun_sum fun k _ => hasDerivAt_dampedVonMangoldt η k).sub
    ((hasDerivAt_dampedReadout hη).mul_const _)

/-! ## §4. The second damping derivative of the critical energy -/

/-- **The damping derivative of the signed work**: the tangent energy plus the pairing of the
source with the second tangent.  Hence `E''_T = 2(‖E_ε‖_T² + ⟪A_ε, F_ε⟫_T)`. -/
theorem hasDerivAt_signedDampingWork {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => signedDampingWork x T)
      (pronicNorm T (dampedChebyshevError ε) ^ 2 +
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (dampedChebyshevSecond ε)) ε := by
  have h := HasDerivAt.fun_sum (u := Icc 1 T)
    (A := fun n x => pmPowerDampedCenteredDivisorPrefix x n * dampedChebyshevError x n /
      ((n : ℝ) * ((n : ℝ) + 1)))
    (A' := fun n => (dampedChebyshevError ε n ^ 2 +
      pmPowerDampedCenteredDivisorPrefix ε n * dampedChebyshevSecond ε n) /
        ((n : ℝ) * ((n : ℝ) + 1)))
    (fun n _ => by
      have hp := ((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε n).mul
        (hasDerivAt_dampedChebyshevError hε n)).div_const ((n : ℝ) * ((n : ℝ) + 1))
      refine hp.congr_deriv ?_
      ring)
  refine h.congr_deriv ?_
  rw [pronicNorm_sq, pronicPairing, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ## §5. The constant-free convexity criterion -/

/-- **Convexity from the second tangent.**  If the source is never anti-aligned with its own second
tangent by more than the tangent energy, the signed work is nondecreasing in the damping. -/
theorem monotoneOn_signedDampingWork_of_second_tangent_pairing_ge (T : ℕ)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      -(pronicNorm T (dampedChebyshevError ε) ^ 2) ≤
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (dampedChebyshevSecond ε)) :
    MonotoneOn (fun ε => signedDampingWork ε T) (Ioc (0 : ℝ) (1 / 2)) := by
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (1 / 2))
    (f' := fun ε => pronicNorm T (dampedChebyshevError ε) ^ 2 +
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (dampedChebyshevSecond ε))
    ((continuousOn_signedDampingWork T).mono fun x hx => mem_Ioi.mpr hx.1) ?_ ?_
  · intro x hx
    rw [interior_Ioc] at hx
    exact (hasDerivAt_signedDampingWork hx.1 T).hasDerivWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    linarith [h x hx.1 (le_of_lt hx.2)]

/-- **The constant-free criterion for the Riemann hypothesis.**  One inequality per damping and
horizon — the source paired with its second tangent above minus the tangent energy — makes the
critical energy convex in the damping, and both ends of the damping range are paid.  No constant
and no horizon-uniform bound appear in the hypothesis. -/
theorem riemannHypothesis_of_second_tangent_pairing_ge
    (h : ∀ (T : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      -(pronicNorm T (dampedChebyshevError ε) ^ 2) ≤
        pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (dampedChebyshevSecond ε)) :
    RiemannHypothesis :=
  riemannHypothesis_of_monotoneOn_signedWork fun T =>
    monotoneOn_signedDampingWork_of_second_tangent_pairing_ge T fun ε hε hε2 => h T ε hε hε2

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
