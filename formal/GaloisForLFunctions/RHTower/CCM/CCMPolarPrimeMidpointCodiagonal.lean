import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation

/-!
# Midpoint renormalization of the polar--prime source codiagonal

The completed critical-Mellin error has a continuous polar derivative and negative von Mangoldt
jumps.  Reading the error after a jump leaves a positive square-jump debt in its self-pairing.
This file installs the source-faithful correction: every atom is read at the midpoint of its two
one-sided error values.

The corrected continuous-minus-atomic codiagonal is exactly one half of the squared endpoint
completed error.  More generally, an affine fraction `θ` of each jump leaves precisely
`(1 / 2 - θ)` times the von Mangoldt square debt.  Thus the midpoint coefficient is forced by exact
prime--polar cancellation; no absolute-value split or prime-distribution estimate enters.
-/

open scoped BigOperators
open MeasureTheory Set Finset ArithmeticFunction

noncomputable section

namespace RHTower

/-- Finite post-jump chain rule: twice the prefix self-pairing, minus the jump squares, is the
square of the total mass. -/
theorem sum_Icc_mul_prefix_square_identity (w : ℕ → ℝ) (N : ℕ) :
    2 * (∑ k ∈ Finset.Icc 2 N, w k * (∑ j ∈ Finset.Icc 2 k, w j)) -
        ∑ k ∈ Finset.Icc 2 N, w k ^ 2 =
      (∑ k ∈ Finset.Icc 2 N, w k) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      by_cases hN : 2 ≤ N + 1
      · simp only [Finset.sum_Icc_succ_top hN]
        nlinarith [ih]
      · have hzero : N = 0 := by omega
        subst N
        norm_num

/-- At a logarithmic integer atom, the prime mass is exactly the prefix through that atom. -/
theorem criticalMellinPrimeMass_log_nat_eq_atomPrefix (k : ℕ) :
    criticalMellinPrimeMass (Real.log k) =
      ∑ j ∈ Finset.Icc 2 k, criticalMellinAtomWeight j := by
  by_cases hk : 2 ≤ k
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    rw [criticalMellinPrimeMass_eq_atomSum, Real.exp_log hkpos, Nat.floor_natCast]
  · have hklt : k < 2 := by omega
    interval_cases k <;>
      rw [criticalMellinPrimeMass_eq_atomSum] <;>
      norm_num [criticalMellinAtomWeight]

private theorem hasDerivAt_criticalMellinPolarPrimitive (x : ℝ) :
    HasDerivAt (fun h : ℝ => Complex.ofReal (4 * Real.sinh (h / 2)))
      (Complex.ofReal (2 * Real.cosh (x / 2))) x := by
  have hr : HasDerivAt (fun h : ℝ => 4 * Real.sinh (h / 2))
      (2 * Real.cosh (x / 2)) x := by
    apply (((Real.hasDerivAt_sinh (x / 2)).comp x
      ((hasDerivAt_id x).div_const 2)).const_mul 4).congr_deriv
    ring
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
  simpa only [Function.comp_apply, ContinuousLinearMap.coe_comp,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul] using! hc

private theorem integral_criticalMellinPolarGap_mul_density
    (H : NNReal) :
    (∫ h in Set.Ioc (0 : ℝ) (H : ℝ),
      Complex.ofReal (4 * Real.sinh ((H : ℝ) / 2) - 4 * Real.sinh (h / 2)) *
        Complex.ofReal (2 * Real.cosh (h / 2))) =
      Complex.ofReal ((4 * Real.sinh ((H : ℝ) / 2)) ^ 2 / 2) := by
  let Hr : ℝ := H
  change (∫ h in Set.Ioc (0 : ℝ) Hr,
      Complex.ofReal (4 * Real.sinh (Hr / 2) - 4 * Real.sinh (h / 2)) *
        Complex.ofReal (2 * Real.cosh (h / 2))) =
      Complex.ofReal ((4 * Real.sinh (Hr / 2)) ^ 2 / 2)
  let P : ℝ → ℂ := fun h => Complex.ofReal (4 * Real.sinh (h / 2))
  let G : ℝ → ℂ := fun h => P Hr * P h - P h ^ 2 / 2
  have hG : ∀ x ∈ Set.uIcc (0 : ℝ) Hr,
      HasDerivAt G
        ((P Hr - P x) * Complex.ofReal (2 * Real.cosh (x / 2))) x := by
    intro x hx
    have hP := hasDerivAt_criticalMellinPolarPrimitive x
    dsimp only [G]
    apply ((hP.const_mul (P Hr)).sub ((hP.pow 2).div_const 2)).congr_deriv
    ring
  have hInt : IntervalIntegrable
      (fun x : ℝ => (P Hr - P x) * Complex.ofReal (2 * Real.cosh (x / 2)))
      volume 0 Hr := by
    apply Continuous.intervalIntegrable
    dsimp only [P]
    fun_prop
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hG hInt
  have hHr : 0 ≤ Hr := by exact H.property
  rw [intervalIntegral.integral_of_le hHr] at hi
  dsimp only [G, P, Hr] at hi ⊢
  convert hi using 1
  all_goals norm_num
  all_goals ring

/-- Actual continuous-minus-atomic source self-pairing with the atom read at its midpoint. -/
def criticalMellinMidpointCodiagonal (a : NNReal) : ℝ :=
  (criticalMellinStieltjesPairing (a : ℝ)
      (fun h => (criticalMellinCompletedError h : ℂ))).re -
    (1 / 2 : ℝ) *
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
        criticalMellinAtomWeight k ^ 2

/-- The midpoint codiagonal is literally the continuous polar readout minus atomic readout at
the average of completed-error values immediately before and after each von Mangoldt jump. -/
theorem criticalMellinMidpointCodiagonal_eq_continuous_sub_midpointAtoms (a : NNReal) :
    criticalMellinMidpointCodiagonal a =
      (∫ h in Set.Ioc (0 : ℝ) (2 * (a : ℝ)),
        (criticalMellinCompletedError h : ℂ) *
          (2 * Real.cosh (h / 2) : ℂ)).re -
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
          criticalMellinAtomWeight k *
            (criticalMellinCompletedError (Real.log k) +
              criticalMellinAtomWeight k / 2) := by
  rw [criticalMellinMidpointCodiagonal, criticalMellinStieltjesPairing,
    Complex.sub_re, Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hhalf :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
        criticalMellinAtomWeight k * (criticalMellinAtomWeight k / 2)) =
      (1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
        criticalMellinAtomWeight k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hhalf]
  ring

private theorem criticalMellinStieltjesPairing_completedError_re
    (a : NNReal) :
    (criticalMellinStieltjesPairing (a : ℝ)
      (fun h => (criticalMellinCompletedError h : ℂ))).re =
      (4 * Real.sinh ((2 * (a : ℝ)) / 2)) ^ 2 / 2 -
        (4 * Real.sinh ((2 * (a : ℝ)) / 2)) *
          criticalMellinPrimeMass (2 * (a : ℝ)) +
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
          criticalMellinAtomWeight k *
            criticalMellinPrimeMass (Real.log k) := by
  let H : ℝ := 2 * (a : ℝ)
  let P : ℝ → ℝ := fun h => 4 * Real.sinh (h / 2)
  let p : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2)
  let F : ℝ → ℂ := fun h => Complex.ofReal (P H - P h)
  let F' : ℝ → ℂ := fun h => -Complex.ofReal (p h)
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hF : ∀ x ∈ Set.Icc (0 : ℝ) H, HasDerivAt F (F' x) x := by
    intro x hx
    have hPr : HasDerivAt (fun h : ℝ => 4 * Real.sinh (h / 2))
        (2 * Real.cosh (x / 2)) x := by
      apply (((Real.hasDerivAt_sinh (x / 2)).comp x
        ((hasDerivAt_id x).div_const 2)).const_mul 4).congr_deriv
      ring
    have hr : HasDerivAt (fun h : ℝ => P H - P h) (-p x) x := by
      simpa only [P, p] using hPr.const_sub (P H)
    have hc := (Complex.ofRealCLM.hasFDerivAt.comp x hr.hasFDerivAt).hasDerivAt
    simpa only [F, F', Function.comp_apply, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, map_neg] using! hc
  have hFint : IntervalIntegrable F' volume 0 H := by
    apply Continuous.intervalIntegrable
    dsimp only [F', p]
    fun_prop
  have hFend : F H = 0 := by
    dsimp only [F]
    simp
  have hsmooth := criticalMellinStieltjesPairing_integrationByParts
    (a := (a : ℝ)) a.property hF hFint hFend
  have hsmooth' :
      criticalMellinStieltjesPairing (a : ℝ) F =
        ∫ h in Set.Ioc (0 : ℝ) H,
          (criticalMellinCompletedError h : ℂ) * Complex.ofReal (p h) := by
    simpa only [H, F', p, mul_neg, MeasureTheory.integral_neg, neg_neg] using hsmooth
  have hgap := integral_criticalMellinPolarGap_mul_density (⟨H, hH⟩ : NNReal)
  change (∫ h in Set.Ioc (0 : ℝ) H,
      Complex.ofReal (4 * Real.sinh (H / 2) - 4 * Real.sinh (h / 2)) *
        Complex.ofReal (2 * Real.cosh (h / 2))) =
      Complex.ofReal ((4 * Real.sinh (H / 2)) ^ 2 / 2) at hgap
  have hsourceIntegral :
      (∫ h in Set.Ioc (0 : ℝ) H,
        (criticalMellinCompletedError h : ℂ) * Complex.ofReal (p h)) =
      Complex.ofReal (P H ^ 2 / 2) -
        ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
          (criticalMellinAtomWeight k : ℂ) * Complex.ofReal (P H - P (Real.log k)) := by
    calc
      _ = criticalMellinStieltjesPairing (a : ℝ) F := hsmooth'.symm
      _ = _ := by
        rw [criticalMellinStieltjesPairing]
        dsimp only [F]
        rw [show 2 * (a : ℝ) = H by rfl]
        have hgap' :
            (∫ h in Set.Ioc (0 : ℝ) H,
              Complex.ofReal (P H - P h) *
                (2 * Real.cosh (h / 2) : ℂ)) =
              Complex.ofReal (P H ^ 2 / 2) := by
          simpa only [P, Complex.ofReal_mul, Complex.ofReal_ofNat] using hgap
        rw [hgap']
  have hpairing :
      criticalMellinStieltjesPairing (a : ℝ)
          (fun h => (criticalMellinCompletedError h : ℂ)) =
        (∫ h in Set.Ioc (0 : ℝ) H,
          (criticalMellinCompletedError h : ℂ) * Complex.ofReal (p h)) -
          ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
            (criticalMellinAtomWeight k : ℂ) *
              (criticalMellinCompletedError (Real.log k) : ℂ) := by
    rw [criticalMellinStieltjesPairing]
    simp only [H, p, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [hpairing]
  rw [hsourceIntegral, Complex.sub_re, Complex.sub_re]
  simp only [Complex.re_sum, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have herror : ∀ k : ℕ,
      criticalMellinCompletedError (Real.log k) =
        P (Real.log k) - criticalMellinPrimeMass (Real.log k) := by
    intro k
    simpa only [P] using criticalMellinCompletedError_eq_polar_sub_primeMass (Real.log k)
  simp_rw [herror]
  have hmass : criticalMellinPrimeMass H =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊, criticalMellinAtomWeight k :=
    criticalMellinPrimeMass_eq_atomSum H
  rw [hmass]
  dsimp only [H, P] at *
  rw [Finset.mul_sum]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hcomm :
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
        criticalMellinAtomWeight k * (4 * Real.sinh ((2 * (a : ℝ)) / 2))) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
        (4 * Real.sinh ((2 * (a : ℝ)) / 2)) * criticalMellinAtomWeight k := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hcomm]
  ring

/-- Exact jump-corrected self-codiagonal law for the actual von Mangoldt--polar source. -/
theorem criticalMellinMidpointCodiagonal_eq_completedError_sq (a : NNReal) :
    criticalMellinMidpointCodiagonal a =
      criticalMellinCompletedError (2 * (a : ℝ)) ^ 2 / 2 := by
  rw [criticalMellinMidpointCodiagonal,
    criticalMellinStieltjesPairing_completedError_re]
  rw [criticalMellinPrimeMass_eq_atomSum]
  simp_rw [criticalMellinPrimeMass_log_nat_eq_atomPrefix]
  have hprefix := sum_Icc_mul_prefix_square_identity criticalMellinAtomWeight
    ⌊Real.exp (2 * (a : ℝ))⌋₊
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass,
    criticalMellinPrimeMass_eq_atomSum]
  nlinarith

/-- Positivity is produced directly by prime--polar cancellation, with no absolute-value split. -/
theorem criticalMellinMidpointCodiagonal_nonneg (a : NNReal) :
    0 ≤ criticalMellinMidpointCodiagonal a := by
  rw [criticalMellinMidpointCodiagonal_eq_completedError_sq]
  positivity

/-- Affine atomic readout, where `θ` is the fraction of the current jump added to the post-jump
completed error. -/
def criticalMellinAffineJumpCodiagonal (θ : ℝ) (a : NNReal) : ℝ :=
  (criticalMellinStieltjesPairing (a : ℝ)
      (fun h => (criticalMellinCompletedError h : ℂ))).re -
    θ * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
      criticalMellinAtomWeight k ^ 2

/-- **Affine jump rigidity.** Every coefficient other than the midpoint leaves exactly its signed
fraction of the von Mangoldt square debt. -/
theorem criticalMellinAffineJumpCodiagonal_eq_completedError_sq_add_atomDebt
    (θ : ℝ) (a : NNReal) :
    criticalMellinAffineJumpCodiagonal θ a =
      criticalMellinCompletedError (2 * (a : ℝ)) ^ 2 / 2 +
        ((1 / 2 : ℝ) - θ) *
          ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * (a : ℝ))⌋₊,
            criticalMellinAtomWeight k ^ 2 := by
  have hmid := criticalMellinMidpointCodiagonal_eq_completedError_sq a
  rw [criticalMellinMidpointCodiagonal] at hmid
  rw [criticalMellinAffineJumpCodiagonal]
  linarith

end RHTower
