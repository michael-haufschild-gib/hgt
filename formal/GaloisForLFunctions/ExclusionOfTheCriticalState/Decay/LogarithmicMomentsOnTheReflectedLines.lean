import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheTiltedStateLiesInTheEnergyDomainUpToTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheLogarithmicDerivativeOfZetaIsSublogarithmicRightOfTheZeros

/-!
# Logarithmic moments on the reflected lines

Exponential confinement transfers the translation estimate for the critical state to
its growing tilt. Plancherel then gives geometric decay of Fourier mass on geometric
shells, enough to multiply the reflected trace by the regular part of the Euler symbol.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- Split the increment of a growing tilt between ordinary and confined mass. -/
private theorem tilted_increment_le {F : ℝ → ℝ} (hd : CriticalHalfLineEnergyDomain F)
    {c k : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) (hk : 0 < k) (hk1 : k ≤ 1)
    (hg : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(c * u)) * F u)) :
    let h := k ^ 2
    let G := fun u => Real.exp (-(c * u)) * F u
    k * (∫ u, (G u - G (u + h)) ^ 2) ≤
      2 * (∫ u, (F u - F (u + h)) ^ 2) + h * (2 * (∫ u, F u ^ 2) +
        (2 + 2 * Real.exp 8) * (∫ u, F u ^ 2 * Real.exp (-(8 * u)))) := by
  intro h G
  have hh : 0 ≤ h := sq_nonneg _
  have hh1 : h ≤ 1 := pow_le_one₀ hk.le hk1
  let r := Real.exp (-(c * h))
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hc hh))
  have hrh : (1 - r) ^ 2 ≤ h := by
    have hch : c * h ≤ h := mul_le_of_le_one_left hh hc1
    have hsmall : 1 - r ≤ h := by linarith only [Real.add_one_le_exp (-(c*h)), hch]
    exact (pow_le_pow_left₀ (sub_nonneg.mpr hr1) hsmall 2).trans
      (by nlinarith only [mul_nonneg hh (sub_nonneg.mpr hh1)])
  let D := fun u => F u + (-r) * F (u + h)
  have ht := hd.causalTranslate hh
  have hD : CriticalHalfLineEnergyDomain D := hd.add_const_mul ht (-r)
  have e (u : ℝ) : G u - G (u + h) = Real.exp (-(c*u)) * D u := by
    dsimp [G, D, r]
    rw [show -(c * (u + h)) = -(c*u) + -(c*h) by ring, Real.exp_add]
    ring
  have hordinary : (∫ u, D u ^ 2) ≤ 2 * (∫ u, (F u - F (u+h)) ^ 2) +
      (2*h) * (∫ u, F u ^ 2) := by
    rw [← integral_add_right_eq_self (fun u => F u ^ 2) h, ← integral_const_mul,
      ← integral_const_mul, ← integral_add ((integrable_sq_increment hd hh).const_mul 2)
        (ht.sq.const_mul (2*h))]
    apply integral_mono hD.sq (((integrable_sq_increment hd hh).const_mul 2).add
      (ht.sq.const_mul (2*h)))
    intro u
    change (F u + -r * F (u+h)) ^ 2 ≤ 2*(F u - F (u+h)) ^ 2 + (2*h)*F (u+h)^2
    nlinarith only [sq_nonneg ((F u - F (u+h)) - (1-r)*F (u+h)),
      mul_nonneg (sub_nonneg.mpr hrh) (sq_nonneg (F (u+h)))]
  let M := ∫ u, F u ^ 2 * Real.exp (-(8*u))
  have hM : 0 ≤ M := integral_nonneg fun u => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  have hconf : (∫ u, D u ^ 2 * Real.exp (-(8*u))) ≤ (2+2*Real.exp 8)*M := by
    have h := criticalHalfLine_exponential_mass_add_const_mul_le hd ht (-r)
    change (∫ u, D u ^ 2 * Real.exp (-(8*u))) ≤ 2*M +
      2*(-r)^2 * (∫ u, F (u+_) ^ 2 * Real.exp (-(8*u))) at h
    rw [exponential_square_comp_add_right] at h
    have hr2 : (-r)^2 ≤ 1 := by simpa only [neg_sq] using pow_le_one₀ hr hr1 (n := 2)
    have he : Real.exp (8 * k^2) ≤ Real.exp 8 := Real.exp_le_exp.mpr (by linarith only [hh1])
    exact h.trans (by
      change 2*M + 2*(-r)^2 * (Real.exp (8*k^2)*M) ≤ _
      nlinarith only [mul_le_mul_of_nonneg_right he hM,
        mul_le_mul_of_nonneg_right hr2 (mul_nonneg (Real.exp_pos (8*k^2)).le hM)])
  have hbound (u : ℝ) : k * (G u - G (u+h))^2 ≤
      D u ^ 2 + h * (D u ^ 2 * Real.exp (-(8*u))) := by
    rw [e, mul_pow]
    by_cases hu : 0 ≤ u
    · simp [hD.support u hu]
    have hcu : -(c*u) ≤ -(2*u) := by nlinarith only [mul_nonneg (show 0 ≤ 2-c by linarith)
      (show 0 ≤ -u by linarith)]
    have h1 : Real.exp (-(c*u)) ^ 2 ≤ Real.exp (-(4*u)) := by
      rw [← Real.exp_nat_mul]
      exact Real.exp_le_exp.mpr (by push_cast; linarith only [hcu])
    have h2 : Real.exp (-(4*u)) ^ 2 = Real.exp (-(8*u)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hkexp := mul_le_mul_of_nonneg_left h1 hk.le
    have he : k * Real.exp (-(c*u))^2 ≤ 1+h*Real.exp (-(8*u)) := by
      rw [← h2]
      dsimp [h]
      nlinarith only [hkexp, sq_nonneg (k*Real.exp (-(4*u))-1/2)]
    nlinarith only [mul_le_mul_of_nonneg_right he (sq_nonneg (D u))]
  have hs := integral_mono ((integrable_sq_increment hg hh).const_mul k)
    (hD.sq.add (hD.exponential.const_mul h)) hbound
  simp only [Pi.add_apply, integral_add hD.sq (hD.exponential.const_mul h), integral_const_mul] at hs
  change k * (∫ u, (G u - G (u+h))^2) ≤ _
  linarith only [hs, hordinary, mul_le_mul_of_nonneg_left hconf hh]

/-- At step `k²` the squared translation modulus of the growing tilt is `O(k)`. -/
theorem criticalState_eventually_tilted_sq_increment_le {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    let G := fun u => Real.exp (-(c*u)) * F u
    ∃ K : ℝ, ∀ᶠ k : ℝ in 𝓝[>] 0, (∫ u, (G u - G (u + k^2)) ^ 2) ≤ K*k := by
  intro G
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hg := criticalHalfLineEnergyDomain_exp_mul_groundState hW ht hF hc hc1
  have hnear : Tendsto (fun k : ℝ => k^2) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (by simpa using ((continuous_id.pow 2).continuousAt (x := (0 : ℝ))).tendsto.mono_left
        nhdsWithin_le_nhds) (self_mem_nhdsWithin.mono fun k (hk : 0 < k) => sq_pos_of_pos hk)
  have hlog : ∀ᶠ h : ℝ in 𝓝[>] 0, 1 ≤ Real.log (1/h) := by
    simpa only [one_div] using (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually_ge_atTop 1
  let M := ∫ u, F u ^ 2 * Real.exp (-(8*u))
  let B := 8 * criticalAliasCoefficient W₀ * M + 1
  let C := 2 * (∫ u, F u ^ 2) + (2+2*Real.exp 8)*M
  refine ⟨2*B+C, ?_⟩
  filter_upwards [hnear.eventually (criticalState_eventually_log_mul_sq_increment_le hW ht hF
    (ε := 1) zero_lt_one), hnear.eventually hlog, self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono nhdsWithin_le_nhds]
    with k hwall hlogk hk hk1
  have hmass : 0 ≤ ∫ u, (F u - F (u + k^2))^2 := integral_nonneg fun _ => sq_nonneg _
  have hsmall : (∫ u, (F u - F (u + k^2))^2) ≤ B*k^2 := by
    exact (le_mul_of_one_le_left hmass hlogk).trans hwall
  have hinc := tilted_increment_le hd hc hc1 hk hk1.le hg
  change k * (∫ u, (G u - G (u+k^2))^2) ≤ 2*(∫ u, (F u - F (u+k^2))^2) + k^2*C at hinc
  apply (mul_le_mul_left hk).mp
  nlinarith only [hinc, hsmall]

end GaloisForLFunctions.ExclusionOfTheCriticalState
