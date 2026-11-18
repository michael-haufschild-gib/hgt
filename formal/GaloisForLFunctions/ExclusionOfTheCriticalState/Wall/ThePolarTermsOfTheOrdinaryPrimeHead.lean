import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProperPrimePowersInThePrimeWave
import GaloisForLFunctions.RHTower.MobiusLaplaceLandauOscillation
import GaloisForLFunctions.RHTower.MertensProductLaplace

/-!
# Removing the polar charges from the ordinary-prime head

The Euler product removes the growing charge at frequency minus one half.
The square-prime pole supplies a second, constant charge. After both
subtractions the ordinary-prime transform is analytic around the closed
unit disk centred at minus one, for every profile in the energy domain.
-/

noncomputable section
open MeasureTheory Set Complex Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The head integrals at ordinary primes. -/
def ordinaryPrimeHead (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' q : Nat.Primes, (vonMangoldtAtom (q : ℕ) : ℂ) *
    (cexp (p * Real.log (q : ℕ)) * levyHead F p (Real.log (q : ℕ)))

private theorem analytic_state_laplace {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {p : ℂ} (hp : -4 < p.re) : AnalyticAt ℂ (negativeHalfLineLaplace (cx F)) p :=
  (differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential).analyticOnNhd
    (isOpen_lt continuous_const continuous_re) _ (by change -(8/2:ℝ) < p.re; linarith)

/-- Regularize the actual proper-power continuation at zero through its analytic numerator. -/
private theorem exists_regular_properPowerHead {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ K : ℂ → ℂ, AnalyticAt ℂ K 0 ∧
      (∀ p : ℂ, -4 < p.re → p.re < 0 → AnalyticAt ℂ K p ∧
        K p = properPowerHead F p + negativeHalfLineLaplace (cx F) 0 / (2*p)) := by
  let L := negativeHalfLineLaplace (cx F)
  obtain ⟨G,hG,hG0,hagree⟩ := properPowerHeadContinuation_residue hF
  let K := fun p : ℂ => if p = 0 then deriv G 0 else properPowerHeadContinuation F p + L 0/(2*p)
  refine ⟨K,?_,?_⟩
  · apply (analyticAt_dslope_of_analyticAt_of_analyticAt hG hG).congr
    apply (eventually_nhdsWithin_iff.mp hagree).mono
    intro p hp
    by_cases h : p = 0
    · subst p
      simp [K,dslope_same]
    · have he := hp (by simpa using h)
      simp only [K,if_neg h,dslope_of_ne _ h,slope_def_field,sub_zero,he,hG0,L]
      field_simp
      ring
  · intro p hp4 hp
    have hU : {z : ℂ | -4 < z.re ∧ z.re < 0} ∈ 𝓝 p :=
      ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).mem_nhds ⟨hp4,hp⟩
    have he : K =ᶠ[𝓝 p] fun z => properPowerHead F z + L 0/(2*z) := by
      filter_upwards [hU] with z hz
      have hn : z ≠ 0 := fun h => by simpa [h] using hz.2
      simp only [K,if_neg hn,properPowerHeadContinuation_eq hF hz.1 hz.2]
    have hpr := (differentiableOn_properPowerHead hF).analyticOnNhd
      (isOpen_lt continuous_re continuous_const) p hp
    have hn : p ≠ 0 := fun h => by simp [h] at hp
    have hc : AnalyticAt ℂ (fun z : ℂ => L 0/(2*z)) p :=
      analyticAt_const.div (analyticAt_const.mul analyticAt_id) (mul_ne_zero (by norm_num) hn)
    exact ⟨(hpr.add hc).congr he.symm,he.eq_of_nhds⟩

/-- Removing the growing polar charge and the prime-square constant continues
the ordinary-prime head across the closed unit disk about minus one. -/
theorem exists_analyticOnNhd_regular_ordinaryPrimeHead {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.closedBall (-1) 1) ∧
      ∀ p : ℂ, -4 < p.re → p.re < -(1/2) → G p = ordinaryPrimeHead F p +
        negativeHalfLineLaplace (cx F) (-(1/2)) / (p+1/2) - negativeHalfLineLaplace (cx F) 0/(2*p) := by
  let L := negativeHalfLineLaplace (cx F)
  obtain ⟨K,hK0,hK⟩ := exists_regular_properPowerHead hF
  let s := fun p : ℂ => 1/2-p
  let G := fun p : ℂ => L p * _root_.RHTower.Sieve.zetaLogDerivReg (s p) -
    dslope L (-(1/2)) p - stateTail F p - K p
  refine ⟨G,?_,?_⟩
  · intro p hp
    have hnorm : ‖p+1‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_eq_norm,sub_neg_eq_add] using hp
    have hhi := (Complex.abs_re_le_norm (p+1)).trans hnorm
    have him := (Complex.abs_im_le_norm (p+1)).trans hnorm
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero] at hhi him
    have hp4 : -4 < p.re := by linarith [(abs_le.mp hhi).1]
    have hp0 : p.re ≤ 0 := by linarith [(abs_le.mp hhi).2]
    have hKp : AnalyticAt ℂ K p := by
      rcases lt_or_eq_of_le hp0 with h | h
      · exact (hK p hp4 h).1
      · have hn := Complex.sq_norm (p+1)
        have hs : ‖p+1‖ ^ 2 ≤ 1 := by nlinarith only [hnorm,norm_nonneg (p+1)]
        have hI : p.im = 0 := by
          simp only [Complex.normSq_apply,Complex.add_re,Complex.one_re,Complex.add_im,
            Complex.one_im,add_zero,h,zero_add] at hn
          nlinarith only [hn,hs,sq_nonneg p.im]
        have he : p = 0 := Complex.ext h hI
        rwa [he]
    have hsu : zetaResidueUnit (s p) ≠ 0 :=
      zetaResidueUnit_ne_zero_of_re_pos_abs_im_le_four
        (by norm_num [s]; linarith) (by simpa [s] using him.trans (by norm_num : (1:ℝ) ≤ 4))
    have hr : AnalyticAt ℂ _root_.RHTower.Sieve.zetaLogDerivReg (s p) := by
      exact ((analyticAt_zetaResidueUnit (s p)).deriv.div (analyticAt_zetaResidueUnit (s p)) hsu).neg
    have hs : AnalyticAt ℂ s p := by dsimp [s]; fun_prop
    have hreg : AnalyticAt ℂ (_root_.RHTower.Sieve.zetaLogDerivReg ∘ s) p := hr.comp hs
    have hS := analyticAt_dslope_of_analyticAt_of_analyticAt
      (analytic_state_laplace hF (p := -(1/2)) (by norm_num)) (analytic_state_laplace hF hp4)
    have hT := (differentiableOn_stateTail_strip hF).analyticOnNhd
      (isOpen_lt continuous_const continuous_re) p hp4
    exact ((((analytic_state_laplace hF hp4).mul hreg).sub hS).sub hT).sub hKp
  · intro p hp4 hp
    have hsp : 1 < (s p).re := by norm_num [s]; linarith
    have hne : s p ≠ 1 := fun h => by simp [h] at hsp
    have hz := _root_.RHTower.Sieve.neg_logDeriv_riemannZeta_eq_of_ne_zero hne
      (riemannZeta_ne_zero_of_one_lt_re hsp)
    have hm : p ≠ -(1/2) := fun h => by norm_num [h] at hp
    have he : s p - 1 = -(p+1/2) := by dsimp [s]; ring
    rw [logDeriv_apply,he,inv_neg] at hz
    have ht := stateTail_eq_left hF hp4 hp
    change stateTail F p = -(L p * (deriv riemannZeta (s p)/riemannZeta (s p))) - primeHead F p at ht
    have hsplit := primeHead_eq_prime_add_properPowerHead hF hp
    change primeHead F p = ordinaryPrimeHead F p + properPowerHead F p at hsplit
    rw [hsplit] at ht
    dsimp only [G]
    rw [dslope_of_ne _ hm,slope_def_field,sub_neg_eq_add,(hK p hp4 (by linarith)).2]
    dsimp only [L] at *
    simp only [div_eq_mul_inv] at *
    linear_combination -(negativeHalfLineLaplace (cx F) p) * hz - ht

#print axioms exists_analyticOnNhd_regular_ordinaryPrimeHead

end GaloisForLFunctions.ExclusionOfTheCriticalState
