import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheUnheatedStateIsTheSumOfItsZeroModes
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheProperPrimePowersInThePrimeWave

/-!
# Unheated zero modes of the physical prime wave

Reflection of the zero index reverses the frequency and growth of each
exponential. The unheated profile beyond the wall is its Hilbert sum on
the unit damping line. After polar subtraction, removing the full left-zero
contribution from the ordinary-prime wave leaves finite square mass under
every positive damping exponent up to one.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem centredZero_mirror (q : XiZeroCopy) :
    centredZero (xiZeroCopyReflectEquiv q) = -centredZero q := by
  simp only [centredZero,xiZeroCopy_reflect_val]; ring

private theorem re_centredZero_lt_one (q : XiZeroCopy) : (centredZero q).re < 1 :=
  (abs_lt.mp (abs_re_centredZero_lt q)).2.trans (by norm_num)

private theorem summable_reflected_density_mass {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable fun q => (xiLineTwoLogDerivConstant + Real.log (|(centredZero (xiZeroCopyReflectEquiv q)).im|+4)) *
      ‖negativeHalfLineLaplace (cx F) (centredZero q)‖^2 := by
  simpa only [centredZero_mirror,Complex.neg_im,abs_neg] using criticalState_summable_zero_density_mass hW ht hF

/-- The unheated profile on the unit damping line is synthesized directly
from its zero coefficients, with the sign and exponent reversed across the wall. -/
theorem criticalState_hasSum_unheated_beyondWall_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) •
      zeroRayFeature 1 (xiZeroCopyReflectEquiv q) (re_centredZero_lt_one _))
      ((criticalAliasCoefficient W₀ : ℂ) • unitLeftDatum W₀ (criticalHalfLineEnergyDomain_of_groundState hF)) := by
  let c := fun q => negativeHalfLineLaplace (cx F) (centredZero q)
  let a : ℂ := criticalAliasCoefficient W₀
  let D := unitLeftDatum W₀ (criticalHalfLineEnergyDomain_of_groundState hF)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive hW).ne'
  have hc := summable_reflected_density_mass hW ht hF
  obtain ⟨U,hU⟩ := summable_zeroRayFeature_of_log_mass xiZeroCopyReflectEquiv.toEmbedding c
    (b := 1/2) (s := 1) (by norm_num) (fun q => (abs_lt.mp (abs_re_centredZero_lt _)).2.le) hc
  have he : U = a • D := by
    apply halfLine_eq_of_feature_readings
    intro w hw
    let p := -(w+1)-8
    have hxi : xi (1/2 + (p+8)) ≠ 0 := by
      intro hh
      obtain ⟨q,hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hh
      have hh' := xiZeroCopy_re_pos q
      rw [hq] at hh'
      simp [p] at hh'
      linarith
    have h := (criticalState_hasSum_stateMeromorphic hW ht hF hxi).mul_left a
    have hscalar : HasSum (fun q => c q*(w+1+centredZero q)⁻¹) (a*stateMeromorphic W₀ F p) := by
      refine h.congr_fun fun q => ?_
      symm
      have e : p+8-centredZero q = -(w+1+centredZero q) := by dsimp [p]; ring
      change a*(-a⁻¹*(c q*(p+8-centredZero q)⁻¹)) = _
      rw [e,inv_neg]
      calc _ = (a*a⁻¹)*(c q*(w+1+centredZero q)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ ha,one_mul]
    have hu : HasSum (fun q => c q*(w+1+centredZero q)⁻¹) (inner ℂ (halfLineLaplaceFeature w hw) U) := by
      refine (hU.mapL (innerSL ℂ (halfLineLaplaceFeature w hw))).congr_fun fun q => ?_
      symm
      change inner ℂ _ (c q • zeroRayFeature 1 (xiZeroCopyReflectEquiv q) _) = _
      rw [inner_smul_right,inner_zeroRayFeature,centredZero_mirror]
      simp
    rw [inner_smul_right,hu.unique hscalar]
    exact congrArg (a * ·) ((stateMeromorphic_eq_laplaceRay_left
      (criticalHalfLineEnergyDomain_of_groundState hF) (c := 1) (by norm_num) (by norm_num) hw).trans
      (halfLineLaplaceTransform_eq_laplaceRay D hw).symm)
  rw [← he]
  exact hU

/-- After removal of a finite left layer, the raw wall profile has finite
square mass with every damping exponent above the remaining growth rates. -/
theorem criticalState_memLp_beyondWall_sub_finite_unheated_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (S : Finset XiZeroCopy)
    {b s : ℝ} (hbs : b < s) (hs : s ≤ 1) (hb : ∀ q ∉ S, -(centredZero q).re ≤ b) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((criticalAliasCoefficient W₀ : ℂ)*beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) t -
       ∑ q ∈ S, negativeHalfLineLaplace (cx F) (centredZero q)*Complex.exp (-(centredZero q)*(t:ℂ))))
      2 halfLineLaplaceMeasure := by
  let c := fun q => negativeHalfLineLaplace (cx F) (centredZero q)
  let a : ℂ := criticalAliasCoefficient W₀
  let D := unitLeftDatum W₀ (criticalHalfLineEnergyDomain_of_groundState hF)
  have hc := summable_reflected_density_mass hW ht hF
  have h := memLp_sub_finite_zero_layer xiZeroCopyReflectEquiv.toEmbedding c hs
    (fun q => re_centredZero_lt_one _) S hbs (fun q hq => by simpa [centredZero_mirror] using hb q hq)
    hc (criticalState_hasSum_unheated_beyondWall_modes hW ht hF)
  refine MemLp.ae_eq ?_ h
  filter_upwards [Lp.coeFn_smul a D] with t ht
  have hm (q) : Complex.exp ((centredZero (xiZeroCopyReflectEquiv q)-1)*(t:ℂ)) =
      Complex.exp (-(t:ℂ))*Complex.exp (-(centredZero q)*(t:ℂ)) := by
    rw [centredZero_mirror,← Complex.exp_add]; congr 1; ring
  have h1 : (Real.exp ((1-s)*t):ℂ)*Complex.exp (-(t:ℂ)) = expRay (s:ℂ) t := by
    rw [Complex.ofReal_exp,← Complex.exp_add]; unfold expRay; congr 1; push_cast; ring
  have h2 : expRay (s:ℂ) t * Complex.exp (t:ℂ) = (Real.exp ((1-s)*t):ℂ) := by
    unfold expRay; rw [← Complex.exp_add,Complex.ofReal_exp]; congr 1; push_cast; ring
  change (Real.exp ((1-s)*t):ℂ)*((a • D) t -
    ∑ q ∈ S, c q*Complex.exp ((centredZero (xiZeroCopyReflectEquiv q)-1)*(t:ℂ))) =
    expRay (s:ℂ) t * (a*(Complex.exp (t:ℂ)*D t) -
      ∑ q ∈ S, c q*Complex.exp (-(centredZero q)*(t:ℂ)))
  simp only [ht,Pi.smul_apply,smul_eq_mul,hm,
    show ∀ (d z : ℂ), d*(Complex.exp (-(t:ℂ))*z) = Complex.exp (-(t:ℂ))*(d*z) by intros; ring,
    ← Finset.mul_sum]
  linear_combination -(a*D t)*h2 -
    (∑ q ∈ S, c q*Complex.exp (-(centredZero q)*(t:ℂ)))*h1

private theorem memLp_prime_sum_of_wall_remainder {W₀ : ℝ} (hW : 0 < W₀)
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs0 : 0 < s) (P : ℝ → ℂ)
    (h : MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((criticalAliasCoefficient W₀:ℂ)*beyondWallProfile W₀ (criticalHalfLineEnergyDomain_of_groundState hF) t - P t))
      2 halfLineLaplaceMeasure) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)) -
        negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) + P t)) 2 halfLineLaplaceMeasure := by
  let hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hp := h.neg
  have hJ := memLp_dampedLevyHeadProfile hd hs0.le
  have hE := (memLp_two_expRay_restrict (w := (s:ℂ)+1/2) (by simp; linarith) 0).const_mul
    (negativeHalfLineLaplace (cx F) (1/2))
  refine MemLp.ae_eq ?_ ((hp.sub hJ).add hE)
  filter_upwards [beyondWallProfile_primeForm hW hd] with t ht
  have he : expRay ((s:ℂ)+1/2) t = expRay (s:ℂ) t * (Real.exp (-(t/2)):ℂ) := by
    unfold expRay; rw [Complex.ofReal_exp,← Complex.exp_add]; congr 1; push_cast; ring
  change -(expRay (s:ℂ) t * (_ - _)) - levyHeadProfile F t * expRay (s:ℂ) t +
    negativeHalfLineLaplace (cx F) (1/2)*expRay ((s:ℂ)+1/2) t = _
  rw [he]
  linear_combination (expRay (s:ℂ) t)*ht.2

/-- The damped signed prime sum after polar subtraction and removal of its
finite left-zero oscillation is square-integrable at the residual rate. -/
theorem criticalState_memLp_prime_sum_sub_pole_add_finite_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (S : Finset XiZeroCopy)
    {b s : ℝ} (hbs : b < s) (hs0 : 0 < s) (hs : s ≤ 1)
    (hb : ∀ q ∉ S, -(centredZero q).re ≤ b) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)) -
       negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) +
       ∑ q ∈ S, negativeHalfLineLaplace (cx F) (centredZero q)*Complex.exp (-(centredZero q)*(t:ℂ))))
      2 halfLineLaplaceMeasure := by
  exact memLp_prime_sum_of_wall_remainder hW hF hs0 _
    (criticalState_memLp_beyondWall_sub_finite_unheated_modes hW ht hF S hbs hs hb)

private theorem memLp_ordinary_of_prime_sum {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs0 : 0 < s) (P : ℝ → ℂ)
    (h : MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)) -
        negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) + P t)) 2 halfLineLaplaceMeasure) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' p : Nat.Primes, (primeAtom (p:ℕ):ℂ)*(F (t-Real.log (p:ℕ)):ℂ)) -
        negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) + P t)) 2 halfLineLaplaceMeasure := by
  have hp := criticalState_memLp_damped_properPowerWave hW ht hF hs0
  refine MemLp.ae_eq ?_ (h.sub hp)
  filter_upwards [beyondWallProfile_primeForm hW (criticalHalfLineEnergyDomain_of_groundState hF)] with t hφ
  let f := fun n : ℕ => (primeAtom n:ℂ)*(F (t-Real.log n):ℂ)
  have hsupp : Function.support f ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hh
    have hv := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr (show ¬ IsPrimePow n from hh)
    exact hn (by simp [f,primeAtom,hv])
  have he := tsum_eq_ordinary_primes_add_proper_powers (f := f) hφ.1 hsupp
  change expRay (s:ℂ) t * ((∑' n, f n)-_+_) -
    expRay (s:ℂ) t * (∑' j, f (properPrimePowerIndex j)) =
    expRay (s:ℂ) t * ((∑' p : Nat.Primes, f (p:ℕ))-_+_)
  rw [he]; ring

/-- The ordinary primes alone, after polar subtraction and removal of the
finite left-zero oscillation, have the same residual square-mean bound. -/
theorem criticalState_memLp_ordinary_prime_sum_sub_pole_add_finite_modes {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (S : Finset XiZeroCopy)
    {b s : ℝ} (hbs : b < s) (hs0 : 0 < s) (hs : s ≤ 1)
    (hb : ∀ q ∉ S, -(centredZero q).re ≤ b) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' p : Nat.Primes, (primeAtom (p:ℕ):ℂ)*(F (t-Real.log (p:ℕ)):ℂ)) -
       negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) +
       ∑ q ∈ S, negativeHalfLineLaplace (cx F) (centredZero q)*Complex.exp (-(centredZero q)*(t:ℂ))))
      2 halfLineLaplaceMeasure := by
  exact memLp_ordinary_of_prime_sum hW ht hF hs0 _
    (criticalState_memLp_prime_sum_sub_pole_add_finite_modes hW ht hF S hbs hs0 hs hb)

/-- The left-zero part of the wall datum on the unit damping line. -/
def unheatedLeftZeroDatum (F : ℝ → ℝ) : HalfLineLaplaceL2 :=
  ∑' q : {q : XiZeroCopy // (centredZero q).re < 0},
    negativeHalfLineLaplace (cx F) (centredZero q) •
      zeroRayFeature 1 (xiZeroCopyReflectEquiv q) (re_centredZero_lt_one _)

/-- After its complete left-zero subseries is removed, the ordinary-prime
wave minus its pole has finite square mass with every small positive damping.
The statement holds for arbitrary off-line support. -/
theorem criticalState_memLp_ordinary_prime_remainder_after_left_zeros {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {s : ℝ} (hs0 : 0 < s) (hs : s ≤ 1) :
    MemLp (fun t : ℝ => expRay (s:ℂ) t *
      ((∑' p : Nat.Primes, (primeAtom (p:ℕ):ℂ)*(F (t-Real.log (p:ℕ)):ℂ)) -
        negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ) +
        Complex.exp (t:ℂ)*unheatedLeftZeroDatum F t)) 2 halfLineLaplaceMeasure := by
  let c := fun q => negativeHalfLineLaplace (cx F) (centredZero q)
  let a : ℂ := criticalAliasCoefficient W₀
  let D := unitLeftDatum W₀ (criticalHalfLineEnergyDomain_of_groundState hF)
  have hc := summable_reflected_density_mass hW ht hF
  have hraw := memLp_sub_zero_layer xiZeroCopyReflectEquiv.toEmbedding c hs
    (fun q => re_centredZero_lt_one _) {q | (centredZero q).re < 0} hs0
    (fun q hq => by
      have hnonneg : 0 ≤ (centredZero q).re := le_of_not_gt (show ¬ (centredZero q).re < 0 from hq)
      simpa [centredZero_mirror] using neg_nonpos.mpr hnonneg) hc
    (criticalState_hasSum_unheated_beyondWall_modes hW ht hF)
  apply memLp_ordinary_of_prime_sum hW ht hF hs0
  apply memLp_prime_sum_of_wall_remainder hW hF hs0
  apply MemLp.ae_eq _ hraw
  filter_upwards [Lp.coeFn_smul a D] with t ht
  change (Real.exp ((1-s)*t):ℂ)*((a • D) t-unheatedLeftZeroDatum F t) =
    expRay (s:ℂ) t*(a*(Complex.exp (t:ℂ)*D t)-Complex.exp (t:ℂ)*unheatedLeftZeroDatum F t)
  have hE : expRay (s:ℂ) t * Complex.exp (t:ℂ) = (Real.exp ((1-s)*t):ℂ) := by
    unfold expRay; rw [← Complex.exp_add,Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [ht,Pi.smul_apply,smul_eq_mul,← hE]
  ring

#print axioms criticalState_memLp_ordinary_prime_remainder_after_left_zeros
#print axioms criticalState_memLp_ordinary_prime_sum_sub_pole_add_finite_modes
#print axioms criticalState_hasSum_unheated_beyondWall_modes
#print axioms criticalState_memLp_prime_sum_sub_pole_add_finite_modes

end GaloisForLFunctions.ExclusionOfTheCriticalState
