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
    have hcu : -(c*u) ≤ -(2*u) := by
      nlinarith only [mul_nonneg (show 0 ≤ 2-c by linarith) (show 0 ≤ -u by linarith)]
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
  have hkpos : ∀ᶠ k : ℝ in 𝓝[>] 0, 0 < k := self_mem_nhdsWithin
  have hnear : Tendsto (fun k : ℝ => k^2) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have he : Tendsto (fun k : ℝ => k^2) (𝓝 0) (𝓝 ((0:ℝ)^2)) :=
        (tendsto_id (x := 𝓝 (0:ℝ))).pow 2
      simpa using he.mono_left nhdsWithin_le_nhds
    · exact hkpos.mono fun k hk => sq_pos_of_pos hk
  have hlog : ∀ᶠ h : ℝ in 𝓝[>] 0, 1 ≤ Real.log (1/h) := by
    simpa only [one_div, Function.comp_apply] using
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually_ge_atTop 1
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
  apply (mul_le_mul_iff_right₀ (show 0 < k from hk)).mp
  nlinarith only [hinc, hsmall]

/-- Sum the Fourier mass on geometric shells. A translation by the reciprocal of the
outer radius detects every frequency in the shell with a uniformly positive weight. -/
private theorem integrable_log_moments_of_increment {G : ℝ → ℝ}
    (hg : CriticalHalfLineEnergyDomain G) {K : ℝ}
    (hK : ∀ᶠ k : ℝ in 𝓝[>] 0, (∫ u, (G u - G (u+k^2)) ^ 2) ≤ K*k) (m : ℕ) :
    Integrable fun t : ℝ => Real.log (|t|+4)^m * ‖paperFT (cx G) t‖^2 := by
  let P := fun t : ℝ => ‖paperFT (cx G) t‖^2
  have hP : Integrable P := integrable_norm_sq_paperFT_cx hg.integrable hg.sq
  have hP0 (t : ℝ) : 0 ≤ P t := sq_nonneg _
  let S := fun n : ℕ => {t : ℝ | 4^n ≤ |t|+4 ∧ |t|+4 < 4^(n+1)}
  have hS (n) : MeasurableSet (S n) :=
    (measurableSet_le measurable_const (continuous_abs.measurable.add measurable_const)).inter
      (measurableSet_lt (continuous_abs.measurable.add measurable_const) measurable_const)
  have hcover : ⋃ n, S n = univ := by
    apply eq_univ_of_forall
    intro t
    exact mem_iUnion.mpr (exists_nat_pow_near (show 1 ≤ |t|+4 by linarith [abs_nonneg t])
      (show (1:ℝ)<4 by norm_num))
  let a := fun n : ℕ => (1/2:ℝ)^(n+1)
  have ha : Tendsto a atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ))
        (by norm_num)).comp (tendsto_add_atTop_nat 1)
    · exact Eventually.of_forall fun n => pow_pos (by norm_num : (0:ℝ)<1/2) (n+1)
  have hshell : ∀ᶠ n in atTop, ∫ t in S n, P t ≤ (256*Real.pi*K)*a n := by
    filter_upwards [ha.eventually hK, eventually_ge_atTop 2] with n hn hn2
    let h := (a n)^2
    have hh : 0 < h := sq_pos_of_pos (pow_pos (by norm_num : 0<(1/2:ℝ)) _)
    have eid : h*4^(n+1) = 1 := by
      dsimp [h, a]
      rw [pow_right_comm, ← mul_pow]
      norm_num
    have h8 : (8:ℝ) ≤ 4^n := le_trans (by norm_num : (8:ℝ) ≤ 4^2)
      (pow_le_pow_right₀ (by norm_num) hn2)
    let Q := fun t : ℝ => (1-Real.cos (h*t))*P t
    have hQ : Integrable Q := integrable_one_sub_cos_mul hP h
    have hQ0 (t : ℝ) : 0 ≤ Q t := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (hP0 t)
    have hs := setIntegral_mono_on hP.integrableOn (hQ.const_mul 256).integrableOn (hS n)
      (g := fun t => 256*Q t) (fun t (ht : 4^n ≤ |t|+4 ∧ |t|+4 < 4^(n+1)) => by
        have hhi : |h*t| ≤ 1 := by
          rw [abs_mul, abs_of_pos hh, ← eid]
          exact mul_le_mul_of_nonneg_left (by linarith only [ht.2]) hh.le
        have hlow : 1/8 ≤ |h*t| := by
          have hb : (4:ℝ)^(n+1) ≤ 8*|t| := by rw [pow_succ]; linarith only [ht.1, h8]
          rw [abs_mul, abs_of_pos hh]
          linarith only [mul_le_mul_of_nonneg_left hb hh.le, eid]
        have hw := sq_div_four_le_one_sub_cos hhi
        have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/8) hlow 2
        rw [sq_abs] at hsq
        have hw' : 1 ≤ 256 * (1-Real.cos (h*t)) := by linarith only [hsq, hw]
        exact (le_mul_of_one_le_left (hP0 t) hw').trans_eq (mul_assoc _ _ _))
    rw [integral_const_mul] at hs
    have hglobal := setIntegral_le_integral (s := S n) hQ (Eventually.of_forall hQ0)
    have hid : (∫ t, Q t) = Real.pi * ∫ u, (G u-G (u+h))^2 :=
      integral_one_sub_cos_mul_norm_sq_paperFT hg hh.le
    change (∫ u, (G u-G (u+h))^2) ≤ K*a n at hn
    linarith only [hs, hglobal, hid, mul_le_mul_of_nonneg_left hn Real.pi_pos.le]
  let L := fun t : ℝ => Real.log (|t|+4)^m
  let b := fun n : ℕ => (((n+1:ℕ):ℝ)*Real.log 4)^m
  have hL0 (t) : 0 ≤ L t := pow_nonneg (Real.log_nonneg (by linarith [abs_nonneg t])) _
  have hL (n) (t : ℝ) (ht : t ∈ S n) : L t ≤ b n := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by linarith [abs_nonneg t]))
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith [abs_nonneg t]) ht.2.le
  have hb (n) : 0 ≤ b n := pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) _
  have hm : AEStronglyMeasurable (fun t => L t * P t) volume :=
    (by fun_prop : Measurable L).aestronglyMeasurable.mul hP.aestronglyMeasurable
  have hnorm (t) : ‖L t*P t‖ = L t*P t := Real.norm_of_nonneg (mul_nonneg (hL0 t) (hP0 t))
  have hi (n) : IntegrableOn (fun t => L t*P t) (S n) := by
    apply ((hP.const_mul (b n)).integrableOn).mono' hm.restrict
    apply (ae_restrict_iff' (hS n)).mpr (Eventually.of_forall fun t ht => ?_)
    rw [hnorm]
    exact mul_le_mul_of_nonneg_right (hL n t ht) (hP0 t)
  have hgeom := (summable_pow_mul_geometric_of_norm_lt_one m
    (by norm_num : ‖(1/2:ℝ)‖ < 1)).comp_injective Nat.succ_injective
  have hseries : Summable fun n => b n * ((256*Real.pi*K)*a n) := by
    refine (hgeom.mul_left ((Real.log 4)^m * (256*Real.pi*K))).congr fun n => ?_
    dsimp [b, a]
    rw [mul_pow]
    ring
  apply integrableOn_univ.mp
  rw [← hcover]
  apply integrableOn_iUnion_of_summable_integral_norm hi
  apply hseries.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hshell] with n hn
  simp only [hnorm, Real.norm_of_nonneg (setIntegral_nonneg (hS n)
    (fun t _ => mul_nonneg (hL0 t) (hP0 t)))]
  refine (setIntegral_mono_on (hi n) ((hP.const_mul (b n)).integrableOn) (hS n)
    (g := fun t => b n * P t) (fun t ht => mul_le_mul_of_nonneg_right (hL n t ht) (hP0 t))).trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left hn (hb n)

/-- Every logarithmic square-mass moment exists on the reflected lines `-1 ≤ Re p ≤ 0`. -/
theorem integrable_log_pow_mul_norm_sq_reflected_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (m : ℕ) : Integrable fun t : ℝ => Real.log (|t|+4)^m *
      ‖negativeHalfLineLaplace (cx F) (((-c:ℝ):ℂ) + (t:ℂ)*I)‖^2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hg := criticalHalfLineEnergyDomain_exp_mul_groundState hW ht hF hc hc1
  obtain ⟨K, hK⟩ := criticalState_eventually_tilted_sq_increment_le hW ht hF hc hc1
  have e : (fun u => Real.exp (-c * min u 0) * F u) = fun u => Real.exp (-(c*u)) * F u := by
    funext u
    rcases le_total u 0 with hu | hu
    · simp only [min_eq_left hu, neg_mul]
    · simp only [hd.support u hu, mul_zero]
  simp only [negativeHalfLineLaplace_add_mul_I_eq_paperFT hd.support, e]
  exact integrable_log_moments_of_increment hg hK m

/-- The reflected regular Euler multiplier times the actual state trace is square
integrable on every line between the zero abscissa and `c = 1`. -/
theorem integrable_norm_sq_reflected_euler_mul_laplace {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {c : ℝ}
    (hc : zetaZeroAbscissa - 1/2 < c) (hc1 : c ≤ 1) :
    Integrable fun t : ℝ => ‖zetaRegularLogDeriv (1/2 + ((c:ℂ) - (t:ℂ)*I)) *
      negativeHalfLineLaplace (cx F) (((-c:ℝ):ℂ) + (t:ℂ)*I)‖^2 := by
  let κ := zetaZeroAbscissa - 1/2
  have hκ : 0 ≤ κ := sub_nonneg.mpr half_le_zetaZeroAbscissa
  have hz (q : XiZeroCopy) : (centredZero q).re ≤ κ := by
    have h := re_le_zetaZeroAbscissa (riemannZeta_xiZeroCopy_eq_zero q)
    simpa [centredZero, κ] using sub_le_sub_right h (1/2)
  obtain ⟨C, hC, hN⟩ := exists_norm_zetaRegularLogDeriv_half_add_le_log hκ hz hc
  have hL := integrable_log_pow_mul_norm_sq_reflected_laplace hW ht hF (hκ.trans hc.le) hc1 2
  let p := fun t : ℝ => (c:ℂ) - (t:ℂ)*I
  have hp (t) : (p t).re = c := by simp [p]
  have him (t) : (p t).im = -t := by simp [p]
  have hcont : Continuous fun t => zetaRegularLogDeriv (1/2+p t) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (differentiableAt_zetaRegularLogDeriv_half_add hκ hz (by rwa [hp] : κ < (p t).re)
      ).continuousAt.comp (by dsimp [p]; fun_prop : ContinuousAt p t)
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hG : Integrable fun u => Real.exp (-c * min u 0) * F u := by
    apply (criticalHalfLineEnergyDomain_exp_mul_groundState hW ht hF (hκ.trans hc.le) hc1).integrable.congr
    apply Eventually.of_forall
    intro u
    rcases le_total u 0 with hu | hu
    · simp [min_eq_left hu, neg_mul]
    · simp [hd.support u hu]
  have htcont : Continuous fun t : ℝ => negativeHalfLineLaplace (cx F) (((-c:ℝ):ℂ) + (t:ℂ)*I) := by
    simp only [negativeHalfLineLaplace_add_mul_I_eq_paperFT hd.support]
    exact continuous_paperFT_cx hG
  apply (hL.const_mul (C^2)).mono' ((hcont.mul htcont).norm.pow 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖‖zetaRegularLogDeriv (1/2 + p t) *
    negativeHalfLineLaplace (cx F) (((-c:ℝ):ℂ) + (t:ℂ)*I)‖^2‖ ≤ _
  rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
  have h := hN (p t) (hp t).ge
  rw [him, abs_neg] at h
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [mul_pow] at h2
  exact (mul_le_mul_of_nonneg_right h2 (sq_nonneg _)).trans_eq (mul_assoc _ _ _)

#print axioms criticalState_eventually_tilted_sq_increment_le
#print axioms integrable_log_pow_mul_norm_sq_reflected_laplace
#print axioms integrable_norm_sq_reflected_euler_mul_laplace

end GaloisForLFunctions.ExclusionOfTheCriticalState
