import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.DilatingTheOrdinaryPrimeMeasure
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheModulusOfContinuityOfTheStateIsCarriedByTheWall
import GaloisForLFunctions.HTGeometry.ReflectionIntegral
import GaloisForLFunctions.RHTower.EulerFisherCurvature

/-!
# The equal-prime term of the ordinary-prime covariance

The squared atom weights contribute one extra logarithm. Writing this logarithm
as the observation time minus the profile coordinate reduces the covariance
to two tests of the dilated prime measure. Its leading kernel is precisely
the translation correlation of the confined state.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

private def reciprocalPrimeTerm (ψ : ℝ → ℝ) (t : ℝ) (p : Nat.Primes) :=
  Real.log (p:ℕ) / (p:ℕ) * ψ (t-Real.log (p:ℕ))

private def logDilation (ψ : ℝ → ℝ) (y : ℝ) : ℝ := ψ (-Real.log (max 1 y)) / max 1 y

private theorem logDilation_of_pos {ψ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → ψ u = 0) {y : ℝ} (hy : 0 < y) :
    logDilation ψ y = ψ (-Real.log y)/y := by
  rcases le_or_gt 1 y with h | h
  · simp only [logDilation,max_eq_right h]
  · simp only [logDilation,max_eq_left h.le,Real.log_one,neg_zero,hs 0 le_rfl,zero_div,
      hs _ (neg_nonneg.mpr (Real.log_nonpos hy.le h.le))]

private theorem exp_two_sub_log (t : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.exp (2*(t-Real.log x)) = Real.exp (2*t)/x^2 := by
  rw [mul_sub,Real.exp_sub,two_mul (Real.log x),Real.exp_add,Real.exp_log hx,sq]

private theorem summable_reciprocalPrimeTerm {ψ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |ψ u| ≤ C*Real.exp (2*u)) (t : ℝ) : Summable (reciprocalPrimeTerm ψ t) := by
  have h := (GaloisForLFunctions.summable_log_nat_div_sq.comp_injective
    (show Function.Injective fun p : Nat.Primes => (p:ℕ) from Subtype.coe_injective)).mul_left
      (C*Real.exp (2*t))
  refine Summable.of_norm_bounded h fun p => ?_
  have hp : (1:ℝ) ≤ (p:ℕ) := by exact_mod_cast p.property.one_le
  have hp0 := zero_lt_one.trans_le hp
  have hl := Real.log_nonneg hp
  rw [reciprocalPrimeTerm,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hl hp0.le)]
  have hc := hb (t-Real.log (p:ℕ))
  rw [exp_two_sub_log _ hp0] at hc
  calc _ ≤ (Real.log (p:ℕ)/(p:ℕ))*(C*(Real.exp (2*t)/(p:ℕ)^2)) :=
           mul_le_mul_of_nonneg_left hc (div_nonneg hl hp0.le)
    _ ≤ Real.log (p:ℕ)*(C*(Real.exp (2*t)/(p:ℕ)^2)) :=
           mul_le_mul_of_nonneg_right (div_le_self hl hp) (by positivity)
    _ = _ := by dsimp [Function.comp_def]; ring

/-- Logarithmic reciprocal prime weights sample Lebesgue measure on translates
of every continuous exponentially decaying test supported on the negative ray. -/
private theorem tendsto_reciprocalPrimeSum {ψ : ℝ → ℝ} (hψ : Continuous ψ)
    (hs : ∀ u, 0 ≤ u → ψ u = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |ψ u| ≤ C*Real.exp (2*u)) :
    Tendsto (fun t : ℝ => ∑' p : Nat.Primes, reciprocalPrimeTerm ψ t p) atTop (𝓝 (∫ u, ψ u)) := by
  have hmax : Continuous (fun y : ℝ => max 1 y) := continuous_const.max continuous_id
  have hpos (y : ℝ) : 0 < max 1 y := zero_lt_one.trans_le (le_max_left _ _)
  have hg : Continuous (logDilation ψ) :=
    (hψ.comp (hmax.log (fun y => (hpos y).ne')).neg).div hmax fun y => (hpos y).ne'
  have hbound (y : ℝ) (_ : 0 ≤ y) : |logDilation ψ y| ≤ (2*C)/(1+y^2) := by
    rcases le_or_gt y 1 with hy | hy
    · simp only [logDilation,max_eq_left hy,Real.log_one,neg_zero,hs 0 le_rfl,zero_div,abs_zero]
      positivity
    · have hy0 := zero_lt_one.trans hy
      rw [logDilation_of_pos hs hy0,abs_div,abs_of_pos hy0]
      have hh := hb (-Real.log y)
      rw [show 2*(-Real.log y) = 2*(0-Real.log y) by ring,exp_two_sub_log 0 hy0,mul_zero,Real.exp_zero] at hh
      have hsqu : 1 ≤ y^2 := one_le_pow₀ hy.le
      calc _ ≤ |ψ (-Real.log y)| := div_le_self (abs_nonneg _) hy.le
        _ ≤ C*(1/y^2) := hh
        _ ≤ _ := by
          rw [mul_one_div,div_le_div_iff₀ (sq_pos_of_pos hy0) (by positivity)]
          nlinarith only [mul_nonneg hC (sub_nonneg.mpr hsqu)]
  have hI : (∫ y in Ici (0:ℝ), logDilation ψ y) = ∫ u, ψ u := by
    rw [integral_Ici_eq_integral_Ioi,HTGeometry.integral_Ioi_comp_exp]
    calc _ = ∫ r : ℝ, ψ (-r) := by
           apply integral_congr_ae (Eventually.of_forall fun r => ?_)
           rw [logDilation_of_pos hs (Real.exp_pos _),Real.log_exp]
           field_simp
      _ = _ := integral_neg_eq_self ψ volume
  have hh := (tendsto_dilated_ordinary_prime_sum hg (by positivity) hbound).comp Real.tendsto_exp_atTop
  rw [hI] at hh
  apply hh.congr fun t => ?_
  change (∑' p : Nat.Primes, Real.log (p:ℕ)*logDilation ψ ((p:ℕ)/Real.exp t))/Real.exp t = _
  rw [← tsum_div_const]
  apply tsum_congr fun p => ?_
  have hp : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.property.pos
  rw [logDilation_of_pos hs (div_pos hp (Real.exp_pos t)),Real.log_div hp.ne' (Real.exp_ne_zero t),
    Real.log_exp,neg_sub,reciprocalPrimeTerm]
  field_simp

/-- Product of the two ordinary-prime atom weights at equal primes, at lag h. -/
def equalPrimeCovariance (Φ : ℝ → ℝ) (h t : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((Real.log (p:ℕ))^2 / (p:ℕ)) *
    (Φ (t-Real.log (p:ℕ)) * Φ (t+h-Real.log (p:ℕ)))

private theorem diagonal_of_representative {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hs : ∀ u, 0 ≤ u → Φ u = 0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (h : ℝ) :
    Tendsto (fun t : ℝ => equalPrimeCovariance Φ h t / t) atTop (𝓝 (∫ u, Φ u*Φ (u+h))) := by
  let ψ := fun u : ℝ => Φ u*Φ (u+h)
  let U := fun u : ℝ => u*ψ u
  let K := C^2*Real.exp (2*h)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hm (u : ℝ) : |ψ u| ≤ K*Real.exp (4*u) := by
    rw [show |ψ u| = |Φ u| * |Φ (u+h)| by exact abs_mul ..]
    calc _ ≤ (C*Real.exp (2*u))*(C*Real.exp (2*(u+h))) :=
           mul_le_mul (hb _) (hb _) (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [show 2*(u+h) = 2*h+2*u by ring,Real.exp_add,
          show 4*u = 2*u+2*u by ring,Real.exp_add]
        dsimp only [K]; ring
  have hsψ (u : ℝ) (hu : 0 ≤ u) : ψ u = 0 := by simp [ψ,hs u hu]
  have hsU (u : ℝ) (hu : 0 ≤ u) : U u = 0 := by simp [U,hsψ u hu]
  have hbψ (u : ℝ) : |ψ u| ≤ K*Real.exp (2*u) := by
    rcases le_or_gt 0 u with hu | hu
    · rw [hsψ u hu,abs_zero]; positivity
    · exact (hm u).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK)
  have hbU (u : ℝ) : |U u| ≤ K*Real.exp (2*u) := by
    rcases le_or_gt 0 u with hu | hu
    · rw [hsU u hu,abs_zero]; positivity
    · have ha : |u| ≤ Real.exp (-u) := by rw [abs_of_neg hu]; linarith [Real.add_one_le_exp (-u)]
      rw [show |U u| = |u| * |ψ u| from abs_mul ..]
      calc _ ≤ Real.exp (-u)*(K*Real.exp (4*u)) :=
             mul_le_mul ha (hm _) (abs_nonneg _) (Real.exp_pos _).le
        _ = K*Real.exp (-u+4*u) := by rw [Real.exp_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hK
  have hcψ : Continuous ψ := hc.mul (hc.comp (continuous_id.add_const h))
  have h1 := tendsto_reciprocalPrimeSum hcψ hsψ hK hbψ
  have h2 := tendsto_reciprocalPrimeSum (continuous_id.mul hcψ : Continuous U) hsU hK hbU
  have he (t : ℝ) : equalPrimeCovariance Φ h t =
      t*(∑' p, reciprocalPrimeTerm ψ t p) - ∑' p, reciprocalPrimeTerm U t p := by
    rw [← tsum_mul_left,← ((summable_reciprocalPrimeTerm hK hbψ t).mul_left t).tsum_sub
      (summable_reciprocalPrimeTerm hK hbU t)]
    apply tsum_congr fun p => ?_
    have e : t+h-Real.log (p:ℕ) = t-Real.log (p:ℕ)+h := by ring
    simp only [reciprocalPrimeTerm,U,ψ,e]
    ring
  have hh := h1.sub (h2.div_atTop tendsto_id)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [he,sub_div,mul_div_cancel_left₀ _ ht.ne']
  rfl

/-- The equal-prime covariance of the actual critical state grows linearly
with coefficient equal to its full translation autocorrelation at every lag. -/
theorem criticalState_equalPrimeCovariance {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧ ∀ h : ℝ,
      Tendsto (fun t : ℝ => equalPrimeCovariance Φ h t / t) atTop (𝓝 (∫ u : ℝ, F u*F (u+h))) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine ⟨Φ,hΦ,heq,fun h => ?_⟩
  have hv : (∫ u : ℝ, F u*F (u+h)) = ∫ u : ℝ, Φ u*Φ (u+h) := by
    apply integral_congr_ae
    filter_upwards [heq,(measurePreserving_add_right volume h).quasiMeasurePreserving.ae heq] with u h1 h2
    rw [h1,show F (u+h) = Φ (u+h) from h2]
  rw [hv]
  exact diagonal_of_representative hΦ hs hC hb h

/-- The equal-prime term of the squared increment at a positive lag. -/
def equalPrimeIncrement (Φ : ℝ → ℝ) (h t : ℝ) : ℝ :=
  equalPrimeCovariance (fun u => Φ u - Φ (u+h)) 0 t

/-- At zero lag the equal-prime sum has leading coefficient one. Its increment
kernel recovers the wall energy by first sending the prime scale to infinity. -/
theorem criticalState_equalPrimeIncrement_wall_energy {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      Tendsto (fun t : ℝ => equalPrimeCovariance Φ 0 t / t) atTop (𝓝 1) ∧
      (∀ h : ℝ, 0 ≤ h → Tendsto (fun t : ℝ => equalPrimeIncrement Φ h t / t) atTop
        (𝓝 (∫ u : ℝ, (F u - F (u+h))^2))) ∧
      Tendsto (fun h : ℝ => Real.log (1/h)/h * limUnder atTop
        (fun t : ℝ => equalPrimeIncrement Φ h t / t)) (𝓝[>] 0)
        (𝓝 (8 * criticalAliasCoefficient W₀ * (∫ u : ℝ, F u^2 * Real.exp (-(8*u))))) := by
  obtain ⟨_,_,Φ,hΦ,heq,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hmass : (∫ u, Φ u * Φ (u+0)) = 1 := by
    rw [← hF.2.2.2.1]
    exact integral_congr_ae (heq.mono fun u hu => by
      change Φ u * Φ (u+0) = F u^2
      rw [add_zero,hu,pow_two])
  have hi (h : ℝ) (hh : 0 ≤ h) : Tendsto (fun t : ℝ => equalPrimeIncrement Φ h t / t) atTop
      (𝓝 (∫ u, (F u - F (u+h))^2)) := by
    let D := fun u : ℝ => Φ u - Φ (u+h)
    have hcD : Continuous D := hΦ.sub (hΦ.comp (continuous_id.add_const h))
    have hsD (u : ℝ) (hu : 0 ≤ u) : D u = 0 := by simp [D,hs u hu,hs (u+h) (add_nonneg hu hh)]
    have hbd (u : ℝ) : |D u| ≤ (C+C*Real.exp (2*h))*Real.exp (2*u) := by
      calc |D u| ≤ |Φ u| + |Φ (u+h)| := abs_sub _ _
        _ ≤ _ := add_le_add (hb u) (hb (u+h))
        _ = _ := by rw [mul_add,Real.exp_add]; ring
    have hl := diagonal_of_representative hcD hsD (by positivity) hbd 0
    have hv : (∫ u, D u * D (u+0)) = ∫ u, (F u-F (u+h))^2 := by
      apply integral_congr_ae
      filter_upwards [heq,(measurePreserving_add_right volume h).quasiMeasurePreserving.ae heq] with u h1 h2
      rw [h1,show F (u+h) = Φ (u+h) from h2,add_zero,pow_two]
    rwa [hv] at hl
  refine ⟨Φ,hΦ,heq,hmass ▸ diagonal_of_representative hΦ hs hC hb 0,hi,?_⟩
  apply (criticalState_tendsto_log_div_mul_sq_increment hW ht hF).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [(hi h (le_of_lt (show 0 < h from hh))).limUnder_eq]

#print axioms criticalState_equalPrimeCovariance
#print axioms criticalState_equalPrimeIncrement_wall_energy

end GaloisForLFunctions.ExclusionOfTheCriticalState
