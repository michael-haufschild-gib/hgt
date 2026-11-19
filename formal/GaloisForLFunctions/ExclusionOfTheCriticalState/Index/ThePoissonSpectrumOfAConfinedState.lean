import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheUnitTiltOfEveryConfinedState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheCriticalStatesFormAnOrthogonalLadder
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheOnLineResolventOfAFiniteLayer
import GaloisForLFunctions.HTGeometry.FourierTranslationModulation
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# The Poisson spectrum of a confined null state

Testing with every inward translate splits the reflected off-line transform into
two Cauchy transforms of positive measures. One measures the critical-line
zeros, the other the Fourier power of the weighted state. For a finite off-line
divisor this gives inverse-square decay of the mass in each fixed-width window.
-/

noncomputable section
open MeasureTheory Set Complex FourierTransform Filter Topology Zeta23
open scoped InnerProductSpace ComplexConjugate
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-- The zero and its reflection enter the translated bare form through this product. -/
def reflectedLaplaceProduct (F : ℝ → ℝ) (q : XiZeroCopy) : ℂ :=
  negativeHalfLineLaplace (cx F) (centredZero q) * negativeHalfLineLaplace (cx F) (-centredZero q)

private def tone (x : ℝ) : ℂ := (x : ℂ) * I

private theorem re_tone (x : ℝ) : (tone x).re = 0 := by simp [tone]

private theorem confined_power_density {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F) :
    ∃ D : ℝ → ℝ, Measurable D ∧ Integrable D ∧ (∀ x, 0 ≤ D x) ∧ ∀ t : ℝ,
      ((criticalHalfLineExponentialPair F (shiftProfile F t) : ℝ) : ℂ) =
        (Real.exp (4*t) : ℂ) * ∫ x : ℝ, (D x : ℂ) * cexp (tone (2*Real.pi*x) * t) := by
  let f := confinedHalf F
  have hf : MemLp f 2 volume :=
    (memLp_two_iff_integrable_sq_norm (measurable_confinedHalf hF).aestronglyMeasurable).mpr
      (integrable_sq_confinedHalf hF)
  let H := hf.toLp f
  let G : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 H
  refine ⟨fun x => ‖G x‖^2, (Lp.stronglyMeasurable G).measurable.norm.pow_const 2,
    (memLp_two_iff_integrable_sq_norm (Lp.memLp G).aestronglyMeasurable).mp (Lp.memLp G),
    fun x => sq_nonneg _, fun t => ?_⟩
  have hc : ⟪H, translateL2 t H⟫_ℂ = profileCorrelation f f t := by
    rw [L2.inner_def, profileCorrelation]
    have hs := (measurePreserving_add_right volume t).quasiMeasurePreserving.ae_eq_comp hf.coeFn_toLp
    apply integral_congr_ae
    filter_upwards [coeFn_translateL2 t H, hf.coeFn_toLp, hs] with x hx hy hz
    change H (x+t) = f (x+t) at hz
    rw [hx,hz,hy,RCLike.inner_apply]
    simp only [f,confinedHalf,Complex.conj_ofReal,mul_comm]
  have hspec : profileCorrelation f f t = ∫ x : ℝ, ((‖G x‖^2 : ℝ) : ℂ) *
      cexp (tone (2*Real.pi*x) * t) := by
    rw [← hc, ← Lp.inner_fourier_eq H (translateL2 t H), fourierTransform_translateL2, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [coeFn_modulationMul t G] with x hx
    change ⟪G x, (modulationMul t G) x⟫_ℂ = _
    rw [hx, RCLike.inner_apply, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]
    congr 1
    unfold modulationSymbol tone
    congr 1
    push_cast
    ring
  rw [← hspec, profileCorrelation, criticalHalfLineExponentialPair, ← integral_complex_ofReal,
    ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    have he : Real.exp (4*t) * (Real.exp (-(4*u)) * Real.exp (-(4*(u+t)))) =
        Real.exp (-(8*u)) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    simp only [f,confinedHalf,shiftProfile, ← Complex.ofReal_mul]
    apply congrArg Complex.ofReal
    rw [← he]
    ring

private theorem bare_shift_at_null {R : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector R F)
    {t : ℝ} (ht : 0 ≤ t) : (bareMixedEnergy F (shiftProfile F t) : ℂ) =
      -(criticalAliasCoefficient R : ℂ) * (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ) := by
  have hs := criticalHalfLineEnergyDomain_shiftProfile hF.1 ht
  have hn := hF.2.2 (shiftProfile F t) hs
  rw [criticalHalfLineMixedEnergy_eq_bare_add, setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun u hu => by rw [hF.1.support u (not_lt.mp hu),zero_mul,zero_mul])] at hn
  change bareMixedEnergy F (shiftProfile F t) + criticalAliasCoefficient R *
    criticalHalfLineExponentialPair F (shiftProfile F t) = 0 at hn
  exact_mod_cast (show bareMixedEnergy F (shiftProfile F t) =
      -criticalAliasCoefficient R * criticalHalfLineExponentialPair F (shiftProfile F t) by linarith)

/-- The translated zero formula before Laplace transformation. -/
private theorem null_frequency_balance {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {t : ℝ} (ht : 0 ≤ t) :
    (∑' q : onLineCopies, (zeroValueMass F q : ℂ) * cexp (tone (centredZero q).im * t)) +
      (∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * cexp (centredZero q * t)) =
      -(criticalAliasCoefficient R : ℂ) * (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ) := by
  have hs := criticalHalfLineEnergyDomain_shiftProfile hF.1 ht
  have htF := (hF.tilt_domain hr zero_le_one le_rfl).causalTranslate ht
  have htG : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1*u))*shiftProfile F t u) := by
    have e : (fun u => Real.exp (-(1*u))*shiftProfile F t u) =
        fun u => Real.exp t * (Real.exp (-(1*(u+t))) * F (u+t)) := by
      funext u; rw [← mul_assoc,← Real.exp_add,shiftProfile]; congr 2; ring
    rw [e]; exact htF.const_mul _
  have hh := hasSum_mul_of_tendsto_gaussian (hF.summable_zero_traces hr).1
    (summable_norm_sq_laplace_neg_centredZero htG) (tendsto_heatedZeroPairing hF.1 hs)
  have h := (hh.summable.tsum_subtype_add_tsum_subtype_compl onLineCopies).trans hh.tsum_eq
  have hon (q : onLineCopies) :
      negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx (shiftProfile F t)) (-centredZero q) =
        (zeroValueMass F q : ℂ) * cexp (tone (centredZero q).im * t) := by
    have he : -conj (centredZero q) = tone (centredZero q).im := by
      apply Complex.ext <;> simp [tone,show (centredZero q).re = 0 from q.property]
    have hz : -centredZero q = conj (centredZero q) := by
      apply Complex.ext <;> simp [show (centredZero q).re = 0 from q.property]
    rw [hz,show cx (shiftProfile F t) = fun u => ((shiftProfile F t u : ℝ) : ℂ) from rfl,
      negativeHalfLineLaplace_real_conj]
    change _ * conj (negativeHalfLineLaplace (cx (shiftProfile F t)) (centredZero q)) = _
    rw [laplace_shiftProfile,map_mul,← Complex.exp_conj,map_neg,map_mul,Complex.conj_ofReal,
      ← neg_mul,he]
    have hm := Complex.mul_conj (negativeHalfLineLaplace (cx F) (centredZero q))
    rw [Complex.normSq_eq_norm_sq] at hm
    unfold zeroValueMass
    rw [← hm]; ring
  have hoff (q : ↑onLineCopiesᶜ) :
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx (shiftProfile F t)) (-centredZero q) =
      reflectedLaplaceProduct F q * cexp (centredZero q * t) := by
    rw [laplace_shiftProfile, neg_mul, neg_neg]
    unfold reflectedLaplaceProduct
    ring
  change (∑' q : onLineCopies, negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx (shiftProfile F t)) (-centredZero q)) +
    (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx (shiftProfile F t)) (-centredZero q)) =
    (bareMixedEnergy F (shiftProfile F t) : ℂ) at h
  simp_rw [hon,hoff] at h
  exact h.trans (bare_shift_at_null hF ht)

private def dampedTone (p z : ℂ) (t : ℝ) : ℂ := cexp ((z-p)*t)

private theorem dampedTone_integrable {z p : ℂ} (h : z.re < p.re) :
    IntegrableOn (dampedTone p z) (Ioi 0) :=
  integrableOn_exp_mul_complex_Ioi (show (z-p).re < 0 by rw [sub_re]; exact sub_neg.mpr h) 0

private theorem integral_dampedTone {z p : ℂ} (h : z.re < p.re) :
    ∫ t in Ioi (0:ℝ), dampedTone p z t = (p-z)⁻¹ := by
  unfold dampedTone
  rw [integral_exp_mul_complex_Ioi (show (z-p).re < 0 by rw [sub_re]; exact sub_neg.mpr h)]
  simp only [ofReal_zero,mul_zero,Complex.exp_zero,neg_div,one_div]
  rw [← inv_neg, neg_sub]

private theorem dampedTone_split (p z : ℂ) (t : ℝ) :
    dampedTone p z t = cexp (-(p*t)) * cexp (z*t) := by
  rw [dampedTone, ← Complex.exp_add]; congr 1; ring

/-- Fubini for the continuous positive part of the translated state. -/
private theorem integrate_power_density {D : ℝ → ℝ} (hD : Measurable D) (hi : Integrable D)
    {p : ℂ} (hp : 0 < p.re) :
    let K := fun (t x : ℝ) => (D x : ℂ) * dampedTone p (tone (2*Real.pi*x)) t
    (IntegrableOn (fun t => ∫ x, K t x) (Ioi 0)) ∧
    (Integrable fun x => (D x : ℂ) * (p-tone (2*Real.pi*x))⁻¹) ∧
    (∫ t in Ioi (0:ℝ), ∫ x, K t x) = ∫ x, (D x : ℂ) * (p-tone (2*Real.pi*x))⁻¹ := by
  intro K
  have hprod : Integrable (Function.uncurry K) ((volume.restrict (Ioi 0)).prod volume) := by
    apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hp) 0).mul_prod hi.abs).mono'
    · dsimp only [K,Function.uncurry,dampedTone,tone]
      fun_prop
    · exact Eventually.of_forall fun v => by
        change ‖(D v.2 : ℂ) * dampedTone p (tone (2*Real.pi*v.2)) v.1‖ ≤
          Real.exp (-p.re*v.1) * |D v.2|
        rw [dampedTone, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_mul_ofReal,
          Complex.sub_re,re_tone,zero_sub,mul_comm]
  have hx (x : ℝ) : ∫ t in Ioi (0:ℝ), K t x = (D x : ℂ) * (p-tone (2*Real.pi*x))⁻¹ := by
    rw [show K = fun t x => (D x : ℂ) * dampedTone p (tone (2*Real.pi*x)) t from rfl,
      integral_const_mul,integral_dampedTone (by rwa [re_tone])]
  refine ⟨hprod.integral_prod_left, hprod.integral_prod_right.congr (Eventually.of_forall hx), ?_⟩
  rw [integral_integral_swap hprod]
  exact integral_congr_ae (Eventually.of_forall hx)

private theorem integrate_line_spectrum {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 0 < p.re) :
    (IntegrableOn (fun t : ℝ => ∑' q : onLineCopies, (zeroValueMass F q : ℂ) *
      dampedTone p (tone (centredZero q).im) t) (Ioi 0)) ∧
    HasSum (fun q : onLineCopies => (zeroValueMass F q : ℂ) *
        (p-tone (centredZero q).im)⁻¹)
      (∫ t in Ioi (0:ℝ), ∑' q : onLineCopies, (zeroValueMass F q : ℂ) *
        dampedTone p (tone (centredZero q).im) t) := by
  let K := fun (q : onLineCopies) (t : ℝ) => (zeroValueMass F q : ℂ) *
      dampedTone p (tone (centredZero q).im) t
  have hi (q : onLineCopies) : IntegrableOn (K q) (Ioi 0) :=
    (dampedTone_integrable (by rwa [re_tone])).const_mul _
  have he (q : onLineCopies) : (fun t => ‖K q t‖) =
      fun t => zeroValueMass F q * Real.exp (-p.re*t) := by
    funext t
    simp only [K,dampedTone,norm_mul,Complex.norm_real,Real.norm_of_nonneg (zeroValueMass_nonneg _ _),
      Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
      Complex.sub_re,re_tone,zero_sub]
  have hs : Summable fun q : onLineCopies => ∫ t in Ioi (0:ℝ), ‖K q t‖ := by
    simp_rw [he,integral_const_mul]
    exact (((hF.summable_zero_traces hr).1).subtype (· ∈ onLineCopies)).mul_right _
  refine ⟨HTGeometry.integrable_tsum_of_summable_integral_norm hi hs, ?_⟩
  apply (hasSum_integral_of_summable_integral_norm hi hs).congr_fun
  intro q
  rw [show K q = fun t => (zeroValueMass F q : ℂ) * dampedTone p (tone (centredZero q).im) t from rfl,
    integral_const_mul,integral_dampedTone (by rwa [re_tone])]

/-- Absolute summability and the zero-free exterior of the critical strip
justify integrating the full off-line series on the ray. -/
private theorem integrate_off_spectrum {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 1 < p.re) :
    let V := fun t : ℝ => ∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * dampedTone p (centredZero q) t
    IntegrableOn V (Ioi 0) ∧ (∫ t in Ioi (0:ℝ), V t) =
      ∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * (p-centredZero q)⁻¹ := by
  intro V
  let A := fun q : ↑onLineCopiesᶜ => reflectedLaplaceProduct F q
  let K := fun (q : ↑onLineCopiesᶜ) (t : ℝ) => A q * dampedTone p (centredZero q) t
  have hA : Summable fun q => ‖A q‖ :=
    ((hF.hasSum_bare_pair hr hr hF).summable.norm).subtype (· ∈ onLineCopiesᶜ)
  have hz (q : ↑onLineCopiesᶜ) : (centredZero q).re < 1 := by
    have h := (abs_lt.mp (abs_re_centredZero_lt q.val)).2
    linarith only [h]
  have hk (q : ↑onLineCopiesᶜ) : IntegrableOn (K q) (Ioi 0) :=
    (dampedTone_integrable ((hz q).trans hp)).const_mul _
  let B := fun t : ℝ => Real.exp ((1-p.re)*t)
  have hB : IntegrableOn B (Ioi 0) := integrableOn_exp_mul_Ioi (by linarith only [hp]) 0
  have hb (q : ↑onLineCopiesᶜ) {t : ℝ} (ht : 0 ≤ t) : ‖K q t‖ ≤ ‖A q‖ * B t := by
    change ‖A q * cexp ((centredZero q-p)*t)‖ ≤ _
    rw [norm_mul,norm_cexp_mul_ofReal,sub_re]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (sub_le_sub_right (hz q).le _) ht)) (norm_nonneg _)
  have hsum : Summable fun q => ∫ t in Ioi (0:ℝ), ‖K q t‖ := by
    apply (hA.mul_right (∫ t in Ioi (0:ℝ), B t)).of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _)
    intro q; rw [← integral_const_mul]
    exact integral_mono_ae (hk q).norm (hB.const_mul _) ((ae_restrict_mem measurableSet_Ioi).mono
      fun t ht => hb q (le_of_lt ht))
  refine ⟨HTGeometry.integrable_tsum_of_summable_integral_norm hk hsum, ?_⟩
  apply Eq.symm
  apply HasSum.tsum_eq
  apply (hasSum_integral_of_summable_integral_norm hk hsum).congr_fun
  intro q
  change A q * (p-centredZero q)⁻¹ = ∫ t in Ioi (0:ℝ), A q * dampedTone p (centredZero q) t
  rw [integral_const_mul,integral_dampedTone ((hz q).trans hp)]

private theorem on_line_tone (q : onLineCopies) : tone (centredZero q).im = centredZero q := by
  apply Complex.ext <;> simp [tone,show (centredZero q).re = 0 from q.property]

private theorem density_mass {F : ℝ → ℝ} {D : ℝ → ℝ}
    (hD : ∀ t : ℝ, ((criticalHalfLineExponentialPair F (shiftProfile F t) : ℝ) : ℂ) =
      (Real.exp (4*t) : ℂ) * ∫ x : ℝ, (D x : ℂ) * cexp (tone (2*Real.pi*x) * t)) :
    (∫ x, D x) = criticalHalfLineExponentialPair F F := by
  have hzero := hD 0
  have hshift0 : shiftProfile F 0 = F := by funext u; simp [shiftProfile]
  simp only [hshift0,mul_zero,Real.exp_zero,Complex.ofReal_one,Complex.ofReal_zero,
    Complex.exp_zero,mul_one,one_mul,integral_complex_ofReal,Complex.ofReal_inj] at hzero
  exact hzero.symm

private theorem damp_density_shift (D : ℝ → ℝ) (p : ℂ) (t : ℝ) :
    (∫ x : ℝ, (D x : ℂ) * dampedTone (p-4) (tone (2*Real.pi*x)) t) = cexp (-(p*t)) * (Real.exp (4*t) : ℂ) *
      ∫ x : ℝ, (D x : ℂ) * cexp (tone (2*Real.pi*x)*t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have he : dampedTone (p-4) (tone (2*Real.pi*x)) t =
          (cexp (-(p*t)) * (Real.exp (4*t) : ℂ)) * cexp (tone (2*Real.pi*x)*t) := by
        rw [dampedTone,Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add]
        congr 1; push_cast; ring
      dsimp only
      rw [he]; ring

private theorem density_resolvent_pos {D : ℝ → ℝ} (hDm : Measurable D) (hDi : Integrable D)
    (hD0 : ∀ x, 0 ≤ D x) (hmass : 0 < ∫ x, D x) {p : ℂ} (hp : 4 < p.re) :
    0 < (∫ x : ℝ, (D x : ℂ) * (p-4-tone (2*Real.pi*x))⁻¹).re := by
  let w := fun x : ℝ => (D x : ℂ) * (p-4-tone (2*Real.pi*x))⁻¹
  have hw : Integrable w := (integrate_power_density hDm hDi
    (show 0 < (p-4).re by simpa using sub_pos.mpr hp)).2.1
  have hk (x : ℝ) : 0 < ((p-4-tone (2*Real.pi*x))⁻¹).re := by
    have h : 0 < (p-4-tone (2*Real.pi*x)).re := by
      simpa only [sub_re,re_tone,sub_zero,re_ofNat] using sub_pos.mpr hp
    rw [Complex.inv_re]
    exact div_pos h (Complex.normSq_pos.mpr (fun e => h.ne' (congrArg Complex.re e)))
  have hwre (x : ℝ) : (w x).re = D x * ((p-4-tone (2*Real.pi*x))⁻¹).re := Complex.re_ofReal_mul _ _
  have hn (x : ℝ) : 0 ≤ (w x).re := by rw [hwre]; exact mul_nonneg (hD0 x) (hk x).le
  have hwpos : 0 < (∫ x, w x).re := by
    have hre : (∫ x, (w x).re) = (∫ x, w x).re := integral_re hw
    rw [← hre]
    apply lt_of_le_of_ne (integral_nonneg hn)
    intro hz
    have hv := (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hn) hw.re).mp hz.symm
    have hd : D =ᵐ[volume] 0 := hv.mono fun x hx =>
      (mul_eq_zero.mp ((hwre x).symm.trans hx)).resolve_right (hk x).ne'
    have h0 : (∫ x, D x) = 0 := by rw [integral_congr_ae hd]; simp
    exact hmass.ne' h0
  exact hwpos

/-- The Laplace transform of the translated bare Weil pairing has strictly
negative real part at every frequency to the right of the confinement weight.
This uses the null equation for the full zero divisor. -/
theorem IsConfinedNullVector.bare_shift_laplace_re_neg {R : ℝ} (hr : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 4 < p.re) :
    (∫ t in Ioi (0:ℝ), cexp (-(p*t)) * (bareMixedEnergy F (shiftProfile F t) : ℂ)).re < 0 := by
  obtain ⟨D,hDm,hDi,hD0,hD⟩ := confined_power_density hF.1
  have hmass : 0 < ∫ x, D x := by rw [density_mass hD]; exact exponentialPair_self_pos hF.1 hF.2.1
  have hpos := density_resolvent_pos hDm hDi hD0 hmass hp
  have hW := (integrate_power_density hDm hDi (show 0 < (p-4).re by simpa using sub_pos.mpr hp)).2.2
  let W := fun t : ℝ => ∫ x : ℝ, (D x : ℂ) * dampedTone (p-4) (tone (2*Real.pi*x)) t
  have he (t : ℝ) (ht : 0 < t) : cexp (-(p*t)) * (bareMixedEnergy F (shiftProfile F t) : ℂ) =
      -(criticalAliasCoefficient R : ℂ) * W t := by
    have hb := bare_shift_at_null hF ht.le
    rw [hb, hD t, show W t = _ from damp_density_shift D p t]
    ring
  change (∫ t in Ioi (0:ℝ), W t) = _ at hW
  rw [setIntegral_congr_fun measurableSet_Ioi he,integral_const_mul,hW,← Complex.ofReal_neg,Complex.re_ofReal_mul]
  exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (criticalAliasCoefficient_positive hr)) hpos

/-- The translated zero pairing gives the Laplace transform of the confinement
correlation. Absolute convergence on the full divisor includes the boundary
`Re p = 4` of the Fourier-power representation. -/
theorem IsConfinedNullVector.translated_zero_resolvent {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 1 < p.re) :
    (∑' q : onLineCopies, (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹) +
      (∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * (p-centredZero q)⁻¹) =
      -(criticalAliasCoefficient R : ℂ) * ∫ t in Ioi (0:ℝ), cexp (-(p*t)) *
        (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ) := by
  let U := fun t : ℝ => ∑' q : onLineCopies, (zeroValueMass F q : ℂ) *
    dampedTone p (tone (centredZero q).im) t
  let V := fun t : ℝ => ∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q *
    dampedTone p (centredZero q) t
  obtain ⟨hUi,hU⟩ := integrate_line_spectrum hr hF (zero_lt_one.trans hp)
  have hu := hU.tsum_eq
  change _ = ∫ t in Ioi (0:ℝ), U t at hu
  change IntegrableOn U (Ioi 0) at hUi
  obtain ⟨hVi,hv⟩ := integrate_off_spectrum hr hF hp
  change IntegrableOn V (Ioi 0) at hVi
  change (∫ t in Ioi (0:ℝ), V t) = _ at hv
  simp_rw [on_line_tone] at hu
  rw [hu,← hv,← integral_add hUi hVi,← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have e := congrArg (cexp (-(p*t)) * ·) (null_frequency_balance hr hF (le_of_lt ht))
  rw [mul_add, ← tsum_mul_left, ← tsum_mul_left] at e
  have el : U t = ∑' q : onLineCopies, cexp (-(p*t)) *
      ((zeroValueMass F q : ℂ) * cexp (tone (centredZero q).im * t)) := by
    apply tsum_congr; intro q; rw [dampedTone_split]; ring
  have er : V t = ∑' q : ↑onLineCopiesᶜ, cexp (-(p*t)) *
      (reflectedLaplaceProduct F q * cexp (centredZero q * t)) := by
    apply tsum_congr; intro q; rw [dampedTone_split]; ring
  change U t + V t = _
  rw [el, er, e]
  ring

/-- For the full off-line divisor, the absolutely convergent transform of its
reflected products is the negative sum of the critical-line Cauchy transform and the
Cauchy transform of the weighted state's Fourier power. -/
theorem IsConfinedNullVector.poisson_spectrum {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) :
    ∃ D : ℝ → ℝ, Measurable D ∧ Integrable D ∧ (∀ x, 0 ≤ D x) ∧
      (∫ x, D x) = criticalHalfLineExponentialPair F F ∧ ∀ p : ℂ, 4 < p.re →
      (∑' q : onLineCopies, (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹) +
        (criticalAliasCoefficient R : ℂ) *
          (∫ x : ℝ, (D x : ℂ) * (p-4-(2*Real.pi*x : ℝ)*I)⁻¹) =
        -(∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * (p-centredZero q)⁻¹) := by
  classical
  obtain ⟨D,hDm,hDi,hD0,hD⟩ := confined_power_density hF.1
  refine ⟨D,hDm,hDi,hD0,density_mass hD,fun p hp => ?_⟩
  have hpt : 0 < (p-4).re := by simpa using sub_pos.mpr hp
  obtain ⟨-,-,hW⟩ := integrate_power_density hDm hDi hpt
  have he := hF.translated_zero_resolvent hr (by linarith only [hp] : 1 < p.re)
  have hw : (∫ t in Ioi (0:ℝ), cexp (-(p*t)) *
      (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ)) =
      ∫ x : ℝ, (D x : ℂ) * (p-4-(2*Real.pi*x : ℝ)*I)⁻¹ := by
    refine Eq.trans ?_ hW
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    change cexp (-(p*t)) * (criticalHalfLineExponentialPair F (shiftProfile F t) : ℂ) =
      ∫ x : ℝ, (D x : ℂ) * dampedTone (p-4) (tone (2*Real.pi*x)) t
    rw [hD t,damp_density_shift D p t]
    ring
  rw [hw] at he
  linear_combination he

/-- The reflected off-line products alone give a transform with strictly
negative real part throughout the half-plane beyond the confinement weight. -/
theorem IsConfinedNullVector.offLine_resolvent_re_neg {R : ℝ} (hr : 0 < R)
    {F : ℝ → ℝ} (hF : IsConfinedNullVector R F) {p : ℂ} (hp : 4 < p.re) :
    (∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * (p-centredZero q)⁻¹).re < 0 := by
  obtain ⟨D,hDm,hDi,hD0,hM,hS⟩ := hF.poisson_spectrum hr
  let w := fun x : ℝ => (D x : ℂ) * (p-4-tone (2*Real.pi*x))⁻¹
  have hwpos : 0 < (∫ x, w x).re := density_resolvent_pos hDm hDi hD0
    (by rw [hM]; exact exponentialPair_self_pos hF.1 hF.2.1) hp
  have hs := (integrate_line_spectrum hr hF (by linarith only [hp] : 0 < p.re)).2.summable
  simp_rw [on_line_tone] at hs
  have hline : 0 ≤ (∑' q : onLineCopies, (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹).re := by
    rw [Complex.re_tsum hs]
    apply tsum_nonneg
    intro q
    rw [Complex.re_ofReal_mul,Complex.inv_re,sub_re,show (centredZero q).re = 0 from q.property,sub_zero]
    exact mul_nonneg (zeroValueMass_nonneg _ _) (div_nonneg (by linarith only [hp]) (Complex.normSq_nonneg _))
  have he := congrArg Complex.re (hS p hp)
  simp only [add_re,Complex.re_ofReal_mul,neg_re] at he
  change _ + criticalAliasCoefficient R * (∫ x, w x).re = _ at he
  linarith only [he, hline, mul_pos (criticalAliasCoefficient_positive hr) hwpos]

private def ordinatePoint (y : ℝ) : ℂ := ⟨5,y⟩

/-- Adding the two opposite frequencies cancels the first-order pole at infinity. -/
private theorem symmetric_resolvent_bound (b : ℂ) (hb : 1 ≤ b.re) (y : ℝ) :
    (1+y^2) * ‖(b+tone y)⁻¹ + (b-tone y)⁻¹‖ ≤ 2*‖b‖*(2+‖b‖^2) := by
  let P := b + tone y
  let M := b - tone y
  have hP : 1 ≤ ‖P‖ := by
    have h := (le_abs_self P.re).trans (Complex.abs_re_le_norm P)
    exact hb.trans (by simpa only [P,add_re,re_tone,add_zero] using h)
  have hM : 1 ≤ ‖M‖ := by
    have h := (le_abs_self M.re).trans (Complex.abs_re_le_norm M)
    exact hb.trans (by simpa only [M,sub_re,re_tone,sub_zero] using h)
  have hp : P ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hP)
  have hm : M ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le hM)
  have hy : (y:ℂ)^2 = P*M-b^2 := by
    dsimp only [P,M,tone]
    rw [show (b+(y:ℂ)*I)*(b-(y:ℂ)*I)-b^2 = -(y:ℂ)^2*Complex.I^2 by ring, Complex.I_sq]
    ring
  have hn := norm_sub_le (P*M) (b^2)
  rw [← hy,norm_pow,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs] at hn
  have hone : 1 ≤ ‖P‖*‖M‖ := one_le_mul_of_one_le_of_one_le hP hM
  have hnum : 1+y^2 ≤ (2+‖b‖^2)*(‖P‖*‖M‖) := by
    nlinarith only [hn,hone,mul_le_mul_of_nonneg_left hone (sq_nonneg ‖b‖)]
  have he : P*M*(P⁻¹+M⁻¹) = 2*b := by
    calc P*M*(P⁻¹+M⁻¹) = P+M := by field_simp; ring
         _ = _ := by dsimp only [P,M]; ring
  have hnorm := congrArg norm he
  simp only [norm_mul] at hnorm
  norm_num at hnorm
  change (1+y^2)*‖P⁻¹+M⁻¹‖ ≤ _
  calc _ ≤ ((2+‖b‖^2)*(‖P‖*‖M‖))*‖P⁻¹+M⁻¹‖ :=
        mul_le_mul_of_nonneg_right hnum (norm_nonneg _)
       _ = _ := by rw [mul_assoc,hnorm,mul_comm]

/-- Cauchy transform of the reflected products over the full off-line divisor. -/
def reflectedOffLineResolvent (F : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * (p - centredZero q)⁻¹

private abbrev offSpectrum (F : ℝ → ℝ) (y : ℝ) := reflectedOffLineResolvent F (ordinatePoint y)

/-- The paired Cauchy kernels at opposite heights decay quadratically for a finite off-line layer. -/
theorem paired_reflectedOffLineResolvent_bound (F : ℝ → ℝ) (hfin : BacklundConverse.FiniteOffLine)
    {σ : ℝ} (hσ : 2 ≤ σ) :
    ∃ C : ℝ, ∀ y : ℝ, (1+y^2)*‖reflectedOffLineResolvent F ⟨σ,y⟩ + reflectedOffLineResolvent F ⟨σ,-y⟩‖ ≤ C := by
  classical
  letI : Fintype (↑onLineCopiesᶜ) := (compl_onLineCopies_finite_of_finiteOffLine hfin).fintype
  let b := fun q : ↑onLineCopiesᶜ => (σ : ℂ) - centredZero q
  let A := fun q : ↑onLineCopiesᶜ => reflectedLaplaceProduct F q
  refine ⟨∑ q, ‖A q‖ * (2*‖b q‖*(2+‖b q‖^2)), fun y => ?_⟩
  let g := fun q => A q * (((b q)+tone y)⁻¹ + ((b q)-tone y)⁻¹)
  have he : reflectedOffLineResolvent F ⟨σ,y⟩ + reflectedOffLineResolvent F ⟨σ,-y⟩ = ∑ q, g q := by
    simp only [reflectedOffLineResolvent,tsum_fintype,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    have hp : (⟨σ,y⟩ : ℂ) = (σ : ℂ)+tone y := by apply Complex.ext <;> simp [tone]
    have hm : (⟨σ,-y⟩ : ℂ) = (σ : ℂ)-tone y := by apply Complex.ext <;> simp [tone]
    rw [hp,hm,show (σ : ℂ)+tone y-centredZero q = b q + tone y by dsimp [b]; ring,
      show (σ : ℂ)-tone y-centredZero q = b q - tone y by dsimp [b]; ring]
    dsimp only [g,A]
    ring
  rw [he]
  calc _ ≤ (1+y^2) * ∑ q, ‖g q‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
       _ ≤ _ := by
         rw [Finset.mul_sum]
         apply Finset.sum_le_sum
         intro q _
         have hb : 1 ≤ (b q).re := by
           have hz := (abs_lt.mp (abs_re_centredZero_lt q.val)).2
           change 1 ≤ σ - (centredZero q.val).re
           linarith only [hz,hσ]
         rw [show ‖g q‖ = ‖A q‖ * ‖(b q+tone y)⁻¹+(b q-tone y)⁻¹‖ by exact norm_mul _ _,mul_left_comm]
         exact mul_le_mul_of_nonneg_left (symmetric_resolvent_bound _ hb y) (norm_nonneg _)

private def localLineMass (F : ℝ → ℝ) (y : ℝ) (q : onLineCopies) : ℝ :=
  if |(centredZero q).im-y| ≤ 1 then zeroValueMass F q else 0

/-- The off-line transform bounds the total mass of all critical-line zero
copies within one unit of each ordinate, for an arbitrary zero divisor. -/
theorem IsConfinedNullVector.critical_line_window_le_reflected {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (y : ℝ) :
    (∑' q : onLineCopies, if |(centredZero q).im-y| ≤ 1 then zeroValueMass F q else 0) ≤
      6 * (-(∑' q : ↑onLineCopiesᶜ, reflectedLaplaceProduct F q * ((⟨5,y⟩ : ℂ)-centredZero q)⁻¹).re) := by
  change (∑' q, localLineMass F y q) ≤ 6 * (-(offSpectrum F y).re)
  obtain ⟨D,hDm,hDi,hD0,hM,hspec⟩ := hF.poisson_spectrum hr
  let p := ordinatePoint y
  let l := fun q : onLineCopies => (zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹
  let w := fun x : ℝ => (D x : ℂ) * (p-4-tone (2*Real.pi*x))⁻¹
  have hp : 4 < p.re := by norm_num [p,ordinatePoint]
  have he := congrArg Complex.re (hspec p hp)
  simp only [add_re,Complex.re_ofReal_mul,neg_re] at he
  change (∑' q, l q).re + criticalAliasCoefficient R * (∫ x, w x).re = -(offSpectrum F y).re at he
  have hpos : 0 ≤ (∫ x, w x).re := (density_resolvent_pos hDm hDi hD0
    (by rw [hM]; exact exponentialPair_self_pos hF.1 hF.2.1) hp).le
  have hl : Summable l := by
    have h := (integrate_line_spectrum hr hF (by linarith only [hp] : 0 < p.re)).2.summable
    simpa only [on_line_tone,l] using h
  have hloc (q : onLineCopies) : localLineMass F y q ≤ 6 * (l q).re := by
    have hq : (centredZero q).re = 0 := q.property
    have hv : (l q).re = zeroValueMass F q * (5 / (25 + (y-(centredZero q).im)^2)) := by
      change ((zeroValueMass F q : ℂ) * (p-centredZero q)⁻¹).re = _
      rw [Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, sub_re, sub_im, hq, sub_zero]
      change zeroValueMass F q * (5/(5*5+(y-(centredZero q).im)*(y-(centredZero q).im))) = _
      rw [sq]; norm_num
    rw [hv]
    unfold localLineMass
    split_ifs with hnear
    · have hy := abs_le.mp hnear
      have hsq : (y-(centredZero q).im)^2 ≤ 1 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hy.2) (by linarith only [hy.1] :
          0 ≤ 1+((centredZero q).im-y))]
      have hfloor : 1 ≤ 6*(5/(25+(y-(centredZero q).im)^2)) := by
        rw [← mul_div_assoc,le_div_iff₀ (by positivity)]; linarith only [hsq]
      nlinarith only [mul_le_mul_of_nonneg_left hfloor (zeroValueMass_nonneg F q)]
    · exact mul_nonneg (by norm_num) (mul_nonneg (zeroValueMass_nonneg _ _) (by positivity))
  have hsmall : Summable (localLineMass F y) := (((hF.summable_zero_traces hr).1).subtype (· ∈ onLineCopies)).of_nonneg_of_le (fun q => by unfold localLineMass; split_ifs <;>
      first | exact zeroValueMass_nonneg _ _ | exact le_rfl)
      (fun q => by unfold localLineMass; split_ifs <;> first | exact le_rfl | exact zeroValueMass_nonneg _ _)
  have hle := hsmall.tsum_le_tsum hloc ((Complex.reCLM.summable hl).mul_left 6)
  rw [tsum_mul_left] at hle
  have hrw := Complex.re_tsum hl
  change (∑' q, l q).re = ∑' q, (l q).re at hrw
  rw [← hrw] at hle
  linarith only [he,hle,mul_nonneg (criticalAliasCoefficient_positive hr).le hpos]

/-- Every radius-one ordinate window in the infinite critical-line spectrum has mass
of order at most the inverse square of its height. This holds for every
confined state of a finite off-line layer, independently of its rung. -/
theorem IsConfinedNullVector.local_critical_line_mass {R : ℝ} (hr : 0 < R) {F : ℝ → ℝ}
    (hF : IsConfinedNullVector R F) (hfin : BacklundConverse.FiniteOffLine) :
    ∃ C : ℝ, ∀ y : ℝ, (1+y^2) * (∑' q : onLineCopies,
      if |(centredZero q).im-y| ≤ 1 then zeroValueMass F q else 0) ≤ C := by
  obtain ⟨C,hC⟩ := paired_reflectedOffLineResolvent_bound F hfin (by norm_num : (2:ℝ) ≤ 5)
  refine ⟨6*C, fun y => ?_⟩
  have h₁ := hF.critical_line_window_le_reflected hr y
  have h₂ := hF.critical_line_window_le_reflected hr (-y)
  change (∑' q, localLineMass F y q) ≤ 6 * (-(offSpectrum F y).re) at h₁
  change (∑' q, localLineMass F (-y) q) ≤ 6 * (-(offSpectrum F (-y)).re) at h₂
  have hn : 0 ≤ ∑' q, localLineMass F (-y) q := tsum_nonneg fun q => by
    unfold localLineMass; split_ifs <;> first | exact zeroValueMass_nonneg _ _ | exact le_rfl
  have hsum : -(offSpectrum F y).re - (offSpectrum F (-y)).re ≤
      ‖offSpectrum F y + offSpectrum F (-y)‖ := by
    have h := (neg_le_abs (offSpectrum F y + offSpectrum F (-y)).re).trans (Complex.abs_re_le_norm _)
    simpa only [add_re,neg_add_rev,sub_eq_add_neg,add_comm] using h
  change (1+y^2) * (∑' q, localLineMass F y q) ≤ _
  have he : (∑' q, localLineMass F y q) ≤ 6*‖offSpectrum F y + offSpectrum F (-y)‖ := by
    linarith only [h₁,h₂,hn,hsum]
  calc _ ≤ (1+y^2)*(6*‖offSpectrum F y + offSpectrum F (-y)‖) := mul_le_mul_of_nonneg_left he (by positivity)
       _ ≤ _ := by rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hC y) (by norm_num)

#print axioms IsConfinedNullVector.translated_zero_resolvent
#print axioms paired_reflectedOffLineResolvent_bound
#print axioms IsConfinedNullVector.bare_shift_laplace_re_neg
#print axioms IsConfinedNullVector.poisson_spectrum
#print axioms IsConfinedNullVector.offLine_resolvent_re_neg
#print axioms IsConfinedNullVector.critical_line_window_le_reflected
#print axioms IsConfinedNullVector.local_critical_line_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
