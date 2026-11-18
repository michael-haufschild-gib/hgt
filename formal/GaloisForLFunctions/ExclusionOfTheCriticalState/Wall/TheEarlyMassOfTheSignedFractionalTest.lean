import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ExponentiallyIntegrableChangeOfPrimeVariance
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheIntegerWaveHasVanishingMeanAbsoluteError
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# The exterior time ranges of the original fractional test

Confinement controls the early integer and ordinary-prime rows. On the
far-right ray the damped ordinary-prime estimate controls every measurable
portion of the actual test in absolute value.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

private theorem coefficient_row_bound {Φ : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (w : ℕ → ℝ), (∀ n, |w n| ≤ Real.log n+1) → ∀ t : ℝ,
      |∑' n : ℕ, w n*continuousIntegerAtom Φ n t| ≤ D*Real.exp (2*t) := by
  let a := fun n : ℕ => Real.log n/(n:ℝ)^2 + 1/(n:ℝ)^2
  have ha : Summable a := GaloisForLFunctions.summable_log_nat_div_sq.add
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hapos (n : ℕ) : 0 ≤ a n :=
    add_nonneg (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)) (by positivity)
  refine ⟨C*(∑' n, a n),mul_nonneg hC (tsum_nonneg hapos),fun w hw t => ?_⟩
  let q := C*Real.exp (2*t)
  have hq : 0 ≤ q := mul_nonneg hC (Real.exp_pos _).le
  have hp (n : ℕ) : |w n*continuousIntegerAtom Φ n t| ≤ q*a n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [continuousIntegerAtom,a]
    · rw [abs_mul]
      calc _ ≤ (Real.log n+1)*(q*(1/(n:ℝ)^2)) :=
             mul_le_mul (hw n) (continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ) ≤ n) t)
               (abs_nonneg _) (by linarith only [Real.log_natCast_nonneg n])
        _ = _ := by dsimp only [a]; ring
  have hs := Summable.of_nonneg_of_le (fun n => abs_nonneg _) hp (ha.mul_left q)
  have hnorm := norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs :
    Summable (fun n : ℕ => ‖w n*continuousIntegerAtom Φ n t‖))
  calc _ ≤ ∑' n : ℕ, |w n*continuousIntegerAtom Φ n t| := by simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∑' n : ℕ, q*a n := hs.tsum_le_tsum hp (ha.mul_left q)
    _ = _ := by rw [tsum_mul_left]; dsimp only [q]; ring

/-- The kernel charges any bounded early row on the whole left ray, before
choosing a time mask or taking either limit. -/
private theorem early_fractional_mass {f : ℝ → ℝ} {U M : ℝ} (hM : 0 ≤ M)
    (hm : Measurable f) (hf : ∀ t ≤ U, |f t| ≤ M) (T : ℝ) :
    IntegrableOn (fun t => |f t| *fractionalPrimeTest (T-t)) (Iic U) ∧
    (∫ t in Iic U, |f t| *fractionalPrimeTest (T-t)) ≤ 2*M*Real.exp ((U-T)/2) := by
  let H := fun t : ℝ => (M*Real.exp (-T/2))*Real.exp ((1/2)*t)
  have hi : IntegrableOn H (Iic U) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) U).const_mul _
  have hK (t : ℝ) : 0 ≤ fractionalPrimeTest (T-t) :=
    mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
  have hbound : ∀ᵐ t ∂volume.restrict (Iic U), |f t| *fractionalPrimeTest (T-t) ≤ H t := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Iic (a := U))] with t ht
    have hk : fractionalPrimeTest (T-t) ≤ Real.exp (-(T-t)/2) :=
      mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
    calc _ ≤ M*Real.exp (-(T-t)/2) := mul_le_mul (hf t ht) hk (hK _) hM
      _ = H t := by dsimp only [H]; rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hI : IntegrableOn (fun t => |f t| *fractionalPrimeTest (T-t)) (Iic U) :=
    hi.mono' (hm.abs.mul (measurable_fractionalPrimeTest.comp (by fun_prop))).aestronglyMeasurable
      (hbound.mono fun t h => (Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (hK t))).le.trans h)
  refine ⟨hI,(integral_mono_ae hI hi hbound).trans_eq ?_⟩
  dsimp only [H]; rw [integral_const_mul,integral_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) U]
  rw [show (U-T)/2 = -T/2+(1/2)*U by ring,Real.exp_add]; ring

/-- Uniform early mass at any cutoff U ≥ 0 for a confined continuous profile.
Both references are included and the integral converges absolutely. -/
theorem early_signed_fractional_mass_of_confinement {Φ : ℝ → ℝ} (hc : Continuous Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ U : ℝ, 0 ≤ U → ∀ T : ℝ,
        let m := ∫ u, Φ u
        let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
        let f := fun t => (|S t|+|ordinaryPrimePolarError Φ t|)*fractionalPrimeTest (T-t)
        IntegrableOn f (Iic U) ∧ (∫ t in Iic U, f t) ≤ B*Real.exp ((5*U-T)/2) := by
  obtain ⟨D,hD,hbound⟩ := coefficient_row_bound hC hb
  let m := ∫ u, Φ u
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
  let w := fun n : ℕ => (if n.Prime then Real.log n else 0)-1
  have href (t : ℝ) : |integerReferenceWave Φ t| ≤ D*Real.exp (2*t) := by
    rw [← tsum_continuousIntegerAtom hb t]
    simpa only [one_mul] using hbound (fun _ => 1) (fun n => by
      rw [abs_one]; linarith only [Real.log_natCast_nonneg n]) t
  have hp (t : ℝ) : |integerCentredPrimeWave Φ t| ≤ D*Real.exp (2*t) := by
    apply hbound w
    intro n
    apply (abs_sub _ _).trans
    by_cases hn : n.Prime
    · simp only [if_pos hn,abs_one,abs_of_nonneg (Real.log_natCast_nonneg _),le_refl]
    · simp only [if_neg hn,abs_zero,abs_one,zero_add]
      linarith only [Real.log_natCast_nonneg n]
  have hs (t : ℝ) : |S t| ≤ D*Real.exp (2*t)+|m/2| := by
    apply (abs_sub _ _).trans
    refine add_le_add (hbound _ (fun n => (abs_sub _ _).trans ?_) t) le_rfl
    rw [abs_one,abs_of_nonneg vonMangoldt_nonneg]
    exact add_le_add vonMangoldt_le_log le_rfl
  let M := 3*D+|m/2|+|A|
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  refine ⟨2*M,by positivity,fun U hU T => ?_⟩
  let H := Real.exp (2*U)
  have hH : 1 ≤ H := Real.one_le_exp (mul_nonneg (by norm_num) hU)
  have hearly (t : ℝ) (htU : t ≤ U) : abs (|S t| + |ordinaryPrimePolarError Φ t|) ≤ M*H := by
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    have hd := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (by linarith only [htU] : 2*t ≤ 2*U)) hD
    have heA := mul_le_mul_of_nonneg_right (Real.exp_le_exp.2
      (by linarith only [htU,hU] : t/2 ≤ 2*U)) (abs_nonneg A)
    have hre := integerCentredPrimeWave_eq hb t
    have heP : ordinaryPrimePolarError Φ t =
        (integerCentredPrimeWave Φ t + integerReferenceWave Φ t)-Real.exp (t/2)*A := by
      dsimp only [A]; rw [ordinaryPrimePolarError,hre]; ring
    have hpolar := abs_sub (integerCentredPrimeWave Φ t+integerReferenceWave Φ t) (Real.exp (t/2)*A)
    rw [abs_mul,abs_of_pos (Real.exp_pos _)] at hpolar
    rw [heP]
    dsimp only [M,H] at *
    linarith only [hs t,hp t,href t,hpolar,abs_add_le (integerCentredPrimeWave Φ t) (integerReferenceWave Φ t),
      heA,hd,mul_le_mul_of_nonneg_left hH (abs_nonneg (m/2))]
  have hmS : Measurable S := by
    dsimp only [S]
    exact (Measurable.tsum fun n : ℕ =>
      measurable_const.mul (measurable_const.mul (hc.measurable.comp (by fun_prop)))).sub measurable_const
  have hmW : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hc.measurable.comp (by fun_prop)))
  have hmP : Measurable (ordinaryPrimePolarError Φ) :=
    (Complex.continuous_re.measurable.comp hmW).sub (by fun_prop)
  have h := early_fractional_mass (f := fun t => |S t|+|ordinaryPrimePolarError Φ t|)
    (mul_nonneg hM (Real.exp_pos _).le) (hmS.abs.add hmP.abs) hearly T
  have hn (t : ℝ) : abs (|S t|+|ordinaryPrimePolarError Φ t|) =
      |S t|+|ordinaryPrimePolarError Φ t| := abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
  simp only [hn] at h
  refine ⟨h.1,h.2.trans_eq ?_⟩
  dsimp only [H]
  rw [show (5*U-T)/2 = 2*U+(U-T)/2 by ring,Real.exp_add]; ring

/-- The literal centered and polar-subtracted prime rows have uniformly
exponentially small early readings, with the early cutoff chosen independently
of the test time. -/
theorem riemannHypothesis_or_early_fractional_mass : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧
      ∀ U : ℝ, 0 ≤ U → ∀ T : ℝ,
        let m := ∫ u, Φ u
        let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
        let f := fun t => (|S t|+|ordinaryPrimePolarError Φ t|)*fractionalPrimeTest (T-t)
        IntegrableOn f (Iic U) ∧ (∫ t in Iic U, f t) ≤ B*Real.exp ((5*U-T)/2) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨B,hB,h⟩ := early_signed_fractional_mass_of_confinement hc hC hb
  exact Or.inr ⟨W₀,F,Φ,B,hW,ht,hF,hc,he,hB,h⟩

/-- The early part of the original fractional test at cutoff T/6, with the
ordinary-prime and literal centered rows charged in absolute value. -/
theorem riemannHypothesis_or_sixth_cutoff_fractional_mass : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧
      ∀ T : ℝ, 0 ≤ T →
        let m := ∫ u, Φ u
        let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
        let f := fun t => (|S t|+|ordinaryPrimePolarError Φ t|)*fractionalPrimeTest (T-t)
        IntegrableOn f (Iic (T/6)) ∧ (∫ t in Iic (T/6), f t) ≤ B*Real.exp (-T/12) := by
  rcases riemannHypothesis_or_early_fractional_mass with hr | ⟨W₀,F,Φ,B,hW,ht,hF,hc,he,hB,h⟩
  · exact Or.inl hr
  refine Or.inr ⟨W₀,F,Φ,B,hW,ht,hF,hc,he,hB,fun T hT => ?_⟩
  simpa only [show (5*(T/6)-T)/2 = -T/12 by ring] using h (T/6) (by positivity) T

/-- The far-right tail of the original ordinary-prime test on any measurable
set. The zero abscissa supplies an integrable absolute error at tilt −2/5. -/
theorem criticalState_late_absolute_ordinary_test {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (A : Set ℝ), 0 ≤ T → MeasurableSet A →
      let f := fun t : ℝ => |(∫ u, Φ u)*ordinaryPrimePolarError Φ t|*fractionalPrimeTest (T-t)
      IntegrableOn f (A ∩ Ioi (6*T)) ∧ (∫ t in A ∩ Ioi (6*T), f t) ≤ C*Real.exp (-T/10) := by
  let d := (31/80:ℝ)
  let c := (1/80:ℝ)
  let m := ∫ u, Φ u
  let g := fun t : ℝ => Real.exp (-(2/5)*t)*|ordinaryPrimePolarError Φ t|
  have hd : zetaZeroAbscissa-1/2 < d := by
    dsimp only [d]; linarith only [ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths]
  have hz := memLp_damped_ordinaryPrimePolarError hW ht hF he hd
  have hq : 0 < (c:ℂ).re := by norm_num [c]
  have hh := ((memLp_two_expRay_restrict hq 0).norm.integrable_mul hz).norm
  have hi : IntegrableOn g (Ioi 0) := by
    apply hh.congr
    apply Eventually.of_forall fun t => ?_
    change |‖expRay (c:ℂ) t‖*(Real.exp (-(d*t))*ordinaryPrimePolarError Φ t)|=_
    rw [norm_expRay,Complex.ofReal_re,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul,
      abs_of_pos (Real.exp_pos _),← mul_assoc,← Real.exp_add]
    dsimp only [g,c,d]; congr 2; ring
  have hg (t : ℝ) : 0 ≤ g t := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
  refine ⟨|m|*(∫ t in Ioi 0, g t),mul_nonneg (abs_nonneg m) (integral_nonneg hg),fun T A hT hA => ?_⟩
  let J := A ∩ Ioi (6*T)
  let f := fun t => |m*ordinaryPrimePolarError Φ t|*fractionalPrimeTest (T-t)
  let b := |m|*Real.exp (-T/10)
  have hb : 0 ≤ b := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hJ : MeasurableSet J := hA.inter measurableSet_Ioi
  have hJ0 : J ⊆ Ioi 0 := fun _ h => lt_of_le_of_lt (by positivity) h.2
  have hmW : Measurable (ordinaryPrimeWave Φ) := Measurable.tsum fun q : Nat.Primes =>
    measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hc.measurable.comp (by fun_prop)))
  have hmP : Measurable (ordinaryPrimePolarError Φ) :=
    (Complex.continuous_re.measurable.comp hmW).sub (by fun_prop)
  have hfm : Measurable f := (measurable_const.mul hmP).abs.mul
    (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))
  have hpos (t : ℝ) : 0 ≤ fractionalPrimeTest (T-t) := mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
  have hle (t : ℝ) (htj : t ∈ J) : f t ≤ b*g t := by
    have hk := (le_abs_self (fractionalPrimeTest (T-t))).trans (fractionalPrimeTest_bounds (T-t)).2
    have hex : Real.exp ((T-t)/2) ≤ Real.exp (-T/10)*Real.exp (-(2/5)*t) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [htj.2])
    calc f t ≤ |m*ordinaryPrimePolarError Φ t|*(Real.exp (-T/10)*Real.exp (-(2/5)*t)) :=
          mul_le_mul_of_nonneg_left (hk.trans hex) (abs_nonneg _)
      _ = _ := by dsimp only [b,g]; rw [abs_mul]; ring
  have hbg : IntegrableOn (fun t => b*g t) J := (hi.const_mul b).mono_set hJ0
  have hfi : IntegrableOn f J := hbg.mono' hfm.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) hJ] with t htj
    rw [Real.norm_of_nonneg (show 0 ≤ f t from mul_nonneg (abs_nonneg _) (hpos t))]
    exact hle t htj)
  refine ⟨hfi,?_⟩
  change (∫ t in J, f t) ≤ _
  calc _ ≤ ∫ t in J, b*g t := setIntegral_mono_on hfi hbg hJ hle
    _ ≤ ∫ t in Ioi 0, b*g t := setIntegral_mono_set (hi.const_mul b)
      (Eventually.of_forall fun t => mul_nonneg hb (hg t)) (Eventually.of_forall fun _ h => hJ0 h)
    _ = _ := by rw [integral_const_mul]; dsimp only [b]; ring

/-- On one forced state the original test has exponentially small absolute
cost on both exterior time ranges, including any late selection of centers. -/
theorem riemannHypothesis_or_exterior_fractional_mass : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (B C : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ T : ℝ, 0 ≤ T →
        let m := ∫ u, Φ u
        let S := fun t : ℝ => (∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t)-m/2
        let f := fun t => (|S t|+|ordinaryPrimePolarError Φ t|)*fractionalPrimeTest (T-t)
        let g := fun t => |m*ordinaryPrimePolarError Φ t|*fractionalPrimeTest (T-t)
        IntegrableOn f (Iic (T/6)) ∧ (∫ t in Iic (T/6), f t) ≤ B*Real.exp (-T/12) ∧
          ∀ A : Set ℝ, MeasurableSet A → IntegrableOn g (A ∩ Ioi (6*T)) ∧
            (∫ t in A ∩ Ioi (6*T), g t) ≤ C*Real.exp (-T/10) := by
  rcases riemannHypothesis_or_sixth_cutoff_fractional_mass with hr | ⟨W₀,F,Φ,B,hW,ht,hF,hc,he,hB,h⟩
  · exact Or.inl hr
  obtain ⟨C,hC,hl⟩ := criticalState_late_absolute_ordinary_test hW ht hF hc he
  exact Or.inr ⟨W₀,F,Φ,B,C,hW,ht,hF,hc,he,hB,hC,fun T hT => ⟨(h T hT).1,(h T hT).2,
    fun A hA => hl T A hT hA⟩⟩

#print axioms riemannHypothesis_or_exterior_fractional_mass
#print axioms riemannHypothesis_or_sixth_cutoff_fractional_mass
#print axioms riemannHypothesis_or_early_fractional_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
