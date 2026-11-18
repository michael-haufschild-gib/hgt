import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfTheIntegerCentredPrimeWave
import GaloisForLFunctions.BezoutValuationIncidence.EnergyMeanOfThePowerDampedSourceTendsToOne
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimePowerMangoldtReindex

/-!
# Fractional-part cancellation on the odd integers

Removing all even Mangoldt coefficients costs exactly the powers of two.
Their geometric series and the odd integer quadrature both admit every
tilt below one half. The remaining two arithmetic rows have only even gaps.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

private def primeDivisorWave (p : Nat.Primes) (Φ : ℝ → ℝ) (t : ℝ) :=
  ∑' n : ℕ, if (p:ℕ) ∣ n then vonMangoldt n*continuousIntegerAtom Φ n t else 0

/-- All Mangoldt atoms removed at one prime form a single geometric
progression. Its tilted absolute contribution is uniformly bounded. -/
private theorem primeDivisorWave_bound (p : Nat.Primes) {Φ : ℝ → ℝ} {C r : ℝ}
    (hC : 0 ≤ C) (hΦ : ∀ u, |Φ u| ≤ C) (hs : ∀ u, 0 ≤ u → Φ u=0)
    (hr : 0 ≤ r) (hr' : r < 1/2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |primeDivisorWave p Φ t| ≤ M*Real.exp (-r*t) := by
  let m := fun k : ℕ => (p:ℕ)^(k+1)
  let w := fun k : ℕ => vonMangoldt (m k)*((m k:ℕ):ℝ)^(-(1/2-r))
  have hw : Summable w :=
    (BezoutValuationIncidence.hasSum_prime_power_vonMangoldt (sub_pos.mpr hr') p).summable
  have hw0 (k : ℕ) : 0 ≤ w k := mul_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hj : Function.Injective m := by
    intro a b h; exact Nat.add_right_cancel (Nat.pow_right_injective p.2.two_le h)
  refine ⟨C*(∑' k, w k),mul_nonneg hC (tsum_nonneg hw0),fun t => ?_⟩
  let f := fun n : ℕ => if (p:ℕ) ∣ n then vonMangoldt n*continuousIntegerAtom Φ n t else 0
  have hsup : Function.support f ⊆ Set.range m := by
    intro n hn
    by_cases hp : (p:ℕ) ∣ n
    · by_cases hΛ : vonMangoldt n=0
      · exact False.elim (hn (by simp [f,hp,hΛ]))
      obtain ⟨k,hk,heq⟩ := RenormalizedArithmeticPotentialTheory.eq_pow_of_dvd_of_vonMangoldt_ne_zero p.2 hp hΛ
      exact ⟨k-1,by dsimp only [m]; rw [Nat.sub_add_cancel hk]; exact heq.symm⟩
    · exact False.elim (hn (if_neg hp))
  have he (k : ℕ) : f (m k)=vonMangoldt (m k)*continuousIntegerAtom Φ (m k) t :=
    if_pos (dvd_pow_self _ (Nat.succ_ne_zero k))
  have term (k : ℕ) : ‖f (m k)‖ ≤ (C*Real.exp (-r*t))*w k := by
    let n := m k
    have hn : 0 < (n:ℝ) := by exact_mod_cast pow_pos p.2.pos (k+1)
    rw [he,Real.norm_eq_abs,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
    by_cases hu : 0 ≤ t-Real.log n
    · rw [continuousIntegerAtom,hs _ hu,mul_zero,abs_zero,mul_zero]
      exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hw0 k)
    have hlt : t < Real.log n := lt_of_sub_neg (lt_of_not_ge hu)
    have hweight : (Real.sqrt (n:ℝ))⁻¹ ≤ Real.exp (-r*t)*(n:ℝ)^(-(1/2-r)) := by
      have he : Real.sqrt (n:ℝ)=Real.exp (Real.log n/2) := by rw [Real.exp_half,Real.exp_log hn]
      rw [he,← Real.exp_neg,Real.rpow_def_of_pos hn,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [mul_le_mul_of_nonneg_left hlt.le hr]
    have hterm : |continuousIntegerAtom Φ (n:ℝ) t| ≤
        (Real.exp (-r*t)*(n:ℝ)^(-(1/2-r)))*C := by
      rw [continuousIntegerAtom,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      exact mul_le_mul hweight (hΦ _) (abs_nonneg _) (by positivity)
    calc _ ≤ vonMangoldt n*((Real.exp (-r*t)*(n:ℝ)^(-(1/2-r)))*C) :=
           mul_le_mul_of_nonneg_left hterm vonMangoldt_nonneg
      _ = _ := by dsimp only [w,n]; ring
  have hbound := (hw.mul_left (C*Real.exp (-r*t)))
  have hi := Summable.of_nonneg_of_le (fun k => norm_nonneg (f (m k))) term hbound
  change |∑' n, f n| ≤ _
  rw [← hj.tsum_eq hsup]
  exact (norm_tsum_le_tsum_norm hi).trans ((hi.tsum_le_tsum term hbound).trans_eq (by
    rw [tsum_mul_left]; ring))

private abbrev twoPrime : Nat.Primes := ⟨2,Nat.prime_two⟩

/-- Both the Mangoldt coefficient and its integer reference are restricted
to odd integers; the reference has density-normalizing factor two. -/
def oddCentredMangoldtWave (Φ : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, if 2 ∣ n then 0 else (vonMangoldt n-2)*continuousIntegerAtom Φ n t

private theorem oddCentredMangoldtWave_eq {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    oddCentredMangoldtWave Φ t=(∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t)-
      primeDivisorWave twoPrime Φ t-sievedIntegerReference {twoPrime} Φ t := by
  let a := fun n : ℕ => continuousIntegerAtom Φ n t
  let l := fun n : ℕ => vonMangoldt n*a n
  let O := {n : ℕ | ¬ 2 ∣ n}
  let E := {n : ℕ | 2 ∣ n}
  have ha : Summable a := summable_continuousIntegerAtom hb t
  have hl : Summable l := summable_mangoldt_integerAtom hb t
  have hN : sievedIntegerReference {twoPrime} Φ t=2*∑' n, O.indicator a n := by
    have hD : sieveDensity {twoPrime} = 1/2 := by norm_num [sieveDensity,twoPrime]
    have hO : {n : ℕ | n.Coprime (sievePrimorial {twoPrime})}=O := by
      ext n
      change n.Coprime (sievePrimorial {twoPrime}) ↔ ¬ 2 ∣ n
      rw [sievePrimorial,Finset.prod_singleton,Nat.coprime_comm]
      exact Nat.prime_two.coprime_iff_not_dvd
    rw [sievedIntegerReference,hD,sievedSum,hO]
    change (∑' n, O.indicator a n)/(1/2)=_
    ring
  have hR : primeDivisorWave twoPrime Φ t=∑' n, E.indicator l n := rfl
  rw [hN,hR,← tsum_mul_left,← hl.tsum_sub (hl.indicator E),
    ← (hl.sub (hl.indicator E)).tsum_sub ((ha.indicator O).mul_left 2)]
  apply tsum_congr fun n => ?_
  by_cases h : 2 ∣ n <;> simp [E,O,Set.indicator,h,sub_mul,a,l]

private theorem bounded_tilt_floor_response {R : ℝ → ℝ} (hm : Measurable R)
    {M r : ℝ} (hM : 0 ≤ M) (hr : 0 ≤ r) (hr' : r < 1/2)
    (hR : ∀ t, |R t| ≤ M*Real.exp (-r*t)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ,
      let f := fun t => R t*fractionalPrimeTest (T-t)
      Integrable f ∧ (∫ t, |f t|) ≤ B*Real.exp (-r*T) := by
  let J := fun v : ℝ => |weightedFloorDiscrepancy (1/2-r) v|
  have hJ : Integrable J := (integrable_weightedFloorDiscrepancy (sub_pos.mpr hr')
    (by linarith only [hr])).abs
  refine ⟨M*(∫ v, J v),mul_nonneg hM (integral_nonneg fun _ => abs_nonneg _),fun T => ?_⟩
  let f := fun t : ℝ => R t*fractionalPrimeTest (T-t)
  let C := M*Real.exp (-r*T)
  have hmaj := (hJ.comp_sub_left T).const_mul C
  have hpt (t : ℝ) : ‖f t‖ ≤ C*J (T-t) := by
    change ‖R t*fractionalPrimeTest (T-t)‖ ≤ _
    rw [Real.norm_eq_abs,abs_mul]
    apply (mul_le_mul_of_nonneg_right (hR t) (abs_nonneg _)).trans_eq
    have he : J (T-t)=Real.exp (r*(T-t))*|fractionalPrimeTest (T-t)| := by
      have h := congrArg abs (fractionalPrimeTest_tilt_eq r (T-t))
      simpa only [abs_mul,abs_neg,abs_of_pos (Real.exp_pos _)] using h.symm
    have htime : Real.exp (-r*T)*Real.exp (r*(T-t))=Real.exp (-r*t) := by
      rw [← Real.exp_add,show -r*T+r*(T-t)= -r*t by ring]
    dsimp only [C]
    rw [he,← htime]; ring
  have hI : Integrable f := hmaj.mono' (hm.mul (measurable_fractionalPrimeTest.comp
    (measurable_const.sub measurable_id))).aestronglyMeasurable (Eventually.of_forall hpt)
  refine ⟨hI,(integral_mono hI.abs hmaj hpt).trans_eq ?_⟩
  change (∫ t : ℝ, C*J (T-t))=_
  rw [integral_const_mul,integral_sub_left_eq_self J volume T]
  dsimp only [C]; ring

private theorem measurable_sievedReference (S : Finset Nat.Primes) {Φ : ℝ → ℝ} (hc : Continuous Φ) :
    Measurable (sievedIntegerReference S Φ) := by
  unfold sievedIntegerReference sievedSum
  apply Measurable.div_const
  apply Measurable.tsum
  intro n
  by_cases h : n.Coprime (sievePrimorial S)
  · simp only [indicator_of_mem (show n ∈ {m : ℕ | m.Coprime (sievePrimorial S)} from h),continuousIntegerAtom]
    fun_prop
  · simp only [indicator_of_notMem (show n ∉ {m : ℕ | m.Coprime (sievePrimorial S)} from h)]
    exact measurable_const

private theorem measurable_primeDivisorWave (p : Nat.Primes) {Φ : ℝ → ℝ} (hc : Continuous Φ) :
    Measurable (primeDivisorWave p Φ) := by
  apply Measurable.tsum
  intro n
  by_cases h : (p:ℕ) ∣ n <;> simp only [h,if_true,if_false,continuousIntegerAtom] <;> fun_prop

private theorem criticalState_odd_fractional_response {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1/2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      let f := fun t => oddCentredMangoldtWave Φ t*fractionalPrimeTest (T-t)
      Integrable f ∧ |∫ t, f t| ≤ B*Real.exp (-r*T) := by
  let V := fun t : ℝ => ∑' n : ℕ, (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let N := sievedIntegerReference {twoPrime} Φ
  let D := fun t : ℝ => integerReferenceWave Φ t-N t
  let R := primeDivisorWave twoPrime Φ
  let A := ∫ u, Real.exp (-u/2)*Φ u
  have hmD := (continuous_integerReferenceWave hc hC hb).measurable.sub
    (measurable_sievedReference {twoPrime} hc)
  have hD : MemLp (fun t : ℝ => Real.exp (r*t)*D t) 2 := by
    have h₁ := criticalState_subcritical_integer_error hW ht hF hc he hC hb hr hr'
    have h₂ := (criticalState_sieved_integer_quadrature hW ht hF hc he hC hb hr hr' {twoPrime}).1
    apply MemLp.ae_eq _ (h₁.sub h₂)
    refine Eventually.of_forall fun t => ?_
    change Real.exp (r*t)*(integerReferenceWave Φ t-Real.exp (t/2)*A)-
      Real.exp (r*t)*(N t-Real.exp (t/2)*A)=Real.exp (r*t)*D t
    dsimp only [D]; ring
  obtain ⟨B₁,h₁,hV⟩ := criticalState_integerCentred_fractional_response hW ht hF hc he hs hC hb hr hr'
  obtain ⟨B₂,h₂,hD'⟩ := tilted_discrepancy_fractional_test_bound hmD hr hr' hD
  have hsup (u : ℝ) : |Φ u| ≤ C := by
    rcases le_or_gt 0 u with h | h
    · simpa only [hs u h,abs_zero] using hC
    exact (hb _).trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith only [h])))
  obtain ⟨M,hM,hR⟩ := primeDivisorWave_bound twoPrime hC hsup hs hr hr'
  obtain ⟨B₃,h₃,hR'⟩ := bounded_tilt_floor_response (measurable_primeDivisorWave twoPrime hc) hM hr hr' hR
  refine ⟨B₁+B₂+B₃,by positivity,fun T hT => ?_⟩
  let K := fun t : ℝ => fractionalPrimeTest (T-t)
  have hv := hV T hT
  have hd := hD' T
  have hq := hR' T
  have hrow (t : ℝ) : oddCentredMangoldtWave Φ t=V t+D t-R t := by
    dsimp only [V,D,R,N]
    rw [oddCentredMangoldtWave_eq hb,centred_mangoldt_atom_sum_split hb,mangoldt_atom_sum_split hb]; ring
  have hF' : (fun t => oddCentredMangoldtWave Φ t*K t)=fun t => (V t*K t+D t*K t)-R t*K t :=
    funext fun t => by rw [hrow]; ring
  change Integrable (fun t => oddCentredMangoldtWave Φ t*K t) ∧ |∫ t, oddCentredMangoldtWave Φ t*K t| ≤ _
  rw [hF',integral_sub (f := fun t => V t*K t+D t*K t) (hv.1.add hd.1) hq.1,
    integral_add (f := fun t => V t*K t) (g := fun t => D t*K t) hv.1 hd.1]
  refine ⟨(hv.1.add hd.1).sub hq.1,(abs_sub _ _).trans ?_⟩
  rw [add_mul,add_mul]
  exact add_le_add ((abs_add_le ..).trans (add_le_add hv.2 (abs_integral_le_integral_abs.trans hd.2)))
    (abs_integral_le_integral_abs.trans hq.2)

private theorem criticalState_damped_odd_wave {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {d : ℝ} (hd : zetaZeroAbscissa-1/2 < d) :
    MemLp (fun t : ℝ => Real.exp (-(d*t))*oddCentredMangoldtWave Φ t) 2 halfLineLaplaceMeasure := by
  let A := ∫ u, Real.exp (-u/2)*Φ u
  let W := fun t : ℝ => ∑' n : ℕ, vonMangoldt n*continuousIntegerAtom Φ n t
  let E := fun t : ℝ => W t-Real.exp (t/2)*A
  let D := sievedReferenceError {twoPrime} Φ A
  let R := primeDivisorWave twoPrime Φ
  let w := fun t : ℝ => Real.exp (-(d*t))
  have hw : Measurable w := by dsimp only [w]; fun_prop
  have hd0 := (sub_nonneg.mpr half_le_zetaZeroAbscissa).trans_lt hd
  have hmW : Measurable W := Measurable.tsum fun _ => measurable_const.mul
    (measurable_const.mul (hc.measurable.comp (measurable_id.sub measurable_const)))
  have hmE : Measurable E := hmW.sub ((by fun_prop : Measurable fun t : ℝ => Real.exp (t/2)).mul measurable_const)
  have hZ := memLp_damped_prime_sum_sub_pole_of_abscissa hW ht hF hd
  have hA : negativeHalfLineLaplace (cx F) (-(1/2))=(A:ℂ) := by
    rw [show (-(1/2):ℂ)=((-(1/2):ℝ):ℂ) by norm_num,negativeHalfLineLaplace_ofReal]
    apply congrArg Complex.ofReal
    apply integral_congr_ae
    filter_upwards [he] with u hu
    rw [hu,show -(1/2:ℝ)*u= -u/2 by ring,mul_comm]
  have hshift : ∀ᵐ t ∂volume, ∀ n : ℕ, F (t-Real.log n)=Φ (t-Real.log n) :=
    ae_all_iff.2 fun n => (measurePreserving_sub_right volume (Real.log n)).quasiMeasurePreserving.ae_eq_comp he
  have hE : MemLp (fun t => w t*E t) 2 halfLineLaplaceMeasure := by
    apply hZ.mono (hw.mul hmE).aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae hshift] with t ht'
    have hrow : (∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ))=(W t:ℂ) := by
      dsimp only [W]; rw [Complex.ofReal_tsum]
      apply tsum_congr fun n => ?_
      have hn : primeAtom n=vonMangoldt n/Real.sqrt n := by
        by_cases h : 2 ≤ n
        · exact if_pos h
        · rcases (show n=0 ∨ n=1 by omega) with rfl | rfl <;> simp [primeAtom]
      rw [ht' n,← Complex.ofReal_mul,hn]
      apply congrArg Complex.ofReal
      simp only [continuousIntegerAtom,div_eq_mul_inv,mul_assoc]
    change ‖w t*E t‖ ≤ ‖expRay (d:ℂ) t*((∑' n : ℕ, (primeAtom n:ℂ)*(F (t-Real.log n):ℂ))-
      negativeHalfLineLaplace (cx F) (-(1/2))*(Real.exp (t/2):ℂ))‖
    rw [hrow,hA,← Complex.ofReal_mul,← Complex.ofReal_sub,norm_mul,norm_expRay,
      Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _ : 0<w t)]
    change _ ≤ Real.exp (-(d*t))*|W t-A*Real.exp (t/2)|
    rw [mul_comm A]; exact le_rfl
  have hD₀ := (criticalState_sieved_integer_quadrature hW ht hF hc he hC hb (β := 0)
    le_rfl (by norm_num) {twoPrime}).1
  have hD : MemLp D 2 halfLineLaplaceMeasure := by
    apply MemLp.mono_measure (μ := volume) _ Measure.restrict_le_self
    simpa only [zero_mul,Real.exp_zero,one_mul,D,A] using hD₀
  have hDw : MemLp (fun t => w t*D t) 2 halfLineLaplaceMeasure := by
    apply hD.mono (hw.aestronglyMeasurable.mul hD.1)
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with t ht'
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _ : 0<w t),Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hd0.le ht'.le)))
  have hsup (u : ℝ) : |Φ u| ≤ C := by
    rcases le_or_gt 0 u with h | h
    · simpa only [hs u h,abs_zero] using hC
    exact (hb _).trans (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith only [h])))
  obtain ⟨M,hM,hR⟩ := primeDivisorWave_bound twoPrime hC hsup hs (r := 0) le_rfl (by norm_num)
  have hRw : MemLp (fun t => w t*R t) 2 halfLineLaplaceMeasure := by
    apply ((memLp_two_expRay_restrict (w := (d:ℂ)) (by exact hd0) 0).norm.const_mul M).mono
      (hw.mul (measurable_primeDivisorWave twoPrime hc)).aestronglyMeasurable
    refine Eventually.of_forall fun t => ?_
    change ‖w t*R t‖ ≤ ‖M*‖expRay (d:ℂ) t‖‖
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _ : 0<w t),
      Real.norm_of_nonneg (mul_nonneg hM (norm_nonneg _)),norm_expRay,Complex.ofReal_re,mul_comm M]
    exact mul_le_mul_of_nonneg_left (by simpa only [neg_zero,zero_mul,Real.exp_zero,mul_one,R] using hR t)
      (Real.exp_pos _).le
  apply MemLp.ae_eq _ ((hE.sub hRw).sub hDw)
  exact Eventually.of_forall fun t => by
    change (w t*E t-w t*R t)-w t*D t=w t*oddCentredMangoldtWave Φ t
    rw [oddCentredMangoldtWave_eq hb]
    dsimp only [E,D,R,W,sievedReferenceError]
    ring

/-- Both arithmetic rows vanish at every even integer. Averaging only the
second time variable makes their signed product exponentially integrable. -/
theorem riemannHypothesis_or_odd_mixed_prime_covariance : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 ≤ ε → ε < 1-zetaZeroAbscissa →
        let V := oddCentredMangoldtWave Φ
        let Y := fun T : ℝ => ∫ t, V t*fractionalPrimeTest (T-t)
        IntegrableOn (fun T : ℝ => Real.exp (ε*T)*|V T*Y T|) (Ioi 0) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun ε hε hε' => ?_⟩
  obtain ⟨d,hd,hd'⟩ := exists_between (by linarith only [hε'] : zetaZeroAbscissa-1/2 < 1/2-ε)
  obtain ⟨r,hr,hr'⟩ := exists_between (by linarith only [hd'] : ε+d < 1/2)
  have hd0 := (sub_nonneg.mpr half_le_zetaZeroAbscissa).trans_lt hd
  obtain ⟨B,hB,h⟩ := criticalState_odd_fractional_response hW ht hF hc he hs hC hb
    ((add_nonneg hε hd0.le).trans hr.le) hr'
  have hmV : Measurable (oddCentredMangoldtWave Φ) := by
    apply Measurable.tsum
    intro n
    by_cases h : 2 ∣ n <;> simp only [h,if_true,if_false,continuousIntegerAtom] <;> fun_prop
  let f := fun z : ℝ × ℝ => oddCentredMangoldtWave Φ z.2*fractionalPrimeTest (z.1-z.2)
  have hmf : Measurable f := (hmV.comp measurable_snd).mul
    (measurable_fractionalPrimeTest.comp (measurable_fst.sub measurable_snd))
  exact integrable_mixed_response (criticalState_damped_odd_wave hW ht hF hc he hs hC hb hd)
    hmf.stronglyMeasurable.integral_prod_right'.measurable hB (fun t ht' => (h t ht').2) hr

#print axioms riemannHypothesis_or_odd_mixed_prime_covariance
end GaloisForLFunctions.ExclusionOfTheCriticalState
