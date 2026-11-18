import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SievingTheIntegerReferenceWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Analysis.TheCostOfSievingAtTheSquareOfTheLogarithmicHorizon

/-!
# The density reference after sieving to quadratic logarithmic height

The cumulative absolute quadrature error stays subexponential even when all
primes up to the square of the observation horizon are removed from the
integer reference. The bound is uniform in every subset of these primes.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory HTGeometry

private theorem empty_reference {Φ : ℝ → ℝ} {C : ℝ} (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (t : ℝ) :
    sievedIntegerReference ∅ Φ t = integerReferenceWave Φ t := by
  rw [sievedIntegerReference,sieveDensity_empty,div_one,sievedSum,← tsum_continuousIntegerAtom hb]
  exact tsum_congr fun n => indicator_of_mem (by simp : n ∈ {m : ℕ | m.Coprime (sievePrimorial ∅)}) _

private theorem integerReference_integrableOn_left {Φ : ℝ → ℝ} (hm : Continuous Φ) {C : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) : IntegrableOn (integerReferenceWave Φ) (Iic 0) := by
  let m := fun n : ℕ => 1/(n:ℝ)^2
  have hs : Summable m := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hmeas : Measurable (integerReferenceWave Φ) := by
    unfold integerReferenceWave
    exact Measurable.tsum fun n => by unfold continuousIntegerAtom; fun_prop
  apply ((integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<2) 0).const_mul (C*∑' n, m n)).mono'
    hmeas.aestronglyMeasurable
  filter_upwards with t
  rw [← tsum_continuousIntegerAtom hb,Real.norm_eq_abs]
  have h := (summable_continuousIntegerAtom hb t).abs
  calc _ ≤ ∑' n : ℕ, |continuousIntegerAtom Φ n t| := by
           simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (summable_continuousIntegerAtom hb t).norm
    _ ≤ ∑' n : ℕ, (C*Real.exp (2*t))*m n := by
           apply h.tsum_le_tsum _ (hs.mul_left _)
           intro n
           rcases Nat.eq_zero_or_pos n with rfl | hn
           · simp [continuousIntegerAtom,m]
           · exact continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ) ≤ n) t
    _ = _ := by rw [tsum_mul_left]; ring

private theorem empty_mass_eventually {Φ : ℝ → ℝ} (hm : Continuous Φ) {C : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (A : ℝ)
    (hi : ∀ T : ℝ, IntegrableOn (fun t => integerReferenceWave Φ t-Real.exp (t/2)*A) (Ioc 0 T))
    (hz : Tendsto (fun T : ℝ => (∫ t in Ioc 0 T, |integerReferenceWave Φ t-Real.exp (t/2)*A|)/T) atTop (𝓝 0)) :
    (∀ᶠ T : ℝ in atTop, IntegrableOn (sievedReferenceError ∅ Φ A) (Iic T)) ∧
      Tendsto (fun T : ℝ => (∫ t in Iic T, |sievedReferenceError ∅ Φ A t|)/T) atTop (𝓝 0) := by
  let g := fun t : ℝ => integerReferenceWave Φ t - Real.exp (t/2)*A
  have he : sievedReferenceError ∅ Φ A = g := funext fun t => by rw [sievedReferenceError,empty_reference hb]
  have hp : IntegrableOn (fun t : ℝ => Real.exp (t/2)*A) (Iic 0) := by
    have hi' : IntegrableOn (fun t : ℝ => Real.exp ((1/2)*t)*A) (Iic (0:ℝ)) :=
      (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) 0).mul_const A
    apply hi'.congr_fun _ measurableSet_Iic
    intro t _
    exact congrArg (fun x : ℝ => Real.exp x*A) (show (1/2:ℝ)*t=t/2 by ring)
  have hn : IntegrableOn g (Iic 0) := (integerReference_integrableOn_left hm hb).sub hp
  have hD : Tendsto (fun T : ℝ => (∫ t in Iic 0, |g t|)/T) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  constructor
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    rw [he,← Iic_union_Ioc_eq_Iic hT]; exact hn.union (hi T)
  · have h := hD.add hz
    rw [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
    rw [he,← Iic_union_Ioc_eq_Iic hT,setIntegral_union
      (Set.disjoint_left.mpr fun _ ht ht' => ht'.1.not_ge ht) measurableSet_Ioc hn.abs (hi T).abs,add_div]

private theorem sieved_mass_le {P : Finset Nat.Primes} {Φ : ℝ → ℝ} {C A T : ℝ}
    (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) (hi : IntegrableOn (sievedReferenceError ∅ Φ A) (Iic T)) :
    (∫ t in Ioc 0 T, |sievedReferenceError P Φ A t|) ≤
      (∏ p ∈ P, (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹)*(∫ t in Iic T, |sievedReferenceError ∅ Φ A t|) := by
  have h := sievedReferenceError_integral_le P Φ A T (summable_continuousIntegerAtom hb) hi
  exact (setIntegral_mono_set h.1.abs (Eventually.of_forall fun _ => abs_nonneg _)
    (Eventually.of_forall fun _ ht => ht.2)).trans h.2

/-- Every removed prime has zero state weight throughout each late interval
[ηT,T], even when the sieve reaches T². -/
theorem smallPrimeAtoms_vanish_on_late_intervals {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ (p : Nat.Primes), ((p:ℕ):ℝ) ≤ T^2 → ∀ t : ℝ, η*T ≤ t →
      continuousIntegerAtom Φ (p:ℕ) t = 0 := by
  have hl := Real.isLittleO_log_id_atTop.bound (half_pos hη)
  filter_upwards [eventually_ge_atTop (1:ℝ),hl] with T hT hlog
  intro p hp t ht
  have hT0 := zero_lt_one.trans_le hT
  have hp0 : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.2.pos
  have hc := Real.log_le_log hp0 hp
  rw [Real.log_pow,Nat.cast_ofNat] at hc
  change ‖Real.log T‖ ≤ η/2*‖T‖ at hlog
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hT),abs_of_pos hT0] at hlog
  rw [continuousIntegerAtom,hs _ (by linarith only [hc,hlog,ht]),mul_zero]

/-- Sifting the same primes from the ordinary-prime wave leaves its value
exactly unchanged on the late observation interval. -/
theorem eventually_ordinaryPrimeWave_eq_sieved {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u = 0)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
      ∀ t : ℝ, η*T ≤ t → ordinaryPrimeWave Φ t =
        ∑' p : Nat.Primes, if p ∈ P then 0 else
          (_root_.RHTower.vonMangoldtAtom (p:ℕ):ℂ)*(Φ (t-Real.log (p:ℕ)):ℂ) := by
  filter_upwards [smallPrimeAtoms_vanish_on_late_intervals hs hη] with T hv
  intro P hP t ht
  apply tsum_congr fun p => ?_
  by_cases hp : p ∈ P
  · have hz := hv p (hP p hp) t ht
    have hp0 : (0:ℝ) < (p:ℕ) := by exact_mod_cast p.2.pos
    have hΦ := (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (Real.sqrt_pos.2 hp0).ne')
    simp [hp,hΦ]
  · simp [hp]

/-- Once two is removed, every odd-gap cross term of two sifted rows vanishes. -/
theorem sifted_odd_gap_product_eq_zero {P : Finset Nat.Primes} (h₂ : ⟨2,Nat.prime_two⟩ ∈ P)
    (f g : ℕ → ℝ) (n : ℕ) {d : ℕ} (hd : Odd d) :
    {k : ℕ | k.Coprime (sievePrimorial P)}.indicator f n *
      {k : ℕ | k.Coprime (sievePrimorial P)}.indicator g (n+d) = 0 := by
  have hdiv : 2 ∣ sievePrimorial P := Finset.dvd_prod_of_mem (fun p : Nat.Primes => (p:ℕ)) h₂
  by_cases hn : n.Coprime (sievePrimorial P)
  · have hnd : ¬(n+d).Coprime (sievePrimorial P) := by
      intro h
      obtain ⟨a,ha⟩ := Nat.coprime_two_right.1 (Nat.Coprime.of_dvd_right hdiv hn)
      obtain ⟨b,hb⟩ := hd
      obtain ⟨c,hc⟩ := Nat.coprime_two_right.1 (Nat.Coprime.of_dvd_right hdiv h)
      omega
    rw [indicator_of_notMem (show n+d ∉ {k : ℕ | k.Coprime (sievePrimorial P)} from hnd),mul_zero]
  · rw [indicator_of_notMem (show n ∉ {k : ℕ | k.Coprime (sievePrimorial P)} from hn),zero_mul]

/-- Failure of RH forces a state whose density reference can be supported on
integers having no prime factor up to T² at subexponential cost in absolute mass. -/
theorem riemannHypothesis_or_quadratically_sieved_density_reference : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧ IsCriticalHalfLineGroundState W₀ F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ (∀ u, 0 ≤ u → Φ u = 0) ∧
      (∀ P : Finset Nat.Primes, Tendsto (fun T : ℝ => (∫ t in Ioc 0 T,
        |sievedReferenceError P Φ (∫ u, Real.exp (-u/2)*F u) t|)/T) atTop (𝓝 0)) ∧
      ∀ᶠ T : ℝ in atTop, ∀ P : Finset Nat.Primes, (∀ p ∈ P, ((p:ℕ):ℝ) ≤ T^2) →
        (∫ t in Ioc 0 T, |sievedIntegerReference P Φ t - Real.exp (t/2)*(∫ u, Real.exp (-u/2)*F u)|) ≤
          T*Real.exp (8*Real.sqrt T+64*T/Real.log T) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨Φ,hΦ,heq,⟨C,hC,hb⟩,hi,hz⟩ := criticalState_integerReference_zero_mean_error hW ht hF
  obtain ⟨_,_,Ψ,hΨ,heqΨ,hs,_,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hΨΦ : Ψ = Φ := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heqΨ.symm.trans heq)
  subst Ψ
  let A := ∫ u, Real.exp (-u/2)*F u
  obtain ⟨hi0,hmean⟩ := empty_mass_eventually hΦ hb A hi hz
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,heq,hs,?_,?_⟩
  · intro P
    let K := ∏ p ∈ P, (1-(Real.sqrt (p:ℕ))⁻¹)⁻¹
    have hu := (tendsto_const_nhds (x := K)).mul hmean
    rw [mul_zero] at hu
    apply squeeze_zero' _ _ hu
    · filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
      exact div_nonneg (integral_nonneg fun _ => abs_nonneg _) hT
    · filter_upwards [eventually_ge_atTop (0:ℝ),hi0] with T hT hiT
      exact (div_le_div_of_nonneg_right (sieved_mass_le (P := P) hb hiT) hT).trans_eq (by ring)
  · filter_upwards [eventually_ge_atTop (3:ℝ),hi0,hmean.eventually_lt_const zero_lt_one] with T hT hiT hsmall
    intro P hP
    have hT0 : 0 < T := by linarith
    have hbase := ((div_lt_iff₀ hT0).1 hsmall).le
    rw [one_mul] at hbase
    apply (sieved_mass_le (P := P) hb hiT).trans
    rw [mul_comm T]
    exact mul_le_mul (sieve_half_cost_le P hT hP) hbase (integral_nonneg fun _ => abs_nonneg _) (Real.exp_pos _).le

#print axioms riemannHypothesis_or_quadratically_sieved_density_reference
#print axioms sifted_odd_gap_product_eq_zero

end GaloisForLFunctions.ExclusionOfTheCriticalState
