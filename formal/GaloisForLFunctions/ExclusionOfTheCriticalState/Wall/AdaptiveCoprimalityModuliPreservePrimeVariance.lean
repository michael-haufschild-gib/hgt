import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeVarianceAfterACommonSieve

/-!
# Prime variance with an adaptive coprimality modulus

The Dirichlet weights of all finite sieves are summable after their
variance costs. The resulting single positive integrable function
dominates every sieve with admissible primorial at each time.
-/

noncomputable section
open MeasureTheory Filter Set Topology Finset
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory
  HTGeometry _root_.RHTower

/-- Logarithm of the product of the sieving primes. -/
def sieveLogSize (P : Finset Nat.Primes) : ℝ := ∑ p ∈ P, Real.log (p:ℕ)

theorem sieveLogSize_eq_log_primorial (P : Finset Nat.Primes) :
    sieveLogSize P=Real.log (sievePrimorial P) := by
  rw [sieveLogSize,sievePrimorial,Nat.cast_prod,Real.log_prod]
  exact fun p _ => Nat.cast_ne_zero.2 p.2.ne_zero

/-- Finite subset products of a nonnegative summable sequence have finite
sum, bounded on any finite family by the full exponential majorant. -/
private theorem summable_subset_products {ι : Type*} {v : ι → ℝ} (hn : ∀ i, 0 ≤ v i) (hv : Summable v) :
    Summable (fun P : Finset ι => ∏ i ∈ P, v i) := by
  classical
  apply summable_of_sum_le (fun P => prod_nonneg fun i _ => hn i) (c := Real.exp (∑' i, v i))
  intro S
  let Q := S.biUnion id
  have hs : S ⊆ Q.powerset := fun P hP => mem_powerset.2 (fun i hi => mem_biUnion.2 ⟨P,hP,hi⟩)
  calc _ ≤ ∑ P ∈ Q.powerset, ∏ i ∈ P, v i :=
         sum_le_sum_of_subset_of_nonneg hs fun P _ _ => prod_nonneg fun i _ => hn i
    _ = ∏ i ∈ Q, (1+v i) := (prod_one_add Q).symm
    _ ≤ ∏ i ∈ Q, Real.exp (v i) := by
         apply prod_le_prod (fun i _ => add_nonneg zero_le_one (hn i))
         intro i _; simpa only [add_comm (1:ℝ)] using Real.add_one_le_exp (v i)
    _ ≤ _ := by rw [← Real.exp_sum]; exact Real.exp_le_exp.2 (hv.sum_le_tsum Q (fun i _ => hn i))

/-- Above one the Dirichlet weight of the primorial pays for all subsets,
with the full variance cost at each removed prime. -/
theorem summable_primorial_variance_cost {s : ℝ} (hs : 1 < s) :
    Summable (fun P : Finset Nat.Primes => (16:ℝ)^P.card*Real.exp (-(s*sieveLogSize P))) := by
  let v := fun p : Nat.Primes => 16*((p:ℕ):ℝ)^(-s)
  have hv : Summable v := (((Real.summable_nat_rpow.2 (by linarith only [hs] : -s < -1)).comp_injective
    (show Function.Injective (fun p : Nat.Primes => (p:ℕ)) from Subtype.coe_injective))).mul_left 16
  apply (summable_subset_products (fun p => mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hv).congr
  intro P
  have h (p : Nat.Primes) : ((p:ℕ):ℝ)^(-s)=Real.exp (-(s*Real.log (p:ℕ))) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast p.2.pos)]; congr 1; ring
  simp only [prod_mul_distrib,prod_const,h,← Real.exp_sum,sieveLogSize]
  rw [Finset.mul_sum,← Finset.sum_neg_distrib]

/-- An integrable majorant simultaneously bounds each member of a countable
positive family whose integrals form a summable series. -/
private theorem common_majorant_of_summable_integrals {ι : Type*} [Countable ι] {μ : Measure ℝ}
    {f : ι → ℝ → ℝ} (hf : ∀ i, Integrable (f i) μ) (hn : ∀ i t, 0 ≤ f i t)
    (hs : Summable fun i => ∫ t, f i t ∂μ) :
    ∃ B : ℝ → ℝ, Integrable B μ ∧ ∀ᵐ t ∂μ, ∀ i, f i t ≤ B t := by
  let b := fun t : ℝ => ∑' i, ENNReal.ofReal (f i t)
  have hm (i : ι) : AEMeasurable (fun t => ENNReal.ofReal (f i t)) μ :=
    (hf i).aemeasurable.ennreal_ofReal
  have hb : AEMeasurable b μ := AEMeasurable.tsum hm
  have he (i : ι) := ofReal_integral_eq_lintegral_ofReal (hf i) (Eventually.of_forall (hn i))
  have hfin : (∫⁻ t, b t ∂μ) ≠ ⊤ := by
    dsimp only [b]; rw [lintegral_tsum hm]
    simp_rw [← he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg (hn i)) hs]
    exact ENNReal.ofReal_ne_top
  refine ⟨fun t => (b t).toReal,integrable_toReal_of_lintegral_ne_top hb hfin,?_⟩
  filter_upwards [ae_lt_top' hb hfin] with t ht
  intro i
  have hi : ENNReal.ofReal (f i t) ≤ b t := ENNReal.le_tsum i
  simpa only [ENNReal.toReal_ofReal (hn i t)] using ENNReal.toReal_mono ht.ne hi

private theorem adaptive_sieve_envelope {V : Finset Nat.Primes → ℝ → ℝ} (hV : ∀ P t, 0 ≤ V P t)
    {a : ℝ} (hmom : ∀ {r : ℝ}, 0 ≤ r → r < a → ∃ M : ℝ, 0 ≤ M ∧ ∀ P : Finset Nat.Primes,
      IntegrableOn (fun t : ℝ => Real.exp (r*t)*V P t) (Ioi 0) ∧
        (∫ t in Ioi (0:ℝ), Real.exp (r*t)*V P t) ≤ M*(16:ℝ)^P.card)
    {b γ : ℝ} (hb0 : 0 ≤ b) (hγ : 0 ≤ γ) (hroom : b+γ < a) :
    ∃ A : ℝ → ℝ, IntegrableOn A (Ioi 0) ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ P : Finset Nat.Primes,
      sieveLogSize P ≤ γ*t → Real.exp (b*t)*V P t ≤ A t := by
  obtain ⟨r,hr,hr'⟩ := exists_between hroom
  let ε := (r-(b+γ))/(2*(1+γ))
  have hε : 0 < ε := div_pos (sub_pos.2 hr) (by positivity)
  let s := 1+ε
  have hs : 1 < s := lt_add_of_pos_right _ hε
  have hεγ : ε*γ ≤ (r-(b+γ))/2 := by
    calc _ ≤ ε*(1+γ) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hε.le
      _ = _ := by dsimp only [ε]; field_simp [show 1+γ ≠ 0 by positivity] <;> ring
  have hbr : b+s*γ ≤ r := by dsimp only [s]; linarith only [hεγ,hr]
  obtain ⟨M,_,hP⟩ := hmom ((add_nonneg hb0 hγ).trans hr.le) hr'
  let w := fun P : Finset Nat.Primes => Real.exp (-(s*sieveLogSize P))
  let f := fun (P : Finset Nat.Primes) (t : ℝ) => w P*(Real.exp (r*t)*V P t)
  have hi (P) : Integrable (f P) halfLineLaplaceMeasure := (hP P).1.const_mul _
  have hn (P t) : 0 ≤ f P t := mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (hV _ _))
  have hsum : Summable fun P => ∫ t, f P t ∂halfLineLaplaceMeasure := by
    apply Summable.of_nonneg_of_le (fun P => integral_nonneg (hn P)) _ ((summable_primorial_variance_cost hs).mul_right M)
    intro P
    change (∫ t in Ioi (0:ℝ), w P*(Real.exp (r*t)*V P t)) ≤ _
    rw [integral_const_mul]
    exact (mul_le_mul_of_nonneg_left (hP P).2 (Real.exp_pos _).le).trans_eq (by ring)
  obtain ⟨A,hA,hmajor⟩ := common_majorant_of_summable_integrals hi hn hsum
  refine ⟨A,hA,?_⟩
  filter_upwards [hmajor,ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t hbound ht0
  intro P hsize
  apply le_trans _ (hbound P)
  change Real.exp (b*t)*V P t ≤ w P*(Real.exp (r*t)*V P t)
  rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (hV _ _)
  dsimp only [w]; rw [← Real.exp_add]; apply Real.exp_le_exp.2
  linarith only [mul_le_mul_of_nonneg_left hsize (zero_lt_one.trans hs).le,
    mul_le_mul_of_nonneg_right hbr (le_of_lt ht0)]

/-- One integrable envelope pays for every choice of sieving primes whose
product is at most exp(γt), even when the choice varies with t. -/
theorem criticalState_adaptive_prime_variance_envelope {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {b γ : ℝ}
    (hb0 : 0 ≤ b) (hγ : 0 ≤ γ) (hroom : b+γ < 1-zetaZeroAbscissa) :
    ∃ A : ℝ → ℝ, IntegrableOn A (Ioi 0) ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ P : Finset Nat.Primes,
      sieveLogSize P ≤ γ*t →
        Real.exp (b*t)*|(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2| ≤ A t := by
  exact adaptive_sieve_envelope
    (V := fun P t => |(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2|)
    (fun _ _ => abs_nonneg _)
    (fun hr hr' => criticalState_commonSieve_variance_bound hW ht hF hc he hC hb hr hr') hb0 hγ hroom

/-- For the wave amplitude, every modulus below exp(γt) with γ < 1
is allowed. Its squared perturbation has an integrable envelope at every
rate b < 1 − γ. -/
theorem criticalState_adaptive_prime_wave_envelope {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal)) {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) {b γ : ℝ}
    (hb0 : 0 ≤ b) (hγ : 0 ≤ γ) (hroom : b+γ < 1) :
    ∃ A : ℝ → ℝ, IntegrableOn A (Ioi 0) ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ P : Finset Nat.Primes,
      sieveLogSize P ≤ γ*t → Real.exp (b*t)*(ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t)^2 ≤ A t := by
  apply adaptive_sieve_envelope (V := fun P t => (ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t)^2)
    (fun _ _ => sq_nonneg _) _ hb0 hγ hroom
  intro r hr hr'
  let β := r/2
  have hβ : 0 ≤ β := div_nonneg hr (by norm_num)
  have hβ' : β < 1/2 := by dsimp only [β]; linarith only [hr']
  obtain ⟨B,_,hP⟩ := criticalState_commonSieve_tilted_error hW ht hF hc he hC hb hβ hβ'
  refine ⟨B^2,sq_nonneg _,fun P => ?_⟩
  let f := fun t : ℝ => ordinaryPrimePolarError Φ t-commonSievedPrimeError P Φ t
  let g := fun t : ℝ => Real.exp (β*t)*f t
  have heq : (fun t : ℝ => Real.exp (r*t)*f t^2)=fun t => g t^2 := by
    funext t
    dsimp only [g]; rw [mul_pow,pow_two (Real.exp _),← Real.exp_add,show β*t+β*t=r*t by dsimp only [β]; ring]
  obtain ⟨hg,hnorm⟩ := hP P
  have hi : Integrable (fun t => g t^2) := by
    simpa only [Real.norm_eq_abs,sq_abs] using (memLp_two_iff_integrable_sq_norm hg.1).1 hg
  refine ⟨heq.symm ▸ hi.integrableOn,?_⟩
  change (∫ t in Ioi (0:ℝ), Real.exp (r*t)*f t^2) ≤ _
  calc _ = ∫ t in Ioi (0:ℝ), g t^2 := setIntegral_congr_fun measurableSet_Ioi fun t _ => congrFun heq t
    _ ≤ ∫ t, g t^2 := setIntegral_le_integral hi (Eventually.of_forall fun _ => sq_nonneg _)
    _ = _ := integral_sq_eq_lpNorm_sq hg
    _ ≤ ((4:ℝ)^P.card*B)^2 := pow_le_pow_left₀ lpNorm_nonneg hnorm 2
    _ = B^2*(16:ℝ)^P.card := by rw [mul_pow,← pow_mul,Nat.mul_comm,pow_mul]; norm_num; ring

/-- One actual state has the adaptive bound for every admissible pair of
rates. The majorant is independent of the chosen time-dependent sieve. -/
theorem riemannHypothesis_or_adaptive_prime_variance : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ b γ : ℝ, 0 ≤ b → 0 ≤ γ → b+γ < 1-zetaZeroAbscissa →
        ∃ A : ℝ → ℝ, IntegrableOn A (Ioi 0) ∧ ∀ᵐ t ∂halfLineLaplaceMeasure, ∀ P : Finset Nat.Primes,
          sieveLogSize P ≤ γ*t →
            Real.exp (b*t)*|(commonSievedPrimeError P Φ t)^2-(ordinaryPrimePolarError Φ t)^2| ≤ A t := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun _ _ =>
    criticalState_adaptive_prime_variance_envelope hW ht hF hc he hC hb⟩

#print axioms riemannHypothesis_or_adaptive_prime_variance
#print axioms criticalState_adaptive_prime_variance_envelope
end GaloisForLFunctions.ExclusionOfTheCriticalState
