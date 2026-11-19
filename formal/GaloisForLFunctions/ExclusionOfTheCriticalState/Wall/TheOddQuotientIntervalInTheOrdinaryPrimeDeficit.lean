import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.AnOrientedQuotientIntervalAfterRestrictingTheState

/-!
# An odd-quotient interval inside the ordinary-prime deficit

Translating each atom by its logarithmic abscissa makes the numerator of its
fractional weight common to all integers. The physical edge then cuts one
interval. The prime discrepancy of a single binary digit on this interval
retains the sign of the adverse contribution to the original test.
-/

noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Integer abscissae in the original middle test at fixed state displacement. -/
def ordinaryBandAtDisplacement (k L : ℕ) (T v : ℝ) : Finset ℕ :=
  ordinaryTestDisplacementSupport k L T v

/-- For even H this factorial ratio is the central binomial coefficient. -/
def halfFactorialQuotient (H : ℕ) : ℕ :=
  H.factorial/((H/2).factorial*(H/2).factorial)

private theorem halves_dvd (H : ℕ) : (H/2).factorial*(H/2).factorial ∣ H.factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (by omega))

/-- Above the square root, the prime valuation of the factorial ratio
is exactly the parity of the quotient, also for odd numerators. -/
theorem halfFactorialQuotient_valuation {H p : ℕ} (hp : p.Prime) (h : H<p^2) :
    (halfFactorialQuotient H).factorization p = H/p%2 := by
  have hleg (n : ℕ) (hn : n<p^2) : n.factorial.factorization p=n/p := by
    have hlog : Nat.log p n<2 := by
      rcases Nat.eq_zero_or_pos n with rfl|hpos
      · simp
      · exact Nat.log_lt_of_lt_pow hpos.ne' hn
    rw [Nat.factorization_factorial hp hlog]
    simp only [show Finset.Ico 1 2 = {1} by decide,Finset.sum_singleton,pow_one]
  rw [halfFactorialQuotient,Nat.factorization_div (halves_dvd H),Finsupp.coe_tsub,Pi.sub_apply,
    Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),Finsupp.coe_add,Pi.add_apply,
    hleg H h,hleg (H/2) ((Nat.div_le_self _ _).trans_lt h)]
  have he : H/2/p=H/p/2 := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 p]
  rw [he]; omega

/-- The odd-quotient discrepancy is the logarithmic mass of prime divisors
of one explicit integer minus the count of all selected reference atoms. -/
theorem oddQuotientPrimeExcess_eq_factorial_divisors (S : Finset ℕ) (H : ℕ)
    (hs : ∀ p ∈ S, Real.sqrt H < p) :
    oddQuotientPrimeExcess S H =
      (∑ p ∈ S with p.Prime ∧ p ∣ halfFactorialQuotient H, Real.log p) -
      ((S.filter fun n => H/n%2=1).card:ℝ) := by
  have hpos : halfFactorialQuotient H ≠ 0 := by
    intro hz
    have h := Nat.div_mul_cancel (halves_dvd H)
    change halfFactorialQuotient H * _ = _ at h
    rw [hz,zero_mul] at h
    exact (Nat.factorial_ne_zero H) h.symm
  have hcard : ((S.filter fun n => H/n%2=1).card:ℝ) =
      ∑ n ∈ S, if H/n%2=1 then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [oddQuotientPrimeExcess,hcard,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hm
  by_cases hp : p.Prime
  · have hlt : (H:ℝ) < (p:ℝ)^2 := (Real.sqrt_lt' (Nat.cast_pos.mpr hp.pos)).mp (hs p hm)
    have hf := halfFactorialQuotient_valuation hp (by exact_mod_cast hlt : H<p^2)
    have hd : p ∣ halfFactorialQuotient H ↔ H/p%2=1 := by
      constructor
      · intro h
        have h1 := hp.factorization_pos_of_dvd hpos h
        rw [hf] at h1
        omega
      · intro h
        by_contra hn
        rw [Nat.factorization_eq_zero_of_not_dvd hn,h] at hf
        omega
    by_cases h : H/p%2=1 <;> simp [ordinaryPrimeExcessCoeff,hp,hd,h]
  · by_cases h : H/p%2=1 <;> simp [ordinaryPrimeExcessCoeff,hp,h]

private def deficitReading (Φ : ℝ → ℝ) (T : ℝ) (k L : ℕ) : ℝ :=
  (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t))

/-- At the same late tests as the exterior gain, a single ordinary-prime
discrepancy on integers with odd quotient exceeds the square root of its
integer numerator by a power of the test scale. Every integer in the interval
is strictly above that square root. The orientation is opposite the state
at the displacement producing this digit. -/
theorem riemannHypothesis_or_odd_quotient_prime_deficit : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (c g : ℝ), 0<W ∧
      (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<c ∧ 0<g ∧ ∀ η : ℝ, 0<η → η≤1 →
      ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (v s : ℝ) (j H a b : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
          H=⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊ ∧ Real.exp (T i)≤H ∧
          (H:ℝ)^(g/6) ≤ Real.exp (g*T i) ∧ k i<a ∧ a≤b ∧ b≤L i ∧ Real.sqrt H<a ∧
          ((ordinaryBandAtDisplacement (k i) (L i) (T i) v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
          c*Real.exp (g*T i)*Real.sqrt H < (1+Real.log 4)*b ∧
          c*Real.exp (g*T i)*Real.sqrt H <
            s*((∑ p ∈ Finset.Icc a b with p.Prime ∧ p ∣ halfFactorialQuotient H, Real.log p) -
              (((Finset.Icc a b).filter fun n => H/n%2=1).card:ℝ)) := by
  rcases riemannHypothesis_or_ordinary_prime_diagonal_band with hr | ⟨W,F,Φ,A,g,hW,ht,hF,hc,he,hA,hg,h⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ v, Φ v
  let M := |m| *(∫ v, |Φ v|)
  let c := A/(16*(M+1))
  have hM : 0≤M := mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hden : 0 < 16*(M+1) := by positivity
  have hc₀ : 0<c := div_pos hA hden
  have hAc : c*(16*(M+1))=A := div_mul_cancel₀ _ hden.ne'
  have hcA : c≤A := by linarith only [hAc,mul_nonneg hc₀.le hM,hc₀]
  refine Or.inr ⟨W,F,Φ,c,g,hW,ht,hF,hc,he,hc₀,hg,fun η hη hη1 => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,_,_,hdef⟩ := h η hη hη1
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hdiv := Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hg)
  have hprice := hdiv.const_mul_atTop hc₀
  have hmargin := hdiv.const_mul_atTop (show 0<A/2 by positivity)
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right hcA (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hT.eventually_ge_atTop 6,hprice.eventually_ge_atTop (1+Real.log 4),
    hmargin.eventually_gt_atTop ((riemannZeta (1/2)).re*m^2+1),hdef 1 (by norm_num)] with i hlate hB hpos hd
  have hloss : deficitReading Φ (T i) (k i) (L i) < -8*(c*Real.exp (g*T i))*M := by
    change deficitReading Φ (T i) (k i) (L i) ≤ (riemannZeta (1/2)).re*m^2-A*Real.exp (g*T i)+1 at hd
    change (A/2)*Real.exp (g*T i) > _ at hpos
    linarith only [hd,hpos,congrArg (· * Real.exp (g*T i)) hAc,
      mul_nonneg hc₀.le (Real.exp_pos (g*T i)).le]
  obtain ⟨v,s,j,H,a,b,hv,hsg,hor,hj,hX,ha,hab,hb,hsq,hcell,hlarge⟩ :=
    exists_oriented_quotient_interval ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he) hs hlate hB _ _ m hloss
  refine ⟨v,s,j,H,a,b,hv,hsg,hor,hj,hX,
    quotient_numerator_power_at_test hlate hη1 hg hX hsq (hab.trans hb) rfl,ha,hab,hb,hsq,hcell,?_,?_⟩
  · apply hlarge.trans_le
    apply (le_abs_self _).trans
    have hsabs : |s|=1 := hsg.elim (fun h => by rw [h,abs_one]) (fun h => by rw [h,abs_neg,abs_one])
    rw [abs_mul,hsabs,one_mul]
    exact oddQuotientPrimeExcess_le _ b H (fun n hn => Finset.mem_Ioc.mpr
      ⟨(Nat.zero_lt_of_lt ha).trans_le (Finset.mem_Icc.mp hn).1,(Finset.mem_Icc.mp hn).2⟩)
  rw [← oddQuotientPrimeExcess_eq_factorial_divisors _ _ (fun n hn =>
    hsq.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1))]
  exact hlarge

#print axioms halfFactorialQuotient_valuation
#print axioms oddQuotientPrimeExcess_eq_factorial_divisors
#print axioms riemannHypothesis_or_odd_quotient_prime_deficit
end GaloisForLFunctions.ExclusionOfTheCriticalState
