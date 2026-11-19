import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.AnOrientedQuotientIntervalAfterRestrictingTheState
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PersistentOppositeOddQuotientIntervals
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OppositeShortChebyshevIncrementsAtTheOriginalTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheWeightedOccupationOfPairedQuotientCells

/-!
# How many numerators carry opposite prime excursions?

Displacements whose signed integrand exceeds the adverse threshold carry a
fixed share of the original deficit. Each supplies a pair of opposite runs
at its own binary numerator. The state's occupation bound forces a lower
bound for the reciprocal mass of these distinct common numerators.
-/

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Signed ordinary middle response with the outer state mass held fixed. -/
def signedOrdinaryMiddleResponse (m : ℝ) (Φ : ℝ → ℝ) (k L : ℕ) (T : ℝ) : ℝ :=
  m*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t))

/-- The given displacement and numerator realize both persistent signs on the
original cut. Each terminal block admits its own two runs of ordinary prime increments. -/
def CarriesOppositePrimeExcursions (Φ : ℝ → ℝ) (m T c g d : ℝ) (k L H : ℕ) (v : ℝ) : Prop :=
  ∃ (s : ℝ) (j a b l u : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
    H=⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊ ∧ Real.exp T≤H ∧
    k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
    ((ordinaryBandAtDisplacement k L T v).filter fun n : ℕ => Real.sqrt H<n)=Finset.Icc a b ∧
    ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
    ∀ M : ℕ, 1≤M → M≤H → (H:ℝ)-M≤(H:ℝ)^(1/2+d) →
      (∀ J : Finset ℕ, J.Nonempty → J ⊆ Finset.Icc M H →
        c*Real.exp (g*T)*Real.sqrt H < s*commonFactorialDivisorDiscrepancy (Finset.Icc a b) J ∧
        c*Real.exp (g*T)*Real.sqrt H < (-s)*commonFactorialDivisorDiscrepancy (Finset.Ioc l u) J) ∧
      let B := Real.exp ((g/4)*T)
      HasSlidingThetaIncrements M H ⌈B⌉₊ (Finset.Icc a b) s B (Real.exp ((g/8)*T)) ∧
      HasSlidingThetaIncrements M H ⌈B⌉₊ (Finset.Ioc l u) (-s) B (Real.exp ((g/8)*T))

private theorem eventually_pair_at_each_displacement {a₀ g : ℝ} (ha₀ : 0<a₀) (hg : 0<g) :
    ∀ᶠ T : ℝ in atTop, ∀ (Φ : ℝ → ℝ) (m η v : ℝ) (k L : ℕ), η≤1 → L=⌈Real.exp ((1+η)*T)⌉₊ →
      HasOrientedQuotientWitness Φ m T (a₀*Real.exp (g*T)) k L v →
      ∃ H : ℕ, H<L^2 ∧ CarriesOppositePrimeExcursions Φ m T (a₀/8) g (min (g/12) (1/4)) k L H v := by
  filter_upwards [eventually_ge_atTop (6:ℝ),eventually_paired_quotient_intervals ha₀ hg,
    eventually_sliding_of_factorial_pair (by positivity : 0<a₀/8) hg] with T hT hp hslide
  rintro Φ m η v k L hη hL ⟨s,j,H,a,b,hv,hs,hor,hj,hX,hk,hab,hb,hr,hcell,hbig⟩
  have hpow := quotient_numerator_power_at_test hT hη hg hX hr (hab.trans hb) hL
  obtain ⟨l,u,hside,hpair⟩ := hp H a b s hX hpow hs hab hr hbig
  have hroot : Real.sqrt H<(L:ℝ) := hr.trans_le (Nat.cast_le.mpr (hab.trans hb))
  have hHL := (Real.sqrt_lt' ((Real.sqrt_nonneg _).trans_lt hroot)).mp hroot
  refine ⟨H,by exact_mod_cast hHL,s,j,a,b,l,u,hv,hs,hor,hj,hX,hk,hab,hb,hr,hcell,hside,?_⟩
  intro M hm hMH hwidth
  have hin (n : ℕ) (hn : n∈Finset.Icc a b) := hr.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1)
  have hout (n : ℕ) (hn : n∈Finset.Ioc l u) : Real.sqrt H<n := by
    rcases hside with ⟨hl,_⟩|⟨hl,_⟩
    · exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp (hl ▸ (Finset.mem_Ioc.mp hn).1)
    · exact hr.trans_le (Nat.cast_le.mpr (hab.trans (hl ▸ (Finset.mem_Ioc.mp hn).1.le)))
  have hfac (J : Finset ℕ) (hj : J.Nonempty) (hsub : J ⊆ Finset.Icc M H) :
      a₀/8*Real.exp (g*T)*Real.sqrt H < s*commonFactorialDivisorDiscrepancy (Finset.Icc a b) J ∧
      a₀/8*Real.exp (g*T)*Real.sqrt H < (-s)*commonFactorialDivisorDiscrepancy (Finset.Ioc l u) J := by
    have htop (n : ℕ) (hn : n∈J) := (Finset.mem_Icc.mp (hsub hn)).2
    rw [commonFactorialDivisorDiscrepancy_eq _ J H htop hin,commonFactorialDivisorDiscrepancy_eq _ J H htop hout]
    exact hpair M hm hMH hwidth J hj hsub
  have hfull := hfac (Finset.Icc M H) ⟨M,Finset.mem_Icc.mpr ⟨le_rfl,hMH⟩⟩ (by rfl)
  exact ⟨hfac,hslide H a b l u M s hm hMH hpow hs hab hr hside hfull.1 hfull.2⟩

private theorem reciprocal_and_count {A c K g T : ℝ} {L : ℕ} {N : Finset ℕ}
    (hc : 0<c) (hK : 0≤K) (hscale : c*(K+1)=A/4) (hN : ∀ H ∈ N, Real.exp T≤H)
    (hcost : (A/4)*Real.exp (g*T)<K*L*Real.exp (-T/2)*∑ H ∈ N, (1/(H:ℝ))) :
    c*Real.exp ((g+1/2)*T)<L*∑ H ∈ N, (1/(H:ℝ)) ∧
    c*Real.exp ((g+3/2)*T)<L*(N.card:ℝ) := by
  let S := ∑ H ∈ N, (1/(H:ℝ))
  let Y := Real.exp (g*T)
  have hbase : c*Y < L*S*Real.exp (-T/2) := by
    by_contra! hle
    have h := mul_le_mul_of_nonneg_left hle hK
    change A/4*Y < K*L*Real.exp (-T/2)*S at hcost
    linarith only [hcost,h,congrArg (· *Y) hscale,mul_pos hc (Real.exp_pos (g*T))]
  have hh : Real.exp (-T/2)*Real.exp (T/2)=1 := by rw [← Real.exp_add,show -T/2+T/2=0 by ring,Real.exp_zero]
  have hmass := mul_lt_mul_of_pos_right hbase (Real.exp_pos (T/2))
  rw [mul_assoc ((L:ℝ)*S),hh,mul_one] at hmass
  have h₁ : Real.exp ((g+1/2)*T)=Y*Real.exp (T/2) := by
    rw [show (g+1/2)*T=g*T+T/2 by ring,Real.exp_add]
  have h₂ : Real.exp ((g+3/2)*T)=Real.exp ((g+1/2)*T)*Real.exp T := by
    rw [show (g+3/2)*T=(g+1/2)*T+T by ring,Real.exp_add]
  have hm : c*Real.exp ((g+1/2)*T)<L*S := by rwa [h₁,← mul_assoc]
  refine ⟨hm,?_⟩
  have hcard : S*Real.exp T ≤ N.card := by
    dsimp only [S]; rw [Finset.sum_mul]
    calc _ ≤ ∑ _ ∈ N, (1:ℝ) := Finset.sum_le_sum fun n hn => by
            rw [one_div,← div_eq_inv_mul]
            exact (div_le_one ((Real.exp_pos T).trans_le (hN n hn))).mpr (hN n hn)
         _ = _ := by simp
  rw [h₂,← mul_assoc]
  exact (mul_lt_mul_of_pos_right hm (Real.exp_pos T)).trans_le
    (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hcard (Nat.cast_nonneg L))

/-- Failure of RH forces a measurable part of each late original test to
carry a negative power-sized response. Every displacement in it realizes
opposite prime runs at its own digit. The resulting distinct numerators
have power-sized reciprocal mass and cardinality after the band normalization. -/
theorem riemannHypothesis_or_abundant_opposite_prime_excursions : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (a c g d : ℝ), 0<W ∧
      (⨅ (r : ℝ) (_ : 0≤r), windowThreshold r)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧
      ∀ η : ℝ, 0<η → η≤1 → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (E : Set ℝ) (N : Finset ℕ), MeasurableSet E ∧
          (∀ v ∈ E, ∃ H ∈ N, CarriesOppositePrimeExcursions Φ m (T i) a g d (k i) (L i) H v) ∧
          (∀ H : ℕ, H∈N ↔ Real.exp (T i)≤H ∧ H<(L i)^2 ∧
            ∃ v ∈ E, CarriesOppositePrimeExcursions Φ m (T i) a g d (k i) (L i) H v) ∧
          signedOrdinaryMiddleResponse m Φ (k i) (L i) (T i) -
            signedOrdinaryMiddleResponse m (Eᶜ.indicator Φ) (k i) (L i) (T i) < -c*Real.exp (g*T i) ∧
          c*Real.exp ((g+1/2)*T i)<L i*∑ H ∈ N, (1/(H:ℝ)) ∧
          c*Real.exp ((g+3/2)*T i)<L i*(N.card:ℝ) := by
  rcases riemannHypothesis_or_ordinary_prime_diagonal_band with hr | ⟨W,F,Φ,A,g,hW,ht,hF,hc,he,hA,hg,h⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨K,hK,hcut⟩ := criticalState_reciprocal_numerator_removal hW ht hF hc he
  let m := ∫ v, Φ v
  let M := |m|*(∫ v, |Φ v|)
  let a₀ := A/(32*(M+1))
  let c := (A/4)/(K+1)
  let d := min (g/12) (1/4)
  have hM : 0≤M := mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hden : 0<32*(M+1) := by positivity
  have ha₀ : 0<a₀ := div_pos hA hden
  have hscale := div_mul_cancel₀ A hden.ne'
  change a₀*(32*(M+1))=A at hscale
  have hc₀ : 0<c := div_pos (by positivity) (by positivity)
  have hKscale : c*(K+1)=A/4 := div_mul_cancel₀ _ (by positivity)
  have hcA : c≤A/4 := by linarith only [hKscale,mul_nonneg hc₀.le hK]
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  refine Or.inr ⟨W,F,Φ,a₀/8,c,g,d,hW,ht,hF,hc,he,by positivity,hc₀,hg,hd,min_le_right ..,fun η hη hη₁ => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,_,_,hdef⟩ := h η hη hη₁
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hdiv := Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hg)
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right (by linarith only [hcA,hA] : c≤A)
    (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hT.eventually_ge_atTop 6,(hdiv.const_mul_atTop ha₀).eventually_ge_atTop (1+Real.log 4),
    (hdiv.const_mul_atTop (show 0<A/4 by positivity)).eventually_gt_atTop ((riemannZeta (1/2)).re*m^2+1),
    hdef 1 (by norm_num),hT.eventually (eventually_pair_at_each_displacement ha₀ hg)] with i hlate hB hmargin hfull hp
  let Y := Real.exp (g*T i)
  obtain ⟨E,hE,hv,hrest⟩ := exists_oriented_quotient_displacements
    ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he) hc hs hlate hB (k i) (L i) m
  let P := CarriesOppositePrimeExcursions Φ m (T i) (a₀/8) g d (k i) (L i)
  let N := (Finset.range ((L i)^2)).filter fun H => ∃ v ∈ E, P H v
  have hhit (v : ℝ) (he : v∈E) : ∃ H ∈ N, P H v := by
    obtain ⟨H,hHL,hw⟩ := hp Φ m η v (k i) (L i) hη₁ rfl (hv v he)
    exact ⟨H,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hHL,v,he,hw⟩,hw⟩
  have hN (H : ℕ) (hn : H∈N) : Real.exp (T i)≤H ∧ H<(L i)^2 ∧ ∃ v ∈ E, P H v := by
    obtain ⟨hHL,hw⟩ := Finset.mem_filter.mp hn
    obtain ⟨v,_,s,j,a,b,l,u,_,_,_,_,hX,_⟩ := hw
    exact ⟨hX,Finset.mem_range.mp hHL,(Finset.mem_filter.mp hn).2⟩
  have hcost := hcut (T i) (k i) (L i) (Ioc (T i/6) (6*T i)) E N
    (fun H hn => Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hN H hn).1)) hE (fun v hev => by
      obtain ⟨H,hn,s,j,a,b,l,u,_,_,_,hj,_⟩ := hhit v hev
      exact ⟨j,hj ▸ hn⟩)
  let changeInReading := signedOrdinaryMiddleResponse m Φ (k i) (L i) (T i) -
    signedOrdinaryMiddleResponse m (Eᶜ.indicator Φ) (k i) (L i) (T i)
  change |changeInReading| ≤ _ at hcost
  change signedOrdinaryMiddleResponse m Φ (k i) (L i) (T i) ≤ (riemannZeta (1/2)).re*m^2-A*Y+1 at hfull
  change -8*(a₀*Y)*M ≤ signedOrdinaryMiddleResponse m (Eᶜ.indicator Φ) (k i) (L i) (T i) at hrest
  change (A/4)*Y > _ at hmargin
  have hneg : changeInReading < -(A/4)*Y := by
    dsimp only [changeInReading]
    linarith only [hfull,hrest,hmargin,congrArg (· *Y) hscale,mul_pos ha₀ (Real.exp_pos (g*T i)),
      mul_pos hA (Real.exp_pos (g*T i))]
  have hmass := reciprocal_and_count hc₀ hK hKscale (fun H hn => (hN H hn).1)
    (lt_of_lt_of_le (by linarith only [hneg,neg_le_abs changeInReading] : (A/4)*Y<|changeInReading|) hcost)
  have hfamily (H : ℕ) : H∈N ↔ Real.exp (T i)≤H ∧ H<(L i)^2 ∧ ∃ v ∈ E, P H v :=
    ⟨hN H,fun hw => Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hw.2.1,hw.2.2⟩⟩
  exact ⟨E,N,hE,hhit,hfamily,hneg.trans_le (by linarith only [mul_le_mul_of_nonneg_right hcA (Real.exp_pos (g*T i)).le]),hmass⟩

#print axioms riemannHypothesis_or_abundant_opposite_prime_excursions
end GaloisForLFunctions.ExclusionOfTheCriticalState
