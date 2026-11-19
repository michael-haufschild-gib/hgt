import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheNumeratorsCarryingOppositePrimeExcursions
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFixedInteriorOfTheMiddleTest
import Mathlib.MeasureTheory.Function.Floor

/-!
# Opposite prime excursions on one fixed band

Displacement localization fixes the interior and the square-root cut for
the entire signed reading. Two measurable partitions then fix the orientation
and the compensating flank. Reciprocal occupation gives a lower bound for a
mixed moment of two arithmetic functions of the same numerator.
-/
noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Left or right complement of the full denominator band above the square root. -/
def middleTestFlank (left : Bool) (k L H : ℕ) : Finset ℕ :=
  if left then Finset.Ioc ⌊Real.sqrt H⌋₊ k else Finset.Ioc L H

/-- Both signed factorial excursions and both runs of prime increments
persist at the same numerator and for each permitted terminal block. -/
def FixedBandPrimePair (left : Bool) (k L H : ℕ) (s a g d T : ℝ) : Prop :=
  ∀ M : ℕ, 1≤M → M≤H → (H:ℝ)-M≤(H:ℝ)^(1/2+d) →
    (∀ J : Finset ℕ, J.Nonempty → J ⊆ Finset.Icc M H →
      a*Real.exp (g*T)*Real.sqrt H < s*commonFactorialDivisorDiscrepancy (Finset.Ioc k L) J ∧
      a*Real.exp (g*T)*Real.sqrt H < (-s)*commonFactorialDivisorDiscrepancy (middleTestFlank left k L H) J) ∧
    let B := Real.exp ((g/4)*T)
    HasSlidingThetaIncrements M H ⌈B⌉₊ (Finset.Ioc k L) s B (Real.exp ((g/8)*T)) ∧
    HasSlidingThetaIncrements M H ⌈B⌉₊ (middleTestFlank left k L H) (-s) B (Real.exp ((g/8)*T))

private theorem freeze_pair {k L H : ℕ} {Φ : ℝ → ℝ} {m a g d T r v s : ℝ}
    (hw : CarriesOppositePrimeExcursions Φ m T a g d k L H v) (hs : s=1 ∨ s= -1)
    (hor : s*m*Φ v<0) (hr : 0<r) (hsmall : r≤1/64) (hd : 3*r≤d)
    (h : MiddleBandScale r T k L) (hv : v∈middleBandInterior r T) (hp : (H:ℝ)^(1/2+d)<L) :
    ∃ j : ℕ, H=⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊ ∧ ∃ left, FixedBandPrimePair left k L H s a g d T := by
  obtain ⟨s',j,b,e,l,u,_,hs',hor',hj,hX,hkb,hbe,he,_,hcell,hside,hblocks⟩ := hw
  have heq : s'=s := by
    rcases hs with rfl|rfl <;> rcases hs' with rfl|rfl <;> first | rfl | exfalso; linarith only [hor,hor']
  subst s'
  have hroot := sqrt_lt_middleBand_start h hr hsmall hd hX hp
  have hfull : ordinaryBandAtDisplacement k L T v=Finset.Ioc k L := by
    rw [← ordinaryIndicesAt_eq_full hr hsmall h hv]
    ext n
    simp only [ordinaryBandAtDisplacement,ordinaryIndicesAt,Finset.mem_filter]
  have hkeep (n : ℕ) (hn : n∈Finset.Ioc k L) : Real.sqrt H<n :=
    hroot.trans (Nat.cast_lt.mpr (Finset.mem_Ioc.mp hn).1)
  rw [hfull,Finset.filter_true_of_mem hkeep] at hcell
  have hkL := hkb.trans_le (hbe.trans he)
  have hb : k+1∈Finset.Icc b e := hcell ▸ (Finset.mem_Ioc.mpr (show k<k+1 ∧ k+1≤L by omega))
  have he' : L∈Finset.Icc b e := hcell ▸ (Finset.mem_Ioc.mpr ⟨hkL,le_rfl⟩)
  rw [Finset.mem_Icc] at hb he'
  have hleft : b-1=k := by omega
  have hright : e=L := by omega
  rw [← hcell] at hblocks
  refine ⟨j,hj,?_⟩
  rcases hside with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨true,by simpa only [FixedBandPrimePair,middleTestFlank,if_true,hleft] using hblocks⟩
  · exact ⟨false,by simpa only [FixedBandPrimePair,middleTestFlank,Bool.false_eq_true,if_false,hright] using hblocks⟩

private theorem integral_split {A B : Set ℝ} {f : ℝ → ℝ} (hf : Integrable f)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ v in A∩B, f v)+(∫ v in A\B, f v)=∫ v in A, f v := by
  have hdis : Disjoint (A∩B) (A\B) := Set.disjoint_left.mpr fun _ h h' => h'.2 h.2
  rw [← setIntegral_union hdis (hA.diff hB) hf.integrableOn hf.integrableOn,Set.inter_union_sdiff]

private theorem choose_piece {A B : Set ℝ} {f : ℝ → ℝ} {z : ℝ} (hf : Integrable f)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hz : (∫ v in A, f v)<2*z) :
    ∃ U : Set ℝ, MeasurableSet U ∧ U ⊆ A ∧ (U ⊆ B ∨ ∀ v ∈ U, v∉B) ∧ (∫ v in U, f v)<z := by
  by_cases h : (∫ v in A∩B, f v)<z
  · exact ⟨A∩B,hA.inter hB,inter_subset_left,Or.inl inter_subset_right,h⟩
  · exact ⟨A\B,hA.diff hB,sdiff_subset,Or.inr (fun _ hv => hv.2),
      by linarith only [integral_split hf hA hB,h,hz]⟩

private def digit (T v : ℝ) (j : ℕ) : ℕ := ⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊

private theorem measurable_digit_hits (T : ℝ) (P : Set ℕ) : MeasurableSet {v | ∃ j, digit T v j∈P} := by
  rw [show {v | ∃ j, digit T v j∈P}=⋃ j : ℕ, (fun v => digit T v j) ⁻¹' P by ext; simp]
  apply MeasurableSet.iUnion
  intro j
  have h : Measurable fun v : ℝ => (2:ℝ)^(j+1)*Real.exp (T-v) := by fun_prop
  exact h.nat_floor (Set.to_countable P).measurableSet

/-- Numerators eligible for the mixed moment, specified without reference to a state. -/
def middleTestNumerators (T d : ℝ) (k L : ℕ) : Finset ℕ :=
  (Finset.range (L^2)).filter fun H => Real.exp T≤H ∧ (H:ℝ)^(1/2+d)<L ∧ Real.sqrt H<k

/-- Joint upper tail of both signed arithmetic discrepancies at the same numerator. -/
def largeOppositePrimeNumerators (left : Bool) (s a g d T : ℝ) (k L : ℕ) : Finset ℕ :=
  (middleTestNumerators T d k L).filter fun H =>
    a*Real.exp (g*T)*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Ioc k L) H ∧
    a*Real.exp (g*T)*Real.sqrt H < (-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H

/-- Product of oppositely oriented positive parts at a common numerator. -/
def oppositePrimeProduct (left : Bool) (s : ℝ) (k L H : ℕ) : ℝ :=
  max 0 (s*oddQuotientPrimeExcess (Finset.Ioc k L) H) *
    max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H) / (H:ℝ)^2

private theorem singleton_pair {k L H : ℕ} {s a g d T : ℝ} {left : Bool}
    (hH : 0<H) (hr : Real.sqrt H<k) (hkL : k≤L) (h : FixedBandPrimePair left k L H s a g d T) :
    a*Real.exp (g*T)*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Ioc k L) H ∧
    a*Real.exp (g*T)*Real.sqrt H < (-s)*oddQuotientPrimeExcess (middleTestFlank left k L H) H := by
  have hi (n : ℕ) (hn : n∈Finset.Ioc k L) := hr.trans (Nat.cast_lt.mpr (Finset.mem_Ioc.mp hn).1)
  have ho (n : ℕ) (hn : n∈middleTestFlank left k L H) : Real.sqrt H<n := by
    cases left
    · exact hr.trans (Nat.cast_lt.mpr (hkL.trans_lt (Finset.mem_Ioc.mp hn).1))
    · exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp (Finset.mem_Ioc.mp hn).1
  have heq (S : Finset ℕ) (hS : ∀ n ∈ S, Real.sqrt H<n) :
      commonFactorialDivisorDiscrepancy S {H}=oddQuotientPrimeExcess S H := by
    rw [commonFactorialDivisorDiscrepancy_eq S {H} H (by simp) hS]
    simp only [commonOddQuotientPrimeExcess,Finset.mem_singleton,forall_eq,oddQuotientPrimeExcess]
  have hb := (h H hH le_rfl (by rw [sub_self]; exact Real.rpow_nonneg (Nat.cast_nonneg _) _)).1
    {H} (Finset.singleton_nonempty _) (by simp)
  rwa [heq _ hi,heq _ ho] at hb

private theorem pair_product {k L H : ℕ} {s a g d T : ℝ} {left : Bool}
    (ha : 0<a) (hj : H∈largeOppositePrimeNumerators left s a g d T k L) :
    (a*Real.exp (g*T))^2*(1/(H:ℝ)) ≤ oppositePrimeProduct left s k L H := by
  obtain ⟨hnum,hb⟩ := Finset.mem_filter.mp hj
  have hH : 0<H := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (Finset.mem_filter.mp hnum).2.1)
  have hpos : 0≤a*Real.exp (g*T)*Real.sqrt H := by positivity
  have hm := mul_le_mul (hb.1.le.trans (le_max_right 0 _)) (hb.2.le.trans (le_max_right 0 _))
    hpos ((le_max_left 0 _))
  unfold oppositePrimeProduct
  apply (le_div_iff₀ (by positivity)).mpr
  have hr2 := Real.sq_sqrt (Nat.cast_nonneg H)
  calc _ = (a*Real.exp (g*T)*Real.sqrt H)^2 := by
             rw [mul_pow (a*Real.exp (g*T)) (Real.sqrt H),hr2]
             field_simp [Nat.cast_ne_zero.mpr hH.ne']
       _ ≤ _ := by simpa only [sq] using hm

private theorem choose_fixed_pair {Φ f : ℝ → ℝ} {m a g d r T z : ℝ} {k L : ℕ} {E : Set ℝ} {N : Finset ℕ}
    (hΦ : Continuous Φ) (hf : Integrable f) (hE : MeasurableSet E)
    (hneg : (∫ v in E, f v)<4*z) (hbulk : E ⊆ middleBandInterior r T)
    (hr : 0<r) (hsmall : r≤1/64) (hd : 3*r≤d) (h : MiddleBandScale r T k L)
    (hpow : ∀ H ∈ N, (H:ℝ)^(1/2+d)<L)
    (hit : ∀ v ∈ E, ∃ H ∈ N, CarriesOppositePrimeExcursions Φ m T a g d k L H v) :
    ∃ (U : Set ℝ) (s : ℝ) (left : Bool), MeasurableSet U ∧ U ⊆ E ∧ (s=1 ∨ s= -1) ∧
      (∀ v ∈ U, s*m*Φ v<0) ∧ (∫ v in U, f v)<z ∧
      ∀ v ∈ U, ∃ j : ℕ, digit T v j ∈ N ∧ FixedBandPrimePair left k L (digit T v j) s a g d T := by
  let B := {v : ℝ | m*Φ v<0}
  have hmB : MeasurableSet B := measurableSet_lt (measurable_const.mul hΦ.measurable) measurable_const
  obtain ⟨V,hV,hVE,hor,hVneg⟩ := choose_piece (z:=2*z) hf hE hmB (by linarith only [hneg])
  have hsign : ∃ s : ℝ, (s=1 ∨ s= -1) ∧ ∀ v ∈ V, s*m*Φ v<0 := by
    rcases hor with hpos|hmin
    · exact ⟨1,Or.inl rfl,fun v hv => by simpa only [B,Set.mem_setOf_eq,one_mul] using hpos hv⟩
    · refine ⟨-1,Or.inr rfl,fun v hv => ?_⟩
      have h₀ : 0 ≤ m*Φ v := le_of_not_gt (hmin v hv)
      obtain ⟨H,_,σ,j,b,e,l,u,_,hσ,hstrict,_⟩ := hit v (hVE hv)
      rcases hσ with rfl|rfl <;> linarith only [h₀,hstrict]
  obtain ⟨s,hs,hsm⟩ := hsign
  let P := {H : ℕ | H∈N ∧ FixedBandPrimePair true k L H s a g d T}
  obtain ⟨U,hU,hUV,hflank,hUn⟩ := choose_piece hf hV (measurable_digit_hits T P) hVneg
  rcases hflank with hleft|hright
  · exact ⟨U,s,true,hU,hUV.trans hVE,hs,fun _ hv => hsm _ (hUV hv),hUn,fun _ hv => hleft hv⟩
  · refine ⟨U,s,false,hU,hUV.trans hVE,hs,fun _ hv => hsm _ (hUV hv),hUn,fun v hv => ?_⟩
    have he := hVE (hUV hv)
    obtain ⟨H,hn,hw⟩ := hit v he
    obtain ⟨j,hj,b,hb⟩ := freeze_pair hw hs (hsm _ (hUV hv)) hr hsmall hd h (hbulk he) (hpow H hn)
    change H=digit T v j at hj
    subst H
    cases b
    · exact ⟨j,hn,hb⟩
    · exact False.elim (hright v hv ⟨j,hn,hb⟩)

private theorem summed_pair_product {k L : ℕ} {s a g d T : ℝ} {left : Bool} {N : Finset ℕ}
    (ha : 0<a) (hN : N ⊆ largeOppositePrimeNumerators left s a g d T k L) :
    (a*Real.exp (g*T))^2 * (∑ H ∈ N, 1/(H:ℝ)) ≤
      ∑ H ∈ largeOppositePrimeNumerators left s a g d T k L, oppositePrimeProduct left s k L H := by
  rw [Finset.mul_sum]
  exact (Finset.sum_le_sum fun _ hn => pair_product ha (hN hn)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hN (fun H _ _ => div_nonneg
      (mul_nonneg (le_max_left ..) (le_max_left ..)) (sq_nonneg _)))

/-- A common interval, orientation and flank carry signed loss in each late
original test. Their mixed arithmetic moment runs over an explicit range
independent of the state and of every displacement or binary digit. -/
theorem riemannHypothesis_or_fixed_band_opposite_prime_moment : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (a c g d r : ℝ), 0<W ∧
      (⨅ (q : ℝ) (_ : 0≤q), windowThreshold q)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<a ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ 0<r ∧
      ∀ η : ℝ, 0<η → η≤r → ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η)≤Real.log (k i) ∧ Real.log (k i)≤T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (U : Set ℝ) (N : Finset ℕ) (s : ℝ) (left : Bool),
          MeasurableSet U ∧ U ⊆ middleBandInterior r (T i) ∧ (s=1 ∨ s= -1) ∧
          (∀ v ∈ U, s*m*Φ v<0 ∧ ∃ j : ℕ, ⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊∈N) ∧
          N ⊆ largeOppositePrimeNumerators left s a g d (T i) (k i) (L i) ∧
          (∀ H ∈ N, (∃ v ∈ U, ∃ j : ℕ, H=⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊) ∧
            FixedBandPrimePair left (k i) (L i) H s a g d (T i)) ∧
          signedOrdinaryMiddleResponse m Φ (k i) (L i) (T i) -
            signedOrdinaryMiddleResponse m (Uᶜ.indicator Φ) (k i) (L i) (T i) < -c*Real.exp (g*T i) ∧
          c*Real.exp ((g+1/2)*T i)<L i*∑ H ∈ N, (1/(H:ℝ)) ∧
          c*a^2*Real.exp ((1/2+3*g)*T i) <
            L i*∑ H ∈ largeOppositePrimeNumerators left s a g d (T i) (k i) (L i), oppositePrimeProduct left s (k i) (L i) H := by
  rcases riemannHypothesis_or_abundant_opposite_prime_excursions with hh | ⟨W,F,Φ,a,b,g,d,hW,ht,hF,hΦ,he,ha,hb,hg,hd,hd₁,hseq⟩
  · exact Or.inl hh
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hconf⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hsame := (Continuous.ae_eq_iff_eq volume hΨ hΦ).mp (heΨ.symm.trans he)
  subst Ψ
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  obtain ⟨K,hK,hcut⟩ := criticalState_reciprocal_numerator_removal hW ht hF hΦ he
  let m := ∫ v, Φ v
  let r := min (1/64:ℝ) (min (g/16) (d/16))
  let c := (b/8)/(K+1)
  have hr : 0<r := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hr₁ : r≤1/64 := min_le_left ..
  have hrg : r≤g/16 := (min_le_right ..).trans (min_le_left ..)
  have hrd : 3*r≤d := by have hh : r≤d/16 := (min_le_right ..).trans (min_le_right ..); linarith only [hh,hd]
  have hc : 0<c := div_pos (by positivity) (by positivity)
  have hck : c*(K+1)=b/8 := div_mul_cancel₀ _ (by positivity)
  have hcb : c≤b/8 := by linarith only [hck,mul_nonneg hc.le hK]
  refine Or.inr ⟨W,F,Φ,a,c,g,d,r,hW,ht,hF,hΦ,he,ha,hc,hg,hd,hd₁,hr,fun η hη hηr => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,hsel⟩ := hseq η hη (by linarith only [hηr,hr₁])
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hgap : 0<g-8*r := by linarith only [hrg,hg]
  have htail := ((Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hgap)).const_mul_atTop
    (by positivity : 0<b/2)).eventually_gt_atTop (2*|m| *C)
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right (by linarith only [hcb,hb] : c≤b)
    (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hsel,htail,hT.eventually (eventually_middleBandScale hr)] with i hseli hprice hscale
  obtain ⟨E,N,hE,hit,hN,hdef,_,_⟩ := hseli
  let t := T i
  let Y := Real.exp (g*t)
  let G := middleBandInterior r t
  let f := ordinaryDisplacementDensity Φ m t (k i) (L i)
  have hf : Integrable f := integrable_ordinaryDisplacementDensity hi m t (k i) (L i)
  have hG : MeasurableSet G := measurableSet_Icc
  have hsc : MiddleBandScale r t (k i) (L i) := hscale hη hηr (hk i).1
  have h₀ (v : ℝ) (hv : v∈E) : v≤0 := by
    obtain ⟨H,_,s,j,b,e,l,u,hle,_⟩ := hit v hv; exact hle
  have hout := ordinaryDisplacementDensity_outside (m:=m) hC hconf hr hr₁ hsc (hE.diff hG)
    (fun v hv => ⟨h₀ v hv.1,hv.2⟩)
  have hexp : Real.exp ((g-8*r)*t)*Real.exp (8*r*t)=Y := by rw [← Real.exp_add]; congr 1; ring
  change 2*|m| *C<(b/2)*Real.exp ((g-8*r)*t) at hprice
  have hbudget := mul_lt_mul_of_pos_right hprice (Real.exp_pos (8*r*t))
  rw [mul_assoc (b/2),hexp] at hbudget
  have hwhole : (∫ v in E, f v)< -b*Y := by
    calc _ = _ := (ordinaryBand_delete_eq_setIntegral hi m t (k i) (L i) hE).symm
         _ < _ := hdef
  have hbulk : (∫ v in E∩G, f v)<4*(-(b/8)*Y) := by
    change |∫ v in E\G, f v|≤_ at hout
    linarith only [hwhole,integral_split hf hE hG,hout,hbudget,neg_le_abs (∫ v in E\G, f v)]
  obtain ⟨U,s,left,hU,hUG,hs,hor,hUn,hpair⟩ := choose_fixed_pair hΦ hf (hE.inter hG) hbulk
    inter_subset_right hr hr₁ hrd hsc (fun H hn => ((hN H).mp hn).2.1) (fun v hv => hit v hv.1)
  let J := N.filter fun H => (∃ v ∈ U, ∃ j : ℕ, H=digit t v j) ∧ FixedBandPrimePair left (k i) (L i) H s a g d t
  have hJ (v : ℝ) (hv : v∈U) : ∃ j : ℕ, digit t v j∈J := by
    obtain ⟨j,hn,hp⟩ := hpair v hv
    exact ⟨j,Finset.mem_filter.mpr ⟨hn,⟨v,hv,j,rfl⟩,hp⟩⟩
  have hallowed : J ⊆ middleTestNumerators t d (k i) (L i) := by
    intro H hj
    obtain ⟨hX,hpow,hHL,_⟩ := (hN H).mp (Finset.mem_filter.mp hj).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hHL,hX,hpow,sqrt_lt_middleBand_start hsc hr hr₁ hrd hX hpow⟩
  have hpos (H : ℕ) (hj : H∈J) := Nat.cast_pos.mp ((Real.exp_pos t).trans_le ((hN H).mp (Finset.mem_filter.mp hj).1).1)
  let mass := ∑ H ∈ J, 1/(H:ℝ)
  have hcost : |∫ v in U, f v| ≤ K*(L i:ℝ)*Real.exp (-t/2)*mass := by
    calc _ = _ := congrArg abs (ordinaryBand_delete_eq_setIntegral hi m t (k i) (L i) hU).symm
         _ ≤ _ := hcut t (k i) (L i) (Ioc (t/6) (6*t)) U J hpos hU hJ
  have hpaid : c*Y<(L i:ℝ)*mass*Real.exp (-t/2) := by
    by_contra! hle
    have hh := mul_le_mul_of_nonneg_left hle hK
    linarith only [hUn,hcost,hh,neg_le_abs (∫ v in U, f v),congrArg (· *Y) hck,mul_pos hc (Real.exp_pos (g*t))]
  have hmass := mul_lt_mul_of_pos_right hpaid (Real.exp_pos (t/2))
  have hunit : Real.exp (-t/2)*Real.exp (t/2)=1 := by
    rw [← Real.exp_add,show -t/2+t/2=0 by ring,Real.exp_zero]
  have hY : Y*Real.exp (t/2)=Real.exp ((g+1/2)*t) := by
    dsimp only [Y]; rw [← Real.exp_add]; congr 1; ring
  rw [mul_assoc ((L i:ℝ)*mass),hunit,mul_one,mul_assoc c,hY] at hmass
  have hkL : k i≤L i := by
    by_contra! hh
    have heL := (Nat.le_ceil (Real.exp ((1+η)*t))).trans_lt (Nat.cast_lt.mpr hh)
    have hkpos := (Real.exp_pos _).trans heL
    have hlt := (Real.lt_log_iff_exp_lt hkpos).mpr heL
    linarith only [hlt,(hk i).2,mul_pos hη hsc.pos]
  have htailset : J ⊆ largeOppositePrimeNumerators left s a g d t (k i) (L i) := by
    intro H hj
    have hn := hallowed hj
    exact Finset.mem_filter.mpr ⟨hn,singleton_pair (hpos H hj) (Finset.mem_filter.mp hn).2.2.2 hkL (Finset.mem_filter.mp hj).2.2⟩
  have hm := summed_pair_product ha htailset
  have hfactor := mul_lt_mul_of_pos_left hmass (sq_pos_of_pos (mul_pos ha (Real.exp_pos (g*t))))
  have hpowers : Real.exp (g*t)^2*Real.exp ((g+1/2)*t)=Real.exp ((1/2+3*g)*t) := by
    rw [sq,← Real.exp_add,← Real.exp_add]; congr 1; ring
  refine ⟨U,J,s,left,hU,hUG.trans inter_subset_right,hs,fun v hv => ⟨hor v hv,hJ v hv⟩,
    htailset,fun H hj => (Finset.mem_filter.mp hj).2,?_,hmass,?_⟩
  · change _ - _ < -c*Y
    rw [show signedOrdinaryMiddleResponse m Φ (k i) (L i) t -
      signedOrdinaryMiddleResponse m (Uᶜ.indicator Φ) (k i) (L i) t=(∫ v in U, f v) from
      ordinaryBand_delete_eq_setIntegral hi m t (k i) (L i) hU]
    exact hUn.trans_le (mul_le_mul_of_nonneg_right (neg_le_neg hcb) (Real.exp_pos _).le)
  · change c*a^2*Real.exp ((1/2+3*g)*t)<_
    calc _ = (a*Real.exp (g*t))^2*(c*Real.exp ((g+1/2)*t)) := by rw [← hpowers]; ring
         _ < (a*Real.exp (g*t))^2*((L i:ℝ)*mass) := hfactor
         _ = (L i:ℝ)*((a*Real.exp (g*t))^2*mass) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (L i))

/-- Below the upper endpoint the right flank is empty. On the left, the
mixed moment agrees with the interior second moment up to relative error
C/B on every subfamily above level B times the square root. -/
theorem oppositePrimeProduct_below_endpoint :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : ℝ) (k L : ℕ), (s=1 ∨ s= -1) → k≤L →
      let P := fun H : ℕ => max 0 (s*oddQuotientPrimeExcess (Finset.Ioc k L) H)
      let Q := fun H : ℕ => max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank true k L H) H)
      (∀ H : ℕ, H≤L → ⌊Real.sqrt H⌋₊≤k →
        oppositePrimeProduct false s k L H=0 ∧ |P H-Q H|≤C*Real.sqrt H) ∧
      ∀ (D : Finset ℕ) (B : ℝ), 0<B →
        (∀ H ∈ D, H≤L ∧ ⌊Real.sqrt H⌋₊≤k ∧ B*Real.sqrt H≤P H) →
        |(∑ H ∈ D, oppositePrimeProduct true s k L H)-(∑ H ∈ D, (P H)^2/(H:ℝ)^2)| ≤
          (C/B)*(∑ H ∈ D, (P H)^2/(H:ℝ)^2) := by
  obtain ⟨C,hC,hrow⟩ := oddQuotientPrimeExcess_complete_above_sqrt
  refine ⟨C,hC,fun s k L hs hk => ?_⟩
  let P := fun H : ℕ => max 0 (s*oddQuotientPrimeExcess (Finset.Ioc k L) H)
  let Q := fun H : ℕ => max 0 ((-s)*oddQuotientPrimeExcess (middleTestFlank true k L H) H)
  have hpoint (H : ℕ) (hH : H≤L) (hr : ⌊Real.sqrt H⌋₊≤k) :
      oppositePrimeProduct false s k L H=0 ∧ |P H-Q H|≤C*Real.sqrt H := by
    have hempty : Finset.Ioc L H=∅ := Finset.Ioc_eq_empty_of_le hH
    refine ⟨by simp [oppositePrimeProduct,middleTestFlank,hempty,oddQuotientPrimeExcess],?_⟩
    let I := oddQuotientPrimeExcess (Finset.Ioc k L) H
    let J := oddQuotientPrimeExcess (Finset.Ioc ⌊Real.sqrt H⌋₊ k) H
    have heq : J+I=oddQuotientPrimeExcess (Finset.Ioc ⌊Real.sqrt H⌋₊ L) H :=
      Finset.sum_Ioc_consecutive _ hr hk
    have hb : |s*I-(-s)*J|≤C*Real.sqrt H := by
      rw [show s*I-(-s)*J=s*(J+I) by ring,abs_mul,heq]
      rcases hs with rfl|rfl <;> simpa only [abs_neg,abs_one,one_mul] using hrow H L hH
    change |max 0 (s*I)-max 0 ((-s)*J)|≤_
    rw [max_comm 0 (s*I),max_comm 0 ((-s)*J)]
    exact (abs_max_sub_max_le_abs _ _ _).trans hb
  refine ⟨hpoint,fun D B hB hD => ?_⟩
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro H hmem
  obtain ⟨hH,hr,hP⟩ := hD H hmem
  have hcl := (hpoint H hH hr).2
  rw [abs_sub_comm] at hcl
  have hx : Real.sqrt H≤P H/B := (le_div_iff₀ hB).mpr (by simpa only [mul_comm B] using hP)
  have hy : |Q H-P H| ≤ (C/B)*P H :=
    hcl.trans ((mul_le_mul_of_nonneg_left hx hC).trans_eq (by ring))
  have hpos : 0≤P H := le_max_left ..
  change |P H*Q H/(H:ℝ)^2-(P H)^2/(H:ℝ)^2| ≤ _
  rw [← sub_div,show P H*Q H-(P H)^2=P H*(Q H-P H) by ring,abs_div,abs_mul,
    abs_of_nonneg hpos,abs_of_nonneg (sq_nonneg (H:ℝ))]
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hy hpos) (sq_nonneg _)).trans_eq (by ring)

#print axioms oppositePrimeProduct_below_endpoint

#print axioms riemannHypothesis_or_fixed_band_opposite_prime_moment
end GaloisForLFunctions.ExclusionOfTheCriticalState
