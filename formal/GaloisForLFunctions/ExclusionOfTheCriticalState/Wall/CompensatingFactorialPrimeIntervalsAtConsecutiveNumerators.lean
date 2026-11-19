import Mathlib.Algebra.GCDMonoid.Finset
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.VariationOfTheFactorialPrimeDiscrepancy
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheOddQuotientIntervalInTheOrdinaryPrimeDeficit

/-!
# Two fixed intervals of prime factors at consecutive numerators

Under failure of RH, a signed discrepancy inside the selected integer band
must be compensated on its left or right for the same factorial quotient.
The numerator variation is small enough that both fixed intervals retain
opposite signed discrepancies across more than square-root many numerators.
-/

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Log mass of prime divisors common to the selected factorial quotients,
less the number of integer denominators with odd quotient at every numerator. -/
def commonFactorialDivisorDiscrepancy (S E : Finset ℕ) : ℝ :=
  (∑ p ∈ S with p.Prime ∧ p ∣ E.gcd halfFactorialQuotient, Real.log p) -
    ((S.filter fun n => ∀ j ∈ E, j/n%2=1).card:ℝ)

/-- Above the square root, intersection of divisor sets is exactly
intersection of odd-quotient columns. -/
theorem commonFactorialDivisorDiscrepancy_eq (S E : Finset ℕ) (H : ℕ)
    (hE : ∀ j ∈ E, j≤H) (hS : ∀ n ∈ S, Real.sqrt H<n) :
    commonFactorialDivisorDiscrepancy S E=commonOddQuotientPrimeExcess S E := by
  let keep := fun n : ℕ => ∀ j ∈ E, j/n%2=1
  have hcard : ((S.filter keep).card:ℝ) = ∑ n ∈ S, if keep n then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  change (∑ p ∈ S with p.Prime ∧ p ∣ E.gcd halfFactorialQuotient, Real.log p) -
    ((S.filter keep).card:ℝ) = ∑ n ∈ S, if keep n then ordinaryPrimeExcessCoeff n else 0
  rw [hcard,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hmem
  by_cases hp : p.Prime
  · have hiff (j : ℕ) (hj : j∈E) : p ∣ halfFactorialQuotient j ↔ j/p%2=1 := by
      have hlt : (H:ℝ)<(p:ℝ)^2 := (Real.sqrt_lt' (Nat.cast_pos.mpr hp.pos)).mp (hS p hmem)
      have hv := halfFactorialQuotient_valuation hp ((hE j hj).trans_lt (by exact_mod_cast hlt : H<p^2))
      have hd : (j/2).factorial*(j/2).factorial ∣ j.factorial :=
        (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (by omega))
      have hpos : 0<halfFactorialQuotient j :=
        Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos _) hd) (mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _))
      constructor
      · intro h; have hh := hp.factorization_pos_of_dvd hpos.ne' h; rw [hv] at hh; omega
      · intro h; by_contra hn; rw [Nat.factorization_eq_zero_of_not_dvd hn,h] at hv; omega
    have hg : p ∣ E.gcd halfFactorialQuotient ↔ keep p := by
      rw [Finset.dvd_gcd_iff]
      exact forall₂_congr fun j hj => hiff j hj
    by_cases h : keep p <;> simp [ordinaryPrimeExcessCoeff,hp,hg,h]
  · by_cases h : keep p <;> simp [ordinaryPrimeExcessCoeff,hp,h]

private theorem oriented_le_abs {s : ℝ} (hs : s=1 ∨ s= -1) (x : ℝ) : s*x ≤ |x| := by
  rcases hs with rfl|rfl
  · simpa only [one_mul] using le_abs_self x
  · simpa only [neg_one_mul] using (neg_le_abs x)

/-- A discrepancy beyond the complete square-root bound on one interval
forces the opposite sign on one of its two exact complementary intervals. -/
private theorem other_interval {H a b : ℕ} {C B s : ℝ} (hC : 0≤C) (hB : 4*C≤B)
    (hs : s=1 ∨ s= -1) (hab : a≤b) (ha : Real.sqrt H<a)
    (hall : ∀ L : ℕ, H≤L → |oddQuotientPrimeExcess (Finset.Ioc ⌊Real.sqrt H⌋₊ L) H| ≤ C*Real.sqrt H)
    (hbig : B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H) :
    ∃ l u : ℕ, ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
      (∀ n ∈ Finset.Ioc l u, Real.sqrt H<n) ∧
      (B/4)*Real.sqrt H < (-s)*oddQuotientPrimeExcess (Finset.Ioc l u) H := by
  let r := ⌊Real.sqrt H⌋₊
  let L := max b H
  let O := fun (S : Finset ℕ) => oddQuotientPrimeExcess S H
  have hra : r<a := (Nat.floor_lt (Real.sqrt_nonneg _)).mpr ha
  have hpos : 1≤a := Nat.zero_lt_of_lt hra
  have hm : Finset.Ioc (a-1) b=Finset.Icc a b := by
    ext n; simp only [Finset.mem_Ioc,Finset.mem_Icc]; omega
  have hend : Finset.Ioc b L=Finset.Ioc b H := by
    ext n; simp only [Finset.mem_Ioc,L]; omega
  have split : O (Finset.Ioc r L) =
      O (Finset.Ioc r (a-1))+O (Finset.Icc a b)+O (Finset.Ioc b H) := by
    dsimp only [O,oddQuotientPrimeExcess]
    rw [← Finset.sum_Ioc_consecutive _ (by omega : r≤b) (le_max_left b H),
        ← Finset.sum_Ioc_consecutive _ (by omega : r≤a-1) (by omega : a-1≤b),hm,hend]
  have hnet := (oriented_le_abs hs _).trans (hall L (le_max_right ..))
  change s*O (Finset.Ioc r L) ≤ _ at hnet
  rw [split] at hnet
  by_cases hl : (B/4)*Real.sqrt H < (-s)*O (Finset.Ioc r (a-1))
  · exact ⟨r,a-1,Or.inl ⟨rfl,rfl⟩,fun n hn => (Nat.floor_lt (Real.sqrt_nonneg _)).mp
      (Finset.mem_Ioc.mp hn).1,hl⟩
  · refine ⟨b,H,Or.inr ⟨rfl,rfl⟩,fun n hn => ha.trans_le (Nat.cast_le.mpr
      (hab.trans (Finset.mem_Ioc.mp hn).1.le)),?_⟩
    change _ < (-s)*O (Finset.Ioc b H)
    change B*Real.sqrt H < s*O (Finset.Icc a b) at hbig
    linarith only [hnet,hbig,le_of_not_gt hl,mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg H),
      mul_nonneg hC (Real.sqrt_nonneg H)]

private theorem eventual_log_price {d A : ℝ} (hd : 0<d) (hA : 0<A) :
    ∀ᶠ x : ℝ in atTop, 2*Real.log x+2+2*|Real.eulerMascheroniConstant| ≤ (A/16)*x^d := by
  have hlog := (isLittleO_log_rpow_atTop hd).bound (show 0<A/64 by positivity)
  have hex := (tendsto_rpow_atTop hd).const_mul_atTop (show 0<A/32 by positivity)
  filter_upwards [hlog,hex.eventually_ge_atTop (2+2*|Real.eulerMascheroniConstant|),
    eventually_ge_atTop (1:ℝ)] with x h hx hx1
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (Real.log_nonneg hx1),
    abs_of_nonneg (Real.rpow_nonneg (by linarith only [hx1]) d)] at h
  change _ ≤ (A/32)*x^d at hx
  linarith only [h,hx]

private theorem block_cost {H M : ℕ} {d A E : ℝ} (hM : 1≤M) (hMH : M≤H) (hA : 0<A)
    (hd : (H:ℝ)^d*(H:ℝ)^d ≤ E) (hE : 40 ≤ (A/16)*E)
    (hlog : 2*Real.log H+2+2*|Real.eulerMascheroniConstant| ≤ (A/16)*(H:ℝ)^d)
    (hwidth : (H:ℝ)-M ≤ (H:ℝ)^(1/2+d)) :
    ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H ≤
      (A*E/8)*Real.sqrt H := by
  have hp : 0<(H:ℝ) := Nat.cast_pos.mpr (hM.trans hMH)
  have hR : 0≤(H:ℝ)^d := Real.rpow_nonneg hp.le _
  have hpos : 0≤2*Real.log H+2+2*|Real.eulerMascheroniConstant| := by
    have h := Real.log_natCast_nonneg H
    positivity
  rw [Real.rpow_add hp,← Real.sqrt_eq_rpow] at hwidth
  have h₁ := mul_le_mul hwidth hlog hpos (mul_nonneg (Real.sqrt_nonneg H) hR)
  have h₂ := mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity : 0≤A/16) (Real.sqrt_nonneg H))
  linarith only [h₁,h₂,mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg H)]

private theorem persist {s B : ℝ} (hs : s=1 ∨ s= -1) (S E : Finset ℕ) (hne : E.Nonempty)
    {M H : ℕ} (hM : 1≤M) (hMH : M≤H) (hE : E ⊆ Finset.Icc M H) (hS : ∀ n ∈ S, Real.sqrt H<n)
    (hmargin : B/4*Real.sqrt H < s*oddQuotientPrimeExcess S H)
    (hcost : ((H:ℝ)-M)*(2*Real.log H+2+2*|Real.eulerMascheroniConstant|)+40*Real.sqrt H ≤ B/8*Real.sqrt H) :
    (B/8)*Real.sqrt H < s*commonFactorialDivisorDiscrepancy S E := by
  have hdiff := (oriented_le_abs hs _).trans ((commonOddQuotientPrimeExcess_change S E hM hMH hne hE).trans hcost)
  rw [commonFactorialDivisorDiscrepancy_eq S E H (fun _ hj => (Finset.mem_Icc.mp (hE hj)).2) hS]
  linarith only [hdiff,hmargin]

/-- At each selected late test, one fixed interior interval and one fixed
exterior interval of prime factors carry opposite discrepancies for the gcd over every
nonempty selection from a common block of length H^(1/2+d). The exterior
interval is an entire side of the original cut above the square root. -/
theorem riemannHypothesis_or_consecutive_factorial_discrepancies : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (c g d : ℝ), 0<W ∧
      (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<c ∧ 0<g ∧ 0<d ∧ d≤1/4 ∧ ∀ η : ℝ, 0<η → η≤1 →
      ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (v s : ℝ) (j H a b l u : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
          H=⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊ ∧ Real.exp (T i)≤H ∧
          (H:ℝ)^(g/6) ≤ Real.exp (g*T i) ∧ k i<a ∧ a≤b ∧ b≤L i ∧ Real.sqrt H<a ∧
          ((ordinaryBandAtDisplacement (k i) (L i) (T i) v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
          ((l=⌊Real.sqrt H⌋₊ ∧ u=a-1) ∨ (l=b ∧ u=H)) ∧
          ∀ M : ℕ, 1≤M → M≤H → (H:ℝ)-M ≤ (H:ℝ)^(1/2+d) →
            ∀ E : Finset ℕ, E.Nonempty → E ⊆ Finset.Icc M H →
              c*Real.exp (g*T i)*Real.sqrt H < s*commonFactorialDivisorDiscrepancy (Finset.Icc a b) E ∧
              c*Real.exp (g*T i)*Real.sqrt H < (-s)*commonFactorialDivisorDiscrepancy (Finset.Ioc l u) E := by
  rcases riemannHypothesis_or_odd_quotient_prime_deficit with hr | ⟨W,F,Φ,A,g,hW,ht,hF,hc,he,hA,hg,h⟩
  · exact Or.inl hr
  obtain ⟨C,hC,hall⟩ := oddQuotientPrimeExcess_complete_above_sqrt
  let d := min (g/12) (1/4)
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  obtain ⟨U,hlog⟩ := eventually_atTop.mp (eventual_log_price hd hA)
  refine Or.inr ⟨W,F,Φ,A/8,g,d,hW,ht,hF,hc,he,by positivity,hg,hd,min_le_right ..,fun η hη hη1 => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,hw⟩ := h η hη hη1
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hE := Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hg)
  have hX := Real.tendsto_exp_atTop.comp hT
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right (by linarith only [hA] : A/8≤A)
    (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hw,hX.eventually_ge_atTop (max U 1),
    (hE.const_mul_atTop hA).eventually_ge_atTop (4*C),
    (hE.const_mul_atTop (show 0<A/16 by positivity)).eventually_ge_atTop 40] with i hw hU hbig h40
  obtain ⟨v,s,j,H,a,b,hv,hs,hor,hj,hHX,hpow,ha,hab,hb,hroot,hcell,_,hdef⟩ := hw
  let E := Real.exp (g*T i)
  let B := A*E
  have hH : 1≤(H:ℝ) := (le_max_right U 1).trans (hU.trans hHX)
  have hS (n : ℕ) (hn : n∈Finset.Icc a b) : Real.sqrt H<n :=
    hroot.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1)
  have hmid : B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H := by
    rw [oddQuotientPrimeExcess_eq_factorial_divisors _ _ hS]
    exact hdef
  obtain ⟨l,u,hside,hsideS,hother⟩ := other_interval hC hbig hs hab hroot (hall H) hmid
  refine ⟨v,s,j,H,a,b,l,u,hv,hs,hor,hj,hHX,hpow,ha,hab,hb,hroot,hcell,hside,fun M hM hMH hwidth J hJ hsub => ?_⟩
  have hd₂ : (H:ℝ)^d*(H:ℝ)^d ≤ E := by
    rw [← Real.rpow_add (by linarith only [hH] : 0<(H:ℝ))]
    exact (Real.rpow_le_rpow_of_exponent_le hH (by linarith only [min_le_left (g/12) (1/4:ℝ)] : d+d≤g/6)).trans hpow
  have hcost := block_cost hM hMH hA hd₂ h40 (hlog _ ((le_max_left U 1).trans (hU.trans hHX))) hwidth
  have hB : 0≤B := mul_nonneg hA.le (Real.exp_pos _).le
  have hlow := persist hs (Finset.Icc a b) J hJ hM hMH hsub hS
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by linarith only [hB] : B/4≤B) (Real.sqrt_nonneg _)) hmid) hcost
  have hneg : -s=1 ∨ -s= -1 := hs.elim (fun h => Or.inr (by rw [h])) (fun h => Or.inl (by rw [h,neg_neg]))
  have hhigh := persist hneg (Finset.Ioc l u) J hJ hM hMH hsub hsideS hother hcost
  have heq : A/8*Real.exp (g*T i)=B/8 := by dsimp only [B,E]; ring
  rw [heq]; exact ⟨hlow,hhigh⟩

#print axioms riemannHypothesis_or_consecutive_factorial_discrepancies
end GaloisForLFunctions.ExclusionOfTheCriticalState
