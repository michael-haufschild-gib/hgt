import Mathlib.Algebra.GCDMonoid.Finset
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PersistentOppositeOddQuotientIntervals
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
  let d := min (g/12) (1/4)
  have hd : 0<d := lt_min (by positivity) (by norm_num)
  refine Or.inr ⟨W,F,Φ,A/8,g,d,hW,ht,hF,hc,he,by positivity,hg,hd,min_le_right ..,fun η hη hη1 => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,hw⟩ := h η hη hη1
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right (by linarith only [hA] : A/8≤A)
    (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hw,hT.eventually (eventually_paired_quotient_intervals hA hg)] with i hw hp
  obtain ⟨v,s,j,H,a,b,hv,hs,hor,hj,hHX,hpow,ha,hab,hb,hroot,hcell,_,hdef⟩ := hw
  have hin (n : ℕ) (hn : n∈Finset.Icc a b) : Real.sqrt H<n :=
    hroot.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1)
  rw [← oddQuotientPrimeExcess_eq_factorial_divisors _ _ hin] at hdef
  obtain ⟨l,u,hside,hpair⟩ := hp H a b s hHX hpow hs hab hroot hdef
  refine ⟨v,s,j,H,a,b,l,u,hv,hs,hor,hj,hHX,hpow,ha,hab,hb,hroot,hcell,hside,fun M hm hMH hwidth J hJ hsub => ?_⟩
  have hout (n : ℕ) (hn : n∈Finset.Ioc l u) : Real.sqrt H<n := by
    rcases hside with ⟨hl,_⟩|⟨hl,_⟩
    · exact (Nat.floor_lt (Real.sqrt_nonneg _)).mp (hl ▸ (Finset.mem_Ioc.mp hn).1)
    · exact hroot.trans_le (Nat.cast_le.mpr (hab.trans (hl ▸ (Finset.mem_Ioc.mp hn).1.le)))
  have htop (j : ℕ) (hj : j∈J) := (Finset.mem_Icc.mp (hsub hj)).2
  rw [commonFactorialDivisorDiscrepancy_eq _ J H htop hin,commonFactorialDivisorDiscrepancy_eq _ J H htop hout]
  exact hpair M hm hMH hwidth J hJ hsub

#print axioms riemannHypothesis_or_consecutive_factorial_discrepancies
end GaloisForLFunctions.ExclusionOfTheCriticalState
