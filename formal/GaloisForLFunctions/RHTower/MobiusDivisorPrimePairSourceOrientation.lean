import GaloisForLFunctions.RHTower.MobiusDivisorPrimePairRatioProfile

/-!
# Pair orientation and the change of a prescribed prime's debt

The uniform source profile determines the complete pair release on every
bounded window sufficiently far along the ratio ray. A common window
works for an even core and that core after a prescribed prime: the same
pair releases energy in the former and costs energy in the latter.
This identifies a failure of transferring a pair's credit unchanged to
a future source state. It does not exclude other ratios or prime orders.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private lemma source_density_pos (P : Finset ℕ) (hP : ∀p∈P,p.Prime) :
    0<Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1) := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]
    positivity
  · apply Finset.prod_pos
    intro p hp
    exact div_pos (by exact_mod_cast (hP p hp).pos) (by positivity)

private lemma ratio_lower {p q U : ℝ} (hp : 0<p) (hpq : p≤q) (hU : 1≤U)
    (hqU : q≤U*p) : 1/U^2≤(p/q)*Real.sqrt (p/q) := by
  have hq : 0<q := hp.trans_le hpq
  have hU0 : 0<U := lt_of_lt_of_le zero_lt_one hU
  have ha : 0<p/q := div_pos hp hq
  have hb : p/q≤1 := (div_le_one hq).mpr hpq
  have hl : 1/U≤p/q := by
    rw [div_le_div_iff₀ hU0 hq]
    simpa [mul_comm] using hqU
  have hs : p/q≤Real.sqrt (p/q) := by
    have hh := Real.sq_sqrt ha.le
    nlinarith [Real.sqrt_nonneg (p/q)]
  have hm := mul_le_mul hl hl (by positivity : (0:ℝ)≤1/U) ha.le
  calc
    _ = (1/U)*(1/U) := by ring
    _ ≤ (p/q)*(p/q) := hm
    _ ≤ _ := mul_le_mul_of_nonneg_left hs ha.le

/-- Beyond a source-derived ratio threshold, the complete pair release
has the original core's parity sign on every bounded ratio window.
The lower window endpoint remains freely selectable above that threshold. -/
theorem exists_mobiusDivisorPrime_pair_tail_orientation (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃L₀ : ℝ,1≤L₀ ∧ ∀L : ℝ,L₀≤L → ∃c T : ℝ,0<c ∧
      ∀p q : ℕ,p.Prime → q.Prime → p∉P → q∉P → q≠p → T≤(p:ℝ) →
      L*(p:ℝ)≤q → (q:ℝ)≤(L+1)*(p:ℝ) →
      c/(p:ℝ) ≤ (-1:ℝ)^P.card*((∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n) := by
  let s : ℝ := (-1)^P.card
  have hs : |s|=1 := by simp [s,abs_pow]
  have hor := divisorCoreMellinPairResidue_oriented_pos P hP hprime
  rw [pow_succ] at hor
  have hR : s*(divisorCoreMellinPairResidue P).re<0 := by dsimp [s]; nlinarith only [hor]
  let a := -(s*(divisorCoreMellinPairResidue P).re)/4
  have ha : 0<a := by dsimp [a]; linarith
  have ht := ((tendsto_mobiusDivisorDilationMean P hP hprime).const_mul s).eventually
    (eventually_lt_nhds (show s*(divisorCoreMellinPairResidue P).re < -2*a by dsimp [a]; linarith))
  obtain ⟨Λ,hΛ⟩ := Filter.eventually_atTop.mp ht
  obtain ⟨C,hC,hprofile⟩ := exists_bound_mobiusDivisorPrime_pair_ratio_profile P hP hprime
  let ρ := Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1)
  have hρ : 0<ρ := source_density_pos P hprime
  refine ⟨max 1 Λ,le_max_left _ _,?_⟩
  intro L hL
  have hL1 : 1≤L := (le_max_left _ _).trans hL
  have hLU : 0<L+1 := by linarith
  let c := ρ*a/(L+1)^2
  have hc : 0<c := by dsimp [c]; positivity
  refine ⟨c,(C/c+1)^2,hc,?_⟩
  intro p q hp hq hpP hqP hqp hpT hqlo hqhi
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hpqR : (p:ℝ)≤q := calc
    _ = 1*(p:ℝ) := by ring
    _ ≤ L*(p:ℝ) := mul_le_mul_of_nonneg_right hL1 hpR.le
    _ ≤ q := hqlo
  have hpq : p≤q := by exact_mod_cast hpqR
  have hqR : (0:ℝ)<q := hpR.trans_le hpqR
  have hratio : Λ≤(q:ℝ)/p := (le_div_iff₀ hpR).mpr
    ((mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hL) hpR.le).trans hqlo)
  have hw := (hΛ ((q:ℝ)/p) hratio).le
  let τ := ((p:ℝ)/q)*Real.sqrt ((p:ℝ)/q)
  have hτ : 0≤τ := by dsimp [τ]; positivity
  have hτlo : 1/(L+1)^2≤τ := ratio_lower hpR hpqR (by linarith) hqhi
  let E := (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
    ∑'n,mobiusDivisorFixedCoreBlockMass P n
  have herror := hprofile p q hp hq hpP hqP hqp hpq
  have herr : |s*((p:ℝ)*E-2*ρ*τ*mobiusDivisorDilationMean P ((q:ℝ)/p))|≤C/Real.sqrt p := by
    rw [abs_mul,hs,one_mul]
    convert! herror using 1; dsimp [E,ρ,τ]; ring
  have hsmall : C/Real.sqrt p<c := by
    have ht0 := Real.sqrt_pos.mpr hpR
    have hroot := Real.sqrt_le_sqrt hpT
    rw [Real.sqrt_sq (by positivity : 0≤C/c+1)] at hroot
    have hm := mul_le_mul_of_nonneg_left hroot hc.le
    have he : c*(C/c+1)=C+c := by field_simp
    rw [he] at hm
    exact (div_lt_iff₀ ht0).mpr (by linarith)
  have hmain : 2*ρ*τ*(s*mobiusDivisorDilationMean P ((q:ℝ)/p))≤-4*c := by
    have hm := mul_le_mul_of_nonneg_left hw (show 0≤2*ρ*τ by positivity)
    have hl := mul_le_mul_of_nonneg_left hτlo (show 0≤4*ρ*a by positivity)
    have he : 4*c=4*ρ*a*(1/(L+1)^2) := by dsimp [c]; ring
    rw [← he] at hl
    nlinarith only [hm,hl]
  have hu := (abs_le.mp herr).2
  apply (div_le_iff₀ hpR).mpr
  have hfinal : c≤(s*(-E))*(p:ℝ) := by nlinarith only [hu,hmain,hsmall,hc]
  convert! hfinal using 1; dsimp [s,E]; ring

/-- The same separated pair releases energy before a prescribed prime
but costs energy after it. Both comparisons use one common ratio window
and one threshold, with no independent sign hypothesis. -/
theorem exists_mobiusDivisorPrime_pair_forced_prime_incompatibility (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card)
    {r : ℕ} (hr : r.Prime) (hrP : r∉P) :
    ∃L c T : ℝ,1≤L ∧ 0<c ∧ ∀p q : ℕ,p.Prime → q.Prime →
      p∉insert r P → q∉insert r P → q≠p → T≤(p:ℝ) →
      L*(p:ℝ)≤q → (q:ℝ)≤(L+1)*(p:ℝ) →
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n ∧
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p (insert r P))) n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n := by
  have hprimeR : ∀p∈insert r P,p.Prime := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · exact hr
    · exact hprime p hp
  obtain ⟨L₀,hL₀,hbase⟩ := exists_mobiusDivisorPrime_pair_tail_orientation P hP hprime
  obtain ⟨L₁,hL₁,hforced⟩ := exists_mobiusDivisorPrime_pair_tail_orientation
    (insert r P) (insert_nonempty _ _) hprimeR
  obtain ⟨c₀,T₀,hc₀,hbase⟩ := hbase (max L₀ L₁) (le_max_left _ _)
  obtain ⟨c₁,T₁,hc₁,hforced⟩ := hforced (max L₀ L₁) (le_max_right _ _)
  refine ⟨max L₀ L₁,min c₀ c₁,max T₀ T₁,hL₀.trans (le_max_left _ _),lt_min hc₀ hc₁,?_⟩
  intro p q hp hq hpR hqR hqp hpT hqlo hqhi
  have hpP : p∉P := fun h => hpR (mem_insert_of_mem h)
  have hqP : q∉P := fun h => hqR (mem_insert_of_mem h)
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp.pos
  have h₀ := hbase p q hp hq hpP hqP hqp ((le_max_left _ _).trans hpT) hqlo hqhi
  have h₁ := hforced p q hp hq hpR hqR hqp ((le_max_right _ _).trans hpT) hqlo hqhi
  rw [heven.neg_one_pow,one_mul] at h₀
  rw [card_insert_of_notMem hrP,pow_succ,heven.neg_one_pow,one_mul,neg_one_mul,neg_sub] at h₁
  exact ⟨(div_le_div_of_nonneg_right (min_le_left c₀ c₁) hp0.le).trans h₀,
    (div_le_div_of_nonneg_right (min_le_right c₀ c₁) hp0.le).trans h₁⟩

/-- Arbitrarily large pairs increase the prescribed prime's coefficient
debt, while releasing a positive reserve in the current even core. -/
theorem exists_arbitrarily_large_mobiusDivisor_forced_prime_debt_growth (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card)
    {r : ℕ} (hr : r.Prime) (hrP : r∉P) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∃p q : ℕ,N≤p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p∉insert r P ∧ q∉insert r P ∧
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n ∧
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p (insert r P))) n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert r P) n := by
  obtain ⟨L,c,T,hL,hc,hpair⟩ := exists_mobiusDivisorPrime_pair_forced_prime_incompatibility
    P hP hprime heven hr hrP
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between (one_div_pos.mpr hL0))
  refine ⟨c,hc,?_⟩
  intro N
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes
    (max N (max ((insert r P).sup id+1) ⌈max T Z⌉₊))
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hNp : N≤p := (le_max_left _ _).trans hpbound
  have hsup : (insert r P).sup id+1≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hpbound)
  have hceil : ⌈max T Z⌉₊≤p := (le_max_right _ _).trans ((le_max_right _ _).trans hpbound)
  have hTZ : max T Z≤(p:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpT : T≤(p:ℝ) := (le_max_left _ _).trans hTZ
  have hpL : (p:ℝ)≤L*(p:ℝ) := by simpa using mul_le_mul_of_nonneg_right hL hpR.le
  obtain ⟨q,hq,hqlo,hqhi⟩ := hZ (L*(p:ℝ)) (((le_max_right _ _).trans hTZ).trans hpL)
  have hpq : p<q := by exact_mod_cast (hpL.trans_lt hqlo)
  have hqhi' : (q:ℝ)≤(L+1)*(p:ℝ) := by
    have he : (1+1/L)*(L*(p:ℝ))=(L+1)*(p:ℝ) := by field_simp
    rw [he] at hqhi
    exact hqhi.le
  have hpP : p∉insert r P := by
    intro h
    have hle : p≤(insert r P).sup id := Finset.le_sup (f := id) h
    omega
  have hqP : q∉insert r P := by
    intro h
    have hle : q≤(insert r P).sup id := Finset.le_sup (f := id) h
    omega
  exact ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,hpair p q hp hq hpP hqP hpq.ne' hpT hqlo.le hqhi'⟩

end RHTower
