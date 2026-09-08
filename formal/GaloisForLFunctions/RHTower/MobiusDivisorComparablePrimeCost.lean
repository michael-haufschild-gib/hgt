import GaloisForLFunctions.RHTower.MobiusDivisorDilationMeanUniformRenewal

/-!
# Comparable prime mergers consume more than the first-prime credit

The uniform physical ratio band forces a second coefficient increase of
order 1/p. The first-prime release is at most order p^(-3/2), so every
sufficiently large pair in that band raises the coefficient above its
original value. The corpus prime-interval theorem supplies such pairs
beyond every cutoff; the actual finite-cutoff energies inherit the cost.
Constants depend on the original core. No complete prime order is ruled
out and no exhaustive reserve is assumed.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private def coreDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1)
private def coreEnergy (P : Finset ℕ) : ℝ := ∑'n,mobiusDivisorFixedCoreBlockMass P n

private lemma density_pos (P : Finset ℕ) (hP : ∀p∈P,p.Prime) : 0<coreDensity P := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]
    positivity
  · apply Finset.prod_pos
    intro p hp
    exact div_pos (by exact_mod_cast (hP p hp).pos) (by positivity)

private lemma density_insert (P : Finset ℕ) {p : ℕ} (hpP : p∉P) :
    coreDensity (insert p P)=(p:ℝ)/(p+1)*coreDensity P := by
  simp only [coreDensity,prod_insert hpP]
  ring

private lemma release_sqrt (P : Finset ℕ) (hP : ∀r∈P,r.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    coreEnergy P-coreEnergy (insert p P)=
      2*coreDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2)*mobiusDivisorDilationMean P p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr : (p:ℝ)^(-(3/2:ℝ))=Real.sqrt p/(p:ℝ)^2 := by
    rw [show -(3/2:ℝ)=1/2-2 by norm_num,Real.rpow_sub hpR,
      ← Real.sqrt_eq_rpow,Real.rpow_two]
  simpa only [coreEnergy,coreDensity,hr] using
    mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hP hp hpP

private lemma ratio_lower {p q : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤2*p) :
    1/(4*p) ≤ Real.sqrt p*Real.sqrt q/q^2 := by
  have hq : 0<q := hp.trans_le hpq
  have hh : p≤Real.sqrt p*Real.sqrt q := by
    calc
      _ = Real.sqrt p*Real.sqrt p := (Real.mul_self_sqrt hp.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpq) (Real.sqrt_nonneg p)
  have hqq : q^2≤4*p^2 := by nlinarith
  calc
    _ ≤ p/q^2 := by
      rw [div_le_div_iff₀ (by positivity : 0<4*p) (pow_pos hq 2)]
      nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right hh (pow_pos hq 2).le

/-- Two comparable large primes force a quantitative second-merger energy
increase. Both prime sizes vary; the original nonempty core is fixed. -/
theorem exists_mobiusDivisorComparablePrime_second_cost (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃η c T : ℝ,0<η ∧ 0<c ∧ ∀p q : ℕ,p.Prime → q.Prime → p∉P → q∉P →
      q≠p → T≤(p:ℝ) → p≤q → (q:ℝ)≤(1+η)*(p:ℝ) →
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert p P) n := by
  obtain ⟨η,c,T,hη,hc,hband⟩ :=
    exists_mobiusDivisorDilationMean_insert_negative_band P hP hprime
  have hρ := density_pos P hprime
  refine ⟨min η 1,coreDensity P*c/8,T,lt_min hη zero_lt_one,by positivity,?_⟩
  intro p q hp hq hpP hqP hqp hpT hpq hqη
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq.one_lt.le
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hqη' : (q:ℝ)≤(1+η)*(p:ℝ) := hqη.trans
    (mul_le_mul_of_nonneg_right (add_le_add_right (min_le_left η 1) 1) hpR.le)
  have hq2 : (q:ℝ)≤2*(p:ℝ) := hqη.trans (by
    have hh := mul_le_mul_of_nonneg_right (min_le_right η (1:ℝ)) hpR.le
    nlinarith)
  have hiprime : ∀r∈insert p P,r.Prime := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    · exact hprime r hr
  have hqi : q∉insert p P := by simp [hqp,hqP]
  have hw := hband p hp hpP hpT q hpqR hqη'
  have hrel := release_sqrt (insert p P) hiprime hq hqi
  have hρi := density_pos (insert q (insert p P)) (by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    · exact hiprime r hr)
  have hρlower : coreDensity P/4≤coreDensity (insert q (insert p P)) := by
    rw [density_insert _ hqi,density_insert _ hpP]
    have ha : (1/2:ℝ)≤(p:ℝ)/(p+1) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ)<p+1)]
      linarith
    have hb : (1/2:ℝ)≤(q:ℝ)/(q+1) := by
      rw [le_div_iff₀ (by positivity : (0:ℝ)<q+1)]
      linarith
    have hm := mul_le_mul hb ha (by norm_num : (0:ℝ)≤1/2) (by positivity : 0≤(q:ℝ)/(q+1))
    have hh := mul_le_mul_of_nonneg_right hm hρ.le
    nlinarith
  have hfactor : 0≤2*coreDensity (insert q (insert p P))*(Real.sqrt q/(q:ℝ)^2) := by positivity
  have hwcost := mul_le_mul_of_nonneg_left hw hfactor
  have hcost : (2*coreDensity (insert q (insert p P))*c)*
      (Real.sqrt p*Real.sqrt q/(q:ℝ)^2) ≤
      coreEnergy (insert q (insert p P))-coreEnergy (insert p P) := by
    rw [← hrel] at hwcost
    convert! neg_le_neg hwcost using 1 <;> ring
  have hf : coreDensity P*c/2≤2*coreDensity (insert q (insert p P))*c := by
    nlinarith [mul_le_mul_of_nonneg_right hρlower hc.le]
  have ht := ratio_lower hpR hpqR hq2
  have hm := mul_le_mul hf ht (by positivity : (0:ℝ)≤1/(4*(p:ℝ))) (by positivity)
  have hfinal := hm.trans hcost
  change (coreDensity P*c/8)/(p:ℝ)≤_
  convert! hfinal using 1; ring

/-- The comparable pair costs more than the first prime can release:
its net energy increase is at least a fixed positive multiple of 1/p. -/
theorem exists_mobiusDivisorComparablePrime_pair_cost (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃η c T : ℝ,0<η ∧ 0<c ∧ ∀p q : ℕ,p.Prime → q.Prime → p∉P → q∉P →
      q≠p → T≤(p:ℝ) → p≤q → (q:ℝ)≤(1+η)*(p:ℝ) →
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass P n := by
  obtain ⟨η,c,T,hη,hc,hcost⟩ := exists_mobiusDivisorComparablePrime_second_cost P hP hprime
  obtain ⟨B,hB,hbound⟩ := exists_bound_mobiusDivisorDilationMean P hP hprime
  have hρ := density_pos P hprime
  let A := 2*coreDensity P*B
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨η,c/2,max T ((2*A/c+1)^2),hη,by positivity,?_⟩
  intro p q hp hq hpP hqP hqp hpT hpq hqη
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hsecond := hcost p q hp hq hpP hqP hqp ((le_max_left _ _).trans hpT) hpq hqη
  have hrel := release_sqrt P hprime hp hpP
  have hρi : 0<coreDensity (insert p P) := by
    rw [density_insert P hpP]
    positivity
  have hρle : coreDensity (insert p P)≤coreDensity P := by
    rw [density_insert P hpP]
    have hr : (p:ℝ)/(p+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
    simpa using mul_le_mul_of_nonneg_right hr hρ.le
  have hfirst : coreEnergy P-coreEnergy (insert p P)≤A*Real.sqrt p/(p:ℝ)^2 := by
    rw [hrel]
    have hw := (le_abs_self (mobiusDivisorDilationMean P p)).trans (hbound p hp1)
    have hm := mul_le_mul_of_nonneg_left hw
      (show 0≤2*coreDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2) by positivity)
    have hfactor := mul_le_mul_of_nonneg_right hρle
      (show 0≤2*Real.sqrt p/(p:ℝ)^2*B by positivity)
    dsimp [A]
    apply hm.trans
    convert! hfactor using 1 <;> ring
  have hsmall : A*Real.sqrt p/(p:ℝ)^2≤(c/2)/(p:ℝ) := by
    have hthreshold : (2*A/c+1)^2≤(p:ℝ) := (le_max_right _ _).trans hpT
    have hs := Real.sqrt_le_sqrt hthreshold
    rw [Real.sqrt_sq (by positivity : 0≤2*A/c+1)] at hs
    have hm := mul_le_mul_of_nonneg_left hs hc.le
    have he : c*(2*A/c+1)=2*A+c := by field_simp
    rw [he] at hm
    have hprod := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (p:ℝ))
    have hsq := Real.sq_sqrt hpR.le
    rw [mul_assoc,← pow_two,hsq] at hprod
    have hh : 2*A*Real.sqrt p≤c*(p:ℝ) := by
      nlinarith only [hprod,mul_nonneg hc.le (Real.sqrt_nonneg (p:ℝ))]
    rw [div_le_div_iff₀ (pow_pos hpR 2) hpR]
    nlinarith only [mul_le_mul_of_nonneg_right hh hpR.le]
  change (c/2)/(p:ℝ)≤coreEnergy (insert q (insert p P))-coreEnergy P
  change c/(p:ℝ)≤coreEnergy (insert q (insert p P))-coreEnergy (insert p P) at hsecond
  have hpay := hfirst.trans hsmall
  have he : c/(p:ℝ)=2*((c/2)/(p:ℝ)) := by ring
  rw [he] at hsecond
  linarith

/-- The positive pair cost occurs beyond every prime cutoff. The corpus
prime-interval theorem supplies distinct primes in the actual ratio band. -/
theorem exists_arbitrarily_large_mobiusDivisorPrime_pair_cost (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∃p q : ℕ,N≤p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p∉P ∧ q∉P ∧ c/(p:ℝ) ≤
        (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
          ∑'n,mobiusDivisorFixedCoreBlockMass P n := by
  obtain ⟨η,c,T,hη,hc,hcost⟩ := exists_mobiusDivisorComparablePrime_pair_cost P hP hprime
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (prime_between hη)
  refine ⟨c,hc,?_⟩
  intro N
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes
    (max N (max (P.sup id+1) ⌈max T L⌉₊))
  have hNp : N≤p := (le_max_left _ _).trans hpbound
  have hsup : P.sup id+1≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hpbound)
  have hceil : ⌈max T L⌉₊≤p := (le_max_right _ _).trans ((le_max_right _ _).trans hpbound)
  have hTL : max T L≤(p:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hpT : T≤(p:ℝ) := (le_max_left _ _).trans hTL
  obtain ⟨q,hq,hpqR,hqη⟩ := hL p ((le_max_right _ _).trans hTL)
  have hpq : p<q := by exact_mod_cast hpqR
  have hpP : p∉P := by
    intro h
    have hle : p≤P.sup id := Finset.le_sup (f := id) h
    omega
  have hqP : q∉P := by
    intro h
    have hle : q≤P.sup id := Finset.le_sup (f := id) h
    omega
  exact ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,
    hcost p q hp hq hpP hqP hpq.ne' hpT hpq.le hqη.le⟩

/-- Arbitrarily large actual prime pairs have a quadratic energy cost at
every sufficiently large physical cutoff. The cutoff threshold is allowed
to depend on the pair; no uniform exhaustion claim is made. -/
theorem exists_arbitrarily_large_mobiusDivisorPrime_pair_energy_cost (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∃p q : ℕ,N≤p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p∉P ∧ q∉P ∧ ∀ᶠM : ℕ in atTop,
        c/(p:ℝ)*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M (insert q (insert p P))-
          mobiusDivisorSelectionEnergy M P := by
  obtain ⟨c,hc,hpairs⟩ := exists_arbitrarily_large_mobiusDivisorPrime_pair_cost P hP hprime
  refine ⟨c/2,by positivity,?_⟩
  intro N
  obtain ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,hcost⟩ := hpairs N
  refine ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,?_⟩
  have hboth : ∀r∈insert q (insert p P),r.Prime := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    · exact hprime r hr
  have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq _ hboth).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq P hprime)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hstrict : (c/2)/(p:ℝ) <
      (∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass P n := by
    apply lt_of_lt_of_le _ hcost
    exact div_lt_div_of_pos_right (by linarith) hpR
  have he := ht.eventually (eventually_gt_nhds hstrict)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
  have hMR : (0:ℝ)<M := by exact_mod_cast hM0
  simp only [← sub_div] at hM
  exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

end RHTower
