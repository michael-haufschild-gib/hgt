import GaloisForLFunctions.RHTower.MobiusDivisorComparablePrimeCost

/-!
# Source-derived pair reserves for every even nonempty prime core

The negative actual residue on an even core supplies a separated ratio
ray with a positive mean after one prime insertion. In a bounded window
of that ray, the second coefficient release dominates the first merger's
whole possible cost. Arbitrarily large prime pairs yield a positive net
reserve and preserve even cardinality. The finite-cutoff arithmetic
energies inherit the reserve eventually for each selected pair. Uniform
cutoff control and inclusion of every prime remain separate obligations.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory
namespace RHTower

/-- The actual negative residue of every even nonempty core becomes a
positive mean after one sufficiently large prime, throughout a full
separated ratio ray. No reserve or sign premise is supplied. -/
theorem exists_mobiusDivisorEvenCore_positive_ratio_ray (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃L c T : ℝ,1≤L ∧ 0<c ∧ ∀p : ℕ,p.Prime → p∉P → T≤(p:ℝ) →
      ∀Y : ℝ,L*(p:ℝ)≤Y → c*Real.sqrt p ≤ mobiusDivisorDilationMean (insert p P) Y := by
  have hor := divisorCoreMellinPairResidue_oriented_pos P hP hprime
  rw [pow_succ,heven.neg_one_pow] at hor
  simp only [one_mul,neg_one_mul] at hor
  let c := -(divisorCoreMellinPairResidue P).re/4
  have hc : 0<c := by dsimp [c]; linarith
  have ht := (tendsto_mobiusDivisorDilationMean P hP hprime).eventually
    (eventually_lt_nhds (show (divisorCoreMellinPairResidue P).re < -2*c by dsimp [c]; linarith))
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp ht
  obtain ⟨C,hC,hbound⟩ := exists_bound_mobiusDivisorDilationMean_insert_ratio P hP hprime
  refine ⟨max 1 L,c,(C/c+1)^2,le_max_left _ _,hc,?_⟩
  intro p hp hpP hpT Y hY
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hYp : (p:ℝ)≤Y := calc
    _ = 1*(p:ℝ) := by ring
    _ ≤ max 1 L*(p:ℝ) := mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) L) hpR.le
    _ ≤ Y := hY
  have hY1 : 1≤Y := hp1.trans hYp
  have hratio : L≤Y/(p:ℝ) := (le_div_iff₀ hpR).mpr
    ((mul_le_mul_of_nonneg_right (le_max_right (1:ℝ) L) hpR.le).trans hY)
  have hneg := hL (Y/(p:ℝ)) hratio
  have hcost := (abs_le.mp (hbound p hp hpP Y hY1)).1
  have hmargin : C<c*Real.sqrt p := by
    have hs := Real.sqrt_le_sqrt hpT
    rw [Real.sqrt_sq (by positivity : 0≤C/c+1)] at hs
    have hm := mul_le_mul_of_nonneg_left hs hc.le
    have he : c*(C/c+1)=C+c := by field_simp
    rw [he] at hm
    linarith
  have hm := mul_le_mul_of_nonneg_left hneg.le (Real.sqrt_nonneg (p:ℝ))
  nlinarith

private def reserveDensity (P : Finset ℕ) : ℝ :=
  Sieve.squarefreeDensity*∏r∈P,(r:ℝ)/(r+1)
private def reserveEnergy (P : Finset ℕ) : ℝ := ∑'n,mobiusDivisorFixedCoreBlockMass P n

private lemma density_pos (P : Finset ℕ) (hP : ∀p∈P,p.Prime) : 0<reserveDensity P := by
  apply mul_pos
  · rw [Sieve.squarefreeDensity_eq]
    positivity
  · apply Finset.prod_pos
    intro p hp
    exact div_pos (by exact_mod_cast (hP p hp).pos) (by positivity)

private lemma density_insert (P : Finset ℕ) {p : ℕ} (hpP : p∉P) :
    reserveDensity (insert p P)=(p:ℝ)/(p+1)*reserveDensity P := by
  simp only [reserveDensity,prod_insert hpP]
  ring

private lemma release_sqrt (P : Finset ℕ) (hP : ∀r∈P,r.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    reserveEnergy P-reserveEnergy (insert p P)=
      2*reserveDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2)*mobiusDivisorDilationMean P p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hr : (p:ℝ)^(-(3/2:ℝ))=Real.sqrt p/(p:ℝ)^2 := by
    rw [show -(3/2:ℝ)=1/2-2 by norm_num,Real.rpow_sub hpR,
      ← Real.sqrt_eq_rpow,Real.rpow_two]
  simpa only [reserveEnergy,reserveDensity,hr] using
    mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hP hp hpP

private lemma ratio_lower {p q U : ℝ} (hp : 0<p) (hpq : p≤q) (hqp : q≤U*p) :
    1/(U^2*p) ≤ Real.sqrt p*Real.sqrt q/q^2 := by
  have hq : 0<q := hp.trans_le hpq
  have hU : 0<U := by nlinarith
  have hh : p≤Real.sqrt p*Real.sqrt q := by
    calc
      _ = Real.sqrt p*Real.sqrt p := (Real.mul_self_sqrt hp.le).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hpq) (Real.sqrt_nonneg p)
  have hqq : q^2≤U^2*p^2 := by nlinarith
  calc
    _ ≤ p/q^2 := by
      rw [div_le_div_iff₀ (by positivity : 0<U^2*p) (pow_pos hq 2)]
      nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right hh (pow_pos hq 2).le

/-- Every even nonempty core supplies a separated prime-ratio window
whose sufficiently large pairs release a positive multiple of 1/p.
The first merger's entire possible cost is paid from the second release. -/
theorem exists_mobiusDivisorEvenCore_pair_reserve (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃L c T : ℝ,1≤L ∧ 0<c ∧ ∀p q : ℕ,p.Prime → q.Prime → p∉P → q∉P →
      q≠p → T≤(p:ℝ) → L*(p:ℝ)≤q → (q:ℝ)≤(L+1)*(p:ℝ) →
      c/(p:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
  obtain ⟨L,c,T,hL,hc,hray⟩ := exists_mobiusDivisorEvenCore_positive_ratio_ray P hP hprime heven
  obtain ⟨B,hB,hbound⟩ := exists_bound_mobiusDivisorDilationMean P hP hprime
  have hρ := density_pos P hprime
  let A := 2*reserveDensity P*B
  let d := reserveDensity P*c/(2*(L+1)^2)
  have hA : 0≤A := by dsimp [A]; positivity
  have hd : 0<d := by dsimp [d]; positivity
  refine ⟨L,d/2,max T ((2*A/d+1)^2),hL,by positivity,?_⟩
  intro p q hp hq hpP hqP hqp hpT hqlo hqhi
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hq1 : (1:ℝ)≤q := by exact_mod_cast hq.one_lt.le
  have hpqR : (p:ℝ)≤q := calc
    _ = 1*(p:ℝ) := by ring
    _ ≤ L*(p:ℝ) := mul_le_mul_of_nonneg_right hL hpR.le
    _ ≤ q := hqlo
  have hiprime : ∀r∈insert p P,r.Prime := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    · exact hprime r hr
  have hqi : q∉insert p P := by simp [hqp,hqP]
  have hw := hray p hp hpP ((le_max_left _ _).trans hpT) q hqlo
  have hrel := release_sqrt (insert p P) hiprime hq hqi
  have hρi := density_pos (insert q (insert p P)) (by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    · exact hiprime r hr)
  have hρlower : reserveDensity P/4≤reserveDensity (insert q (insert p P)) := by
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
  have hsecond : d/(p:ℝ)≤reserveEnergy (insert p P)-reserveEnergy (insert q (insert p P)) := by
    have hfactor : 0≤2*reserveDensity (insert q (insert p P))*(Real.sqrt q/(q:ℝ)^2) := by positivity
    have hwcost := mul_le_mul_of_nonneg_left hw hfactor
    rw [← hrel] at hwcost
    have hcost : (2*reserveDensity (insert q (insert p P))*c)*
        (Real.sqrt p*Real.sqrt q/(q:ℝ)^2) ≤
        reserveEnergy (insert p P)-reserveEnergy (insert q (insert p P)) := by
      convert! hwcost using 1; ring
    have hf : reserveDensity P*c/2≤2*reserveDensity (insert q (insert p P))*c := by
      nlinarith [mul_le_mul_of_nonneg_right hρlower hc.le]
    have ht := ratio_lower hpR hpqR hqhi
    have hm := mul_le_mul hf ht (by positivity : (0:ℝ)≤1/((L+1)^2*(p:ℝ))) (by positivity)
    dsimp [d]
    convert! hm.trans hcost using 1
    field_simp
  have hfirst : reserveEnergy (insert p P)-reserveEnergy P≤A*Real.sqrt p/(p:ℝ)^2 := by
    have hρp := density_pos (insert p P) hiprime
    have hρle : reserveDensity (insert p P)≤reserveDensity P := by
      rw [density_insert P hpP]
      have hr : (p:ℝ)/(p+1)≤1 := (div_le_one (by positivity)).mpr (by linarith)
      simpa using mul_le_mul_of_nonneg_right hr hρ.le
    have hw := (abs_le.mp (hbound p hp1)).1
    have hm := mul_le_mul_of_nonneg_left hw
      (show 0≤2*reserveDensity (insert p P)*(Real.sqrt p/(p:ℝ)^2) by positivity)
    rw [← release_sqrt P hprime hp hpP] at hm
    have hstep : reserveEnergy (insert p P)-reserveEnergy P≤
        reserveDensity (insert p P)*(2*Real.sqrt p/(p:ℝ)^2*B) := by
      convert! neg_le_neg hm using 1 <;> ring
    have hh := mul_le_mul_of_nonneg_right hρle
      (show 0≤2*Real.sqrt p/(p:ℝ)^2*B by positivity)
    dsimp [A]
    convert! hstep.trans hh using 1; ring
  have hsmall : A*Real.sqrt p/(p:ℝ)^2≤(d/2)/(p:ℝ) := by
    have hthreshold : (2*A/d+1)^2≤(p:ℝ) := (le_max_right _ _).trans hpT
    have hs := Real.sqrt_le_sqrt hthreshold
    rw [Real.sqrt_sq (by positivity : 0≤2*A/d+1)] at hs
    have hm := mul_le_mul_of_nonneg_left hs hd.le
    have he : d*(2*A/d+1)=2*A+d := by field_simp
    rw [he] at hm
    have hprod := mul_le_mul_of_nonneg_right hm (Real.sqrt_nonneg (p:ℝ))
    rw [mul_assoc,← pow_two,Real.sq_sqrt hpR.le] at hprod
    have hh : 2*A*Real.sqrt p≤d*(p:ℝ) := by
      nlinarith only [hprod,mul_nonneg hd.le (Real.sqrt_nonneg (p:ℝ))]
    rw [div_le_div_iff₀ (pow_pos hpR 2) hpR]
    nlinarith only [mul_le_mul_of_nonneg_right hh hpR.le]
  change (d/2)/(p:ℝ)≤reserveEnergy P-reserveEnergy (insert q (insert p P))
  have hpay := hfirst.trans hsmall
  have he : d/(p:ℝ)=2*((d/2)/(p:ℝ)) := by ring
  rw [he] at hsecond
  linarith

/-- Every even nonempty core has arbitrarily large prime pairs that
release a positive reserve and preserve even cardinality, so the same
source theorem applies again to the enlarged core. -/
theorem exists_arbitrarily_large_mobiusDivisorEvenCore_pair_reserve (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∃p q : ℕ,N≤p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p∉P ∧ q∉P ∧ Even (insert q (insert p P)).card ∧ c/(p:ℝ) ≤
        (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
          ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
  obtain ⟨L,c,T,hL,hc,hreserve⟩ := exists_mobiusDivisorEvenCore_pair_reserve P hP hprime heven
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between (one_div_pos.mpr hL0))
  refine ⟨c,hc,?_⟩
  intro N
  obtain ⟨p,hpbound,hp⟩ := Nat.exists_infinite_primes
    (max N (max (P.sup id+1) ⌈max T Z⌉₊))
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hNp : N≤p := (le_max_left _ _).trans hpbound
  have hsup : P.sup id+1≤p := (le_max_left _ _).trans ((le_max_right _ _).trans hpbound)
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
  have hpP : p∉P := by
    intro h
    have hle : p≤P.sup id := Finset.le_sup (f := id) h
    omega
  have hqP : q∉P := by
    intro h
    have hle : q≤P.sup id := Finset.le_sup (f := id) h
    omega
  have hqi : q∉insert p P := by simp [hpq.ne',hqP]
  have hnew : Even (insert q (insert p P)).card := by
    rw [card_insert_of_notMem hqi,card_insert_of_notMem hpP]
    obtain ⟨k,hk⟩ := heven
    exact ⟨k+1,by omega⟩
  exact ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,hnew,
    hreserve p q hp hq hpP hqP hpq.ne' hpT hqlo.le hqhi'⟩

/-- The source-selected reserve also holds for the actual arithmetic
energies at every sufficiently large cutoff for the selected pair. -/
theorem exists_arbitrarily_large_mobiusDivisorEvenCore_pair_energy_reserve (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃c : ℝ,0<c ∧ ∀N : ℕ,∃p q : ℕ,N≤p ∧ p<q ∧ p.Prime ∧ q.Prime ∧
      p∉P ∧ q∉P ∧ Even (insert q (insert p P)).card ∧ ∀ᶠM : ℕ in atTop,
        c/(p:ℝ)*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M P-
          mobiusDivisorSelectionEnergy M (insert q (insert p P)) := by
  obtain ⟨c,hc,hpairs⟩ := exists_arbitrarily_large_mobiusDivisorEvenCore_pair_reserve P hP hprime heven
  refine ⟨c/2,by positivity,?_⟩
  intro N
  obtain ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,hnew,hreserve⟩ := hpairs N
  refine ⟨p,q,hNp,hpq,hp,hq,hpP,hqP,hnew,?_⟩
  have hboth : ∀r∈insert q (insert p P),r.Prime := by
    intro r hr
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    · exact hprime r hr
  have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq P hprime).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq _ hboth)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have hstrict : (c/2)/(p:ℝ) < (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert q (insert p P)) n := by
    apply lt_of_lt_of_le _ hreserve
    exact div_lt_div_of_pos_right (by linarith) hpR
  have he := ht.eventually (eventually_gt_nhds hstrict)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
  have hMR : (0:ℝ)<M := by exact_mod_cast hM0
  simp only [← sub_div] at hM
  exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

end RHTower
