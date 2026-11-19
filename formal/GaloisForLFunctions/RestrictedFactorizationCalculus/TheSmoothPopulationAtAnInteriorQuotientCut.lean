import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola
import GaloisForLFunctions.RHTower.Sieve.MertensWindowSharp
import GaloisForLFunctions.RHTower.RobinLcmCriterion
import GaloisForLFunctions.ArithmeticWeightTheory.GaugeDeformations.PrimeAbelCutoff

/-!
# The signed prime reading above an interior quotient cut

At q > floor(X/Z), transposition keeps exactly the prime window
(floor(X/Z), floor(X/m)] for every m up to Z. The integer-floor
reading at the interior cofactor wall is the positive smooth
population. Both the prime interval and its signed remainder survive.
-/

noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The signed contribution of the quotient indices above floor(X/Z). -/
def upperQuotientReading (a : ArithmeticFunction ℝ) (y X Z : ℕ) :=
  ∑ q ∈ Ioc (X/Z) X,a q*coprimeMoebiusSum (primorial y) (X/q)

theorem transpose_the_upper_quotient_cells (a : ArithmeticFunction ℝ) (y X : ℕ) {Z : ℕ} (zp : 0<Z) :
    upperQuotientReading a y X Z=
      ∑ m ∈ Icc 1 Z,RoughReading.row y m*∑ q ∈ Ioc (X/Z) (X/m),a q := by
  let K := X/Z
  let f := fun m q : ℕ => if q ≤ X/m then RoughReading.row y m*a q else 0
  have inner (q : ℕ) (hq : q ∈ Ioc K X) :
      a q*coprimeMoebiusSum (primorial y) (X/q)=∑ m ∈ Icc 1 Z,f m q := by
    have qp : 0<q := (Nat.zero_le K).trans_lt (mem_Ioc.mp hq).1
    have lower := (Nat.div_lt_iff_lt_mul zp).mp (mem_Ioc.mp hq).1
    have before : X/q < Z := (Nat.div_lt_iff_lt_mul qp).mpr (by simpa only [Nat.mul_comm] using lower)
    have short := before.le
    have support : (Icc 1 Z).filter (fun m => q ≤ X/m)=Icc 1 (X/q) := by
      ext m
      simp only [mem_filter,mem_Icc]
      constructor
      · rintro ⟨⟨mp,_⟩,below⟩
        exact ⟨mp,(Nat.le_div_iff_mul_le qp).mpr (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le mp).mp below)⟩
      · rintro ⟨mp,below⟩
        exact ⟨⟨mp,below.trans short⟩,(Nat.le_div_iff_mul_le mp).mpr (by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le qp).mp below)⟩
    simp only [f,←sum_filter,support,coprimeMoebiusSum,mul_sum]
    exact sum_congr rfl (fun n hn => by rw [primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1,mul_comm])
  unfold upperQuotientReading
  rw [sum_congr rfl inner,sum_comm]
  apply sum_congr rfl
  intro m hm
  have support : (Ioc K X).filter (fun q => q ≤ X/m)=Ioc K (X/m) := by
    ext q
    simp only [mem_filter,mem_Ioc]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans (Nat.div_le_self ..)⟩,h.2⟩⟩
  simp only [f,←sum_filter,support,mul_sum]
  rfl

/-- The upper quotient sector has a *positive* interior smooth center.
Subtracting it changes the reading at every retained rough cofactor. -/
theorem positive_smooth_center_at_an_interior_quotient_cut (a : ArithmeticFunction ℝ)
    (y X : ℕ) {Z : ℕ} (zp : 0<Z) :
    upperQuotientReading a y X Z-(X:ℝ)/Z*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) Z).card=
      ∑ m ∈ RoughReading.freeSet y Z,RoughReading.row y m*((∑ q ∈ Ioc (X/Z) (X/m),a q)-(X:ℝ)/Z*(⌊(Z:ℝ)/m⌋:ℝ)) := by
  have eq := smooth_population_as_a_rough_floor_sum y (Z:ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast] at eq
  have support (f : ℕ → ℝ) : (∑ m ∈ Icc 1 Z,RoughReading.row y m*f m)=
      ∑ m ∈ RoughReading.freeSet y Z,RoughReading.row y m*f m := by
    simp only [RoughReading.freeSet,sum_filter]
    apply sum_congr rfl
    intro m _
    by_cases good : IsFree (RoughReading.banned y) m
    · rw [if_pos good]
    · rw [if_neg good,RoughReading.row_value,if_neg good,zero_mul]
  rw [transpose_the_upper_quotient_cells _ _ _ zp,support,←eq,mul_sum,←sum_sub_distrib]
  exact sum_congr rfl (fun _ _ => by ring)

private abbrev band (y Z : ℕ) := RHTower.Sieve.bigPrimeSet y Z

/-- Through the square of the prime wall the rough Möbius measure
consists exactly of the positive unit and the negative surviving primes. -/
theorem rough_row_through_the_first_prime_band {y Z : ℕ} (zp : 1 ≤ Z) (ceiling : Z ≤ y^2) (f : ℕ → ℝ) :
    (∑ m ∈ Icc 1 Z,RoughReading.row y m*f m)=f 1-∑ p ∈ band y Z,f p := by
  have sets : band y Z=(Icc 1 Z).filter (fun p => p.Prime ∧ y<p) := by
    ext p
    simp only [band,RHTower.Sieve.bigPrimeSet,mem_filter,mem_Icc]
    constructor
    · rintro ⟨⟨lo,hi⟩,pr⟩; exact ⟨⟨pr.pos,hi⟩,pr,lo⟩
    · rintro ⟨⟨_,hi⟩,pr,lo⟩; exact ⟨⟨lo,hi⟩,pr⟩
  have per (n : ℕ) (hn : n ∈ Icc 1 Z) :
      RoughReading.row y n*f n=(if n=1 then f n else 0)-(if n.Prime ∧ y<n then f n else 0) := by
    rcases eq_or_ne n 1 with rfl | different
    · simp [RoughReading.row_value,isFree_one,Nat.not_prime_one]
    rw [RoughReading.row_value,if_neg different,zero_sub]
    by_cases pr : n.Prime
    · have free : IsFree (RoughReading.banned y) n ↔ y<n := by
        simpa only [RoughReading.banned,Set.mem_setOf_eq,not_le] using isFree_prime (RoughReading.banned y) pr
      rw [moebius_apply_prime pr]
      by_cases lo : y<n <;> simp [free,pr,lo]
    · have bad : ¬IsFree (RoughReading.banned y) n := by
        intro good
        have hp : n.minFac ∈ n.primeFactors := Nat.mem_primeFactors.mpr
          ⟨Nat.minFac_prime different,Nat.minFac_dvd _,good.1⟩
        have large : y<n.minFac := lt_of_not_ge (show ¬n.minFac ≤ y from good.2 _ hp)
        have sq := (Nat.minFac_sq_le_self (mem_Icc.mp hn).1 pr).trans ((mem_Icc.mp hn).2.trans ceiling)
        exact (not_lt_of_ge sq) (Nat.pow_lt_pow_left large (by decide : 2 ≠ 0))
      simp [bad,pr]
  rw [sum_congr rfl per,sum_sub_distrib,sets,sum_filter]
  simp [zp]

/-- The reciprocal prime mass has its logarithmic profile uniformly in the upper endpoint. -/
theorem reciprocal_mass_above_the_prime_wall {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,y ≤ Z →
      |(∑ p ∈ band y Z,1/(p:ℝ))-Real.log (Real.log Z/Real.log y)| ≤ ε := by
  let C := 2*RHTower.Sieve.mertensFirstConst+1/2
  have grow := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [grow.eventually_ge_atTop (2*|C|/ε),eventually_ge_atTop (2:ℕ)] with y large yp
  intro Z yz
  have yp' : (1:ℝ)<y := by exact_mod_cast (show 1<y by omega)
  have yl := Real.log_pos yp'
  have order := Real.log_le_log (zero_lt_one.trans yp') (Nat.cast_le.mpr yz)
  have zl := yl.trans_le order
  have step := RHTower.Sieve.abs_sum_inv_bigPrimeSet_sub_le yp yz
  rw [Real.log_div zl.ne' yl.ne']
  have cy : C/Real.log y ≤ |C|/Real.log y := div_le_div_of_nonneg_right (le_abs_self _) yl.le
  have cz := (div_le_div_of_nonneg_right (le_abs_self C) zl.le).trans
    (div_le_div_of_nonneg_left (abs_nonneg C) yl order)
  have small : |C|/Real.log y ≤ ε/2 := (div_le_iff₀ yl).mpr (by
    have pay : 2*|C| ≤ Real.log (y:ℝ)*ε := (div_le_iff₀ ep).mp large
    linarith only [pay])
  exact step.trans ((add_le_add cz cy).trans (by linarith only [small]))

/-- Past the sieve wall the prime number theorem controls every interval
reading even if each proper prime power is independently kept, negated
or deleted. The error is relative to the upper endpoint. -/
theorem ordinary_prime_interval_price {ε : ℝ} (ep : 0<ε) :
    ∃ N : ℕ,0<N ∧ ∀ y K : ℕ,y ≤ K → N ≤ K → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      ∀ t : ℝ,(K:ℝ) ≤ t →
      |(∑ q ∈ Ioc K ⌊t⌋₊,a q)-(t-K)| ≤ ε*t := by
  let δ := ε/6
  have dp : 0<δ := div_pos ep (by norm_num)
  have theta := (Metric.tendsto_nhds.mp RHTower.tendsto_theta_div_self) δ dp
  have psi := (Metric.tendsto_nhds.mp RHTower.tendsto_psi_div_self) δ dp
  obtain ⟨B,fromB⟩ := eventually_atTop.mp (theta.and psi)
  let N : ℕ := max 1 ⌈B⌉₊
  refine ⟨N,Nat.zero_lt_one.trans_le (le_max_left ..),fun y K yK NK a dom same t Kt => ?_⟩
  have kp : 0<(K:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_one.trans_le ((le_max_left 1 ⌈B⌉₊).trans NK))
  have past : B ≤ (K:ℝ) := (Nat.le_ceil B).trans (Nat.cast_le.mpr ((le_max_right ..).trans NK))
  have approxim (u : ℝ) (hu : (K:ℝ) ≤ u) :
      |Chebyshev.theta u-u| ≤ δ*u ∧ |Chebyshev.psi u-u| ≤ δ*u := by
    have estimates := fromB u (past.trans hu)
    have up := kp.trans_le hu
    rw [Real.dist_eq,Real.dist_eq] at estimates
    have convert (z : ℝ) (bound : |z/u-1|<δ) : |z-u| ≤ δ*u := by
      calc |z-u| = |(z/u-1)*u| := by rw [sub_mul,div_mul_cancel₀ _ up.ne',one_mul]
           _ = |z/u-1| * u := by rw [abs_mul,abs_of_pos up]
           _ ≤ δ*u := mul_le_mul_of_nonneg_right bound.le up.le
    exact ⟨convert _ estimates.1,convert _ estimates.2⟩
  let I := Ioc K ⌊t⌋₊
  let pr := fun q : ℕ => if q.Prime then Real.log q else 0
  have ttheta : Chebyshev.theta t-Chebyshev.theta K=∑ q ∈ I,pr q := by
    simp only [Chebyshev.theta,Nat.floor_natCast,sum_filter,pr]
    exact sub_eq_of_eq_add ((sum_Ioc_consecutive _ (Nat.zero_le K) (Nat.le_floor Kt)).symm.trans (add_comm ..))
  have tpsi : Chebyshev.psi t-Chebyshev.psi K=∑ q ∈ I,vonMangoldt q := by
    simp only [Chebyshev.psi,Nat.floor_natCast]
    exact sub_eq_of_eq_add ((sum_Ioc_consecutive _ (Nat.zero_le K) (Nat.le_floor Kt)).symm.trans (add_comm ..))
  have between (q : ℕ) (hq : q ∈ I) : 2*pr q-vonMangoldt q ≤ a q ∧ a q ≤ vonMangoldt q := by
    have ad := abs_le.mp (dom q)
    refine ⟨?_,ad.2⟩
    by_cases hp : q.Prime
    · have free := (isFree_prime (RoughReading.banned y) hp).mpr
        (not_le.mpr (yK.trans_lt (mem_Ioc.mp hq).1))
      rw [same q hp,roughMangoldtWeight,roughRestriction_apply,if_pos free,vonMangoldt_apply_prime hp]
      simp only [pr,if_pos hp]; linarith
    · simp only [pr,if_neg hp,mul_zero,zero_sub]; exact ad.1
  have lo := sum_le_sum (fun q hq => (between q hq).1)
  have hi := sum_le_sum (fun q hq => (between q hq).2)
  rw [sum_sub_distrib,←mul_sum,←ttheta,←tpsi] at lo
  rw [←tpsi] at hi
  have T := approxim t Kt
  have K' := approxim K le_rfl
  have kδ := mul_le_mul_of_nonneg_left Kt dp.le
  apply abs_le.mpr
  dsimp only [δ] at *
  constructor <;> linarith only [lo,hi,(abs_le.mp T.1).1,(abs_le.mp T.1).2,(abs_le.mp T.2).1,
    (abs_le.mp T.2).2,(abs_le.mp K'.1).1,(abs_le.mp K'.1).2,(abs_le.mp K'.2).1,(abs_le.mp K'.2).2,kδ]


/-- The unit and surviving primes through Z have vanishing relative population. -/
theorem density_of_the_first_prime_band {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z : ℕ,y ≤ Z → (1+(band y Z).card:ℝ)/(Z:ℝ) ≤ ε := by
  have unit := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have lim := unit.add ArithmeticWeightTheory.GaugeDeformations.tendsto_primeCounting_div_nat_zero
  rw [add_zero] at lim
  obtain ⟨N,fromN⟩ := eventually_atTop.mp (lim.eventually_le_const ep)
  filter_upwards [eventually_ge_atTop N] with y large
  intro Z yz
  have sub : band y Z ⊆ Nat.primesLE Z := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(mem_Icc.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  rw [add_div,one_div]
  apply le_trans _ (fromN Z (large.trans yz))
  change (Z:ℝ)⁻¹+((band y Z).card:ℝ)/Z ≤ (Z:ℝ)⁻¹+(Nat.primeCounting Z:ℝ)/Z
  have card : (band y Z).card ≤ Nat.primeCounting Z := by
    simpa only [Nat.primesLE_card_eq_primeCounting] using card_le_card sub
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (Nat.cast_le.mpr card) (Nat.cast_nonneg (α := ℝ) Z))

/-- Uniform signed profile throughout y ≤ Z ≤ y² and X ≥ yZ.
Above the index floor(X/Z) the normalized prime reading equals
1 − log(log Z/log y) with an error tending to zero. All proper
prime-power weights can change independently. -/
theorem signed_profile_through_the_first_prime_band {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ Z X : ℕ,y ≤ Z → Z ≤ y^2 → y*Z ≤ X → ∀ a : ArithmeticFunction ℝ,
      (∀ q,|a q| ≤ vonMangoldt q) → (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
      |upperQuotientReading a y X Z/(X:ℝ)-(1-Real.log (Real.log Z/Real.log y))| ≤ ε := by
  let η := ε/8
  have hp : 0<η := div_pos ep (by norm_num)
  obtain ⟨N,_,window⟩ := ordinary_prime_interval_price hp
  filter_upwards [reciprocal_mass_above_the_prime_wall hp,reciprocal_mass_above_the_prime_wall (ε := 1) zero_lt_one,density_of_the_first_prime_band hp,
    eventually_ge_atTop N,eventually_ge_atTop (2:ℕ)] with y mass ceiling count large yp
  intro Z X yz zz room a dom same
  let K := X/Z
  let w := fun m : ℕ => ∑ q ∈ Ioc K (X/m),a q
  let P := band y Z
  let h := ∑ q ∈ P,1/(q:ℝ)
  let l := Real.log (Real.log Z/Real.log y)
  have pos : 0<y := by omega
  have zp := pos.trans_le yz
  have yk : y ≤ K := (Nat.le_div_iff_mul_le zp).mpr room
  have xp : 0<(X:ℝ) := Nat.cast_pos.mpr ((Nat.mul_pos pos zp).trans_le room)
  have kbound : (K:ℝ)*Z ≤ X := by exact_mod_cast Nat.div_mul_le_self X Z
  have sparse := count Z yz
  have cost (m : ℕ) (hm : 1 ≤ m) (mz : m ≤ Z) :
      |w m-((X:ℝ)/m-K)| ≤ η*((X:ℝ)/m) := by
    have lo : (K:ℝ) ≤ (X:ℝ)/m := (le_div_iff₀ (Nat.cast_pos.mpr hm)).mpr
      ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr mz) (Nat.cast_nonneg K)).trans kbound)
    simpa only [w,Nat.floor_div_natCast,Nat.floor_natCast] using
      window y K yk (large.trans yk) a dom same ((X:ℝ)/m) lo
  have first : |w 1-((X:ℝ)-K)| ≤ η*X := by
    simpa only [Nat.cast_one,div_one] using cost 1 (by decide) zp
  have each (p : ℕ) (pq : p ∈ P) : |w p-((X:ℝ)/p-K)| ≤ η*((X:ℝ)/p) :=
    cost p (mem_filter.mp pq).2.pos (mem_Icc.mp (mem_filter.mp pq).1).2
  have summed := (abs_sum_le_sum_abs (fun p => w p-((X:ℝ)/p-K)) P).trans (sum_le_sum each)
  have paid : |(∑ p ∈ P,w p)-((X:ℝ)*h-(P.card:ℝ)*K)| ≤ η*X*h := by
    simpa only [sum_sub_distrib,div_eq_mul_inv,one_mul,one_div,h,mul_assoc,←mul_sum,
      sum_const,nsmul_eq_mul] using summed
  have total : upperQuotientReading a y X Z=w 1-∑ p ∈ P,w p :=
    (transpose_the_upper_quotient_cells _ _ _ zp).trans (rough_row_through_the_first_prime_band zp zz w)
  have rounding : (1+(P.card:ℝ))*K ≤ η*X := by
    have size := (div_le_iff₀ (Nat.cast_pos.mpr zp)).mp sparse
    have hK := mul_le_mul_of_nonneg_right size (Nat.cast_nonneg (α := ℝ) K)
    linarith only [hK,mul_le_mul_of_nonneg_left kbound hp.le]
  have shape : |h-l| ≤ η := mass Z yz
  have yl := Real.log_pos (show (1:ℝ)<y by exact_mod_cast (show 1<y by omega))
  have zl := Real.log_pos (show (1:ℝ)<Z by exact_mod_cast (show 1<Z by omega))
  have maxlog := Real.log_le_log (Nat.cast_pos.mpr zp) (Nat.cast_le.mpr zz)
  rw [Nat.cast_pow,Real.log_pow] at maxlog
  have ratio : Real.log Z/Real.log y ≤ 2 := (div_le_iff₀ yl).mpr (by simpa using maxlog)
  have log2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have l1 := (Real.log_le_log (div_pos zl yl) ratio).trans log2
  have c : h ≤ 2 := by linarith only [(abs_le.mp (ceiling Z yz)).2,l1]
  change |upperQuotientReading a y X Z/(X:ℝ)-(1-l)| ≤ ε
  rw [total,show (w 1-∑ p ∈ P,w p)/(X:ℝ)-(1-l)=
    ((w 1-∑ p ∈ P,w p)-(1-l)*X)/(X:ℝ) by field_simp [xp.ne'],abs_div,abs_of_pos xp]
  apply (div_le_iff₀ xp).mpr
  apply abs_le.mpr
  have mx := mul_le_mul_of_nonneg_right (abs_le.mp shape).2 xp.le
  have mn := mul_le_mul_of_nonneg_right (abs_le.mp shape).1 xp.le
  have mh := mul_le_mul_of_nonneg_left c (mul_nonneg hp.le xp.le)
  have cp := mul_nonneg (Nat.cast_nonneg (α := ℝ) P.card) (Nat.cast_nonneg (α := ℝ) K)
  dsimp only [η] at *
  constructor <;> linarith only [(abs_le.mp first).1,(abs_le.mp first).2,(abs_le.mp paid).1,
    (abs_le.mp paid).2,rounding,mx,mn,mh,cp,Nat.cast_nonneg (α := ℝ) K,mul_nonneg ep.le xp.le]

private theorem positive_contributions_begin_above_the_prime_wall {y q : ℕ} (small : q ≤ y) :
    roughMangoldtWeight y q=0 := by
  rw [roughMangoldtWeight,roughRestriction_apply]
  by_cases unit : q=1
  · simp [unit]
  split
  · rename_i free
    have prime := Nat.minFac_prime unit
    have hp : q.minFac ∈ q.primeFactors := Nat.mem_primeFactors.mpr ⟨prime,Nat.minFac_dvd _,free.1⟩
    exact (free.2 _ hp ((Nat.le_of_dvd (Nat.pos_of_ne_zero free.1) (Nat.minFac_dvd _)).trans small)).elim
  · rfl

/-- In the polynomial range y² ≤ X ≤ y³, the interior profile gives
the negative main term of the complete logarithmically weighted
rough Möbius prefix, at every observation and uniformly in the wall. -/
theorem signed_bias_between_the_square_and_cube_of_the_prime_wall {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ y : ℕ in atTop,∀ X : ℕ,y^2 ≤ X → X ≤ y^3 →
      |roughLogarithmicHead y X/(X:ℝ)+
        (1-Real.log (Real.log ((X/y:ℕ):ℝ)/Real.log y))| ≤ ε := by
  filter_upwards [signed_profile_through_the_first_prime_band ep,eventually_ge_atTop (1:ℕ)] with y profile yp
  intro X low high
  let Z := X/y
  have yz : y ≤ Z := (Nat.le_div_iff_mul_le yp).mpr (by simpa only [pow_two] using low)
  have zp := yp.trans yz
  have upper : Z ≤ y^2 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul yp).mpr
    (by rw [Nat.succ_mul,←pow_succ]; exact high.trans_lt (Nat.lt_add_of_pos_right yp)))
  have prod : y*Z ≤ X := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self X y
  have rem := (Nat.mod_lt X yp).trans_le yz
  have cut : X/Z=y := by
    apply le_antisymm _ ((Nat.le_div_iff_mul_le zp).mpr prod)
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul zp).mpr
    rw [Nat.succ_mul]
    calc X = y*Z+X%y := (Nat.div_add_mod X y).symm
         _ < y*Z+Z := Nat.add_lt_add_left rem _
  let a := roughMangoldtWeight y
  have all : upperQuotientReading a y X Z=quotientReading (roughFloorCoefficient y a) X := by
    rw [upperQuotientReading,cut,coefficient_head_as_quotient_sum]
    apply sum_subset (fun q hq => mem_Icc.mpr ⟨(Nat.zero_le y).trans_lt (mem_Ioc.mp hq).1,(mem_Ioc.mp hq).2⟩)
    intro q hq out
    have small : q ≤ y := le_of_not_gt (fun past => out (mem_Ioc.mpr ⟨past,(mem_Icc.mp hq).2⟩))
    rw [show a q=0 from positive_contributions_begin_above_the_prime_wall small,zero_mul]
  have exactHead : quotientReading (roughFloorCoefficient y a) X= -roughLogarithmicHead y X :=
    (rough_action_as_a_coefficient_prefix y X a).symm.trans (full_rough_reading yp X)
  have paid := profile Z X yz upper prod a (mangoldt_dominated y) (fun _ _ => rfl)
  rw [all,exactHead,neg_div] at paid
  let h := roughLogarithmicHead y X/(X:ℝ)
  let v := 1-Real.log (Real.log (Z:ℝ)/Real.log y)
  change |-h-v| ≤ ε at paid
  change |h+v| ≤ ε
  rwa [show -h-v= -(h+v) by ring,abs_neg] at paid

/-- At the log-square sieve, the quotient cut floor(X/y²) retains a
positive fraction 1 − log 2 of X, uniformly over all choices at the
proper prime powers. -/
theorem upper_prime_charge_at_the_log_square_cutoff {ε : ℝ} (ep : 0<ε) :
    ∀ᶠ X : ℕ in atTop,let y := logSquareCutoff X
      ∀ a : ArithmeticFunction ℝ,(∀ q,|a q| ≤ vonMangoldt q) →
        (∀ p,p.Prime → a p=roughMangoldtWeight y p) →
        |upperQuotientReading a y X (y^2)/(X:ℝ)-(1-Real.log 2)| ≤ ε := by
  have prof := logSquareCutoff_tendsto_atTop (signed_profile_through_the_first_prime_band ep)
  filter_upwards [prof,log_square_deletion_cost (by norm_num : (1:ℝ)/2<1) (by norm_num : (0:ℝ)<1/3),
    logSquareCutoff_tendsto_atTop.eventually_ge_atTop 2,eventually_ge_atTop (1:ℕ)] with X row small two xp
  let y := logSquareCutoff X
  have y1 : (1:ℝ)<y := by exact_mod_cast (show 1<y by omega)
  have e1 := deletionPrice_one_le (by norm_num : (0:ℝ)<1) y
  have wall : (y:ℝ) ≤ (X:ℝ)^(1/3:ℝ) := by
    have square : 1 ≤ (deletionPrice 1 y)^2 := by nlinarith only [e1,sq_nonneg (deletionPrice 1 y-1)]
    have z := le_mul_of_one_le_right (show 0 ≤ (y:ℝ)+1 by positivity) square
    exact (show (y:ℝ) ≤ (y:ℝ)+1 by linarith).trans (z.trans small)
  have room : y*y^2 ≤ X := by
    have pw := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) y) wall 3
    have collapse : ((X:ℝ)^(1/3:ℝ))^3=X := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
    rw [collapse] at pw
    rw [Nat.mul_comm,←pow_succ]
    exact_mod_cast pw
  dsimp only
  intro a dom same
  have result := row (y^2) X (Nat.le_self_pow (by decide : 2 ≠ 0) y) le_rfl room a dom same
  have ratio : Real.log ((y^2:ℕ):ℝ)/Real.log y=2 := by
    rw [Nat.cast_pow,Real.log_pow]; push_cast; field_simp [(Real.log_pos y1).ne']
  rwa [ratio] at result

#print axioms upper_prime_charge_at_the_log_square_cutoff
#print axioms signed_bias_between_the_square_and_cube_of_the_prime_wall
#print axioms transpose_the_upper_quotient_cells
#print axioms positive_smooth_center_at_an_interior_quotient_cut
#print axioms signed_profile_through_the_first_prime_band
end GaloisForLFunctions.RestrictedFactorizationCalculus
