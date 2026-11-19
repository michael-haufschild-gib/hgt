import GaloisForLFunctions.RestrictedFactorizationCalculus.TheSignedBoundaryOfAPrefix
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeMassInDeficientRows

/-!
# Signed surplus above the cube-root threshold

Every composite rough tail above this threshold has exactly two prime factors.
The pair count fits in nine tenths of the prime row, uniformly in both sharp
endpoints at fixed logarithmic relative width. Its divisor sum therefore has
a definite sign even when the least-prime cutoff varies with the interval.
-/

noncomputable section

open Finset Filter RHTower ArithmeticFunction
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The single-prime exits of a least-prime row. -/
def tailPrimes (L U y : ℕ) := (Nat.primesLE U).filter (fun p => max L y < p)

private theorem tailPrimes_eq_window {L U y : ℕ} (hy : y ≤ L) :
    tailPrimes L U y = windowPrimes L U := by
  apply Finset.ext
  intro p
  rw [mem_windowPrimes (by positivity) (by positivity)]
  simp only [tailPrimes,mem_filter,Nat.mem_primesLE,max_eq_left hy,Nat.cast_lt,Nat.cast_le]
  tauto

private theorem tailPrimes_eq_real_window {u v : ℝ} {y : ℕ} (hy : (y:ℝ) ≤ u) :
    tailPrimes ⌊u⌋₊ ⌊v⌋₊ y = windowPrimes u v := by
  rw [tailPrimes_eq_window (Nat.le_floor hy)]
  simp only [windowPrimes,Nat.floor_natCast]

/-- Composite squarefree tails whose prime factors all exceed the cutoff. -/
def compositeTails (L U y : ℕ) := (roughTails L U y).filter (fun n => ¬n.Prime)

/-- Deleting the least prime from a composite tail gives a nonunit member of its child row. -/
theorem peel_composite_tail {L U y n : ℕ} (hn : n ∈ roughTails L U y) (hc : ¬n.Prime) :
    ∃ m ∈ roughTails (L/n.minFac) (U/n.minFac) n.minFac, m*n.minFac = n := by
  obtain ⟨hn1,_,hU,_,hy⟩ := mem_roughTails.mp hn
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hF : n ∈ (roughTails L U y).filter (fun w => w.minFac = n.minFac) :=
    mem_filter.mpr ⟨hn,rfl⟩
  rw [roughTails_minFac_fibre hp hy ((Nat.minFac_le (by omega)).trans hU)] at hF
  rcases mem_union.mp hF with h | h
  · split_ifs at h
    · exact False.elim (hc ((mem_singleton.mp h) ▸ hp))
    · exact False.elim (notMem_empty _ h)
  · exact mem_image.mp h

private theorem prime_of_short_tail {L U y n : ℕ} (hn : n ∈ roughTails L U y)
    (hs : n ≤ y^2) : n.Prime := by
  by_contra hc
  obtain ⟨m,hm,he⟩ := peel_composite_tail hn hc
  obtain ⟨hm1,_,_,_,hp⟩ := mem_roughTails.mp hm
  obtain ⟨hn1,_,_,_,hy⟩ := mem_roughTails.mp hn
  have hp0 := (Nat.minFac_prime (by omega : n ≠ 1)).pos
  have hm' := hp.trans_le (Nat.minFac_le (by omega))
  have h := (Nat.mul_le_mul hy.le hy.le).trans_lt (Nat.mul_lt_mul_of_pos_right hm' hp0)
  rw [he,← pow_two] at h
  omega

/-- Every composite in a cube-root rough row has a unique least prime and a
larger prime as complementary factor. -/
theorem cube_root_tail_pair {L U y n : ℕ} (hU : U ≤ y^3) (hn : n ∈ compositeTails L U y) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ y < q ∧ q < r ∧ n = q*r := by
  obtain ⟨hn,hc⟩ := mem_filter.mp hn
  obtain ⟨hn1,_,hnu,_,hy⟩ := mem_roughTails.mp hn
  obtain ⟨m,hm,he⟩ := peel_composite_tail hn hc
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hs : m ≤ n.minFac^2 := by
    by_contra! h
    have hh := Nat.mul_lt_mul_of_pos_right h hp.pos
    rw [he,← pow_succ] at hh
    exact (not_lt_of_ge (hnu.trans (hU.trans (Nat.pow_le_pow_left hy.le 3)))) hh
  have hpr := prime_of_short_tail hm hs
  obtain ⟨_,_,_,_,hlt⟩ := mem_roughTails.mp hm
  exact ⟨n.minFac,m,hp,hpr,hy,by simpa only [hpr.minFac_eq] using hlt,he.symm.trans (Nat.mul_comm m n.minFac)⟩

/-- The prime boundary is precisely the prime part of the rough row. -/
theorem mem_tailPrimes {L U y p : ℕ} :
    p ∈ tailPrimes L U y ↔ p ∈ roughTails L U y ∧ p.Prime := by
  constructor
  · intro h
    obtain ⟨hP,hh⟩ := mem_filter.mp h
    obtain ⟨hpU,hp⟩ := Nat.mem_primesLE.mp hP
    obtain ⟨hL,hy⟩ := max_lt_iff.mp hh
    exact ⟨mem_roughTails.mpr ⟨hp.one_lt,hL,hpU,Irreducible.squarefree hp,
      by simpa only [hp.minFac_eq] using hy⟩,hp⟩
  · rintro ⟨hn,hp⟩
    obtain ⟨_,hL,hU,_,hy⟩ := mem_roughTails.mp hn
    exact mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hU,hp⟩,max_lt hL (by simpa only [hp.minFac_eq] using hy)⟩

/-- Exact signed residual after charging one prime for each composite tail. -/
theorem cube_root_tail_balance (L U y : ℕ) (hU : U ≤ y^3) :
    tailBalance L U y = ((tailPrimes L U y).card:ℤ) - (compositeTails L U y).card := by
  let P := tailPrimes L U y
  let C := compositeTails L U y
  have hsplit : roughTails L U y = P ∪ C := by
    ext n
    constructor
    · intro h
      by_cases hp : n.Prime
      · exact mem_union_left _ (mem_tailPrimes.mpr ⟨h,hp⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨h,hp⟩)
    · exact fun h => (mem_union.mp h).elim (fun a => (mem_tailPrimes.mp a).1)
        (fun a => (mem_filter.mp a).1)
  have hdis : Disjoint P C := disjoint_left.mpr (fun _ hP hC =>
    (mem_filter.mp hC).2 (mem_tailPrimes.mp hP).2)
  have hp : ∑ n ∈ P, μ n = -(P.card:ℤ) := by
    calc _ = ∑ _ ∈ P, (-1:ℤ) := sum_congr rfl (fun _ h => moebius_apply_prime (mem_tailPrimes.mp h).2)
         _ = _ := by simp
  have hc : ∑ n ∈ C, μ n = (C.card:ℤ) := by
    calc _ = ∑ _ ∈ C, (1:ℤ) := by
              apply sum_congr rfl
              intro n hn
              obtain ⟨q,r,hq,hr,_,hqr,rfl⟩ := cube_root_tail_pair hU hn
              rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.coprime_primes hq hr).2 hqr.ne),
                moebius_apply_prime hq,moebius_apply_prime hr]
              decide
         _ = _ := by simp
  change -(∑ n ∈ roughTails L U y, μ n) = (P.card:ℤ) - C.card
  rw [hsplit,sum_union hdis,hp,hc]
  ring

/-- Uniform positive signed balance on every sufficiently large cube-root
rough row of fixed logarithmic relative width. -/
theorem eventually_real_cube_root_surplus (B : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ u v : ℝ, ∀ y : ℕ, s^6 ≤ u → u ≤ v → v ≤ 2*s^6 →
      s^6 / Real.log s ^ B ≤ v-u → ⌊v⌋₊ ≤ y^3 →
      ((tailPrimes ⌊u⌋₊ ⌊v⌋₊ y).card:ℤ) ≤ 10 * tailBalance ⌊u⌋₊ ⌊v⌋₊ y := by
  filter_upwards [eventually_ge_atTop (2:ℝ),eventually_cubeProducts_nine_tenths B] with s hs hcap
  intro u v y hu huv hv hw hy
  have hs0 : 0 ≤ s := by linarith only [hs]
  have hu0 := (pow_nonneg hs0 6).trans hu
  have hv0 := hu0.trans huv
  rw [cube_root_tail_balance _ _ _ hy]
  by_cases hC : (compositeTails ⌊u⌋₊ ⌊v⌋₊ y).Nonempty
  · obtain ⟨n,hn⟩ := hC
    obtain ⟨q,r,_,hr,hyq,_,hen⟩ := cube_root_tail_pair hy hn
    obtain ⟨_,hnL,hnU,_,_⟩ := mem_roughTails.mp (mem_filter.mp hn).1
    have hnv := (Nat.cast_le.mpr hnU).trans (Nat.floor_le hv0)
    have hqL : (q:ℝ) ≤ u := by
      have hqr : 2*q ≤ n := by rw [hen,mul_comm 2]; exact Nat.mul_le_mul_left q hr.two_le
      have hqr' : 2*(q:ℝ) ≤ n := by exact_mod_cast hqr
      linarith only [hqr',hnv,hv,hu]
    have hpEq := tailPrimes_eq_real_window (v := v) ((by exact_mod_cast hyq.le : (y:ℝ) ≤ q).trans hqL)
    have hbase : s^2 ≤ (y:ℝ) := by
      apply (pow_le_pow_iff_left₀ (sq_nonneg s) (Nat.cast_nonneg _) (by decide : 3 ≠ 0)).1
      calc (s^2)^3 = s^6 := by ring
           _ ≤ (n:ℝ) := hu.trans ((Nat.floor_lt hu0).1 hnL).le
           _ ≤ _ := by exact_mod_cast hnU.trans hy
    have hsub : compositeTails ⌊u⌋₊ ⌊v⌋₊ y ⊆ cubeProducts s u v := by
      intro n hn
      obtain ⟨a,b,ha,hb,hya,hab,he⟩ := cube_root_tail_pair hy hn
      obtain ⟨_,hlo,hhi,_,_⟩ := mem_roughTails.mp (mem_filter.mp hn).1
      have ha0 : (0:ℝ) < a := by exact_mod_cast ha.pos
      rw [he] at hlo hhi ⊢
      have hlow := (Nat.floor_lt hu0).1 hlo
      have hhigh := (Nat.cast_le.mpr hhi).trans (Nat.floor_le hv0)
      push_cast at hlow hhigh
      have hprod := hhigh.trans hv
      have hau : (a:ℝ) ≤ 2*s^3 := by
        by_contra! h
        have hh := mul_lt_mul_of_pos_right h (show 0 < (a:ℝ)+2*s^3 by positivity)
        have hsq := mul_le_mul_of_nonneg_left (by exact_mod_cast hab.le : (a:ℝ) ≤ b) ha0.le
        nlinarith only [hsq,hh,hprod,pow_nonneg hs0 6]
      refine mem_biUnion.mpr ⟨a,(mem_windowPrimes (by positivity) (by positivity)).2
        ⟨ha,?_,hau⟩,mem_image.mpr ⟨b,(mem_windowPrimes (by positivity) (by positivity)).2
        ⟨hb,?_,?_⟩,rfl⟩⟩
      · have hlay : (y:ℝ) < a := by exact_mod_cast hya
        linarith only [hbase,hlay,sq_nonneg s]
      · rw [div_lt_iff₀ ha0,mul_comm]; exact hlow
      · rw [le_div_iff₀ ha0,mul_comm]; exact hhigh
    have h := (Nat.mul_le_mul_left 10 (card_le_card hsub)).trans (hcap u v hu huv hv hw)
    rw [←hpEq] at h
    omega
  · rw [not_nonempty_iff_eq_empty.mp hC,card_empty,Nat.cast_zero,sub_zero]
    omega

/-- Integer endpoints, including both boundaries of a partial octave. -/
theorem eventually_cube_root_signed_surplus (B : ℕ) :
    ∀ᶠ s : ℝ in atTop, ∀ L U y : ℕ, s^6 ≤ L → L ≤ U → (U:ℝ) ≤ 2*s^6 →
      s^6 / Real.log s ^ B ≤ (U:ℝ)-L → U ≤ y^3 →
      ((tailPrimes L U y).card:ℤ) ≤ 10 * tailBalance L U y := by
  filter_upwards [eventually_real_cube_root_surplus B] with s h L U y hL hLU hU hw hy
  simpa only [Nat.floor_natCast] using h L U y hL (by exact_mod_cast hLU) hU hw
    (by simpa only [Nat.floor_natCast] using hy)

/-- Each prime in a fixed range just above the fourth root begins an actual
branch of definite sign, with its full reciprocal-prime weight. -/
private theorem eventually_prime_band_branches :
    ∀ᶠ X : ℕ in atTop,
      let t := (X:ℝ)^(1/16:ℝ)
      ∀ p ∈ windowPrimes (2*t^4) (t^5), ((X:ℝ)/(20*Real.log X))*(1/(p:ℝ)) ≤
        ∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ) := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_real_cube_root_surplus 0)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp eventually_dyadic_prime_lower
  have hlim : Tendsto (fun X : ℕ => (X:ℝ)^(1/16:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 2,hlim.eventually_ge_atTop (max 2 (max H J))] with X hX ht
  let t := (X:ℝ)^(1/16:ℝ)
  let W := windowPrimes (2*t^4) (t^5)
  have ht2 : 2 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := by linarith only [ht2]
  have ht1 : 1 ≤ t := by linarith only [ht2]
  have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXL := Real.log_pos (by exact_mod_cast (by omega : 1 < X) : (1:ℝ) < X)
  have h16 : t^16=X := by
    dsimp [t]; rw [←Real.rpow_natCast,←Real.rpow_mul hX0.le]; norm_num
  have powers {a b : ℕ} (h : a ≤ b) : t^a ≤ t^b := pow_le_pow_right₀ ht1 h
  have hrow (p : ℕ) (hp : p ∈ W) : ((X:ℝ)/(20*Real.log X))*(1/(p:ℝ)) ≤
      ∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ) := by
    obtain ⟨hpp,hplo,hphi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    let T := (X:ℝ)/p
    have hT0 : 0 < T := div_pos hX0 hp0
    have h11 : t^11 ≤ T := by
      apply (le_div_iff₀ hp0).2
      calc t^11*(p:ℝ) ≤ t^11*t^5 := mul_le_mul_of_nonneg_left hphi (by positivity)
           _ = t^16 := by ring
           _ = _ := h16
    have htT : t ≤ T := (by simpa only [pow_one] using powers (by decide : 1 ≤ 11) : t ≤ t^11).trans h11
    have hpT : (p:ℝ) ≤ T := hphi.trans ((powers (by decide : 5 ≤ 11)).trans h11)
    have hpX : p ≤ X := by exact_mod_cast hphi.trans ((powers (by decide : 5 ≤ 16)).trans h16.le)
    let s := T^(1/6:ℝ)
    have hs0 : 0 ≤ s := Real.rpow_nonneg hT0.le _
    have hs6 : s^6=T := by dsimp [s]; rw [←Real.rpow_natCast,←Real.rpow_mul hT0.le]; norm_num
    have hts : t ≤ s := by
      apply (pow_le_pow_iff_left₀ ht0.le hs0 (by decide : 6 ≠ 0)).1
      rw [hs6]; exact (powers (by decide : 6 ≤ 11)).trans h11
    have hshort : ⌊2*T⌋₊ ≤ p^3 := by
      have hreal : 2*T ≤ (p:ℝ)^3 := by
        change 2*((X:ℝ)/p) ≤ _
        rw [←mul_div_assoc,div_le_iff₀ hp0,←h16]
        have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 2*t^4) hplo.le 4
        nlinarith only [hh,pow_nonneg ht0.le 16]
      exact_mod_cast (Nat.floor_le (by positivity : 0 ≤ 2*T)).trans hreal
    have hbal := hH s ((le_max_left _ _).trans ((le_max_right _ _).trans (ht.trans hts)))
      T (2*T) p hs6.le (by linarith only [hT0]) (by rw [hs6])
      (by rw [hs6,pow_zero,div_one]; linarith) hshort
    rw [tailPrimes_eq_real_window hpT] at hbal
    have hLo : ⌊T⌋₊ = X/p := by dsimp [T]; rw [Nat.floor_div_natCast,Nat.floor_natCast]
    have hHi : ⌊2*T⌋₊ = (2*X)/p := by
      have hv : 2*T = ((2*X:ℕ):ℝ)/p := by dsimp [T]; push_cast; ring
      rw [hv,Nat.floor_div_natCast,Nat.floor_natCast]
    rw [hLo,hHi] at hbal
    have he := minFac_signed_fibre (L := X) (U := 2*X) (y := 0) (p := p)
      (mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨by omega,hpp⟩,hpp.pos⟩)
    rw [if_neg hpX.not_gt,zero_add] at he
    have hbranch : ((windowPrimes T (2*T)).card:ℝ) ≤
        10 * (∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ)) := by
      rw [←he] at hbal
      exact_mod_cast hbal
    have hcnt := hJ T ((le_max_right _ _).trans ((le_max_right _ _).trans (ht.trans htT)))
    have hlog := Real.log_pos (by linarith only [ht2,htT] : 1 < 2*T)
    have hlogLe : Real.log (2*T) ≤ Real.log X := by
      apply Real.log_le_log (by positivity)
      dsimp [T]
      rw [←mul_div_assoc,div_le_iff₀ hp0]
      have h2p : (2:ℝ) ≤ p := by exact_mod_cast hpp.two_le
      simpa only [mul_comm (X:ℝ)] using mul_le_mul_of_nonneg_right h2p hX0.le
    have hcost : 10*(((X:ℝ)/(20*Real.log X))*(1/(p:ℝ))) ≤ (99/100)*T/Real.log (2*T) := by
      calc _ = ((1/2)*T)/Real.log X := by dsimp [T]; ring
           _ ≤ ((1/2)*T)/Real.log (2*T) := div_le_div_of_nonneg_left (by positivity) hlog hlogLe
           _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hT0]) hlog.le
    linarith only [hcost.trans (hcnt.trans hbranch)]
  exact hrow

/-- On every sufficiently large octave there is a single least-prime branch
of signed mass at least X^(3/4)/(80 log X); its first prime is within a
factor of two of twice the fourth root. -/
theorem eventually_large_single_prime_branch :
    ∀ᶠ X : ℕ in atTop,
      let t := (X:ℝ)^(1/16:ℝ)
      ∃ p : ℕ, p.Prime ∧ 2*t^4 < p ∧ (p:ℝ) ≤ 4*t^4 ∧
        t^12/(80*Real.log X) ≤
          ∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp (prime_between (by norm_num : (0:ℝ) < 1))
  have lim : Tendsto (fun X : ℕ => (X:ℝ)^(1/16:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_prime_band_branches,eventually_ge_atTop 2,
    lim.eventually_ge_atTop (max 4 K)] with X hrow hX ht
  let t := (X:ℝ)^(1/16:ℝ)
  have ht4 : 4 ≤ t := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ t := by linarith only [ht4]
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have hpow : t ≤ t^4 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1 ≤ 4)
  obtain ⟨p,hp,hlo,hhi⟩ := hK (2*t^4) (by
    linarith only [((le_max_right _ _).trans ht : K ≤ t),hpow,pow_nonneg ht0.le 4])
  have hu : (p:ℝ) ≤ 4*t^4 := by linarith only [hhi]
  have hwin : p ∈ windowPrimes (2*t^4) (t^5) := by
    apply (mem_windowPrimes (by positivity) (by positivity)).2
    refine ⟨hp,hlo,hu.trans ?_⟩
    rw [pow_succ t 4,mul_comm (t^4)]
    exact mul_le_mul_of_nonneg_right ht4 (pow_nonneg ht0.le 4)
  have hX0 : (0:ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hXL := Real.log_pos (by exact_mod_cast (by omega : 1 < X) : (1:ℝ) < X)
  have h16 : t^16 = X := by
    dsimp [t]; rw [←Real.rpow_natCast,←Real.rpow_mul hX0.le]; norm_num
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨p,hp,hlo,hu,le_trans ?_ (hrow p hwin)⟩
  calc t^12/(80*Real.log X) = ((X:ℝ)/(20*Real.log X))*(1/(4*t^4)) := by
         field_simp [ht0.ne',hXL.ne']
         rw [←h16]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hp0 hu) (by positivity)

/-- On every large octave the disjoint branches from the fourth-root band
together carry positive signed mass of prime order. -/
theorem eventually_prime_order_signed_branches :
    ∀ᶠ X : ℕ in atTop,
      let t := (X:ℝ)^(1/16:ℝ)
      (X:ℝ)/(200*Real.log X) ≤
        ∑ p ∈ windowPrimes (2*t^4) (t^5),
          ∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ) := by
  have lim : Tendsto (fun X : ℕ => (X:ℝ)^(1/16:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_prime_band_branches,lim.eventually eventually_deficient_band_reciprocal,
    eventually_ge_atTop 2] with X hrow hsum hX
  let t := (X:ℝ)^(1/16:ℝ)
  let W := windowPrimes (2*t^4) (t^5)
  have hXL := Real.log_pos (by exact_mod_cast (by omega : 1 < X) : (1:ℝ) < X)
  change (X:ℝ)/(200*Real.log X) ≤ ∑ p ∈ W, _
  calc _ = ((X:ℝ)/(20*Real.log X))*(1/10) := by ring
       _ ≤ ((X:ℝ)/(20*Real.log X))*∑ p ∈ W,1/(p:ℝ) := mul_le_mul_of_nonneg_left hsum (by positivity)
       _ ≤ _ := by rw [mul_sum]; exact sum_le_sum hrow

/-- Positive signed mass in a region must either survive there or leave it
along a matching edge. Internal targets can absorb at most the negative
population of the region. -/
theorem signed_mass_le_unmatched_add_exports {R : ℕ → ℕ → Prop} {S V : Finset ℕ}
    (hV : V ⊆ S) (M : OppositeParityMatching R S) :
    (∑ n ∈ V, μ n) ≤ ((M.unmatchedSet ∩ V).card:ℤ) +
      (M.sources.filter (fun n => n ∈ V ∧ M.partner n ∉ V)).card := by
  let P := posParity V
  let T := P ∩ M.sources
  let I := T.filter (fun n => M.partner n ∈ V)
  have hfree : P \ M.sources ⊆ M.unmatchedSet ∩ V := by
    intro n hn
    obtain ⟨hp,hs⟩ := mem_sdiff.mp hn
    obtain ⟨hv,hμ⟩ := mem_filter.mp hp
    have hsP : n ∈ posParity S := mem_filter.mpr ⟨hV hv,hμ⟩
    apply mem_inter.mpr
    refine ⟨mem_sdiff.mpr ⟨?_,?_⟩,hv⟩
    · rw [squarefreeOf_eq_posParity_union_negParity]
      exact mem_union_left _ hsP
    · intro hm
      rcases mem_union.mp hm with h | h
      · exact hs h
      · exact disjoint_left.mp (disjoint_posParity_negParity S) hsP (M.targets_subset h)
  have hI : I ⊆ M.sources := (filter_subset _ _).trans inter_subset_right
  have him : I.image M.partner ⊆ negParity V := by
    intro n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    exact mem_filter.mpr ⟨(mem_filter.mp hx).2,(mem_filter.mp (M.partner_mem _ (hI hx))).2⟩
  have hi := card_le_card him
  rw [card_image_of_injOn (M.injOn.mono (coe_subset.mpr hI))] at hi
  have ho : T.filter (fun n => M.partner n ∉ V) ⊆ M.sources.filter (fun n => n ∈ V ∧ M.partner n ∉ V) := by
    intro n hn
    obtain ⟨ht,hout⟩ := mem_filter.mp hn
    obtain ⟨hp,hm⟩ := mem_inter.mp ht
    exact mem_filter.mpr ⟨hm,(mem_filter.mp hp).1,hout⟩
  have hf := card_le_card hfree
  have hc := card_le_card ho
  have hT : I.card + (T.filter (fun n => M.partner n ∉ V)).card = T.card :=
    card_filter_add_card_filter_not (s := T) (fun n => M.partner n ∈ V)
  have hP : T.card + (P \ M.sources).card = P.card := card_inter_add_card_sdiff P M.sources
  rw [sum_moebius_eq_card_pos_sub_neg]
  change (P.card:ℤ) - (negParity V).card ≤ _
  omega

/-- The disjoint least-prime branches which carry the forced positive flux. -/
def fourthRootBranches (X : ℕ) : Finset ℕ :=
  let t := (X:ℝ)^(1/16:ℝ)
  (roughTails X (2*X) 0).filter (fun n => n.minFac ∈ windowPrimes (2*t^4) (t^5))

/-- On every large octave a prime-order number of vertices must remain
unmatched in these branches or cross their least-prime boundary. The
constraint applies to every edge relation, including unrestricted pairing. -/
theorem eventually_forced_least_prime_flux :
    ∀ᶠ X : ℕ in atTop, ∀ {R : ℕ → ℕ → Prop} (M : OppositeParityMatching R (Ioc X (2*X))),
      (X:ℝ)/(200*Real.log X) ≤ ((M.unmatchedSet ∩ fourthRootBranches X).card:ℝ) +
        (M.sources.filter (fun n => n ∈ fourthRootBranches X ∧ M.partner n ∉ fourthRootBranches X)).card := by
  filter_upwards [eventually_prime_order_signed_branches] with X hx
  intro R M
  let t := (X:ℝ)^(1/16:ℝ)
  let W := windowPrimes (2*t^4) (t^5)
  let V := fourthRootBranches X
  have maps : ∀ n ∈ V, n.minFac ∈ W := fun _ hn => (mem_filter.mp hn).2
  have he (p : ℕ) (hp : p ∈ W) : V.filter (fun n => n.minFac=p) =
      (roughTails X (2*X) 0).filter (fun n => n.minFac=p) := by
    ext n
    change (n ∈ ((roughTails X (2*X) 0).filter (fun n => n.minFac ∈ W)).filter
      (fun n => n.minFac=p)) ↔ _
    simp only [mem_filter]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,by rw [h.2]; exact hp⟩,h.2⟩⟩
  have hsum : (∑ p ∈ W, ∑ n ∈ (roughTails X (2*X) 0).filter (fun n => n.minFac=p), (μ n:ℝ)) =
      ∑ n ∈ V, (μ n:ℝ) := by
    rw [←sum_fiberwise_of_maps_to maps (fun n => (μ n:ℝ))]
    exact sum_congr rfl (fun p hp => by rw [he p hp])
  have hV : V ⊆ Ioc X (2*X) := by
    intro n hn
    obtain ⟨_,hL,hU,_,_⟩ := mem_roughTails.mp (mem_filter.mp hn).1
    exact mem_Ioc.mpr ⟨hL,hU⟩
  change (X:ℝ)/(200*Real.log X) ≤ ∑ p ∈ W, _ at hx
  rw [hsum] at hx
  exact hx.trans (by exact_mod_cast signed_mass_le_unmatched_add_exports hV M)

#print axioms eventually_cube_root_signed_surplus
#print axioms eventually_large_single_prime_branch
#print axioms eventually_prime_order_signed_branches
#print axioms eventually_forced_least_prime_flux

end GaloisForLFunctions.RestrictedFactorizationCalculus
