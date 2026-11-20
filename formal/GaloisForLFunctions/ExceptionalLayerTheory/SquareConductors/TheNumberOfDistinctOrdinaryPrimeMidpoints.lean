import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheExactFibersOfThePrimeMidpoint
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CountingSimultaneousPrimesAtTwoEndpoints
import GaloisForLFunctions.RHTower.MobiusPrimeApertureDifferentialOrder

/-!
# The number of distinct ordinary-prime midpoint values

The three moving endpoints cross primes with total multiplicity
π(2N) + π(3N) + π(4N). Counting distinct prices counts each occupied
crossing time once. Simultaneous crossings cost O(N / log² N) by the
two-affine-form sieve. The leading constant for distinct prices is nine.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private def slope (i : Fin 5) : ℕ := ![2,3,3,4,4] i
private def shift (i : Fin 5) : ℕ := ![1,1,2,1,3] i
private def primeAt (i : Fin 5) (n : ℕ) : Prop := (slope i*n + shift i).Prime
private abbrev Pair := {p : Fin 5 × Fin 5 // p.1 < p.2}
private def bothPrime (q : Pair) (n : ℕ) : Prop := primeAt q.val.1 n ∧ primeAt q.val.2 n
private def primeIndicator (k : ℕ) : ℕ := if k.Prime then 1 else 0

private theorem sum_indicator_nat {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p] :
    (∑ i ∈ s, if p i then 1 else 0 : ℕ) = (s.filter p).card := by
  simpa only [Nat.cast_id] using (Finset.sum_boole (R := ℕ) p s)

private theorem prime_count_add_site (k : ℕ) :
    Nat.primeCounting (k+1) = Nat.primeCounting k + (if (k+1).Prime then 1 else 0) := by
  rw [←Nat.primesLE_card_eq_primeCounting,←Nat.primesLE_card_eq_primeCounting,Nat.primesLE_succ]
  split_ifs
  · exact card_insert_of_notMem (Nat.notMem_primesLE _)
  · simp

private theorem not_prime_multiple {p k : ℕ} (hp : 1 < p) (hk : p < k) (hd : p ∣ k) :
    ¬ k.Prime := fun h => hk.ne' ((h.dvd_iff_eq hp.ne').mp hd)

open Classical in
private theorem endpoint_clock_step {n : ℕ} (hn : 0 < n) :
    primeMidpointClock (n+1) - primeMidpointClock n = (univ.filter (fun i => primeAt i n)).card := by
  classical
  have h₂ := prime_count_add_site (2*n)
  have h₂' := prime_count_add_site (2*n+1)
  have h₃ := prime_count_add_site (3*n)
  have h₃' := prime_count_add_site (3*n+1)
  have h₃'' := prime_count_add_site (3*n+2)
  have h₄ := prime_count_add_site (4*n)
  have h₄' := prime_count_add_site (4*n+1)
  have h₄'' := prime_count_add_site (4*n+2)
  have h₄''' := prime_count_add_site (4*n+3)
  have z₂ := not_prime_multiple (p:=2) (k:=2*n+2) (by decide) (by omega) (by omega)
  have z₃ := not_prime_multiple (p:=3) (k:=3*n+3) (by decide) (by omega) (by omega)
  have z₄ := not_prime_multiple (p:=2) (k:=4*n+2) (by decide) (by omega) (by omega)
  have z₄' := not_prime_multiple (p:=2) (k:=4*n+4) (by decide) (by omega) (by omega)
  have ind (i : Fin 5) : (if primeAt i n then 1 else 0 : ℕ) = primeIndicator (slope i*n+shift i) := by
    by_cases hp : (slope i*n+shift i).Prime <;> simp [primeIndicator,primeAt,hp]
  rw [←sum_indicator_nat univ (fun i => primeAt i n)]
  simp only [ind,Fin.sum_univ_succ,Finset.univ_unique,Finset.sum_singleton,
    Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  change primeMidpointClock (n+1) - primeMidpointClock n =
    primeIndicator (2*n+1) + (primeIndicator (3*n+1) + (primeIndicator (3*n+2) +
    (primeIndicator (4*n+1) + primeIndicator (4*n+3))))
  simp only [primeMidpointClock,primeIndicator,Nat.mul_add,Nat.mul_one]
  simp only [Nat.add_assoc,Nat.reduceAdd,if_neg z₂,if_neg z₃,if_neg z₄,if_neg z₄'] at *
  omega

open Classical in
/-- Number of distinct signed prices through the integer center N, including zero. -/
def distinctPrimeMidpointCount (N : ℕ) := ((range (N+1)).image primeMidpointPrice).card

private theorem distinct_as_occupied (N : ℕ) :
    distinctPrimeMidpointCount N =
      1 + ∑ n ∈ range N, (if primeMidpointClock n < primeMidpointClock (n+1) then 1 else 0) := by
  rw [distinctPrimeMidpointCount,number_of_distinct_midpoint_readings,sum_indicator_nat]

open Classical in
private def doubleHits (N : ℕ) := (Icc 1 N).filter (fun n => ∃ q : Pair, bothPrime q n)

/-- The excess of the clock over the number of new prices is supported
on simultaneous hits, apart from the initial crossing. -/
private theorem missed_crossings (N : ℕ) :
    distinctPrimeMidpointCount N ≤ 1 + primeMidpointClock N ∧
    primeMidpointClock N ≤ distinctPrimeMidpointCount N + primeMidpointClock 1 + 5*(doubleHits N).card := by
  classical
  let c := primeMidpointClock
  let v := fun n => if c n < c (n+1) then 1 else 0
  have hv (n : ℕ) : v n ≤ c (n+1)-c n := by dsimp only [v]; split <;> omega
  have ht : ∑ n ∈ range N, (c (n+1)-c n) = c N := by
    induction N with
    | zero => simp [c,primeMidpointClock]
    | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      have hm : c N ≤ c (N+1) := monotone_prime_midpoint_clock (Nat.le_succ N)
      omega
  have hupper := sum_le_sum (s:=range N) fun n _ => hv n
  have hlocal (n : ℕ) :
      c (n+1)-c n ≤ v n + (if n=0 then c 1 else 0) +
        5*(if 0<n ∧ ∃ q : Pair, bothPrime q n then 1 else 0) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp <;> omega
    have he := endpoint_clock_step hn
    let S := univ.filter (fun i => primeAt i n)
    have hsize : S.card ≤ 5 := by
      simpa using card_le_card (filter_subset (fun i => primeAt i n) (univ : Finset (Fin 5)))
    change c (n+1)-c n = S.card at he
    rw [if_neg hn.ne']
    by_cases hpair : ∃ q : Pair, bothPrime q n
    · rw [if_pos ⟨hn,hpair⟩]; omega
    · have hs : S.card ≤ 1 := by
        apply card_le_one.mpr
        intro i hi j hj
        rcases lt_trichotomy i j with hij | hij | hji
        · exact (hpair ⟨⟨(i,j),hij⟩,(mem_filter.mp hi).2,(mem_filter.mp hj).2⟩).elim
        · exact hij
        · exact (hpair ⟨⟨(j,i),hji⟩,(mem_filter.mp hj).2,(mem_filter.mp hi).2⟩).elim
      simp only [hpair,and_false,if_false,mul_zero,add_zero,v]
      split <;> omega
  have hsum := sum_le_sum (s:=range N) fun n _ => hlocal n
  rw [ht,sum_add_distrib,sum_add_distrib,←mul_sum,
    sum_indicator_nat (range N) (fun n => 0<n ∧ ∃ q : Pair, bothPrime q n)] at hsum
  have hfirst : (∑ n ∈ range N, if n=0 then c 1 else 0) ≤ c 1 := by
    rw [sum_ite_eq']; split <;> omega
  have hh : ((range N).filter (fun n => 0<n ∧ ∃ q : Pair, bothPrime q n)).card ≤ (doubleHits N).card := by
    apply card_le_card
    intro n hn
    obtain ⟨hr,hp,hq⟩ := mem_filter.mp hn
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hp,(mem_range.mp hr).le⟩,hq⟩
  have hF : distinctPrimeMidpointCount N = 1 + ∑ n ∈ range N, v n := distinct_as_occupied N
  rw [ht] at hupper
  change distinctPrimeMidpointCount N ≤ 1+c N ∧ c N ≤ distinctPrimeMidpointCount N+c 1+5*(doubleHits N).card
  omega

private theorem double_hit_estimate :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, Real.log N^2 * ((doubleHits N).card:ℝ) ≤ C*N := by
  classical
  have h (q : Pair) : ∃ C : ℝ, 0<C ∧ ∀ᶠ N : ℕ in atTop,
      Real.log N^2 * (((Icc 1 N).filter (bothPrime q)).card:ℝ) ≤ C*N := by
    obtain ⟨⟨i,j⟩,hij⟩ := q
    have pos (r : Fin 5) : 0 < slope r := by fin_cases r <;> decide
    have hne : slope i * shift j ≠ slope j * shift i := by
      fin_cases i <;> fin_cases j <;> first | decide | (exfalso; revert hij; decide)
    obtain ⟨C,hC,hN⟩ := two_affine_prime_endpoints_log_squared (pos i) (pos j) (shift i) (shift j) hne
    refine ⟨C,hC,?_⟩
    filter_upwards [hN] with N hn
    have hs : (Icc 1 N).filter (bothPrime ⟨(i,j),hij⟩) =
        (Icc 1 N).filter (fun n => (slope i*n+shift i).Prime ∧ (slope j*n+shift j).Prime) := by
      ext n
      simp only [mem_filter,bothPrime,primeAt]
    rw [hs]
    exact hn
  choose K hK hK' using h
  refine ⟨∑ q, K q,sum_nonneg (fun q _ => (hK q).le),?_⟩
  filter_upwards [eventually_all.mpr hK'] with N hN
  have hsub : doubleHits N ⊆ univ.biUnion (fun q : Pair => (Icc 1 N).filter (bothPrime q)) := by
    intro n hn
    obtain ⟨hn,⟨q,hq⟩⟩ := mem_filter.mp hn
    exact mem_biUnion.mpr ⟨q,mem_univ _,mem_filter.mpr ⟨hn,hq⟩⟩
  have hcard := (card_le_card hsub).trans (card_biUnion_le)
  have hc := mul_le_mul_of_nonneg_left ((Nat.cast_le (α:=ℝ)).mpr hcard) (sq_nonneg (Real.log N))
  rw [Nat.cast_sum,mul_sum] at hc
  rw [sum_mul]
  exact hc.trans (sum_le_sum fun q _ => hN q)

/-- Counting each occupied crossing once loses at most O(N / log² N)
of the prime-counting clock, including all simultaneous crossings. -/
theorem distinct_midpoint_count_error :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop,
      0 ≤ (primeMidpointClock N:ℝ) + 1 - distinctPrimeMidpointCount N ∧
      Real.log N ^ 2 * ((primeMidpointClock N:ℝ) + 1 - distinctPrimeMidpointCount N) ≤ K*N := by
  obtain ⟨C,hC,h⟩ := double_hit_estimate
  let A : ℝ := primeMidpointClock 1 + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨4*A+5*C,by positivity,?_⟩
  filter_upwards [h] with N hn
  have hu := (Nat.cast_le (α:=ℝ)).mpr (missed_crossings N).1
  have hv := (Nat.cast_le (α:=ℝ)).mpr (missed_crossings N).2
  push_cast at hu hv
  have hlog := Real.log_le_rpow_div (Nat.cast_nonneg N) (by norm_num : (0:ℝ)<1/2)
  rw [←Real.sqrt_eq_rpow] at hlog
  have hsq := pow_le_pow_left₀ (Real.log_natCast_nonneg N) hlog 2
  have hsmall : Real.log N ^ 2 ≤ 4*N := by nlinarith only [hsq,Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) N)]
  have hraw : (primeMidpointClock N:ℝ) + 1 - distinctPrimeMidpointCount N ≤ A + 5*(doubleHits N).card := by
    dsimp only [A]; linarith only [hv]
  have hm := mul_le_mul_of_nonneg_left hraw (sq_nonneg (Real.log N))
  have hk := mul_le_mul_of_nonneg_right hsmall hA
  constructor <;> linarith only [hu,hm,hk,hn]

private theorem dilated_prime_count {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => (Nat.primeCounting (k*N):ℝ)*Real.log N/N) atTop (𝓝 (k:ℝ)) := by
  have hk₀ := (Nat.cast_pos (α:=ℝ)).mpr hk
  have hr := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hlog := Real.tendsto_log_atTop.comp hr
  have hp := _root_.RHTower.tendsto_primeCounting_ratio.comp (hr.const_mul_atTop hk₀)
  have hcor := (tendsto_inv_atTop_zero.comp hlog).const_mul (Real.log k)
  have hden := hcor.add_const 1
  simp only [mul_zero,zero_add] at hden
  have hlim := (hp.mul_const (k:ℝ)).div hden (by norm_num)
  simp only [one_mul,div_one] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1:ℕ)] with N hN
  have hN₁ := (Nat.one_lt_cast (α:=ℝ)).mpr hN
  have hN₀ := zero_lt_one.trans hN₁
  have hl := Real.log_pos hN₁
  have hkl : 0 < Real.log k + Real.log N := add_pos_of_nonneg_of_pos (Real.log_nonneg (Nat.one_le_cast.mpr hk)) hl
  change (Nat.primeCounting ⌊(k:ℝ)*N⌋₊:ℝ)/((k:ℝ)*N/Real.log ((k:ℝ)*N))*k/
    (Real.log k * (Real.log N)⁻¹+1) = _
  rw [←Nat.cast_mul,Nat.floor_natCast,Nat.cast_mul,Real.log_mul hk₀.ne' hN₀.ne']
  field_simp [hk₀.ne',hN₀.ne',hl.ne',hkl.ne']
  <;> ring

/-- The number of distinct midpoint prices observed at integer centers
from zero through N is asymptotic to 9 N / log N. -/
theorem asymptotic_number_of_distinct_prime_midpoints :
    Tendsto (fun N : ℕ => (distinctPrimeMidpointCount N:ℝ)*Real.log N/N) atTop (𝓝 9) := by
  obtain ⟨C,hC,he⟩ := double_hit_estimate
  have hclock : Tendsto (fun N : ℕ => (primeMidpointClock N:ℝ)*Real.log N/N) atTop (𝓝 9) := by
    have h := ((dilated_prime_count (by decide : 0<2)).add (dilated_prime_count (by decide : 0<3))).add
      (dilated_prime_count (by decide : 0<4))
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_add] at h
    convert h using 1
    · ext N; simp only [primeMidpointClock,Nat.cast_add]; ring
  have hr := tendsto_natCast_atTop_atTop (R:=ℝ)
  have hln := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hr
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp hr)
  have herr := (hln.const_mul (primeMidpointClock 1:ℝ)).add (hinv.const_mul (5*C))
  have hup := hclock.add hln
  have hlow := hclock.sub herr
  simp only [mul_zero,add_zero,sub_zero] at hup hlow
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup
  · filter_upwards [he,eventually_gt_atTop (1:ℕ)] with N hh hN
    have hN₁ := (Nat.one_lt_cast (α:=ℝ)).mpr hN
    have hN₀ := zero_lt_one.trans hN₁
    have hl := Real.log_pos hN₁
    have hf := (Nat.cast_le (α:=ℝ)).mpr (missed_crossings N).2
    push_cast at hf
    have hm := mul_le_mul_of_nonneg_right hf (div_nonneg hl.le hN₀.le)
    have hhit : ((doubleHits N).card:ℝ)*(Real.log N / N) ≤ C*(Real.log N)⁻¹ := by
      rw [←div_eq_mul_inv,le_div_iff₀ hl]
      field_simp [hN₀.ne']
      nlinarith only [hh]
    change _ - ((primeMidpointClock 1:ℝ)*(Real.log N/N)+5*C*(Real.log N)⁻¹) ≤ _
    simp only [div_eq_mul_inv] at hm hhit ⊢
    linarith only [hm,hhit]
  · filter_upwards with N
    have hf := (Nat.cast_le (α:=ℝ)).mpr (missed_crossings N).1
    push_cast at hf
    have hm := mul_le_mul_of_nonneg_right hf (div_nonneg (Real.log_natCast_nonneg N) (Nat.cast_nonneg N))
    change _ ≤ (primeMidpointClock N:ℝ)*Real.log N/N + Real.log N/N
    simp only [div_eq_mul_inv] at hm ⊢
    linarith only [hm]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
