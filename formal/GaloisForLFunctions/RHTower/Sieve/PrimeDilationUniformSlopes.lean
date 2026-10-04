import GaloisForLFunctions.RHTower.Sieve.PrimeDilationFullSieve
import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic

/-!
# Prime dilation density uniform over all coprime slopes

The full source sieve retains its anchor, finite remainder and all slope primes.
Distinct-prime divisibility bounds the inverse singular correction by the fourth
root of the full discriminant abs(v)*a*b. The resulting constant and threshold
are independent of slopes and shifts. This supplies the arithmetic density input
for rational cubic neighborhoods, including growing slopes; analytic uniformity
in growing moduli and full signed cubic cancellation remain separate open problems.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace RHTower.Sieve

private theorem dilation_singular_inverse_quarter {d h:ℕ} (hd:0<d) :
    (∏ p ∈ (rangePrimes 3 h).filter (fun p => p∣d), (((p:ℝ)-1)/p))⁻¹ ≤
      (d:ℝ)^((1:ℝ)/4) := by
  let S := (rangePrimes 3 h).filter (fun p => p∣d)
  have hdata (p:ℕ) (hp:p∈S) : p.Prime ∧ 5≤p ∧ p∣d := by
    obtain ⟨hr,hdv⟩ := Finset.mem_filter.mp hp
    have hpp := rangePrimes_prime hr
    have hp4 : 4≤p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    have hp5 : 5≤p := by
      by_contra hn
      have he:p=4 := by omega
      subst p
      norm_num at hpp
    exact ⟨hpp,hp5,hdv⟩
  have hsub : S⊆d.primeFactors := fun p hp =>
    (hdata p hp).1.mem_primeFactors (hdata p hp).2.2 hd.ne'
  have hprod_dvd : (∏ p∈S,p)∣d :=
    (Finset.prod_dvd_prod_of_subset S d.primeFactors id hsub).trans d.prod_primeFactors_dvd
  have hprod_le : (∏ p∈S,(p:ℝ))≤d := by
    have hc : ((∏ p∈S,p:ℕ):ℝ)≤(d:ℝ) := Nat.cast_le.mpr (Nat.le_of_dvd hd hprod_dvd)
    simpa only [Nat.cast_prod] using hc
  have hlocal (p:ℕ) (hp:p∈S) : ((p:ℝ)/((p:ℝ)-1))^4≤p := by
    have hp5 : (5:ℝ)≤p := by exact_mod_cast (hdata p hp).2.1
    have hp0 : (0:ℝ)<p := by linarith
    have hm : (0:ℝ)<p-1 := by linarith
    have hpoly : (p:ℝ)^3≤((p:ℝ)-1)^4 := by
      have hp5n : (0:ℝ)≤p-5 := by linarith
      have hp3n : (0:ℝ)≤3*(p:ℝ)-2 := by linarith
      have hh : 0≤(p:ℝ)^3*((p:ℝ)-5)+2*(p:ℝ)*(3*(p:ℝ)-2)+1 := by positivity
      nlinarith only [hh]
    rw [div_pow]
    apply (div_le_iff₀ (pow_pos hm 4)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hpoly hp0.le]
  have hnonneg : 0≤∏ p∈S,(p:ℝ)/((p:ℝ)-1) := by
    apply Finset.prod_nonneg
    intro p hp
    have hp5 : (5:ℝ)≤p := by exact_mod_cast (hdata p hp).2.1
    exact div_nonneg (Nat.cast_nonneg p) (by linarith)
  have hfour : (∏ p∈S,(p:ℝ)/((p:ℝ)-1))^4≤d := by
    rw [← Finset.prod_pow]
    exact (Finset.prod_le_prod (fun p hp => pow_nonneg (by
      have hp5 : (5:ℝ)≤p := by exact_mod_cast (hdata p hp).2.1
      exact div_nonneg (Nat.cast_nonneg p) (by linarith)) 4) hlocal).trans hprod_le
  have hroot := Real.rpow_le_rpow (pow_nonneg hnonneg 4) hfour (by norm_num : (0:ℝ)≤1/4)
  rw [← Real.rpow_natCast,← Real.rpow_mul hnonneg] at hroot
  norm_num at hroot
  simpa only [S,← Finset.prod_inv_distrib,inv_div,Finset.prod_div_distrib] using hroot

private theorem uniform_dilation_sieve {N:ℕ} (hN2:2≤N)
    (hbig:markerLogBase≤Real.log (N:ℝ)) {a b:ℕ} (ha:0<a) (hb:0<b)
    (hcop:a.Coprime b) (v:ℤ) (hv:v≠0) :
    ((primeDilationPairs (2*N) (2*N) a b (sieveSift N) v).card:ℝ) ≤
      1+(4*(288*Real.log 3)^2*Real.exp (2*mertensGapConst))*(N:ℝ)*
        ((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2+2*(N:ℝ)^((3:ℝ)/4) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have hc1 := mertensFirstConst_nonneg
  have hN1 : 1 ≤ N := by omega
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hN0 : (0 : ℝ) < (N : ℝ) := by linarith
  rw [markerLogBase] at hbig
  have hb288 : 288 * Real.log 2 ≤ Real.log (N : ℝ) := by linarith
  have hb144 : 144 * Real.log 3 ≤ Real.log (N : ℝ) := by linarith
  have hlogN : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  have hs3 : 3 ≤ sieveSift N := three_le_sieveSift hb144 hN1
  have hs2 : 2 ≤ sieveSift N := by omega
  have hsift := log_sieveSift_ge hN2 hb288 hs2
  have hlog20 : 20 * mertensFirstConst ≤ Real.log (sieveSift N) := by linarith
  have hsY3 : (3 : ℕ) ≤ sieveSift N := hs3
  have hsav := sieve_saving_ge hsY3
  have hlogY0 : (0 : ℝ) < Real.log (sieveSift N) := by linarith
  have hlow : Real.log (N : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)
      ≤ Real.exp (mertensS (sieveSift N) - mertensS 3) := by
    refine le_trans ?_ hsav
    have hstep : Real.log (N : ℝ) / (288 * Real.log 3)
        ≤ Real.log (sieveSift N) / Real.log 3 := by
      rw [div_le_div_iff₀ (by positivity) hlog3]
      nlinarith [hsift, hlog3]
    have hexp0 : (0 : ℝ) < Real.exp (-mertensGapConst) := Real.exp_pos _
    exact mul_le_mul_of_nonneg_right hstep hexp0.le
  have hpos : (0 : ℝ) < Real.log (N : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst) := by
    have := Real.exp_pos (-mertensGapConst); positivity
  have hsq : (Real.log (N : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)) ^ 2
      ≤ (Real.exp (mertensS (sieveSift N) - mertensS 3)) ^ 2 := by
    exact pow_le_pow_left₀ hpos.le hlow 2
  have hden0 : (0 : ℝ)
      < (Real.log (N : ℝ) / (288 * Real.log 3) * Real.exp (-mertensGapConst)) ^ 2 := by
    positivity

  let S : ℝ := ∏ p ∈ (rangePrimes 3 (sieveSift N)).filter (fun p => p∣v.natAbs*a*b),
    (((p:ℝ)-1)/p)
  have hS : 0<S := by
    apply Finset.prod_pos
    intro p hp
    have hp1 : (1:ℝ)<p := by
      exact_mod_cast (rangePrimes_prime (Finset.mem_filter.mp hp).1).one_lt
    exact div_pos (by linarith) (by linarith)
  have hvabs : 0<v.natAbs := Int.natAbs_pos.mpr hv
  have hquarter := dilation_singular_inverse_quarter (h:=sieveSift N) (mul_pos (mul_pos hvabs ha) hb)
  push_cast at hquarter
  change S⁻¹≤((v.natAbs:ℝ)*a*b)^((1:ℝ)/4) at hquarter
  have hfull := card_primeDilationPairs_full_mertens_le (2*N) (2*N)
    (P₁:=3) (by norm_num) ha hb hcop v (one_le_sieveLevel hN1) hs2 hs3
    (sieveSift_pow_le hN1) hlog20
  have hnum : (((2*N)/b:ℕ):ℝ)≤2*(N:ℝ) := by exact_mod_cast Nat.div_le_self (2*N) b
  have hmain : (((2*N)/b:ℕ):ℝ)/((1/2)*(Real.exp (mertensS (sieveSift N)-mertensS 3)^2*S)) ≤
      (4*(288*Real.log 3)^2*Real.exp (2*mertensGapConst))*(N:ℝ)*
        ((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := by
    have hepos : 0<Real.exp (mertensS (sieveSift N)-mertensS 3)^2 := by positivity
    calc
      _ = (2*((((2*N)/b:ℕ):ℝ))/Real.exp (mertensS (sieveSift N)-mertensS 3)^2)*S⁻¹ := by ring
      _ ≤ (4*(N:ℝ)/Real.exp (mertensS (sieveSift N)-mertensS 3)^2)*
          ((v.natAbs:ℝ)*a*b)^((1:ℝ)/4) := by
        apply mul_le_mul _ hquarter (inv_nonneg.mpr hS.le) (by positivity)
        exact div_le_div_of_nonneg_right (by linarith) hepos.le
      _ ≤ (4*(N:ℝ)/(Real.log (N:ℝ)/(288*Real.log 3)*Real.exp (-mertensGapConst))^2)*
          ((v.natAbs:ℝ)*a*b)^((1:ℝ)/4) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact div_le_div_of_nonneg_left (by positivity) hden0 hsq
      _ = _ := by
        have hexpsq : Real.exp (-mertensGapConst)^2 = 1/Real.exp (2*mertensGapConst) := by
          rw [←Real.exp_nat_mul,show ((2:ℕ):ℝ)*(-mertensGapConst)=-(2*mertensGapConst) by push_cast;ring,
            Real.exp_neg,one_div]
        rw [mul_pow,div_pow,hexpsq]
        field_simp
  have hrem := sieve_remainder_le (P₁:=3) (h:=sieveSift N) (by norm_num)
    (one_le_sieveLevel hN1)
  have hrem' : (∑ e ∈ (rangePrimorial 3 (sieveSift N)).divisors,
      if (e:ℝ) ≤ sieveLevel N then (6:ℝ)^e.primeFactors.card else 0) ≤ 2*(N:ℝ)^((3:ℝ)/4) := by
    have hle : (∑ e ∈ (rangePrimorial 3 (sieveSift N)).divisors,
        if (e:ℝ) ≤ sieveLevel N then (6:ℝ)^e.primeFactors.card else 0) ≤
        ∑ e ∈ (rangePrimorial 3 (sieveSift N)).divisors,
        if (e:ℝ) ≤ sieveLevel N then 2*(6:ℝ)^e.primeFactors.card else 0 := by
      apply Finset.sum_le_sum
      intro e he
      split_ifs <;> nlinarith [pow_nonneg (show (0:ℝ)≤6 by norm_num) e.primeFactors.card]
    have hlev : sieveLevel N^3=(N:ℝ)^((3:ℝ)/4) := by
      rw [←Real.rpow_natCast (sieveLevel N) 3,sieveLevel,←Real.rpow_mul hN0.le]
      norm_num
    exact (hle.trans hrem).trans_eq (by rw [hlev])
  exact hfull.trans (add_le_add (add_le_add le_rfl hmain) hrem')

/-- One source-constructed density bound and threshold for all positive coprime
slopes and nonzero shifts. The entire slope-dependent singular factor survives;
no prime-distribution premise or fixed-slope threshold is imposed. -/
theorem exists_primeDilationPairs_uniform_slopes_bound :
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℕ in atTop, ∀ a b:ℕ,0<a → 0<b → a.Coprime b →
      ∀ v:ℤ,v≠0 →
      ((primeDilationPairs (2*N) (2*N) a b (sieveSift N) v).card:ℝ) ≤
        C*(N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := by
  have ht : Tendsto (fun N:ℕ => (Real.log (N:ℝ))^2/(N:ℝ)^((1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1/4 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  let A:ℝ:=4*(288*Real.log 3)^2*Real.exp (2*mertensGapConst)
  have hA : 0<A := by dsimp [A];positivity
  refine ⟨A+3,by positivity,?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hlog.eventually_ge_atTop markerLogBase,eventually_ge_atTop (2:ℕ)] with N htN hbig hN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : (Real.log (N:ℝ))^2≤(N:ℝ)^((1:ℝ)/4) :=
    (div_le_one (Real.rpow_pos_of_pos hN0 _)).mp htN.le
  have herr : (N:ℝ)^((3:ℝ)/4)≤(N:ℝ)/(Real.log (N:ℝ))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ (N:ℝ)^((3:ℝ)/4)*(N:ℝ)^((1:ℝ)/4) := by gcongr
      _ = N := by rw [← Real.rpow_add hN0];norm_num
  have hpow1 : 1≤(N:ℝ)^((3:ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
  intro a b ha hb hcop v hv
  have hv1 : (1:ℝ)≤v.natAbs := by exact_mod_cast (Int.natAbs_pos.mpr hv)
  have hD : (1:ℝ)≤(v.natAbs:ℝ)*a*b := by
    have ha1 : (1:ℝ)≤a := by exact_mod_cast ha
    have hb1 : (1:ℝ)≤b := by exact_mod_cast hb
    calc
      (1:ℝ) = 1*1*1 := by ring
      _ ≤ (v.natAbs:ℝ)*a*b := mul_le_mul
        (mul_le_mul hv1 ha1 (by norm_num) (by positivity)) hb1 (by norm_num) (by positivity)
  have hq1 : 1≤((v.natAbs:ℝ)*a*b)^((1:ℝ)/4) := Real.one_le_rpow hD (by norm_num)
  have hq0 : 0≤((v.natAbs:ℝ)*a*b)^((1:ℝ)/4) := by positivity
  have hbase := uniform_dilation_sieve hN hbig ha hb hcop v hv
  change _≤1+A*(N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2+
    2*(N:ℝ)^((3:ℝ)/4) at hbase
  refine hbase.trans ?_
  have h1 : 1≤(N:ℝ)/(Real.log (N:ℝ))^2 := hpow1.trans herr
  have hh : (N:ℝ)/(Real.log (N:ℝ))^2≤
      (N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    nlinarith
  calc
    _ ≤ (N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2+
        A*(N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2+
        2*((N:ℝ)*((v.natAbs:ℝ)*a*b)^((1:ℝ)/4)/(Real.log (N:ℝ))^2) :=
      add_le_add (add_le_add (h1.trans hh) le_rfl)
        (mul_le_mul_of_nonneg_left (herr.trans hh) (by norm_num))
    _ = _ := by ring

end RHTower.Sieve
