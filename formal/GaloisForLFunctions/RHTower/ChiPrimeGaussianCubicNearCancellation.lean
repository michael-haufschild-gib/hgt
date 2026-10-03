import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicRowCancellation
import GaloisForLFunctions.RHTower.Sieve.GenericMarkerAnalytic
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Actual Gaussian prime cubic cancellation without a lower gap cutoff

At the existing exponential conductors, complete every original physical middle-prime
row for all distinct full-band prime pairs with `|p-r| ≤ m^3`. Their total row norm,
normalized by `log(N)^2/N`, tends to zero. Both Jordan parts of this same family diverge.

The source two-prime sieve controls each positive gap fibre, retaining its finite
remainder. The completed-row inverse-square decay then has a harmonic aggregate
with a full extra prime-density saving. This closes the previously excluded small-gap
range, including bounded gaps; no prime-pair asymptotic is assumed.

The large-gap signed cubic, growing mixed moments and BAG self-target recurrence
remain open. Neither the full cubic asymptotic nor RH is asserted.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem near_band_eq (N:ℕ) :
    primeProfileBand (N:ℝ) = Sieve.bigPrimeSet N (2*N) := by
  have he : 2*(N:ℝ)=((2*N:ℕ):ℝ) := by push_cast;rfl
  unfold primeProfileBand Sieve.bigPrimeSet
  rw [he,Nat.floor_natCast,Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_Ioc,Finset.mem_Icc]
  omega

private theorem near_dist_cast (r p:ℕ) : (Nat.dist r p:ℝ)=|(p:ℝ)-r| := by
  rcases le_total r p with h | h
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h,abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h))]
    ring

private theorem near_gap_mem {N:ℝ} {H r p:ℕ} :
    (r,p)∈primeGaussianCubicGapPairs N 0 H ↔
      r∈primeProfileBand N ∧ p∈primeProfileBand N ∧ 1≤Nat.dist r p ∧ Nat.dist r p≤H := by
  have hcast := near_dist_cast r p
  simp only [primeGaussianCubicGapPairs,Finset.mem_biUnion,Finset.mem_image,
    Finset.mem_filter,Prod.mk.injEq]
  constructor
  · rintro ⟨s,hs,q,⟨hq,hl,hu⟩,rfl,rfl⟩
    refine ⟨hs,hq,?_,?_⟩
    · have : (0:ℝ)<Nat.dist s q := by simpa only [near_dist_cast] using hl
      have : 0<Nat.dist s q := by exact_mod_cast this
      omega
    · exact_mod_cast (show (Nat.dist s q:ℝ)≤H by simpa only [near_dist_cast] using hu)
  · rintro ⟨hr,hp,hl,hu⟩
    refine ⟨r,hr,p,⟨hp,?_,?_⟩,rfl,rfl⟩
    · rw [← hcast]
      exact_mod_cast (show 0<Nat.dist r p by omega)
    · rw [← hcast]
      exact_mod_cast hu

private def nearShift (N d:ℕ) : Finset ℕ :=
  (primeProfileBand (N:ℝ)).filter fun p => p+d∈primeProfileBand (N:ℝ)

private theorem near_fibre_card (N H d:ℕ) :
    ((primeGaussianCubicGapPairs (N:ℝ) 0 H).filter
      (fun rp => Nat.dist rp.1 rp.2=d)).card ≤ 2*(nearShift N d).card := by
  let S:=nearShift N d
  have hsub : ((primeGaussianCubicGapPairs (N:ℝ) 0 H).filter
      (fun rp => Nat.dist rp.1 rp.2=d)) ⊆
      (S.image (fun p => (p,p+d))) ∪ (S.image (fun p => (p+d,p))) := by
    rintro ⟨r,p⟩ hrp
    obtain ⟨hg,hd⟩:=Finset.mem_filter.mp hrp
    obtain ⟨hr,hp,_,_⟩:=near_gap_mem.mp hg
    rcases le_total r p with h | h
    · have hpd : r+d=p := by rw [Nat.dist_eq_sub_of_le h] at hd;omega
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨r,Finset.mem_filter.mpr ⟨hr,by simpa only [hpd] using hp⟩,by simp only [hpd]⟩)
    · have hrd : p+d=r := by rw [Nat.dist_eq_sub_of_le_right h] at hd;omega
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p,Finset.mem_filter.mpr ⟨hp,by simpa only [hrd] using hr⟩,by simp only [hrd]⟩)
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (S.image (fun p => (p,p+d))).card+(S.image (fun p => (p+d,p))).card :=
      Finset.card_union_le _ _
    _ ≤ S.card+S.card := add_le_add Finset.card_image_le Finset.card_image_le
    _ = _ := by ring

private theorem near_shift_sieve {N:ℕ} (hN:2≤N)
    (hbig:Sieve.markerLogBase≤Real.log (N:ℝ)) {d:ℕ} (hd:1≤d) :
    ((nearShift N d).card:ℝ) ≤ (d:ℝ)*
      (2*Sieve.pairMainConst*(N:ℝ)/(Real.log (N:ℝ))^2+2*(N:ℝ)^((3:ℝ)/4)) := by
  have hs := Sieve.generic_pair_le' (b:=2*N) (K:=d) hN hbig
  have hsingle := Finset.single_le_sum
    (f:=fun k => (((Sieve.bigPrimeSet N (2*N)).filter
      (fun p => p+k∈Sieve.bigPrimeSet N (2*N))).card:ℝ))
    (fun k _ => Nat.cast_nonneg _) (Finset.mem_Icc.mpr ⟨hd,le_rfl⟩)
  calc
    _ ≤ _ := by simpa only [nearShift,near_band_eq] using hsingle
    _ ≤ _ := hs
    _ = _ := by push_cast;ring

private theorem near_rows_sum {N H:ℕ} (F:ℕ→ℝ)
    (hF:∀ d∈Finset.Icc 1 H,0≤F d)
    (hrow:∀ rp∈primeGaussianCubicGapPairs (N:ℝ) 0 H,
      ‖primeGaussianCubicCompleteRow (N:ℝ) rp.2 rp.1‖≤F (Nat.dist rp.1 rp.2)) :
    primeGaussianCubicGapRowMass (N:ℝ) 0 H ≤
      2*∑ d∈Finset.Icc 1 H,((nearShift N d).card:ℝ)*F d := by
  have hmap (rp:ℕ×ℕ) (hrp:rp∈primeGaussianCubicGapPairs (N:ℝ) 0 H) :
      Nat.dist rp.1 rp.2∈Finset.Icc 1 H := by
    obtain ⟨_,_,hl,hu⟩:=near_gap_mem.mp hrp
    exact Finset.mem_Icc.mpr ⟨hl,hu⟩
  unfold primeGaussianCubicGapRowMass
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  calc
    _ ≤ ∑ d∈Finset.Icc 1 H,
        (((primeGaussianCubicGapPairs (N:ℝ) 0 H).filter
          (fun rp => Nat.dist rp.1 rp.2=d)).card:ℝ)*F d := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        _ ≤ ∑ _rp∈(primeGaussianCubicGapPairs (N:ℝ) 0 H).filter
            (fun rp => Nat.dist rp.1 rp.2=d), F d := by
          apply Finset.sum_le_sum
          intro rp hrp
          obtain ⟨hrp,he⟩:=Finset.mem_filter.mp hrp
          simpa only [he] using hrow rp hrp
        _ = _ := by simp
    _ ≤ ∑ d∈Finset.Icc 1 H, (2*((nearShift N d).card:ℝ))*F d := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast near_fibre_card N H d) (hF d hd)
    _ = _ := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro d hd;ring

private theorem near_shift_bound :
    ∃ B:ℝ,0<B ∧ ∀ᶠ N:ℕ in atTop, ∀ d:ℕ,1≤d →
      ((nearShift N d).card:ℝ) ≤ B*(d:ℝ)*(N:ℝ)/(Real.log (N:ℝ))^2 := by
  have ht : Tendsto (fun N:ℕ => (Real.log (N:ℝ))^2/(N:ℝ)^((1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop (2:ℝ) (show (0:ℝ)<1/4 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  let B:ℝ:=2*Sieve.pairMainConst+2
  refine ⟨B,by dsimp [B];linarith [Sieve.pairMainConst_pos],?_⟩
  filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)),
    hlog.eventually_ge_atTop Sieve.markerLogBase,eventually_ge_atTop (2:ℕ)] with N htN hbig hN
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  have hp : (Real.log (N:ℝ))^2≤(N:ℝ)^((1:ℝ)/4) :=
    (div_le_one (Real.rpow_pos_of_pos hN0 _)).mp htN.le
  have herr : (N:ℝ)^((3:ℝ)/4)≤(N:ℝ)/(Real.log (N:ℝ))^2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    calc
      _ ≤ (N:ℝ)^((3:ℝ)/4)*(N:ℝ)^((1:ℝ)/4) := by gcongr
      _ = N := by rw [← Real.rpow_add hN0];norm_num
  intro d hd
  refine (near_shift_sieve hN hbig hd).trans ?_
  calc
    _ ≤ (d:ℝ)*(2*Sieve.pairMainConst*(N:ℝ)/(Real.log (N:ℝ))^2+
        2*((N:ℝ)/(Real.log (N:ℝ))^2)) := by gcongr
    _ = _ := by dsimp [B];ring

private theorem near_rows_bound :
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℕ in atTop, ∀ H:ℕ,
      (Real.log (N:ℝ))^2/(N:ℝ)*primeGaussianCubicGapRowMass (N:ℝ) 0 H ≤
        C*((1+Real.log (H:ℝ))/Real.log (N:ℝ)+(H:ℝ)^2*
          ((1+H)/(Real.log (N:ℝ))^13+(1+H)/((N:ℝ)*Real.log (N:ℝ))+1/(N:ℝ))) := by
  obtain ⟨B,hB,hshift⟩:=near_shift_bound
  obtain ⟨C,hC,hrow⟩:=exists_primeGaussianCubicCompleteRow_bound
  refine ⟨2*B*C,by positivity,?_⟩
  filter_upwards [hshift,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hrow,
    eventually_ge_atTop (2:ℕ)] with N hs hr hN
  intro H
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let L:=Real.log (N:ℝ)
  let E:ℝ:=(1+H)/L^12+(1+H)/(N:ℝ)
  let F:ℕ→ℝ:=fun d => C/L*(1/(d:ℝ)^2+E)+C/(N:ℝ)
  have hE : 0≤E := by dsimp [E,L];positivity
  have hF (d:ℕ) : 0≤F d := by dsimp [F,L];positivity
  have hrows : primeGaussianCubicGapRowMass (N:ℝ) 0 H ≤
      2*∑ d∈Finset.Icc 1 H,((nearShift N d).card:ℝ)*F d := by
    apply near_rows_sum F (fun d _ => hF d)
    intro rp hp
    obtain ⟨hrr,hpp,hd,hH⟩:=near_gap_mem.mp hp
    have hneq : rp.2≠rp.1 := by intro he;rw [he,Nat.dist_self] at hd;omega
    refine (hr _ hpp _ hrr hneq).trans ?_
    rw [← near_dist_cast]
    have hcast : (Nat.dist rp.1 rp.2:ℝ)≤H := by exact_mod_cast hH
    dsimp [F,E,L]
    simp only [← add_assoc]
    gcongr
  have hsum : (∑ d∈Finset.Icc 1 H,((nearShift N d).card:ℝ)*F d) ≤
      (B*(N:ℝ)/L^2)*(C/L*(1+Real.log (H:ℝ))+(H:ℝ)^2*(C/L*E+C/(N:ℝ))) := by
    calc
      _ ≤ ∑ d∈Finset.Icc 1 H, (B*(N:ℝ)/L^2)*((d:ℝ)*F d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hb:=mul_le_mul_of_nonneg_right (hs d (Finset.mem_Icc.mp hd).1) (hF d)
        calc
          _ ≤ (B*(d:ℝ)*(N:ℝ)/(Real.log (N:ℝ))^2)*F d := hb
          _ = _ := by dsimp [L];ring
      _ = (B*(N:ℝ)/L^2)*∑ d∈Finset.Icc 1 H, (d:ℝ)*F d := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [L];positivity)
        calc
          _ = ∑ d∈Finset.Icc 1 H, ((C/L)*(1/(d:ℝ))+(d:ℝ)*(C/L*E+C/(N:ℝ))) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hd0 : (d:ℝ)≠0 := by exact_mod_cast (show d≠0 by have := (Finset.mem_Icc.mp hd).1;omega)
            dsimp [F]
            field_simp
            ring
          _ ≤ ∑ d∈Finset.Icc 1 H, ((C/L)*(1/(d:ℝ))+(H:ℝ)*(C/L*E+C/(N:ℝ))) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdH : (d:ℝ)≤H := by exact_mod_cast (Finset.mem_Icc.mp hd).2
            gcongr
          _ = C/L*(∑ d∈Finset.Icc 1 H,1/(d:ℝ))+(H:ℝ)^2*(C/L*E+C/(N:ℝ)) := by
            rw [Finset.sum_add_distrib,← Finset.mul_sum]
            simp only [Finset.sum_const,Nat.card_Icc,add_tsub_cancel_right,nsmul_eq_mul]
            ring
          _ ≤ _ := by
            exact add_le_add (mul_le_mul_of_nonneg_left
              (Sieve.sum_Icc_one_div_le_one_add_log H)
              (show 0≤C/L from div_nonneg hC.le hL.le)) le_rfl
  calc
    _ ≤ L^2/(N:ℝ)*(2*((B*(N:ℝ)/L^2)*
        (C/L*(1+Real.log (H:ℝ))+(H:ℝ)^2*(C/L*E+C/(N:ℝ))))) := by
      exact mul_le_mul_of_nonneg_left (hrows.trans (mul_le_mul_of_nonneg_left hsum (by norm_num)))
        (by positivity)
    _ = _ := by dsimp [E,L];field_simp

private theorem near_conductor_eq (m:ℕ) :
    (primeGaussianHyperbolicConductor m:ℝ) = ((10000000:ℝ)^4)^m := by
  change (((10000000:ℕ)^(4*m):ℕ):ℝ)=_
  rw [Nat.cast_pow,pow_mul]
  norm_cast

private theorem near_conductor_log (m:ℕ) :
    Real.log (primeGaussianHyperbolicConductor m:ℝ) = (4*Real.log 10000000)*(m:ℝ) := by
  rw [near_conductor_eq,Real.log_pow,Real.log_pow]
  ring

private theorem near_budget_tendsto :
    Tendsto (fun m:ℕ =>
      (1+Real.log ((m:ℝ)^3))/Real.log (primeGaussianHyperbolicConductor m:ℝ)+(m:ℝ)^6*
        ((1+(m:ℝ)^3)/(Real.log (primeGaussianHyperbolicConductor m:ℝ))^13+
        (1+(m:ℝ)^3)/((primeGaussianHyperbolicConductor m:ℝ)*
          Real.log (primeGaussianHyperbolicConductor m:ℝ))+
        1/(primeGaussianHyperbolicConductor m:ℝ))) atTop (𝓝 0) := by
  let a:ℝ:=4*Real.log 10000000
  have ha : 0<a := by dsimp [a];positivity
  have hinv (k:ℕ) (hk:k≠0) : Tendsto (fun m:ℕ => 1/(m:ℝ)^k) atTop (𝓝 0) :=
    tendsto_const_div_pow 1 k hk
  have hlog : Tendsto (fun m:ℕ => Real.log (m:ℝ)/(m:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp (k:ℕ) : Tendsto (fun m:ℕ => (m:ℝ)^k/(primeGaussianHyperbolicConductor m:ℝ))
      atTop (𝓝 0) := by
    simpa only [near_conductor_eq] using
      tendsto_pow_const_div_const_pow_of_one_lt k
        (show (1:ℝ)<(10000000:ℝ)^4 from one_lt_pow₀ (by norm_num) (by norm_num))
  have ht:=((((hinv 1 (by norm_num)).add (hlog.const_mul 3)).const_mul (1/a)).add
      (((hinv 7 (by norm_num)).add (hinv 4 (by norm_num))).const_mul (1/a^13)))
      |>.add (((hp 5).add (hp 8)).const_mul (1/a)) |>.add (hp 6)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN0 : (0:ℝ)<primeGaussianHyperbolicConductor m := by rw [near_conductor_eq];positivity
  rw [near_conductor_log,Real.log_pow]
  change _=(1+(3:ℝ)*Real.log (m:ℝ))/(a*(m:ℝ))+(m:ℝ)^6*
    ((1+(m:ℝ)^3)/(a*(m:ℝ))^13+(1+(m:ℝ)^3)/
      ((primeGaussianHyperbolicConductor m:ℝ)*(a*(m:ℝ)))+1/(primeGaussianHyperbolicConductor m:ℝ))
  field_simp [ha.ne',hm0.ne',hN0.ne']
  ring

/-- Every complete actual physical q-row with `0 < |p-r| ≤ m^3` is negligible
in total row norm at the cubic scale. In particular, the lower prime-gap cutoff
is removed without a prime-pair asymptotic or any cancellation hypothesis. -/
theorem tendsto_primeGaussianCubicNearRowMass :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicGapRowMass (primeGaussianHyperbolicConductor m) 0 (m^3))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩:=near_rows_bound
  obtain ⟨N₀,hN₀⟩:=eventually_atTop.mp hbound
  have ht:=near_budget_tendsto.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_gt_atTop 0] with m hm
    exact mul_nonneg (div_nonneg (sq_nonneg _) hm.le)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_ge_atTop (N₀:ℝ)] with m hm
    have hNm : N₀≤primeGaussianHyperbolicConductor m := by exact_mod_cast hm
    have hb:=hN₀ _ hNm (m^3)
    push_cast at hb
    simpa only [← pow_mul] using hb

/-- Both Jordan parts still diverge on the entire noncontracting near family,
although the normalized sum of complete-row norms tends to zero. -/
theorem tendsto_primeGaussianCubicNearSignedVariation (negative:Bool) :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicGapSignedVariation negative (primeGaussianHyperbolicConductor m) 0 (m^3))
      atTop atTop := by
  apply tendsto_atTop_mono _ (tendsto_primeGaussianCubicGapSignedVariation negative)
  intro m
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rp hrp
    obtain ⟨r,hr,himage⟩:=Finset.mem_biUnion.mp hrp
    obtain ⟨p,hp,he⟩:=Finset.mem_image.mp himage
    obtain ⟨hp,hlo,hhi⟩:=Finset.mem_filter.mp hp
    apply Finset.mem_biUnion.mpr
    refine ⟨r,hr,Finset.mem_image.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,?_,hhi⟩,he⟩⟩
    exact lt_of_le_of_lt (by positivity) hlo
  · intro rp _ _
    apply Finset.sum_nonneg
    intro q hq
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _

end RHTower
