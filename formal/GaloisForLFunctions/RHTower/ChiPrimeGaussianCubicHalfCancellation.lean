import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicHalfResonance
import GaloisForLFunctions.RHTower.Sieve.PrimeDilationThreeHalves
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Actual large-gap Gaussian cubic resonance cancellation

At the existing exponential conductors, retain every original-band outer prime
pair with `|2*p-3*r| ≤ m^3` and complete every physical middle-prime row except
its exact contraction. The normalized sum of row norms tends to zero.

The physical profile has a nonzero lower endpoint, retained by the source
inverse-first-power row bound. Exact signed dilation fibres and their complete
source sieve provide two prime-density savings with fourth-root shift cost.
The finite sieve remainder, moving window and both physical kernel errors remain.

This closes one genuine macroscopic-gap resonance. The full joint signed
large-gap discrepancy, growing moments and positive BAG self-target recurrence
remain open. Neither a lower affine-prime count nor RH is asserted.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

/-- All original-band outer prime pairs in the three-halves resonance. -/
def primeGaussianCubicHalfResonancePairs (N:ℝ) (H:ℕ) : Finset (ℕ×ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter
    (fun pr => Nat.dist (2*pr.1) (3*pr.2)≤H)

/-- Sum of norms of complete physical middle-prime rows in this resonance. -/
def primeGaussianCubicHalfResonanceRowMass (N:ℝ) (H:ℕ) : ℝ :=
  ∑ pr∈primeGaussianCubicHalfResonancePairs N H, ‖primeGaussianCubicCompleteRow N pr.1 pr.2‖

private theorem half_dist_cast (p r:ℕ) :
    (Nat.dist (2*p) (3*r):ℝ)=|2*(p:ℝ)-3*r| := by
  rcases le_total (3*r) (2*p) with h | h
  · rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h]
    have hh : (3:ℝ)*r≤2*(p:ℝ) := by exact_mod_cast h
    push_cast
    rw [abs_of_nonneg (sub_nonneg.mpr hh)]
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h]
    have hh : 2*(p:ℝ)≤3*r := by exact_mod_cast h
    push_cast
    rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    ring

private theorem half_pair_mem {N:ℝ} {H p r:ℕ} :
    (p,r)∈primeGaussianCubicHalfResonancePairs N H ↔
      p∈primeProfileBand N ∧ r∈primeProfileBand N ∧ Nat.dist (2*p) (3*r)≤H := by
  simp only [primeGaussianCubicHalfResonancePairs,Finset.mem_filter]
  constructor
  · rintro ⟨hpr,hd⟩
    obtain ⟨hp,hr⟩:=Finset.mem_product.mp hpr
    exact ⟨hp,hr,hd⟩
  · rintro ⟨hp,hr,hd⟩
    exact ⟨Finset.mem_product.mpr ⟨hp,hr⟩,hd⟩

private theorem half_dist_pos {N:ℝ} (hN:2<N) {p r:ℕ}
    (hr:r∈primeProfileBand N) : 1≤Nat.dist (2*p) (3*r) := by
  have hN0 : 0≤N := by linarith
  obtain ⟨hrP,hrN,_⟩ := primeProfileBand_mem hN0 hr
  have hr2 : r≠2 := by intro he;subst r;norm_num at hrN;linarith
  obtain ⟨j,hj⟩:=hrP.odd_of_ne_two hr2
  rcases le_total (2*p) (3*r) with h | h
  · rw [Nat.dist_eq_sub_of_le h];omega
  · rw [Nat.dist_eq_sub_of_le_right h];omega

private theorem half_fibre_card {N H d:ℕ} (hN:2≤N) :
    ((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
      (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)).card ≤
      (Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (d:ℤ)).card+
      (Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (-(d:ℤ))).card := by
  have hsift := Sieve.sieveSift_le (show 1≤N by omega)
  have hsub : ((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
      (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)) ⊆
      Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (d:ℤ) ∪
      Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (-(d:ℤ)) := by
    rintro ⟨p,r⟩ hpr
    obtain ⟨hpair,hd⟩:=Finset.mem_filter.mp hpr
    obtain ⟨hp,hr,_⟩:=half_pair_mem.mp hpair
    obtain ⟨hpP,hpN,hp2⟩:=primeProfileBand_mem (show (0:ℝ)≤N by positivity) hp
    obtain ⟨hrP,hrN,hr2⟩:=primeProfileBand_mem (show (0:ℝ)≤N by positivity) hr
    have hpN' : N<p := by exact_mod_cast hpN
    have hrN' : N<r := by exact_mod_cast hrN
    have hp2' : p≤2*N := by exact_mod_cast hp2
    have hr2' : r≤2*N := by exact_mod_cast hr2
    have hmem (v:ℤ) (hv:2*(p:ℤ)-3*r=v) :
        (p,r)∈Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) v := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hp2'⟩,
        Finset.mem_Icc.mpr ⟨by omega,hr2'⟩⟩,hpP,hrP,by omega,by omega,?_⟩
      simpa only [Nat.cast_ofNat] using hv
    rcases le_total (3*r) (2*p) with h | h
    · rw [Nat.dist_eq_sub_of_le_right h] at hd
      apply Finset.mem_union_left
      apply hmem
      omega
    · rw [Nat.dist_eq_sub_of_le h] at hd
      apply Finset.mem_union_right
      apply hmem
      omega
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem half_fibre_bound :
    ∃ B:ℝ,0<B ∧ ∀ᶠ N:ℕ in atTop, ∀ H d:ℕ,1≤d →
      (((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
        (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)).card:ℝ) ≤
        B*(N:ℝ)*(d:ℝ)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := by
  obtain ⟨B,hB,hbound⟩:=Sieve.exists_primeDilationPairs_threeHalves_bound
  refine ⟨2*B,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (2:ℕ)] with N hb hN
  intro H d hd
  have hdZ : (d:ℤ)≠0 := by exact_mod_cast (show d≠0 by omega)
  have hpos:=hb (d:ℤ) hdZ
  have hneg:=hb (-(d:ℤ)) (neg_ne_zero.mpr hdZ)
  simp only [Int.natAbs_neg,Int.natAbs_natCast] at hpos hneg
  have hc : (((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
      (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)).card:ℝ) ≤
      (Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (d:ℤ)).card+
      (Sieve.primeDilationPairs (2*N) (2*N) 2 3 (Sieve.sieveSift N) (-(d:ℤ))).card := by
    exact_mod_cast half_fibre_card (H:=H) (d:=d) hN
  calc
    _ ≤ _ := hc
    _ ≤ B*(N:ℝ)*(d:ℝ)^((1:ℝ)/4)/(Real.log (N:ℝ))^2+
      B*(N:ℝ)*(d:ℝ)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := add_le_add hpos hneg
    _ = _ := by ring

private theorem half_rows_sum {N H:ℕ} (hN:2<N) (F:ℕ→ℝ)
    (hrow:∀ pr∈primeGaussianCubicHalfResonancePairs (N:ℝ) H,
      ‖primeGaussianCubicCompleteRow (N:ℝ) pr.1 pr.2‖≤F (Nat.dist (2*pr.1) (3*pr.2))) :
    primeGaussianCubicHalfResonanceRowMass (N:ℝ) H ≤
      ∑ d∈Finset.Icc 1 H,
        (((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
          (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)).card:ℝ)*F d := by
  have hmap (pr:ℕ×ℕ) (hpr:pr∈primeGaussianCubicHalfResonancePairs (N:ℝ) H) :
      Nat.dist (2*pr.1) (3*pr.2)∈Finset.Icc 1 H := by
    obtain ⟨_,hr,hd⟩:=half_pair_mem.mp hpr
    exact Finset.mem_Icc.mpr ⟨half_dist_pos (by exact_mod_cast hN) hr,hd⟩
  unfold primeGaussianCubicHalfResonanceRowMass
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro d hd
  calc
    _ ≤ ∑ _pr∈(primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
        (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d), F d := by
      apply Finset.sum_le_sum
      intro pr hpr
      obtain ⟨hpr,he⟩:=Finset.mem_filter.mp hpr
      simpa only [he] using hrow pr hpr
    _ = _ := by simp

private theorem half_rows_bound :
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℕ in atTop, ∀ H:ℕ,
      (Real.log (N:ℝ))^2/(N:ℝ)*primeGaussianCubicHalfResonanceRowMass (N:ℝ) H ≤
        C*((H:ℝ)^((1:ℝ)/4)*(1+Real.log (H:ℝ))/Real.log (N:ℝ)+(H:ℝ)^2*
          ((1+H)/(Real.log (N:ℝ))^13+(1+H)/((N:ℝ)*Real.log (N:ℝ))+1/(N:ℝ))) := by
  obtain ⟨B,hB,hfibre⟩:=half_fibre_bound
  obtain ⟨C,hC,hrow⟩:=exists_primeGaussianCubicCompleteRow_half_resonance_bound
  refine ⟨B*C,by positivity,?_⟩
  filter_upwards [hfibre,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hrow,
    eventually_ge_atTop (3:ℕ)] with N hs hr hN
  intro H
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let L:=Real.log (N:ℝ)
  let E:ℝ:=(1+H)/L^12+(1+H)/(N:ℝ)
  let F:ℕ→ℝ:=fun d => C/L*(1/(d:ℝ)+E)+C/(N:ℝ)
  have hE : 0≤E := by dsimp [E,L];positivity
  have hF (d:ℕ) : 0≤F d := by dsimp [F,L];positivity
  have hrows := half_rows_sum (H:=H) (by omega : 2<N) F (by
    intro pr hp
    obtain ⟨hpp,hrr,hH⟩:=half_pair_mem.mp hp
    refine (hr _ hpp _ hrr).trans ?_
    rw [← half_dist_cast]
    have hcast : (Nat.dist (2*pr.1) (3*pr.2):ℝ)≤H := by exact_mod_cast hH
    dsimp [F,E,L]
    simp only [← add_assoc]
    gcongr)
  have hsum : (∑ d∈Finset.Icc 1 H,
      (((primeGaussianCubicHalfResonancePairs (N:ℝ) H).filter
        (fun pr => Nat.dist (2*pr.1) (3*pr.2)=d)).card:ℝ)*F d) ≤
      (B*(N:ℝ)/L^2)*(C/L*(H:ℝ)^((1:ℝ)/4)*(1+Real.log (H:ℝ))+
        (H:ℝ)^2*(C/L*E+C/(N:ℝ))) := by
    calc
      _ ≤ ∑ d∈Finset.Icc 1 H, (B*(N:ℝ)/L^2)*((d:ℝ)^((1:ℝ)/4)*F d) := by
        apply Finset.sum_le_sum
        intro d hd
        have hb:=mul_le_mul_of_nonneg_right (hs H d (Finset.mem_Icc.mp hd).1) (hF d)
        calc
          _ ≤ (B*(N:ℝ)*(d:ℝ)^((1:ℝ)/4)/(Real.log (N:ℝ))^2)*F d := hb
          _ = _ := by dsimp [L];ring
      _ = (B*(N:ℝ)/L^2)*∑ d∈Finset.Icc 1 H, (d:ℝ)^((1:ℝ)/4)*F d := by rw [Finset.mul_sum]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by dsimp [L];positivity)
        calc
          _ = ∑ d∈Finset.Icc 1 H, ((C/L)*((d:ℝ)^((1:ℝ)/4)/(d:ℝ))+
              (d:ℝ)^((1:ℝ)/4)*(C/L*E+C/(N:ℝ))) := by
            apply Finset.sum_congr rfl
            intro d hd
            dsimp [F]
            ring
          _ ≤ ∑ d∈Finset.Icc 1 H, ((C/L)*((H:ℝ)^((1:ℝ)/4)/(d:ℝ))+
              (H:ℝ)*(C/L*E+C/(N:ℝ))) := by
            apply Finset.sum_le_sum
            intro d hd
            have hdH : (d:ℝ)≤H := by exact_mod_cast (Finset.mem_Icc.mp hd).2
            have hd1 : (1:ℝ)≤d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
            have hdq : (d:ℝ)^((1:ℝ)/4)≤d := by
              calc
                _ ≤ (d:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hd1 (by norm_num)
                _ = _ := Real.rpow_one _
            have hqH := Real.rpow_le_rpow (Nat.cast_nonneg d) hdH (by norm_num : (0:ℝ)≤1/4)
            exact add_le_add
              (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hqH (Nat.cast_nonneg d))
                (show 0≤C/L from div_nonneg hC.le hL.le))
              (mul_le_mul_of_nonneg_right (hdq.trans hdH) (by positivity))
          _ = C/L*(H:ℝ)^((1:ℝ)/4)*(∑ d∈Finset.Icc 1 H,1/(d:ℝ))+
              (H:ℝ)^2*(C/L*E+C/(N:ℝ)) := by
            simp_rw [show ∀ d:ℕ, C/L*((H:ℝ)^((1:ℝ)/4)/(d:ℝ)) =
              (C/L*(H:ℝ)^((1:ℝ)/4))*(1/(d:ℝ)) by intro d;ring]
            rw [Finset.sum_add_distrib,← Finset.mul_sum]
            simp only [Finset.sum_const,Nat.card_Icc,add_tsub_cancel_right,nsmul_eq_mul]
            ring
          _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
              (Sieve.sum_Icc_one_div_le_one_add_log H)
              (show 0≤C/L*(H:ℝ)^((1:ℝ)/4) by dsimp [L];positivity)) le_rfl
  calc
    _ ≤ L^2/(N:ℝ)*((B*(N:ℝ)/L^2)*
        (C/L*(H:ℝ)^((1:ℝ)/4)*(1+Real.log (H:ℝ))+(H:ℝ)^2*(C/L*E+C/(N:ℝ)))) := by
      exact mul_le_mul_of_nonneg_left (hrows.trans hsum) (by positivity)
    _ = _ := by dsimp [E,L];field_simp
private theorem half_conductor_eq (m:ℕ) :
    (primeGaussianHyperbolicConductor m:ℝ) = ((10000000:ℝ)^4)^m := by
  change (((10000000:ℕ)^(4*m):ℕ):ℝ)=_
  rw [Nat.cast_pow,pow_mul]
  norm_cast

private theorem half_conductor_log (m:ℕ) :
    Real.log (primeGaussianHyperbolicConductor m:ℝ) = (4*Real.log 10000000)*(m:ℝ) := by
  rw [half_conductor_eq,Real.log_pow,Real.log_pow]
  ring

private theorem half_budget_tendsto :
    Tendsto (fun m:ℕ =>
      ((m:ℝ)^3)^((1:ℝ)/4)*(1+Real.log ((m:ℝ)^3))/Real.log (primeGaussianHyperbolicConductor m:ℝ)+(m:ℝ)^6*
        ((1+(m:ℝ)^3)/(Real.log (primeGaussianHyperbolicConductor m:ℝ))^13+
        (1+(m:ℝ)^3)/((primeGaussianHyperbolicConductor m:ℝ)*
          Real.log (primeGaussianHyperbolicConductor m:ℝ))+
        1/(primeGaussianHyperbolicConductor m:ℝ))) atTop (𝓝 0) := by
  let a:ℝ:=4*Real.log 10000000
  have ha : 0<a := by dsimp [a];positivity
  have hinv (k:ℕ) (hk:k≠0) : Tendsto (fun m:ℕ => 1/(m:ℝ)^k) atTop (𝓝 0) :=
    tendsto_const_div_pow 1 k hk
  have hlog : Tendsto (fun m:ℕ => Real.log (m:ℝ)/(m:ℝ)^((1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (1:ℝ) (show (0:ℝ)<1/4 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hinvq : Tendsto (fun m:ℕ => 1/(m:ℝ)^((1:ℝ)/4)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.rpow_zero] using
      (isLittleO_log_rpow_rpow_atTop (0:ℝ) (show (0:ℝ)<1/4 by norm_num)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp (k:ℕ) : Tendsto (fun m:ℕ => (m:ℝ)^k/(primeGaussianHyperbolicConductor m:ℝ))
      atTop (𝓝 0) := by
    simpa only [half_conductor_eq] using
      tendsto_pow_const_div_const_pow_of_one_lt k
        (show (1:ℝ)<(10000000:ℝ)^4 from one_lt_pow₀ (by norm_num) (by norm_num))
  have ht:=(((hinvq.add (hlog.const_mul 3)).const_mul (1/a)).add
      (((hinv 7 (by norm_num)).add (hinv 4 (by norm_num))).const_mul (1/a^13)))
      |>.add (((hp 5).add (hp 8)).const_mul (1/a)) |>.add (hp 6)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN0 : (0:ℝ)<primeGaussianHyperbolicConductor m := by rw [half_conductor_eq];positivity
  rw [half_conductor_log,Real.log_pow]
  change _=((m:ℝ)^3)^((1:ℝ)/4)*(1+(3:ℝ)*Real.log (m:ℝ))/(a*(m:ℝ))+(m:ℝ)^6*
    ((1+(m:ℝ)^3)/(a*(m:ℝ))^13+(1+(m:ℝ)^3)/
      ((primeGaussianHyperbolicConductor m:ℝ)*(a*(m:ℝ)))+1/(primeGaussianHyperbolicConductor m:ℝ))
  have hpow : ((m:ℝ)^3)^((1:ℝ)/4)*(m:ℝ)^((1:ℝ)/4)=(m:ℝ) := by
    rw [←Real.rpow_natCast (m:ℝ) 3,←Real.rpow_mul hm0.le,←Real.rpow_add hm0]
    norm_num
  have hmQ : (m:ℝ)^((1:ℝ)/4)≠0 := (Real.rpow_pos_of_pos hm0 _).ne'
  have hlead : ((m:ℝ)^3)^((1:ℝ)/4)/(m:ℝ)=1/(m:ℝ)^((1:ℝ)/4) := by
    field_simp
    exact hpow
  have hid : ((m:ℝ)^3)^((1:ℝ)/4)*(1+3*Real.log (m:ℝ))/(a*(m:ℝ)) =
      (1/(m:ℝ)^((1:ℝ)/4)+3*(Real.log (m:ℝ)/(m:ℝ)^((1:ℝ)/4)))*(1/a) := by
    calc
      _ = (((m:ℝ)^3)^((1:ℝ)/4)/(m:ℝ))*((1+3*Real.log (m:ℝ))/a) := by ring
      _ = _ := by rw [hlead];ring
  rw [hid]
  field_simp [ha.ne',hm0.ne',hN0.ne',hmQ]
  ring

/-- The normalized sum of complete physical row norms tends to zero on every
actual outer-prime pair with `|2*p-3*r| ≤ m^3`. No prime-pair asymptotic is assumed. -/
theorem tendsto_primeGaussianCubicHalfResonanceRowMass :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicHalfResonanceRowMass (primeGaussianHyperbolicConductor m) (m^3))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩:=half_rows_bound
  obtain ⟨N₀,hN₀⟩:=eventually_atTop.mp hbound
  have ht:=half_budget_tendsto.const_mul C
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


end RHTower
