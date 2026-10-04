import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicRationalRows
import GaloisForLFunctions.RHTower.Sieve.PrimeDilationUniformSlopes
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

/-!
# Complete physical cubic cancellation around every fixed rational slope

All noncontracting outer prime pairs within a growing determinant window are
retained, with every original physical q-row. Actual rational profiles and the
full slope-uniform sieve supply cancellation without affine-prime asymptotics.
The remaining complementary joint signed average is not asserted here.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem rational_exp_log_error {c:ℝ} (hc:0<c) (k:ℕ) :
    ∀ᶠ N:ℝ in atTop, Real.exp (-(c*Real.log N^((1:ℝ)/10)))≤1/(Real.log N)^k := by
  have ht : Tendsto (fun N:ℝ => Real.log N^((1:ℝ)/10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hd := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10*k:ℝ) c hc).comp ht
  have hdec : Tendsto (fun N:ℝ => Real.log N^k*Real.exp (-(c*Real.log N^((1:ℝ)/10))))
      atTop (𝓝 0) := by
    apply hd.congr'
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with N hL
    dsimp only [Function.comp_def]
    rw [←Real.rpow_mul hL.le]
    simp only [show (1:ℝ)/10*(10*k:ℝ)=(k:ℝ) by ring,Real.rpow_natCast]
    ring
  filter_upwards [hdec.eventually_le_const (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_gt_atTop 0] with N hd hL
  apply (le_div_iff₀ (pow_pos hL k)).mpr
  nlinarith only [hd]

private theorem rational_frequency_abs (A Q:ℕ) [NeZero Q] {N:ℝ} (hN:0<N)
    {p r:ℕ} (hr:r∈primeProfileBand N) :
    |(Q:ℝ)*p-(A:ℝ)*r|/(Q:ℝ)≤|primeGaussianCubicRationalFrequency A Q N p r| ∧
    |primeGaussianCubicRationalFrequency A Q N p r|≤8*|(Q:ℝ)*p-(A:ℝ)*r| := by
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hQ0 : (0:ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hQ1 : (1:ℝ)≤Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have he : primeGaussianCubicRationalFrequency A Q N p r =
      (2*Real.pi*N/((r:ℝ)*Q))*((Q:ℝ)*p-(A:ℝ)*r) := by
    dsimp only [primeGaussianCubicRationalFrequency]
    field_simp
  rw [he,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi*N/((r:ℝ)*Q))]
  have hlo : 1/(Q:ℝ)≤2*Real.pi*N/((r:ℝ)*Q) := by
    rw [div_le_div_iff₀ hQ0 (mul_pos hr0 hQ0)]
    have hpi : 1≤Real.pi := by linarith only [Real.pi_gt_three]
    have hh : (r:ℝ)≤2*Real.pi*N := by nlinarith only [hr2,mul_nonneg hN.le (sub_nonneg.mpr hpi)]
    nlinarith only [mul_le_mul_of_nonneg_right hh hQ0.le]
  have hhi : 2*Real.pi*N/((r:ℝ)*Q)≤8 := by
    apply (div_le_iff₀ (mul_pos hr0 hQ0)).mpr
    have hNr : N≤(r:ℝ)*Q := hrN.le.trans (le_mul_of_one_le_right hr0.le hQ1)
    nlinarith [Real.pi_lt_four]
  constructor
  · simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one] using
      mul_le_mul_of_nonneg_right hlo (abs_nonneg ((Q:ℝ)*p-(A:ℝ)*r))
  · exact mul_le_mul_of_nonneg_right hhi (abs_nonneg _)

private theorem rational_determinant_row_bound (A Q:ℕ) [NeZero Q] :
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      (Q:ℝ)*p-(A:ℝ)*r≠0 →
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        C/Real.log N*(1/|(Q:ℝ)*p-(A:ℝ)*r|+(1+|(Q:ℝ)*p-(A:ℝ)*r|)/(Real.log N)^12+
          (1+|(Q:ℝ)*p-(A:ℝ)*r|)/N)+C/N := by
  obtain ⟨c,B,X,hc,hB,hX,hrow⟩ := exists_primeGaussianCubicCompleteRow_rational_bound Q
  let M : ℝ := Q+8
  let C : ℝ := B*M+B+8
  have hM : 0<M := by dsimp [M];positivity
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop X,rational_exp_log_error hc 12,
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with N hNX he hL1
  intro p hp r hr hdet
  have hN0 : 0<N := by linarith only [hX,hNX]
  have hL : 0<Real.log N := by linarith only [hL1]
  let d : ℝ := |(Q:ℝ)*p-(A:ℝ)*r|
  let τ := primeGaussianCubicRationalFrequency A Q N p r
  have hd : 0<d := abs_pos.mpr hdet
  have hQ0 : (0:ℝ)<Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  obtain ⟨hlo,hhi⟩ := rational_frequency_abs A Q hN0 hr
  change d/(Q:ℝ)≤|τ| at hlo
  change |τ|≤8*d at hhi
  have ht : 0 < |τ| := (div_pos hd hQ0).trans_le hlo
  have hinv : 1/|τ|≤(Q:ℝ)/d := by
    apply (div_le_div_iff₀ ht hd).mpr
    nlinarith only [(div_le_iff₀ hQ0).mp hlo]
  have htail : (1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))≤
      8*((1+d)/(Real.log N)^12) := by
    have h8 : 1+|τ|≤8*(1+d) := by linarith only [hhi]
    have hh := mul_le_mul h8 he (Real.exp_pos _).le (by positivity : 0≤8*(1+d))
    exact hh.trans_eq (by ring)
  have hterm : 1/|τ|+(1+|τ|)*Real.exp (-(c*Real.log N^((1:ℝ)/10)))≤
      M*(1/d+(1+d)/(Real.log N)^12) := by
    have hmQ : (Q:ℝ)≤M := by dsimp [M];linarith
    have hm8 : 8≤M := by dsimp [M];linarith only [show (0:ℝ)≤Q from Nat.cast_nonneg Q]
    calc
      _ ≤ (Q:ℝ)/d+8*((1+d)/(Real.log N)^12) := add_le_add hinv htail
      _ ≤ M/d+M*((1+d)/(Real.log N)^12) := add_le_add
        (div_le_div_of_nonneg_right hmQ hd.le)
        (mul_le_mul_of_nonneg_right hm8 (by positivity))
      _ = _ := by ring
  have hb := hrow N hNX A p hp r hr (abs_pos.mp ht)
  have hBMC : B*M≤C := by dsimp [C];linarith only [hB]
  have hB8 : B+8≤C := by dsimp [C];linarith only [mul_nonneg hB.le hM.le]
  have hphysical : B/(N*Real.log N)+8/N≤(B+8)/N := by
    have hn : N≤N*Real.log N := le_mul_of_one_le_right hN0.le hL1
    have hh := div_le_div_of_nonneg_left hB.le hN0 hn
    calc
      _ ≤ B/N+8/N := add_le_add hh le_rfl
      _ = _ := by ring
  have hD : 0≤1/d+(1+d)/(Real.log N)^12 := by positivity
  change ‖primeGaussianCubicCompleteRow N p r‖≤C/Real.log N*(1/d+(1+d)/(Real.log N)^12+(1+d)/N)+C/N
  calc
    _ ≤ B/Real.log N*(M*(1/d+(1+d)/(Real.log N)^12))+(B+8)/N := by
      have hh := mul_le_mul_of_nonneg_left hterm (div_nonneg hB.le hL.le)
      exact hb.trans (by linarith only [hh,hphysical])
    _ = (B*M)/Real.log N*(1/d+(1+d)/(Real.log N)^12)+(B+8)/N := by ring
    _ ≤ C/Real.log N*(1/d+(1+d)/(Real.log N)^12)+C/N :=
      add_le_add (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hBMC hL.le) hD)
        (div_le_div_of_nonneg_right hB8 hN0.le)
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (by positivity : 0≤(1+d)/N)) (div_nonneg hC.le hL.le)) le_rfl

/-- All original-band outer prime pairs in the fixed rational resonance. -/
def primeGaussianCubicRationalPairs (A Q:ℕ) (N:ℝ) (H:ℕ) : Finset (ℕ×ℕ) :=
  ((primeProfileBand N).product (primeProfileBand N)).filter
    (fun pr => pr.1≠pr.2 ∧ Nat.dist (Q*pr.1) (A*pr.2)≤H)

/-- Sum of norms of complete physical middle-prime rows in this resonance. -/
def primeGaussianCubicRationalRowMass (A Q:ℕ) (N:ℝ) (H:ℕ) : ℝ :=
  ∑ pr∈primeGaussianCubicRationalPairs A Q N H, ‖primeGaussianCubicCompleteRow N pr.1 pr.2‖

private theorem rational_dist_cast (A Q p r:ℕ) :
    (Nat.dist (Q*p) (A*r):ℝ)=|(Q:ℝ)*p-(A:ℝ)*r| := by
  rcases le_total (A*r) (Q*p) with h | h
  · rw [Nat.dist_eq_sub_of_le_right h,Nat.cast_sub h]
    have hh : (A:ℝ)*r≤(Q:ℝ)*p := by exact_mod_cast h
    push_cast
    rw [abs_of_nonneg (sub_nonneg.mpr hh)]
  · rw [Nat.dist_eq_sub_of_le h,Nat.cast_sub h]
    have hh : (Q:ℝ)*p≤(A:ℝ)*r := by exact_mod_cast h
    push_cast
    rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    ring

private theorem rational_pair_mem {A Q:ℕ} {N:ℝ} {H p r:ℕ} :
    (p,r)∈primeGaussianCubicRationalPairs A Q N H ↔
      p∈primeProfileBand N ∧ r∈primeProfileBand N ∧ p≠r ∧ Nat.dist (Q*p) (A*r)≤H := by
  simp only [primeGaussianCubicRationalPairs,Finset.mem_filter]
  constructor
  · rintro ⟨hpr,hd⟩
    obtain ⟨hp,hr⟩:=Finset.mem_product.mp hpr
    exact ⟨hp,hr,hd⟩
  · rintro ⟨hp,hr,hd⟩
    exact ⟨Finset.mem_product.mpr ⟨hp,hr⟩,hd⟩

private theorem rational_dist_pos {A Q:ℕ} (hA:0<A) {N:ℝ}
    (hN:0≤N) (hAN:(A:ℝ)<N) {p r:ℕ} (hp:p∈primeProfileBand N)
    (hr:r∈primeProfileBand N) (hne:p≠r) : 1≤Nat.dist (Q*p) (A*r) := by
  obtain ⟨hpp,hpN,_⟩ := primeProfileBand_mem hN hp
  obtain ⟨hrp,_,_⟩ := primeProfileBand_mem hN hr
  have hAp : A<p := by exact_mod_cast hAN.trans hpN
  have he : Q*p≠A*r := by
    intro he
    have hd : p∣A*r := he ▸ dvd_mul_left p Q
    rcases hpp.dvd_mul.mp hd with hpa | hpr
    · exact (not_le_of_gt hAp) (Nat.le_of_dvd hA hpa)
    · exact hne ((Nat.prime_dvd_prime_iff_eq hpp hrp).mp hpr)
  exact Nat.one_le_iff_ne_zero.mpr (fun hz => he (Nat.eq_of_dist_eq_zero hz))

private theorem rational_fibre_card {A Q N H d:ℕ} (hN:2≤N) :
    ((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
      (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)).card ≤
      (Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (d:ℤ)).card+
      (Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (-(d:ℤ))).card := by
  have hsift := Sieve.sieveSift_le (show 1≤N by omega)
  have hsub : ((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
      (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)) ⊆
      Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (d:ℤ) ∪
      Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (-(d:ℤ)) := by
    rintro ⟨p,r⟩ hpr
    obtain ⟨hpair,hd⟩:=Finset.mem_filter.mp hpr
    obtain ⟨hp,hr,_,_⟩:=rational_pair_mem.mp hpair
    obtain ⟨hpP,hpN,hp2⟩:=primeProfileBand_mem (show (0:ℝ)≤N by positivity) hp
    obtain ⟨hrP,hrN,hr2⟩:=primeProfileBand_mem (show (0:ℝ)≤N by positivity) hr
    have hpN' : N<p := by exact_mod_cast hpN
    have hrN' : N<r := by exact_mod_cast hrN
    have hp2' : p≤2*N := by exact_mod_cast hp2
    have hr2' : r≤2*N := by exact_mod_cast hr2
    have hmem (v:ℤ) (hv:(Q:ℤ)*p-(A:ℤ)*r=v) :
        (p,r)∈Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) v := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hp2'⟩,
        Finset.mem_Icc.mpr ⟨by omega,hr2'⟩⟩,hpP,hrP,by omega,by omega,?_⟩
      exact hv
    rcases le_total (A*r) (Q*p) with h | h
    · rw [Nat.dist_eq_sub_of_le_right h] at hd
      apply Finset.mem_union_left
      apply hmem
      have hz := congrArg (fun n:ℕ => (n:ℤ)) hd
      rw [Nat.cast_sub h,Nat.cast_mul,Nat.cast_mul] at hz
      exact hz
    · rw [Nat.dist_eq_sub_of_le h] at hd
      apply Finset.mem_union_right
      apply hmem
      have hz := congrArg (fun n:ℕ => (n:ℤ)) hd
      rw [Nat.cast_sub h,Nat.cast_mul,Nat.cast_mul] at hz
      linarith only [hz]
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

private theorem rational_fibre_bound (A Q:ℕ) (hA:0<A) (hQ:0<Q) (hcop:Q.Coprime A) :
    ∃ B:ℝ,0<B ∧ ∀ᶠ N:ℕ in atTop, ∀ H d:ℕ,1≤d →
      (((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
        (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)).card:ℝ) ≤
        B*(N:ℝ)*(d:ℝ)^((1:ℝ)/4)/(Real.log (N:ℝ))^2 := by
  obtain ⟨B,hB,hbound⟩:=Sieve.exists_primeDilationPairs_uniform_slopes_bound
  let K : ℝ := ((Q:ℝ)*A)^((1:ℝ)/4)
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨2*B*K,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (2:ℕ)] with N hb hN
  intro H d hd
  have hdZ : (d:ℤ)≠0 := by exact_mod_cast (show d≠0 by omega)
  have hpos:=hb Q A hQ hA hcop (d:ℤ) hdZ
  have hneg:=hb Q A hQ hA hcop (-(d:ℤ)) (neg_ne_zero.mpr hdZ)
  simp only [Int.natAbs_neg,Int.natAbs_natCast] at hpos hneg
  have hc : (((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
      (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)).card:ℝ) ≤
      (Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (d:ℤ)).card+
      (Sieve.primeDilationPairs (2*N) (2*N) Q A (Sieve.sieveSift N) (-(d:ℤ))).card := by
    exact_mod_cast rational_fibre_card (A:=A) (Q:=Q) (H:=H) (d:=d) hN
  have he : ((d:ℝ)*Q*A)^((1:ℝ)/4)=(d:ℝ)^((1:ℝ)/4)*K := by
    rw [mul_assoc,Real.mul_rpow (Nat.cast_nonneg d) (by positivity)]
  rw [he] at hpos hneg
  exact (hc.trans (add_le_add hpos hneg)).trans_eq (by ring)

private theorem rational_rows_sum {A Q N H:ℕ} (hA:0<A) (hAN:(A:ℝ)<N) (hN:2<N) (F:ℕ→ℝ)
    (hrow:∀ pr∈primeGaussianCubicRationalPairs A Q (N:ℝ) H,
      ‖primeGaussianCubicCompleteRow (N:ℝ) pr.1 pr.2‖≤F (Nat.dist (Q*pr.1) (A*pr.2))) :
    primeGaussianCubicRationalRowMass A Q (N:ℝ) H ≤
      ∑ d∈Finset.Icc 1 H,
        (((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
          (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)).card:ℝ)*F d := by
  have hmap (pr:ℕ×ℕ) (hpr:pr∈primeGaussianCubicRationalPairs A Q (N:ℝ) H) :
      Nat.dist (Q*pr.1) (A*pr.2)∈Finset.Icc 1 H := by
    obtain ⟨hp,hr,hne,hd⟩:=rational_pair_mem.mp hpr
    exact Finset.mem_Icc.mpr ⟨rational_dist_pos hA (by positivity) hAN hp hr hne,hd⟩
  unfold primeGaussianCubicRationalRowMass
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro d hd
  calc
    _ ≤ ∑ _pr∈(primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
        (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d), F d := by
      apply Finset.sum_le_sum
      intro pr hpr
      obtain ⟨hpr,he⟩:=Finset.mem_filter.mp hpr
      simpa only [he] using hrow pr hpr
    _ = _ := by simp

private theorem rational_rows_bound (A Q:ℕ) [NeZero Q] (hA:0<A) (hcop:Q.Coprime A) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ N:ℕ in atTop, ∀ H:ℕ,
      (Real.log (N:ℝ))^2/(N:ℝ)*primeGaussianCubicRationalRowMass A Q (N:ℝ) H ≤
        C*((H:ℝ)^((1:ℝ)/4)*(1+Real.log (H:ℝ))/Real.log (N:ℝ)+(H:ℝ)^2*
          ((1+H)/(Real.log (N:ℝ))^13+(1+H)/((N:ℝ)*Real.log (N:ℝ))+1/(N:ℝ))) := by
  obtain ⟨B,hB,hfibre⟩:=rational_fibre_bound A Q hA (Nat.pos_of_ne_zero (NeZero.ne Q)) hcop
  obtain ⟨C,hC,hrow⟩:=rational_determinant_row_bound A Q
  refine ⟨B*C,by positivity,?_⟩
  filter_upwards [hfibre,(tendsto_natCast_atTop_atTop (R:=ℝ)).eventually hrow,
    eventually_ge_atTop (3:ℕ),eventually_gt_atTop A] with N hs hr hN hAN
  intro H
  have hN0 : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hL : 0<Real.log (N:ℝ) := Real.log_pos (by exact_mod_cast (show 1<N by omega))
  let L:=Real.log (N:ℝ)
  let E:ℝ:=(1+H)/L^12+(1+H)/(N:ℝ)
  let F:ℕ→ℝ:=fun d => C/L*(1/(d:ℝ)+E)+C/(N:ℝ)
  have hE : 0≤E := by dsimp [E,L];positivity
  have hF (d:ℕ) : 0≤F d := by dsimp [F,L];positivity
  have hrows := rational_rows_sum (A:=A) (Q:=Q) (H:=H) hA (by exact_mod_cast hAN) (by omega : 2<N) F (by
    intro pr hp
    obtain ⟨hpp,hrr,hne,hH⟩:=rational_pair_mem.mp hp
    have hd : 0<Nat.dist (Q*pr.1) (A*pr.2) := rational_dist_pos hA
      (by positivity) (by exact_mod_cast hAN) hpp hrr hne
    have hdet : (Q:ℝ)*pr.1-(A:ℝ)*pr.2≠0 := by
      apply abs_pos.mp
      rw [←rational_dist_cast]
      exact_mod_cast hd
    refine (hr _ hpp _ hrr hdet).trans ?_
    rw [← rational_dist_cast]
    have hcast : (Nat.dist (Q*pr.1) (A*pr.2):ℝ)≤H := by exact_mod_cast hH
    dsimp [F,E,L]
    simp only [← add_assoc]
    gcongr)
  have hsum : (∑ d∈Finset.Icc 1 H,
      (((primeGaussianCubicRationalPairs A Q (N:ℝ) H).filter
        (fun pr => Nat.dist (Q*pr.1) (A*pr.2)=d)).card:ℝ)*F d) ≤
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
private theorem rational_conductor_eq (m:ℕ) :
    (primeGaussianHyperbolicConductor m:ℝ) = ((10000000:ℝ)^4)^m := by
  change (((10000000:ℕ)^(4*m):ℕ):ℝ)=_
  rw [Nat.cast_pow,pow_mul]
  norm_cast

private theorem rational_conductor_log (m:ℕ) :
    Real.log (primeGaussianHyperbolicConductor m:ℝ) = (4*Real.log 10000000)*(m:ℝ) := by
  rw [rational_conductor_eq,Real.log_pow,Real.log_pow]
  ring

private theorem rational_budget_tendsto :
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
    simpa only [rational_conductor_eq] using
      tendsto_pow_const_div_const_pow_of_one_lt k
        (show (1:ℝ)<(10000000:ℝ)^4 from one_lt_pow₀ (by norm_num) (by norm_num))
  have ht:=(((hinvq.add (hlog.const_mul 3)).const_mul (1/a)).add
      (((hinv 7 (by norm_num)).add (hinv 4 (by norm_num))).const_mul (1/a^13)))
      |>.add (((hp 5).add (hp 8)).const_mul (1/a)) |>.add (hp 6)
  simp only [mul_zero,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hN0 : (0:ℝ)<primeGaussianHyperbolicConductor m := by rw [rational_conductor_eq];positivity
  rw [rational_conductor_log,Real.log_pow]
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
actual outer-prime pair with `|Q*p-A*r| ≤ m^3` with p!=r. No prime-pair asymptotic is assumed. -/
theorem tendsto_primeGaussianCubicRationalRowMass (A Q:ℕ) [NeZero Q]
    (hA:0<A) (hcop:Q.Coprime A) :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicRationalRowMass A Q (primeGaussianHyperbolicConductor m) (m^3))
      atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩:=rational_rows_bound A Q hA hcop
  obtain ⟨N₀,hN₀⟩:=eventually_atTop.mp hbound
  have ht:=rational_budget_tendsto.const_mul C
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
