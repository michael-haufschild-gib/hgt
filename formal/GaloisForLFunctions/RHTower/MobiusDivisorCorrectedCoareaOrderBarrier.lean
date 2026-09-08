import GaloisForLFunctions.RHTower.MobiusDivisorCorrectedCoareaMassBalance
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic

/-!
# Every complete order also crosses the corrected coarea mass-balance barrier

Bounded prime-atom increments force a prefix with consumed and remaining
late mass both at least a quarter of their total. The full signed total
is negligible relative to that late mass, so corrected action pays at
least a constant times `T³/U` at this prefix. Actual source asymptotics
make `T³/(U M²)` unbounded. This excludes a quadratic corrected-action
ceiling for every complete one-index order, independently of mixed-cell
cancellation. It does not exclude a quadratic raw-energy bound.
-/
noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower

/-- Any sequence reaching its total in jumps at most half that total visits the middle half. -/
theorem exists_prefix_mass_quarter_band (x : ℕ → ℝ) (T : ℝ) (k : ℕ)
    (hT : 0<T) (h0 : x 0=0) (hk : x k=T)
    (hstep : ∀ n<k, x (n+1)-x n ≤ T/2) :
    ∃ n≤k, T/4 ≤ x n ∧ x n ≤ 3*T/4 := by
  have hex : ∃ n, T/4 ≤ x n := ⟨k,by rw [hk]; linarith⟩
  let j := Nat.find hex
  have hj : T/4 ≤ x j := Nat.find_spec hex
  have hjk : j ≤ k := Nat.find_min' hex (by rw [hk]; linarith)
  have hj0 : j ≠ 0 := by intro he; rw [he,h0] at hj; linarith
  have hlo : x (j-1) < T/4 := lt_of_not_ge (Nat.find_min hex (by omega : j-1<j))
  have hinc := hstep (j-1) (by omega)
  rw [show j-1+1=j by omega] at hinc
  exact ⟨j,hjk,hj,by linarith⟩

/-- Every complete order has a cubic late-mass cost once the full signed total is small enough. -/
theorem exists_mobiusDivisorCorrectedCoarea_prefix_mass_barrier (M k : ℕ)
    (P : ℕ → Finset ℕ) (q : ℕ → ℕ)
    (hT : 0 < mobiusDivisorLatePrimeMass M)
    (hjump : (3/5:ℝ)*Real.sqrt M ≤ mobiusDivisorLatePrimeMass M/2)
    (hS : -mobiusDivisorLatePrimeMass M/8 ≤ ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)
    (h0 : Disjoint (mobiusDivisorActiveLatePrimes M) (P 0))
    (hk : mobiusDivisorActiveLatePrimes M ⊆ P k)
    (hstep : ∀ n<k, P (n+1)=insert (q n) (P n)) :
    ∃ n≤k, (mobiusDivisorLatePrimeMass M)^3 ≤
      256*mobiusDivisorAbsoluteMass M*mobiusDivisorCorrectedCoareaAction M (P n) := by
  have hx0 : mobiusDivisorConsumedLateMass M (P 0)=0 := by
    simp [mobiusDivisorConsumedLateMass,Finset.disjoint_iff_inter_eq_empty.mp h0]
  have hxk : mobiusDivisorConsumedLateMass M (P k)=mobiusDivisorLatePrimeMass M := by
    have hr : mobiusDivisorRemainingLateMass M (P k)=0 := by
      simp [mobiusDivisorRemainingLateMass,sdiff_eq_empty_iff_subset.mpr hk]
    simpa only [hr,add_zero] using mobiusDivisorConsumed_add_remainingLateMass M (P k)
  obtain ⟨n,hn,hlo,hhi⟩ := exists_prefix_mass_quarter_band
    (fun n => mobiusDivisorConsumedLateMass M (P n)) (mobiusDivisorLatePrimeMass M) k hT hx0 hxk
    (fun n hn => by rw [hstep n hn]; exact
      (mobiusDivisorConsumedLateMass_insert_step_le M (P n) (q n)).trans hjump)
  have hsum := mobiusDivisorConsumed_add_remainingLateMass M (P n)
  have hsigned : mobiusDivisorLatePrimeMass M/8 ≤
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M (P n) := by
    linarith only [hsum,hhi,hS]
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ mobiusDivisorLatePrimeMass M/8) hsigned 2
  have ht : 0 ≤ mobiusDivisorConsumedLateMass M (P n) := sum_nonneg (fun _ _ => abs_nonneg _)
  have hprod := mul_le_mul hlo hsquare (sq_nonneg (mobiusDivisorLatePrimeMass M/8)) ht
  have hbal := mobiusDivisorCorrectedCoareaAction_mass_balance M (P n)
  refine ⟨n,hn,?_⟩
  nlinarith only [hprod,hbal]

private lemma log_cube_div_nat_tendsto :
    Tendsto (fun N : ℕ => (Real.log (2*(N:ℝ)))^3/(N:ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun x : ℝ => (Real.log x)^3/x) atTop (𝓝 0) := by
    simpa only [Real.rpow_ofNat,Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop (s:=1) 3 (by norm_num)).tendsto_div_nhds_zero
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (hreal.comp hcast).const_mul 2
  convert h using 1
  · ext N
    dsimp only [Function.comp_def]
    ring
  · simp

/-- Actual late mass cubed exceeds every fixed multiple of absolute mass times the quadratic scale. -/
theorem eventually_mobiusDivisorLatePrimeMass_cube_gt (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, B*(4*(N:ℝ))^2*mobiusDivisorAbsoluteMass (4*N) <
      (mobiusDivisorLatePrimeMass (4*N))^3 := by
  let b := |B|+1
  let K := b*(384/5:ℝ)*80^3
  have hb : 0<b := by dsimp [b]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  have hsmall := log_cube_div_nat_tendsto.eventually (gt_mem_nhds (by positivity : (0:ℝ)<1/K))
  filter_upwards [hsmall,eventually_mobiusDivisorLatePrimeMass_ge,eventually_ge_atTop (1:ℕ)] with N hlog hT hN
  have hn : (0:ℝ)<N := by positivity
  have hlogpos : 0<Real.log (2*(N:ℝ)) := Real.log_pos (by
    have h := (show (1:ℝ)≤N by exact_mod_cast hN)
    linarith)
  have hlogbound : K*(Real.log (2*(N:ℝ)))^3 < (N:ℝ) := by
    have h := (div_lt_iff₀ hn).mp hlog
    have h' := mul_lt_mul_of_pos_left h hK
    field_simp at h'
    nlinarith only [h']
  have hs : (Real.sqrt N)^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  have hcube : ((N:ℝ)*Real.sqrt N)^3=(N:ℝ)^4*Real.sqrt N := by
    calc
      _ = (N:ℝ)^3*((Real.sqrt N)^2*Real.sqrt N) := by ring
      _ = _ := by rw [hs]; ring
  have h4 : Real.sqrt (4*N:ℕ)=2*Real.sqrt N := by
    rw [Nat.cast_mul,Real.sqrt_mul (by norm_num)]
    norm_num
  have hU := mobiusDivisorAbsoluteMass_le (4*N)
  rw [h4] at hU
  push_cast at hU
  have hUn : 0 ≤ mobiusDivisorAbsoluteMass (4*N) := sum_nonneg (fun _ _ => abs_nonneg _)
  have hupper : B*(4*(N:ℝ))^2*mobiusDivisorAbsoluteMass (4*N) ≤
      b*(4*(N:ℝ))^2*((24/5:ℝ)*(N:ℝ)*Real.sqrt N) := by
    have hBb : B≤b := by dsimp [b]; linarith only [le_abs_self B]
    calc
      _ ≤ b*(4*(N:ℝ))^2*mobiusDivisorAbsoluteMass (4*N) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBb (sq_nonneg _)) hUn
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith only [hU]) (by positivity)
  have hstrict : b*(4*(N:ℝ))^2*((24/5:ℝ)*(N:ℝ)*Real.sqrt N) <
      ((N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ))))^3 := by
    rw [div_pow,hcube]
    apply (lt_div_iff₀ (pow_pos (by positivity : (0:ℝ)<80*Real.log (2*(N:ℝ))) 3)).mpr
    have hm := mul_lt_mul_of_pos_right hlogbound
      (by positivity : (0:ℝ)<(N:ℝ)^3*Real.sqrt N)
    dsimp [K] at hm
    convert hm using 1 <;> ring
  have hpow := pow_le_pow_left₀
    (by positivity : (0:ℝ)≤(N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ)))) hT 3
  exact hupper.trans_lt (hstrict.trans_le hpow)

/-- The corrected coarea action also fails a uniform quadratic ceiling for every complete prime order. -/
theorem eventually_every_mobiusDivisorCorrectedCoarea_order_exceeds_quadratic (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ (k : ℕ) (P : ℕ → Finset ℕ) (q : ℕ → ℕ),
      Disjoint (mobiusDivisorActiveLatePrimes (4*N)) (P 0) →
      mobiusDivisorActiveLatePrimes (4*N) ⊆ P k →
      (∀ n<k, P (n+1)=insert (q n) (P n)) →
      ∃ n≤k, C*(4*(N:ℝ))^2 < mobiusDivisorCorrectedCoareaAction (4*N) (P n) := by
  have hT := tendsto_mobiusDivisorLatePrimeMass_div_atTop.eventually_gt_atTop 2
  have hS := tendsto_total_div_mobiusDivisorLatePrimeMass.eventually
    (lt_mem_nhds (by norm_num : (-1/8:ℝ)<0))
  filter_upwards [hT,hS,eventually_mobiusDivisorLatePrimeMass_cube_gt (256*|C|),
    eventually_ge_atTop (1:ℕ)] with N hT hS hbig hN
  have hM : (1:ℝ)≤4*N := by exact_mod_cast (show 1≤4*N by omega)
  have hMp : (0:ℝ)<4*N := by linarith
  have hlarge := (lt_div_iff₀ hMp).mp hT
  have hTp : 0 < mobiusDivisorLatePrimeMass (4*N) := by linarith
  have hSraw := (lt_div_iff₀ hTp).mp hS
  have hsqrt : Real.sqrt (4*N:ℕ) ≤ 4*(N:ℝ) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      Real.sqrt_le_self_iff.mpr (Or.inr (show (1:ℝ)≤(4*N:ℕ) by exact_mod_cast (show 1≤4*N by omega)))
  intro k P q h0 hk hstep
  obtain ⟨n,hn,hbarrier⟩ := exists_mobiusDivisorCorrectedCoarea_prefix_mass_barrier
    (4*N) k P q hTp (by linarith only [hsqrt,hlarge]) (by linarith only [hSraw]) h0 hk hstep
  refine ⟨n,hn,?_⟩
  by_contra hbad
  have hbad' : mobiusDivisorCorrectedCoareaAction (4*N) (P n) ≤ C*(4*(N:ℝ))^2 := le_of_not_gt hbad
  have hUn : 0 ≤ mobiusDivisorAbsoluteMass (4*N) := sum_nonneg (fun _ _ => abs_nonneg _)
  have hbound := mul_le_mul_of_nonneg_left hbad' (by positivity : (0:ℝ)≤256*mobiusDivisorAbsoluteMass (4*N))
  have habs := mul_le_mul_of_nonneg_right (le_abs_self C)
    (by positivity : (0:ℝ)≤256*mobiusDivisorAbsoluteMass (4*N)*(4*(N:ℝ))^2)
  nlinarith only [hbarrier,hbound,habs,hbig]

end RHTower
