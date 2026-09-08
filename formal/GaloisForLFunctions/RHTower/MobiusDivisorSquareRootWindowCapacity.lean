import GaloisForLFunctions.RHTower.RetainedPrimeWindowSupply

/-! # Prime-window capacity above the square-root receiving scale -/
noncomputable section
open Finset Filter Topology
namespace RHTower

private lemma sqrt_log_mul_tendsto {b : ℕ} (hb : 0<b) :
    Tendsto (fun N : ℕ => Real.sqrt N/Real.log ((b:ℝ)*N)) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r:=1/2) (by norm_num)).tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.sqrt_pos.mpr (by linarith))
  have hr : Tendsto (fun x : ℝ => Real.sqrt x/Real.log x) atTop atTop := by
    exact hwithin.inv_tendsto_nhdsGT_zero.congr (fun x => by
      change (Real.log x/Real.sqrt x)⁻¹=Real.sqrt x/Real.log x
      rw [inv_div])
  have hbR : (0:ℝ)<b := by exact_mod_cast hb
  have hcast : Tendsto (fun N : ℕ => (b:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbR
  have h := (hr.comp hcast).const_mul_atTop (show (0:ℝ)<1/Real.sqrt b by positivity)
  convert h using 1
  funext N
  simp only [Function.comp_def,Real.sqrt_mul hbR.le]
  field_simp

/-- Every fixed macroscopic prime window supplies more than any fixed multiple of the square-root scale. -/
theorem tendsto_prime_window_card_div_sqrt (b : ℕ) (hb : 1≤b) :
    Tendsto (fun N : ℕ =>
      ((GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N)).card:ℝ)/Real.sqrt N) atTop atTop := by
  have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hratio : (1:ℝ)<((b:ℝ)+1)/b := by rw [lt_div_iff₀ hbR]; linarith
  have hcast : Tendsto (fun N : ℕ => (b:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbR
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hratio)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (1/2:ℝ)*(Real.sqrt N/Real.log ((b:ℝ)*N)) ≤
        ((GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N)).card:ℝ)/Real.sqrt N := by
    filter_upwards [hcount,eventually_ge_atTop (1:ℕ)] with N hcount hN
    have harg : (((b:ℝ)+1)/b)*((b:ℝ)*N)=((b+1)*N:ℕ) := by push_cast; field_simp
    have hbN : (b:ℝ)*N=(b*N:ℕ) := by push_cast; rfl
    rw [harg,hbN,Nat.floor_natCast,Nat.floor_natCast] at hcount
    rw [← GaloisForLFunctions.HTGeometry.card_primesInIoc (show b*N≤(b+1)*N by nlinarith)] at hcount
    have hd := div_le_div_of_nonneg_right hcount (Real.sqrt_nonneg (N:ℝ))
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) N)
    have hroot : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.2 (by exact_mod_cast (show 0<N by omega))).ne'
    have he : (((((b:ℝ)+1)/b-1)/2*((b*N:ℕ)/Real.log (b*N:ℕ)))/Real.sqrt N)=
        (1/2:ℝ)*(Real.sqrt N/Real.log ((b:ℝ)*N)) := by
      push_cast
      field_simp
      rw [hs]
      ring
    rwa [he] at hd
  exact tendsto_atTop_mono' _ hbound
    ((sqrt_log_mul_tendsto (by omega : 0<b)).const_mul_atTop (by norm_num : (0:ℝ)<1/2))

private lemma scaled_window_card_div_sqrt (b a : ℕ) (hb : 1≤b) (ha : 1≤a) :
    Tendsto (fun N : ℕ =>
      ((GaloisForLFunctions.HTGeometry.primesInIoc (b*(a*N)) ((b+1)*(a*N))).card:ℝ)/Real.sqrt N) atTop atTop := by
  have hnat : Tendsto (fun N : ℕ => a*N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop' (by omega : 0<a) tendsto_id
  have haR : 0<Real.sqrt (a:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0<a by omega))
  have h := ((tendsto_prime_window_card_div_sqrt b hb).comp hnat).const_mul_atTop haR
  convert h using 1
  funext N
  simp only [Function.comp_def,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg a)]
  field_simp

/-- After reserving one prescribed prime, all three coupled direction pools still dominate every fixed square-root demand. -/
theorem eventually_mobiusDivisorCoupledTwoCapacity_sub_one_ge_sqrt
    (b : ℕ) (hb : 1≤b) (C : ℝ) (hC : 0<C) :
    ∀ᶠ N : ℕ in atTop,
      C*Real.sqrt (14*(b+1)*N:ℕ)≤((mobiusDivisorCoupledTwoCapacity b N-1:ℕ):ℝ) := by
  let T : ℝ := C*Real.sqrt (14*(b+1):ℕ)+2
  have h7 := (scaled_window_card_div_sqrt b 7 hb (by omega)).eventually_ge_atTop T
  have h2 := (scaled_window_card_div_sqrt b 2 hb (by omega)).eventually_ge_atTop T
  have h1 := (tendsto_prime_window_card_div_sqrt b hb).eventually_ge_atTop T
  filter_upwards [h7,h2,h1,eventually_ge_atTop (1:ℕ)] with N h7 h2 h1 hN
  have hroot : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (show 0<N by omega))
  have hr1 : (1:ℝ)≤Real.sqrt N := by rw [Real.le_sqrt (by norm_num) (by positivity)]; exact_mod_cast hN
  have h7' := (le_div_iff₀ hroot).mp h7
  have h2' := (le_div_iff₀ hroot).mp h2
  have h1' := (le_div_iff₀ hroot).mp h1
  have hcap : T*Real.sqrt N≤(mobiusDivisorCoupledTwoCapacity b N:ℝ) := by
    simpa only [mobiusDivisorCoupledTwoCapacity,mobiusDivisorCoupledTwoWindow,Nat.reduceDiv,
      one_mul,Nat.cast_min] using le_min h7' (le_min h2' h1')
  have hT : 2≤T := by dsimp only [T]; have h := mul_nonneg hC.le (Real.sqrt_nonneg ((14*(b+1):ℕ):ℝ)); linarith only [h]
  have hcap1 : 1 ≤ mobiusDivisorCoupledTwoCapacity b N := by
    have hh : (1:ℝ) ≤ mobiusDivisorCoupledTwoCapacity b N := by nlinarith only [hcap,hr1,hT]
    exact_mod_cast hh
  rw [Nat.cast_sub hcap1,Nat.cast_one,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg (14*(b+1)))]
  dsimp only [T] at hcap
  nlinarith only [hcap,hr1]
end RHTower
