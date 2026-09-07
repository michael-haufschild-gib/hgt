import GaloisForLFunctions.RHTower.DivisorUnsignedChannelPositivity
import GaloisForLFunctions.RHTower.MobiusDivisorAbelQuadraticDiagonal
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount
/-!
# Unavoidable late-prime compensation

The first-block divisor source gives a square-root floor on every prime in a
fixed late window. The corpus prime-window theorem makes their total mass
superlinear. Exact subtraction identifies that positive mass with the gap
between the smooth-prime head and the final arithmetic sum, ruling out a
uniform quadratic energy budget for both. This does not refute SD1.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem first_defect_lower : (1/10:ℝ) ≤ primeFreeDivisorDefect 1 := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic,Finset.sum_range_succ,Real.log_four_eq] at h
  norm_num [primeFreeDivisorDefect]
  linarith [Real.log_two_lt_d9]

private theorem unsigned_channel_first_block {M d : ℕ} (hd : 1 ≤ d)
    (hdM : d<M) (hMd : M ≤ 2*d) :
    divisorUnsignedDilationChannel M d =
      (Real.sqrt M-Real.sqrt d)*primeFreeDivisorDefect 1 := by
  have hdiv (k : ℕ) (hk : k ∈ Icc d (M-1)) : k/d=1 := by
    obtain ⟨hdk,hkM⟩ := mem_Icc.mp hk
    have hlo : 1 ≤ k/d := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hdk)
    have hhi : k/d<2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by omega)
    omega
  unfold divisorUnsignedDilationChannel
  calc
    _ = ∑ k ∈ Icc d (M-1), (Real.sqrt (k+1:ℕ)-Real.sqrt k)*primeFreeDivisorDefect 1 :=
      sum_congr rfl (fun k hk => by rw [hdiv k hk])
    _ = _ := by
      rw [← sum_mul,sum_sqrt_succ_sub_sqrt_Icc_general (by omega : d ≤ M-1),show M-1+1=M by omega]

/-- Positive mass still carried by primes in the final half of the actual cutoff. -/
def mobiusDivisorLatePrimeMass (M : ℕ) : ℝ :=
  ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M, divisorUnsignedDilationChannel M p

/-- The late-prime source mass has a square-root floor per prime in the inner subwindow. -/
theorem mobiusDivisorLatePrimeMass_four_mul_ge (N : ℕ) :
    ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*Real.sqrt N/40 ≤
      mobiusDivisorLatePrimeMass (4*N) := by
  have hpoint (p : ℕ) (hp : p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)) :
      Real.sqrt N/40 ≤ divisorUnsignedDilationChannel (4*N) p := by
    obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    have hN : 1 ≤ N := by have := hprime.pos; omega
    rw [unsigned_channel_first_block (by omega : 1 ≤ p) (by omega : p<4*N) (by omega : 4*N ≤ 2*p)]
    have hroot : Real.sqrt p ≤ (7/4:ℝ)*Real.sqrt N := by
      have hpSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
      have hNSq := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
      have hpR : (p:ℝ) ≤ 3*N := by exact_mod_cast hhi
      nlinarith [Real.sqrt_nonneg (p:ℝ),Real.sqrt_nonneg (N:ℝ)]
    have h4 : Real.sqrt (4*N:ℕ)=2*Real.sqrt N := by
      rw [Nat.cast_mul,Real.sqrt_mul (by norm_num)]
      norm_num
    rw [h4]
    have hgap : Real.sqrt N/4 ≤ 2*Real.sqrt N-Real.sqrt p := by linarith only [hroot]
    have h1 := mul_le_mul_of_nonneg_right hgap (show (0:ℝ) ≤ 1/10 by norm_num)
    have h2 := mul_le_mul_of_nonneg_left first_defect_lower
      (show 0 ≤ 2*Real.sqrt N-Real.sqrt p from (by positivity : 0 ≤ Real.sqrt N/4).trans hgap)
    linarith only [h1,h2]
  have hsum := sum_le_sum hpoint
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hsub : GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N) ⊆
      GaloisForLFunctions.HTGeometry.primesInIoc ((4*N)/2) (4*N) := by
    intro p hp
    obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    simp only [GaloisForLFunctions.HTGeometry.primesInIoc,mem_filter,mem_Ioc]
    exact ⟨⟨by omega,by omega⟩,hprime⟩
  have hext := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => divisorUnsignedDilationChannel_nonneg (4*N) p)
  unfold mobiusDivisorLatePrimeMass
  have hsum' : ((GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N)).card:ℝ)*Real.sqrt N/40 ≤
      ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (2*N) (3*N), divisorUnsignedDilationChannel (4*N) p := by
    simpa only [mul_div_assoc] using hsum
  exact hsum'.trans hext

private theorem sqrt_log_double_tendsto :
    Tendsto (fun N : ℕ => Real.sqrt N/(320*Real.log (2*(N:ℝ)))) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.sqrt_pos.mpr (by linarith))
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  have hr : Tendsto (fun x : ℝ => Real.sqrt x/Real.log x) atTop atTop := by
    exact hinv.congr (fun x => by change (Real.log x/Real.sqrt x)⁻¹=Real.sqrt x/Real.log x; rw [inv_div])
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (hr.comp hcast).const_mul_atTop (show (0:ℝ)<1/(320*Real.sqrt 2) by positivity)
  convert h using 1
  funext N
  simp only [Function.comp_def,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp

/-- The positive late-prime mass grows faster than the linear scale of the SD1 receiver. -/
theorem tendsto_mobiusDivisorLatePrimeMass_div_atTop :
    Tendsto (fun N : ℕ => mobiusDivisorLatePrimeMass (4*N)/(4*(N:ℝ))) atTop atTop := by
  have hcast : Tendsto (fun N : ℕ => 2*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
    (K := (3:ℝ)/2) (by norm_num))
  have hbound : ∀ᶠ N : ℕ in atTop,
      Real.sqrt N/(320*Real.log (2*(N:ℝ))) ≤ mobiusDivisorLatePrimeMass (4*N)/(4*(N:ℝ)) := by
    filter_upwards [hcount,eventually_ge_atTop (1:ℕ)] with N hc hN
    have harg : (3/2:ℝ)*(2*(N:ℝ))=(3*N:ℕ) := by push_cast; ring
    have htwo : 2*(N:ℝ)=((2*N:ℕ):ℝ) := by push_cast; rfl
    rw [harg,htwo,Nat.floor_natCast,Nat.floor_natCast] at hc
    have hcard := GaloisForLFunctions.HTGeometry.card_primesInIoc (show 2*N ≤ 3*N by omega)
    rw [← hcard] at hc
    have hmass := mobiusDivisorLatePrimeMass_four_mul_ge N
    have hmult := mul_le_mul_of_nonneg_right hc (show 0 ≤ Real.sqrt N/40 by positivity)
    have hraw : ((3/2:ℝ)-1)/2*(((2*N:ℕ):ℝ)/Real.log (2*N:ℕ))*(Real.sqrt N/40) ≤
        mobiusDivisorLatePrimeMass (4*N) := by
      rw [mul_div_assoc] at hmass
      exact hmult.trans hmass
    have hd := div_le_div_of_nonneg_right hraw (show (0:ℝ) ≤ 4*N by positivity)
    have hNr : (0:ℝ)<N := by positivity
    have heq : (((3/2:ℝ)-1)/2*(((2*N:ℕ):ℝ)/Real.log (2*N:ℕ))*(Real.sqrt N/40))/(4*(N:ℝ)) =
        Real.sqrt N/(320*Real.log (2*(N:ℝ))) := by
      push_cast
      field_simp
      ring
    rwa [heq] at hd
  exact tendsto_atTop_mono' _ hbound sqrt_log_double_tendsto

/-- The literal head left after all primes through half the cutoff have been paired. -/
def mobiusDivisorHalfPrimeHead (M : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, if ∀ p ∈ d.primeFactors, p ≤ M/2 then mobiusDivisorDilationChannel M d else 0

private theorem half_smooth_iff_not_late_prime {M d : ℕ} (hd : d ∈ Icc 1 M) :
    (∀ p ∈ d.primeFactors, p ≤ M/2) ↔ ¬(d.Prime ∧ M/2<d) := by
  obtain ⟨hd1,hdM⟩ := mem_Icc.mp hd
  constructor
  · intro hs hlate
    have hm : d ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hlate.1,dvd_rfl,by omega⟩
    have := hs d hm
    omega
  · intro hnot p hp
    obtain ⟨hpprime,hpd,_⟩ := Nat.mem_primeFactors.mp hp
    by_contra hlarge
    have hMp : M<2*p := by omega
    obtain ⟨k,hk⟩ := hpd
    have hk0 : 1 ≤ k := by
      by_contra h
      have hkz : k=0 := by omega
      rw [hkz,Nat.mul_zero] at hk
      omega
    have hk1 : k=1 := by
      by_contra hne
      have hkle : 2 ≤ k := by omega
      have hmul := Nat.mul_le_mul_left p hkle
      omega
    have heq : d=p := by simpa only [hk1,Nat.mul_one] using hk
    exact hnot ⟨heq ▸ hpprime,by omega⟩

/-- Exact late-prime compensation: the intermediate smooth-prime head differs from the final
signed aggregate by the complete positive late-prime mass. -/
theorem mobiusDivisorHalfPrimeHead_sub_total (M : ℕ) :
    mobiusDivisorHalfPrimeHead M-(∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d) =
      mobiusDivisorLatePrimeMass M := by
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 M) :
      (if ∀ p ∈ d.primeFactors, p ≤ M/2 then mobiusDivisorDilationChannel M d else 0)-
        mobiusDivisorDilationChannel M d =
      if d.Prime ∧ M/2<d then divisorUnsignedDilationChannel M d else 0 := by
    simp only [half_smooth_iff_not_late_prime hd]
    by_cases h : d.Prime ∧ M/2<d
    · rw [if_neg (not_not.mpr h),if_pos h,mobiusDivisorDilationChannel_eq_moebius_unsigned,
        ArithmeticFunction.moebius_apply_prime h.1]
      push_cast
      ring
    · simp [h]
  have hfilter : (Icc 1 M).filter (fun d => d.Prime ∧ M/2<d) =
      GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M := by
    ext d
    simp only [mem_filter,mem_Icc,GaloisForLFunctions.HTGeometry.primesInIoc,mem_Ioc]
    constructor
    · rintro ⟨⟨hd1,hdM⟩,hp,hl⟩
      exact ⟨⟨hl,hdM⟩,hp⟩
    · rintro ⟨⟨hl,hdM⟩,hp⟩
      exact ⟨⟨hp.one_lt.le,hdM⟩,hp,hl⟩
  unfold mobiusDivisorHalfPrimeHead
  rw [← sum_sub_distrib,sum_congr rfl hpoint,← sum_filter,hfilter]
  rfl

/-- Intermediate head and final aggregate cannot both stay on the linear receiver scale:
late primes force their combined normalized absolute size to infinity. -/
theorem tendsto_halfPrimeHead_add_total_abs_div_atTop :
    Tendsto (fun N : ℕ =>
      (|mobiusDivisorHalfPrimeHead (4*N)|+
        |∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d|)/(4*(N:ℝ))) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_mobiusDivisorLatePrimeMass_div_atTop
  intro N
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [← mobiusDivisorHalfPrimeHead_sub_total]
  exact (le_abs_self _).trans (by
    simpa only [sub_zero,zero_sub,abs_neg] using (abs_sub_le (mobiusDivisorHalfPrimeHead (4*N)) 0
      (∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d)))

/-- No uniform linear budget can cover both the actual smooth-prime head and the final signed
aggregate, even though every first-prime pairing contracts energy. -/
theorem not_uniform_halfPrimeHead_and_total_linear :
    ¬∃ C : ℝ, ∀ M : ℕ, |mobiusDivisorHalfPrimeHead M|+
      |∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d| ≤ C*M := by
  rintro ⟨C,hC⟩
  have hgt := tendsto_halfPrimeHead_add_total_abs_div_atTop.eventually_gt_atTop C
  obtain ⟨N,hN,hlarge⟩ := (Filter.Eventually.and (eventually_ge_atTop (1:ℕ)) hgt).exists
  have h := hC (4*N)
  have hpos : (0:ℝ)<4*N := by positivity
  have hle : (|mobiusDivisorHalfPrimeHead (4*N)|+
      |∑ d ∈ Icc 1 (4*N), mobiusDivisorDilationChannel (4*N) d|)/(4*(N:ℝ)) ≤ C := by
    rw [div_le_iff₀ hpos]
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using h
  exact (not_lt_of_ge hle) hlarge


/-- A fixed quadratic budget cannot bound both actual endpoints of the late-prime compensation. -/
theorem not_uniform_halfPrimeHead_and_total_quadratic :
    ¬∃ C : ℝ, ∀ M : ℕ, (mobiusDivisorHalfPrimeHead M)^2+
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^2 ≤ C*(M:ℝ)^2 := by
  rintro ⟨C,hC⟩
  apply not_uniform_halfPrimeHead_and_total_linear
  refine ⟨2*|C|+1,?_⟩
  intro M
  let H := mobiusDivisorHalfPrimeHead M
  let S := ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d
  have hs : (|H|+|S|)^2 ≤ 2*(H^2+S^2) := by
    nlinarith only [sq_nonneg (|H|-|S|),sq_abs H,sq_abs S]
  have hcoef : 2*|C| ≤ (2*|C|+1)^2 := by nlinarith [abs_nonneg C,sq_nonneg (2*|C|)]
  have hc := hC M
  change H^2+S^2 ≤ C*(M:ℝ)^2 at hc
  have hcabs := mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg (M:ℝ))
  have hbig := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (M:ℝ))
  have hsq : (|H|+|S|)^2 ≤ ((2*|C|+1)*(M:ℝ))^2 := by nlinarith only [hs,hc,hcabs,hbig]
  have hpos : 0 ≤ (2*|C|+1)*(M:ℝ) := by positivity
  change |H|+|S| ≤ _
  nlinarith only [hsq,hpos,abs_nonneg H,abs_nonneg S]

/-- No fixed multiple of the original arithmetic diagonal can cover both the intermediate
smooth-prime head energy and the final signed energy. -/
theorem not_uniform_halfPrimeHead_and_total_diagonal :
    ¬∃ C : ℝ, ∀ M : ℕ, (mobiusDivisorHalfPrimeHead M)^2+
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^2 ≤
        C*∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^2 := by
  rintro ⟨C,hC⟩
  apply not_uniform_halfPrimeHead_and_total_quadratic
  refine ⟨|C| * 722,?_⟩
  intro M
  have hQ : 0 ≤ ∑ d ∈ Icc 1 M, (mobiusDivisorDilationChannel M d)^2 :=
    sum_nonneg (fun _ _ => sq_nonneg _)
  have h1 := mul_le_mul_of_nonneg_right (le_abs_self C) hQ
  have h2 := mul_le_mul_of_nonneg_left (sum_mobiusDivisorDilationChannel_sq_le_quadratic M) (abs_nonneg C)
  have h := (hC M).trans (h1.trans h2)
  simpa only [mul_assoc] using h

end RHTower

