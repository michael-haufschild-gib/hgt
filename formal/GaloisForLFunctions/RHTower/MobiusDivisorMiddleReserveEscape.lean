import GaloisForLFunctions.RHTower.MobiusDivisorMiddleChildHead
import GaloisForLFunctions.RHTower.MobiusDivisorSignedPrimeBatches
/-!
# Middle-prime energy escapes every fixed scalar-reserve budget

At parent cutoff `64N²`, the processed core below `4N` creates uniformly
large child heads on both clipped quotient endpoints for primes in `(8N,9N]`.
Their retained singleton squares force energy divided by the parent cutoff
squared to diverge. This lower bound is uniform over every selected pool of
scalar primes above one eighth of the parent cutoff: consuming such primes
leaves all disjoint nonempty coordinates unchanged.

This excludes increasing middle-prime processing supplemented by those fixed
scalar reserves. It does not exclude schedules that interleave nonisolated
primes across that increasing front. All estimates follow analytically from
the corpus source identities and quantitative PNT; no numerical result is used.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower

/-- Consuming isolated primes leaves every disjoint nonempty source coordinate unchanged. -/
theorem mobiusDivisorSelectionFibre_union_isolated_nonempty (M : ℕ) (P L R : Finset ℕ)
    (hL : ∀ p∈L,p.Prime ∧ p<M ∧ p∉P ∧ mobiusDivisorSelectionPrimes (M/p+1)⊆P)
    (hR : R.Nonempty) (hRL : Disjoint R L) :
    mobiusDivisorSelectionFibre M (P∪L) R=mobiusDivisorSelectionFibre M P R := by
  revert hL hRL
  induction L using Finset.induction_on with
  | empty => intro _ _; simp
  | @insert p L hpL ih =>
    intro hL hRL
    obtain ⟨hp,hpM,hpP,hcore⟩ := hL p (mem_insert_self p L)
    have hpR : p∉R := fun h => disjoint_left.mp hRL h (mem_insert_self p L)
    have hRL' : Disjoint R L := hRL.mono_right (subset_insert p L)
    rw [union_insert,mobiusDivisorSelectionFibre_insert,if_neg hpR,
      mobiusDivisorSelectionFibre_insertLabel_isolated M (P∪L) R hp
        (by simp [hpP,hpL]) hpR (hcore.trans subset_union_left),
      if_neg hR.ne_empty,add_zero]
    exact ih (fun q hq => hL q (mem_insert_of_mem hq)) hRL'

/-- Any specified prime-singleton square sum is part of the literal complete energy. -/
theorem sum_mobiusDivisorSelectionSingleton_sq_le_energy (M : ℕ) (P U : Finset ℕ)
    (hU : U⊆mobiusDivisorSelectionPrimes M) :
    (∑ p∈U,(mobiusDivisorSelectionFibre M P {p})^2)≤ mobiusDivisorSelectionEnergy M P := by
  have hsub : U.image (fun p => ({p}:Finset ℕ))⊆(mobiusDivisorSelectionPrimes M).powerset := by
    intro R hR
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
    exact mem_powerset.mpr (singleton_subset_iff.mpr (hU hp))
  have hs := sum_le_sum_of_subset_of_nonneg hsub
    (fun R _ _ => sq_nonneg (mobiusDivisorSelectionFibre M P R))
  rw [sum_image (fun a _ b _ h => singleton_injective h)] at hs
  exact hs

private theorem middle_quotient_range {N p : ℕ} (hN : 1≤N)
    (hp : p∈GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)) :
    7*N≤(64*N^2)/p ∧ (64*N^2)/p+1≤8*N := by
  obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  constructor
  · exact (Nat.le_div_iff_mul_le hprime.pos).mpr (by nlinarith)
  · have h := (Nat.div_lt_iff_lt_mul hprime.pos).mpr (show 64*N^2<8*N*p by nlinarith)
    omega

/-- A macroscopic family of actual middle-prime singletons inherits the uniformly large child heads. -/
theorem eventually_mobiusDivisorMiddlePrimeFibre_upper :
    ∀ᶠ N : ℕ in atTop,∀ p : ℕ,
      p∈GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N) →
      mobiusDivisorSelectionFibre (64*N^2) (mobiusDivisorSelectionPrimes (4*N)) {p}≤
        -(N:ℝ)^2/(80*Real.log (8*(N:ℝ))) := by
  filter_upwards [eventually_mobiusDivisorMiddleChildHead_lower,eventually_ge_atTop (1:ℕ)] with N hhead hN
  intro p hp
  obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  obtain ⟨hqlo,hqhi⟩ := middle_quotient_range hN hp
  have h0 := hhead ((64*N^2)/p) hqlo (by omega)
  have h1 := hhead ((64*N^2)/p+1) (by omega) hqhi
  let a := (N:ℝ)*Real.sqrt N/(160*Real.log (8*(N:ℝ)))
  have hl4 : 0<Real.log (4*(N:ℝ)) := Real.log_pos (by exact_mod_cast (show 1<4*N by omega))
  have hl8 : 0<Real.log (8*(N:ℝ)) := Real.log_pos (by exact_mod_cast (show 1<8*N by omega))
  have hlog : Real.log (4*(N:ℝ))≤Real.log (8*(N:ℝ)) :=
    Real.log_le_log (by positivity) (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
  have ha : a≤(N:ℝ)*Real.sqrt N/(160*Real.log (4*(N:ℝ))) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith only [hlog]
  have ha0 : 0≤a := by dsimp [a]; positivity
  have hw0 := divisorPrimeClipWeight_nonneg (64*N^2) p hpp.pos
  have hw1 := (divisorPrimeClipWeight_lt_one (64*N^2) p hpp.pos).le
  have hm0 := mul_le_mul_of_nonneg_left (ha.trans h0) (by linarith only [hw1] : 0≤1-divisorPrimeClipWeight (64*N^2) p)
  have hm1 := mul_le_mul_of_nonneg_left (ha.trans h1) hw0
  have hinterp : a≤ mobiusDivisorInterpolatedFibre (64*N^2) p (mobiusDivisorSelectionPrimes (4*N)) ∅ := by
    unfold mobiusDivisorInterpolatedFibre
    nlinarith only [hm0,hm1]
  have hpP : p∉mobiusDivisorSelectionPrimes (4*N) := by
    intro h
    have := mem_range.mp (mem_filter.mp h).1
    omega
  rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hpp _ _ ∅ hpP (by simp)]
  have hroot : 2*Real.sqrt N≤Real.sqrt p := by
    have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hsqp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have hpr : 4*(N:ℝ)≤p := by exact_mod_cast (show 4*N≤p by omega)
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg (p:ℝ)]
  have hm := mul_le_mul_of_nonneg_left hinterp (Real.sqrt_nonneg (p:ℝ))
  have hr := mul_le_mul_of_nonneg_right hroot ha0
  have he : 2*Real.sqrt N*a=(N:ℝ)^2/(80*Real.log (8*(N:ℝ))) := by
    dsimp [a]
    have hn := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    calc
      _ = (N:ℝ)*(Real.sqrt N)^2/(80*Real.log (8*(N:ℝ))) := by ring
      _ = _ := by rw [hn]; ring
  have hh : (N:ℝ)^2/(80*Real.log (8*(N:ℝ)))≤
      Real.sqrt p*mobiusDivisorInterpolatedFibre (64*N^2) p
        (mobiusDivisorSelectionPrimes (4*N)) ∅ := by
    rw [← he]
    exact hr.trans hm
  simpa only [neg_mul,neg_div] using neg_le_neg hh

private theorem middle_pool_persists {N : ℕ} (hN : 2≤N) (L : Finset ℕ)
    (hL : ∀ q∈L,q.Prime ∧ q<64*N^2 ∧ 64*N^2<8*q)
    {p : ℕ} (hp : p∈GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)) :
    mobiusDivisorSelectionFibre (64*N^2) (mobiusDivisorSelectionPrimes (4*N)∪L) {p}=
      mobiusDivisorSelectionFibre (64*N^2) (mobiusDivisorSelectionPrimes (4*N)) {p} := by
  have hcore : mobiusDivisorSelectionPrimes 8⊆mobiusDivisorSelectionPrimes (4*N) := by
    intro q hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hq; omega),hprime⟩
  have hL' : ∀ q∈L,q.Prime ∧ q<64*N^2 ∧ q∉mobiusDivisorSelectionPrimes (4*N) ∧
      mobiusDivisorSelectionPrimes ((64*N^2)/q+1)⊆mobiusDivisorSelectionPrimes (4*N) := by
    intro q hq
    obtain ⟨hprime,hqM,hlarge⟩ := hL q hq
    have hqP : q∉mobiusDivisorSelectionPrimes (4*N) := by
      intro hn
      have := mem_range.mp (mem_filter.mp hn).1
      nlinarith
    exact ⟨hprime,hqM,hqP,mobiusDivisorPrime_isolated_after_eight _ _ hcore hprime hlarge⟩
  have hpL : p∉L := by
    intro h
    have hlarge := (hL p h).2.2
    have hhi := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hp).2.2
    nlinarith
  apply mobiusDivisorSelectionFibre_union_isolated_nonempty _ _ _ _ hL' (singleton_nonempty p)
  exact disjoint_singleton_left.mpr hpL

private theorem eventually_eight_nine_count :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)/(2*Real.log (8*(N:ℝ)))≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)).card := by
  have hcast : Tendsto (fun N : ℕ => 8*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hc := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
    (K := (9:ℝ)/8) (by norm_num))
  filter_upwards [hc] with N hc
  have he : (9/8:ℝ)*(8*(N:ℝ))=(9*N:ℕ) := by push_cast; ring
  have hf : 8*(N:ℝ)=(8*N:ℕ) := by push_cast; rfl
  rw [he,hf,Nat.floor_natCast,Nat.floor_natCast,
    ← GaloisForLFunctions.HTGeometry.card_primesInIoc (show 8*N≤9*N by omega)] at hc
  convert hc using 1; push_cast; ring

/-- The unchanged middle singleton sector alone forces a superquadratic lower bound, uniformly over every fixed scalar-reserve selection. -/
theorem eventually_mobiusDivisorMiddleEnergy_lower :
    ∀ᶠ N : ℕ in atTop,∀ L : Finset ℕ,
      (∀ q∈L,q.Prime ∧ q<64*N^2 ∧ 64*N^2<8*q) →
      (N:ℝ)/(52428800*Real.log (8*(N:ℝ))^3)≤
        mobiusDivisorSelectionEnergy (64*N^2) (mobiusDivisorSelectionPrimes (4*N)∪L)/
          ((64*N^2:ℕ):ℝ)^2 := by
  filter_upwards [eventually_mobiusDivisorMiddlePrimeFibre_upper,eventually_eight_nine_count,
    eventually_ge_atTop (2:ℕ)] with N hf hc hN
  intro L hL
  have hl : 0<Real.log (8*(N:ℝ)) := Real.log_pos (by exact_mod_cast (show 1<8*N by omega))
  let a := (N:ℝ)^2/(80*Real.log (8*(N:ℝ)))
  have ha : 0≤a := by dsimp [a]; positivity
  have hsum := sum_le_sum (s := GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N))
    (fun p hp => show a^2≤(mobiusDivisorSelectionFibre (64*N^2)
      (mobiusDivisorSelectionPrimes (4*N)∪L) {p})^2 from by
      rw [middle_pool_persists hN L hL hp]
      have hfp : mobiusDivisorSelectionFibre (64*N^2) (mobiusDivisorSelectionPrimes (4*N)) {p}≤-a := by
        simpa only [a,neg_div] using hf p hp
      have hs := mul_nonneg (by linarith only [hfp] : 0≤ -mobiusDivisorSelectionFibre (64*N^2)
        (mobiusDivisorSelectionPrimes (4*N)) {p}-a)
        (by linarith only [hfp,ha] : 0≤ -mobiusDivisorSelectionFibre (64*N^2)
          (mobiusDivisorSelectionPrimes (4*N)) {p}+a)
      nlinarith only [hs])
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg a)
  have hsub : GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)⊆mobiusDivisorSelectionPrimes (64*N^2) := by
    intro p hp
    obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact mem_filter.mpr ⟨mem_range.mpr (by nlinarith),hpp⟩
  have hraw := (hm.trans hsum).trans (sum_mobiusDivisorSelectionSingleton_sq_le_energy _ _ _ hsub)
  have hd := div_le_div_of_nonneg_right hraw (sq_nonneg (((64*N^2:ℕ):ℝ)))
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have he : ((N:ℝ)/(2*Real.log (8*(N:ℝ)))*a^2)/((64*N^2:ℕ):ℝ)^2 =
      (N:ℝ)/(52428800*Real.log (8*(N:ℝ))^3) := by
    dsimp [a]
    push_cast
    field_simp
    ring
  rwa [he] at hd

private theorem middle_escape_rate :
    Tendsto (fun N : ℕ => (N:ℝ)/(52428800*Real.log (8*(N:ℝ))^3)) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x^3/x) atTop (𝓝 0) :=
    (Real.isLittleO_pow_log_id_atTop (n := 3)).tendsto_div_nhds_zero
  have hwithin : Tendsto (fun x : ℝ => Real.log x^3/x) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hzero
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (pow_pos (Real.log_pos hx) 3) (by linarith)
  have hr : Tendsto (fun x : ℝ => x/Real.log x^3) atTop atTop := by
    exact hwithin.inv_tendsto_nhdsGT_zero.congr (fun x => by
      change (Real.log x^3/x)⁻¹=x/Real.log x^3
      rw [inv_div])
  have hcast : Tendsto (fun N : ℕ => 8*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := (hr.comp hcast).const_mul_atTop (show (0:ℝ)<1/(8*52428800) by norm_num)
  convert h using 1
  funext N
  simp only [Function.comp_def]
  ring

/-- No fixed quadratic budget can contain increasing middle-prime processing, even after arbitrary interleavings of all scalar reserves above one eighth of the cutoff. -/
theorem eventually_mobiusDivisorMiddleEnergy_escape (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,∀ L : Finset ℕ,
      (∀ q∈L,q.Prime ∧ q<64*N^2 ∧ 64*N^2<8*q) →
      C*((64*N^2:ℕ):ℝ)^2<
        mobiusDivisorSelectionEnergy (64*N^2) (mobiusDivisorSelectionPrimes (4*N)∪L) := by
  filter_upwards [middle_escape_rate.eventually_gt_atTop C,eventually_mobiusDivisorMiddleEnergy_lower,
    eventually_ge_atTop (1:ℕ)] with N hrate hlower hN
  intro L hL
  have h := hrate.trans_le (hlower L hL)
  have hden : (0:ℝ)<((64*N^2:ℕ):ℝ)^2 := by positivity
  exact (lt_div_iff₀ hden).mp h
end RHTower
