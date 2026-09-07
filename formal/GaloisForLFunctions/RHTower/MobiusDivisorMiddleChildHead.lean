import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import GaloisForLFunctions.RHTower.MobiusDivisorSquareRootTerminalOrder
import GaloisForLFunctions.RHTower.MobiusDivisorHeadNeutralization
/-!
# Uniform child-head growth before middle-prime processing

At every child cutoff in [7N,8N], processing all primes below 4N leaves only
late singleton fibres. Their positive unsigned mass exceeds the complete
signed-source correction uniformly throughout this entire window. The proof
uses the corpus quantitative PNT and exact source identities, with no
numerical channel estimates.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem child_source_terminal {N K : ℕ} (hN : 1≤N) (hK : K≤8*N) :
    mobiusDivisorSmallSelectionPrimes K⊆mobiusDivisorSelectionPrimes (4*N) := by
  intro p hp
  obtain ⟨hp,hsmall⟩ := mem_filter.mp hp
  obtain ⟨hp,hprime⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨mem_range.mpr ?_,hprime⟩
  nlinarith

/-- A child cutoff through eight times the base has an exact complete-source plus late-mass head after the core below four times the base. -/
theorem mobiusDivisorMiddleChildHead_eq_total_add_tail {N K : ℕ} (hN : 1≤N) (hK : K≤8*N) :
    mobiusDivisorSelectionFibre K (mobiusDivisorSelectionPrimes (4*N)) ∅=
      (∑ d∈Icc 1 K,mobiusDivisorDilationChannel K d)+
      ∑ p∈mobiusDivisorSelectionPrimes K\mobiusDivisorSelectionPrimes (4*N),
        divisorUnsignedDilationChannel K p := by
  have hh := mobiusDivisorSelectionHead_add_terminal_leaves K _ (child_source_terminal hN hK)
  have he : (∑ p∈mobiusDivisorSelectionPrimes K\mobiusDivisorSelectionPrimes (4*N),
      mobiusDivisorSelectionFibre K (mobiusDivisorSelectionPrimes (4*N)) {p}) =
      -(∑ p∈mobiusDivisorSelectionPrimes K\mobiusDivisorSelectionPrimes (4*N),
        divisorUnsignedDilationChannel K p) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hpK,hpP⟩ := mem_sdiff.mp hp
    obtain ⟨hpK,hprime⟩ := mem_filter.mp hpK
    have hpLo : 4*N≤p := by
      by_contra hn
      exact hpP (mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩)
    rw [mobiusDivisorSelectionFibre_late_prime hprime (mem_range.mp hpK) (by omega)
      _ {p} hpP (mem_singleton_self p),if_pos rfl,
      mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hprime]
    push_cast
    ring
  linarith only [hh,he]

private theorem first_defect_floor : (1/10:ℝ)≤primeFreeDivisorDefect 1 := by
  have h := (harmonic_mascheroni_half_bounds (n := 4) (by norm_num)).2
  norm_num [harmonic,Finset.sum_range_succ,Real.log_four_eq] at h
  norm_num [primeFreeDivisorDefect]
  linarith [Real.log_two_lt_d9]

private theorem child_late_channel_floor {N K p : ℕ} (hN : 1≤N) (hKlo : 7*N≤K) (hKhi : K≤8*N)
    (hp : p∈GaloisForLFunctions.HTGeometry.primesInIoc (4*N) (5*N)) :
    Real.sqrt N/40≤divisorUnsignedDilationChannel K p := by
  obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  rw [divisorUnsignedDilationChannel_eq_first_block hprime.pos (by omega) (by omega)]
  have hsqK := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) K)
  have hsqp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
  have hKr : 7*(N:ℝ)≤K := by exact_mod_cast hKlo
  have hpr : (p:ℝ)≤5*N := by exact_mod_cast hhi
  have hrootK : (13/5:ℝ)*Real.sqrt N≤Real.sqrt K := by
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg (K:ℝ)]
  have hrootp : Real.sqrt p≤(23/10:ℝ)*Real.sqrt N := by
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg (p:ℝ)]
  have hgap : Real.sqrt N/4≤Real.sqrt K-Real.sqrt p := by
    nlinarith only [hrootK,hrootp,Real.sqrt_nonneg (N:ℝ)]
  have hm := mul_le_mul_of_nonneg_left first_defect_floor
    (show 0≤Real.sqrt K-Real.sqrt p from (by positivity : 0≤Real.sqrt N/4).trans hgap)
  nlinarith only [hgap,hm]

private theorem eventually_four_five_count :
    ∀ᶠ N : ℕ in atTop,(N:ℝ)/(2*Real.log (4*(N:ℝ)))≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (4*N) (5*N)).card := by
  have hcast : Tendsto (fun N : ℕ => 4*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hc := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
    (K := (5:ℝ)/4) (by norm_num))
  filter_upwards [hc] with N hc
  have he : (5/4:ℝ)*(4*(N:ℝ))=(5*N:ℕ) := by push_cast; ring
  have hf : 4*(N:ℝ)=(4*N:ℕ) := by push_cast; rfl
  rw [he,hf,Nat.floor_natCast,Nat.floor_natCast,
    ← GaloisForLFunctions.HTGeometry.card_primesInIoc (show 4*N≤5*N by omega)] at hc
  convert hc using 1; push_cast; ring

private theorem eventually_child_tail_floor :
    ∀ᶠ N : ℕ in atTop,∀ K : ℕ,7*N≤K → K≤8*N →
      (N:ℝ)*Real.sqrt N/(80*Real.log (4*(N:ℝ)))≤
        ∑ p∈mobiusDivisorSelectionPrimes K\mobiusDivisorSelectionPrimes (4*N),
          divisorUnsignedDilationChannel K p := by
  filter_upwards [eventually_four_five_count,eventually_ge_atTop (1:ℕ)] with N hc hN
  intro K hlo hhi
  have hsub : GaloisForLFunctions.HTGeometry.primesInIoc (4*N) (5*N)⊆
      mobiusDivisorSelectionPrimes K\mobiusDivisorSelectionPrimes (4*N) := by
    intro p hp
    obtain ⟨hprime,hpLo,hpHi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩,?_⟩
    intro hn
    have := mem_range.mp (mem_filter.mp hn).1
    omega
  have hsum := sum_le_sum (fun p hp => child_late_channel_floor hN hlo hhi hp)
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hc (show (0:ℝ)≤Real.sqrt N/40 by positivity)
  have hext := sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => divisorUnsignedDilationChannel_nonneg K p)
  calc
    _ = (N/(2*Real.log (4*(N:ℝ))))*(Real.sqrt N/40) := by ring
    _ ≤ _ := hm
    _ ≤ _ := hsum
    _ ≤ _ := hext

private theorem eventually_child_total_small :
    ∀ᶠ N : ℕ in atTop,∀ K : ℕ,7*N≤K → K≤8*N →
      |∑ d∈Icc 1 K,mobiusDivisorDilationChannel K d|≤
        (N:ℝ)*Real.sqrt N/(160*Real.log (4*(N:ℝ))) := by
  have hs := tendsto_sum_mobiusDivisorDilationChannel_log_normalized.abs.eventually
    (gt_mem_nhds (by norm_num : |(0:ℝ)|<1/3840))
  obtain ⟨K₀,hK₀⟩ := eventually_atTop.mp hs
  filter_upwards [eventually_ge_atTop (max K₀ 1)] with N hN
  have hN1 : 1≤N := (le_max_right _ _).trans hN
  intro K hlo hhi
  have hK0 : K₀≤K := by have := (le_max_left K₀ 1).trans hN; omega
  have hs := hK₀ K hK0
  have hKr : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hlogK : 0<Real.log K := Real.log_pos (by exact_mod_cast (show 1<K by omega))
  have hlogN : 0<Real.log (4*(N:ℝ)) := Real.log_pos (by exact_mod_cast (show 1<4*N by omega))
  rw [abs_div,abs_mul,abs_of_pos hlogK,abs_of_pos (mul_pos hKr (Real.sqrt_pos.mpr hKr))] at hs
  have hsraw := (div_lt_iff₀ (mul_pos hKr (Real.sqrt_pos.mpr hKr))).mp hs
  have hlog : Real.log (4*(N:ℝ))≤Real.log K := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast (show 4*N≤K by omega)
  have hslog := mul_le_mul_of_nonneg_left hlog (abs_nonneg (∑ d∈Icc 1 K,mobiusDivisorDilationChannel K d))
  have hK8 : (K:ℝ)≤8*N := by exact_mod_cast hhi
  have hroot : Real.sqrt K≤3*Real.sqrt N := by
    have hsqK := Real.sq_sqrt hKr.le
    have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    nlinarith [Real.sqrt_nonneg (K:ℝ),Real.sqrt_nonneg (N:ℝ)]
  have hnum := mul_le_mul hK8 hroot (Real.sqrt_nonneg (K:ℝ))
    (show (0:ℝ)≤8*N by positivity)
  apply (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<160) hlogN)).mpr
  nlinarith only [hsraw,hslog,hnum]

/-- The actual smaller retained heads have a uniform positive superlinear floor throughout the complete clipped quotient window. -/
theorem eventually_mobiusDivisorMiddleChildHead_lower :
    ∀ᶠ N : ℕ in atTop,∀ K : ℕ,7*N≤K → K≤8*N →
      (N:ℝ)*Real.sqrt N/(160*Real.log (4*(N:ℝ)))≤
        mobiusDivisorSelectionFibre K (mobiusDivisorSelectionPrimes (4*N)) ∅ := by
  filter_upwards [eventually_child_tail_floor,eventually_child_total_small,
    eventually_ge_atTop (1:ℕ)] with N htail htotal hN
  intro K hlo hhi
  rw [mobiusDivisorMiddleChildHead_eq_total_add_tail hN hhi]
  have hT := htail K hlo hhi
  have hS := htotal K hlo hhi
  have habs := neg_abs_le (∑ d∈Icc 1 K,mobiusDivisorDilationChannel K d)
  have he : (N:ℝ)*Real.sqrt N/(80*Real.log (4*(N:ℝ)))=
      2*((N:ℝ)*Real.sqrt N/(160*Real.log (4*(N:ℝ)))) := by ring
  rw [he] at hT
  linarith only [hT,hS,habs]
end RHTower
