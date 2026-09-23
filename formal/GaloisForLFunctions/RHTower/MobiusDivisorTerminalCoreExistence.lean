import GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import GaloisForLFunctions.RHTower.MobiusDivisorTerminalBudgetRecovery
/-!
# Unconditional small-energy terminal cores from actual signed windows

Quantitative PNT makes the complete signed aggregate smaller than either
reserved source mass. Processing the complement of the positive quotient-seven
window and negative late window leaves a head inside their cancellation
interval. A finite actual source cover makes the head square-root sized;
prime density controls the full successor envelope.

Every prime outside those two windows is processed. No initial energy premise,
source availability premise, or numerical certificate enters the theorem.
A uniformly bounded path reaching this core and the final signed endpoint
bound remain separate obligations.
-/
noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem positive_window_covers_total (b : ℕ) (hb : 8 ≤ b) (c : ℝ) (hc : 0 < c)
    (hf : ∀ N p : ℕ,p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N) →
      c*Real.sqrt N ≤ mobiusDivisorSelectionFibre (7*(b+1)*N)
        (mobiusDivisorSelectionPrimes 8) {p}) :
    ∀ᶠ N : ℕ in atTop,
      |∑ d ∈ Icc 1 (7*(b+1)*N),mobiusDivisorDilationChannel (7*(b+1)*N) d| ≤
        ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N),
          mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p} := by
  let K : ℝ := 7*((b:ℝ)+1)
  have hK : 0 < K := by dsimp [K]; positivity
  have hbR : (0:ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hscale : Tendsto (fun N : ℕ => 7*(b+1)*N) atTop atTop :=
    tendsto_atTop_mono (fun N : ℕ => show N ≤ 7*(b+1)*N by nlinarith) tendsto_id
  have hlim := (tendsto_sum_mobiusDivisorDilationChannel_log_normalized.comp hscale).abs
  have hδ : 0 < c/(2*K*Real.sqrt K) := by positivity
  have hsmall := hlim.eventually (eventually_lt_nhds (by simpa using hδ))
  have hratio : (1:ℝ) < ((b:ℝ)+1)/b := by rw [lt_div_iff₀ hbR]; linarith
  have hcast : Tendsto (fun N : ℕ => (b:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbR
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hratio)
  filter_upwards [hsmall,hcount,eventually_ge_atTop (1:ℕ)] with N hsmall hcount hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have harg : (((b:ℝ)+1)/b)*((b:ℝ)*N)=((b+1)*N:ℕ) := by push_cast; field_simp
  have hbN : (b:ℝ)*N=(b*N:ℕ) := by push_cast; rfl
  rw [harg,hbN,Nat.floor_natCast,Nat.floor_natCast] at hcount
  rw [← GaloisForLFunctions.HTGeometry.card_primesInIoc
    (show b*N ≤ (b+1)*N by nlinarith)] at hcount
  have hsum := sum_le_sum (fun p hp => hf N p hp)
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hraw := (mul_le_mul_of_nonneg_right hcount
    (mul_nonneg hc.le (Real.sqrt_nonneg (N:ℝ)))).trans hsum
  have hraw' : c*(N:ℝ)*Real.sqrt N/(2*Real.log ((b:ℝ)*N)) ≤
      ∑ p ∈ GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N),
        mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p} := by
    convert hraw using 1 <;> first | rfl | (push_cast; field_simp; ring)
  have hMcast : ((7*(b+1)*N:ℕ):ℝ)=K*N := by dsimp [K]; push_cast; ring
  have hroot : Real.sqrt (7*(b+1)*N:ℕ)=Real.sqrt K*Real.sqrt N := by
    rw [hMcast,Real.sqrt_mul hK.le]
  have hbN1 : (1:ℝ) < (b:ℝ)*N := by
    have hb8 : (8:ℝ) ≤ b := by exact_mod_cast hb
    have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  have hlogb := Real.log_pos hbN1
  have hlogmono : Real.log ((b:ℝ)*N) ≤ Real.log (7*(b+1)*N:ℕ) := by
    apply Real.log_le_log (by positivity)
    rw [hMcast]
    dsimp [K]
    nlinarith
  have hlogM := hlogb.trans_le hlogmono
  have hMR : (0:ℝ) < (7*(b+1)*N:ℕ) := by rw [hMcast]; positivity
  dsimp only [Function.comp_def] at hsmall
  rw [abs_div,abs_mul,abs_of_pos hlogM,
    abs_of_pos (mul_pos hMR (Real.sqrt_pos.mpr hMR))] at hsmall
  have ht : |∑ d ∈ Icc 1 (7*(b+1)*N),mobiusDivisorDilationChannel (7*(b+1)*N) d| ≤
      (c/(2*K*Real.sqrt K))*((7*(b+1)*N:ℕ)*Real.sqrt (7*(b+1)*N:ℕ))/
        Real.log (7*(b+1)*N:ℕ) := by
    apply (le_div_iff₀ hlogM).mpr
    exact ((div_lt_iff₀ (mul_pos hMR (Real.sqrt_pos.mpr hMR))).mp hsmall).le
  have heq : (c/(2*K*Real.sqrt K))*((7*(b+1)*N:ℕ)*Real.sqrt (7*(b+1)*N:ℕ))/
      Real.log (7*(b+1)*N:ℕ) = c*(N:ℝ)*Real.sqrt N/(2*Real.log (7*(b+1)*N:ℕ)) := by
    rw [hroot,hMcast]
    field_simp
  have hd := div_le_div_of_nonneg_left (show 0 ≤ c*(N:ℝ)*Real.sqrt N by positivity)
    (show 0 < 2*Real.log ((b:ℝ)*N) by positivity) (by linarith :
      2*Real.log ((b:ℝ)*N) ≤ 2*Real.log (7*(b+1)*N:ℕ))
  exact (ht.trans_eq heq).trans (hd.trans hraw')

private theorem late_covers_total :
    ∀ᶠ N : ℕ in atTop,
      |∑ d ∈ Icc 1 (4*N),mobiusDivisorDilationChannel (4*N) d| ≤ mobiusDivisorLatePrimeMass (4*N) := by
  have hh := tendsto_total_div_mobiusDivisorLatePrimeMass.abs.eventually
    (eventually_lt_nhds (by norm_num : |(0:ℝ)| < 1))
  filter_upwards [hh,eventually_mobiusDivisorLatePrimeMass_ge,eventually_ge_atTop (1:ℕ)] with N hh hmass hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log (2*(N:ℝ)) := Real.log_pos (by linarith)
  have hpos : 0 < mobiusDivisorLatePrimeMass (4*N) :=
    (show (0:ℝ) < (N:ℝ)*Real.sqrt N/(80*Real.log (2*(N:ℝ))) by positivity).trans_le hmass
  rw [abs_div,abs_of_pos hpos] at hh
  simpa using ((div_lt_iff₀ hpos).mp hh).le

private theorem isolated_singleton_eq (M : ℕ) (P Q : Finset ℕ) {p : ℕ}
    (hp : p.Prime) (hpP : p ∉ P) (hpQ : p ∉ Q)
    (hP : mobiusDivisorSelectionPrimes (M/p+1) ⊆ P)
    (hQ : mobiusDivisorSelectionPrimes (M/p+1) ⊆ Q) :
    mobiusDivisorSelectionFibre M P {p}=mobiusDivisorSelectionFibre M Q {p} := by
  have hmono : mobiusDivisorSelectionPrimes (M/p) ⊆ mobiusDivisorSelectionPrimes (M/p+1) := by
    intro q hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hq; omega),hprime⟩
  rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hp M P ∅ hpP (notMem_empty _),
    mobiusDivisorSelectionFibre_prime_interpolation hp M Q ∅ hpQ (notMem_empty _)]
  rw [mobiusDivisorInterpolatedFibre,mobiusDivisorInterpolatedFibre,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed _ P _ (hmono.trans hP),
    mobiusDivisorSelectionFibre_of_all_source_primes_processed _ P _ hP,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed _ Q _ (hmono.trans hQ),
    mobiusDivisorSelectionFibre_of_all_source_primes_processed _ Q _ hQ]

/-- An unconditional actual terminal core processes every prime outside two macroscopic signed windows, with arbitrarily small quadratic successor envelope. This asserts an endpoint, not a bounded order reaching it. -/
theorem exists_mobiusDivisorSmallTerminalCore :
    ∃ b : ℕ,8 ≤ b ∧ ∀ ε : ℝ,0 < ε → ∀ᶠ N : ℕ in atTop,
      let M := 7*(b+1)*(4*N)
      let A := GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N))
      let B := mobiusDivisorActiveLatePrimes M
      ∃ P ⊆ mobiusDivisorSelectionPrimes M,
        mobiusDivisorSelectionPrimes M \ (A ∪ B) ⊆ P ∧
        mobiusDivisorSmallSelectionPrimes M ⊆ P ∧
        |mobiusDivisorSelectionFibre M P ∅| ≤ 5*Real.sqrt M ∧
        mobiusDivisorSuccessorEnvelope M P ≤ ε*(M:ℝ)^(2 : ℕ) := by
  obtain ⟨b,hb,c,hc,hfloor⟩ := exists_mobiusDivisorPositivePrimeWindow
  refine ⟨b,hb,fun ε hε => ?_⟩
  have hfour : Tendsto (fun N : ℕ => 4*N) atTop atTop :=
    tendsto_atTop_mono (fun N : ℕ => show N ≤ 4*N by omega) tendsto_id
  have hscale : Tendsto (fun N : ℕ => 7*(b+1)*N) atTop atTop :=
    tendsto_atTop_mono (fun N : ℕ => show N ≤ 7*(b+1)*N by nlinarith) tendsto_id
  have hMscale : Tendsto (fun N : ℕ => 7*(b+1)*(4*N)) atTop atTop := hscale.comp hfour
  have hpos := hfour.eventually (positive_window_covers_total b hb c hc hfloor)
  have hneg := hscale.eventually late_covers_total
  have henergy := hMscale.eventually (eventually_mobiusDivisor_terminal_envelope_small 7 5 ε (by norm_num) hε)
  filter_upwards [hpos,hneg,henergy,eventually_ge_atTop (1:ℕ)] with N hpos hneg henergy hN
  let M := 7*(b+1)*(4*N)
  let A := GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N))
  let B := mobiusDivisorActiveLatePrimes M
  let U := A ∪ B
  let P := mobiusDivisorSelectionPrimes M \ U
  change ∃ Q ⊆ mobiusDivisorSelectionPrimes M,P ⊆ Q ∧ _
  have hM64 : 64 ≤ M := by dsimp [M]; nlinarith
  have hAdata : ∀ p ∈ A,p.Prime ∧ p < M ∧ 8 ≤ p ∧ M < 8*p := by
    intro p hp
    obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact ⟨hpp,by dsimp [M]; nlinarith,by nlinarith,by dsimp [M]; nlinarith⟩
  have hBdata : ∀ p ∈ B,p.Prime ∧ p < M ∧ 8 ≤ p ∧ M < 8*p := by
    intro p hp
    obtain ⟨hpp,hpM,h2p⟩ := mem_mobiusDivisorActiveLatePrimes hp
    exact ⟨hpp,hpM,by omega,by omega⟩
  have hUdata : ∀ p ∈ U,p.Prime ∧ p < M ∧ 8 ≤ p ∧ M < 8*p := by
    intro p hp
    rcases mem_union.mp hp with hp|hp
    · exact hAdata p hp
    · exact hBdata p hp
  have hUsub : U ⊆ mobiusDivisorSelectionPrimes M := by
    intro p hp
    exact mem_filter.mpr ⟨mem_range.mpr (hUdata p hp).2.1,(hUdata p hp).1⟩
  have hremaining : mobiusDivisorSelectionPrimes M \ P=U := by
    change mobiusDivisorSelectionPrimes M \ (mobiusDivisorSelectionPrimes M \ U)=U
    apply Finset.ext
    intro p
    rw [Finset.mem_sdiff,Finset.mem_sdiff]
    constructor
    · rintro ⟨hp,hn⟩
      by_contra hnU
      exact hn ⟨hp,hnU⟩
    · intro hp
      exact ⟨hUsub hp,fun h => h.2 hp⟩
  have hfront : ∀ p ∈ mobiusDivisorSelectionPrimes M \ P,M/p ≤ 7 := by
    rw [hremaining]
    intro p hp
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (hUdata p hp).1.pos).mpr (hUdata p hp).2.2.2)
  have hterminal := mobiusDivisorSmallSelectionPrimes_subset_of_quotient M 7 P (by norm_num; exact hM64) hfront
  have hcore : mobiusDivisorSelectionPrimes 8 ⊆ P := by
    intro p hp
    obtain ⟨hpr,hprime⟩ := mem_filter.mp hp
    have hp8 := mem_range.mp hpr
    exact mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),hprime⟩,
      fun h => by have := (hUdata p h).2.2.1; omega⟩
  have hfree : ∀ p ∈ U,p ∉ P := by intro p hp h; exact (mem_sdiff.mp h).2 hp
  have hposcoef : ∀ p ∈ A,mobiusDivisorSelectionFibre M P {p}=
      mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) {p} := by
    intro p hp
    have hd := hAdata p hp
    exact isolated_singleton_eq M P _ hd.1 (hfree p (mem_union_left _ hp))
      (fun h => by have := mem_range.mp (mem_filter.mp h).1; omega)
      (mobiusDivisorPrime_isolated_after_eight M P hcore hd.1 hd.2.2.2)
      (mobiusDivisorPrime_isolated_after_eight M _ Subset.rfl hd.1 hd.2.2.2)
  have hnegcoef : ∀ p ∈ B,mobiusDivisorSelectionFibre M P {p} = -divisorUnsignedDilationChannel M p := by
    intro p hp
    obtain ⟨hpp,hpM,h2p⟩ := mem_mobiusDivisorActiveLatePrimes hp
    rw [mobiusDivisorSelectionFibre_late_prime hpp hpM h2p _ {p}
      (hfree p (mem_union_right _ hp)) (mem_singleton_self p),if_pos rfl,
      mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hpp]
    push_cast
    ring
  have hnegmass : (∑ p ∈ B,mobiusDivisorSelectionFibre M P {p}) = -mobiusDivisorLatePrimeMass M := by
    rw [← sum_mobiusDivisorActiveLatePrimes M,← sum_neg_distrib]
    exact sum_congr rfl hnegcoef
  have hposmass : (∑ p ∈ A,mobiusDivisorSelectionFibre M P {p}) =
      ∑ p ∈ A,mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) {p} := sum_congr rfl hposcoef
  have hdis : Disjoint A B := by
    apply disjoint_left.mpr
    intro p hpA hpB
    have hhi := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpA).2.2
    have h2p := (mem_mobiusDivisorActiveLatePrimes hpB).2.2
    dsimp [M] at h2p
    nlinarith
  have hhead := mobiusDivisorSelectionHead_add_terminal_leaves M P hterminal
  rw [hremaining,sum_union hdis,hnegmass] at hhead
  have hMswap : 4*(7*(b+1)*N)=M := by dsimp [M]; ring
  rw [hMswap] at hneg
  change |∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d| ≤ _ at hpos
  rw [← hposmass] at hpos
  have hcovA : -mobiusDivisorSelectionFibre M P ∅ ≤ ∑ p ∈ A,mobiusDivisorSelectionFibre M P {p} := by
    have ht := (abs_le.mp hneg).1
    linarith only [hhead,ht]
  have hcovB : mobiusDivisorSelectionFibre M P ∅ ≤ ∑ p ∈ B,-mobiusDivisorSelectionFibre M P {p} := by
    rw [sum_neg_distrib,hnegmass,neg_neg]
    have ht := (abs_le.mp hpos).2
    linarith only [hhead,ht]
  have hbound : ∀ p ∈ U, |mobiusDivisorSelectionFibre M P {p}| ≤ 5*Real.sqrt M := by
    intro p hp
    have hs := (single_le_sum (fun R (_ : R ∈ ((mobiusDivisorSelectionPrimes M).erase p).powerset) =>
      abs_nonneg (mobiusDivisorSelectionFibre M P (insert p R)))
      (mem_powerset.mpr (empty_subset _))).trans
        (sum_abs_mobiusDivisorPrimeFibre_le_quotient M P (hUdata p hp).1)
    simp only [insert_empty_eq] at hs
    have hq : ((M/p:ℕ):ℝ) ≤ 7 := by exact_mod_cast hfront p (hremaining.symm ▸ hp)
    nlinarith [Real.sqrt_nonneg (M:ℝ)]
  obtain ⟨L,hLU,hheadSmall⟩ := exists_signedScalarHeadCover A B
    (fun p => mobiusDivisorSelectionFibre M P {p}) (mobiusDivisorSelectionFibre M P ∅)
    (5*Real.sqrt M) (by positivity)
    (fun p hp => ⟨by rw [hposcoef p hp]; exact (mul_nonneg hc.le (Real.sqrt_nonneg (4*N:ℕ))).trans (hfloor (4*N) p hp),
      (le_abs_self _).trans (hbound p (mem_union_left _ hp))⟩)
    (fun p hp => ⟨by rw [hnegcoef p hp,neg_neg]; exact divisorUnsignedDilationChannel_nonneg M p,
      (neg_le_abs _).trans (hbound p (mem_union_right _ hp))⟩) hcovA hcovB
  have hsmall : |mobiusDivisorSelectionFibre M (P ∪ L) ∅| ≤ 5*Real.sqrt M := by
    rwa [mobiusDivisorSelectionHead_union_terminal M P L hterminal]
  refine ⟨P ∪ L,union_subset sdiff_subset (hLU.trans hUsub),subset_union_left,
    hterminal.trans subset_union_left,hsmall,?_⟩
  apply henergy (P ∪ L) _ hsmall
  intro p hp
  apply hfront p
  exact mem_sdiff.mpr ⟨(mem_sdiff.mp hp).1,fun h => (mem_sdiff.mp hp).2 (mem_union_left _ h)⟩

end RHTower
