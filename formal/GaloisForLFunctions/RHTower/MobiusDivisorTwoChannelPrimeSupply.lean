import GaloisForLFunctions.RHTower.MobiusDivisorTwoChannelPrimeBlocks
import GaloisForLFunctions.RHTower.DivisorUniformSquareRootBound

/-!
# Actual prime supply for an interacting initial block

The corpus prime-window theorem supplies enough primes in `(8N,9N]`.
At cutoff `20N`, each has an analytic positive source floor and also changes
the cofactor-two fibre. A nonempty finite selection respects the original head
budget and leaves head at most `sqrt(20N)/15`. The two-channel block theorem
then controls every retained sign, complete and nonempty energies, and every
available one-prime extension at every intermediate subset.

No prime list, saved channel value, or numerical experiment enters the proof.
The result supplies a selected initial block; it does not consume every prime
or establish sign preservation after an arbitrary further small prime.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower


private theorem eventually_two_channel_window_count :
    ∀ᶠ N : ℕ in atTop,(700:ℝ) ≤
      (GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)).card := by
  have hcast : Tendsto (fun N : ℕ => 8*(N:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge
    (K := (9:ℝ)/8) (by norm_num))
  filter_upwards [hcount,eventually_ge_atTop (22400^2:ℕ)] with N hc hN
  have harg : (9/8:ℝ)*(8*(N:ℝ))=(9*N:ℕ) := by push_cast; ring
  have height : 8*(N:ℝ)=((8*N:ℕ):ℝ) := by push_cast; rfl
  rw [harg,height,Nat.floor_natCast,Nat.floor_natCast] at hc
  rw [← GaloisForLFunctions.HTGeometry.card_primesInIoc (show 8*N≤9*N by omega)] at hc
  have hx1 : (1:ℝ)<(8*N:ℕ) := by exact_mod_cast (show 1<8*N by omega)
  have hx0 : (0:ℝ)<(8*N:ℕ) := by linarith only [hx1]
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at hl
  have hsq := Real.sq_sqrt hx0.le
  have hroot0 := Real.sqrt_nonneg ((8*N:ℕ):ℝ)
  have hroot : (22400:ℝ)≤Real.sqrt (8*N:ℕ) := by
    have hn : (22400:ℝ)^2≤(8*N:ℕ) := by
      exact_mod_cast (show 22400^2≤8*N from hN.trans (by omega))
    nlinarith only [hn,hsq,hroot0]
  have hdiv : Real.sqrt (8*N:ℕ)/2≤((8*N:ℕ):ℝ)/Real.log (8*N:ℕ) := by
    rw [le_div_iff₀ (Real.log_pos hx1)]
    have hm := mul_le_mul_of_nonneg_left hl hroot0
    nlinarith only [hm,hsq,hroot0]
  nlinarith only [hc,hdiv,hroot]

/-- Every prime in the inner two-channel window carries a uniform analytic square-root mass floor. -/
theorem divisorUnsignedDilationChannel_two_channel_window_lower {N p : ℕ}
    (hp : p∈GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)) :
    Real.sqrt N/20 ≤ divisorUnsignedDilationChannel (20*N) p := by
  obtain ⟨hprime,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hs := divisorUnsignedDilationChannel_second_block_lower hprime.pos
    (M := 20*N) (by omega) (by omega)
  have hroot : 2*Real.sqrt N≤Real.sqrt p := by
    have hsqN := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have hsqp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
    have h4 : 4*(N:ℝ)≤p := by exact_mod_cast (show 4*N≤p by omega)
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg (p:ℝ)]
  linarith only [hs,hroot]

/-- The actual prime window eventually supplies enough unsigned mass to cover the entire original head. -/
theorem eventually_two_channel_window_covers_unit_source :
    ∀ᶠ N : ℕ in atTop,divisorUnsignedDilationChannel (20*N) 1 ≤
      ∑ p∈GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N),
        divisorUnsignedDilationChannel (20*N) p := by
  filter_upwards [eventually_two_channel_window_count] with N hc
  have hsum := sum_le_sum (fun p hp => divisorUnsignedDilationChannel_two_channel_window_lower (N := N) hp)
  simp only [sum_const,nsmul_eq_mul] at hsum
  have hm := mul_le_mul_of_nonneg_right hc (show 0≤Real.sqrt N/20 by positivity)
  have hu := divisorUnsignedDilationChannel_one_le_seven_sqrt (20*N)
  have hr : Real.sqrt (20*N:ℕ)≤5*Real.sqrt N := by
    have hn := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) N)
    have h20 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (20*N))
    have hb : ((20*N:ℕ):ℝ)≤25*(N:ℝ) := by push_cast; have := Nat.cast_nonneg (α := ℝ) N; linarith
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.sqrt_nonneg ((20*N:ℕ):ℝ)]
  nlinarith only [hsum,hm,hu,hr]

private theorem exists_nonempty_mass_cover_below {α : Type*} [DecidableEq α]
    (U : Finset α) (w : α → ℝ) (a h : ℝ) (ha : 0≤a) (hU : U.Nonempty) (hah : a≤h)
    (hw : ∀ p∈U,0≤w p ∧ w p≤a) (hcover : h≤∑ p∈U,w p) :
    ∃ L⊆U,L.Nonempty ∧ 0≤h-(∑ p∈L,w p) ∧ h-(∑ p∈L,w p)≤a := by
  obtain ⟨p,hp⟩ := hU
  have hs := sum_erase_add U w hp
  have hrest : h-w p≤∑ q∈U.erase p,w q := by linarith only [hs,hcover]
  obtain ⟨L,hLU,h0,h1⟩ := exists_mass_cover_below_with_bounded_residual
    (U.erase p) w a (h-w p) ha (by linarith only [(hw p hp).2,hah])
    (fun q hq => hw q (mem_erase.mp hq).2) hrest
  have hpL : p∉L := fun h => (notMem_erase p U) (hLU h)
  refine ⟨insert p L,insert_subset hp (hLU.trans (erase_subset p U)),insert_nonempty _ _,?_,?_⟩
  · rw [sum_insert hpL]
    linarith only [h0]
  · rw [sum_insert hpL]
    linarith only [h1]

/-- Unconditionally, a nonempty initial block reduces the head and the cofactor-two reserve while preserving all retained signs and both energy ceilings at every subset. -/
theorem eventually_exists_mobiusDivisorTwoChannelPrimeBlock :
    ∀ᶠ N : ℕ in atTop,∃ L⊆GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N),
      L.Nonempty ∧
      (0 ≤ mobiusDivisorSelectionFibre (20*N) L ∅ ∧
        mobiusDivisorSelectionFibre (20*N) L ∅≤Real.sqrt (20*N:ℕ)/15) ∧
      (0 ≤ mobiusDivisorOrientedFibre (20*N) L {2} ∧
        mobiusDivisorOrientedFibre (20*N) L {2}<divisorUnsignedDilationChannel (20*N) 2) ∧
      mobiusDivisorSelectionEnergy (20*N) L ≤
        mobiusDivisorNonemptyEnergy (20*N) ∅+((20*N:ℕ):ℝ)/225 ∧
      ∀ P⊆L,
        (∀ R : Finset ℕ,0 ≤ mobiusDivisorOrientedFibre (20*N) P R) ∧
        mobiusDivisorSelectionEnergy (20*N) P ≤ mobiusDivisorSelectionEnergy (20*N) ∅ ∧
        mobiusDivisorNonemptyEnergy (20*N) P ≤ mobiusDivisorNonemptyEnergy (20*N) ∅ ∧
        ∀ q : ℕ,q.Prime → q<20*N → q∉P →
          mobiusDivisorSelectionEnergy (20*N) (insert q P) ≤ mobiusDivisorSelectionEnergy (20*N) P := by
  obtain ⟨M₀,hblocks⟩ := exists_mobiusDivisorTwoChannelBlockParity
  obtain ⟨T,hfloor⟩ := eventually_atTop.mp eventually_divisorUnsignedDilationChannel_one_ge_fifteenth
  filter_upwards [eventually_two_channel_window_count,eventually_two_channel_window_covers_unit_source,
    eventually_ge_atTop (max (max M₀ T) 1)] with N hc hcover hN
  have hN1 : 1≤N := (le_max_right _ _).trans hN
  have hM0 : M₀≤20*N := by have := (le_max_left (max M₀ T) 1).trans hN; omega
  have hT : T≤20*N := by have := (le_max_left (max M₀ T) 1).trans hN; omega
  let U := GaloisForLFunctions.HTGeometry.primesInIoc (8*N) (9*N)
  have hU : ∀ p∈U,p.Prime ∧ p<20*N ∧ 2*(20*N)≤5*p := by
    intro p hp
    obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    exact ⟨hpp,by omega,by omega⟩
  have hUn : U.Nonempty := by
    apply card_pos.mp
    have hcard : (0:ℝ)<U.card := by dsimp [U]; linarith only [hc]
    exact_mod_cast hcard
  have hweights : ∀ p∈U,0≤divisorUnsignedDilationChannel (20*N) p ∧
      divisorUnsignedDilationChannel (20*N) p≤Real.sqrt (20*N:ℕ)/15 := by
    intro p hp
    exact ⟨divisorUnsignedDilationChannel_nonneg _ _,
      divisorUnsignedDilationChannel_le_fifteenth_of_le_five_mul (hU p hp).1.pos
        (by have := (hU p hp).2.2; omega)⟩
  obtain ⟨L,hLU,hLn,h0,h1⟩ := exists_nonempty_mass_cover_below U
    (divisorUnsignedDilationChannel (20*N)) (Real.sqrt (20*N:ℕ)/15)
    (divisorUnsignedDilationChannel (20*N) 1) (by positivity) hUn (hfloor _ hT) hweights hcover
  have hL : ∀ p∈L,p.Prime ∧ p<20*N ∧ 2*(20*N)≤5*p := fun p hp => hU p (hLU hp)
  have hbudget : (∑ p∈L,divisorUnsignedDilationChannel (20*N) p)≤
      divisorUnsignedDilationChannel (20*N) 1 := by linarith only [h0]
  have hblock := hblocks (20*N) hM0 L hL hbudget
  have hpair : ∀ p∈L,∀ q∈L,p≠q → 20*N≤p*q := by
    intro p hp q hq _
    have hpw := GaloisForLFunctions.HTGeometry.mem_primesInIoc (hLU hp)
    have hqw := GaloisForLFunctions.HTGeometry.mem_primesInIoc (hLU hq)
    have hq3 : 3≤q := by omega
    nlinarith only [hpw.2.1,hq3]
  have hhead : mobiusDivisorSelectionFibre (20*N) L ∅ = divisorUnsignedDilationChannel (20*N) 1-
      ∑ p∈L,divisorUnsignedDilationChannel (20*N) p := by
    simpa only [mobiusDivisorOrientedFibre,card_empty,pow_zero,one_mul,prod_empty,Nat.mul_one] using
      mobiusDivisorOrientedFibre_sparse_prime_block (20*N) L ∅ (fun p hp => (hL p hp).1)
        hpair (by simp) (by simp)
  rw [← hhead] at h0 h1
  have h2L : 2∉L := by
    intro h
    have hw := GaloisForLFunctions.HTGeometry.mem_primesInIoc (hLU h)
    omega
  have htwo : mobiusDivisorOrientedFibre (20*N) L {2}=divisorUnsignedDilationChannel (20*N) 2-
      ∑ p∈L,divisorUnsignedDilationChannel (20*N) (p*2) := by
    simpa only [prod_singleton] using
      mobiusDivisorOrientedFibre_sparse_prime_block (20*N) L {2} (fun p hp => (hL p hp).1)
        hpair (by norm_num) (by simpa using h2L)
  have hdrop : 0<∑ p∈L,divisorUnsignedDilationChannel (20*N) (p*2) := by
    apply sum_pos _ hLn
    intro p hp
    have hpw := GaloisForLFunctions.HTGeometry.mem_primesInIoc (hLU hp)
    have hpM : p*2<20*N := by omega
    rw [divisorUnsignedDilationChannel_eq_first_block (by have := hpw.1.pos; omega) hpM (by omega)]
    apply mul_pos
    · exact sub_pos.mpr (Real.sqrt_lt_sqrt (by positivity) (by exact_mod_cast hpM))
    · have hg := Real.one_half_lt_eulerMascheroniConstant
      norm_num [primeFreeDivisorDefect]
      linarith only [hg]
  have hsquare : (mobiusDivisorSelectionFibre (20*N) L ∅)^2≤((20*N:ℕ):ℝ)/225 := by
    have hm := mul_nonneg (sub_nonneg.mpr h1) (add_nonneg h0 (by positivity : 0≤Real.sqrt (20*N:ℕ)/15))
    have hs := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (20*N))
    nlinarith only [hm,hs]
  have hall := hblock L (Subset.refl _)
  refine ⟨L,hLU,hLn,⟨h0,h1⟩,⟨(hall.1 {2}).1,?_⟩,?_,?_⟩
  · rw [htwo]
    linarith only [hdrop]
  · have hn := hall.2.2.1
    unfold mobiusDivisorNonemptyEnergy at hn ⊢
    linarith only [hn,hsquare]
  · intro P hPL
    have hb := hblock P hPL
    exact ⟨fun R => (hb.1 R).1,hb.2.1,hb.2.2.1,hb.2.2.2⟩

end RHTower
