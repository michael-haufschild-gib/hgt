import GaloisForLFunctions.RHTower.MobiusDivisorPositivePrimeSupply
import GaloisForLFunctions.RHTower.MobiusDivisorSignedPrimeBatches
/-!
# Actual growing batches of both retained prime signs

After the fixed prime core below eight, the positive quotient-seven window
and the negative late window both have superlinear mass. Matching selected
subpools and retaining their removed-square reserve gives an unconditional
complete batch order with one uniform quadratic energy bound. The remaining
middle primes are not consumed, so this does not prove RH or SD1.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem fixed_core_head_bound {M : ℕ} (hM : 8≤M) :
    |mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) ∅|≤184832*(M:ℝ) := by
  have he := mobiusDivisorSelectionEnergy_small_core_le M hM (mobiusDivisorSelectionPrimes 8) Subset.rfl
  have hn := mobiusDivisorNonemptyEnergy_nonneg M (mobiusDivisorSelectionPrimes 8)
  unfold mobiusDivisorNonemptyEnergy at hn
  have hc : (2:ℝ)^(8 : ℕ)*722=184832 := by norm_num
  rw [hc] at he
  nlinarith only [he,hn,sq_abs (mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) ∅),
    abs_nonneg (mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) ∅),
    Nat.cast_nonneg (α := ℝ) M,sq_nonneg (M:ℝ)]

private theorem late_pool_at_scaled_cutoff {b N : ℕ} (hb : 8≤b) (hN : 1≤N) :
    let M := 7*(b+1)*(4*N)
    ∀ p∈GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M,
      p.Prime ∧ p<M ∧ p∉mobiusDivisorSelectionPrimes 8 ∧ M<8*p ∧
      mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) {p}=
        -divisorUnsignedDilationChannel M p := by
  dsimp only
  intro p hp
  obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hM16 : 16≤7*(b+1)*(4*N) := by nlinarith
  have hlate : 7*(b+1)*(4*N)≤2*p := by omega
  have h8p : 8<p := by omega
  have hpP : p∉mobiusDivisorSelectionPrimes 8 := by
    intro hp
    have := mem_range.mp (mem_filter.mp hp).1
    omega
  have hnotprime : ¬(7*(b+1)*(4*N)).Prime :=
    Nat.not_prime_mul (by omega : 7*(b+1)≠1) (by omega : 4*N≠1)
  have hpM : p<7*(b+1)*(4*N) := lt_of_le_of_ne hhi (fun h => hnotprime (h ▸ hpp))
  refine ⟨hpp,hpM,hpP,by omega,?_⟩
  rw [mobiusDivisorSelectionFibre_late_prime hpp hpM hlate _ {p} hpP (mem_singleton_self p),if_pos rfl,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,ArithmeticFunction.moebius_apply_prime hpp]
  push_cast
  ring

/-- Unconditionally, growing matched batches consume arbitrarily many linear units of both signed source masses while every prefix stays under one fixed quadratic energy ceiling. The middle primes need not yet be processed. -/
theorem exists_mobiusDivisorGrowingSignedPrimeBatches :
    ∃ b : ℕ,8≤b ∧ ∀ T : ℝ,∀ᶠ N : ℕ in atTop,
      let M := 7*(b+1)*(4*N)
      ∃ L⊆GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N)),
      ∃ R⊆GaloisForLFunctions.HTGeometry.primesInIoc (M/2) M,
        (T*(M:ℝ)≤∑ p∈L,mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) {p}) ∧
        (T*(M:ℝ)≤∑ p∈R,-mobiusDivisorSelectionFibre M (mobiusDivisorSelectionPrimes 8) {p}) ∧
        ∃ l : List ℕ,l.Nodup ∧ l.toFinset=L∪R ∧ ∀ k : ℕ,
          mobiusDivisorSelectionEnergy M (mobiusDivisorSelectionPrimes 8∪(l.take k).toFinset)≤
            (2:ℝ)^(8 : ℕ)*722*(M:ℝ)^(2 : ℕ) := by
  obtain ⟨b,hb,c,hc,hfloor,hpositive⟩ := exists_mobiusDivisorPositivePrimeWindow_mass_atTop
  refine ⟨b,hb,fun T => ?_⟩
  let M := fun N : ℕ => 7*(b+1)*(4*N)
  let A := fun N : ℕ => GaloisForLFunctions.HTGeometry.primesInIoc (b*(4*N)) ((b+1)*(4*N))
  let B := fun N : ℕ => GaloisForLFunctions.HTGeometry.primesInIoc (M N/2) (M N)
  let pos := fun N : ℕ => ∑ p∈A N,mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) {p}
  let neg := fun N : ℕ => ∑ p∈B N,-mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) {p}
  have hfour : Tendsto (fun N : ℕ => 4*N) atTop atTop :=
    tendsto_atTop_mono' _ (Filter.Eventually.of_forall (fun N => by omega : ∀ N : ℕ,N≤4*N)) tendsto_id
  have hpos : Tendsto (fun N => pos N/(M N:ℝ)) atTop atTop := by
    apply (hpositive.comp hfour).congr
    intro N
    dsimp [pos,A,M]
    push_cast
    rfl
  have hscale : Tendsto (fun N : ℕ => 7*(b+1)*N) atTop atTop := by
    apply tendsto_atTop_mono' _ _ tendsto_id
    exact Filter.Eventually.of_forall (fun N => by nlinarith : ∀ N : ℕ,N≤7*(b+1)*N)
  have hneg : Tendsto (fun N => neg N/(M N:ℝ)) atTop atTop := by
    have hlate := tendsto_mobiusDivisorLatePrimeMass_div_atTop.comp hscale
    apply hlate.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
    have heM : 4*(7*(b+1)*N)=M N := by dsimp [M]; ring
    dsimp only [Function.comp_def]
    rw [heM]
    have he : neg N=mobiusDivisorLatePrimeMass (M N) := by
      apply sum_congr rfl
      intro p hp
      have h := (late_pool_at_scaled_cutoff hb hN p hp).2.2.2.2
      change -mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) {p}=_
      rw [h,neg_neg]
    rw [← he]
    dsimp [M]
    push_cast
    ring
  have hpbound := hpos.eventually (eventually_ge_atTop (max T 0+184832))
  have hnbound := hneg.eventually (eventually_ge_atTop (max T 0+184832))
  filter_upwards [hpbound,hnbound,eventually_ge_atTop (1:ℕ)] with N hpbound hnbound hN
  change ∃ L⊆A N,∃ R⊆B N, _
  have hM8 : 8≤M N := by dsimp [M]; nlinarith
  have hMr : (0:ℝ)<M N := by exact_mod_cast (show 0<M N by omega)
  have hposMass : (max T 0+184832)*(M N:ℝ)≤pos N := (le_div_iff₀ hMr).mp hpbound
  have hnegMass : (max T 0+184832)*(M N:ℝ)≤neg N := (le_div_iff₀ hMr).mp hnbound
  have hhead := fixed_core_head_bound hM8
  have hAdata : ∀ p∈A N,p.Prime ∧ p<M N ∧ p∉mobiusDivisorSelectionPrimes 8 ∧ M N<8*p := by
    intro p hp
    obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
    have h8p : 8<p := by nlinarith
    have hpP : p∉mobiusDivisorSelectionPrimes 8 := by
      intro hp
      have := mem_range.mp (mem_filter.mp hp).1
      omega
    exact ⟨hpp,by dsimp [M]; nlinarith,hpP,by dsimp [M]; nlinarith⟩
  have hBdata := late_pool_at_scaled_cutoff hb hN
  have hdis : Disjoint (A N) (B N) := by
    apply disjoint_left.mpr
    intro p hpA hpB
    have ha := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpA).2.2
    have hb' := (GaloisForLFunctions.HTGeometry.mem_primesInIoc hpB).2.1
    have hm : M N<2*p := by omega
    dsimp [M] at hm
    nlinarith
  have hU : ∀ p∈A N∪B N,p.Prime ∧ p<M N ∧ p∉mobiusDivisorSelectionPrimes 8 ∧
      mobiusDivisorSelectionPrimes (M N/p+1)⊆mobiusDivisorSelectionPrimes 8 := by
    intro p hp
    have hd : p.Prime ∧ p<M N ∧ p∉mobiusDivisorSelectionPrimes 8 ∧ M N<8*p := by
      rcases mem_union.mp hp with hp|hp
      · exact hAdata p hp
      · obtain ⟨hp1,hp2,hp3,hp4,_⟩ := hBdata p hp
        exact ⟨hp1,hp2,hp3,hp4⟩
    exact ⟨hd.1,hd.2.1,hd.2.2.1,
      mobiusDivisorPrime_isolated_after_eight (M N) _ Subset.rfl hd.1 hd.2.2.2⟩
  have hAs : ∀ p∈A N,0≤ mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) {p} := by
    intro p hp
    exact (mul_nonneg hc.le (Real.sqrt_nonneg (4*N:ℕ))).trans (hfloor (4*N) p hp)
  have hBs : ∀ p∈B N,mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) {p}≤0 := by
    intro p hp
    rw [(hBdata p hp).2.2.2.2]
    exact neg_nonpos.mpr (divisorUnsignedDilationChannel_nonneg _ _)
  have hreserve : T*(M N:ℝ)≤ min (pos N) (neg N)-
      |mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) ∅| := by
    have hm : (max T 0+184832)*(M N:ℝ)≤ min (pos N) (neg N) := le_min hposMass hnegMass
    have ht := mul_le_mul_of_nonneg_right (le_max_left T 0) hMr.le
    nlinarith only [hm,ht,hhead]
  have hcovA : |mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) ∅|≤pos N := by
    have hz := mul_nonneg (le_max_right T 0) hMr.le
    nlinarith only [hhead,hposMass,hz]
  have hcovB : |mobiusDivisorSelectionFibre (M N) (mobiusDivisorSelectionPrimes 8) ∅|≤neg N := by
    have hz := mul_nonneg (le_max_right T 0) hMr.le
    nlinarith only [hhead,hnegMass,hz]
  obtain ⟨L,hLA,R,hRB,hLm,hRm,l,hl,hset,hbound⟩ := exists_mobiusDivisorBalancedIsolatedBatch
    (M N) (mobiusDivisorSelectionPrimes 8) (A N) (B N) hdis hU hAs hBs hcovA hcovB
  refine ⟨L,hLA,R,hRB,hreserve.trans hLm,hreserve.trans hRm,l,hl,hset,fun k => ?_⟩
  exact (hbound k).trans (mobiusDivisorSelectionEnergy_small_core_le (M N) hM8 _ Subset.rfl)
end RHTower
