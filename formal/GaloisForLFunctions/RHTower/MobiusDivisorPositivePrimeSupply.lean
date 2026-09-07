import GaloisForLFunctions.RHTower.MobiusDivisorPrimeFibreInterpolation
import GaloisForLFunctions.RHTower.MobiusDivisorRetainedPrimeOrientation
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeCompensation
/-!
# Macroscopic positive retained prime supply

The strictly negative complete source at seven persists under sufficiently
small clipping toward eight. After the fixed prime core below eight is
processed, a fixed macroscopic prime window therefore has uniformly positive
singleton fibres. The corpus prime-window theorem proves that their total
mass is superlinear. No numerical experiment enters this proof.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem seven_window_quotient {b N p : ℕ} (hb : 8≤b)
    (hlo : b*N<p) (hhi : p≤(b+1)*N) : (7*(b+1)*N)/p=7 := by
  have hp : 0<p := by omega
  have hlow : 7≤(7*(b+1)*N)/p :=
    (Nat.le_div_iff_mul_le hp).mpr (by nlinarith)
  have hhigh : (7*(b+1)*N)/p<8 :=
    (Nat.div_lt_iff_lt_mul hp).mpr (by nlinarith)
  omega

private theorem seven_window_clip {b N p : ℕ} (hb : 8≤b)
    (hlo : b*N<p) (hhi : p≤(b+1)*N) :
    (b:ℝ)*divisorPrimeClipWeight (7*(b+1)*N) p≤70 := by
  have hp : 0<p := by omega
  have hN : 0<N := by nlinarith
  have hquot := seven_window_quotient hb hlo hhi
  have hw := divisorPrimeClipWeight_nonneg (7*(b+1)*N) p hp
  have hstep := divisorPrimeClipWeight_mul_step (7*(b+1)*N) p hp
  rw [hquot] at hstep
  norm_num only [Nat.reduceAdd] at hstep
  have hgap : (1/10:ℝ)≤Real.sqrt 8-Real.sqrt 7 := by
    have h8 := Real.sq_sqrt (by norm_num : (0:ℝ)≤8)
    have h7 := Real.sq_sqrt (by norm_num : (0:ℝ)≤7)
    have h8lo : (14/5:ℝ)≤Real.sqrt 8 := by nlinarith [Real.sqrt_nonneg (8:ℝ)]
    have h7hi : Real.sqrt 7≤(27/10:ℝ) := by nlinarith [Real.sqrt_nonneg (7:ℝ)]
    linarith only [h8lo,h7hi]
  have hMp : 7*p≤7*(b+1)*N := by nlinarith
  have hroot : Real.sqrt (p:ℝ)≤Real.sqrt (p*7:ℕ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p≤p*7 by omega)
  have hdiff : 0≤Real.sqrt (7*(b+1)*N:ℕ)-Real.sqrt (p*7:ℕ) := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show p*7≤7*(b+1)*N by omega)
  have hsM := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (7*(b+1)*N))
  have hs7 := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) (p*7))
  have hsp := Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) p)
  have hmul := mul_le_mul_of_nonneg_left
    (show Real.sqrt p≤Real.sqrt (7*(b+1)*N:ℕ)+Real.sqrt (p*7:ℕ) by
      linarith only [hroot,Real.sqrt_nonneg ((7*(b+1)*N:ℕ):ℝ)]) hdiff
  have hNat : ((7*(b+1)*N:ℕ):ℝ)≤(p*7:ℕ)+7*N := by
    exact_mod_cast (show 7*(b+1)*N≤p*7+7*N by nlinarith)
  have hbound : (Real.sqrt (7*(b+1)*N:ℕ)-Real.sqrt (p*7:ℕ))*Real.sqrt p≤7*N := by
    nlinarith only [hmul,hsM,hs7,hNat]
  have he := congrArg (fun x : ℝ => x*Real.sqrt p) hstep
  have he' : divisorPrimeClipWeight (7*(b+1)*N) p*(p:ℝ)*(Real.sqrt 8-Real.sqrt 7)≤7*N := by
    calc
      _ = divisorPrimeClipWeight (7*(b+1)*N) p*(Real.sqrt p)^2*
          (Real.sqrt 8-Real.sqrt 7) := by rw [hsp]
      _ = divisorPrimeClipWeight (7*(b+1)*N) p*Real.sqrt p*
          (Real.sqrt 8-Real.sqrt 7)*Real.sqrt p := by ring
      _ = _ := he
      _ ≤ _ := hbound
  have h10 := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hw (Nat.cast_nonneg (α := ℝ) p))
  have hbn : (b:ℝ)*N≤p := by exact_mod_cast hlo.le
  have hbmul := mul_le_mul_of_nonneg_left hbn hw
  have hNr : (0:ℝ)<N := by exact_mod_cast hN
  nlinarith only [he',h10,hbmul,hNr]

private theorem seven_window_singleton {b N p : ℕ} (hb : 8≤b)
    (hp : p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N)) :
    mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p} =
      -Real.sqrt p*((1-divisorPrimeClipWeight (7*(b+1)*N) p)*
        (∑ d∈Icc 1 7,mobiusDivisorDilationChannel 7 d)+
        divisorPrimeClipWeight (7*(b+1)*N) p*
        (∑ d∈Icc 1 8,mobiusDivisorDilationChannel 8 d)) := by
  obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  have hN : 1≤N := by have := hpp.pos; nlinarith
  have hlarge : 8<p := by nlinarith
  have hpP : p∉mobiusDivisorSelectionPrimes 8 := by
    intro h
    have := mem_range.mp (mem_filter.mp h).1
    omega
  have hsub : mobiusDivisorSelectionPrimes 7⊆mobiusDivisorSelectionPrimes 8 := by
    intro q hq
    obtain ⟨hq,hprime⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hq; omega),hprime⟩
  rw [show ({p}:Finset ℕ)=insert p ∅ by rfl,
    mobiusDivisorSelectionFibre_prime_interpolation hpp _ _ ∅ hpP (by simp),
    mobiusDivisorInterpolatedFibre,seven_window_quotient hb hlo hhi]
  rw [mobiusDivisorSelectionFibre_of_all_source_primes_processed 7 _ ∅ hsub,
    mobiusDivisorSelectionFibre_of_all_source_primes_processed 8 _ ∅ Subset.rfl]
  simp

/-- A fixed macroscopic prime window carries positive retained fibres after the fixed small core, uniformly at every cutoff in the sequence. -/
theorem exists_mobiusDivisorPositivePrimeWindow :
    ∃ b : ℕ,8≤b ∧ ∃ c : ℝ,0<c ∧ ∀ N p : ℕ,
      p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N) →
      c*Real.sqrt N≤ mobiusDivisorSelectionFibre (7*(b+1)*N)
        (mobiusDivisorSelectionPrimes 8) {p} := by
  let A := ∑ d∈Icc 1 7,mobiusDivisorDilationChannel 7 d
  let B := ∑ d∈Icc 1 8,mobiusDivisorDilationChannel 8 d
  let c := -A/2
  have hA : A<0 := sum_mobiusDivisorDilationChannel_seven_neg
  have hc : 0<c := by dsimp [c]; linarith only [hA]
  obtain ⟨b₀,hb₀⟩ := exists_nat_ge (70*|B-A|/c)
  let b := max b₀ 8
  have hb : 8≤b := le_max_right _ _
  have hbc : 70*|B-A|≤(b:ℝ)*c := by
    have hcast : (b₀:ℝ)≤b := by exact_mod_cast (le_max_left b₀ 8)
    exact (div_le_iff₀ hc).mp (hb₀.trans hcast)
  refine ⟨b,hb,c,hc,fun N p hp => ?_⟩
  obtain ⟨hpp,hlo,hhi⟩ := GaloisForLFunctions.HTGeometry.mem_primesInIoc hp
  let w := divisorPrimeClipWeight (7*(b+1)*N) p
  have hw : 0≤w := divisorPrimeClipWeight_nonneg _ _ hpp.pos
  have hw70 : (b:ℝ)*w≤70 := seven_window_clip hb hlo hhi
  have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hprod := mul_le_mul_of_nonneg_right hw70 (abs_nonneg (B-A))
  have hwb : w*|B-A|≤c := by nlinarith only [hprod,hbc,hbR]
  have hupper := mul_le_mul_of_nonneg_left (le_abs_self (B-A)) hw
  have hinterp : (1-w)*A+w*B≤-c := by
    dsimp [c] at hwb ⊢
    nlinarith only [hwb,hupper]
  have hroot : Real.sqrt N≤Real.sqrt p := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (show N≤p by nlinarith)
  rw [seven_window_singleton hb hp]
  change c*Real.sqrt N≤-Real.sqrt p*((1-w)*A+w*B)
  have hm := mul_le_mul_of_nonneg_left hinterp (Real.sqrt_nonneg (p:ℝ))
  have hr := mul_le_mul_of_nonneg_left hroot hc.le
  nlinarith only [hm,hr]
private theorem sqrt_log_mul_tendsto {b : ℕ} (hb : 0<b) :
    Tendsto (fun N : ℕ => Real.sqrt N/Real.log ((b:ℝ)*N)) atTop atTop := by
  have hzero : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
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

private theorem positive_window_mass_growth (b : ℕ) (hb : 8≤b) (c : ℝ) (hc : 0<c)
    (hf : ∀ N p : ℕ,p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N) →
      c*Real.sqrt N≤ mobiusDivisorSelectionFibre (7*(b+1)*N)
        (mobiusDivisorSelectionPrimes 8) {p}) :
    Tendsto (fun N : ℕ =>
      (∑ p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N),
        mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p})/
          (7*((b:ℝ)+1)*N)) atTop atTop := by
  have hbR : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
  have hratio : (1:ℝ)<((b:ℝ)+1)/b := by rw [lt_div_iff₀ hbR]; linarith
  have hcast : Tendsto (fun N : ℕ => (b:ℝ)*N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hbR
  have hcount := hcast.eventually (GaloisForLFunctions.HTGeometry.eventually_primeCount_window_ge hratio)
  have hbound : ∀ᶠ N : ℕ in atTop,
      (c/(14*((b:ℝ)+1)))*(Real.sqrt N/Real.log ((b:ℝ)*N)) ≤
      (∑ p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N),
        mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p})/
          (7*((b:ℝ)+1)*N) := by
    filter_upwards [hcount,eventually_ge_atTop (1:ℕ)] with N hcount hN
    have harg : (((b:ℝ)+1)/b)*((b:ℝ)*N)=((b+1)*N:ℕ) := by
      push_cast
      field_simp
    have hbN : (b:ℝ)*N=(b*N:ℕ) := by push_cast; rfl
    rw [harg,hbN,Nat.floor_natCast,Nat.floor_natCast] at hcount
    rw [← GaloisForLFunctions.HTGeometry.card_primesInIoc
      (show b*N≤(b+1)*N by nlinarith)] at hcount
    have hsum := sum_le_sum (fun p hp => hf N p hp)
    simp only [sum_const,nsmul_eq_mul] at hsum
    have hm := mul_le_mul_of_nonneg_right hcount
      (mul_nonneg hc.le (Real.sqrt_nonneg (N:ℝ)))
    have hraw := hm.trans hsum
    have hd := div_le_div_of_nonneg_right hraw
      (show (0:ℝ)≤7*((b:ℝ)+1)*N by positivity)
    have hNr : (0:ℝ)<N := by exact_mod_cast hN
    have heq : (((((b:ℝ)+1)/b-1)/2*((b*N:ℕ)/Real.log (b*N:ℕ)))*
        (c*Real.sqrt N))/(7*((b:ℝ)+1)*N) =
        (c/(14*((b:ℝ)+1)))*(Real.sqrt N/Real.log ((b:ℝ)*N)) := by
      push_cast
      field_simp
      ring
    rwa [heq] at hd
  exact tendsto_atTop_mono' _ hbound
    ((sqrt_log_mul_tendsto (by omega : 0<b)).const_mul_atTop
      (show (0:ℝ)<c/(14*((b:ℝ)+1)) by positivity))

/-- The actual positive retained prime source has superlinear mass in one fixed macroscopic window. -/
theorem exists_mobiusDivisorPositivePrimeWindow_mass_atTop :
    ∃ b : ℕ,8≤b ∧ ∃ c : ℝ,0<c ∧
      (∀ N p : ℕ,p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N) →
        c*Real.sqrt N≤ mobiusDivisorSelectionFibre (7*(b+1)*N)
          (mobiusDivisorSelectionPrimes 8) {p}) ∧
      Tendsto (fun N : ℕ =>
        (∑ p∈GaloisForLFunctions.HTGeometry.primesInIoc (b*N) ((b+1)*N),
          mobiusDivisorSelectionFibre (7*(b+1)*N) (mobiusDivisorSelectionPrimes 8) {p})/
            (7*((b:ℝ)+1)*N)) atTop atTop := by
  obtain ⟨b,hb,c,hc,hf⟩ := exists_mobiusDivisorPositivePrimeWindow
  exact ⟨b,hb,c,hc,hf,positive_window_mass_growth b hb c hc hf⟩
end RHTower
