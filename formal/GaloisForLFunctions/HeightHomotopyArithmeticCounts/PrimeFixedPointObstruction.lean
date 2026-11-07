import GaloisForLFunctions.HeightHomotopyArithmeticCounts.PrimeComponentRigidity
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.PrimeWindowCount

/-!
# The fixed points cannot have square-root cardinality

Upper-half prime vertices force at least `N/(4 log N)` fixed points for every
self-map of the prime complex homotopic to the identity, at all sufficiently
large heights. Hence even an eventual square-root bound on the fixed-point
set is impossible. The obstruction concerns literal fixed-point cardinality;
it does not bound a signed Lefschetz sum or a relative invariant of the core.
-/

noncomputable section
open Finset Filter Topology ContinuousMap
open GaloisForLFunctions.EffectiveScalingGeometry
open GaloisForLFunctions.HTGeometry
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- Upper-half primes have a positive `N/log N` supply. -/
theorem eventually_upperPrime_count_ge :
    ∀ᶠ N : ℕ in atTop,
      (N:ℝ)/(4*Real.log N) ≤ ((primesInIoc (N/2) N).card:ℝ) := by
  have hcast : Tendsto (fun N : ℕ => (N:ℝ)/2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hc := hcast.eventually (eventually_primeCount_window_ge (K := 2) (by norm_num))
  filter_upwards [hc,eventually_gt_atTop (2:ℕ)] with N hc hN
  have hNr : (2:ℝ)<N := by exact_mod_cast hN
  have harg : (2:ℝ)*((N:ℝ)/2)=N := by ring
  rw [harg, Nat.floor_natCast, show (2:ℝ)=(2:ℕ) by norm_num,
    Nat.floor_div_natCast, Nat.floor_natCast] at hc
  rw [← card_primesInIoc (Nat.div_le_self N 2)] at hc
  have hloghalf : 0<Real.log ((N:ℝ)/2) := Real.log_pos (by linarith only [hNr])
  have hlogN : 0<Real.log N := Real.log_pos (by linarith only [hNr])
  have hlogle : Real.log ((N:ℝ)/2)≤Real.log N :=
    Real.log_le_log (by linarith only [hNr]) (by linarith only [hNr])
  have hdiv := div_le_div_of_nonneg_left (show (0:ℝ)≤N by positivity)
    (mul_pos (by norm_num : (0:ℝ)<4) hloghalf) (mul_le_mul_of_nonneg_left hlogle (by norm_num))
  calc
    (N:ℝ)/(4*Real.log N) ≤ (N:ℝ)/(4*Real.log ((N:ℝ)/2)) := hdiv
    _ = (2-1)/2*(((N:ℝ)/2)/Real.log ((N:ℝ)/2)) := by ring
    _ ≤ _ := hc

private theorem sqrt_div_log_tendsto :
    Tendsto (fun N : ℕ => Real.sqrt N/(4*Real.log N)) atTop atTop := by
  have hz : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)).tendsto_div_nhds_zero
  have hw : Tendsto (fun x : ℝ => Real.log x/Real.sqrt x) atTop
      (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hz
    filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (Real.sqrt_pos.mpr (by linarith only [hx]))
  have hi : Tendsto (fun x : ℝ => Real.sqrt x/Real.log x) atTop atTop :=
    hw.inv_tendsto_nhdsGT_zero.congr (fun x => by
      change (Real.log x/Real.sqrt x)⁻¹=Real.sqrt x/Real.log x
      rw [inv_div])
  have h := (hi.comp tendsto_natCast_atTop_atTop).const_mul_atTop
    (show (0:ℝ)<1/4 by norm_num)
  convert h using 1
  funext N
  simp only [Function.comp_def]
  ring

/-- The forced isolated-prime contribution grows faster than the square-root scale. -/
theorem tendsto_upperPrime_count_div_sqrt :
    Tendsto (fun N : ℕ => ((primesInIoc (N/2) N).card:ℝ)/Real.sqrt N) atTop atTop := by
  have hb : ∀ᶠ N : ℕ in atTop,
      Real.sqrt N/(4*Real.log N) ≤ ((primesInIoc (N/2) N).card:ℝ)/Real.sqrt N := by
    filter_upwards [eventually_upperPrime_count_ge,eventually_gt_atTop (1:ℕ)] with N hc hN
    have hNr : (0:ℝ)<N := by exact_mod_cast (Nat.zero_lt_of_lt hN)
    have hs := Real.sqrt_pos.mpr hNr
    have he : (N:ℝ)/(4*Real.log N)/Real.sqrt N=Real.sqrt N/(4*Real.log N) := by
      have hlog : Real.log (N:ℝ)≠0 := ne_of_gt (Real.log_pos (by exact_mod_cast hN))
      field_simp [hs.ne',hlog]; nlinarith only [Real.sq_sqrt hNr.le]
    have h := div_le_div_of_nonneg_right hc hs.le
    rwa [he] at h
  exact tendsto_atTop_mono' _ hb sqrt_div_log_tendsto

#print axioms eventually_upperPrime_count_ge
#print axioms tendsto_upperPrime_count_div_sqrt

/-- The forced finite-ambient vertices are exactly the actual upper-half primes. -/
theorem upperPrimeVertices_map (N : ℕ) :
    (upperPrimeVertices N N).map Fin.valEmbedding = primesInIoc (N/2) N := by
  ext p
  simp only [Finset.mem_map, upperPrimeVertices, mem_filter, mem_univ, true_and,
    primesInIoc, mem_Ioc, Fin.valEmbedding_apply]
  constructor
  · rintro ⟨q,⟨hq,hqN,hhalf⟩,rfl⟩
    exact ⟨⟨by omega,hqN⟩,hq⟩
  · rintro ⟨⟨hhalf,hpN⟩,hp⟩
    exact ⟨⟨p,by omega⟩,⟨hp,hpN,by change N<2*p; omega⟩,rfl⟩

theorem upperPrimeVertices_card (N : ℕ) :
    (upperPrimeVertices N N).card=(primesInIoc (N/2) N).card := by
  have h := congrArg Finset.card (upperPrimeVertices_map N)
  simpa only [card_map] using h

/-- Every finite cover of the fixed-point set eventually exceeds any square-root budget. -/
theorem eventually_fixedPoint_cover_large (C : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (f : C(PrimeHeightSpace N N, PrimeHeightSpace N N))
        (_H : (ContinuousMap.id _).Homotopy f) (A : Finset (PrimeHeightSpace N N)),
        (∀x, f x=x → x∈A) → C*Real.sqrt N < (A.card:ℝ) := by
  have hbig := tendsto_upperPrime_count_div_sqrt.eventually_gt_atTop C
  filter_upwards [hbig,eventually_gt_atTop (0:ℕ)] with N hbig hN
  intro f H A hA
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  have hc : C*Real.sqrt N < ((primesInIoc (N/2) N).card:ℝ) :=
    (lt_div_iff₀ hs).mp hbig
  have hcover := upperPrime_card_le_fixedPoint_cover f H A hA
  rw [upperPrimeVertices_card] at hcover
  exact hc.trans_le (by exact_mod_cast hcover)

/-- No family homotopic to the identity has an eventually square-root-sized fixed set. -/
theorem not_squareRoot_fixedPoint_localization :
    ¬∃ (C : ℝ) (N₀ : ℕ), ∀ N≥N₀,
      ∃ (f : C(PrimeHeightSpace N N, PrimeHeightSpace N N))
        (_H : (ContinuousMap.id _).Homotopy f) (A : Finset (PrimeHeightSpace N N)),
        (∀x, f x=x → x∈A) ∧ (A.card:ℝ)≤C*Real.sqrt N := by
  rintro ⟨C,N₀,h⟩
  obtain ⟨N,hlarge,hN⟩ := ((eventually_fixedPoint_cover_large C).and
    (eventually_ge_atTop N₀)).exists
  obtain ⟨f,H,A,hA,hcard⟩ := h N hN
  exact (not_lt_of_ge hcard) (hlarge f H A hA)

#print axioms eventually_fixedPoint_cover_large
#print axioms not_squareRoot_fixedPoint_localization

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
