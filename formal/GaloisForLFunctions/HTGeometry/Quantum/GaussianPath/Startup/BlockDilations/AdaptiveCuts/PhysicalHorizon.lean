import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.ContinuousWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.TripleSignals.FirstExcess

/-! # A K^(65/64) horizon for physical circuit costs and pairs of visits -/

open Real Filter MeasureTheory Matrix Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

private theorem root_horizon (K : ℕ) (hK : 0<K) :
    (K:ℝ)^(65/64:ℝ)≤(2*(sizeRoot K:ℝ))^65 := by
  have hq : 0≤2*(sizeRoot K:ℝ) := by positivity
  have hhi : (K:ℝ)≤(2*(sizeRoot K:ℝ))^64 := by exact_mod_cast (root_bounds hK).2.2
  apply (rpow_le_rpow (Nat.cast_nonneg K) hhi (by norm_num : (0:ℝ)≤65/64)).trans_eq
  calc
    _ = ((2*(sizeRoot K:ℝ))^((64:ℕ):ℝ))^(65/64:ℝ) := by rw [rpow_natCast]
    _ = (2*(sizeRoot K:ℝ))^(((64:ℕ):ℝ)*(65/64)) := (rpow_mul hq ..).symm
    _ = _ := by norm_num

/-- Almost surely on one nested chain, a positive density of gates is
necessary at every physical date from inverse size through K^(65/64). -/
theorem gaussian_superlinear_from_startup :
    ∃ τ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      ∀ t : ℝ, A≤K * |t| → |t|≤δ*K^(65/64:ℝ) → ∀ s : ℕ,
        HasProjectiveCircuitApproximation (n+2) (1/4) s
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t) → τ*K<(s:ℝ) := by
  obtain ⟨τ,hτ,a,ha,δ,hδ,hp⟩ := gaussian_superlinear_window
  obtain ⟨A,hA,hs⟩ := SpanningDensity.FixedHorizon.gaussian_all_bounded_horizons
    (η:=1/2) (by norm_num)
  refine ⟨min τ (1/4),lt_min hτ (by norm_num),2*A,by positivity,δ/(2:ℝ)^65,by positivity,?_⟩
  filter_upwards [hs,hp] with ω hω hw
  filter_upwards [hω a,hw] with n hs hn
  intro K t ht hfin s hfit
  have hK : 0≤K := Nat.cast_nonneg _
  have hbound : δ/(2:ℝ)^65*K^(65/64:ℝ)≤δ*(sizeRoot (n+2):ℝ)^65 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos two_pos 65)).mpr
    have h := mul_le_mul_of_nonneg_left (root_horizon (n+2) (by omega)) hδ.le
    simpa only [mul_pow,mul_assoc,mul_comm,mul_left_comm] using h
  by_cases hl : |t|<a
  · have hsize : K≤2*((n+1:ℕ):ℝ) := by dsimp only [K]; exact_mod_cast (show n+2≤2*(n+1) by omega)
    have htime : A≤|t| * ((n+1:ℕ):ℝ) := by
      nlinarith only [ht,mul_le_mul_of_nonneg_right hsize (abs_nonneg t)]
    have h := hs t htime hl.le s hfit
    have hb' := mul_le_mul_of_nonneg_right (min_le_right τ (1/4:ℝ)) hK
    linarith only [hb',h,hsize]
  · have h' := hn |t| ⟨le_of_not_gt hl,hfin.trans hbound⟩ s
    apply (mul_le_mul_of_nonneg_right (min_le_left ..) hK).trans_lt
    apply h'
    rcases le_total 0 t with h|h
    · rwa [abs_of_nonneg h]
    · let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
        ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
      rw [abs_of_nonpos h]
      exact hfit.neg_time H

/-- Two low-budget visits must cluster on the inverse-size scale or
be separated by more than the full superlinear exclusion horizon. -/
theorem gaussian_superlinear_visit_spacing :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ (t w : ℝ) (r s : ℕ) (e f : ℝ), e+f≤1/4 → (r+s:ℕ)≤κ*K →
        HasProjectiveCircuitApproximation (n+2) e r (unitaryEvolution H t) →
        HasProjectiveCircuitApproximation (n+2) f s (unitaryEvolution H w) →
        |w-t|<A/K ∨ δ*K^(65/64:ℝ) < |w-t| := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,h⟩ := gaussian_superlinear_from_startup
  refine ⟨κ,hκ,A,hA,δ,hδ,?_⟩
  filter_upwards [h] with ω hw
  filter_upwards [hw] with n hn
  intro K H t w r s e f hef hk ht hw
  let G : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := ⟨H,isSelfAdjoint_pathHamiltonian _⟩
  by_contra! hlag
  have hf := affordable_add_time G (x:= -t) (y:=w) (ht.neg_time G) hw
  rw [show -t+w=w-t by ring] at hf
  obtain ⟨z,hz,C,hC,he⟩ := hf
  have hK : 0<K := by dsimp only [K]; positivity
  have hstart := (div_le_iff₀ hK).mp hlag.1
  exact (hn (w-t) (by rwa [mul_comm]) hlag.2 (r+s)
    ⟨z,hz,C,hC,he.trans hef⟩).not_ge hk

/-- On both sides of the actual first low visit after the near-Hilbert
crossing, an inverse-size lag already forces an extensive combined
cost. This persists throughout the superlinear window. -/
theorem gaussian_superlinear_first_dip :
    ∃ κ>0, ∃ A>0, ∃ δ>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω n),isSelfAdjoint_pathHamiltonian _⟩
      ∀ (s r : ℕ) (h : ℝ), A/K≤|h| → |h|≤δ*K^(65/64:ℝ) →
        let v := RepeatedGates.PhysicalBlocks.firstLowAfterCrossing ω n s
        HasProjectiveCircuitApproximation (n+2) (3/20) r (unitaryEvolution H.val (v+h)) →
        κ*K<((s+r:ℕ):ℝ) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,hg⟩ := gaussian_superlinear_visit_spacing
  refine ⟨κ,hκ,A,hA,δ,hδ,?_⟩
  filter_upwards [hg] with ω hω
  filter_upwards [hω] with n hn
  intro K H s r h hstart hend v hf
  have hv : HasProjectiveCircuitApproximation (n+2) (1/10) s (unitaryEvolution H.val v) :=
    (PrecisionReturns.firstVisit_isLeast H _ s (by norm_num : (0:ℝ)<1/10)).1.2
  by_contra! hk
  have hl := hn v (v+h) s r (1/10) (3/20) (by norm_num) hk hv hf
  rw [add_sub_cancel_left] at hl
  exact hl.elim hstart.not_gt hend.not_gt

#print axioms gaussian_superlinear_from_startup
#print axioms gaussian_superlinear_visit_spacing
#print axioms gaussian_superlinear_first_dip
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
