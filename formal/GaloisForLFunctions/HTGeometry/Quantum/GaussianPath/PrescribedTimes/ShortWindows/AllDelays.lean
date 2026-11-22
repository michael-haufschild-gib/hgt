import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.MesoscopicDelay
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.InitialDeadline

/-! # A physical return is unlikely throughout a growing window at any prescribed delay -/
open MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

private theorem travel_dominates_square (N : ℕ) (hh : 64 ≤ N.sqrt) :
    (N:ℝ)^2+N ≤ (2:ℝ)^(N-10*N.sqrt) := by
  let h := N.sqrt
  have hs := ReturnExcursions.dimension_dominates_speed hh
  have hN : N+1 ≤ (h+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt N
  have hn : N ≤ 2^h := (Nat.le_succ N).trans (hN.trans ((by omega : (h+1)^2 ≤ 64*(h+1)^2).trans hs))
  have hmul := Nat.mul_le_mul_right h (show 13 ≤ h by dsimp [h]; omega)
  have hsq := Nat.sqrt_le N
  change h*h ≤ N at hsq
  have he : h*2+1 ≤ N-10*h := by dsimp [h] at *; omega
  have hNpos : 1 ≤ N := by dsimp [h] at *; omega
  have hNN : N ≤ N^2 := le_self_pow₀ hNpos (by decide)
  have h₂ := Nat.pow_le_pow_left hn 2
  have hpr : N^2+N ≤ (2^h)^2*2 := by omega
  rw [←pow_mul,←pow_succ] at hpr
  exact_mod_cast hpr.trans (Nat.pow_le_pow_right (by decide : 0<2) he)

private theorem eventually_linear_budget {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ⌊c*sqrt N⌋₊ ≤ nearHilbertContinuousCircuitBudget N/2 := by
  obtain ⟨m,hm⟩ := exists_nat_gt (2*c)
  filter_upwards [eventually_ge_atTop (max 64 (m^2))] with N hN
  have hbig : 64 ≤ N := (le_max_left ..).trans hN
  have hsq : (m:ℝ)^2 ≤ N := by exact_mod_cast ((le_max_right ..).trans hN : m^2 ≤ N)
  have hm' : (m:ℝ) ≤ sqrt N := (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr hsq
  have hs := (mul_le_mul_of_nonneg_right (hm.le.trans hm') (sqrt_nonneg _)).trans_eq (Real.mul_self_sqrt (Nat.cast_nonneg _))
  have hf := Nat.floor_le (mul_nonneg hc.le (sqrt_nonneg (N:ℝ)))
  have hh : ⌊c*sqrt N⌋₊*2 ≤ N := by
    exact_mod_cast (show (⌊c*sqrt N⌋₊:ℝ)*2 ≤ N by linarith only [hs,hf])
  apply (Nat.le_div_iff_mul_le (by decide)).mpr
  apply (Nat.le_div_iff_mul_le (by positivity)).mpr
  have hd := ReturnExcursions.dimension_dominates_speed hbig
  exact (Nat.mul_le_mul_right _ hh).trans (by nlinarith only [hd,Nat.zero_le N])

/-- On the initial polynomial interval after the near-Hilbert crossing,
the exponential travel estimate excludes every low-cost visit simultaneously. -/
theorem gaussian_initial_window_gap {c : ℝ} (hc : 0 < c) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      ∀ L w : ℝ, 0 ≤ L → L+w ≤ (N:ℝ)^2+N →
        prefixPoint k ω ∉ hitWindow (k+1) P ⌊c*sqrt N⌋₊ L w := by
  obtain ⟨_,hfirst⟩ := ReturnExcursions.gaussian_initial_crossing_short_return_tradeoff
  filter_upwards [hfirst,ReturnExcursions.gaussian_robust_travel_time] with ω hσ hf
  filter_upwards [hσ,hf,(tendsto_add_atTop_nat 3).eventually (eventually_linear_budget hc),
    eventually_ge_atTop (64*64)] with k hdate htravel hbudget hk
  intro N P L w hL hw hhit
  let s := ⌊c*sqrt N⌋₊
  let H : selfAdjoint (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) :=
    ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let x := prefixPoint k ω
  have he (j : ℕ) (v : ℝ) : pathGateDistance (k+1) j x v=orbitCircuitDistance H j v := by
    rw [pathGateDistance,show numberedGenerator (k+1) x=H.val from numberedGenerator_shell _]
    rfl
  obtain ⟨σ,hpos,heq,hprior,_,_⟩ := hdate
  have hσpos := (by positivity : (0:ℝ) < 2^(N-10*N.sqrt)).trans hpos
  have horigin := crossingOrigin_eq_of_first hσpos.le ((he P σ).trans heq)
    (fun t ht => (he P t).trans_lt (hprior t ht))
  obtain ⟨t,ht,hd⟩ := hhit
  change t∈Icc (crossingOrigin (k+1) P (9/80) x+L) _ at ht
  rw [horigin] at ht
  have hlow := htravel σ t heq.ge s hbudget
    ((hasProjectiveCircuitApproximation_iff_infDist _ s _).mpr ((he s t).symm.trans_le hd))
  have hnon : σ ≤ t := (le_add_of_nonneg_right hL).trans ht.1
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hnon)] at hlow
  have hbig := travel_dominates_square N (Nat.le_sqrt.mpr (by dsimp [N]; omega))
  change (2:ℝ)^(N-10*N.sqrt) < t-σ at hlow
  linarith only [hbig,hlow,ht.2,hw]

/-- Choose any nonnegative delay before drawing the Gaussian couplings.
Starting that long after the chain's first near-Hilbert crossing, a whole
interval of length N^(1/96) excludes ⌊c√N⌋ gates at error 1/10 with
probability tending to one. -/
theorem gaussian_any_prescribed_delay :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ → ℝ,
      Tendsto (fun k => let N := k+3
                        let P := nearHilbertContinuousCircuitBudget N
                        pathPauliDisorderLaw.real (prefixPoint k ⁻¹'
                          hitWindow (k+1) P ⌊c*sqrt N⌋₊ (max (d k) 0) (delayWindowWidth N))) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨c,hc,hh⟩ := gaussian_prescribed_growing_window
  refine ⟨c,hc,fun d => ?_⟩
  let N (k : ℕ) := k+3
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (N k)
  let s (k : ℕ) := ⌊c*sqrt (N k)⌋₊
  let L (k : ℕ) := max (d k) 0
  let A (k : ℕ) (u : ℝ) := prefixPoint k ⁻¹' hitWindow (k+1) (P k) (s k) u (delayWindowWidth (N k))
  let B (k : ℕ) := A k (max (L k) ((N k:ℝ)^2))
  let C (k : ℕ) := A k (L k) \ B k
  have hm (k : ℕ) (u : ℝ) : MeasurableSet (A k u) :=
    (measurable_hitWindow ..).preimage (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  have hmiss : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω∉C k := by
    filter_upwards [gaussian_initial_window_gap hc] with ω hf
    filter_upwards [hf] with k hk
    rintro ⟨hcheap,hout⟩
    by_cases hL : (N k:ℝ)^2 ≤ L k
    · apply hout
      change ω ∈ A k (max (L k) ((N k:ℝ)^2))
      rwa [max_eq_left hL]
    have hN : 1 ≤ (N k:ℝ) := by exact_mod_cast (show 1 ≤ N k by dsimp [N]; omega)
    have hw : delayWindowWidth (N k) ≤ N k :=
      (Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (96:ℝ)⁻¹ ≤ 1)).trans_eq (Real.rpow_one _)
    exact hk _ _ (le_max_right (d k) 0) (add_le_add (le_of_not_ge hL) hw) hcheap
  have hC := probability_vanishes pathPauliDisorderLaw C (fun k => (hm k _).diff (hm k _)) hmiss
  have hB : Tendsto (fun k => pathPauliDisorderLaw.real (B k)) atTop (𝓝 0) := hh P L
  have hupper (k : ℕ) : pathPauliDisorderLaw.real (A k (L k)) ≤ pathPauliDisorderLaw.real (B k)+pathPauliDisorderLaw.real (C k) :=
    (measureReal_mono (μ:=pathPauliDisorderLaw) (show A k (L k) ⊆ B k ∪ C k from fun ω h =>
      (em (ω∈B k)).elim Or.inl (fun hb => Or.inr ⟨h,hb⟩))).trans (measureReal_union_le _ _)
  exact squeeze_zero (fun _ => measureReal_nonneg) hupper (by simpa only [add_zero] using hB.add hC)

#print axioms gaussian_any_prescribed_delay
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
