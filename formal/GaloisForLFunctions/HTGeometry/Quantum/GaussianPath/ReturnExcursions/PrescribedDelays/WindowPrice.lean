import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrescribedDelays.InitialWindow
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.PrescribedDelays.AngularData.Grid
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalHorizon
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.Iterated.SubcriticalWait

/-! # Low-gate visits after the original crossing, conditional on direction -/

open MeasureTheory Set Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
open PrescribedTimes ShortWindows LocalPatches.RampWindows.SparseReadings
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- A visit at fixed projective error one tenth after the original crossing. -/
def crossingWindow (k : ℕ) (c T w : ℝ) : Set PathPauliDisorder :=
  prefixPoint k ⁻¹' hitWindow (k+1) (nearHilbertContinuousCircuitBudget (k+3))
    ⌊c*((k+3:ℕ):ℝ)⌋₊ T w

theorem measurable_crossingWindow (k : ℕ) (c T w : ℝ) : MeasurableSet (crossingWindow k c T w) :=
  (measurable_hitWindow ..).preimage (gaussian_pauli_prefix_coordinates_law (k+1)).measurable

/-- Outside a common event eventually absent on almost every chain,
any observation window has probability at most O((1+w)/K^(65/64))
times the mass of its angular selection. This holds at every delay. -/
theorem gaussian_directional_window_price :
    ∃ c>0, ∃ C>0, ∃ B : ℕ → Set PathPauliDisorder, (∀ k, MeasurableSet (B k)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ B k) ∧
      ∀ (k : ℕ) (D : Set (PrefixIndex (k+1) → ℝ)), MeasurableSet D →
        (∀ x (u : ℝ), 0<u → u • x ∈ D → x ∈ D) →
        ∀ T ≥ (0:ℝ), ∀ w ≥ (0:ℝ),
          pathPauliDisorderLaw.real ((crossingWindow k c T w \ B k) ∩ prefixPoint k ⁻¹' D) ≤
            (C*(1+w)/((k+3:ℕ):ℝ)^(65/64:ℝ))*pathPauliDisorderLaw.real (prefixPoint k ⁻¹' D) := by
  obtain ⟨κ,hκ,A,hA,δ,hδ,hfloor⟩ := BlockDilations.AdaptiveCuts.gaussian_superlinear_from_startup
  obtain ⟨C,hC,hlate⟩ := angular_late_window A δ hA hδ
  let c := min (κ/2) 1
  have hc : 0<c := lt_min (half_pos hκ) zero_lt_one
  let N (k : ℕ) : ℝ := (k+3:ℕ)
  let s (k : ℕ) := ⌊c*N k⌋₊
  let P (k : ℕ) := nearHilbertContinuousCircuitBudget (k+3)
  let Q (k : ℕ) := (N k)^(65/64:ℝ)
  let L (k : ℕ) := prefixPoint k ⁻¹' cheapLag (k+1) (s k) (A/N k) (δ*Q k)
  let B (k : ℕ) := L k ∪ crossingWindow k c 0 (2*(N k)^3)
  have hL (k : ℕ) : MeasurableSet (L k) := (measurable_cheapLag ..).preimage
    (gaussian_pauli_prefix_coordinates_law (k+1)).measurable
  refine ⟨c,hc,max 1 C,zero_lt_one.trans_le (le_max_left ..),B,
    fun k => (hL k).union (measurable_crossingWindow ..),?_,?_⟩
  · have hhalf : ∀ᶠ k : ℕ in atTop, k+3 ≤ P k/2 := by
      simpa only [P,pow_one] using (tendsto_add_atTop_nat 3).eventually
        (Iterated.eventually_half_budget (SharpOccupation.polynomial_subcritical 1))
    filter_upwards [hfloor,initial_cubic_window] with ω hf hi
    filter_upwards [(tendsto_add_atTop_nat 1).eventually hf,hi,hhalf] with k hk hinit hsize
    have hN : 0<N k := by dsimp only [N]; positivity
    have hs : (s k:ℝ) ≤ c*N k := Nat.floor_le (mul_nonneg hc.le hN.le)
    have hsκ := hs.trans (mul_le_mul_of_nonneg_right (min_le_left ..) hN.le)
    have hsN : (s k:ℝ) ≤ N k := hs.trans (mul_le_of_le_one_left hN.le (min_le_right ..))
    rintro (⟨t,ht,htc⟩ | h)
    · have ht₀ := (div_pos hA hN).le.trans ht.1
      have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ _ _).mpr htc
      rw [show numberedGenerator (k+1) (prefixPoint k ω)=pathHamiltonian (pathPauliDisorderShell ω (k+1))
        from numberedGenerator_shell _] at hfit
      have hcost := hk t (by rw [abs_of_nonneg ht₀,mul_comm]; exact (div_le_iff₀ hN).mp ht.1)
        (by rw [abs_of_nonneg ht₀]; exact ht.2) (s k+s k) hfit
      change κ*N k < ((s k+s k:ℕ):ℝ) at hcost
      rw [Nat.cast_add] at hcost
      change (s k:ℝ) ≤ (κ/2)*N k at hsκ
      linarith only [hsκ,hcost]
    · change (s k:ℝ) ≤ ((k+3:ℕ):ℝ) at hsN
      exact hinit (s k) ((Nat.cast_le.mp hsN).trans hsize) h
  · intro k D hD hdir T hT w hw
    let K := N k
    have hK : 1 ≤ K := by change (1:ℝ) ≤ ((k+3:ℕ):ℝ); exact_mod_cast (show 1 ≤ k+3 by omega)
    have hQ : 0<Q k := rpow_pos_of_pos (zero_lt_one.trans_le hK) _
    let F := (crossingWindow k c T w \ B k) ∩ prefixPoint k ⁻¹' D
    by_cases hearly : T ≤ K^3
    · by_cases hwide : K^3 ≤ w
      · have hQ₃ : Q k ≤ K^3 := (rpow_le_rpow_of_exponent_le hK (by norm_num : (65/64:ℝ)≤(3:ℕ))).trans_eq
          (rpow_natCast K 3)
        have hprice : 1 ≤ max 1 C*(1+w)/Q k := (le_div_iff₀ hQ).mpr (by
          rw [one_mul]
          exact (hQ₃.trans hwide).trans ((le_add_of_nonneg_left zero_le_one).trans
            (le_mul_of_one_le_left (by linarith only [hw]) (le_max_left ..))))
        have hsub : F ⊆ prefixPoint k ⁻¹' D := fun _ hx => hx.2
        exact (measureReal_mono hsub).trans (le_mul_of_one_le_left measureReal_nonneg hprice)
      · have hem : F=∅ := eq_empty_iff_forall_notMem.mpr (by
          rintro ω ⟨⟨⟨t,ht,hfit⟩,hout⟩,_⟩
          apply hout
          right
          refine ⟨t,⟨?_,?_⟩,hfit⟩
          · change _+0 ≤ t
            rw [add_zero]
            exact (le_add_of_nonneg_right hT).trans ht.1
          · change t ≤ _+0+2*K^3
            rw [add_zero]
            linarith only [ht.2,hearly,lt_of_not_ge hwide])
        change pathPauliDisorderLaw.real F ≤ _
        rw [hem,measureReal_empty]
        exact mul_nonneg (div_nonneg (mul_nonneg (zero_le_one.trans (le_max_left ..))
          (by linarith only [hw])) hQ.le) measureReal_nonneg
    · have hsub : F ⊆ prefixPoint k ⁻¹' ((visit (k+1) (s k) (some (P k)) T w \
          cheapLag (k+1) (s k) (A/K) (δ*Q k)) ∩ D) := by
        rintro ω ⟨⟨⟨t,ht,hfit⟩,hout⟩,hd⟩
        exact ⟨⟨⟨t,ht,hfit.trans (by norm_num : (1/10:ℝ)≤1/8)⟩,fun hl => hout (Or.inl hl)⟩,hd⟩
      apply (measureReal_mono hsub).trans ((hlate k (s k) (some (P k)) D hD hdir T (le_of_not_ge hearly) w hw).trans _)
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right ..) (by linarith only [hw])) hQ.le) measureReal_nonneg

/-- The same price with no restriction on the Gaussian direction. -/
theorem gaussian_crossing_window_price :
    ∃ c>0, ∃ C>0, ∃ B : ℕ → Set PathPauliDisorder, (∀ k, MeasurableSet (B k)) ∧
      (∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ B k) ∧
      ∀ k : ℕ, ∀ T ≥ (0:ℝ), ∀ w ≥ (0:ℝ),
        pathPauliDisorderLaw.real (crossingWindow k c T w \ B k) ≤ C*(1+w)/((k+3:ℕ):ℝ)^(65/64:ℝ) := by
  obtain ⟨c,hc,C,hC,B,hB,he,hp⟩ := gaussian_directional_window_price
  refine ⟨c,hc,C,hC,B,hB,he,fun k T hT w hw => ?_⟩
  simpa only [preimage_univ,inter_univ,probReal_univ,mul_one] using
    hp k univ MeasurableSet.univ (fun _ _ _ _ => mem_univ _) T hT w hw

#print axioms gaussian_directional_window_price
#print axioms gaussian_crossing_window_price
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.PrescribedDelays
