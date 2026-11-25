import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.PhysicalNeighbors
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw

/-! # Field stability at the first low-gate return as precision increases -/
open Filter MeasureTheory Set Topology Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
open PrecisionReturns
noncomputable section

/-- A positive logarithmic precision exponent forces the absolute date to diverge. -/
theorem diverges_of_precision_exponent {v : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hpos : ∀ ε > 0, 0 < v ε)
    (h : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    Tendsto v (𝓝[>] (0:ℝ)) atTop := by
  apply tendsto_atTop.mpr
  intro L
  have hb := (tendsto_const_div_log_one_div (log (max L 1))).eventually_lt_const (half_pos hd)
  filter_upwards [hb,h.eventually_const_lt (half_lt_self hd),Ioo_mem_nhdsGT (zero_lt_one' ℝ)]
    with ε h1 h2 hε
  have hlog := log_pos ((one_lt_div hε.1).mpr hε.2)
  have hh := (div_lt_div_iff_of_pos_right hlog).mp (h1.trans h2)
  exact (le_max_left L 1).trans ((log_lt_log_iff (lt_max_of_lt_right zero_lt_one) (hpos ε hε.1)).mp hh).le

/-- At the actual first return at precision ε the terminal field is stable
through radius 1/(20v), where v is the absolute return date. A one-sided
change of at most C/v reaches a full interval above the near-Hilbert budget.
Both comparisons use operator error 1/10 and the original draw. -/
theorem gaussian_first_precision_return_field_width :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let K (z : ℝ) : selfAdjoint (Register N) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
      ∃ σ > 0, orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∃ C > (0:ℝ), ∀ s : ℕ, 2*s<N → ∀ᶠ ε : ℝ in 𝓝[>] 0,
          let v := firstVisit H σ s ε
          (∀ z : ℝ, v*|z|≤1/20 → orbitCircuitDistance (K z) s v ≤ 1/10) ∧
          ∃ u∈Icc (0:ℝ) (C/v), ∀ z : ℝ, v*|z-u|≤1/400 → 1/10<orbitCircuitDistance (K z) P v := by
  filter_upwards [gaussian_physical_inverse_time_neighbors,gaussian_first_return_precision_exponent,
    gaussian_first_crossing_precision_wait] with ω hpair hret hcross
  filter_upwards [hpair,hcross] with k hk hc
  intro N H P K
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hc
  obtain ⟨C,hC,hT⟩ := hk
  refine ⟨σ,hσ,he,hbefore,C,hC,?_⟩
  intro s hs
  let v := firstVisit H σ s
  obtain ⟨hmin,hexp,_⟩ := hret k σ hσ s hs
  have hd : (3:ℕ) ≤ 2^N := (by decide : 3≤2^3).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  have hpos (ε : ℝ) (hε : 0<ε) : 0 < v ε := hσ.trans_le (hmin ε hε).1.1
  have hv := diverges_of_precision_exponent (by exact_mod_cast (show 0<2^N-2 by omega)) hpos hexp
  filter_upwards [hv.eventually hT,Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1/20)] with ε hp hε
  obtain ⟨_,_,u,hu,_,hhi⟩ := hp
  refine ⟨?_,u,hu,hhi⟩
  intro z hz
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mp (hmin ε hε.1).1.2
  have hh := field_distance_le ω k s z 0 (v ε)
  change orbitCircuitDistance (K z) s (v ε) ≤ orbitCircuitDistance (K 0) s (v ε) + |v ε| * |z-0| at hh
  rw [abs_of_pos (hpos ε hε.1),sub_zero] at hh
  have hbase : orbitCircuitDistance (K 0) s (v ε) ≤ ε := by
    simpa only [orbitCircuitDistance,K,boundaryHamiltonian,Complex.ofReal_zero,zero_smul,add_zero] using hfit
  change orbitCircuitDistance (K z) s (v ε) ≤ 1/10
  linarith only [hh,hbase,hz,hε.2]

#print axioms gaussian_first_precision_return_field_width
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
