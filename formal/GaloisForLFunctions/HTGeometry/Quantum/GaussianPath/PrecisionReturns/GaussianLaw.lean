import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.ExponentTransfer
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GapSpectrum
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.UntouchedSites.CircuitReturns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingWidth

/-! # Sharp precision exponent of the first continuous low-gate return -/
open Matrix MeasureTheory Filter Topology Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns
noncomputable section

private theorem elapsed_exponent {v : ℝ → ℝ} {a d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hv : ∀ ε > 0, a ≤ v ε)
    (h : Tendsto (fun ε => log (v ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d)) :
    Tendsto (fun ε => log (v ε-a)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 d) := by
  have hb := (tendsto_const_div_log_one_div (log (2*a))).eventually_lt_const (half_pos hd)
  have hl := h.eventually_const_lt (half_lt_self hd)
  have he : ∀ᶠ ε : ℝ in 𝓝[>] (0:ℝ), 2*a < v ε ∧ 0 < log (1/ε) := by
    filter_upwards [hb,hl,Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h1 h2 hε
    have hlog := log_pos ((one_lt_div hε.1).mpr hε.2)
    have hh := (div_lt_div_iff_of_pos_right hlog).mp (h1.trans h2)
    exact ⟨(log_lt_log_iff (by positivity : 0<2*a) (ha.trans_le (hv ε hε.1))).mp hh,hlog⟩
  have hh := h.sub (tendsto_const_div_log_one_div (log 2))
  rw [sub_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hh h
  · filter_upwards [he] with ε hε
    have hm : v ε/2 ≤ v ε-a := by linarith only [hε.1]
    have hp : 0 < v ε/2 := by linarith only [hε.1,ha]
    rw [←sub_div,←log_div (by linarith only [hp]) (by norm_num)]
    exact div_le_div_of_nonneg_right (log_le_log hp hm) hε.2.le
  · filter_upwards [he] with ε hε
    exact div_le_div_of_nonneg_right (log_le_log (by linarith only [hε.1,ha]) (sub_le_self _ ha.le)) hε.2.le

/-- For almost every chain, fix any prefix of at least three sites and any
positive observation origin, even one chosen from the whole draw. At every
budget below half the qubit count the first subsequent return, and its
elapsed waiting time, have precision exponent exactly 2ᴺ−2. -/
theorem gaussian_first_return_precision_exponent :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∀ a : ℝ, 0<a → ∀ s : ℕ, 2*s<N →
        (∀ ε > 0, IsLeast (visitSet H a s ε) (firstVisit H a s ε)) ∧
        Tendsto (fun ε => log (firstVisit H a s ε)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) ∧
        Tendsto (fun ε => log (firstVisit H a s ε-a)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_gap_clock,UntouchedSites.gaussian_few_gate_scalar_return] with ω hspec hcomm k
  intro N H a ha s hs
  have hdim : 3 ≤ (2:ℕ)^N := (by decide : 3 ≤ 2^3).trans (Nat.pow_le_pow_right (by decide) (by dsimp [N]; omega))
  obtain ⟨e,hg,hy⟩ := hspec k
  obtain ⟨A,hA,h⟩ := hcomm (k+1)
  have hh := exponent_of_scalar_control H e s hA (fun t ε => h t ε s hs) hg hy ha
  have he : 2^N-3+1=2^N-2 := by omega
  change Tendsto _ _ (𝓝 ((2^N-3+1:ℕ):ℝ)) at hh
  rw [he] at hh
  refine ⟨fun ε hε => firstVisit_isLeast H a s hε,hh,elapsed_exponent ha ?_ (fun ε hε => (firstVisit_isLeast H a s hε).1.1) hh⟩
  exact_mod_cast (show 0 < 2^N-2 by omega)

#print axioms gaussian_first_return_precision_exponent

/-- Starting specifically at the first near-Hilbert-budget crossing yields
the same law for the elapsed first wait on that very draw. -/
theorem gaussian_first_crossing_precision_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > 0, orbitCircuitDistance H P σ = 9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        ∀ s : ℕ, 2*s<N →
          Tendsto (fun ε => log (firstVisit H σ s ε-σ)/log (1/ε)) (𝓝[>] (0:ℝ)) (𝓝 ((2^N-2:ℕ):ℝ)) := by
  filter_upwards [gaussian_first_return_precision_exponent,LocalPatches.gaussian_first_crossing_local_width] with ω hr hw
  filter_upwards [hw] with k hk
  intro N H P
  obtain ⟨σ,hσ,he,hbefore,_⟩ := hk
  have hpos : 0 < σ := (show 0 ≤ LocalPatches.localCrossingWidth N by
    unfold LocalPatches.localCrossingWidth; positivity).trans_lt hσ
  exact ⟨σ,hpos,he,hbefore,fun s hs => (hr k σ hpos s hs).2.2⟩

#print axioms gaussian_first_crossing_precision_wait
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns
