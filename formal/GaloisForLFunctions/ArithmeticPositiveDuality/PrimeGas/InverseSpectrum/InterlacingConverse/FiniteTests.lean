import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.InterlacingConverse.Closure
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.TraceProbes

/-! # Finite scalar tests for a uniform physical trace inequality -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Set the chosen occupations independently and leave every other level at its full weight. -/
def finiteProfile (F : Finset ℕ) (x : ℕ → ℝ) (hx : ∀ k ∈ F, x k ∈ Icc (occupationWeight (k+1)) (occupationWeight k)) :
    SpectralBand 1 := fun k => if h : k ∈ F then ⟨x k,hx k h⟩ else hotEdge 1 k

theorem finiteProfile_partition (F : Finset ℕ) (x : ℕ → ℝ) (hx) (z : ℂ) :
    relativePartition (finiteProfile F x hx) z =
      ∑ k ∈ F, ((occupationWeight k:ℂ)^z-(x k:ℂ)^z) := by
  unfold relativePartition
  rw [tsum_eq_sum (s := F) (fun k hk => by simp only [complexDrop,finiteProfile,dif_neg hk,hotEdge,sub_self])]
  exact Finset.sum_congr rfl (fun k hk => by simp only [complexDrop,finiteProfile,dif_pos hk])

theorem finiteProfile_quadratic (F : Finset ℕ) (x : ℕ → ℝ) (hx) :
    relativeReading quadraticResponse (finiteProfile F x hx) =
      ∑ k ∈ F, (occupationWeight k^2-(x k)^2) := by
  unfold relativeReading
  rw [tsum_eq_sum (s := F) (fun k hk => by simp only [spectralDrop,finiteProfile,dif_neg hk,hotEdge,sub_self])]
  exact Finset.sum_congr rfl (fun k hk => by simp only [spectralDrop,finiteProfile,dif_pos hk,quadraticResponse])

/-- A uniform physical estimate is equivalent to its elementary finite scalar inequalities, with the same coefficient. -/
theorem rank_one_trace_finite_iff {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) :
    traceControlsAt 1 z p K ↔ ∀ (F : Finset ℕ) (x : ℕ → ℝ),
      (∀ k ∈ F, x k ∈ Icc (occupationWeight (k+1)) (occupationWeight k)) →
      ‖∑ k ∈ F, ((occupationWeight k:ℂ)^z-(x k:ℂ)^z)‖^p ≤ K*∑ k ∈ F, (occupationWeight k^2-(x k)^2) := by
  constructor
  · intro h F x hx
    have hb : finiteProfile F x hx ∈ closure (physicalSpectra 1) := by
      rw [closure_rank_one_spectra]
      exact mem_univ _
    have hw := trace_control_on_closure hz hp.le h hb
    rwa [finiteProfile_partition,finiteProfile_quadratic] at hw
  · intro h P hd hc
    let b := physicalSpectrum P hd hc
    have hL := ((summable_complexDrop b hz).hasSum.tendsto_sum_nat).norm
    have hD := (summable_spectralDrop quadraticResponse b).hasSum.tendsto_sum_nat
    rw [← quadratic_physicalReading P hd hc]
    exact le_of_tendsto_of_tendsto (((Real.continuous_rpow_const hp.le).tendsto _).comp hL)
      (hD.const_mul K) (Eventually.of_forall fun n => h (Finset.range n) (fun k => (b k).val) (fun k _ => (b k).property))

#print axioms rank_one_trace_finite_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
