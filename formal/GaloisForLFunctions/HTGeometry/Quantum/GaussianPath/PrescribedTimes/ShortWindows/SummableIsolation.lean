import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries

/-! # Summable probabilities for isolated physical visits on one Gaussian chain -/
open Set MeasureTheory Filter Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section

/-- If the inverse grid sizes are summable, a typical infinite chain
eventually misses every isolated hit, even though its prefixes are dependent. -/
theorem eventually_no_isolated (E : (k : ℕ) → Set (PrefixIndex (k+1) → ℝ))
    (hE : ∀ k, MeasurableSet (E k)) (m : ℕ → ℕ) (a : (k : ℕ) → Fin (m k) → ℝ)
    (hm : Summable fun k => ((m k:ℝ))⁻¹)
    (hp : ∀ᶠ k : ℕ in atTop, 0 < m k ∧ ∀ i, 1 ≤ a k i ∧
      (Fintype.card (PrefixIndex (k+1)):ℝ)*(a k i-1) ≤ 1) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, prefixPoint k ω ∉ isolated (a k) (E k) := by
  let μ := pathPauliDisorderLaw
  letI : IsProbabilityMeasure μ := by dsimp [μ,pathPauliDisorderLaw]; infer_instance
  let B (k : ℕ) := isolated (a k) (E k)
  let A (k : ℕ) := prefixPoint k ⁻¹' B k
  have hs : Summable (fun k => μ.real (A k)) := by
    apply (hm.mul_left (exp 1)).of_norm_bounded_eventually_nat
    filter_upwards [hp] with k hk
    rw [Real.norm_of_nonneg measureReal_nonneg,←div_eq_mul_inv]
    apply (le_div_iff₀ (by exact_mod_cast hk.1 : (0:ℝ) < m k)).mpr
    have h := gaussian_isolated_mass (hE k) (fun i => (hk.2 i).1) (fun i => (hk.2 i).2)
    have he := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
      (measurable_isolated (a k) (hE k)).nullMeasurableSet
    change μ.real (A k)=(centredProductGaussian (PrefixIndex (k+1)) 1).real (B k) at he
    change (m k:ℝ)*(centredProductGaussian (PrefixIndex (k+1)) 1).real (B k) ≤ exp 1 at h
    rwa [mul_comm,he]
  apply ae_eventually_notMem (μ:=μ) (s:=A)
  simpa only [ofReal_measureReal (measure_ne_top μ _)] using hs.tsum_ofReal_ne_top

#print axioms eventually_no_isolated
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
