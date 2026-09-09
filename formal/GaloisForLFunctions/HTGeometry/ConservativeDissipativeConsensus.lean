import GaloisForLFunctions.HTGeometry.ConservativeDissipativeMixingContraction
import GaloisForLFunctions.HTGeometry.ConservativeDissipativeEntropyIterations

set_option autoImplicit false

/-!
# Convergence of adaptive positive transport to consensus

The Schaffer–Exl energy mechanism (arXiv:2609.04530), combined with the
uniform implicit complete-mixing contraction, yields geometric convergence
of actual positive densities. Raw network coefficients and time steps may
change arbitrarily with time and state. The limiting density is the initial
positive-reference average, fixed by population conservation. Logarithmic
states, physical populations, and relative Boltzmann energies converge, and
total physical-plus-temporal entropy loss equals the explicit initial-to-limit
energy difference.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Average of a density against the constructed positive reference. -/
def transportAverage (r p : ι → ℝ) : ℝ :=
  (∑ i, Real.exp (r i) * p i) / transportReferenceMass r

/-- The positive-reference mean lies between the density extrema. -/
theorem transportAverage_interval (r p : ι → ℝ) :
    transportMin p ≤ transportAverage r p ∧ transportAverage r p ≤ transportMax p := by
  have hm := transportReferenceMass_pos r
  constructor
  · apply (le_div_iff₀ hm).mpr
    rw [transportReferenceMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_left (transportMin_le p i) (Real.exp_pos (r i)).le]
  · apply (div_le_iff₀ hm).mpr
    rw [transportReferenceMass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [mul_le_mul_of_nonneg_left (le_transportMax p i) (Real.exp_pos (r i)).le]

/-- Oscillation bounds the error at each coordinate relative to the positive-reference mean. -/
theorem abs_sub_transportAverage_le_oscillation (r p : ι → ℝ) (i : ι) :
    |p i - transportAverage r p| ≤ transportOscillation p := by
  have hm := transportAverage_interval r p
  have hl := transportMin_le p i
  have hh := le_transportMax p i
  unfold transportOscillation
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The conserved consensus density is strictly positive for every logarithmic input. -/
theorem transportAverage_exp_pos (r x : ι → ℝ) :
    0 < transportAverage r (fun i => Real.exp (x i)) := by
  apply div_pos _ (transportReferenceMass_pos r)
  exact Finset.sum_pos (fun i _ => mul_pos (Real.exp_pos _) (Real.exp_pos _)) Finset.univ_nonempty

/-- Logarithmic implicit evolution with arbitrary adaptive complete mixing. -/
def consensusLogOrbit (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) : ℕ → ι → ℝ :=
  implicitEntropyOrbit (fun n y => mixingCoefficients (a n y)) r (fun n y => mixingStep (u n y)) x

/-- Actual positive densities along the adaptive complete-mixing trajectory. -/
def consensusDensity (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) (i : ι) : ℝ :=
  Real.exp (consensusLogOrbit a r u x n i)

omit [Nonempty ι] in
/-- The nonlinear adaptive log update reconstructs the genuine linear density solve at each step. -/
theorem consensusDensity_step (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) :
    consensusDensity a r u x (n + 1) =
      densityImplicitStep (mixingCoefficients (a n (consensusLogOrbit a r u x n))) r
        (mixingStep (u n (consensusLogOrbit a r u x n))) (consensusDensity a r u x n) := by
  funext i
  exact exp_implicitEntropyLog _ _ _ _ i

omit [Nonempty ι] in
/-- The positive-reference average is conserved under arbitrary adaptive complete mixing. -/
theorem consensusDensity_average (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) :
    transportAverage r (consensusDensity a r u x n) = transportAverage r (fun i => Real.exp (x i)) := by
  simp only [transportAverage, consensusDensity, consensusLogOrbit, ← Real.exp_add,
    implicitEntropyOrbit_mass]

/-- Uniform geometric decay of density oscillation, independent of network adaptation. -/
theorem consensusDensity_oscillation_bound (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) :
    transportOscillation (consensusDensity a r u x n) ≤
      transportContraction r ^ n * transportOscillation (fun i => Real.exp (x i)) := by
  induction n with
  | zero =>
    change transportOscillation (fun i => Real.exp (x i)) ≤
      transportContraction r ^ 0 * transportOscillation (fun i => Real.exp (x i))
    simp only [pow_zero, one_mul, le_refl]
  | succ n ih =>
    rw [consensusDensity_step]
    calc
      _ ≤ transportContraction r * transportOscillation (consensusDensity a r u x n) :=
        densityImplicitStep_oscillation_contract _ _ _ _
      _ ≤ transportContraction r * (transportContraction r ^ n * transportOscillation (fun i => Real.exp (x i))) :=
        mul_le_mul_of_nonneg_left ih (transportContraction_nonneg r)
      _ = _ := by rw [pow_succ]; ring

/-- Every density coordinate has an explicit geometric error bound to the conserved consensus. -/
theorem consensusDensity_error_bound (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (n : ℕ) (i : ι) :
    |consensusDensity a r u x n i - transportAverage r (fun j => Real.exp (x j))| ≤
      transportContraction r ^ n * transportOscillation (fun j => Real.exp (x j)) := by
  have h := abs_sub_transportAverage_le_oscillation r (consensusDensity a r u x n) i
  rw [consensusDensity_average] at h
  exact h.trans (consensusDensity_oscillation_bound a r u x n)

/-- Actual density convergence, despite unrestricted time- and state-dependent network changes. -/
theorem consensusDensity_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) :
    Filter.Tendsto (fun n => consensusDensity a r u x n i) Filter.atTop
      (nhds (transportAverage r (fun j => Real.exp (x j)))) := by
  have hp : Filter.Tendsto
      (fun n : ℕ => transportContraction r ^ n * transportOscillation (fun j => Real.exp (x j)))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (transportContraction_nonneg r)
        (transportContraction_lt_one r)).mul_const (transportOscillation (fun j => Real.exp (x j)))
  have h := squeeze_zero (fun n => abs_nonneg
      (consensusDensity a r u x n i - transportAverage r (fun j => Real.exp (x j))))
    (fun n => consensusDensity_error_bound a r u x n i) hp
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using h)

/-- The actual logarithmic state converges to the log of its conserved density average. -/
theorem consensusLogOrbit_tendsto_coord (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) :
    Filter.Tendsto (fun n => consensusLogOrbit a r u x n i) Filter.atTop
      (nhds (Real.log (transportAverage r (fun j => Real.exp (x j))))) := by
  have h := (consensusDensity_tendsto a r u x i).log (transportAverage_exp_pos r x).ne'
  simpa only [consensusDensity, Real.log_exp] using h

/-- Convergence of the whole finite logarithmic state, not only its energy. -/
theorem consensusLogOrbit_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) :
    Filter.Tendsto (consensusLogOrbit a r u x) Filter.atTop
      (nhds (fun _ => Real.log (transportAverage r (fun j => Real.exp (x j))))) :=
  tendsto_pi_nhds.mpr (fun i => consensusLogOrbit_tendsto_coord a r u x i)

/-- The limiting physical population is the prescribed reference times conserved total density. -/
theorem consensusPopulation_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) (i : ι) :
    Filter.Tendsto (fun n => Real.exp (r i + consensusLogOrbit a r u x n i)) Filter.atTop
      (nhds (Real.exp (r i) * transportAverage r (fun j => Real.exp (x j)))) := by
  simpa only [consensusDensity, Real.exp_add] using
    (consensusDensity_tendsto a r u x i).const_mul (Real.exp (r i))

/-- Limiting entropy of the actual convergent adaptive trajectory. -/
theorem consensusLogOrbit_energy_tendsto (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) :
    Filter.Tendsto (fun n => relativeEntropyEnergy r (consensusLogOrbit a r u x n)) Filter.atTop
      (nhds (relativeEntropyEnergy r (fun _ => Real.log (transportAverage r (fun j => Real.exp (x j)))))) := by
  have hc : Continuous (relativeEntropyEnergy r) := by unfold relativeEntropyEnergy; fun_prop
  exact hc.continuousAt.tendsto.comp (consensusLogOrbit_tendsto a r u x)

/-- All lost entropy is accounted for exactly by the explicit consensus energy. -/
theorem consensus_total_entropy_loss (a : ℕ → (ι → ℝ) → ι → ι → ℝ) (r : ι → ℝ)
    (u : ℕ → (ι → ℝ) → ℝ) (x : ι → ℝ) :
    ∑' n, implicitEntropyOrbitLoss (fun k y => mixingCoefficients (a k y)) r
        (fun k y => mixingStep (u k y)) x n =
      relativeEntropyEnergy r x -
        relativeEntropyEnergy r (fun _ => Real.log (transportAverage r (fun j => Real.exp (x j)))) := by
  have h := implicitEntropyOrbit_energy_tendsto (fun k y => mixingCoefficients (a k y)) r
    (fun k y => mixingStep (u k y)) x
  have he := tendsto_nhds_unique h (consensusLogOrbit_energy_tendsto a r u x)
  linarith

end
end GaloisForLFunctions.HTGeometry.SchafferExl
