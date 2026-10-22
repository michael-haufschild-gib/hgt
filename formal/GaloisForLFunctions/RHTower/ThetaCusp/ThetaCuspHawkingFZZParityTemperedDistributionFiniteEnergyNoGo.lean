import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParityTemperedDistributionLocalProbeNoGo

/-!
# Finite-energy obstruction for distributional FZZ reflection

The tempered-distribution completion is the broadest regular FZZ reflection class currently left
by the corpus.  Exact complex-order covariance already fixes one canonical moving-probe response
to the reciprocal-Fermi ultraviolet weight.  That response is uniformly bounded away from zero
(in fact it grows exponentially), so neither its absolute response nor its squared response is
summable.

Consequently universal FZZ reflection has no trace-summable or finite-energy/Fock realization even
after finite measures are replaced by tempered distributions.  A surviving FZZ-P reflection arrow
must therefore be singular and non-Fock before the still-missing source phase law is addressed.

`[FZZ-P ROUTE-CLASS KILL] [TEMPERED DISTRIBUTION] [FINITE ENERGY] [NEW KNOWLEDGE]`
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Square-summability of the canonical ultraviolet moving-probe response: the minimal Hilbert/Fock
finite-energy condition on a source-faithful distributional FZZ reflection. -/
def FZZCigarParityTemperedDistributionFEReflectionData.FiniteEnergy
    (D : FZZCigarParityTemperedDistributionFEReflectionData) : Prop :=
  Summable (fun n : ℕ => (D.uvLocalProbeResponse n) ^ (2 : ℕ))

/-- The forced reciprocal-Fermi ultraviolet response is uniformly separated from zero.  This is
the sharp positive survivor needed by both trace and energy obstructions. -/
theorem fzzCigarParityForcedLocal_uvUniformLowerBound
    (n : ℕ) :
    Real.exp 1 / (Real.exp 1 + 1) ≤
      fzzCigarParityForcedLocalFEReflectionData.uvWeight n := by
  apply le_trans ?_ (fzzCigarParityForcedLocalFEReflectionData.exp_div_le_uvWeight n)
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < Real.exp 1 + 1)).2
  exact Real.exp_le_exp.mpr (by
    exact_mod_cast Nat.le_add_left 1 n)

/-- No source-faithful tempered-distribution FZZ reflection has finite canonical probe energy. -/
theorem FZZCigarParityTemperedDistributionFEReflectionData.not_finiteEnergy
    (D : FZZCigarParityTemperedDistributionFEReflectionData) :
    ¬ D.FiniteEnergy := by
  intro hsum
  have hzero : Tendsto
      (fun n : ℕ => (D.uvLocalProbeResponse n) ^ (2 : ℕ)) atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  let c : ℝ := Real.exp 1 / (Real.exp 1 + 1)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hlower : ∀ n : ℕ, c ^ (2 : ℕ) ≤ (D.uvLocalProbeResponse n) ^ (2 : ℕ) := by
    intro n
    have hcn : c ≤ D.uvLocalProbeResponse n := by
      rw [D.uvLocalProbeResponse_eq_forced]
      exact fzzCigarParityForcedLocal_uvUniformLowerBound n
    exact pow_le_pow_left₀ hc.le hcn 2
  have hcontra : c ^ (2 : ℕ) ≤ 0 :=
    ge_of_tendsto hzero (Eventually.of_forall hlower)
  nlinarith [sq_pos_of_pos hc]

/-- The stronger trace-level obstruction: the unsquared canonical response is not summable. -/
theorem FZZCigarParityTemperedDistributionFEReflectionData.uvLocalProbeResponse_not_summable
    (D : FZZCigarParityTemperedDistributionFEReflectionData) :
    ¬ Summable D.uvLocalProbeResponse := by
  intro hsum
  have hzero : Tendsto D.uvLocalProbeResponse atTop (𝓝 0) :=
    hsum.tendsto_atTop_zero
  let c : ℝ := Real.exp 1 / (Real.exp 1 + 1)
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hlower : ∀ n : ℕ, c ≤ D.uvLocalProbeResponse n := by
    intro n
    rw [D.uvLocalProbeResponse_eq_forced]
    exact fzzCigarParityForcedLocal_uvUniformLowerBound n
  have hcontra : c ≤ 0 :=
    ge_of_tendsto hzero (Eventually.of_forall hlower)
  linarith

/-- Union of the trace-summable and Hilbert/Fock finite-energy distributional FZZ classes. -/
def FZZCigarParityTemperedDistributionFEReflectionData.FiniteTraceOrEnergy
    (D : FZZCigarParityTemperedDistributionFEReflectionData) : Prop :=
  Summable D.uvLocalProbeResponse ∨ D.FiniteEnergy

/-- Premise-free finite-energy route kill. -/
theorem no_finiteEnergy_FZZCigarParityTemperedDistributionFEReflectionData :
    ¬ ∃ D : FZZCigarParityTemperedDistributionFEReflectionData,
      D.FiniteEnergy := by
  rintro ⟨D, hD⟩
  exact D.not_finiteEnergy hD

/-- **[FZZ-P FINITE-ENERGY DISTRIBUTIONAL ROUTE KILL].**  Universal complex-order reflection of
the literal FZZ parity source admits neither a trace-summable canonical response nor a finite-energy
tempered-distribution realization. -/
theorem no_finiteTraceOrEnergy_FZZCigarParityTemperedDistributionFEReflectionData :
    ¬ ∃ D : FZZCigarParityTemperedDistributionFEReflectionData,
      D.FiniteTraceOrEnergy := by
  rintro ⟨D, htrace | henergy⟩
  · exact D.uvLocalProbeResponse_not_summable htrace
  · exact D.not_finiteEnergy henergy

end

end RHTower
