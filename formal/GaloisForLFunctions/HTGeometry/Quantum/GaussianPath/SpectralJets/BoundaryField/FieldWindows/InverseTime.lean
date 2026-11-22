import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.BoundaryField.FieldWindows.EmptyReturns
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOccupationScaling
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.PhysicalTolerance

/-! # Scalar return settings within inverse time of one boundary coupling -/
open MeasureTheory Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
noncomputable section

/-- A sequential small-width, large-phase limit gives a single
width constant that works at every sufficiently late date. -/
theorem inverse_time_rectangle (P : ℝ→ℝ→Prop)
    (h : ∀ w T : ℕ→ℝ, Tendsto w atTop (𝓝 0) → (∀ᶠ n in atTop, 0<w n) →
      Tendsto (fun n => T n*w n) atTop atTop → ∀ᶠ n in atTop, P (w n) (T n)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ w T : ℝ, 0<w → w≤1/C → C≤T*w → P w T := by
  by_contra! hf
  have hfail (k : ℕ) := hf ((k:ℝ)+1) (by linarith only [Nat.cast_nonneg (α:=ℝ) k])
  choose w T hw hsmall hlarge hbad using hfail
  have hlim := squeeze_zero (fun n => (hw n).le) hsmall tendsto_one_div_add_atTop_nhds_zero_nat
  have hproduct : Tendsto (fun n => T n*w n) atTop atTop :=
    tendsto_atTop_mono (fun k => (by linarith only [hlarge k] : (k:ℝ) ≤ T k*w k)) tendsto_natCast_atTop_atTop
  obtain ⟨n,hn⟩ := (h w T hlim (Eventually.of_forall hw) hproduct).exists
  exact hbad n hn

private abbrev Reg (k : ℕ) := Matrix (Fin (k+3)→Bool) (Fin (k+3)→Bool) ℂ

/-- For each physical tolerance there are scalar settings within C/T
of the baseline at every date T≥C². Only the last onsite Z varies.
The constant may depend on the prefix, baseline and tolerance. -/
theorem gaussian_inverse_time_scalar_field :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ, ∃ B : Set ℝ, B.Countable ∧ ∀ b∉B,
      ∀ ε∈Ioo (0:ℝ) (Real.sqrt 2), ∃ C : ℝ, 1≤C ∧ ∀ T : ℝ, C^2≤T →
        ∃ z∈Icc b (b+C/T), HasProjectiveCircuitApproximation (k+3) ε 0
          (unitaryEvolution (boundaryHamiltonian ω k z) T) := by
  filter_upwards [gaussian_fixed_date_empty_returns] with ω hω
  intro k
  obtain ⟨B,hB,hret⟩ := hω k
  refine ⟨B,hB,?_⟩
  intro b hb ε hε
  obtain ⟨hx,htol⟩ := SharpOccupation.physicalArc_spec hε.1 hε.2
  let x : Icc (0:ℝ) 1 := ⟨SharpOccupation.physicalArc ε,hx.1.le,hx.2.le.trans (by norm_num)⟩
  let H (z : ℝ) : selfAdjoint (Reg k) := ⟨boundaryHamiltonian ω k z,(boundaryHermitian ω k z).isSelfAdjoint⟩
  let E (w T : ℝ) : Set ℝ := {s | T∈zeroGateReturnSet (H (b+w*s)) x}
  let μ : Measure ℝ := unitIntervalProbabilityMeasure
  have hpos : 0 < zeroGateArcOccupationPolynomial (2^(k+3)) x := by
    rw [←zeroGateFullArcMass_eq_exactPolynomial]
    exact (pow_pos hx.1 _).trans_le (zeroGateFullArcMass_bounds (k+3) x).1
  obtain ⟨C,hC,hrect⟩ := inverse_time_rectangle (fun w T => 0 < μ.real (E w T))
    (fun w T hw hp ht => (hret b hb x w T hw hp ht).eventually (Ioi_mem_nhds hpos))
  refine ⟨C,hC,?_⟩
  intro T hT
  have hC0 := zero_lt_one.trans_le hC
  have ht := (sq_pos_of_pos hC0).trans_le hT
  let w := C/T
  have hw : 0 < w := div_pos hC0 ht
  have hsmall : w≤1/C := (div_le_div_iff₀ ht hC0).mpr (by linarith only [hT])
  have hlarge : C≤T*w := by dsimp [w]; rw [mul_div_cancel₀ _ ht.ne']
  have hm := hrect w T hw hsmall hlarge
  have hchoose : ∃ u∈Ioc (0:ℝ) 1, u∈E w T := by
    by_contra! hn
    have hu : ∀ᵐ u ∂μ, u∈Ioc (0:ℝ) 1 := ae_restrict_mem measurableSet_Ioc
    have hzero : μ (E w T)=0 := measure_eq_zero_iff_ae_notMem.mpr (hu.mono hn)
    simp only [measureReal_def,hzero,ENNReal.toReal_zero,lt_self_iff_false] at hm
  obtain ⟨u,hu,he⟩ := hchoose
  refine ⟨b+w*u,⟨le_add_of_nonneg_right (mul_nonneg hw.le hu.1.le),
    add_le_add_right (mul_le_of_le_one_right hw.le hu.2) b⟩,?_⟩
  change orbitCircuitDistance (H (b+w*u)) 0 T ≤ zeroGateArcTolerance x at he
  rw [show zeroGateArcTolerance x=ε from htol] at he
  exact (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr he

#print axioms gaussian_inverse_time_scalar_field
end
end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.FieldWindows
