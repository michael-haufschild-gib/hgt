import GaloisForLFunctions.HTGeometry.Quantum.IntegerClockPhaseEquidistribution
import GaloisForLFunctions.HTGeometry.Quantum.DyadicCircuitCapture
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-!
# Circuit shortcuts on a prescribed clock

For each prescribed injective sequence of integer observation times, draw the
static chain once. Its empirical shortcut-run frequencies satisfy the same
bounds as continuous late-time sampling, even for the clock 1, 2, 4, … .
-/
open Filter Set MeasureTheory
open scoped Topology Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open StaticLocalLaboratoryComplexityGrowthLaw

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem physical_seed_continuous (L : ℕ) :
    Continuous (RHTower.pairQubitProjectivePauliSeed L) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ =>
    (0 : Reg (L*2)) i j + ∑ t, (p t : ℂ) * _)
  fun_prop

private theorem physical_seed_scale (L : ℕ) (a : ℝ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    RHTower.pairQubitProjectivePauliSeed L (a • p) = (a:ℂ) • RHTower.pairQubitProjectivePauliSeed L p := by
  ext i j
  simp only [RHTower.pairQubitProjectivePauliSeed,Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,
    nearestNeighborPathLocalHamiltonian,realAffineMatrix,Matrix.zero_apply,zero_add,
    Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,Matrix.smul_apply,Finset.mul_sum,mul_assoc]


/-- Pulling back an observed phase event gives exactly the empirical time
fraction, including repeated hits and all endpoints of the prefix. -/
private theorem prefix_phase_preimage {d : ℕ} (ω : Fin d → ℝ) (b : ℕ → ℤ) (N : ℕ)
    {A : Set (Fin d → UnitAddCircle)} (hA : MeasurableSet A) :
    (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ) (finiteClockPhasePoint ω ⁻¹' A) =
      (integerClockPrefixLaw (fun j => finiteClockPhasePoint ω (b j)) N : Measure _) A := by
  simp only [integerClockPrefixLaw,ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply (measurable_of_finite _) (hA.preimage (finiteClockPhasePoint_continuous ω).measurable),
    Measure.map_apply (measurable_of_finite _) hA]
  rfl

private theorem prescribed_peak_positive {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (b : ℕ → ℤ) (m : ℕ) (hm : 0 < m)
    (hmax : IsRecurrentOrbitCircuitMaximum H m)
    (hclock : Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint
      (RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))) (b j))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d)))) :
    0 < atTop.liminf (fun N => (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ)
      {t | ¬ HasProjectiveCircuitApproximation n (1/10:ℝ) (m-1) (unitaryEvolution (H : Reg n) t)}) := by
  let ω := RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let A := (projectiveContinuousCircuitCaptureTarget e V (m-1) (1/10:ℝ))ᶜ
  have hA : IsOpen A := (isClosed_projectiveContinuousCircuitCaptureTarget e V _ _).isOpen_compl
  obtain ⟨G,w,_,hw,hvisit⟩ := hmax.2
  obtain ⟨u,_,hu⟩ := hvisit 0
  have hne : A.Nonempty := by
    refine ⟨finiteClockPhasePoint ω u,?_⟩
    intro h
    obtain ⟨c,hc,C,hC,he⟩ := (physical_circuit_approximation_iff_spectral_capture e H (m-1) _ u).mpr h
    have hge := hu u ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ c hc C he
    omega
  have heq : {t | ¬ HasProjectiveCircuitApproximation n (1/10:ℝ) (m-1) (unitaryEvolution (H : Reg n) t)} =
      finiteClockPhasePoint ω ⁻¹' A := by
    ext t
    exact not_congr (physical_circuit_approximation_iff_spectral_capture e H (m-1) _ t)
  simp only [heq,prefix_phase_preimage ω b _ hA.measurableSet]
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hclock hA
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hlim
  exact (hA.measure_pos volume hne).trans_le hlim

private theorem prescribed_returns_positive {n d : ℕ} (e : (Fin n → Bool) ≃ Fin (d+1))
    (H : selfAdjoint (Reg n)) (b : ℕ → ℤ)
    (hclock : Tendsto (integerClockPrefixLaw (fun j => finiteClockPhasePoint
      (RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))) (b j))) atTop
      (𝓝 (finiteTorusHaarProbabilityMeasure (Fin d)))) (ε : ℝ) (hε : 0 < ε) :
    0 < atTop.liminf (fun N => (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ)
      {t | HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution (H : Reg n) t)}) := by
  let ω := RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  let D (θ) := Metric.infDist (projectiveSpectralMatrix e V θ) (phaseCircuitMatrixImageAtMost n 0)
  let A := {θ | D θ < ε}
  have hA : IsOpen A := isOpen_lt
    ((Metric.continuous_infDist_pt _).comp (continuous_projectiveSpectralMatrix e V)) continuous_const
  have hmin (t δ : ℝ) : D (finiteClockPhasePoint ω t) ≤ δ ↔ HasProjectiveCircuitApproximation n δ 0
      (unitaryEvolution (H : Reg n) t) := by
    rw [physical_circuit_approximation_iff_spectral_capture e H]
    exact (hasProjectiveCircuitApproximation_iff_infDist _ 0 δ).symm.trans
      (mem_projectiveContinuousCircuitCaptureTarget_iff e V 0 δ _).symm
  have hz : HasProjectiveCircuitApproximation n 0 0 (unitaryEvolution (H : Reg n) 0) := by
    refine ⟨1,by simp,TwoQubitCircuit.one n,le_rfl,?_⟩
    simp [unitaryEvolution,TwoQubitCircuit.one_eval]
  have hne : A.Nonempty := ⟨finiteClockPhasePoint ω 0, ((hmin 0 0).mpr hz).trans_lt hε⟩
  have hsub : finiteClockPhasePoint ω ⁻¹' A ⊆
      {t | HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution (H : Reg n) t)} :=
    fun t ht => (hmin t ε).mp (le_of_lt ht)
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hclock hA
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hlim
  refine ((hA.measure_pos volume hne).trans_le hlim).trans_le (Filter.liminf_le_liminf ?_)
  apply Eventually.of_forall
  intro N
  rw [← prefix_phase_preimage ω b N hA.measurableSet]
  exact measure_mono hsub

/-- Upper frequency of affordable doubling runs, lower frequencies of exact
orbital peaks and zero-gate returns, and permanent locality of the same draw. -/
def PrescribedClockCircuitStatistics (b : ℕ → ℤ) (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) : Prop :=
  let n := L*2
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let r := excursionGateBudget n
  (∀ k : ℕ, atTop.limsup (fun N => (integerClockPrefixLaw (fun j => (b j : ℝ)) N : Measure ℝ)
    (physicalDyadicCircuitHits H r k)) ≤ ENNReal.ofReal ((1/(r+1:ℝ)^(2*r))^k)) ∧
  (∃ m > r, IsRecurrentOrbitCircuitMaximum H m ∧
    0 < atTop.liminf (fun N => (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ)
      {t | ¬ HasProjectiveCircuitApproximation n (1/10:ℝ) (m-1) (unitaryEvolution (H : Reg n) t)})) ∧
  (∀ ε : ℝ, 0 < ε → 0 < atTop.liminf (fun N => (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ)
    {t | HasProjectiveCircuitApproximation n ε 0 (unitaryEvolution (H : Reg n) t)})) ∧
    RHTower.NearestNeighborPathPermanentLocalityHaarSeparation L p

/-- Every injective integer clock fixed before the draw exhibits the circuit
statistics of the static Gaussian chain at almost every realization. -/
theorem gaussianPath_prescribed_integer_clock_circuit_runs (b : ℕ → ℤ) (hb : Function.Injective b) :
    ∀ᶠ L : ℕ in atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      PrescribedClockCircuitStatistics b L p := by
  have hcof : Tendsto (fun L : ℕ => L*2) atTop atTop := by
    rw [tendsto_atTop]; intro N; exact eventually_atTop.2 ⟨N,fun L h => by omega⟩
  filter_upwards [eventually_ge_atTop 1,hcof.eventually eventually_nearHilbertContinuousCircuitEntropy_lt_projectiveBooleanCarrier,
    gaussianPath_attained_circuit_maximum_and_permanent_locality] with L hL hent hpeak
  let n := L*2
  let d := 2^n-1
  let r := excursionGateBudget n
  let e₀ : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hpos : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  let m := nearestNeighborPathLocalParameterCount L
  have hμ : centredProductGaussian (Fin m) 1 ≪ (volume : Measure (Fin m → ℝ)) := by
    simpa [centredProductGaussian] using (productGaussian_absolutelyContinuous m one_ne_zero (fun _ => 0))
  have hfull := (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure (L := L) hL).2.2
  have htyp : ∀ᵐ p ∂(centredProductGaussian (Fin m) 1), p ∈ nearestNeighborPathLocalMaximalSet L :=
    ae_iff.mpr (hμ hfull)
  have hw := ae_static_integerClock_phaseLaw e₀ _ (RHTower.pairQubitProjectivePauliSeed_isHermitian L)
    (physical_seed_continuous L) (fun a _ p => physical_seed_scale L a p) b hb
  filter_upwards [htyp,hμ.ae_le hw,hpeak] with p hp hclock hpeak
  obtain ⟨e,he⟩ := hclock (RHTower.pairQubitProjectivePauliSeed_maximallyProjective hp)
  let H := RHTower.pairQubitProjectivePauliSeedSelfAdjoint L p
  let ω := RHTower.zeroProjectiveFrequency (fun i => H.2.isHermitian.eigenvalues (e.symm i))
  let Φ := finiteClockPhasePoint ω
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  obtain ⟨⟨m,hm,hactual⟩,hsep⟩ := hpeak
  refine ⟨fun k => ?_,⟨m,hm,hactual,prescribed_peak_positive e H b m
    ((Nat.zero_le r).trans_lt hm) hactual he⟩,prescribed_returns_positive e H b he,hsep⟩
  let A := dyadicCircuitCapture e V r k
  have hA : IsClosed A := dyadicCircuitCapture_closed e V r k
  have heq (N) : (integerClockPrefixLaw (fun j => (b j:ℝ)) N : Measure ℝ) (physicalDyadicCircuitHits H r k) =
      (integerClockPrefixLaw (fun j => Φ (b j)) N : Measure (Fin d → UnitAddCircle)) A := by
    rw [physical_dyadic_preimage e H r k]
    exact prefix_phase_preimage ω b N hA.measurableSet
  apply le_trans ((congrArg (fun f : ℕ → ENNReal => atTop.limsup f) (funext heq)).le)
  have hlim := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto he hA
  rw [finiteTorusHaarProbabilityMeasure_toMeasure_eq_volume] at hlim
  refine hlim.trans ?_
  have hvol := ENNReal.ofReal_le_ofReal (volume_dyadicCircuitCapture_le e V r k)
  have hcard : ((atMostQuarterCircuitNet n r).card:ℝ)/(2:ℝ)^d ≤ 1/(r+1:ℝ)^(2*r) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [one_mul,mul_comm]
    have hh := translated_excursion_square_card (n := n) (d := d) (by dsimp [n]; omega) hent
    exact_mod_cast hh.le
  apply le_trans ?_ (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hcard k))
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using hvol

/-- On one Gaussian draw the ordinary clock 1, 2, 4, … observes both actual
maximum complexity and arbitrarily close identity returns with positive lower
frequencies, while repeated shortcuts have exponentially small frequency. -/
theorem gaussianPath_fixed_dyadic_clock_peaks_and_returns :
    ∀ᶠ L : ℕ in atTop,
    ∀ᵐ p ∂(centredProductGaussian (Fin (nearestNeighborPathLocalParameterCount L)) 1),
      PrescribedClockCircuitStatistics (fun j => (2:ℤ)^j) L p :=
  gaussianPath_prescribed_integer_clock_circuit_runs _ (pow_right_strictMono₀ (by norm_num : 1 < (2:ℤ))).injective

#print axioms gaussianPath_prescribed_integer_clock_circuit_runs
#print axioms gaussianPath_fixed_dyadic_clock_peaks_and_returns
end
end GaloisForLFunctions.HTGeometry
