import GaloisForLFunctions.RHTower.NearestNeighborPolynomialCircuitSameDrawLaw
import GaloisForLFunctions.RHTower.NearestNeighborGaussianSameDrawCircuitExcursionFirstReturnLaw
import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedOscillationQuantitativeLaw

/-!
# Double-exponential complete-circuit excursion gaps for one static local draw

The polynomial-circuit Choi occupation cost decays exponentially in exact Hilbert dimension
`4 ^ L`.  Retaining the same Gaussian draw inside the laboratory-growth ball also gives a
deterministic projective speed bound.  These facts force arbitrarily late, consecutive returns to
the complete padded polynomial circuit dictionary whose intervening circuit-free excursion has
width at least `(3 / 2) ^ (4 ^ L)`.

This is a double-exponential-in-sites recurrence-excursion theorem for one ordinary
time-independent nearest-neighbour Hamiltonian.  It does not identify the first excursion after
time zero; that stronger initial-return statement still requires finite-window spectral/coarea
control.
-/

open Filter Topology MeasureTheory Set
open scoped Matrix.Norms.L2Operator
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

namespace RHTower

lemma projectiveChoiSpeed_nearestNeighborPathChoiEnergy_le_norm
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p) ≤
      2 * (nearestNeighborPathProjectiveDimension L : ℝ) *
          ‖nearestNeighborPathLocalHamiltonian L p‖ + 1 := by
  let H := nearestNeighborPathLocalHamiltonian L p
  let hH := nearestNeighborPathLocalHamiltonian_isHermitian L p
  have hpoint (i : Fin (nearestNeighborPathProjectiveDimension L + 1)) :
      |nearestNeighborPathChoiEnergy L p i| ≤ ‖H‖ := by
    dsimp [nearestNeighborPathChoiEnergy, H]
    simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem
      (hH.eigenvalues_mem_spectrum_real ((nearestNeighborPathConfigChoiEquiv L).symm i))
  have hgap (i : Fin (nearestNeighborPathProjectiveDimension L)) :
      |zeroProjectiveFrequency (nearestNeighborPathChoiEnergy L p) i| ≤ 2 * ‖H‖ := by
    unfold zeroProjectiveFrequency
    calc
      |nearestNeighborPathChoiEnergy L p 0 -
          nearestNeighborPathChoiEnergy L p i.succ| ≤
        |nearestNeighborPathChoiEnergy L p 0| +
          |nearestNeighborPathChoiEnergy L p i.succ| := abs_sub _ _
      _ ≤ ‖H‖ + ‖H‖ := add_le_add (hpoint 0) (hpoint i.succ)
      _ = 2 * ‖H‖ := by ring
  unfold projectiveChoiSpeed
  calc
    (∑ i : Fin (nearestNeighborPathProjectiveDimension L),
        |zeroProjectiveFrequency (nearestNeighborPathChoiEnergy L p) i|) + 1 ≤
      (∑ _i : Fin (nearestNeighborPathProjectiveDimension L), 2 * ‖H‖) + 1 := by
        gcongr with i
        exact hgap i
    _ = 2 * (nearestNeighborPathProjectiveDimension L : ℝ) * ‖H‖ + 1 := by
      simp
      ring

lemma norm_nearestNeighborPathLocalHamiltonian_le_length_add_two
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
      (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))) :
    ‖nearestNeighborPathLocalHamiltonian L p‖ ≤ (L : ℝ) + 2 := by
  letI : NormedRing
      (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
    Matrix.instL2OpNormedRing
  let M := nearestNeighborPathLocalGeneratorMass L
  have hM : 0 ≤ M := by
    dsimp [M, nearestNeighborPathLocalGeneratorMass]
    exact Finset.sum_nonneg fun i _ => norm_nonneg _
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have hdev := norm_nearestNeighborPathLocalHamiltonian_sub_center_le L p hp
  have hratio : (1 / ((L : ℝ) * (M + 1))) * M ≤ 1 := by
    have hM1 : 0 < M + 1 := by linarith
    calc
      (1 / ((L : ℝ) * (M + 1))) * M = (1 / (L : ℝ)) * (M / (M + 1)) := by
        field_simp
      _ ≤ 1 * 1 := by
        gcongr
        · exact (div_le_one hLR).2 (by exact_mod_cast hL)
        · exact (div_le_one hM1).2 (by linarith)
      _ = 1 := by ring
  have hseed := norm_inverseSquareChainHamiltonian_le_length_add_one hL
  calc
    ‖nearestNeighborPathLocalHamiltonian L p‖ ≤
        ‖nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L‖ +
          ‖inverseSquareChainHamiltonian L‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (nearestNeighborPathLocalHamiltonian L p - inverseSquareChainHamiltonian L)
        (inverseSquareChainHamiltonian L)
    _ ≤ (1 / ((L : ℝ) * (M + 1))) * M + ((L : ℝ) + 1) :=
      add_le_add hdev hseed
    _ ≤ 1 + ((L : ℝ) + 1) := by
      simpa [add_comm] using add_le_add_right hratio ((L : ℝ) + 1)
    _ = (L : ℝ) + 2 := by ring

lemma projectiveChoiSpeed_nearestNeighborPath_le_explicit
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
      (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1)))) :
    projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p) ≤
      2 * ((4 ^ L : ℕ) : ℝ) * ((L : ℝ) + 2) + 1 := by
  have hs := projectiveChoiSpeed_nearestNeighborPathChoiEnergy_le_norm L p
  have hn := norm_nearestNeighborPathLocalHamiltonian_le_length_add_two hL hp
  have hdimEq := nearestNeighborPathProjectiveDimension_add_one L
  have hdimNat : nearestNeighborPathProjectiveDimension L ≤ 4 ^ L := by omega
  have hdim : (nearestNeighborPathProjectiveDimension L : ℝ) ≤ ((4 ^ L : ℕ) : ℝ) := by
    exact_mod_cast hdimNat
  exact hs.trans (by gcongr)

lemma nat_le_four_pow (L : ℕ) : L ≤ 4 ^ L := by
  have htwo : L ≤ 2 ^ L := by
    induction L with
    | zero => simp
    | succ L ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ L := one_le_pow₀ (by norm_num)
        omega
  exact htwo.trans (Nat.pow_le_pow_left (by omega : 2 ≤ 4) L)

lemma explicitSpeed_le_seven_dimension_sq (L : ℕ) :
    2 * ((4 ^ L : ℕ) : ℝ) * ((L : ℝ) + 2) + 1 ≤
      7 * (((4 ^ L : ℕ) : ℝ) ^ (2 : ℕ)) := by
  let D : ℕ := 4 ^ L
  have hD : 1 ≤ D := one_le_pow₀ (by norm_num)
  have hLD : L ≤ D := by simpa [D] using nat_le_four_pow L
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hLDR : (L : ℝ) ≤ D := by exact_mod_cast hLD
  dsimp [D] at hDR hLDR ⊢
  nlinarith [sq_nonneg (((4 ^ L : ℕ) : ℝ) - 1)]

noncomputable def polynomialCircuitExponentialGapMajor (L : ℕ) : ℝ :=
  70 * (((4 ^ L : ℕ) : ℝ) ^ (3 : ℕ)) * (3 / 5 : ℝ) ^ (4 ^ L) +
    10 * ((4 ^ L : ℕ) : ℝ) * (2 / 5 : ℝ) ^ (4 ^ L)

theorem tendsto_polynomialCircuitExponentialGapMajor_atTop :
    Tendsto polynomialCircuitExponentialGapMajor atTop (nhds 0) := by
  have h3base : Tendsto
      (fun D : ℕ => 70 * ((D : ℝ) ^ (3 : ℕ) * (3 / 5 : ℝ) ^ D)) atTop (nhds 0) :=
    by
      simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 3
        (by norm_num : (0 : ℝ) ≤ 3 / 5) (by norm_num : (3 / 5 : ℝ) < 1)).const_mul 70
  have h1base : Tendsto
      (fun D : ℕ => 10 * ((D : ℝ) ^ (1 : ℕ) * (2 / 5 : ℝ) ^ D)) atTop (nhds 0) :=
    by
      simpa using (tendsto_pow_const_mul_const_pow_of_lt_one 1
        (by norm_num : (0 : ℝ) ≤ 2 / 5) (by norm_num : (2 / 5 : ℝ) < 1)).const_mul 10
  have hD : Tendsto (fun L : ℕ => 4 ^ L) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsum := (h3base.comp hD).add (h1base.comp hD)
  change Tendsto
    (fun L : ℕ =>
      70 * (((4 ^ L : ℕ) : ℝ) ^ (3 : ℕ)) * (3 / 5 : ℝ) ^ (4 ^ L) +
        10 * ((4 ^ L : ℕ) : ℝ) * (2 / 5 : ℝ) ^ (4 ^ L))
    atTop (nhds 0)
  simpa [pow_one, mul_assoc] using hsum

lemma polynomialCircuitEntropy_mul_speedGap_le_major (g k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      polynomialCircuitChoiEntropyCost g k L *
          ((2 * ((4 ^ L : ℕ) : ℝ) * ((L : ℝ) + 2) + 1) *
              (3 / 2 : ℝ) ^ (4 ^ L) + 1 / 200) ≤
        polynomialCircuitExponentialGapMajor L := by
  filter_upwards [eventually_polynomialCircuitChoiEntropyCost_le_major g k] with L hcost
  let D : ℕ := 4 ^ L
  have hcost0 : 0 ≤ polynomialCircuitChoiEntropyCost g k L := by
    unfold polynomialCircuitChoiEntropyCost
    positivity
  have hW : 0 ≤ (3 / 2 : ℝ) ^ D := by positivity
  have hspeed := explicitSpeed_le_seven_dimension_sq L
  have hfactor :
      (2 * (D : ℝ) * ((L : ℝ) + 2) + 1) * (3 / 2 : ℝ) ^ D + 1 / 200 ≤
        7 * (D : ℝ) ^ (2 : ℕ) * (3 / 2 : ℝ) ^ D + 1 := by
    gcongr
    norm_num
  calc
    polynomialCircuitChoiEntropyCost g k L *
        ((2 * (D : ℝ) * ((L : ℝ) + 2) + 1) * (3 / 2 : ℝ) ^ D + 1 / 200) ≤
      (10 * (D : ℝ) * (2 / 5 : ℝ) ^ D) *
        (7 * (D : ℝ) ^ (2 : ℕ) * (3 / 2 : ℝ) ^ D + 1) := by
          calc
            polynomialCircuitChoiEntropyCost g k L *
                ((2 * (D : ℝ) * ((L : ℝ) + 2) + 1) * (3 / 2 : ℝ) ^ D + 1 / 200) ≤
              (10 * (D : ℝ) * (2 / 5 : ℝ) ^ D) *
                ((2 * (D : ℝ) * ((L : ℝ) + 2) + 1) * (3 / 2 : ℝ) ^ D + 1 / 200) :=
              mul_le_mul_of_nonneg_right hcost (by positivity)
            _ ≤ (10 * (D : ℝ) * (2 / 5 : ℝ) ^ D) *
                (7 * (D : ℝ) ^ (2 : ℕ) * (3 / 2 : ℝ) ^ D + 1) :=
              mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = 70 * (D : ℝ) ^ (3 : ℕ) *
          ((2 / 5 : ℝ) ^ D * (3 / 2 : ℝ) ^ D) +
        10 * (D : ℝ) * (2 / 5 : ℝ) ^ D := by ring
    _ = 70 * (D : ℝ) ^ (3 : ℕ) * (3 / 5 : ℝ) ^ D +
        10 * (D : ℝ) * (2 / 5 : ℝ) ^ D := by
      rw [← mul_pow]
      norm_num
    _ = polynomialCircuitExponentialGapMajor L := rfl

theorem eventually_polynomialCircuitEntropy_speedGap_lt
    (g k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      polynomialCircuitChoiEntropyCost g k L *
          ((2 * ((4 ^ L : ℕ) : ℝ) * ((L : ℝ) + 2) + 1) *
              (3 / 2 : ℝ) ^ (4 ^ L) + 1 / 200) < 1 / 200 := by
  filter_upwards [polynomialCircuitEntropy_mul_speedGap_le_major g k,
    tendsto_polynomialCircuitExponentialGapMajor_atTop.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 200)] with L hle hlt
  exact hle.trans_lt hlt

def nearestNeighborPathGaussianControlledGrowthEvent
    (L : ℕ) (T ε ρ : ℝ) :
    Set (Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :=
  nearestNeighborPathGaussianGrowthMaximalEvent L T ε ∩
    Metric.closedBall (inverseSquarePathLocalCenter L) ρ

theorem measure_nearestNeighborPathGaussianControlledGrowthEvent_pos
    {L : ℕ} (hL : 0 < L) {T ε ρ : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hρ : 0 < ρ)
    (hscale : T * (ρ * nearestNeighborPathLocalGeneratorMass L) ≤ ε) :
    0 < (centredProductGaussian
      (Fin (nearestNeighborPathLocalParameterCount L)) 1)
      (nearestNeighborPathGaussianControlledGrowthEvent L T ε ρ) := by
  let μ := centredProductGaussian
    (Fin (nearestNeighborPathLocalParameterCount L)) 1
  let B := Metric.ball (inverseSquarePathLocalCenter L) ρ
  have hvolB : 0 < (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) B :=
    Metric.measure_ball_pos volume _ hρ
  have hvolAC : (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) ≪ μ := by
    exact volume_absolutelyContinuous_centredProductGaussian _ one_ne_zero
  have hμB : μ B ≠ 0 := by
    intro hzero
    exact hvolB.ne' (hvolAC hzero)
  have hμAC : μ ≪ (volume : Measure
      (Fin (nearestNeighborPathLocalParameterCount L) → ℝ)) := by
    simpa [μ, centredProductGaussian] using
      (productGaussian_absolutelyContinuous
        (nearestNeighborPathLocalParameterCount L) one_ne_zero
        (fun _ => 0))
  have hbadVol :=
    (nearestNeighborPathLocalMaximalSet_dense_residual_fullMeasure hL).2.2
  have hbadμ : μ (nearestNeighborPathLocalMaximalSet L)ᶜ = 0 := hμAC hbadVol
  have hinter : μ (B ∩ nearestNeighborPathLocalMaximalSet L) = μ B := by
    rw [show B ∩ nearestNeighborPathLocalMaximalSet L =
      B \ (nearestNeighborPathLocalMaximalSet L)ᶜ by ext p; simp]
    exact measure_sdiff_null hbadμ
  have hsubset : B ∩ nearestNeighborPathLocalMaximalSet L ⊆
      nearestNeighborPathGaussianControlledGrowthEvent L T ε ρ := by
    intro p hp
    have hpclosed : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L) ρ :=
      Metric.ball_subset_closedBall hp.1
    have hnorm := norm_nearestNeighborPathLocalHamiltonian_sub_center_le
      L p hpclosed
    have htube : T * ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤ ε :=
      (mul_le_mul_of_nonneg_left hnorm hT).trans hscale
    refine ⟨⟨hp.2, ?_⟩, hpclosed⟩
    intro t htMin htLab htT
    exact perturbed_inverseSquareChain_uniform_laboratory_growth
      (nearestNeighborPathLocalHamiltonian_isSelfAdjoint L p)
      hε hεmax htube t htMin htLab htT
  have hle : μ (B ∩ nearestNeighborPathLocalMaximalSet L) ≤
      μ (nearestNeighborPathGaussianControlledGrowthEvent L T ε ρ) :=
    measure_mono hsubset
  rw [hinter] at hle
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hμB) hle

theorem eventually_exists_nearestNeighborPath_polynomial_sameDraw_exponentialCircuitExcursion
    (gate : Type*) [Fintype gate] (k : ℕ) :
    ∀ᶠ L : ℕ in atTop,
      ∀ (target : PaddedCircuitWord gate (L ^ k) →
          EuclideanSpace ℂ
            (Fin (nearestNeighborPathProjectiveDimension L + 1) ×
              Fin (nearestNeighborPathProjectiveDimension L + 1))),
        (∀ w, ‖target w‖ = 1) →
        ∀ identityWord : PaddedCircuitWord gate (L ^ k),
          target identityWord =
            fullUniformPhaseChoiVector (nearestNeighborPathProjectiveDimension L + 1)
              (zeroAnchoredPhase (nearestNeighborPathProjectiveDimension L)
                (0 : Fin (nearestNeighborPathProjectiveDimension L) → UnitAddCircle)) →
          ∃ p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ,
            p ∈ nearestNeighborPathGaussianGrowthMaximalEvent L
              ((1 / 10000 : ℝ) * L) (1 / 10000 : ℝ) ∧
            p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
              (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))) ∧
            NearestNeighborPathExplicitCircuitExcursionFirstReturnGap
              L (L ^ k) p target (1 / 200 : ℝ)
                ((3 / 2 : ℝ) ^ (4 ^ L)) ∧
            ((⌊((1 / 10000 : ℝ) * L) /
                (256 * Real.pi * (1 / 10000 : ℝ))⌋₊ : ℕ) : ℕ∞) ≤
              operatorTwoGateComplexityTo L (1 / 10000 : ℝ)
                (unitaryEvolution (nearestNeighborPathLocalHamiltonian L p)
                  ((1 / 10000 : ℝ) * L)) := by
  filter_upwards [eventually_polynomialCircuitEntropy_speedGap_lt
      (Fintype.card gate) k,
    Filter.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (2048 * Real.pi)] with
      L hentropySpeed hL hLlarge target htarget identityWord hidentity
  have hLpos : 0 < L := by omega
  let rho : ℝ := 1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))
  have hrhoPos : 0 < rho := by
    dsimp [rho]
    letI : NormedRing
        (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
      Matrix.instL2OpNormedRing
    have hmass : 0 ≤ nearestNeighborPathLocalGeneratorMass L := by
      unfold nearestNeighborPathLocalGeneratorMass
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
    positivity
  have hrhoBudget :
      (1 / 10000 : ℝ) * L *
          (rho * nearestNeighborPathLocalGeneratorMass L) ≤ 1 / 10000 := by
    dsimp [rho]
    letI : NormedRing
        (Matrix (Config (PairQubit L)) (Config (PairQubit L)) ℂ) :=
      Matrix.instL2OpNormedRing
    let M := nearestNeighborPathLocalGeneratorMass L
    have hM : 0 ≤ M := by
      dsimp [M, nearestNeighborPathLocalGeneratorMass]
      exact Finset.sum_nonneg fun i _ => norm_nonneg _
    have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
    have hM1 : 0 < M + 1 := by linarith
    have hratio : M / (M + 1) ≤ 1 := (div_le_one hM1).2 (by linarith)
    calc
      (1 / 10000 : ℝ) * L * ((1 / ((L : ℝ) * (M + 1))) * M) =
          (1 / 10000 : ℝ) * (M / (M + 1)) := by field_simp
      _ ≤ (1 / 10000 : ℝ) * 1 := by gcongr
      _ = 1 / 10000 := by ring
  have heventPos := measure_nearestNeighborPathGaussianControlledGrowthEvent_pos
    hLpos
    (T := (1 / 10000 : ℝ) * L)
    (ε := (1 / 10000 : ℝ))
    (ρ := rho)
    (by positivity) (by norm_num) (by norm_num)
    hrhoPos hrhoBudget
  obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero (ne_of_gt heventPos)
  have hgrowth := hp.1
  have hpball : p ∈ Metric.closedBall (inverseSquarePathLocalCenter L)
      (1 / ((L : ℝ) * (nearestNeighborPathLocalGeneratorMass L + 1))) := by
    simpa [rho] using hp.2
  let speed := projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)
  let speedBound : ℝ :=
    2 * ((4 ^ L : ℕ) : ℝ) * ((L : ℝ) + 2) + 1
  let W : ℝ := (3 / 2 : ℝ) ^ (4 ^ L)
  let b : ℝ := polynomialCircuitChoiEntropyCost (Fintype.card gate) k L
  have hspeedPos : 0 < speed := projectiveChoiSpeed_pos _
  have hspeed : speed ≤ speedBound := by
    exact projectiveChoiSpeed_nearestNeighborPath_le_explicit hL hpball
  have hW : 0 ≤ W := by positivity
  have hb0 : 0 ≤ b := by
    dsimp [b]
    unfold polynomialCircuitChoiEntropyCost
    positivity
  have hactual : b * (speed * W + 1 / 200) < 1 / 200 := by
    calc
      b * (speed * W + 1 / 200) ≤
          b * (speedBound * W + 1 / 200) := by
        gcongr
      _ < 1 / 200 := by
        simpa [b, speedBound, W] using hentropySpeed
  have hdenPos : 0 < W + (1 / 200 : ℝ) / speed := by positivity
  have hpackAbstract :
      b < ((1 / 200 : ℝ) / speed) /
        (W + (1 / 200 : ℝ) / speed) := by
    rw [lt_div_iff₀ hdenPos]
    calc
      b * (W + (1 / 200 : ℝ) / speed) =
          (b * (speed * W + 1 / 200)) / speed := by
        field_simp
      _ < (1 / 200 : ℝ) / speed :=
        (div_lt_div_iff_of_pos_right hspeedPos).2 hactual
  have hpack :
      (Fintype.card gate : ℝ) ^ (L ^ k + 1) *
          ((((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) *
            Real.exp
              (((nearestNeighborPathProjectiveDimension L + 1 : ℕ) : ℝ) / 2) *
            Real.sqrt (Real.pi * (2 * (Real.sqrt 2 * (1 / 100 : ℝ)) ^ (2 : ℕ)) / 2) ^
              ((nearestNeighborPathProjectiveDimension L + 1 : ℕ) - 1))) <
        (((1 / 100 : ℝ) - 1 / 200) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)) /
          ((3 / 2 : ℝ) ^ (4 ^ L) + ((1 / 100 : ℝ) - 1 / 200) /
            projectiveChoiSpeed (nearestNeighborPathChoiEnergy L p)) := by
    rw [nearestNeighborPathProjectiveDimension_add_one]
    change polynomialCircuitChoiEntropyCost (Fintype.card gate) k L <
      (((1 / 100 : ℝ) - 1 / 200) / speed) /
        (W + ((1 / 100 : ℝ) - 1 / 200) / speed)
    have hdiff : (1 / 100 : ℝ) - 1 / 200 = 1 / 200 := by norm_num
    rw [hdiff]
    simpa only [b] using hpackAbstract
  have hgapLaw := nearestNeighborPath_sameDraw_growth_explicitConsecutiveCircuitFirstReturnGap
    hgrowth (L ^ k) target htarget identityWord hidentity
    (epsn := (1 / 200 : ℝ)) (epsw := (1 / 100 : ℝ))
    (W := (3 / 2 : ℝ) ^ (4 ^ L))
    (by norm_num) (by norm_num) (by positivity) hpack
  have hend := hgrowth.2 ((1 / 10000 : ℝ) * L)
    (by nlinarith : 2048 * Real.pi * (1 / 10000 : ℝ) ≤ (1 / 10000 : ℝ) * L)
    le_rfl le_rfl
  exact ⟨p, hgrowth, hpball, hgapLaw.2, hend⟩

end RHTower
