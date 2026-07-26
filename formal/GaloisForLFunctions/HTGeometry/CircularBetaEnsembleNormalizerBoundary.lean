import GaloisForLFunctions.HTGeometry.SymmetricDirichletNormalizerBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Circular beta-ensemble normalization boundary

Dyson's circular beta ensemble has normalized Selberg integral

`Gamma(K*z+1) / Gamma(z+1)^K`,

where `K` is the number of eigenangles and `z = beta/2`.  Gamma recurrence identifies this
random-matrix partition normalizer exactly with the symmetric `K`-category Dirichlet normalizer

`Gamma(K*z) / Gamma(z)^K`

times the rational gauge `K*z / z^K`.  Consequently the two observables have the same exact
differential-algebraic/hypertranscendental boundary in their coupling/concentration clock:
they are DA only at `K = 1` and HT for every `K > 1`.

This is a value relation between random-matrix quantum statistics and AI/genomic Dirichlet
normalization.  It concerns the observable normalization as the coupling is read, not the temporal
evolution of either physical or learned system.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The Gamma part of the circular beta-ensemble Selberg integral, with `z = beta/2` and `K`
eigenangles. -/
def circularBetaEnsemblePartitionNormalizerMero (K : ℕ) : meroField Set.univ :=
  gammaNatScaleMero K 1 / gammaShiftMero 1 ^ K

/-- The Gamma-dependent probability-density prefactor in Jiang--Matsumoto equation (1.3),
omitting only the nonzero constant `(2*pi)^(-K)`. -/
def circularBetaEnsembleDensityGammaNormalizerMero (K : ℕ) : meroField Set.univ :=
  (circularBetaEnsemblePartitionNormalizerMero K)⁻¹

/-- The rational gauge relating the circular beta-ensemble and symmetric Dirichlet normalizers. -/
def circularBetaDirichletGaugeRat (K : ℕ) : RatFunc ℂ :=
  gammaNatScaleLinearFactorRat K 0 /
    gammaNatScaleLinearFactorRat 1 0 ^ K

/-- The cross-domain gauge is explicitly `K*X/X^K`. -/
theorem circularBetaDirichletGaugeRat_eq (K : ℕ) :
    circularBetaDirichletGaugeRat K =
      RatFunc.C (K : ℂ) * RatFunc.X / RatFunc.X ^ K := by
  simp [circularBetaDirichletGaugeRat, gammaNatScaleLinearFactorRat]

theorem circularBetaDirichletGaugeRat_ne_zero
    {K : ℕ} (hK : 0 < K) :
    circularBetaDirichletGaugeRat K ≠ 0 := by
  rw [circularBetaDirichletGaugeRat]
  exact div_ne_zero
    (gammaNatScaleLinearFactorRat_ne_zero hK 0)
    (pow_ne_zero K
      (gammaNatScaleLinearFactorRat_ne_zero (show 0 < 1 by norm_num) 0))

theorem circularBetaDirichletGaugeMero_ne_zero
    {K : ℕ} (hK : 0 < K) :
    algebraMap (RatFunc ℂ) (meroField Set.univ)
        (circularBetaDirichletGaugeRat K) ≠ 0 :=
  (map_ne_zero_iff _
    (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
      Set.univ_nonempty Set.infinite_univ).injective).mpr
    (circularBetaDirichletGaugeRat_ne_zero hK)

theorem differentialAlgebraicOver_circularBetaDirichletGaugeMero
    (K : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (algebraMap (RatFunc ℂ) (meroField Set.univ)
        (circularBetaDirichletGaugeRat K)) :=
  HTGeometry.differentialAlgebraicOver_algebraMap _

/-- **Random-matrix/Dirichlet value relation.**  The two exact Gamma normalizers differ by only
the rational observable `K*z/z^K`. -/
theorem circularBetaEnsemblePartitionNormalizerMero_eq_dirichlet
    {K : ℕ} (hK : 0 < K) :
    circularBetaEnsemblePartitionNormalizerMero K =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
          (circularBetaDirichletGaugeRat K) *
        symmetricDirichletNormalizerMero K := by
  have hnum := gammaNatScaleMero_add_one hK (0 : ℂ)
  have hden := gammaNatScaleMero_add_one
    (n := 1) (show 0 < 1 by norm_num) (0 : ℂ)
  simp only [zero_add] at hnum hden
  simp only [gammaNatScaleMero_one] at hden
  rw [circularBetaEnsemblePartitionNormalizerMero,
    symmetricDirichletNormalizerMero, hnum, hden,
    circularBetaDirichletGaugeRat, map_div₀, map_pow]
  ring

theorem circularBetaEnsemblePartitionNormalizerMero_ne_zero
    {K : ℕ} (hK : 0 < K) :
    circularBetaEnsemblePartitionNormalizerMero K ≠ 0 := by
  rw [circularBetaEnsemblePartitionNormalizerMero]
  exact div_ne_zero (gammaNatScaleMero_ne_zero hK 1)
    (pow_ne_zero K (gammaShiftMero_ne_zero 1))

/-- Partition normalization and density normalization are exact reciprocal observations. -/
theorem circularBetaEnsemblePartition_mul_densityGammaNormalizer
    {K : ℕ} (hK : 0 < K) :
    circularBetaEnsemblePartitionNormalizerMero K *
        circularBetaEnsembleDensityGammaNormalizerMero K = 1 := by
  rw [circularBetaEnsembleDensityGammaNormalizerMero,
    mul_inv_cancel₀ (circularBetaEnsemblePartitionNormalizerMero_ne_zero hK)]

private theorem symmetricDirichletNormalizerMero_ne_zero_of_pos
    {K : ℕ} (hK : 0 < K) :
    symmetricDirichletNormalizerMero K ≠ 0 := by
  rw [symmetricDirichletNormalizerMero]
  exact div_ne_zero (gammaNatScaleMero_ne_zero hK 0)
    (pow_ne_zero K (gammaShiftMero_ne_zero 0))

/-- Dividing the random-matrix partition normalizer by the AI/genomic normalizer removes every
Gamma factor and leaves exactly the rational gauge. -/
theorem circularBetaEnsemble_div_symmetricDirichlet_eq_gauge
    {K : ℕ} (hK : 0 < K) :
    circularBetaEnsemblePartitionNormalizerMero K /
        symmetricDirichletNormalizerMero K =
      algebraMap (RatFunc ℂ) (meroField Set.univ)
        (circularBetaDirichletGaugeRat K) := by
  rw [circularBetaEnsemblePartitionNormalizerMero_eq_dirichlet hK]
  field_simp [symmetricDirichletNormalizerMero_ne_zero_of_pos hK]

/-- The cross-domain quotient is differentially algebraic even though both factors are HT for
`K > 1`. -/
theorem differentialAlgebraicOver_circularBetaEnsemble_div_symmetricDirichlet
    {K : ℕ} (hK : 0 < K) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (circularBetaEnsemblePartitionNormalizerMero K /
        symmetricDirichletNormalizerMero K) := by
  rw [circularBetaEnsemble_div_symmetricDirichlet_eq_gauge hK]
  exact differentialAlgebraicOver_circularBetaDirichletGaugeMero K

/-- Every circular beta ensemble with more than one eigenangle has an HT partition normalizer in
the beta-coupling clock. -/
theorem hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero
    {K : ℕ} (hK : 1 < K) :
    HypertranscendentalOver (RatFunc ℂ)
      (circularBetaEnsemblePartitionNormalizerMero K) := by
  rw [circularBetaEnsemblePartitionNormalizerMero_eq_dirichlet (by omega), mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_circularBetaDirichletGaugeMero K)
    (circularBetaDirichletGaugeMero_ne_zero (by omega))).2
      (hypertranscendentalOver_symmetricDirichletNormalizerMero hK)

/-- A one-eigenangle circular ensemble has no pair interaction and partition normalizer one. -/
@[simp] theorem circularBetaEnsemblePartitionNormalizerMero_one :
    circularBetaEnsemblePartitionNormalizerMero 1 = 1 := by
  rw [circularBetaEnsemblePartitionNormalizerMero, gammaNatScaleMero_one]
  simpa using div_self (gammaShiftMero_ne_zero 1)

/-- **Exact eigenangle-count boundary.**  For positive `K`, the circular beta-ensemble partition
normalizer is DA exactly when there is only one eigenangle. -/
theorem differentialAlgebraicOver_circularBetaEnsemblePartitionNormalizerMero_iff_one
    {K : ℕ} (hK : 0 < K) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (circularBetaEnsemblePartitionNormalizerMero K) ↔
      K = 1 := by
  constructor
  · intro hDA
    by_contra hne
    have hmany : 1 < K := by omega
    exact (hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero hmany) hDA
  · intro hKone
    subst K
    rw [circularBetaEnsemblePartitionNormalizerMero_one]
    simpa only [map_one] using
      (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))

/-- Hypertranscendence is exactly the genuinely interacting `K > 1` sector. -/
theorem hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero_iff_many
    {K : ℕ} (hK : 0 < K) :
    HypertranscendentalOver (RatFunc ℂ)
        (circularBetaEnsemblePartitionNormalizerMero K) ↔
      1 < K := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_circularBetaEnsemblePartitionNormalizerMero_iff_one hK]
  omega

/-- The Gamma-dependent probability-density prefactor has the same exact interacting-sector
boundary as its reciprocal partition normalizer. -/
theorem hypertranscendentalOver_circularBetaEnsembleDensityGammaNormalizerMero_iff_many
    {K : ℕ} (hK : 0 < K) :
    HypertranscendentalOver (RatFunc ℂ)
        (circularBetaEnsembleDensityGammaNormalizerMero K) ↔
      1 < K := by
  rw [circularBetaEnsembleDensityGammaNormalizerMero,
    HTGeometry.hypertranscendentalOver_inv_iff,
    hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero_iff_many hK]

/-- **Positive source extraction for random-matrix partition circuits.**  Any scalar-aware finite
differential circuit realizing the exact `K > 1` normalizer must contain an HT non-scalar atom. -/
theorem exists_hypertranscendental_atom_of_circularBetaEnsembleNormalizerCircuit
    {K : ℕ} (hK : 1 < K) {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (circularBetaEnsemblePartitionNormalizerMero K)) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    (hypertranscendentalOver_circularBetaEnsemblePartitionNormalizerMero hK) hcircuit

end

end GaloisForLFunctions
