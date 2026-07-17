import GaloisForLFunctions.HTGeometry.CircularBetaEnsembleNormalizerBoundary

/-!
# Gaussian beta-ensemble normalization boundary

Dumitriu--Edelman equation (2) gives the Gamma part of the beta-Hermite/Gaussian-ensemble density
normalizer as

`Gamma(1+z)^K / product_{j=1}^K Gamma(1+j*z)`,

where `z=beta/2`.  Its reciprocal partition normalizer is a finite multiscale Gamma family.  The
largest scale has the refined center `1/K`, which cannot occur at any smaller positive integer
scale.  This exposed orbit proves the exact DA/HT boundary: the normalizer is DA for `K=0,1` and HT
for every interacting sector `K>1`.

The Gaussian and circular beta normalizers share their largest-scale factor, but their quotient is
the complete lower-scale Gamma tower.  Unlike the circular/Dirichlet quotient, it remains HT for
`K>1`.  Thus changing the ensemble changes the observable's orbit content rather than merely its
rational gauge.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance gaussianBetaDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance gaussianBetaDifferential : Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance gaussianBetaRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance gaussianBetaRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

local instance gaussianBetaDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance gaussianBetaCharZero : CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The `K` numerator scales followed by one scale-one denominator slot. -/
def gaussianBetaEnsembleScale (K : ℕ) (i : Fin (K + 1)) : ℕ :=
  if i.val < K then i.val + 1 else 1

/-- Every Gamma factor in the beta-Hermite normalizer has unit affine shift. -/
def gaussianBetaEnsembleShift (K : ℕ) (_ : Fin (K + 1)) : ℂ := 1

/-- Unit charge on every numerator scale and a selectable charge on the final scale-one slot. -/
def gaussianBetaEnsembleCharge (K : ℕ) (r : ℤ) (i : Fin (K + 1)) : ℤ :=
  if i.val < K then 1 else r

/-- Reciprocal of the Gamma-dependent density prefactor in Dumitriu--Edelman equation (2), with
`z=beta/2`; frequency-independent powers of `2*pi` are omitted. -/
def gaussianBetaEnsemblePartitionNormalizerMero (K : ℕ) : meroField Set.univ :=
  (∏ i : Fin K, gammaNatScaleMero (i.val + 1) 1) /
    gammaShiftMero 1 ^ K

/-- The Gamma-dependent beta-Hermite probability-density prefactor. -/
def gaussianBetaEnsembleDensityGammaNormalizerMero (K : ℕ) :
    meroField Set.univ :=
  (gaussianBetaEnsemblePartitionNormalizerMero K)⁻¹

/-- Signed-family presentation.  The extra charge parameter will also expose the lower-scale tower
by setting the last charge to zero. -/
def gaussianBetaEnsembleFamilyMero (K : ℕ) (r : ℤ) : meroField Set.univ :=
  gammaNatScaleFamilyMero
    (gaussianBetaEnsembleScale K)
    (gaussianBetaEnsembleShift K)
    (gaussianBetaEnsembleCharge K r)

/-- The signed-family presentation is exactly the primary-source Gamma partition normalizer when
the final scale-one charge is `-K`. -/
theorem gaussianBetaEnsembleFamilyMero_eq_partitionNormalizer (K : ℕ) :
    gaussianBetaEnsembleFamilyMero K (-(K : ℤ)) =
      gaussianBetaEnsemblePartitionNormalizerMero K := by
  rw [gaussianBetaEnsembleFamilyMero, gammaNatScaleFamilyMero,
    Fin.prod_univ_castSucc, gaussianBetaEnsemblePartitionNormalizerMero]
  simp [gaussianBetaEnsembleScale, gaussianBetaEnsembleShift,
    gaussianBetaEnsembleCharge, gammaNatScaleMero_one,
    zpow_neg, div_eq_mul_inv]

/-- The distinguished largest-scale numerator index for an ensemble of size `N+2`. -/
def gaussianBetaTopFamilyIndex (N : ℕ) : Fin ((N + 2) + 1) :=
  ⟨N + 1, by omega⟩

/-- The refined center `1/(N+2)` in the largest-scale numerator factor. -/
def gaussianBetaTopRefinedSlot (N : ℕ) :
    Σ i, Fin (gaussianBetaEnsembleScale (N + 2) i) :=
  ⟨gaussianBetaTopFamilyIndex N, ⟨0, by
    simp [gaussianBetaTopFamilyIndex, gaussianBetaEnsembleScale]⟩⟩

theorem gaussianBetaEnsembleScale_pos (K : ℕ) (i : Fin (K + 1)) :
    0 < gaussianBetaEnsembleScale K i := by
  rw [gaussianBetaEnsembleScale]
  split_ifs <;> omega

theorem gaussianBetaEnsembleScale_le
    {K : ℕ} (hK : 0 < K) (i : Fin (K + 1)) :
    gaussianBetaEnsembleScale K i ≤ K := by
  rw [gaussianBetaEnsembleScale]
  split_ifs <;> omega

/-- A nonzero positive fraction with denominator at most `K` cannot differ from `1/K` by an
integer when equality of denominators is accompanied by a nonzero numerator offset. -/
theorem refinedPositiveFraction_ne_integer_of_maximalDenominator
    {K j k : ℕ} (hK : 0 < K) (hj : 0 < j) (hjK : j ≤ K)
    (hk : k < j) (hstrict : j < K ∨ 0 < k) (q : ℤ) :
    (((k + 1 : ℕ) : ℂ) / (j : ℂ) - (1 : ℂ) / (K : ℂ)) ≠ (q : ℂ) := by
  intro h
  have hj0 : (j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hj.ne'
  have hK0 : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  have hEqC : (K : ℂ) * ((k + 1 : ℕ) : ℂ) - (j : ℂ) =
      (q : ℂ) * (j : ℂ) * (K : ℂ) := by
    field_simp [hj0, hK0] at h
    linear_combination h
  have hEqZ : (K : ℤ) * ((k + 1 : ℕ) : ℤ) - (j : ℤ) =
      q * (j : ℤ) * (K : ℤ) := by
    exact_mod_cast hEqC
  have hlowNat : j < K * (k + 1) := by
    rcases hstrict with hjlt | hkpos
    · calc
        j < K := hjlt
        _ ≤ K * (k + 1) := by
          have : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
          simpa using Nat.mul_le_mul_left K this
    · have hk2 : 2 ≤ k + 1 := by omega
      calc
        j ≤ K := hjK
        _ < K * (k + 1) := by
          have : K < K * 2 := by omega
          exact lt_of_lt_of_le this (Nat.mul_le_mul_left K hk2)
  have huppNat : K * (k + 1) ≤ K * j :=
    Nat.mul_le_mul_left K (by omega)
  have hPpos : (0 : ℤ) < (j : ℤ) * (K : ℤ) := by positivity
  have hdiffpos : (0 : ℤ) <
      (K : ℤ) * ((k + 1 : ℕ) : ℤ) - (j : ℤ) := by
    have hlowZ : (j : ℤ) <
        (K : ℤ) * ((k + 1 : ℕ) : ℤ) := by
      exact_mod_cast hlowNat
    omega
  have hdiff_lt : (K : ℤ) * ((k + 1 : ℕ) : ℤ) - (j : ℤ) <
      (j : ℤ) * (K : ℤ) := by
    have hjZ : (0 : ℤ) < j := by exact_mod_cast hj
    have huppZ : (K : ℤ) * ((k + 1 : ℕ) : ℤ) ≤ (K : ℤ) * (j : ℤ) := by
      exact_mod_cast huppNat
    nlinarith
  have hqPpos : 0 < q * ((j : ℤ) * (K : ℤ)) := by
    rw [hEqZ] at hdiffpos
    simpa [mul_assoc] using hdiffpos
  have hqpos : 0 < q := by
    rcases (mul_pos_iff.mp hqPpos) with hq | hq
    · exact hq.1
    · exact (not_lt_of_ge hPpos.le hq.2).elim
  have hP_le : (j : ℤ) * (K : ℤ) ≤ q * ((j : ℤ) * (K : ℤ)) := by
    have hqone : (1 : ℤ) ≤ q := by omega
    simpa using mul_le_mul_of_nonneg_right hqone hPpos.le
  rw [hEqZ] at hdiff_lt
  have : q * ((j : ℤ) * (K : ℤ)) < (j : ℤ) * (K : ℤ) := by
    simpa [mul_assoc] using hdiff_lt
  exact (not_lt_of_ge hP_le) this

/-- **Largest-scale exposed-orbit theorem.**  For every ensemble size `N+2`, the full signed
multiscale family is HT for every charge on the extra scale-one slot.  The proof is independent of
all possible collisions away from the largest-scale center `1/(N+2)`. -/
theorem hypertranscendentalOver_gaussianBetaEnsembleFamilyMero
    (N : ℕ) (r : ℤ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gaussianBetaEnsembleFamilyMero (N + 2) r) := by
  apply hypertranscendentalOver_gammaNatScaleFamilyMero_of_exposedRefinedOrbit
    (gaussianBetaEnsembleScale (N + 2))
    (gaussianBetaEnsembleShift (N + 2))
    (gaussianBetaEnsembleCharge (N + 2) r)
    (gaussianBetaEnsembleScale_pos (N + 2))
    (gaussianBetaTopRefinedSlot N)
  · simp [gaussianBetaTopRefinedSlot, gaussianBetaTopFamilyIndex,
      gaussianBetaEnsembleCharge]
  · rintro ⟨i, k⟩ hne q
    have hscaleLe : gaussianBetaEnsembleScale (N + 2) i ≤ N + 2 :=
      gaussianBetaEnsembleScale_le (by omega) i
    have hstrict : gaussianBetaEnsembleScale (N + 2) i < N + 2 ∨ 0 < k.val := by
      by_contra h
      push Not at h
      have hscaleEq : gaussianBetaEnsembleScale (N + 2) i = N + 2 :=
        le_antisymm hscaleLe h.1
      have hi : i = gaussianBetaTopFamilyIndex N := by
        apply Fin.ext
        rw [gaussianBetaEnsembleScale] at hscaleEq
        split at hscaleEq <;> simp [gaussianBetaTopFamilyIndex] <;> omega
      have hk : k.val = 0 := by omega
      apply hne
      subst i
      have hkEq : k =
          (⟨0, by
            simp [gaussianBetaTopFamilyIndex,
              gaussianBetaEnsembleScale]⟩ :
            Fin (gaussianBetaEnsembleScale (N + 2)
              (gaussianBetaTopFamilyIndex N))) := Fin.ext hk
      subst k
      rfl
    have hfrac := refinedPositiveFraction_ne_integer_of_maximalDenominator
      (K := N + 2)
      (j := gaussianBetaEnsembleScale (N + 2) i)
      (k := k.val) (by omega)
      (gaussianBetaEnsembleScale_pos (N + 2) i)
      hscaleLe k.isLt hstrict q
    rw [show gammaNatScaleRefinedSlotShift
        (gaussianBetaEnsembleScale (N + 2))
        (gaussianBetaEnsembleShift (N + 2))
        (gaussianBetaTopRefinedSlot N) =
          (1 : ℂ) / ((N + 2 : ℕ) : ℂ) by
      simp [gammaNatScaleRefinedSlotShift, gaussianBetaEnsembleShift,
        gaussianBetaTopRefinedSlot, gaussianBetaTopFamilyIndex,
        gaussianBetaEnsembleScale]
      exact_mod_cast (show N + 1 + 1 = N + 2 by omega)]
    simp only [gammaNatScaleRefinedSlotShift, gaussianBetaEnsembleShift]
    have hkcast : (((k.val + 1 : ℕ) : ℂ)) = 1 + (k.val : ℂ) := by
      push_cast
      ring
    rw [hkcast] at hfrac
    exact hfrac

/-- Every genuinely interacting Gaussian beta ensemble has an HT partition normalizer in the
complexified coupling clock. -/
theorem hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero
    (N : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gaussianBetaEnsemblePartitionNormalizerMero (N + 2)) := by
  rw [← gaussianBetaEnsembleFamilyMero_eq_partitionNormalizer]
  exact hypertranscendentalOver_gaussianBetaEnsembleFamilyMero
    N (-((N + 2 : ℕ) : ℤ))

/-- The complete positive integer-scale Gamma tower below a selected maximal scale. -/
def gaussianBetaLowerScaleTowerMero (K : ℕ) : meroField Set.univ :=
  ∏ i : Fin K, gammaNatScaleMero (i.val + 1) 1

/-- Zeroing the extra denominator charge leaves exactly the positive lower-scale tower. -/
theorem gaussianBetaEnsembleFamilyMero_zero_eq_lowerScaleTower (K : ℕ) :
    gaussianBetaEnsembleFamilyMero K 0 =
      gaussianBetaLowerScaleTowerMero K := by
  rw [gaussianBetaEnsembleFamilyMero, gammaNatScaleFamilyMero,
    Fin.prod_univ_castSucc, gaussianBetaLowerScaleTowerMero]
  simp [gaussianBetaEnsembleScale, gaussianBetaEnsembleShift,
    gaussianBetaEnsembleCharge]

/-- Every nonempty consecutive positive integer-scale Gamma tower is HT. -/
theorem hypertranscendentalOver_gaussianBetaLowerScaleTowerMero (N : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gaussianBetaLowerScaleTowerMero (N + 1)) := by
  cases N with
  | zero =>
      simpa [gaussianBetaLowerScaleTowerMero, gammaNatScaleMero_one] using
        (hypertranscendentalOver_gammaNatScaleMero
          (n := 1) (show 0 < 1 by norm_num) (1 : ℂ))
  | succ N =>
      rw [← gaussianBetaEnsembleFamilyMero_zero_eq_lowerScaleTower]
      exact hypertranscendentalOver_gaussianBetaEnsembleFamilyMero N 0

/-- **Gaussian/circular value relation.**  The Gaussian normalizer equals the circular normalizer
at the same eigenvalue count times every lower positive integer-scale Gamma factor. -/
theorem gaussianBetaEnsemblePartitionNormalizerMero_eq_lowerScale_mul_circular
    (N : ℕ) :
    gaussianBetaEnsemblePartitionNormalizerMero (N + 1) =
      gaussianBetaLowerScaleTowerMero N *
        circularBetaEnsemblePartitionNormalizerMero (N + 1) := by
  rw [gaussianBetaEnsemblePartitionNormalizerMero,
    gaussianBetaLowerScaleTowerMero,
    circularBetaEnsemblePartitionNormalizerMero,
    Fin.prod_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc]
  ring

/-- Dividing Gaussian by circular normalization leaves the lower-scale Gamma tower exactly. -/
theorem gaussianBetaEnsemble_div_circular_eq_lowerScaleTower
    (N : ℕ) :
    gaussianBetaEnsemblePartitionNormalizerMero (N + 1) /
        circularBetaEnsemblePartitionNormalizerMero (N + 1) =
      gaussianBetaLowerScaleTowerMero N := by
  rw [gaussianBetaEnsemblePartitionNormalizerMero_eq_lowerScale_mul_circular]
  field_simp [circularBetaEnsemblePartitionNormalizerMero_ne_zero
    (K := N + 1) (Nat.succ_pos N)]

/-- The Gaussian/circular quotient remains HT in every interacting sector: their difference is
not a DA gauge. -/
theorem hypertranscendentalOver_gaussianBetaEnsemble_div_circular (N : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
      (gaussianBetaEnsemblePartitionNormalizerMero (N + 2) /
        circularBetaEnsemblePartitionNormalizerMero (N + 2)) := by
  rw [gaussianBetaEnsemble_div_circular_eq_lowerScaleTower]
  exact hypertranscendentalOver_gaussianBetaLowerScaleTowerMero N

@[simp] theorem gaussianBetaEnsemblePartitionNormalizerMero_zero :
    gaussianBetaEnsemblePartitionNormalizerMero 0 = 1 := by
  simp [gaussianBetaEnsemblePartitionNormalizerMero]

@[simp] theorem gaussianBetaEnsemblePartitionNormalizerMero_one :
    gaussianBetaEnsemblePartitionNormalizerMero 1 = 1 := by
  simp [gaussianBetaEnsemblePartitionNormalizerMero,
    gammaNatScaleMero_one, gammaShiftMero_ne_zero]

/-- **Exact size boundary.**  The Gaussian beta partition normalizer is DA exactly in the empty
or one-eigenvalue sectors. -/
theorem differentialAlgebraicOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_le_one
    (K : ℕ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (gaussianBetaEnsemblePartitionNormalizerMero K) ↔
      K ≤ 1 := by
  constructor
  · intro hDA
    by_contra hK
    have hmany : 1 < K := by omega
    obtain ⟨N, rfl⟩ : ∃ N, K = N + 2 := by
      refine ⟨K - 2, ?_⟩
      omega
    exact (hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero N) hDA
  · intro hK
    have hcases : K = 0 ∨ K = 1 := by omega
    rcases hcases with rfl | rfl
    · rw [gaussianBetaEnsemblePartitionNormalizerMero_zero]
      simpa only [map_one] using
        (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
          DifferentialAlgebraicOver (RatFunc ℂ)
            (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))
    · rw [gaussianBetaEnsemblePartitionNormalizerMero_one]
      simpa only [map_one] using
        (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
          DifferentialAlgebraicOver (RatFunc ℂ)
            (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))

/-- Hypertranscendence is exactly the interacting `K>1` sector. -/
theorem hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_many
    (K : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
        (gaussianBetaEnsemblePartitionNormalizerMero K) ↔
      1 < K := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_le_one]
  omega

/-- The probability-density Gamma prefactor has the same exact boundary as its reciprocal
partition normalizer. -/
theorem hypertranscendentalOver_gaussianBetaEnsembleDensityGammaNormalizerMero_iff_many
    (K : ℕ) :
    HypertranscendentalOver (RatFunc ℂ)
        (gaussianBetaEnsembleDensityGammaNormalizerMero K) ↔
      1 < K := by
  rw [gaussianBetaEnsembleDensityGammaNormalizerMero,
    HTGeometry.hypertranscendentalOver_inv_iff,
    hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_many]

/-- **Positive source extraction for Gaussian random-matrix normalization circuits.** -/
theorem exists_hypertranscendental_atom_of_gaussianBetaEnsembleNormalizerCircuit
    {K : ℕ} (hK : 1 < K) {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (gaussianBetaEnsemblePartitionNormalizerMero K)) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    ((hypertranscendentalOver_gaussianBetaEnsemblePartitionNormalizerMero_iff_many K).2 hK)
    hcircuit

end

end GaloisForLFunctions
