import GaloisForLFunctions.HTGeometry.LaguerreWishartNormalizerBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Jacobi--MANOVA normalization boundary

Dumitriu--Edelman equation (6), on the classical rectangular ray
`a1=n1*z`, `a2=n2*z`, gives the exact Gamma quotient between the Jacobi/MANOVA and
beta-Hermite/Gaussian reciprocal normalizers:

`J_{m,n1,n2}(z) / G_m(z) = product_{r=0}^{m-1}
  Gamma((n1-r)*z) Gamma((n2-r)*z) / Gamma((n1+n2-r)*z)`.

For `0<m<=n1,n2`, the denominator factor at the unique largest scale `n1+n2` has the refined
center `1/(n1+n2)`.  No smaller positive integer scale can contain that center modulo integer
translation.  It is therefore an exposed charge-minus-one orbit, proving that the complete
Jacobi/Gaussian quotient is hypertranscendental.  The observed clock is the Dyson coupling
`z=beta/2`; the theorem does not assert temporal evolution of a transport system.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- Three `m`-blocks of scales: the two numerator bands and the denominator band. -/
def jacobiMANOVAGammaScale (m n₁ n₂ : ℕ) (i : Fin (3 * m)) : ℕ :=
  if i.val < m then n₁ - i.val
  else if i.val < 2 * m then n₂ - (i.val - m)
  else n₁ + n₂ - (i.val - 2 * m)

/-- All classical Jacobi--MANOVA Gamma factors have zero affine shift on the coupling ray. -/
def jacobiMANOVAGammaShift (m _n₁ _n₂ : ℕ) (_ : Fin (3 * m)) : ℂ := 0

/-- Positive charges on the two numerator bands and negative charge on the sum-scale band. -/
def jacobiMANOVAGammaCharge (m : ℕ) (i : Fin (3 * m)) : ℤ :=
  if i.val < 2 * m then 1 else -1

/-- The exact Gamma-dependent Jacobi/MANOVA quotient by the Gaussian normalizer on the
classical rectangular coupling ray. -/
def jacobiMANOVAGammaQuotientMero (m n₁ n₂ : ℕ) : meroField Set.univ :=
  gammaNatScaleFamilyMero
    (jacobiMANOVAGammaScale m n₁ n₂)
    (jacobiMANOVAGammaShift m n₁ n₂)
    (jacobiMANOVAGammaCharge m)

/-- The reciprocal Gamma part of the classical Jacobi/MANOVA normalizer, with its elementary
nonzero exponential gauge omitted. -/
def jacobiMANOVAPartitionNormalizerMero (m n₁ n₂ : ℕ) : meroField Set.univ :=
  gaussianBetaEnsemblePartitionNormalizerMero m *
    jacobiMANOVAGammaQuotientMero m n₁ n₂

/-- The first slot of the sum-scale denominator band. -/
def jacobiMANOVATopFamilyIndex {m : ℕ} (hm : 0 < m) : Fin (3 * m) :=
  ⟨2 * m, by omega⟩

theorem jacobiMANOVAGammaScale_top
    {m n₁ n₂ : ℕ} (hm : 0 < m) :
    jacobiMANOVAGammaScale m n₁ n₂ (jacobiMANOVATopFamilyIndex hm) =
      n₁ + n₂ := by
  have hfirst : ¬ 2 * m < m := by omega
  simp [jacobiMANOVAGammaScale, jacobiMANOVATopFamilyIndex,
    hfirst]

theorem jacobiMANOVAGammaScale_pos
    {m n₁ n₂ : ℕ} (hm₁ : m ≤ n₁) (hm₂ : m ≤ n₂)
    (i : Fin (3 * m)) :
    0 < jacobiMANOVAGammaScale m n₁ n₂ i := by
  rw [jacobiMANOVAGammaScale]
  split_ifs <;> omega

theorem jacobiMANOVAGammaScale_le_sum
    (m n₁ n₂ : ℕ) (i : Fin (3 * m)) :
    jacobiMANOVAGammaScale m n₁ n₂ i ≤ n₁ + n₂ := by
  rw [jacobiMANOVAGammaScale]
  split_ifs <;> omega

/-- The sum scale occurs at exactly one family index. -/
theorem jacobiMANOVAGammaScale_eq_sum_iff
    {m n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (i : Fin (3 * m)) :
    jacobiMANOVAGammaScale m n₁ n₂ i = n₁ + n₂ ↔
      i.val = 2 * m := by
  rw [jacobiMANOVAGammaScale]
  split_ifs <;> omega

/-- The exposed refined center `1/(n1+n2)` in the unique largest-scale denominator factor. -/
def jacobiMANOVATopRefinedSlot
    {m n₁ n₂ : ℕ} (hm : 0 < m) (hK : 1 < n₁ + n₂) :
    Σ i, Fin (jacobiMANOVAGammaScale m n₁ n₂ i) :=
  ⟨jacobiMANOVATopFamilyIndex hm, ⟨1, by
    rw [jacobiMANOVAGammaScale_top hm]
    exact hK⟩⟩

private theorem zero_fraction_sub_unitFraction_ne_integer
    {K : ℕ} (hK : 1 < K) (q : ℤ) :
    (0 : ℂ) / (K : ℂ) - (1 : ℂ) / (K : ℂ) ≠ (q : ℂ) := by
  intro h
  have hKreal : (1 : ℝ) < K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := lt_trans (by norm_num) hKreal
  have hfracPos : (0 : ℝ) < 1 / (K : ℝ) := one_div_pos.mpr hKpos
  have hfracLt : (1 : ℝ) / (K : ℝ) < 1 :=
    (div_lt_one hKpos).2 hKreal
  have hinvPos : (0 : ℝ) < (K : ℝ)⁻¹ := by
    simpa [one_div] using hfracPos
  have hinvLt : (K : ℝ)⁻¹ < 1 := by
    simpa [one_div] using hfracLt
  have hreal := congrArg Complex.re h
  norm_num at hreal
  have hqNegReal : (q : ℝ) < 0 := by
    rw [← hreal]
    exact neg_neg_of_pos hinvPos
  have hqGtReal : (-1 : ℝ) < (q : ℝ) := by
    rw [← hreal]
    linarith
  have hqNeg : q < 0 := by exact_mod_cast hqNegReal
  have hqGt : (-1 : ℤ) < q := by exact_mod_cast hqGtReal
  omega

/-- **Unique-largest-scale theorem.**  The classical rectangular Jacobi/MANOVA Gamma quotient
is HT for every positive matrix size. -/
theorem hypertranscendentalOver_jacobiMANOVAGammaQuotientMero
    {m n₁ n₂ : ℕ} (hm : 0 < m) (hm₁ : m ≤ n₁) (hm₂ : m ≤ n₂) :
    HypertranscendentalOver (RatFunc ℂ)
      (jacobiMANOVAGammaQuotientMero m n₁ n₂) := by
  have hn₁ : 0 < n₁ := lt_of_lt_of_le hm hm₁
  have hn₂ : 0 < n₂ := lt_of_lt_of_le hm hm₂
  have hK : 1 < n₁ + n₂ := by omega
  apply hypertranscendentalOver_gammaNatScaleFamilyMero_of_exposedRefinedOrbit
    (jacobiMANOVAGammaScale m n₁ n₂)
    (jacobiMANOVAGammaShift m n₁ n₂)
    (jacobiMANOVAGammaCharge m)
    (jacobiMANOVAGammaScale_pos hm₁ hm₂)
    (jacobiMANOVATopRefinedSlot hm hK)
  · simp [jacobiMANOVATopRefinedSlot, jacobiMANOVATopFamilyIndex,
      jacobiMANOVAGammaCharge]
  · rintro ⟨i, k⟩ hne q
    have hjPos := jacobiMANOVAGammaScale_pos hm₁ hm₂ i
    have hjLe := jacobiMANOVAGammaScale_le_sum m n₁ n₂ i
    rw [show gammaNatScaleRefinedSlotShift
        (jacobiMANOVAGammaScale m n₁ n₂)
        (jacobiMANOVAGammaShift m n₁ n₂)
        (jacobiMANOVATopRefinedSlot hm hK) =
          (1 : ℂ) / ((n₁ + n₂ : ℕ) : ℂ) by
      simp only [gammaNatScaleRefinedSlotShift, jacobiMANOVAGammaShift,
        jacobiMANOVATopRefinedSlot, zero_add]
      rw [jacobiMANOVAGammaScale_top hm]
      norm_num]
    simp only [gammaNatScaleRefinedSlotShift, jacobiMANOVAGammaShift,
      zero_add]
    by_cases hkZero : k.val = 0
    · rw [hkZero]
      simpa only [Nat.cast_zero, zero_div] using
        zero_fraction_sub_unitFraction_ne_integer hK q
    · let t : ℕ := k.val - 1
      have htSucc : t + 1 = k.val := by
        simpa [t] using
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hkZero)
      have hstrict :
          jacobiMANOVAGammaScale m n₁ n₂ i < n₁ + n₂ ∨ 0 < t := by
        by_contra h
        push Not at h
        have hscaleEq :
            jacobiMANOVAGammaScale m n₁ n₂ i = n₁ + n₂ :=
          le_antisymm hjLe h.1
        have hiVal : i.val = 2 * m :=
          (jacobiMANOVAGammaScale_eq_sum_iff hn₁ hn₂ i).mp hscaleEq
        have hi : i = jacobiMANOVATopFamilyIndex hm := by
          apply Fin.ext
          simpa [jacobiMANOVATopFamilyIndex] using hiVal
        have hkVal : k.val = 1 := by omega
        apply hne
        subst i
        have hk : k =
            (⟨1, by rw [jacobiMANOVAGammaScale_top hm]; exact hK⟩ :
              Fin (jacobiMANOVAGammaScale m n₁ n₂
                (jacobiMANOVATopFamilyIndex hm))) := Fin.ext hkVal
        subst k
        rfl
      have hfrac := refinedPositiveFraction_ne_integer_of_maximalDenominator
        (K := n₁ + n₂)
        (j := jacobiMANOVAGammaScale m n₁ n₂ i)
        (k := t) (by omega) hjPos hjLe (by omega) hstrict q
      simpa [htSucc] using hfrac

/-- **Exact classical Jacobi/Gaussian value relation.** -/
theorem jacobiMANOVAPartitionNormalizerMero_eq_gaussian_mul_gammaQuotient
    (m n₁ n₂ : ℕ) :
    jacobiMANOVAPartitionNormalizerMero m n₁ n₂ =
      gaussianBetaEnsemblePartitionNormalizerMero m *
        jacobiMANOVAGammaQuotientMero m n₁ n₂ := rfl

/-- Dividing the classical Jacobi/MANOVA normalizer by the Gaussian one exposes the signed
three-band Gamma quotient exactly. -/
theorem jacobiMANOVAPartitionNormalizer_div_gaussian_eq_gammaQuotient
    (m n₁ n₂ : ℕ) :
    jacobiMANOVAPartitionNormalizerMero m n₁ n₂ /
        gaussianBetaEnsemblePartitionNormalizerMero m =
      jacobiMANOVAGammaQuotientMero m n₁ n₂ := by
  rw [jacobiMANOVAPartitionNormalizerMero_eq_gaussian_mul_gammaQuotient]
  field_simp [gaussianBetaEnsemblePartitionNormalizerMero_ne_zero]

@[simp] theorem jacobiMANOVAGammaQuotientMero_zero (n₁ n₂ : ℕ) :
    jacobiMANOVAGammaQuotientMero 0 n₁ n₂ = 1 := by
  simp [jacobiMANOVAGammaQuotientMero, gammaNatScaleFamilyMero]

/-- Under the rectangularity hypotheses, the classical Jacobi/Gaussian quotient is HT exactly
when the observed transmission/covariance spectrum has positive size. -/
theorem hypertranscendentalOver_jacobiMANOVA_div_gaussian_iff_pos
    {m n₁ n₂ : ℕ} (hm₁ : m ≤ n₁) (hm₂ : m ≤ n₂) :
    HypertranscendentalOver (RatFunc ℂ)
        (jacobiMANOVAPartitionNormalizerMero m n₁ n₂ /
          gaussianBetaEnsemblePartitionNormalizerMero m) ↔
      0 < m := by
  rw [jacobiMANOVAPartitionNormalizer_div_gaussian_eq_gammaQuotient]
  constructor
  · intro hHT
    by_contra hm
    have hm0 : m = 0 := by omega
    subst m
    exact hHT (by
      rw [jacobiMANOVAGammaQuotientMero_zero]
      simpa only [map_one] using
        (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
          DifferentialAlgebraicOver (RatFunc ℂ)
            (algebraMap (RatFunc ℂ) (meroField Set.univ) 1)))
  · intro hm
    exact hypertranscendentalOver_jacobiMANOVAGammaQuotientMero hm hm₁ hm₂

/-- The Euler beta/Veneziano Gamma carrier when both channel arguments vary on positive integer
slopes of the same observed clock. -/
def scaledEulerBetaMero (n₁ n₂ : ℕ) : meroField Set.univ :=
  gammaNatScaleMero n₁ 0 * gammaNatScaleMero n₂ 0 /
    gammaNatScaleMero (n₁ + n₂) 0

/-- **Quantum-transport/open-string value relation.**  A one-channel Jacobi/MANOVA quotient is
exactly the scaled Euler beta carrier `B(n₁*z,n₂*z)`. -/
theorem jacobiMANOVAGammaQuotientMero_one_eq_scaledEulerBeta
    (n₁ n₂ : ℕ) :
    jacobiMANOVAGammaQuotientMero 1 n₁ n₂ =
      scaledEulerBetaMero n₁ n₂ := by
  rw [jacobiMANOVAGammaQuotientMero, gammaNatScaleFamilyMero]
  simp [jacobiMANOVAGammaScale, jacobiMANOVAGammaShift,
    jacobiMANOVAGammaCharge, scaledEulerBetaMero,
    Fin.prod_univ_succ]
  ring

/-- Dividing the one-channel Jacobi/MANOVA normalizer by its Gaussian normalizer exposes the
scaled Euler beta amplitude exactly. -/
theorem jacobiMANOVAPartitionNormalizer_one_div_gaussian_eq_scaledEulerBeta
    (n₁ n₂ : ℕ) :
    jacobiMANOVAPartitionNormalizerMero 1 n₁ n₂ /
        gaussianBetaEnsemblePartitionNormalizerMero 1 =
      scaledEulerBetaMero n₁ n₂ := by
  rw [jacobiMANOVAPartitionNormalizer_div_gaussian_eq_gammaQuotient,
    jacobiMANOVAGammaQuotientMero_one_eq_scaledEulerBeta]

/-- If both channel slopes are positive, the scaled Euler beta/Veneziano carrier is HT in the
common clock.  This is the variable-variable complement of the fixed-channel Veneziano boundary. -/
theorem hypertranscendentalOver_scaledEulerBetaMero
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    HypertranscendentalOver (RatFunc ℂ)
      (scaledEulerBetaMero n₁ n₂) := by
  rw [← jacobiMANOVAGammaQuotientMero_one_eq_scaledEulerBeta]
  exact hypertranscendentalOver_jacobiMANOVAGammaQuotientMero
    (m := 1) (n₁ := n₁) (n₂ := n₂) (by omega) (by omega) (by omega)

/-- No rational or finite-Laurent clock model equals a positive-slope scaled Euler beta
amplitude. -/
theorem scaledEulerBetaMero_ne_ratFuncModel
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (r : RatFunc ℂ) :
    scaledEulerBetaMero n₁ n₂ ≠
      algebraMap (RatFunc ℂ) (meroField Set.univ) r := by
  intro heq
  apply hypertranscendentalOver_scaledEulerBetaMero hn₁ hn₂
  rw [heq]
  exact HTGeometry.differentialAlgebraicOver_algebraMap r

/-- Any scalar-aware finite differential circuit for the positive-slope scaled beta amplitude
contains a hypertranscendental non-scalar source. -/
theorem exists_hypertranscendental_atom_of_scaledEulerBetaCircuit
    {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (scaledEulerBetaMero n₁ n₂)) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    (hypertranscendentalOver_scaledEulerBetaMero hn₁ hn₂) hcircuit

end

end GaloisForLFunctions
