import GaloisForLFunctions.SelbergClass.MultipleStandardTwistDataGammaGeometry

/-!
# Spectral data for multiple standard twists

This module formalizes the unconditional data layer in Kaczorowski--Perelli,
*Multiple standard twists of `L`-functions*, equations (1.4)--(1.9): total
degree and internal shift, the conductor-normalized spectral values, their
finite fibres, the finite residual function `Ξ`, and the affine polar
hyperplanes.

`spectralXi` is only the finite sum displayed in (1.8).  This module does not
assert the paper's meromorphic continuation, the formula for residue fibres,
or non-cancellation of any displayed polar hyperplane.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.SelbergClass

namespace MultipleStandardTwistData

/-- Total degree `d = Σ d_ν` from Kaczorowski--Perelli (1.4), attached to the
selected gamma presentations of the input factors. -/
noncomputable def totalDegree {N : ℕ} (D : MultipleStandardTwistData N) : ℝ :=
  ∑ i, (D.factors i).gammaData.degree

/-- Total internal shift `θ = Σ d_ν θ_ν` from Kaczorowski--Perelli (1.4),
attached to the selected gamma presentations of the input factors. -/
noncomputable def totalInternalShift {N : ℕ} (D : MultipleStandardTwistData N) : ℝ :=
  ∑ i, (D.factors i).gammaData.degree * (D.factors i).gammaData.internalShift

/-- Affine constant in the reciprocal-Gamma denominator from Corollary 1:
`-(d + 1) / 2 + i θ`. -/
noncomputable def kpGammaShift {N : ℕ} (D : MultipleStandardTwistData N) : ℂ :=
  (-(((D.totalDegree + 1) / 2 : ℝ) : ℂ)) + I * (D.totalInternalShift : ℂ)

/-- Positive coordinate scale `q_ν κ_ν ^ d_ν` in the spectral value (1.7).
The conductor is read from the concrete selected gamma presentation. -/
noncomputable def spectralScale {N : ℕ} (D : MultipleStandardTwistData N)
    (i : Fin N) : ℝ :=
  (D.factors i).gammaData.conductor *
    (D.kappa i) ^ (D.factors i).gammaData.degree

/-- Product of the positive coordinate scales raised to their twist exponents. -/
noncomputable def spectralScaleProduct {N : ℕ} (D : MultipleStandardTwistData N) : ℝ :=
  ∏ i, (D.spectralScale i) ^ (D.kappa i)

/-- Unnormalized positive index product `∏ n_ν ^ κ_ν`. -/
noncomputable def weightedIndexValue {N : ℕ} (D : MultipleStandardTwistData N)
    (n : Fin N → ℕ+) : ℝ :=
  ∏ i, (((n i : ℕ) : ℝ) ^ (D.kappa i))

/-- Spectral value `α_n = ∏ (n_ν / (q_ν κ_ν ^ d_ν)) ^ κ_ν` from
Kaczorowski--Perelli (1.7). -/
noncomputable def spectralValue {N : ℕ} (D : MultipleStandardTwistData N)
    (n : Fin N → ℕ+) : ℝ :=
  ∏ i, ((((n i : ℕ) : ℝ) / D.spectralScale i) ^ (D.kappa i))

/-- Every spectral scale is strictly positive from the concrete positive
conductor and the positive twist exponent. -/
theorem spectralScale_pos {N : ℕ} (D : MultipleStandardTwistData N) (i : Fin N) :
    0 < D.spectralScale i := by
  unfold spectralScale
  exact mul_pos (D.factors i).gammaData.conductor_pos
    (Real.rpow_pos_of_pos (D.kappa_pos i) _)

/-- Exact normalization relating (1.7) to the unnormalized index product. -/
theorem spectralValue_mul_spectralScaleProduct {N : ℕ}
    (D : MultipleStandardTwistData N) (n : Fin N → ℕ+) :
    D.spectralValue n * D.spectralScaleProduct = D.weightedIndexValue n := by
  rw [spectralValue, spectralScaleProduct, weightedIndexValue,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Real.div_rpow (by positivity) (D.spectralScale_pos i).le]
  exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos (D.spectralScale_pos i) _).ne'

/-- All spectral values are positive. -/
theorem spectralValue_pos {N : ℕ} (D : MultipleStandardTwistData N)
    (n : Fin N → ℕ+) : 0 < D.spectralValue n := by
  unfold spectralValue
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos
    (div_pos (by exact_mod_cast (n i).property) (D.spectralScale_pos i)) _

/-- The scale product is positive. -/
theorem spectralScaleProduct_pos {N : ℕ} (D : MultipleStandardTwistData N) :
    0 < D.spectralScaleProduct := by
  unfold spectralScaleProduct
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (D.spectralScale_pos i) _

/-- A coordinate's unnormalized factor is bounded by the full unnormalized
index product. -/
theorem weightedIndexCoordinate_le {N : ℕ} (D : MultipleStandardTwistData N)
    (n : Fin N → ℕ+) (i : Fin N) :
    ((n i : ℕ) : ℝ) ^ D.kappa i ≤ D.weightedIndexValue n := by
  calc
    ((n i : ℕ) : ℝ) ^ D.kappa i = ∏ j ∈ ({i} : Finset (Fin N)),
        ((n j : ℕ) : ℝ) ^ D.kappa j := by simp
    _ ≤ ∏ j ∈ Finset.univ, ((n j : ℕ) : ℝ) ^ D.kappa j := by
      refine Finset.prod_le_prod_of_subset_of_one_le
        (Finset.singleton_subset_iff.mpr (Finset.mem_univ _)) ?_ ?_
      · intro j _
        exact Real.rpow_nonneg (by positivity) _
      · intro j _ _
        exact Real.one_le_rpow (by exact_mod_cast (n j).property) (D.kappa_pos j).le
    _ = D.weightedIndexValue n := rfl

/-- The indices giving one prescribed spectral value and nonzero coefficient
product. -/
def spectralFibre {N : ℕ} (D : MultipleStandardTwistData N) (α : ℝ) : Set (Fin N → ℕ+) :=
  {n | D.spectralValue n = α ∧ ∀ i, D.coeff i (n i : ℕ) ≠ 0}

/-- Spectrum of the multiple standard twist, as the image of the nonzero
coefficient index tuples under the spectral-value map. -/
def spectrum {N : ℕ} (D : MultipleStandardTwistData N) : Set ℝ :=
  {α | (D.spectralFibre α).Nonempty}

theorem mem_spectralFibre_iff {N : ℕ} (D : MultipleStandardTwistData N)
    (α : ℝ) (n : Fin N → ℕ+) :
    n ∈ D.spectralFibre α ↔
      D.spectralValue n = α ∧ ∀ i, D.coeff i (n i : ℕ) ≠ 0 := by
  rfl

theorem mem_spectrum_iff {N : ℕ} (D : MultipleStandardTwistData N) (α : ℝ) :
    α ∈ D.spectrum ↔ ∃ n : Fin N → ℕ+,
      D.spectralValue n = α ∧ ∀ i, D.coeff i (n i : ℕ) ≠ 0 := by
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, hn⟩

/-- Every spectral fibre is finite, without a caller-supplied certificate.
For positive `α`, the normalization identity bounds each positive-natural
coordinate by `(α * ∏ scale_ν ^ κ_ν) ^ (κ_i)⁻¹`; for nonpositive `α`, the
fibre is empty. -/
theorem spectralFibre_finite {N : ℕ} (D : MultipleStandardTwistData N) (α : ℝ) :
    (D.spectralFibre α).Finite := by
  by_cases hα : 0 < α
  · let M : ℝ := α * D.spectralScaleProduct
    have hM : 0 < M := mul_pos hα D.spectralScaleProduct_pos
    let B : Fin N → ℕ := fun i => Nat.ceil (M ^ (D.kappa i)⁻¹)
    let T : Set (Fin N → ℕ) := {m | ∀ i, m i ≤ B i}
    have hTfinite : T.Finite := by
      simpa only [T, Set.mem_setOf_eq, Set.mem_Iic] using
        (Set.Finite.pi' fun i => Set.finite_Iic (B i))
    let coeIndex : (Fin N → ℕ+) → (Fin N → ℕ) := fun n i => (n i : ℕ)
    have hcoeIndex : Function.Injective coeIndex := by
      intro n m h
      funext i
      apply PNat.eq
      exact congrFun h i
    have hsubset : D.spectralFibre α ⊆ coeIndex ⁻¹' T := by
      intro n hn
      change ∀ i, (n i : ℕ) ≤ B i
      intro i
      have hweighted : D.weightedIndexValue n = M := by
        rw [← D.spectralValue_mul_spectralScaleProduct, hn.1]
      have hfactor : ((n i : ℕ) : ℝ) ^ D.kappa i ≤ M := by
        rw [← hweighted]
        exact D.weightedIndexCoordinate_le n i
      have hrootpow : (M ^ (D.kappa i)⁻¹) ^ D.kappa i = M := by
        rw [← Real.rpow_mul hM.le, inv_mul_cancel₀ (ne_of_gt (D.kappa_pos i)),
          Real.rpow_one]
      have hreal : ((n i : ℕ) : ℝ) ≤ M ^ (D.kappa i)⁻¹ := by
        apply (Real.rpow_le_rpow_iff (by positivity)
          (Real.rpow_nonneg hM.le _) (D.kappa_pos i)).mp
        simpa only [hrootpow] using hfactor
      have hcast : ((n i : ℕ) : ℝ) ≤ (B i : ℝ) := by
        dsimp only [B]
        exact hreal.trans (Nat.le_ceil _)
      exact_mod_cast hcast
    exact (Set.Finite.preimage hcoeIndex.injOn hTfinite).subset hsubset
  · have hempty : D.spectralFibre α = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hn⟩
      have hpos := D.spectralValue_pos n
      rw [hn.1] at hpos
      exact (not_lt_of_ge (le_of_not_gt hα)) hpos
    rw [hempty]
    exact Set.finite_empty

/-- Finite carrier for a spectral fibre, constructed from the unconditional
finiteness theorem rather than supplied by a caller. -/
noncomputable def spectralFibreFinset {N : ℕ} (D : MultipleStandardTwistData N)
    (α : ℝ) : Finset (Fin N → ℕ+) :=
  (D.spectralFibre_finite α).toFinset

theorem mem_spectralFibreFinset_iff {N : ℕ} (D : MultipleStandardTwistData N)
    (α : ℝ) (n : Fin N → ℕ+) :
    n ∈ D.spectralFibreFinset α ↔ n ∈ D.spectralFibre α :=
  Set.Finite.mem_toFinset _

/-- Product root number `ω_F = ∏ ω_ν` from (1.9). -/
noncomputable def totalRootNumber {N : ℕ} (D : MultipleStandardTwistData N) : ℂ :=
  ∏ i, (D.factors i).gammaData.rootNumber

/-- Finite reflected residual sum
`Ξ(s, α) = ω_F ∑_{α_n = α} ∏ overline(a_ν(n_ν)) / n_ν^(1 - s_ν)`
from Kaczorowski--Perelli (1.8).  It is defined for every real `α`; outside
the spectrum the finite index set is empty. -/
noncomputable def spectralXi {N : ℕ} (D : MultipleStandardTwistData N)
    (s : Fin N → ℂ) (α : ℝ) : ℂ :=
  D.totalRootNumber * ∑ n ∈ D.spectralFibreFinset α,
    ∏ i, star (D.coeff i (n i : ℕ)) * (((n i : ℕ) : ℂ) ^ (s i - 1))

/-- Polar hyperplane `H_ℓ^*` from (1.5), expressed directly in coordinates. -/
def sourceHyperplane {N : ℕ} (D : MultipleStandardTwistData N) (ell : ℕ) :
    Set (Fin N → ℂ) :=
  {s | ∑ i, (((D.factors i).gammaData.degree : ℝ) : ℂ) * s i =
    (((D.totalDegree + 1) / 2 : ℝ) : ℂ) - (ell : ℂ) - I * (D.totalInternalShift : ℂ)}

/-- The source hyperplane is exactly the existing reciprocal-Gamma candidate
hyperplane for the Kaczorowski--Perelli affine shift. -/
theorem candidateHyperplane_eq_sourceHyperplane {N : ℕ}
    (D : MultipleStandardTwistData N) (ell : ℕ) :
    gammaCandidateHyperplane (multipleStandardTwistDegreeLinear D) (D.kpGammaShift) ell =
      D.sourceHyperplane ell := by
  ext s
  simp only [gammaCandidateHyperplane, Set.mem_setOf_eq, sourceHyperplane,
    multipleStandardTwistDegreeLinear_apply, kpGammaShift]
  constructor <;> intro h <;> linear_combination h

end MultipleStandardTwistData

end GaloisForLFunctions.SelbergClass
