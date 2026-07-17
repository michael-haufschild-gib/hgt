import GaloisForLFunctions.HTGeometry.MeromorphicGammaNatScale

/-!
# Symmetric Dirichlet normalizer boundary

The normalizing factor of a `K`-category symmetric Dirichlet density with common concentration
parameter `z` is

`Gamma(K*z) / Gamma(z)^K`.

This exact value occurs in Dirichlet evidential machine learning and in Dirichlet-multinomial
models for genomic and genetic count data.  Gauss multiplication refines it into `K` unit-scale
Gamma orbits.  For `K > 1`, every nonzero fractional orbit survives, so the normalizer is
hypertranscendental in the concentration parameter.  For `K = 1`, it is exactly one.

Thus the obstruction belongs to the observable normalization across categories, not to the
temporal evolution of an optimizer, neural network, population, or sequencing process.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

local instance symmetricDirichletDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance symmetricDirichletComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance symmetricDirichletComplexAlgebraMero :
    Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance symmetricDirichletDifferential :
    Differential (meroField Set.univ) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

local instance symmetricDirichletRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField Set.univ) :=
  (ratfuncToMero Set.univ isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ).toAlgebra

local instance symmetricDirichletRatFuncDifferential :
    Differential (RatFunc ℂ) := ratFuncCoordinateDifferential

local instance symmetricDirichletDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField Set.univ) :=
  { deriv_algebraMap := fun r => meroField_deriv_ratfuncToMero r }

local instance symmetricDirichletCharZero :
    CharZero (meroField Set.univ) :=
  charZero_of_injective_algebraMap
    (algebraMap (RatFunc ℂ) (meroField Set.univ)).injective

/-- The concentration-dependent normalizing factor of a symmetric `K`-category Dirichlet
density. -/
def symmetricDirichletNormalizerMero (K : ℕ) : meroField Set.univ :=
  gammaNatScaleMero K 0 / gammaShiftMero 0 ^ K

/-- Fractional translation-orbit representatives exposed by Gauss multiplication. -/
def symmetricDirichletOrbitShifts (K : ℕ) : Fin K → ℂ :=
  fun k => (k : ℂ) / K

/-- After cancelling the denominator, the zero orbit has charge `1-K` and every nonzero
fractional orbit has charge one. -/
def symmetricDirichletOrbitCharges (K : ℕ) : Fin K → ℤ :=
  fun k => if k.val = 0 then 1 - (K : ℤ) else 1

/-- The unit-scale orbit product left after Gauss refinement of the symmetric Dirichlet
normalizer. -/
def symmetricDirichletRefinedMero (K : ℕ) : meroField Set.univ :=
  gammaOrbitProductMero
    (symmetricDirichletOrbitShifts K) (symmetricDirichletOrbitCharges K)

private theorem fin_prod_div_distinguished_pow_eq_charge_product
    {K : ℕ} (hK : 0 < K) (f : Fin K → meroField Set.univ)
    (hf : ∀ k, f k ≠ 0) :
    (∏ k, f k) / f ⟨0, hK⟩ ^ K =
      ∏ k, f k ^ (if k.val = 0 then 1 - (K : ℤ) else 1) := by
  classical
  let k0 : Fin K := ⟨0, hK⟩
  have hmem : k0 ∈ (Finset.univ : Finset (Fin K)) := Finset.mem_univ k0
  rw [← Finset.mul_prod_erase Finset.univ f hmem]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun k => f k ^ (if k.val = 0 then 1 - (K : ℤ) else 1)) hmem]
  have hrest :
      (∏ k ∈ (Finset.univ : Finset (Fin K)).erase k0,
          f k ^ (if k.val = 0 then 1 - (K : ℤ) else 1)) =
        ∏ k ∈ (Finset.univ : Finset (Fin K)).erase k0, f k := by
    apply Finset.prod_congr rfl
    intro k hk
    have hk0 : k ≠ k0 := Finset.ne_of_mem_erase hk
    have hkzero : k.val ≠ 0 := by
      intro hvalue
      apply hk0
      apply Fin.ext
      simpa [k0] using hvalue
    simp [hkzero]
  rw [hrest]
  change
    (f k0 * ∏ k ∈ (Finset.univ : Finset (Fin K)).erase k0, f k) / f k0 ^ K =
      f k0 ^ (1 - (K : ℤ)) *
        ∏ k ∈ (Finset.univ : Finset (Fin K)).erase k0, f k
  rw [zpow_sub₀ (hf k0), zpow_one, zpow_natCast]
  ring

/-- **Exact Dirichlet normal form.**  The symmetric normalizer is a nonzero DA Gauss gauge times
its fractional-orbit charge product. -/
theorem symmetricDirichletNormalizerMero_normalForm
    {K : ℕ} (hK : 0 < K) :
    symmetricDirichletNormalizerMero K =
      gammaNatScaleGaussGaugeMero K 0 * symmetricDirichletRefinedMero K := by
  rw [symmetricDirichletNormalizerMero, gammaNatScaleMero_gauss hK 0]
  change
    (gammaNatScaleGaussGaugeMero K 0 * gammaNatScaleGaussProductMero K 0) /
        gammaShiftMero 0 ^ K =
      gammaNatScaleGaussGaugeMero K 0 * symmetricDirichletRefinedMero K
  have hrefined : gammaNatScaleGaussProductMero K 0 / gammaShiftMero 0 ^ K =
      symmetricDirichletRefinedMero K := by
    rw [gammaNatScaleGaussProductMero, symmetricDirichletRefinedMero,
      gammaOrbitProductMero, ← Fin.prod_univ_eq_prod_range]
    simpa [symmetricDirichletOrbitShifts, symmetricDirichletOrbitCharges] using
      (fin_prod_div_distinguished_pow_eq_charge_product hK
        (fun k : Fin K => gammaShiftMero ((k : ℂ) / K))
        (fun k => gammaShiftMero_ne_zero ((k : ℂ) / K)))
  calc
    (gammaNatScaleGaussGaugeMero K 0 * gammaNatScaleGaussProductMero K 0) /
          gammaShiftMero 0 ^ K =
        gammaNatScaleGaussGaugeMero K 0 *
          (gammaNatScaleGaussProductMero K 0 / gammaShiftMero 0 ^ K) := by ring
    _ = _ := by rw [hrefined]

/-- Every genuinely multiclass symmetric Dirichlet normalizer is HT in its common concentration
parameter. -/
theorem hypertranscendentalOver_symmetricDirichletNormalizerMero
    {K : ℕ} (hK : 1 < K) :
    HypertranscendentalOver (RatFunc ℂ) (symmetricDirichletNormalizerMero K) := by
  let shifts := symmetricDirichletOrbitShifts K
  let charges := symmetricDirichletOrbitCharges K
  let c0 : Fin K := ⟨1, hK⟩
  have hrefined : HypertranscendentalOver (RatFunc ℂ)
      (symmetricDirichletRefinedMero K) := by
    rw [symmetricDirichletRefinedMero]
    apply hypertranscendentalOver_gammaOrbitProductMero shifts charges c0
    · simp [charges, symmetricDirichletOrbitCharges, c0]
    · intro c hc n hn
      have hKC : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hmulC : (c.val : ℂ) - 1 = (K : ℂ) * (n : ℂ) := by
        simp [shifts, symmetricDirichletOrbitShifts, c0] at hn
        field_simp [hKC] at hn
        linear_combination hn
      have hmulZ : (c.val : ℤ) - 1 = (K : ℤ) * n := by
        exact_mod_cast hmulC
      have hcLt : (c.val : ℤ) < K := by exact_mod_cast c.isLt
      have hcNe : (c.val : ℤ) ≠ 1 := by
        intro hvalue
        apply hc
        apply Fin.ext
        exact_mod_cast hvalue
      have hKZ : (1 : ℤ) < K := by exact_mod_cast hK
      have hcNonneg : (0 : ℤ) ≤ c.val := by omega
      have hKNonneg : (0 : ℤ) ≤ K := by omega
      rcases lt_trichotomy n 0 with hnNeg | hnZero | hnPos
      · have hnLe : n ≤ -1 := by omega
        have hprodLe : (K : ℤ) * n ≤ (K : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left hnLe hKNonneg
        omega
      · rw [hnZero, mul_zero] at hmulZ
        exact hcNe (by omega)
      · have hnOne : (1 : ℤ) ≤ n := by omega
        have hKLe : (K : ℤ) ≤ (K : ℤ) * n := by
          calc
            (K : ℤ) = (K : ℤ) * 1 := by ring
            _ ≤ (K : ℤ) * n := mul_le_mul_of_nonneg_left hnOne hKNonneg
        omega
  rw [symmetricDirichletNormalizerMero_normalForm (by omega), mul_comm]
  exact (HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
    (differentialAlgebraicOver_gammaNatScaleGaussGaugeMero K 0)
    (gammaNatScaleGaussGaugeMero_ne_zero (by omega) 0)).2 hrefined

/-- **Positive source extraction for AI/genomic circuits.**  Any finite differential circuit
with arbitrary rational-function scalars that exactly realizes a multiclass symmetric Dirichlet
normalizer must already contain a genuinely HT non-scalar atom. -/
theorem exists_hypertranscendental_atom_of_symmetricDirichletNormalizerCircuit
    {K : ℕ} (hK : 1 < K) {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (symmetricDirichletNormalizerMero K)) :
    ∃ a : meroField Set.univ,
      Atom a ∧ HypertranscendentalOver (RatFunc ℂ) a :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    (hypertranscendentalOver_symmetricDirichletNormalizerMero hK) hcircuit

/-- A one-category Dirichlet normalizer contains no observable Gamma orbit: it is exactly one. -/
@[simp] theorem symmetricDirichletNormalizerMero_one :
    symmetricDirichletNormalizerMero 1 = 1 := by
  rw [symmetricDirichletNormalizerMero, gammaNatScaleMero_one]
  simpa using div_self (gammaShiftMero_ne_zero 0)

/-- **Exact category-count boundary.**  Among positive category counts, the symmetric Dirichlet
normalizer is DA exactly in the degenerate one-category case. -/
theorem differentialAlgebraicOver_symmetricDirichletNormalizerMero_iff_one
    {K : ℕ} (hK : 0 < K) :
    DifferentialAlgebraicOver (RatFunc ℂ) (symmetricDirichletNormalizerMero K) ↔
      K = 1 := by
  constructor
  · intro hDA
    by_contra hne
    have hmulticlass : 1 < K := by omega
    exact (hypertranscendentalOver_symmetricDirichletNormalizerMero hmulticlass) hDA
  · intro hKone
    subst K
    rw [symmetricDirichletNormalizerMero_one]
    simpa only [map_one] using
      (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))

/-- Hypertranscendence is exactly the genuinely multiclass sector. -/
theorem hypertranscendentalOver_symmetricDirichletNormalizerMero_iff_multiclass
    {K : ℕ} (hK : 0 < K) :
    HypertranscendentalOver (RatFunc ℂ) (symmetricDirichletNormalizerMero K) ↔
      1 < K := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_symmetricDirichletNormalizerMero_iff_one hK]
  omega

end

end GaloisForLFunctions
