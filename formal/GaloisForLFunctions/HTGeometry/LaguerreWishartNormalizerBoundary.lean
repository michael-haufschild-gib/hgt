import GaloisForLFunctions.HTGeometry.GammaSameSignProductBoundary
import GaloisForLFunctions.HTGeometry.GaussianBetaEnsembleNormalizerBoundary
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Laguerre--Wishart normalization boundary

Dumitriu--Edelman equation (4) gives the beta-Laguerre density normalizer.  After writing
`z = beta/2`, taking the reciprocal Gamma part, and omitting the `z`-independent factor
`Gamma(a)`, its exact relation to the beta-Hermite/Gaussian partition normalizer is

`L_{N+1}(a,z) / G_{N+1}(z) = product_{r=1}^N Gamma(a-r*z)`.

The quotient is a nonempty same-orientation negative Gamma family precisely when `N>0`.
The finite same-sign parent theorem removes every exceptional-shift condition: its HT boundary is
exactly `N>0`, for every complex shape parameter `a`.

On the classical rectangular Wishart ray `a=n*z`, the previously omitted `Gamma(a)` also varies.
The complete Laguerre/Gaussian quotient becomes the positive Gamma band

`product_{r=0}^{m-1} Gamma((n-r)*z)`.

For `m <= n`, every scale is positive, so this band is HT exactly when the observed matrix has at
least one eigenvalue.  This isolates the obstruction in the normalization of the observed
eigenvalue/time-delay spectrum, not in a temporal evolution law.
-/

open Filter Set Topology Function Complex
open scoped BigOperators Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The negative slopes `1,...,N` in the fixed-shape beta-Laguerre/Gaussian quotient. -/
def laguerreBetaDeformationScale (N : ℕ) (i : Fin N) : ℕ := i.val + 1

/-- Fixed beta-Laguerre shape on every negative-slope Gamma factor. -/
def laguerreBetaDeformationShift (N : ℕ) (a : ℂ) (_ : Fin N) : ℂ := a

/-- Every factor in the Laguerre deformation tower has positive multiplicity one. -/
def laguerreBetaDeformationCharge (N : ℕ) (_ : Fin N) : ℤ := 1

/-- The exact variable Gamma tower distinguishing a fixed-shape beta-Laguerre ensemble with
`N+1` eigenvalues from its beta-Hermite/Gaussian counterpart. -/
def laguerreBetaDeformationTowerMero (N : ℕ) (a : ℂ) : meroField Set.univ :=
  gammaNegativeNatScaleFamilyMero
    (laguerreBetaDeformationScale N)
    (laguerreBetaDeformationShift N a)
    (laguerreBetaDeformationCharge N)

/-- Reciprocal Gamma part of the fixed-shape beta-Laguerre density normalizer, with the
`z`-independent factor `Gamma(a)` and elementary powers of two omitted. -/
def laguerreBetaEnsemblePartitionNormalizerMero (N : ℕ) (a : ℂ) :
    meroField Set.univ :=
  gaussianBetaEnsemblePartitionNormalizerMero (N + 1) *
    laguerreBetaDeformationTowerMero N a

/-- The corresponding Gamma-dependent probability-density prefactor. -/
def laguerreBetaEnsembleDensityGammaNormalizerMero (N : ℕ) (a : ℂ) :
    meroField Set.univ :=
  (laguerreBetaEnsemblePartitionNormalizerMero N a)⁻¹

theorem laguerreBetaDeformationScale_pos (N : ℕ) (i : Fin N) :
    0 < laguerreBetaDeformationScale N i := by
  simp [laguerreBetaDeformationScale]

theorem laguerreBetaDeformationTowerMero_ne_zero (N : ℕ) (a : ℂ) :
    laguerreBetaDeformationTowerMero N a ≠ 0 := by
  rw [laguerreBetaDeformationTowerMero,
    gammaNegativeNatScaleFamilyMero, Finset.prod_ne_zero_iff]
  intro i _
  exact zpow_ne_zero _
    (gammaNegativeNatScaleMero_ne_zero
      (laguerreBetaDeformationScale_pos N i)
      (laguerreBetaDeformationShift N a i))

theorem gaussianBetaEnsemblePartitionNormalizerMero_ne_zero (K : ℕ) :
    gaussianBetaEnsemblePartitionNormalizerMero K ≠ 0 := by
  rw [gaussianBetaEnsemblePartitionNormalizerMero]
  apply div_ne_zero
  · rw [Finset.prod_ne_zero_iff]
    intro i _
    exact gammaNatScaleMero_ne_zero (by omega) 1
  · exact pow_ne_zero K (gammaShiftMero_ne_zero 1)

/-- **Exact beta-Laguerre/Gaussian value relation.** -/
theorem laguerreBetaEnsemblePartitionNormalizerMero_eq_gaussian_mul_deformation
    (N : ℕ) (a : ℂ) :
    laguerreBetaEnsemblePartitionNormalizerMero N a =
      gaussianBetaEnsemblePartitionNormalizerMero (N + 1) *
        laguerreBetaDeformationTowerMero N a := rfl

/-- Dividing the fixed-shape beta-Laguerre normalizer by the Gaussian normalizer exposes exactly
the negative-orientation Gamma deformation tower. -/
theorem laguerreBetaEnsemble_div_gaussian_eq_deformationTower
    (N : ℕ) (a : ℂ) :
    laguerreBetaEnsemblePartitionNormalizerMero N a /
        gaussianBetaEnsemblePartitionNormalizerMero (N + 1) =
      laguerreBetaDeformationTowerMero N a := by
  rw [laguerreBetaEnsemblePartitionNormalizerMero_eq_gaussian_mul_deformation]
  field_simp [gaussianBetaEnsemblePartitionNormalizerMero_ne_zero]

/-- Every nonempty fixed-shape Laguerre deformation tower is unconditionally HT. -/
theorem hypertranscendentalOver_laguerreBetaDeformationTowerMero
    {N : ℕ} (hN : 0 < N) (a : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
      (laguerreBetaDeformationTowerMero N a) := by
  exact hypertranscendentalOver_gammaNegativeNatScaleFamilyMero_of_pos hN
    (laguerreBetaDeformationScale N)
    (laguerreBetaDeformationShift N a)
    (laguerreBetaDeformationCharge N)
    (laguerreBetaDeformationScale_pos N)
    (by simp [laguerreBetaDeformationCharge])

@[simp] theorem laguerreBetaDeformationTowerMero_zero (a : ℂ) :
    laguerreBetaDeformationTowerMero 0 a = 1 := by
  simp [laguerreBetaDeformationTowerMero,
    gammaNegativeNatScaleFamilyMero]

/-- The deformation tower is DA exactly in the one-eigenvalue sector. -/
theorem differentialAlgebraicOver_laguerreBetaDeformationTowerMero_iff_eq_zero
    (N : ℕ) (a : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (laguerreBetaDeformationTowerMero N a) ↔
      N = 0 := by
  constructor
  · intro hDA
    by_contra hN
    exact (hypertranscendentalOver_laguerreBetaDeformationTowerMero
      (Nat.pos_of_ne_zero hN) a) hDA
  · rintro rfl
    rw [laguerreBetaDeformationTowerMero_zero]
    simpa only [map_one] using
      (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
        DifferentialAlgebraicOver (RatFunc ℂ)
          (algebraMap (RatFunc ℂ) (meroField Set.univ) 1))

/-- **Exact fixed-shape Laguerre/Gaussian quotient boundary.** -/
theorem hypertranscendentalOver_laguerreBetaEnsemble_div_gaussian_iff_pos
    (N : ℕ) (a : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (laguerreBetaEnsemblePartitionNormalizerMero N a /
          gaussianBetaEnsemblePartitionNormalizerMero (N + 1)) ↔
      0 < N := by
  rw [laguerreBetaEnsemble_div_gaussian_eq_deformationTower,
    HypertranscendentalOver,
    differentialAlgebraicOver_laguerreBetaDeformationTowerMero_iff_eq_zero]
  omega

/-- Positive source extraction for every finite differential circuit presenting a nontrivial
Laguerre/Gaussian normalization quotient. -/
theorem exists_hypertranscendental_atom_of_laguerreGaussianNormalizerQuotientCircuit
    {N : ℕ} (hN : 0 < N) (a : ℂ)
    {Atom : meroField Set.univ → Prop}
    (hcircuit : HTGeometry.FiniteDifferentialCircuit
      (HTGeometry.BaseScalarOrAtom (RatFunc ℂ) (meroField Set.univ) Atom)
      (laguerreBetaEnsemblePartitionNormalizerMero N a /
        gaussianBetaEnsemblePartitionNormalizerMero (N + 1))) :
    ∃ x : meroField Set.univ,
      Atom x ∧ HypertranscendentalOver (RatFunc ℂ) x :=
  HTGeometry.exists_hypertranscendental_atom_of_scalarAwareFiniteDifferentialCircuit
    ((hypertranscendentalOver_laguerreBetaEnsemble_div_gaussian_iff_pos
      N a).2 hN) hcircuit

/-- Positive scales on the classical `m`-by-`n` rectangular Wishart ray. -/
def wishartRectangularGammaScale (m n : ℕ) (i : Fin m) : ℕ := n - i.val

/-- The complete Gamma band `Gamma(n*z) ... Gamma((n-m+1)*z)`. -/
def wishartRectangularGammaBandMero (m n : ℕ) : meroField Set.univ :=
  gammaNatScaleFamilyMero
    (wishartRectangularGammaScale m n)
    (fun _ => 0)
    (fun _ => 1)

/-- The reciprocal Gamma part of the classical rectangular Wishart/Laguerre normalizer after
omitting its nonzero elementary exponential gauge. -/
def wishartRectangularPartitionNormalizerMero (m n : ℕ) :
    meroField Set.univ :=
  gaussianBetaEnsemblePartitionNormalizerMero m *
    wishartRectangularGammaBandMero m n

theorem wishartRectangularGammaScale_pos
    {m n : ℕ} (hmn : m ≤ n) (i : Fin m) :
    0 < wishartRectangularGammaScale m n i := by
  rw [wishartRectangularGammaScale]
  omega

theorem wishartRectangularGammaBandMero_ne_zero
    {m n : ℕ} (hmn : m ≤ n) :
    wishartRectangularGammaBandMero m n ≠ 0 := by
  rw [wishartRectangularGammaBandMero,
    gammaNatScaleFamilyMero, Finset.prod_ne_zero_iff]
  intro i _
  exact zpow_ne_zero _
    (gammaNatScaleMero_ne_zero
      (wishartRectangularGammaScale_pos hmn i) 0)

/-- **Exact classical Wishart/Gaussian value relation.** -/
theorem wishartRectangularPartitionNormalizerMero_eq_gaussian_mul_gammaBand
    (m n : ℕ) :
    wishartRectangularPartitionNormalizerMero m n =
      gaussianBetaEnsemblePartitionNormalizerMero m *
        wishartRectangularGammaBandMero m n := rfl

/-- The Wishart/Gaussian quotient is exactly the rectangular Gamma band. -/
theorem wishartRectangular_div_gaussian_eq_gammaBand
    (m n : ℕ) :
    wishartRectangularPartitionNormalizerMero m n /
        gaussianBetaEnsemblePartitionNormalizerMero m =
      wishartRectangularGammaBandMero m n := by
  rw [wishartRectangularPartitionNormalizerMero_eq_gaussian_mul_gammaBand]
  field_simp [gaussianBetaEnsemblePartitionNormalizerMero_ne_zero]

/-- Every nonempty rectangular Wishart Gamma band is HT. -/
theorem hypertranscendentalOver_wishartRectangularGammaBandMero
    {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    HypertranscendentalOver (RatFunc ℂ)
      (wishartRectangularGammaBandMero m n) := by
  exact hypertranscendentalOver_gammaNatScaleFamilyMero_of_pos hm
    (wishartRectangularGammaScale m n)
    (fun _ => 0) (fun _ => 1)
    (wishartRectangularGammaScale_pos hmn)
    (by simp)

@[simp] theorem wishartRectangularGammaBandMero_zero (n : ℕ) :
    wishartRectangularGammaBandMero 0 n = 1 := by
  simp [wishartRectangularGammaBandMero, gammaNatScaleFamilyMero]

/-- Under the rectangularity condition, the complete classical Wishart/Gaussian quotient is HT
exactly when the observed covariance matrix has positive size. -/
theorem hypertranscendentalOver_wishartRectangular_div_gaussian_iff_pos
    {m n : ℕ} (hmn : m ≤ n) :
    HypertranscendentalOver (RatFunc ℂ)
        (wishartRectangularPartitionNormalizerMero m n /
          gaussianBetaEnsemblePartitionNormalizerMero m) ↔
      0 < m := by
  rw [wishartRectangular_div_gaussian_eq_gammaBand]
  constructor
  · intro hHT
    by_contra hm
    have hm0 : m = 0 := by omega
    subst m
    exact hHT (by
      rw [wishartRectangularGammaBandMero_zero]
      simpa only [map_one] using
        (HTGeometry.differentialAlgebraicOver_algebraMap (1 : RatFunc ℂ) :
          DifferentialAlgebraicOver (RatFunc ℂ)
            (algebraMap (RatFunc ℂ) (meroField Set.univ) 1)))
  · intro hm
    exact hypertranscendentalOver_wishartRectangularGammaBandMero hm hmn

end

end GaloisForLFunctions
