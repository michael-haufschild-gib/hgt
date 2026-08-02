import GaloisForLFunctions.HTGeometry.MultivariateEntireVanishingPower

/-!
# Gaussian flat units for fixed-factor Poincare interpolation

A centered complex Gaussian supplies lattice decay but ordinarily changes target jets.  The exact
finite-order correction

`D = 1 - (1 - G)^m = G * ∑_{r < m} (1 - G)^r`

simultaneously has the same jets as `1` below order `m` and retains one full Gaussian factor.
This is the seed used in the rigorous integer-lattice Poincare construction.
-/

open Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Coordinatewise centered complex Gaussian with real decay parameters. -/
def centeredComplexGaussian {d : ℕ} (σ : Fin d → ℝ)
    (center : Fin d → ℂ) : MultivariateEntire d :=
  ⟨⟨fun x ↦ Complex.exp (-∑ i, (σ i : ℂ) * (x i - center i) ^ 2), by
      fun_prop⟩,
    fun x v ↦ by
      apply Complex.differentiable_exp.comp
      fun_prop⟩

@[simp]
theorem centeredComplexGaussian_apply {d : ℕ} (σ : Fin d → ℝ)
    (center x : Fin d → ℂ) :
    (centeredComplexGaussian σ center).1 x =
      Complex.exp (-∑ i, (σ i : ℂ) * (x i - center i) ^ 2) :=
  rfl

@[simp]
theorem centeredComplexGaussian_center {d : ℕ} (σ : Fin d → ℝ)
    (center : Fin d → ℂ) :
    (centeredComplexGaussian σ center).1 center = 1 := by
  simp

/-- Bundled flat correction of a centered Gaussian. -/
structure GaussianFlatSeedData {d : ℕ} (center : Fin d → ℂ) (m : ℕ) where
  gaussian : MultivariateEntire d
  damping : MultivariateEntire d
  geom : MultivariateEntire d
  gaussian_center : gaussian.1 center = 1
  damping_center : damping.1 center = 1
  factorization : damping = multivariateEntireMul gaussian geom
  preserves_target : ∀ (P : MultivariateEntire d) (a : Fin d →₀ ℕ),
    Finsupp.degree a < m →
      multiIndexJetEvalCLM center a (multivariateEntireMul damping P) =
        multiIndexJetEvalCLM center a P

/-- Exact finite-order flat correction for any entire source taking value one at the center. -/
def gaussianFlatSeedDataOfUnitValue {d m : ℕ}
    (center : Fin d → ℂ) (G : MultivariateEntire d)
    (hG : G.1 center = 1) (hm : 0 < m) : GaussianFlatSeedData center m := by
  let one : MultivariateEntire d := mvPolynomialMultivariateEntire 1
  let complement : MultivariateEntire d := one - G
  let damping : MultivariateEntire d :=
    one - multivariateEntirePow complement m
  let geom : MultivariateEntire d :=
    ∑ r ∈ Finset.range m, multivariateEntirePow complement r
  have hone (x : Fin d → ℂ) : one.1 x = 1 := by
    simp [one, mvPolynomialMultivariateEntire]
  have hcomplement : complement.1 center = 0 := by
    simp [complement, hone, hG]
  have hdamping : damping.1 center = 1 := by
    simp [damping, hcomplement, hone, hm.ne']
  have hfactor : damping = multivariateEntireMul G geom := by
    ext x
    have hgeom := geom_sum_mul_neg (1 - G.1 x) m
    have hdampingx : damping.1 x = one.1 x - complement.1 x ^ m := by
      rfl
    have hgeomx : geom.1 x =
        ∑ r ∈ Finset.range m, complement.1 x ^ r := by
      simp [geom]
    have hcomp : complement.1 x = 1 - G.1 x := by
      change one.1 x - G.1 x = 1 - G.1 x
      rw [hone]
    rw [multivariateEntireMul_apply, hdampingx, hgeomx]
    rw [hone, hcomp]
    calc
      1 - (1 - G.1 x) ^ m =
          (∑ r ∈ Finset.range m, (1 - G.1 x) ^ r) * G.1 x := by
        rw [← hgeom]
        ring
      _ = G.1 x * ∑ r ∈ Finset.range m, (1 - G.1 x) ^ r := by ring
  refine ⟨G, damping, geom, hG, hdamping, hfactor, ?_⟩
  intro P a ha
  have hvanish := multiIndexJetEvalCLM_mul_pow_eq_zero_of_degree_lt
    complement P center hcomplement a ha
  have hsource : multivariateEntireMul damping P =
      P - multivariateEntireMul (multivariateEntirePow complement m) P := by
    ext x
    change (one.1 x - complement.1 x ^ m) * P.1 x =
      P.1 x - complement.1 x ^ m * P.1 x
    rw [hone]
    ring
  rw [hsource]
  calc
    multiIndexJetEvalCLM center a
        (P - multivariateEntireMul (multivariateEntirePow complement m) P) =
        multiIndexJetEvalCLM center a P -
          multiIndexJetEvalCLM center a
            (multivariateEntireMul (multivariateEntirePow complement m) P) :=
      map_sub (multiIndexJetEvalCLM center a) P
        (multivariateEntireMul (multivariateEntirePow complement m) P)
    _ = multiIndexJetEvalCLM center a P := by rw [hvanish, sub_zero]

/-- The canonical flat Gaussian seed at a chosen center and order. -/
def gaussianFlatSeedData {d m : ℕ} (σ : Fin d → ℝ)
    (center : Fin d → ℂ) (hm : 0 < m) : GaussianFlatSeedData center m :=
  gaussianFlatSeedDataOfUnitValue center (centeredComplexGaussian σ center)
    (centeredComplexGaussian_center σ center) hm

end

end GaloisForLFunctions.HTGeometry
