import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAlgebra
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
# Frenet--Serret force conservation for elastica

This module formalizes paper equations (7)--(14) independently of coordinates.  A closed data
structure packages the Frenet--Serret and Euler component laws.  Their product-rule consequences
give the exact derivative of the elastica force, its constancy, the integrated multiplier and
torsion laws, and the scalar curvature ODE.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

/-- Twice-differentiable scalar data and a differentiable Frenet--Serret frame. -/
structure FrenetElasticaData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  curvature : ℝ → ℝ
  curvature₁ : ℝ → ℝ
  curvature₂ : ℝ → ℝ
  torsion : ℝ → ℝ
  torsion₁ : ℝ → ℝ
  lagrange : ℝ → ℝ
  lagrange₁ : ℝ → ℝ
  tangent : ℝ → V
  normal : ℝ → V
  binormal : ℝ → V
  curvature_deriv : ∀ s, HasDerivAt curvature (curvature₁ s) s
  curvature₁_deriv : ∀ s, HasDerivAt curvature₁ (curvature₂ s) s
  torsion_deriv : ∀ s, HasDerivAt torsion (torsion₁ s) s
  lagrange_deriv : ∀ s, HasDerivAt lagrange (lagrange₁ s) s
  tangent_deriv : ∀ s, HasDerivAt tangent (curvature s • normal s) s
  normal_deriv : ∀ s,
    HasDerivAt normal (torsion s • binormal s - curvature s • tangent s) s
  binormal_deriv : ∀ s, HasDerivAt binormal (-(torsion s) • normal s) s

/-- Paper equation (9), written in a general real normed vector space. -/
noncomputable def elasticaForce
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : FrenetElasticaData V) (s : ℝ) : V :=
  E.curvature₁ s • E.normal s +
    (E.curvature s * E.torsion s) • E.binormal s -
    (E.curvature s ^ (2 : ℕ) + E.lagrange s) • E.tangent s

/-- Exact three-component derivative in paper equation (10). -/
theorem hasDerivAt_elasticaForce
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : FrenetElasticaData V) (s : ℝ) :
    HasDerivAt (elasticaForce E)
      ((-(3 * E.curvature s * E.curvature₁ s + E.lagrange₁ s)) • E.tangent s +
       (2 * E.curvature₁ s * E.torsion s +
          E.curvature s * E.torsion₁ s) • E.binormal s +
       (E.curvature₂ s - E.curvature s *
          (E.curvature s ^ (2 : ℕ) + E.torsion s ^ (2 : ℕ) + E.lagrange s)) • E.normal s) s := by
  have hcurvatureTorsion : HasDerivAt
      (fun x => E.curvature x * E.torsion x)
      (E.curvature₁ s * E.torsion s + E.curvature s * E.torsion₁ s) s :=
    (E.curvature_deriv s).mul (E.torsion_deriv s)
  have hcurvatureSqLagrange : HasDerivAt
      (fun x => E.curvature x * E.curvature x + E.lagrange x)
      (E.curvature₁ s * E.curvature s +
        E.curvature s * E.curvature₁ s + E.lagrange₁ s) s :=
    ((E.curvature_deriv s).mul (E.curvature_deriv s)).add (E.lagrange_deriv s)
  have h := ((E.curvature₁_deriv s).smul (E.normal_deriv s)).add
    (hcurvatureTorsion.smul (E.binormal_deriv s)) |>.sub
      (hcurvatureSqLagrange.smul (E.tangent_deriv s))
  convert h using 1
  · funext x
    simp [elasticaForce, pow_two]
  · simp only [smul_sub, smul_smul]
    module

/-- Closed stationary-elastica package: positivity plus all three Euler components. -/
structure StationaryElasticaData (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    extends FrenetElasticaData V where
  curvature_pos : ∀ s, 0 < curvature s
  tangent_euler : ∀ s, 3 * curvature s * curvature₁ s + lagrange₁ s = 0
  binormal_euler : ∀ s, 2 * curvature₁ s * torsion s + curvature s * torsion₁ s = 0
  normal_euler : ∀ s,
    curvature₂ s - curvature s * (curvature s ^ (2 : ℕ) + torsion s ^ (2 : ℕ) + lagrange s) = 0

/-- Euler components make the full variational force stationary. -/
theorem stationaryElasticaForce_hasDerivAt_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    HasDerivAt (elasticaForce E.toFrenetElasticaData) 0 s := by
  convert hasDerivAt_elasticaForce E.toFrenetElasticaData s using 1
  rw [E.tangent_euler s, E.binormal_euler s, E.normal_euler s]
  simp

/-- Paper's vector `W` is globally constant along every packaged stationary elastica. -/
theorem stationaryElasticaForce_constant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    elasticaForce E.toFrenetElasticaData s =
      elasticaForce E.toFrenetElasticaData 0 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (elasticaForce E.toFrenetElasticaData) 0 x :=
    stationaryElasticaForce_hasDerivAt_zero E
  have hdiff : Differentiable ℝ (elasticaForce E.toFrenetElasticaData) :=
    fun x => (hderiv x).differentiableAt
  have hfderiv : ∀ x : ℝ,
      fderiv ℝ (elasticaForce E.toFrenetElasticaData) x = 0 := by
    intro x
    rw [(hderiv x).hasFDerivAt.fderiv]
    simp
  exact is_const_of_fderiv_eq_zero hdiff hfderiv s 0

/-- Integrated constant represented by `λ k₀²` in paper equation (11). -/
noncomputable def elasticaLambdaScale
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) : ℝ :=
  3 * E.curvature 0 ^ (2 : ℕ) + 2 * E.lagrange 0

/-- Tangent Euler component integrates to paper's multiplier formula. -/
theorem stationaryElastica_lagrange_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    E.lagrange s = -3 / 2 * E.curvature s ^ (2 : ℕ) + elasticaLambdaScale E / 2 := by
  let F : ℝ → ℝ :=
    (fun _ => (3 : ℝ)) * (E.curvature * E.curvature) +
      (fun _ => (2 : ℝ)) * E.lagrange
  have hzero : ∀ x : ℝ, HasDerivAt F 0 x := by
    intro x
    have h := ((hasDerivAt_const x (3 : ℝ)).mul
      ((E.curvature_deriv x).mul (E.curvature_deriv x))).add
      ((hasDerivAt_const x (2 : ℝ)).mul (E.lagrange_deriv x))
    have hraw : HasDerivAt F
        (3 * (E.curvature₁ x * E.curvature x +
          E.curvature x * E.curvature₁ x) + 2 * E.lagrange₁ x) x := by
      simpa only [F, zero_mul, zero_add] using h
    convert hraw using 1
    calc
      0 = 2 * (3 * E.curvature x * E.curvature₁ x + E.lagrange₁ x) := by
        rw [E.tangent_euler x, mul_zero]
      _ = 3 * (E.curvature₁ x * E.curvature x +
          E.curvature x * E.curvature₁ x) + 2 * E.lagrange₁ x := by ring
  have hdiff : Differentiable ℝ F := fun x => (hzero x).differentiableAt
  have hfderiv : ∀ x : ℝ, fderiv ℝ F x = 0 := by
    intro x
    rw [(hzero x).hasFDerivAt.fderiv]
    simp
  have hconst := is_const_of_fderiv_eq_zero hdiff hfderiv s 0
  have hconst' : 3 * E.curvature s ^ (2 : ℕ) + 2 * E.lagrange s =
      3 * E.curvature 0 ^ (2 : ℕ) + 2 * E.lagrange 0 := by
    simpa [F, pow_two] using hconst
  rw [elasticaLambdaScale]
  linarith

/-- Paper equation (12): the curvature--torsion product is conserved. -/
theorem stationaryElastica_curvatureSq_mul_torsion_constant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    E.curvature s ^ (2 : ℕ) * E.torsion s = E.curvature 0 ^ (2 : ℕ) * E.torsion 0 := by
  let F : ℝ → ℝ := E.curvature * E.curvature * E.torsion
  have hzero : ∀ x : ℝ, HasDerivAt F 0 x := by
    intro x
    have h := ((E.curvature_deriv x).mul (E.curvature_deriv x)).mul
      (E.torsion_deriv x)
    have hraw : HasDerivAt F
        ((E.curvature₁ x * E.curvature x +
            E.curvature x * E.curvature₁ x) * E.torsion x +
          E.curvature x * E.curvature x * E.torsion₁ x) x := by
      exact h
    convert hraw using 1
    calc
      0 = E.curvature x *
          (2 * E.curvature₁ x * E.torsion x +
            E.curvature x * E.torsion₁ x) := by
        rw [E.binormal_euler x, mul_zero]
      _ = (E.curvature₁ x * E.curvature x +
            E.curvature x * E.curvature₁ x) * E.torsion x +
          E.curvature x * E.curvature x * E.torsion₁ x := by ring
  have hdiff : Differentiable ℝ F := fun x => (hzero x).differentiableAt
  have hfderiv : ∀ x : ℝ, fderiv ℝ F x = 0 := by
    intro x
    rw [(hzero x).hasFDerivAt.fderiv]
    simp
  have hconst := is_const_of_fderiv_eq_zero hdiff hfderiv s 0
  simpa [F, pow_two] using hconst

/-- Pointwise torsion reconstruction from the conserved charge. -/
theorem stationaryElastica_torsion_eq
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    E.torsion s = E.curvature 0 ^ (2 : ℕ) * E.torsion 0 / E.curvature s ^ (2 : ℕ) := by
  have hne : E.curvature s ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (ne_of_gt (E.curvature_pos s))
  apply (eq_div_iff hne).2
  simpa [mul_comm] using stationaryElastica_curvatureSq_mul_torsion_constant E s

/-- Paper equation (14), with `elasticaLambdaScale E` standing for `λ k₀²`. -/
theorem stationaryElastica_curvature_ode
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : StationaryElasticaData V) (s : ℝ) :
    E.curvature₂ s = -1 / 2 * E.curvature s ^ (3 : ℕ) +
      E.curvature 0 ^ (4 : ℕ) * E.torsion 0 ^ (2 : ℕ) / E.curvature s ^ (3 : ℕ) +
      elasticaLambdaScale E / 2 * E.curvature s := by
  have hk : E.curvature s ≠ 0 := ne_of_gt (E.curvature_pos s)
  have hnormal := E.normal_euler s
  have hlagrange := stationaryElastica_lagrange_eq E s
  have htorsion := stationaryElastica_torsion_eq E s
  rw [hlagrange, htorsion] at hnormal
  field_simp [hk] at hnormal ⊢
  nlinarith

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
