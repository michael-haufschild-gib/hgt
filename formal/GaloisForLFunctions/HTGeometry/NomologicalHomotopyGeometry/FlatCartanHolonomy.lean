import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Flat Cartan holonomy, recurrent observation, and open polar history

This file formalizes the concrete rank-two Cartan model from the corresponding paper-proven NHG
card.  The boost representation preserves the split cyclic form.  Its constant one-dimensional
connection is flat, but its circle monodromy translates the full line of positive Cartan
polarizations.  Quotient observation is compact and recurrent while the marked lift, its length,
its action, and its polar condition number escape.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy

open Filter
open scoped Interval

/-- The real rank-two fibre of the Cartan model. -/
abbrev Fibre := ℝ × ℝ

/-- Split cyclic bilinear form of signature `(1, 1)`. -/
def splitForm (v w : Fibre) : ℝ :=
  v.1 * w.1 - v.2 * w.2

/-- Standard positive Euclidean pairing used to represent the polarized metric operator. -/
def euclideanPairing (v w : Fibre) : ℝ :=
  v.1 * w.1 + v.2 * w.2

/-- Infinitesimal boost generator `J(x,y)=(y,x)`. -/
def boostGenerator : Module.End ℝ Fibre where
  toFun v := (v.2, v.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem boostGenerator_apply (v : Fibre) : boostGenerator v = (v.2, v.1) :=
  rfl

/-- Lorentz boost `g_s`.  Its inverse is the boost with parameter `-s`. -/
noncomputable def boost (s : ℝ) : Fibre ≃ₗ[ℝ] Fibre where
  toFun v :=
    (Real.cosh s * v.1 + Real.sinh s * v.2,
      Real.sinh s * v.1 + Real.cosh s * v.2)
  invFun v :=
    (Real.cosh (-s) * v.1 + Real.sinh (-s) * v.2,
      Real.sinh (-s) * v.1 + Real.cosh (-s) * v.2)
  map_add' v w := by
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      ring
  map_smul' c v := by
    apply Prod.ext
    · dsimp
      ring
    · dsimp
      ring
  left_inv v := by
    rcases v with ⟨x, y⟩
    apply Prod.ext
    · simp only [Real.cosh_neg, Real.sinh_neg]
      calc
        Real.cosh s * (Real.cosh s * x + Real.sinh s * y) +
            -Real.sinh s * (Real.sinh s * x + Real.cosh s * y) =
            (Real.cosh s ^ 2 - Real.sinh s ^ 2) * x := by ring
        _ = x := by rw [Real.cosh_sq_sub_sinh_sq]; simp
    · simp only [Real.cosh_neg, Real.sinh_neg]
      calc
        -Real.sinh s * (Real.cosh s * x + Real.sinh s * y) +
            Real.cosh s * (Real.sinh s * x + Real.cosh s * y) =
            (Real.cosh s ^ 2 - Real.sinh s ^ 2) * y := by ring
        _ = y := by rw [Real.cosh_sq_sub_sinh_sq]; simp
  right_inv v := by
    rcases v with ⟨x, y⟩
    apply Prod.ext
    · simp only [Real.cosh_neg, Real.sinh_neg]
      calc
        Real.cosh s * (Real.cosh s * x + -Real.sinh s * y) +
            Real.sinh s * (-Real.sinh s * x + Real.cosh s * y) =
            (Real.cosh s ^ 2 - Real.sinh s ^ 2) * x := by ring
        _ = x := by rw [Real.cosh_sq_sub_sinh_sq]; simp
    · simp only [Real.cosh_neg, Real.sinh_neg]
      calc
        Real.sinh s * (Real.cosh s * x + -Real.sinh s * y) +
            Real.cosh s * (-Real.sinh s * x + Real.cosh s * y) =
            (Real.cosh s ^ 2 - Real.sinh s ^ 2) * y := by ring
        _ = y := by rw [Real.cosh_sq_sub_sinh_sq]; simp

@[simp]
theorem boost_apply (s : ℝ) (v : Fibre) :
    boost s v =
      (Real.cosh s * v.1 + Real.sinh s * v.2,
        Real.sinh s * v.1 + Real.cosh s * v.2) :=
  rfl

@[simp]
theorem boost_zero : boost 0 = LinearEquiv.refl ℝ Fibre := by
  ext v <;> simp

/-- Boosts form the additive one-parameter representation. -/
theorem boost_add_apply (s t : ℝ) (v : Fibre) :
    boost (s + t) v = boost s (boost t v) := by
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · simp only [boost_apply, Real.cosh_add, Real.sinh_add]
    ring
  · simp only [boost_apply, Real.cosh_add, Real.sinh_add]
    ring

/-- The inverse boost acts by the negative parameter. -/
@[simp]
theorem boost_neg_apply (s : ℝ) (v : Fibre) :
    boost (-s) (boost s v) = v := by
  rw [← boost_add_apply, neg_add_cancel, boost_zero]
  rfl

/-- Every boost preserves the split cyclic form. -/
theorem splitForm_boost (s : ℝ) (v w : Fibre) :
    splitForm (boost s v) (boost s w) = splitForm v w := by
  rcases v with ⟨x₁, x₂⟩
  rcases w with ⟨y₁, y₂⟩
  simp only [splitForm, boost_apply]
  calc
    (Real.cosh s * x₁ + Real.sinh s * x₂) *
          (Real.cosh s * y₁ + Real.sinh s * y₂) -
        (Real.sinh s * x₁ + Real.cosh s * x₂) *
          (Real.sinh s * y₁ + Real.cosh s * y₂) =
        (Real.cosh s ^ 2 - Real.sinh s ^ 2) * (x₁ * y₁ - x₂ * y₂) := by ring
    _ = x₁ * y₁ - x₂ * y₂ := by rw [Real.cosh_sq_sub_sinh_sq]; simp

/-- The constant connection one-form `-a J dφ` in its single coordinate direction. -/
def connectionForm (a : ℝ) : Fin 1 → Module.End ℝ Fibre :=
  fun _ => -a • boostGenerator

/-- Coordinate curvature of a constant connection one-form.  Derivative terms vanish, leaving
the commutator of its two coordinate components. -/
def constantConnectionCurvature (a : ℝ) (i j : Fin 1) : Module.End ℝ Fibre :=
  (connectionForm a i).comp (connectionForm a j) -
    (connectionForm a j).comp (connectionForm a i)

/-- The connection `d-aJ dφ` is flat: every curvature component is zero. -/
theorem connection_flat (a : ℝ) :
    ∀ i j, constantConnectionCurvature a i j = 0 := by
  intro i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  simp [constantConnectionCurvature]

/-- Parallel transport path from the identity to one turn of the connection. -/
noncomputable def parallelTransportPath (a : ℝ) (v : Fibre) (t : ℝ) : Fibre :=
  boost (a * t) v

/-- Scalar derivative predicate with the canonical normed-algebra module structure on `ℝ`. -/
abbrev ScalarHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ _ (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

/-- The two boost coordinates solve the parallel equation `v̇=aJv` of `d-aJ dφ`. -/
theorem parallelTransportPath_satisfies_equation (a : ℝ) (v : Fibre) (t : ℝ) :
    ScalarHasDerivAt (fun x => (parallelTransportPath a v x).1)
        (a * (parallelTransportPath a v t).2) t ∧
      ScalarHasDerivAt (fun x => (parallelTransportPath a v x).2)
        (a * (parallelTransportPath a v t).1) t := by
  have harg : ScalarHasDerivAt (fun x : ℝ => a * x) a t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul a
  have hcosh : ScalarHasDerivAt (fun x : ℝ => Real.cosh (a * x))
      (a * Real.sinh (a * t)) t := by
    simpa only [Function.comp_apply, Function.comp_def, id_eq, mul_one, mul_comm] using
      (Real.hasDerivAt_cosh (a * t)).comp t harg
  have hsinh : ScalarHasDerivAt (fun x : ℝ => Real.sinh (a * x))
      (a * Real.cosh (a * t)) t := by
    simpa only [Function.comp_apply, Function.comp_def, id_eq, mul_one, mul_comm] using
      (Real.hasDerivAt_sinh (a * t)).comp t harg
  have hfirst := (hcosh.mul_const v.1).add (hsinh.mul_const v.2)
  have hsecond := (hsinh.mul_const v.1).add (hcosh.mul_const v.2)
  constructor
  · convert hfirst using 1
    · funext x
      simp only [parallelTransportPath, boost_apply, Pi.add_apply]
    · simp only [parallelTransportPath, boost_apply]
      ring
  · convert hsecond using 1
    · funext x
      simp only [parallelTransportPath, boost_apply, Pi.add_apply]
    · simp only [parallelTransportPath, boost_apply]
      ring

/-- One full positive turn ends at the boost `g_a`. -/
theorem parallelTransportPath_one (a : ℝ) (v : Fibre) :
    parallelTransportPath a v 1 = boost a v := by
  simp [parallelTransportPath]

/-- Monodromy representation of the circle fundamental group, generated by `g_a`. -/
noncomputable def holonomyRepresentation (a : ℝ) :
    Multiplicative ℤ →* (Fibre ≃ₗ[ℝ] Fibre) :=
  zpowersHom (Fibre ≃ₗ[ℝ] Fibre) (boost a)

/-- Positive generator has holonomy `g_a`. -/
@[simp]
theorem holonomy_generator (a : ℝ) :
    holonomyRepresentation a (Multiplicative.ofAdd 1) = boost a := by
  simp [holonomyRepresentation]

/-- Global holonomy is exactly the cyclic subgroup generated by `g_a`. -/
theorem holonomy_range_eq_zpowers (a : ℝ) :
    Set.range (holonomyRepresentation a) = Subgroup.zpowers (boost a) := by
  change ((holonomyRepresentation a).range : Set (Fibre ≃ₗ[ℝ] Fibre)) = _
  rw [holonomyRepresentation, Subgroup.range_zpowersHom]

/-- Initial Cartan involution `θ₀=B`. -/
def initialCartan : Module.End ℝ Fibre where
  toFun v := (v.1, -v.2)
  map_add' _ _ := by ext <;> simp [add_comm]
  map_smul' _ _ := by ext <;> simp

@[simp]
theorem initialCartan_apply (v : Fibre) : initialCartan v = (v.1, -v.2) :=
  rfl

/-- Cartan polarization `θ_u=g_u θ₀ g_u⁻¹`. -/
noncomputable def cartan (u : ℝ) : Module.End ℝ Fibre :=
  (boost u).toLinearMap.comp
    (initialCartan.comp (boost (-u)).toLinearMap)

@[simp]
theorem cartan_apply (u : ℝ) (v : Fibre) :
    cartan u v = boost u (initialCartan (boost (-u) v)) :=
  rfl

/-- Explicit matrix of the Cartan involution. -/
theorem cartan_apply_formula (u : ℝ) (v : Fibre) :
    cartan u v =
      (Real.cosh (2 * u) * v.1 - Real.sinh (2 * u) * v.2,
        Real.sinh (2 * u) * v.1 - Real.cosh (2 * u) * v.2) := by
  rcases v with ⟨x, y⟩
  simp only [cartan_apply, boost_apply, initialCartan_apply, Real.cosh_neg,
    Real.sinh_neg, neg_mul]
  rw [Real.cosh_two_mul, Real.sinh_two_mul]
  apply Prod.ext
  · dsimp
    ring
  · dsimp
    ring

/-- Every `θ_u` is an involution. -/
theorem cartan_sq (u : ℝ) : (cartan u).comp (cartan u) = 1 := by
  apply LinearMap.ext
  intro v
  change cartan u (cartan u v) = v
  rcases v with ⟨x, y⟩
  rw [cartan_apply_formula, cartan_apply_formula]
  apply Prod.ext
  · dsimp
    calc
      Real.cosh (2 * u) *
            (Real.cosh (2 * u) * x - Real.sinh (2 * u) * y) -
          Real.sinh (2 * u) *
            (Real.sinh (2 * u) * x - Real.cosh (2 * u) * y) =
          (Real.cosh (2 * u) ^ 2 - Real.sinh (2 * u) ^ 2) * x := by ring
      _ = x := by rw [Real.cosh_sq_sub_sinh_sq]; simp
  · dsimp
    calc
      Real.sinh (2 * u) *
            (Real.cosh (2 * u) * x - Real.sinh (2 * u) * y) -
          Real.cosh (2 * u) *
            (Real.sinh (2 * u) * x - Real.cosh (2 * u) * y) =
          (Real.cosh (2 * u) ^ 2 - Real.sinh (2 * u) ^ 2) * y := by ring
      _ = y := by rw [Real.cosh_sq_sub_sinh_sq]; simp

/-- Conjugating a polarization by parallel transport. -/
noncomputable def transportCartan (a : ℝ) (T : Module.End ℝ Fibre) :
    Module.End ℝ Fibre :=
  (boost a).toLinearMap.comp (T.comp (boost (-a)).toLinearMap)

/-- Parallel transport translates the Cartan-polarization parameter. -/
theorem transport_cartan (a u : ℝ) :
    transportCartan a (cartan u) = cartan (u + a) := by
  apply LinearMap.ext
  intro v
  change boost a (boost u (initialCartan (boost (-u) (boost (-a) v)))) =
    boost (u + a) (initialCartan (boost (-(u + a)) v))
  rw [← boost_add_apply a u]
  rw [← boost_add_apply (-u) (-a)]
  rw [add_comm a u]
  have hneg : -u + -a = -(u + a) := by ring
  rw [hneg]

/-- First standard basis vector. -/
def e₁ : Fibre := (1, 0)

/-- A Cartan polarization records `sinh(2u)` on `e₁`. -/
theorem cartan_e₁_second (u : ℝ) : (cartan u e₁).2 = Real.sinh (2 * u) := by
  simp only [cartan_apply, e₁, boost_apply, initialCartan_apply, mul_one, mul_zero,
    add_zero, Real.cosh_neg, Real.sinh_neg]
  rw [Real.sinh_two_mul]
  ring

/-- The polarization line is faithfully parametrized: `u ↦ θ_u` is injective. -/
theorem cartan_injective : Function.Injective cartan := by
  intro u v huv
  have h := congrArg (fun T : Module.End ℝ Fibre => (T e₁).2) huv
  rw [cartan_e₁_second, cartan_e₁_second] at h
  have htwo : 2 * u = 2 * v := Real.sinh_injective h
  linarith

/-- A parallel positive Cartan polarization exists exactly for trivial boost monodromy. -/
theorem exists_parallel_cartan_iff (a : ℝ) :
    (∃ u, transportCartan a (cartan u) = cartan u) ↔ a = 0 := by
  constructor
  · rintro ⟨u, hu⟩
    rw [transport_cartan] at hu
    have := cartan_injective hu
    linarith
  · rintro rfl
    exact ⟨0, by simp [transportCartan]⟩

/-- Positive metric operator `Bθ_u` in the standard Euclidean chart. -/
noncomputable def polarMetricOperator (u : ℝ) : Module.End ℝ Fibre :=
  initialCartan.comp (cartan u)

/-- Explicit matrix of `Bθ_u`. -/
theorem polarMetricOperator_apply (u : ℝ) (v : Fibre) :
    polarMetricOperator u v =
      (Real.cosh (2 * u) * v.1 - Real.sinh (2 * u) * v.2,
        -Real.sinh (2 * u) * v.1 + Real.cosh (2 * u) * v.2) := by
  change initialCartan (cartan u v) = _
  rw [cartan_apply_formula]
  rcases v with ⟨x, y⟩
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- Polarized bilinear metric `G_u(v,w)=B(v,θ_u w)`. -/
noncomputable def polarMetric (u : ℝ) (v w : Fibre) : ℝ :=
  splitForm v (cartan u w)

/-- The polarized metric is the Euclidean pairing with `Bθ_u`. -/
theorem polarMetric_eq_euclidean (u : ℝ) (v w : Fibre) :
    polarMetric u v w = euclideanPairing v (polarMetricOperator u w) := by
  simp only [polarMetric, splitForm, euclideanPairing, polarMetricOperator,
    LinearMap.comp_apply, initialCartan_apply]
  ring

/-- Exact positive sum-of-squares normal form for the polarized metric. -/
theorem polarMetric_self (u : ℝ) (v : Fibre) :
    polarMetric u v v =
      (Real.exp (-2 * u) * (v.1 + v.2) ^ 2 +
        Real.exp (2 * u) * (v.1 - v.2) ^ 2) / 2 := by
  rw [polarMetric_eq_euclidean, polarMetricOperator_apply]
  simp only [euclideanPairing]
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

/-- Every Cartan polarization produces a positive-definite metric. -/
theorem polarMetric_pos (u : ℝ) (v : Fibre) (hv : v ≠ 0) :
    0 < polarMetric u v v := by
  rw [polarMetric_self]
  have hcoordinates : v.1 + v.2 ≠ 0 ∨ v.1 - v.2 ≠ 0 := by
    contrapose! hv
    apply Prod.ext <;> dsimp
    · linarith
    · linarith
  rcases hcoordinates with hplus | hminus
  · have hterm : 0 < Real.exp (-2 * u) * (v.1 + v.2) ^ 2 := by positivity
    have hother : 0 ≤ Real.exp (2 * u) * (v.1 - v.2) ^ 2 := by positivity
    positivity
  · have hterm : 0 < Real.exp (2 * u) * (v.1 - v.2) ^ 2 := by positivity
    have hother : 0 ≤ Real.exp (-2 * u) * (v.1 + v.2) ^ 2 := by positivity
    positivity

/-- Expanding and contracting eigenlines of the polarized metric operator. -/
def ePlus : Fibre := (1, -1)

def eMinus : Fibre := (1, 1)

theorem polarMetricOperator_ePlus (u : ℝ) :
    polarMetricOperator u ePlus = Real.exp (2 * u) • ePlus := by
  rw [polarMetricOperator_apply]
  apply Prod.ext
  · simp [ePlus, Prod.smul_mk, Real.cosh_add_sinh]
  · simp only [ePlus, Prod.smul_mk, smul_eq_mul, mul_neg, mul_one]
    rw [show -Real.sinh (2 * u) + -Real.cosh (2 * u) =
      -(Real.cosh (2 * u) + Real.sinh (2 * u)) by ring, Real.cosh_add_sinh]

theorem polarMetricOperator_eMinus (u : ℝ) :
    polarMetricOperator u eMinus = Real.exp (-2 * u) • eMinus := by
  rw [polarMetricOperator_apply]
  apply Prod.ext
  · simp [eMinus, Prod.smul_mk, Real.cosh_sub_sinh]
  · simp only [eMinus, Prod.smul_mk, smul_eq_mul, mul_one]
    rw [show -Real.sinh (2 * u) + Real.cosh (2 * u) =
      Real.cosh (2 * u) - Real.sinh (2 * u) by ring, Real.cosh_sub_sinh]
    congr 1
    ring

/-- Spectral condition number from the two proved positive eigenvalues. -/
noncomputable def polarConditionNumber (u : ℝ) : ℝ :=
  max (Real.exp (2 * u)) (Real.exp (-2 * u)) /
    min (Real.exp (2 * u)) (Real.exp (-2 * u))

/-- Exact exponential conditioning law. -/
theorem polarConditionNumber_eq (u : ℝ) :
    polarConditionNumber u = Real.exp (4 * |u|) := by
  rcases le_total 0 u with hu | hu
  · have horder : Real.exp (-2 * u) ≤ Real.exp (2 * u) := by
      apply Real.exp_monotone
      linarith
    rw [polarConditionNumber, max_eq_left horder, min_eq_right horder, ← Real.exp_sub]
    rw [abs_of_nonneg hu]
    congr 1
    ring
  · have horder : Real.exp (2 * u) ≤ Real.exp (-2 * u) := by
      apply Real.exp_monotone
      linarith
    rw [polarConditionNumber, max_eq_right horder, min_eq_left horder, ← Real.exp_sub]
    rw [abs_of_nonpos hu]
    congr 1
    ring

/-- Observed polarization circle for nonzero monodromy parameter. -/
abbrev PolarQuotient (a : ℝ) := AddCircle |a|

/-- One monodromy step vanishes in the observed quotient. -/
theorem monodromy_period_eq_zero (a : ℝ) (ha : a ≠ 0) :
    (a : PolarQuotient a) = 0 := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · rw [abs_of_neg hneg]
    have hperiod : ((-a : ℝ) : AddCircle (-a)) = 0 := AddCircle.coe_period (-a)
    calc
      (a : AddCircle (-a)) = -((-a : ℝ) : AddCircle (-a)) := by
        simpa only [neg_neg] using
          (AddCircle.coe_neg (p := -a) (x := -a))
      _ = 0 := by rw [hperiod, neg_zero]
  · rw [abs_of_pos hpos]
    exact AddCircle.coe_period a

/-- Marked lift sampled after each full observer loop. -/
def markedHistory (u₀ a : ℝ) (n : ℕ) : ℝ :=
  u₀ + (n : ℝ) * a

/-- Quotient-observed history. -/
noncomputable def observedHistory (u₀ a : ℝ) (n : ℕ) : PolarQuotient a :=
  markedHistory u₀ a n

/-- The quotient history is closed at every integer loop time. -/
theorem observedHistory_eq_initial (u₀ a : ℝ) (ha : a ≠ 0) (n : ℕ) :
    observedHistory u₀ a n = observedHistory u₀ a 0 := by
  simp only [observedHistory, markedHistory, Nat.cast_zero, zero_mul, add_zero]
  change ((u₀ + (n : ℝ) * a : ℝ) : PolarQuotient a) = (u₀ : PolarQuotient a)
  rw [AddCircle.coe_add]
  have hmul : (n : ℝ) * a = n • a := by simp [nsmul_eq_mul]
  rw [hmul, AddCircle.coe_nsmul, monodromy_period_eq_zero a ha, nsmul_zero, add_zero]

/-- For nonzero monodromy, the observed quotient is compact. -/
theorem polarQuotient_compact (a : ℝ) (ha : a ≠ 0) :
    IsCompact (Set.univ : Set (PolarQuotient a)) := by
  letI : Fact (0 < |a|) := ⟨abs_pos.mpr ha⟩
  exact isCompact_univ

/-- Despite closed observation, the marked lift escapes to infinite absolute displacement. -/
theorem markedHistory_escapes (u₀ a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => |markedHistory u₀ a n|) atTop atTop := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hlinear : Tendsto (fun n : ℕ => -(markedHistory u₀ a n)) atTop atTop := by
      have hscale : Tendsto (fun n : ℕ => (-a) * (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop (neg_pos.mpr hneg)
      have hconst : Tendsto (fun _ : ℕ => -u₀) atTop (nhds (-u₀)) :=
        tendsto_const_nhds
      convert hscale.atTop_add hconst using 1
      funext n
      simp only [markedHistory]
      ring
    have habs := tendsto_abs_atTop_atTop.comp hlinear
    convert habs using 1
    funext n
    simp only [Function.comp_apply, abs_neg]
  · have hlinear : Tendsto (markedHistory u₀ a) atTop atTop := by
      have hscale : Tendsto (fun n : ℕ => a * (n : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hpos
      have hconst : Tendsto (fun _ : ℕ => u₀) atTop (nhds u₀) :=
        tendsto_const_nhds
      convert hscale.atTop_add hconst using 1
      funext n
      simp only [markedHistory]
      ring
    exact tendsto_abs_atTop_atTop.comp hlinear

/-- Continuous marked lift `u(t)=u₀+at`. -/
def liftedPath (u₀ a t : ℝ) : ℝ :=
  u₀ + a * t

/-- Length of the marked lift over `[0,T]` in the invariant line metric. -/
noncomputable def liftedLength (a T : ℝ) : ℝ :=
  ∫ _t in (0 : ℝ)..T, |a|

/-- Quadratic local action of the marked lift over `[0,T]`. -/
noncomputable def liftedAction (a T : ℝ) : ℝ :=
  ∫ _t in (0 : ℝ)..T, a ^ 2

theorem liftedLength_eq (a T : ℝ) : liftedLength a T = |a| * T := by
  simp [liftedLength, mul_comm]

theorem liftedAction_eq (a T : ℝ) : liftedAction a T = a ^ 2 * T := by
  simp [liftedAction, mul_comm]

/-- Repeated-loop lifted lengths diverge for nonzero monodromy. -/
theorem liftedLength_diverges (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => liftedLength a n) atTop atTop := by
  simp_rw [liftedLength_eq]
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (abs_pos.mpr ha)

/-- Repeated-loop quadratic actions diverge for nonzero monodromy. -/
theorem liftedAction_diverges (a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => liftedAction a n) atTop atTop := by
  simp_rw [liftedAction_eq]
  exact tendsto_natCast_atTop_atTop.const_mul_atTop (sq_pos_of_ne_zero ha)

/-- Polar conditioning diverges along every nontrivial marked recurrent history. -/
theorem polarConditionNumber_diverges (u₀ a : ℝ) (ha : a ≠ 0) :
    Tendsto (fun n : ℕ => polarConditionNumber (markedHistory u₀ a n)) atTop atTop := by
  simp_rw [polarConditionNumber_eq]
  exact Real.tendsto_exp_atTop.comp
    ((markedHistory_escapes u₀ a ha).const_mul_atTop (by norm_num : (0 : ℝ) < 4))

/-- Closed capstone collecting the seven derived faces of the single flat Cartan field. -/
theorem flatCartan_fourFaceLaw (u₀ a : ℝ) (ha : a ≠ 0) :
    (∀ i j, constantConnectionCurvature a i j = 0) ∧
      holonomyRepresentation a (Multiplicative.ofAdd 1) = boost a ∧
      (∀ u, transportCartan a (cartan u) = cartan (u + a)) ∧
      ¬ (∃ u, transportCartan a (cartan u) = cartan u) ∧
      IsCompact (Set.univ : Set (PolarQuotient a)) ∧
      (∀ n, observedHistory u₀ a n = observedHistory u₀ a 0) ∧
      Tendsto (fun n : ℕ => |markedHistory u₀ a n|) atTop atTop ∧
      Tendsto (fun n : ℕ => liftedLength a n) atTop atTop ∧
      Tendsto (fun n : ℕ => liftedAction a n) atTop atTop ∧
      Tendsto (fun n : ℕ => polarConditionNumber (markedHistory u₀ a n)) atTop atTop := by
  refine ⟨connection_flat a, holonomy_generator a, transport_cartan a, ?_,
    polarQuotient_compact a ha, observedHistory_eq_initial u₀ a ha,
    markedHistory_escapes u₀ a ha, liftedLength_diverges a ha,
    liftedAction_diverges a ha, polarConditionNumber_diverges u₀ a ha⟩
  rw [exists_parallel_cartan_iff]
  exact ha

end HTGeometry.NomologicalHomotopyGeometry.FlatCartanHolonomy
