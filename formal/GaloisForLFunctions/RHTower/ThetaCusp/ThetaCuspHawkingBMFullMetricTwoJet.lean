import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMKIVectorChiralReconstruction
import GaloisForLFunctions.HTGeometry.ScalarTwoJetCalculus
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexVariations
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Full covariant Birmingham--Mokhtari metric two-jet

The scalar representative has `f_a = H_T = 0`; the vector representative has `H_T = 0`.
KI Eqs. (2.4), (2.7), (2.21), (5.9)--(5.10) fix its covariant metric components. Every
reconstruction operation is lifted to complete coordinate two-jets, retaining the derivatives of
radial factors, time modes, angular harmonics and the horizon metric. Source conventions:
https://arxiv.org/pdf/hep-th/0305147 .

This constructs a bulk metric representative and its actual coordinate derivatives. The physical
nonlinear gauge constraints, response domain and final left-QNM projection remain separate.
-/

namespace RHTower.D4BMMetricReconstruction

open GaloisForLFunctions.HTGeometry
noncomputable section

/-- Primitive scalar fields appearing in the full scalar/vector covariant reconstruction. -/
inductive Primitive where
  | radius
  | scalarValue
  | scalarZDerivative
  | vectorValue
  | vectorZDerivative
  | timeMode
  | scalarHarmonic
  | vectorHarmonic (i : Fin 2)
  | horizon00
  | horizon01
  | horizon11

private abbrev Expr := ScalarTwoJet.Expression Primitive
private def atom (i : Primitive) : Expr := .atom i
private def c (z : ℂ) : Expr := .constant z
private def scale (z : ℂ) (p : Expr) : Expr := (c z).mul p
private def difference (p q : Expr) : Expr := p.add q.neg
private def r : Expr := atom .radius
private def rho : Expr := r.inv
private def f : Expr := difference (r.mul r) (c 1)
private def zInv : Expr := (r.mul r).mul f.inv

private def scalarX (omega kSq : ℂ) : Expr :=
  ((scale (omega ^ (2 : ℕ)) (rho.mul (zInv.mul (atom .scalarValue)))).add
    (scale (-kSq) (rho.mul (atom .scalarValue)))).add
    (scale 2 (rho.mul ((difference (scale 2 (rho.mul rho)) (c 1)).mul
      (atom .scalarZDerivative))))

private def scalarY (omega : ℂ) : Expr :=
  (scale (-(omega ^ (2 : ℕ))) (rho.mul (zInv.mul (atom .scalarValue)))).add
    (scale (-2) (rho.mul (atom .scalarZDerivative)))

private def scalarZ (omega : ℂ) : Expr :=
  scale (Complex.I * omega) (difference (atom .scalarValue)
    (scale 2 ((difference (c 1) (rho.mul rho)).mul (atom .scalarZDerivative))))

private def vectorFt : Expr :=
  (rho.mul (atom .vectorValue)).add
    (scale 2 ((rho.mul (rho.mul rho)).mul (atom .vectorZDerivative)))

private def vectorFr (omega : ℂ) : Expr := scale (Complex.I * omega) (atom .vectorValue)

/-- Full symmetric covariant metric expression, with both scalar and vector sectors retained. -/
def covariantMetricExpression (omega kSq : ℂ) : Matrix (Fin 4) (Fin 4) Expr :=
  let angular (p : Expr) := (p.mul (atom .scalarHarmonic)).mul (atom .timeMode)
  let scalarTT := scale (1 / 2) (difference (scalarX omega kSq) (scalarY omega))
  let scalarTrace := scale (-(1 / 4)) ((scalarX omega kSq).add (scalarY omega))
  let tt := angular (f.mul scalarTT).neg
  let tr := angular (f.inv.mul (scalarZ omega))
  let rr := angular (f.inv.mul scalarTT.neg)
  let tv (i : Fin 2) :=
    (((r.mul (f.mul vectorFt)).neg.mul (atom (.vectorHarmonic i))).mul (atom .timeMode))
  let rv (i : Fin 2) :=
    (((r.mul (f.inv.mul (vectorFr omega))).mul (atom (.vectorHarmonic i))).mul (atom .timeMode))
  let hab (a : Primitive) := angular (scale 2 ((r.mul r).mul (scalarTrace.mul (atom a))))
  !![tt, tr, tv 0, tv 1;
     tr, rr, rv 0, rv 1;
     tv 0, rv 0, hab .horizon00, hab .horizon01;
     tv 1, rv 1, hab .horizon01, hab .horizon11]

/-- Covariant index lowering and harmonic attachment for the already constructed KI orbits. -/
def covariantMetricFromOrbits (a : Primitive → ℂ)
    (s : D4KIScalarGaugeInvariantOrbit) (v : D4KIVectorGaugeInvariantOrbit) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let blackening := a .radius ^ (2 : ℕ) - 1
  let angular (p : ℂ) := p * a .scalarHarmonic * a .timeMode
  let tt := angular (-blackening * s.FttMixed)
  let tr := angular (blackening⁻¹ * s.FrtMixed)
  let rr := angular (blackening⁻¹ * s.FrrMixed)
  let tv (i : Fin 2) := -a .radius * blackening * v.FtContravariant *
    a (.vectorHarmonic i) * a .timeMode
  let rv (i : Fin 2) := a .radius * blackening⁻¹ * v.FrContravariant *
    a (.vectorHarmonic i) * a .timeMode
  let hab (i : Primitive) := angular (2 * a .radius ^ (2 : ℕ) * s.angularTrace * a i)
  !![tt, tr, tv 0, tv 1;
     tr, rr, rv 0, rv 1;
     tv 0, rv 0, hab .horizon00, hab .horizon01;
     tv 1, rv 1, hab .horizon01, hab .horizon11]

/-- Literal covariant reconstruction from primitive values. The old orbit constructors do not
inspect their `second` input; metric derivatives are computed subsequently from the full fields. -/
def covariantMetric (omega kSq : ℂ) (a : Primitive → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  covariantMetricFromOrbits a
    (d4KIScalarGaugeInvariantOrbitOfBMMaster (a .radius)⁻¹
      (a .radius ^ (2 : ℕ) * (a .radius ^ (2 : ℕ) - 1)⁻¹) omega kSq
      ⟨a .scalarValue, a .scalarZDerivative, 0⟩)
    (d4KIVectorGaugeInvariantOrbitOfBMMaster (a .radius)⁻¹ omega
      ⟨a .vectorValue, a .vectorZDerivative, 0⟩)

/-- The complete expression agrees with the covariant form of the corpus KI reconstruction. -/
theorem covariantMetricExpression_eval (omega kSq : ℂ) (a : Primitive → ℂ) (i j : Fin 4) :
    ((covariantMetricExpression omega kSq) i j).eval a = covariantMetric omega kSq a i j := by
  fin_cases i <;> fin_cases j <;>
    simp [covariantMetricExpression, covariantMetric, covariantMetricFromOrbits,
      d4KIScalarGaugeInvariantOrbitOfBMMaster, d4KIScalarMasslessTopologicalX,
      d4KIScalarMasslessTopologicalY, d4KIScalarMasslessTopologicalZtilde,
      d4KIVectorGaugeInvariantOrbitOfBMMaster, scalarX, scalarY, scalarZ, vectorFt, vectorFr,
      rho, zInv, r, f, difference, scale, c, atom, ScalarTwoJet.Expression.eval]
  all_goals ring_nf
  all_goals simp

/-- The full covariant expression is symmetric before evaluating any source data. -/
theorem covariantMetricExpression_symm (omega kSq : ℂ) (i j : Fin 4) :
    covariantMetricExpression omega kSq i j = covariantMetricExpression omega kSq j i := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Only radius and blackening nondegeneracy are required by the rational reconstruction. -/
theorem covariantMetricExpression_regular (omega kSq : ℂ) (a : Primitive → ℂ)
    (hr : a .radius ≠ 0) (hf : a .radius ^ (2 : ℕ) - 1 ≠ 0) (i j : Fin 4) :
    (covariantMetricExpression omega kSq i j).Regular a := by
  have hf' : a .radius * a .radius + -1 ≠ 0 := by simpa [pow_two, sub_eq_add_neg] using hf
  fin_cases i <;> fin_cases j <;>
    simp [covariantMetricExpression, scalarX, scalarY, scalarZ, vectorFt, vectorFr,
      rho, zInv, r, f, difference, scale, c, atom, ScalarTwoJet.Expression.Regular,
      ScalarTwoJet.Expression.eval, hr, hf']

private def assemble (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ where
  metric i j := (J i j).value
  first k i j := (J i j).first k
  second k l i j := (J i j).second k l

/-- Complete reconstructed metric two-jet from all primitive scalar two-jets. -/
def metricJet (omega kSq : ℂ) (a : Primitive → ScalarTwoJet (Fin 4) ℂ) :
    CoordinateMetricTwoJet 4 ℂ :=
  assemble (fun i j => (covariantMetricExpression omega kSq i j).evalJet a)

/-- Complete actual metric two-jet of a complex metric field in real coordinates. -/
def ofMetricField (g : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ) (x : Fin 4 → ℝ) :
    CoordinateMetricTwoJet 4 ℂ :=
  assemble (fun i j => ScalarTwoJet.ofField (fun y => g y i j) x)

/-- The finite metric jet has exactly the independently reconstructed covariant metric value. -/
theorem metricJet_value (omega kSq : ℂ) (a : Primitive → ScalarTwoJet (Fin 4) ℂ) (i j : Fin 4) :
    (metricJet omega kSq a).metric i j = covariantMetric omega kSq (fun p => (a p).value) i j := by
  change ((covariantMetricExpression omega kSq i j).evalJet a).value = _
  rw [ScalarTwoJet.Expression.evalJet_value, covariantMetricExpression_eval]

/-- Every reconstructed coordinate derivative agrees with the actual complete metric field jet. -/
theorem metricJet_correct (omega kSq : ℂ) {a : Primitive → (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (ha : ∀ p, ContDiffAt ℝ 2 (a p) x)
    (hr : a .radius x ≠ 0) (hf : a .radius x ^ (2 : ℕ) - 1 ≠ 0) :
    metricJet omega kSq (fun p => ScalarTwoJet.ofField (a p) x) =
      ofMetricField (fun y => covariantMetric omega kSq (fun p => a p y)) x := by
  change assemble _ = assemble _
  congr 1
  funext i j
  have h := ((covariantMetricExpression omega kSq i j).eval_jet_correct ha
    (covariantMetricExpression_regular omega kSq (fun p => a p x) hr hf i j)).2
  have heq : (fun y => (covariantMetricExpression omega kSq i j).eval (fun p => a p y)) =
      fun y => covariantMetric omega kSq (fun p => a p y) i j := by
    funext y
    exact covariantMetricExpression_eval omega kSq (fun p => a p y) i j
  rw [heq] at h
  exact h.symm

/-- Complete scalar, vector and symmetric metric data on the horizon chart. -/
structure HorizonFields where
  scalar : (Fin 2 → ℝ) → ℂ
  vector : Fin 2 → (Fin 2 → ℝ) → ℂ
  metric00 : (Fin 2 → ℝ) → ℂ
  metric01 : (Fin 2 → ℝ) → ℂ
  metric11 : (Fin 2 → ℝ) → ℂ

/-- Horizon coordinates in the static chart `(t,r,x,y)`. -/
def angularPoint (x : Fin 4 → ℝ) : Fin 2 → ℝ := ![x 2, x 3]

/-- Literal Birmingham--Mokhtari radial coordinate. -/
def bmCoordinate (x : Fin 4 → ℝ) : ℂ := 1 - (x 1 : ℂ)⁻¹ ^ (2 : ℕ)

/-- Actual separated master, time, harmonic and horizon-metric fields underlying the recipe. -/
def primitiveFields (omega : ℂ) (Φ Ψ : ℂ → ℂ) (H : HorizonFields) :
    Primitive → (Fin 4 → ℝ) → ℂ
  | .radius, x => x 1
  | .scalarValue, x => Φ (bmCoordinate x)
  | .scalarZDerivative, x => deriv Φ (bmCoordinate x)
  | .vectorValue, x => Ψ (bmCoordinate x)
  | .vectorZDerivative, x => deriv Ψ (bmCoordinate x)
  | .timeMode, x => Complex.exp (-Complex.I * omega * (x 0 : ℂ))
  | .scalarHarmonic, x => H.scalar (angularPoint x)
  | .vectorHarmonic i, x => H.vector i (angularPoint x)
  | .horizon00, x => H.metric00 (angularPoint x)
  | .horizon01, x => H.metric01 (angularPoint x)
  | .horizon11, x => H.metric11 (angularPoint x)

private theorem angularPoint_contDiff : ContDiff ℝ n angularPoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ n (fun x : Fin 4 → ℝ => x 2)
    exact contDiff_apply ℝ ℝ 2
  · change ContDiff ℝ n (fun x : Fin 4 → ℝ => x 3)
    exact contDiff_apply ℝ ℝ 3

private theorem realCoordinate_contDiff (k : Fin 4) :
    ContDiff ℝ n (fun x : Fin 4 → ℝ => (x k : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)

private theorem bmCoordinate_contDiffAt (x : Fin 4 → ℝ) (hr : x 1 ≠ 0) :
    ContDiffAt ℝ 2 bmCoordinate x := by
  have hc : ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => (y 1 : ℂ)) x :=
    (realCoordinate_contDiff 1).contDiffAt
  have hr' : (x 1 : ℂ) ≠ 0 := by exact_mod_cast hr
  exact contDiffAt_const.sub ((hc.inv hr').pow 2)

/-- The actual reconstruction fields need only three master derivatives and two horizon derivatives. -/
theorem primitiveFields_contDiffAt (omega : ℂ) {Φ Ψ : ℂ → ℂ} {H : HorizonFields}
    {x : Fin 4 → ℝ} (hr : x 1 ≠ 0)
    (hΦ : ContDiffAt ℂ 3 Φ (bmCoordinate x)) (hΨ : ContDiffAt ℂ 3 Ψ (bmCoordinate x))
    (hS : ContDiffAt ℝ 2 H.scalar (angularPoint x))
    (hV : ∀ i, ContDiffAt ℝ 2 (H.vector i) (angularPoint x))
    (h00 : ContDiffAt ℝ 2 H.metric00 (angularPoint x))
    (h01 : ContDiffAt ℝ 2 H.metric01 (angularPoint x))
    (h11 : ContDiffAt ℝ 2 H.metric11 (angularPoint x)) (p : Primitive) :
    ContDiffAt ℝ 2 (primitiveFields omega Φ Ψ H p) x := by
  have hz := bmCoordinate_contDiffAt x hr
  have hΦ₂ : ContDiffAt ℂ 2 Φ (bmCoordinate x) := hΦ.of_le (by norm_num)
  have hΨ₂ : ContDiffAt ℂ 2 Ψ (bmCoordinate x) := hΨ.of_le (by norm_num)
  cases p with
  | radius => exact (realCoordinate_contDiff 1).contDiffAt
  | scalarValue => exact (hΦ₂.restrict_scalars ℝ).comp x hz
  | scalarZDerivative => exact ((hΦ.derivWithin (m := 2) (by norm_num)).restrict_scalars ℝ).comp x hz
  | vectorValue => exact (hΨ₂.restrict_scalars ℝ).comp x hz
  | vectorZDerivative => exact ((hΨ.derivWithin (m := 2) (by norm_num)).restrict_scalars ℝ).comp x hz
  | timeMode =>
    change ContDiffAt ℝ 2 (fun y : Fin 4 → ℝ => Complex.exp (-Complex.I * omega * (y 0 : ℂ))) x
    exact Complex.contDiff_exp.contDiffAt.comp x
      (contDiffAt_const.mul (realCoordinate_contDiff 0).contDiffAt)
  | scalarHarmonic => exact hS.comp x angularPoint_contDiff.contDiffAt
  | vectorHarmonic i => exact (hV i).comp x angularPoint_contDiff.contDiffAt
  | horizon00 => exact h00.comp x angularPoint_contDiff.contDiffAt
  | horizon01 => exact h01.comp x angularPoint_contDiff.contDiffAt
  | horizon11 => exact h11.comp x angularPoint_contDiff.contDiffAt

/-- The master derivative's second spatial jet explicitly retains the third master derivative. -/
theorem scalarZDerivative_jet (omega : ℂ) {Φ Ψ : ℂ → ℂ} (H : HorizonFields)
    {x : Fin 4 → ℝ} (hr : x 1 ≠ 0) (hΦ : ContDiffAt ℂ 3 Φ (bmCoordinate x)) :
    ScalarTwoJet.ofField (primitiveFields omega Φ Ψ H .scalarZDerivative) x =
      ScalarTwoJet.compose (ScalarTwoJet.ofField bmCoordinate x)
        (deriv Φ (bmCoordinate x)) (deriv (deriv Φ) (bmCoordinate x))
        (deriv (deriv (deriv Φ)) (bmCoordinate x)) :=
  ScalarTwoJet.ofField_comp (hΦ.derivWithin (m := 2) (by norm_num)) (bmCoordinate_contDiffAt x hr)

/-- Full metric two-jet correctness for actual separated master and horizon fields. -/
theorem metricJet_of_masters (omega kSq : ℂ) {Φ Ψ : ℂ → ℂ} {H : HorizonFields}
    {x : Fin 4 → ℝ} (hr : x 1 ≠ 0) (hf : (x 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0)
    (hΦ : ContDiffAt ℂ 3 Φ (bmCoordinate x)) (hΨ : ContDiffAt ℂ 3 Ψ (bmCoordinate x))
    (hS : ContDiffAt ℝ 2 H.scalar (angularPoint x))
    (hV : ∀ i, ContDiffAt ℝ 2 (H.vector i) (angularPoint x))
    (h00 : ContDiffAt ℝ 2 H.metric00 (angularPoint x))
    (h01 : ContDiffAt ℝ 2 H.metric01 (angularPoint x))
    (h11 : ContDiffAt ℝ 2 H.metric11 (angularPoint x)) :
    metricJet omega kSq (fun p => ScalarTwoJet.ofField (primitiveFields omega Φ Ψ H p) x) =
      ofMetricField (fun y => covariantMetric omega kSq (fun p => primitiveFields omega Φ Ψ H p y)) x := by
  apply metricJet_correct
    (ha := primitiveFields_contDiffAt omega hr hΦ hΨ hS hV h00 h01 h11)
  · change (x 1 : ℂ) ≠ 0
    exact_mod_cast hr
  · exact hf

end
end RHTower.D4BMMetricReconstruction
