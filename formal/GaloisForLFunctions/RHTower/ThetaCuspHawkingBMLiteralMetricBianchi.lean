import GaloisForLFunctions.HTGeometry.ComplexMetricFieldBianchi
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCorrectedMetricSource

set_option autoImplicit false

namespace RHTower.D4BMLiteralMetricBianchi
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMMetricReconstruction D4BMActualMetricSource
open Filter Topology
open scoped ContDiff
noncomputable section

private theorem expression_smooth {α : Type*} {n : ℕ∞ω}
    (e : ScalarTwoJet.Expression α) {a : α → (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ}
    (ha : ∀ b, ContDiffAt ℝ n (a b) x) (he : e.Regular (fun b => a b x)) :
    ContDiffAt ℝ n (fun y => e.eval (fun b => a b y)) x := by
  induction e with
  | atom b => exact ha b
  | constant c => exact contDiffAt_const
  | add p q hp hq => exact (hp he.1).add (hq he.2)
  | neg p hp => exact (hp he).neg
  | mul p q hp hq => exact (hp he.1).mul (hq he.2)
  | inv p hp => exact (hp he.1).inv he.2

private theorem angular_smooth (n : ℕ∞ω) : ContDiff ℝ n angularPoint := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_apply ℝ ℝ 2
  · exact contDiff_apply ℝ ℝ 3

private theorem primitive_smooth (n : ℕ) (p : ExteriorPoint) (omega u aS aV : ℂ) (b : Primitive) :
    ContDiffAt ℝ n (D4BMFundamentalMetric.primitives omega aS aV
      (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) b) p.val := by
  let Φ := fun z => aS * D4BMFundamentalMaster.master omega z
  let Ψ := fun z => aV * D4BMFundamentalMaster.master omega z
  have hΦ : ContDiffAt ℂ (n+1) Φ (bmCoordinate p.val) :=
    contDiffAt_const.mul (D4BMFundamentalMaster.exterior_master_contDiffAt omega p (n+1))
  have hΨ : ContDiffAt ℂ (n+1) Ψ (bmCoordinate p.val) :=
    contDiffAt_const.mul (D4BMFundamentalMaster.exterior_master_contDiffAt omega p (n+1))
  have hΦn := hΦ.of_le (show (n : ℕ∞ω) ≤ n+1 by exact_mod_cast Nat.le_succ n)
  have hΨn := hΨ.of_le (show (n : ℕ∞ω) ≤ n+1 by exact_mod_cast Nat.le_succ n)
  have hc (k : Fin 4) : ContDiffAt ℝ n (fun x : Fin 4 → ℝ => (x k : ℂ)) p.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ k)).contDiffAt
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hz : ContDiffAt ℝ n bmCoordinate p.val := contDiffAt_const.sub (((hc 1).inv hr).pow 2)
  have hS := D4BMLiteralCusp.scalar_contDiffAt u n (angularPoint p.val) p.property.2
  have hV := D4BMLiteralCusp.vector_contDiffAt u n (angularPoint p.val) p.property.2
  have hM := D4BMFundamentalMetric.horizonScale_contDiffAt (angularPoint p.val) p.property.2 n
  cases b with
  | radius => exact hc 1
  | scalarValue => exact (hΦn.restrict_scalars ℝ).comp p.val hz
  | scalarZDerivative => exact ((hΦ.derivWithin (m := n) (by norm_cast)).restrict_scalars ℝ).comp p.val hz
  | vectorValue => exact (hΨn.restrict_scalars ℝ).comp p.val hz
  | vectorZDerivative => exact ((hΨ.derivWithin (m := n) (by norm_cast)).restrict_scalars ℝ).comp p.val hz
  | timeMode =>
    exact Complex.contDiff_exp.contDiffAt.comp p.val (contDiffAt_const.mul (hc 0))
  | scalarHarmonic => exact hS.comp p.val (angular_smooth n).contDiffAt
  | vectorHarmonic i => exact (hV i).comp p.val (angular_smooth n).contDiffAt
  | horizon00 => exact hM.comp p.val (angular_smooth n).contDiffAt
  | horizon01 => exact contDiffAt_const
  | horizon11 => exact hM.comp p.val (angular_smooth n).contDiffAt

/-- The full literal infinite-series reconstruction supplies every finite spatial smoothness order. -/
theorem literal_contDiffAt (n : ℕ) (p : ExteriorPoint) (omega u aS aV : ℂ) (i j : Fin 4) :
    ContDiffAt ℝ n (fun x => D4BMLiteralCusp.perturbation omega u aS aV x i j) p.val := by
  let a := D4BMFundamentalMetric.primitives omega aS aV (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u)
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    have h : (p.val 1)^(2 : ℕ)-1 ≠ 0 := by nlinarith [p.property.1]
    exact_mod_cast h
  have he := expression_smooth (covariantMetricExpression omega (D4BMLiteralCusp.scalarQ u) i j)
    (primitive_smooth n p omega u aS aV)
    (covariantMetricExpression_regular omega (D4BMLiteralCusp.scalarQ u)
      (fun b => a b p.val) hr hf i j)
  have hfun : (fun x => (covariantMetricExpression omega (D4BMLiteralCusp.scalarQ u) i j).eval (fun b => a b x)) =
      fun x => D4BMLiteralCusp.perturbation omega u aS aV x i j := by
    funext x
    exact covariantMetricExpression_eval omega (D4BMLiteralCusp.scalarQ u) (fun b => a b x) i j
  rwa [hfun] at he

private theorem literal_symm (omega u aS aV : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    D4BMLiteralCusp.perturbation omega u aS aV x i j = D4BMLiteralCusp.perturbation omega u aS aV x j i := by
  let a := fun b => D4BMFundamentalMetric.primitives omega aS aV
    (D4BMLiteralCusp.scalar u) (D4BMLiteralCusp.vector u) b x
  have hs := congrArg (fun e : ScalarTwoJet.Expression Primitive => e.eval a)
    (covariantMetricExpression_symm omega (D4BMLiteralCusp.scalarQ u) i j)
  rw [covariantMetricExpression_eval, covariantMetricExpression_eval] at hs
  exact hs

private theorem metric_symm (omega u aS aV ε : ℂ) (x : Fin 4 → ℝ) (i j : Fin 4) :
    perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x i j =
      perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε x j i := by
  have hb : metric (x 1) (x 3) i j = metric (x 1) (x 3) j i := by
    by_cases hij : i = j
    · subst j; rfl
    · simp [metric, hij, Ne.symm hij]
  change metric (x 1) (x 3) i j + ε * D4BMLiteralCusp.perturbation omega u aS aV x i j = _
  rw [hb, literal_symm omega u aS aV x i j]
  rfl

/-- The metric Bianchi development uses exactly the source's original complete field jet. -/
theorem twoJet_eq_sourceJet (g : MetricField) (x : Fin 4 → ℝ) :
    ComplexMetricField.twoJet g x = ofMetricField g x := rfl

/-- The literal perturbed metric obeys full differential Bianchi throughout a genuine
amplitude neighborhood of the actual vacuum, with no regularity or symmetry premises. -/
theorem literal_bianchi_near_zero (p : ExteriorPoint) (omega u aS aV : ℂ) :
    ∀ᶠ ε : ℂ in 𝓝 0, ∀ k i j a b : Fin 4,
      ComplexCoordinateConnection.tensorPartial
        (ComplexMetricField.connection (perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε))
        p.val k i j a b +
      ComplexCoordinateConnection.tensorPartial
        (ComplexMetricField.connection (perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε))
        p.val i j k a b +
      ComplexCoordinateConnection.tensorPartial
        (ComplexMetricField.connection (perturbedMetric (D4BMLiteralCusp.perturbation omega u aS aV) ε))
        p.val j k i a b = 0 := by
  let h := D4BMLiteralCusp.perturbation omega u aS aV
  have hd : Continuous (fun ε : ℂ => (perturbedMetric h ε p.val).det) := by
    simp only [Matrix.det_apply', perturbedMetric, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    fun_prop
  have h0 : (perturbedMetric h 0 p.val).det ≠ 0 := by
    simpa [perturbedMetric] using exterior_metric_det_ne_zero p
  filter_upwards [hd.continuousAt.eventually_ne h0] with ε hε
  intro k i j a b
  exact ComplexMetricField.bianchi (perturbedMetric h ε) p.val
    (fun i j => (exterior_metric_contDiffAt p i j).add
      (contDiffAt_const.mul (literal_contDiffAt 3 p omega u aS aV i j)))
    hε (metric_symm omega u aS aV ε) k i j a b

end
end RHTower.D4BMLiteralMetricBianchi
