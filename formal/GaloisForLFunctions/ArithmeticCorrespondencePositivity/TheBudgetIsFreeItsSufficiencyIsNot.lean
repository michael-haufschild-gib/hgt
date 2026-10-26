import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheTheoremOfTheSquareIsFree
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.KernelCountsAreBlindToComplexQuartets
import GaloisForLFunctions.ArithmeticCorrelationGeometry.TheGoldenDatumHasNoFixedBudget

/-!
# The budget is free; its sufficiency is not

Weil's inequality `|N_m − q^m − 1| ≤ 2g q^{m/2}` has a constant, the budget `2g`, which does not
grow with `m`. Its origin is the defect of the diagonal, `δ(Δ, Δ) = 2g`, and its independence of `m`
is the similitude law of Frobenius graphs. Both exist on every scaling datum, hence over `ℤ`.

* **The similitude law** (`normGraph_degree_heckeGraph`, `normGraph_degree_act`). The degree of the
  normalized graph of a Hecke graph `T_g x = e^{s(g)/2} ψ_g x` is `e^{s(g)}` times that of `x`; for
  the normalized correspondence `ψ_g` it is unchanged. The budget of a cycle,
  `δ(x, x) = 2 deg N(x)`, is carried unchanged along its orbit.
* **Sufficiency is positivity of two graphs** (`hasseWeilAt_iff_normGraph_degree_nonneg`). Weil's
  inequality `|c_x(g)| ≤ c_x(0)` at a scale is `deg N(x + ψ_g x) ≥ 0` and `deg N(x − ψ_g x) ≥ 0`;
  these degrees are `c_x(0) ± c_x(g)`. In genus one these are `deg(1 ± F)`.
* **Curves** (`CurveDatum.diagonal_defect`). The budget of the diagonal of a curve datum is `2g`, for
  pure and fake data alike. It is sufficient at every level iff the power sums are bounded iff the
  datum is unitary (`budget_sufficient_iff_unitary`, from ACG). The golden datum and the complex fake
  have budgets `2` and `4` and no fixed bound on their power sums
  (`goldenDatum_budget_insufficient`, `complexFake_budget_insufficient`).
* **`ζ`** (`riemannHypothesis_iff_spline_graphs_one_add_sub_nonneg`). RH is the sufficiency of the
  budget of the cubic spline at every scale: the normalized graphs of `1 ± ψ_t` applied to it have
  nonnegative degree.

So over `ℤ` the budget exists, is computable for every test, and is fixed along every Hecke orbit.
What `ℤ` lacks is the proof that it suffices, which is the positivity of the graphs of `1 ± T`.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry

section ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-- **The normalized correspondence preserves the budget.** -/
theorem normGraph_degree_act (x : E) (g : G) :
    D.pair (normGraph D.toPolarSurface (D.act g x)) D.H =
      D.pair (normGraph D.toPolarSurface x) D.H := by
  rw [normGraph_degree, normGraph_degree, D.defect_act]

/-- **The similitude law.** A Hecke graph multiplies the degree by `e^{s(g)}`. -/
theorem normGraph_degree_heckeGraph (x : E) (g : G) :
    D.pair (normGraph D.toPolarSurface (D.heckeGraph x g)) D.H =
      Real.exp (D.scale g) * D.pair (normGraph D.toPolarSurface x) D.H := by
  rw [normGraph_degree, normGraph_degree, ScalingDatum.heckeGraph, D.defect_smul_left,
    D.defect_smul_right, D.defect_act, ← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The degrees of the normalized graphs of `x ± ψ_g x` are `c_x(0) ± c_x(g)`. -/
theorem normGraph_degree_one_add_act (x : E) (g : G) (ε : ℝ) (hε : ε ^ 2 = 1) :
    D.pair (normGraph D.toPolarSurface (x + ε • D.act g x)) D.H =
      D.orbitCorr x 0 + ε * D.orbitCorr x g := by
  rw [normGraph_degree, add_comm, show ε • D.act g x + x = ε • D.act g x + (1 : ℝ) • x by
    rw [one_smul], D.defect_weilPlane_self, D.orbitCorr_zero, hε]
  ring

/-- **Budget sufficiency is positivity of two normalized graphs.** -/
theorem hasseWeilAt_iff_normGraph_degree_nonneg (x : E) (g : G) :
    D.HasseWeilAt x g ↔
      0 ≤ D.pair (normGraph D.toPolarSurface (x + D.act g x)) D.H ∧
        0 ≤ D.pair (normGraph D.toPolarSurface (x - D.act g x)) D.H := by
  have h1 := normGraph_degree_one_add_act D x g 1 (by norm_num)
  have h2 := normGraph_degree_one_add_act D x g (-1) (by norm_num)
  rw [one_smul] at h1
  rw [neg_one_smul, ← sub_eq_add_neg] at h2
  rw [h1, h2, ScalingDatum.HasseWeilAt, abs_le]
  constructor <;> rintro ⟨a, b⟩ <;> constructor <;> linarith

end ScalingDatum

/-! ### Curves: the budget `2g` -/

/-- **The budget of the diagonal of a curve datum is `2g`.** -/
theorem CurveDatum.diagonal_defect {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (D.windowSurface {0}).defect (0, 0, Pi.single 0 1) (0, 0, Pi.single 0 1) = Fintype.card ι := by
  rw [D.windowSurface_defect_self, D.spanDefect_eq_toeplitz, CurveDatum.toeplitz]
  simp [D.trace_zero]

/-- **For curve data a fixed budget at every level is unitarity** (bounded power sums, ACG). -/
theorem budget_sufficient_iff_unitary {ι : Type*} [Fintype ι] (D : CurveDatum ι) :
    (∃ C, ∀ j, ‖D.powerSum j‖ ≤ C) ↔ ∀ i, ‖D.β i‖ = 1 := by
  refine ⟨ArithmeticCorrelationGeometry.unitary_of_bounded_powerSum D, fun h => ?_⟩
  refine ⟨Fintype.card ι, fun j => ?_⟩
  rw [CurveDatum.powerSum]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_pow, h]

/-- **The golden datum: budget `2`, insufficient.** -/
theorem goldenDatum_budget_insufficient :
    (goldenDatum.windowSurface {0}).defect (0, 0, Pi.single 0 1) (0, 0, Pi.single 0 1) = 2 ∧
      ¬ ∃ C, ∀ j, ‖goldenDatum.powerSum j‖ ≤ C := by
  refine ⟨by rw [CurveDatum.diagonal_defect]; simp, ?_⟩
  exact ArithmeticCorrelationGeometry.goldenDatum_no_fixed_budget

/-- **The complex fake: budget `4`, insufficient**, although all its point counts and kernel counts
are nonnegative. -/
theorem complexFake_budget_insufficient :
    (complexFake.windowSurface {0}).defect (0, 0, Pi.single 0 1) (0, 0, Pi.single 0 1) = 4 ∧
      ¬ ∃ C, ∀ j, ‖complexFake.powerSum j‖ ≤ C := by
  refine ⟨by rw [CurveDatum.diagonal_defect]; simp, fun h => ?_⟩
  exact complexFake_not_unitary ((budget_sufficient_iff_unitary complexFake).mp h)

/-! ### `ζ`: sufficiency of the spline budget -/

/-- **RH is the sufficiency of the budget of the cubic spline at every scale**: the normalized
graphs of `1 ± ψ_t` applied to it have nonnegative degree. -/
theorem riemannHypothesis_iff_spline_graphs_one_add_sub_nonneg :
    RiemannHypothesis ↔ ∀ t : ℝ,
      0 ≤ zetaScalingDatum.pair
          (normGraph scalingSurface (splineCycle + zetaScalingDatum.act t splineCycle))
          scalingSurface.H ∧
        0 ≤ zetaScalingDatum.pair
          (normGraph scalingSurface (splineCycle - zetaScalingDatum.act t splineCycle))
          scalingSurface.H := by
  rw [riemannHypothesis_iff_splineOrbit_hasseWeil]
  exact forall_congr' fun t => hasseWeilAt_iff_normGraph_degree_nonneg zetaScalingDatum splineCycle t

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
