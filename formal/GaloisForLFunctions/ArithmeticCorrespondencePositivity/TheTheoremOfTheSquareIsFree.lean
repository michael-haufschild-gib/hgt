import GaloisForLFunctions.ArithmeticOrientationGeometry.TheSplineOrbitDecidesTheCriticalLine
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDefectOfAGraphIsTwiceItsDegree

/-!
# The theorem of the square is free

On `E × E` for an elliptic curve the graph map `f ↦ [Γ_f]` from `End(E)` to the Néron–Severi group
is quadratic (the theorem of the square), each graph has `Γ_f · V = 1` and `Γ_f² = 0`, and its
horizontal degree `deg f = Γ_f · H` is a quadratic form whose polarization is the Rosati trace.
Hasse's proof is the positivity of that form. This file shows that the algebraic half of this
structure exists on every polar surface, hence over `ℤ`, and carries no positivity.

* **Normalized graphs** (`normGraph`). Every class `y` has a unique class `N(y)` in `y + ⟨H, V⟩`
  with `N(y) · V = 1` and `N(y)² = 0` (`normGraph_pair_V`, `normGraph_isotropic`,
  `eq_normGraph_of_mem`); it depends only on `y` modulo the fibre plane (`normGraph_add_fibre`).
* **Degree is half the defect** (`normGraph_degree`): `N(y) · H = δ(y, y)/2`, and its polarization
  is the defect pairing (`normGraph_degree_add`).
* **The theorem of the square** (`normGraph_square`):
  `N(y + z) + N(y − z) = 2N(y) + N(z) + N(−z) − 2N(0)`, `N(0) = H`, on every polar surface.
* **Scaling data** (`graphDegree`). On the correspondence ring of a scaling datum the degree of the
  normalized graph of `ξ · x` is half the Rosati trace `τ_x(ξ ⋆ ξ′)` (`graphDegree_eq`); degree
  positivity on the ring is the orbit Hodge index (`forall_graphDegree_nonneg_iff`), and on the
  two-term correspondences `r[g] + t[0]` it is the Hasse–Weil bound at `g`
  (`hasseWeilAt_iff_graphDegree_nonneg`).
* **ℤ.** RH ⟺ every normalized Hecke graph of every test has nonnegative degree
  (`riemannHypothesis_iff_forall_graphDegree_nonneg`) ⟺ those of the cubic spline do
  (`riemannHypothesis_iff_splineCycle_graphDegree_nonneg`). The degree of the normalized graph of a
  test is half Weil's form (`normGraph_degree_scalingSurface`). The ring map satisfies the theorem
  of the square while the scale map `a ↦ T_a x` satisfies no parallelogram law
  (`ring_square_and_scale_no_square`): ring addition, not scale addition, is what the theorem
  of the square is about.
* **Calibration.** In genus one the graph classes of `m − nF` are the normalized graphs of
  `mΔ − nΓ_F` (`CurveDatum.graphCycle_eq_normGraph`). The golden datum satisfies the theorem of the
  square and has the normalized graph of `2Δ − Γ_F` of degree `−1`
  (`goldenDatum_normGraph_degree_neg`).

So the theorem of the square is an identity: it is not the missing ingredient of a budget over
`ℤ`. The sign lives in the positivity of the degree form, which is the Rosati positivity.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open ArithmeticCastelnuovoSeveri ArithmeticOrientationGeometry
open ArithmeticOrientationGeometry.ScalingDatum (conv rosati)

/-! ### Normalized graphs on a polar surface -/

section PolarSurface

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The **normalized graph** `N(y) = y + (1 − y·V) H + (−y²/2 − (1 − y·V)(y·H)) V`: the isotropic
class of unit vertical degree in `y + ⟨H, V⟩`. -/
def normGraph (y : E) : E :=
  y + (1 - S.pair y S.V) • S.H + (-(S.pair y y / 2) - (1 - S.pair y S.V) * S.pair y S.H) • S.V

theorem pair_normGraph (y z : E) :
    S.pair (normGraph S y) z = S.pair y z + (1 - S.pair y S.V) * S.pair S.H z +
      (-(S.pair y y / 2) - (1 - S.pair y S.V) * S.pair y S.H) * S.pair S.V z := by
  simp only [normGraph, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- A normalized graph has unit vertical degree. -/
theorem normGraph_pair_V (y : E) : S.pair (normGraph S y) S.V = 1 := by
  rw [pair_normGraph, S.pair_H_V, S.pair_V_V]; ring

/-- **The degree of a normalized graph is half the defect.** -/
theorem normGraph_degree (y : E) : S.pair (normGraph S y) S.H = S.defect y y / 2 := by
  rw [pair_normGraph, S.pair_H_H, S.pair_V_H, S.defect_self]; ring

/-- A normalized graph is isotropic (adjunction for a graph of genus one). -/
theorem normGraph_isotropic (y : E) : S.pair (normGraph S y) (normGraph S y) = 0 := by
  have hH : S.pair S.H (normGraph S y) = S.defect y y / 2 := by rw [S.pair_comm, normGraph_degree]
  have hV : S.pair S.V (normGraph S y) = 1 := by rw [S.pair_comm, normGraph_pair_V]
  have hy : S.pair y (normGraph S y) = S.pair y y + (1 - S.pair y S.V) * S.pair y S.H +
      (-(S.pair y y / 2) - (1 - S.pair y S.V) * S.pair y S.H) * S.pair y S.V := by
    rw [S.pair_comm, pair_normGraph, S.pair_comm S.H y, S.pair_comm S.V y]
  rw [pair_normGraph, hy, hH, hV, S.defect_self]; ring

/-- The defect does not change under normalization. -/
theorem defect_normGraph (y : E) : S.defect (normGraph S y) (normGraph S y) = S.defect y y := by
  rw [S.defect_self, normGraph_isotropic, normGraph_pair_V, normGraph_degree]; ring

/-- The normalized graph depends only on the class modulo the fibre plane. -/
theorem normGraph_add_fibre (y : E) (a b : ℝ) :
    normGraph S (y + a • S.H + b • S.V) = normGraph S y := by
  have hV : S.pair (y + a • S.H + b • S.V) S.V = S.pair y S.V + a := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_H_V, S.pair_V_V]; ring
  have hH : S.pair (y + a • S.H + b • S.V) S.H = S.pair y S.H + b := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_H_H, S.pair_V_H]; ring
  have hyy : S.pair (y + a • S.H + b • S.V) (y + a • S.H + b • S.V) =
      S.pair y y + 2 * a * S.pair y S.H + 2 * b * S.pair y S.V + 2 * a * b := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      S.pair_H_H, S.pair_V_V, S.pair_H_V, S.pair_V_H, S.pair_comm S.H y, S.pair_comm S.V y]
    ring
  rw [normGraph, normGraph, hV, hH, hyy]
  module

/-- A class that is already isotropic of unit vertical degree is its own normalized graph. -/
theorem normGraph_eq_self {z : E} (hV : S.pair z S.V = 1) (hz : S.pair z z = 0) :
    normGraph S z = z := by
  rw [normGraph, hV, hz]; simp

/-- **Uniqueness.** The normalized graph is the only isotropic class of unit vertical degree in
`y + ⟨H, V⟩`. -/
theorem eq_normGraph_of_mem {y z : E} (a b : ℝ) (hzy : z = y + a • S.H + b • S.V)
    (hV : S.pair z S.V = 1) (hz : S.pair z z = 0) : z = normGraph S y := by
  rw [← normGraph_eq_self S hV hz, hzy, normGraph_add_fibre]

/-- The normalized graph of `0` is the horizontal fibre `H`, the graph of the zero map. -/
theorem normGraph_zero : normGraph S 0 = S.H := by
  simp [normGraph]

/-- **The polarization of the degree is the defect pairing.** -/
theorem normGraph_degree_add (y z : E) :
    S.pair (normGraph S (y + z)) S.H =
      S.pair (normGraph S y) S.H + S.pair (normGraph S z) S.H + S.defect y z := by
  rw [normGraph_degree, normGraph_degree, normGraph_degree, S.defect_add_left,
    S.defect_comm y (y + z), S.defect_comm z (y + z), S.defect_add_left, S.defect_add_left,
    S.defect_comm z y]
  ring

/-- **The theorem of the square.** The normalized graph map is quadratic:
`N(y + z) + N(y − z) = 2N(y) + N(z) + N(−z) − 2N(0)`. -/
theorem normGraph_square (y z : E) :
    normGraph S (y + z) + normGraph S (y - z) =
      (2 : ℝ) • normGraph S y + normGraph S z + normGraph S (-z) - (2 : ℝ) • normGraph S 0 := by
  simp only [normGraph, map_add, map_sub, map_neg, map_zero, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.zero_apply, S.pair_comm z y]
  module

end PolarSurface

/-! ### The degree form of the correspondence ring -/

section ScalingDatum

variable {G : Type*} [AddCommGroup G] {E : Type*} [AddCommGroup E] [Module ℝ E]
variable (D : ScalingDatum G E)

/-- The degree of the normalized graph of the correspondence `ξ` applied to the cycle `x`. -/
def graphDegree (x : E) (ξ : Correspondence G) : ℝ :=
  D.pair (normGraph D.toPolarSurface (D.corr ξ x)) D.H

/-- **The degree of a normalized graph is half the Rosati trace.** -/
theorem graphDegree_eq (x : E) (ξ : Correspondence G) :
    graphDegree D x ξ = D.traceAt x (conv ξ (rosati ξ)) / 2 := by
  rw [graphDegree, normGraph_degree, D.defect_corr_corr]

theorem corr_sub (ξ η : Correspondence G) (x : E) :
    D.corr (ξ - η) x = D.corr ξ x - D.corr η x := by
  rw [eq_sub_iff_add_eq, ← D.corr_add, sub_add_cancel]

/-- **The theorem of the square on the correspondence ring.** -/
theorem normGraph_corr_square (x : E) (ξ η : Correspondence G) :
    normGraph D.toPolarSurface (D.corr (ξ + η) x) + normGraph D.toPolarSurface (D.corr (ξ - η) x) =
      (2 : ℝ) • normGraph D.toPolarSurface (D.corr ξ x) +
        normGraph D.toPolarSurface (D.corr η x) + normGraph D.toPolarSurface (-D.corr η x) -
          (2 : ℝ) • D.H := by
  rw [D.corr_add, corr_sub, normGraph_square, normGraph_zero]

/-- **Degree positivity on the correspondence ring is the orbit Hodge index.** -/
theorem forall_graphDegree_nonneg_iff (x : E) :
    (∀ ξ, 0 ≤ graphDegree D x ξ) ↔ D.OrbitHodgeIndex x := by
  rw [← D.rosatiPositive_iff_orbitHodgeIndex, ScalingDatum.RosatiPositive]
  simp only [graphDegree_eq]
  constructor <;> intro h ξ <;> have := h ξ <;> linarith

/-- The two-term correspondence `r[g] + t[0]` spans the Weil plane of `x` at `g`. -/
theorem corr_weilPlane (x : E) (g : G) (r t : ℝ) :
    D.corr (Finsupp.single g r + Finsupp.single 0 t) x = r • D.act g x + t • x := by
  rw [D.corr_add, D.corr_single, D.corr_single, D.act_zero]

/-- **Hasse–Weil at one scale is degree positivity on the two-term correspondences.** -/
theorem hasseWeilAt_iff_graphDegree_nonneg (x : E) (g : G) :
    D.HasseWeilAt x g ↔
      ∀ r t : ℝ, 0 ≤ graphDegree D x (Finsupp.single g r + Finsupp.single 0 t) := by
  rw [D.hasseWeilAt_iff_defect_nonneg_weilPlane]
  simp only [graphDegree, normGraph_degree, corr_weilPlane]
  constructor <;> intro h r t <;> have := h r t <;> linarith

end ScalingDatum

/-! ### The scaling surface of `ℤ` -/

/-- The degree of the normalized graph of a cycle of the scaling surface is half Weil's form of its
test. -/
theorem normGraph_degree_scalingSurface (x : ScalingCycle) :
    scalingSurface.pair (normGraph scalingSurface x) scalingSurface.H = weilPair x.2.2 x.2.2 / 2 := by
  rw [normGraph_degree, scalingSurface_defect_self]

theorem zetaHodgeIndex_iff_forall_orbitHodgeIndex :
    zetaScalingDatum.HodgeIndex ↔ ∀ x, zetaScalingDatum.OrbitHodgeIndex x :=
  zetaScalingDatum.hodgeIndex_tfae.out 0 1

/-- **RH is degree positivity of all normalized Hecke graphs.** -/
theorem riemannHypothesis_iff_forall_graphDegree_nonneg :
    RiemannHypothesis ↔
      ∀ (x : ScalingCycle) (ξ : Correspondence ℝ), 0 ≤ graphDegree zetaScalingDatum x ξ := by
  rw [← zetaScalingDatum_hodgeIndex_iff, zetaHodgeIndex_iff_forall_orbitHodgeIndex]
  exact forall_congr' fun x => (forall_graphDegree_nonneg_iff _ x).symm

/-- **One cycle suffices**: RH is degree positivity of the normalized Hecke graphs of the cubic
spline. -/
theorem riemannHypothesis_iff_splineCycle_graphDegree_nonneg :
    RiemannHypothesis ↔ ∀ ξ : Correspondence ℝ, 0 ≤ graphDegree zetaScalingDatum splineCycle ξ := by
  rw [forall_graphDegree_nonneg_iff]
  constructor
  · intro h
    exact zetaHodgeIndex_iff_forall_orbitHodgeIndex.mp (zetaScalingDatum_hodgeIndex_iff.mpr h)
      splineCycle
  · intro h
    exact riemannHypothesis_iff_splineOrbit_hasseWeil.mpr fun t =>
      zetaScalingDatum.hasseWeilAt_of_orbitHodgeIndex h t

/-- **Ring addition versus scale addition.** On the scaling surface the normalized graph map of
the correspondence ring obeys the theorem of the square at every cycle, while the Hecke scale map
`a ↦ T_a x` of a cycle with nonzero source obeys no parallelogram law modulo fibres. -/
theorem ring_square_and_scale_no_square (x : ScalingCycle) (hx : x.2.2 ≠ 0) :
    (∀ ξ η : Correspondence ℝ,
      normGraph scalingSurface (zetaScalingDatum.corr (ξ + η) x) +
          normGraph scalingSurface (zetaScalingDatum.corr (ξ - η) x) =
        (2 : ℝ) • normGraph scalingSurface (zetaScalingDatum.corr ξ x) +
          normGraph scalingSurface (zetaScalingDatum.corr η x) +
            normGraph scalingSurface (-zetaScalingDatum.corr η x) - (2 : ℝ) • scalingSurface.H) ∧
    ∀ a b : ℝ, 0 < b → b < a → a ≠ 2 * b → ∀ α β : ℝ,
      heckeCorrespondence (a + b) x + heckeCorrespondence (a - b) x -
          (2 : ℝ) • heckeCorrespondence a x - (2 : ℝ) • heckeCorrespondence b x ≠
        α • scalingSurface.H + β • scalingSurface.V :=
  ⟨fun ξ η => normGraph_corr_square zetaScalingDatum x ξ η,
    fun _ _ hb hab h2 α β => heckeCorrespondence_no_square_relation hb hab h2 x hx α β⟩

/-! ### Calibration: genus one and the golden datum -/

/-- **Genus one: the graph classes of `m − nF` are normalized graphs** of `mΔ − nΓ_F`. -/
theorem CurveDatum.graphCycle_eq_normGraph {ι : Type*} [Fintype ι] (D : CurveDatum ι)
    (hg : Fintype.card ι = 2) (m n : ℝ) :
    D.graphCycle m n = normGraph (D.windowSurface {0, 1}) (0, 0, CurveDatum.graphCoeff m n) := by
  refine eq_normGraph_of_mem _ (1 - m + n) (D.endDeg m n - m + n * D.q) ?_
    (D.pair_graphCycle_V m n) (D.defect_graphCycle_of_genusOne hg m n).2
  ext <;> simp [CurveDatum.graphCycle, CurveDatum.windowSurface]

/-- **The golden datum has the theorem of the square and a graph of negative degree.** Its window
surface satisfies the theorem of the square, and the normalized graph of `2Δ − Γ_F` has degree
`deg(2 − F) = −1`. -/
theorem goldenDatum_normGraph_degree_neg :
    (∀ y z : SpanCycle,
      normGraph (goldenDatum.windowSurface {0, 1}) (y + z) +
          normGraph (goldenDatum.windowSurface {0, 1}) (y - z) =
        (2 : ℝ) • normGraph (goldenDatum.windowSurface {0, 1}) y +
          normGraph (goldenDatum.windowSurface {0, 1}) z +
            normGraph (goldenDatum.windowSurface {0, 1}) (-z) -
              (2 : ℝ) • normGraph (goldenDatum.windowSurface {0, 1}) 0) ∧
    (goldenDatum.windowSurface {0, 1}).pair
        (normGraph (goldenDatum.windowSurface {0, 1}) (0, 0, CurveDatum.graphCoeff 2 1))
        (goldenDatum.windowSurface {0, 1}).H = -1 := by
  refine ⟨fun y z => normGraph_square _ y z, ?_⟩
  rw [← CurveDatum.graphCycle_eq_normGraph goldenDatum (Fintype.card_fin 2),
    CurveDatum.pair_graphCycle_H, goldenDatum_endDeg_two_one.1]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
