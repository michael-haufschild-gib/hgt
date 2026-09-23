import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.RingTheory.RootsOfUnity.Complex

open Filter Set Topology
open scoped InnerProductSpace

/-!
# Finite law-relation wall synchronization

Closed formalization of finite-dimensional law walls: fixed-rank graph Grassmannians,
Gram/determinant synchronization, closed inverse relations, divergent inverse-lift cost,
exactification fibers, unitary phase loss, and the sharp one-port model.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

abbrev FullRankFrame (V H : Type*) [NormedAddCommGroup V] [NormedAddCommGroup H]
    [NormedSpace ℂ V] [NormedSpace ℂ H] :=
  { f : V →L[ℂ] H // Function.Injective f }

namespace FullRankFrame

variable {V H : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H]
    [NormedSpace ℂ V] [NormedSpace ℂ H]

def rangeSetoid : Setoid (FullRankFrame V H) where
  r f g := f.1.toLinearMap.range = g.1.toLinearMap.range
  iseqv := {
    refl := fun _ => rfl
    symm := fun h => h.symm
    trans := fun h₁ h₂ => h₁.trans h₂ }

end FullRankFrame

def FiniteGrassmannian (V H : Type*) [NormedAddCommGroup V] [NormedAddCommGroup H]
    [NormedSpace ℂ V] [NormedSpace ℂ H] :=
  Quotient (FullRankFrame.rangeSetoid (V := V) (H := H))

noncomputable instance finiteGrassmannianTopologicalSpace
    {V H : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H]
    [NormedSpace ℂ V] [NormedSpace ℂ H] :
    TopologicalSpace (FiniteGrassmannian V H) := by
  unfold FiniteGrassmannian
  infer_instance

namespace FiniteGrassmannian

variable {V H : Type*} [NormedAddCommGroup V] [NormedAddCommGroup H]
    [NormedSpace ℂ V] [NormedSpace ℂ H]

def mk (f : FullRankFrame V H) : FiniteGrassmannian V H :=
  @Quotient.mk' _ (FullRankFrame.rangeSetoid (V := V) (H := H)) f

def carrier : FiniteGrassmannian V H → Submodule ℂ H :=
  Quotient.lift (fun f => f.1.toLinearMap.range) (by
    intro f g h
    exact h)

@[simp] theorem carrier_mk (f : FullRankFrame V H) :
    carrier (mk f) = f.1.toLinearMap.range := rfl

theorem carrier_finrank [FiniteDimensional ℂ V] (g : FiniteGrassmannian V H) :
    Module.finrank ℂ (carrier g) = Module.finrank ℂ V := by
  refine Quotient.inductionOn g (fun f => ?_)
  change Module.finrank ℂ (LinearMap.range f.1.toLinearMap) = Module.finrank ℂ V
  have h := f.1.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.ker_eq_bot.mpr f.2] at h
  simpa using h

end FiniteGrassmannian

variable {V W : Type*} [NormedAddCommGroup V] [NormedAddCommGroup W]
    [InnerProductSpace ℂ V] [InnerProductSpace ℂ W]

def forwardGraphFrame (A : V →L[ℂ] W) : FullRankFrame V (V × W) :=
  ⟨(ContinuousLinearMap.id ℂ V).prod A, by
    intro x y h
    exact congrArg Prod.fst h⟩

def inverseGraphFrame (A : V →L[ℂ] W) : FullRankFrame V (W × V) :=
  ⟨A.prod (ContinuousLinearMap.id ℂ V), by
    intro x y h
    exact congrArg Prod.snd h⟩

def forwardGraphGrassmannian (A : V →L[ℂ] W) :
    FiniteGrassmannian V (V × W) :=
  FiniteGrassmannian.mk (forwardGraphFrame A)

def inverseGraphGrassmannian (A : V →L[ℂ] W) :
    FiniteGrassmannian V (W × V) :=
  FiniteGrassmannian.mk (inverseGraphFrame A)

theorem continuous_forwardGraphGrassmannian :
    Continuous (forwardGraphGrassmannian : (V →L[ℂ] W) → FiniteGrassmannian V (V × W)) := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  have hpair : Continuous (fun A : V →L[ℂ] W =>
      ((ContinuousLinearMap.id ℂ V), A)) :=
    continuous_const.prodMk continuous_id
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) ℂ).continuous.comp hpair

theorem continuous_inverseGraphGrassmannian :
    Continuous (inverseGraphGrassmannian : (V →L[ℂ] W) → FiniteGrassmannian V (W × V)) := by
  apply continuous_quotient_mk'.comp
  apply Continuous.subtype_mk
  have hpair : Continuous (fun A : V →L[ℂ] W =>
      (A, (ContinuousLinearMap.id ℂ V))) :=
    continuous_id.prodMk continuous_const
  exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℂ) ℂ).continuous.comp hpair

theorem inverseGraphGrassmannian_tendsto {α : Type*} {l : Filter α}
    {A : α → V →L[ℂ] W} {A0 : V →L[ℂ] W} (hA : Tendsto A l (𝓝 A0)) :
    Tendsto (fun t => inverseGraphGrassmannian (A t)) l
      (𝓝 (inverseGraphGrassmannian A0)) :=
  continuous_inverseGraphGrassmannian.continuousAt.tendsto.comp hA

def inverseLawRelation (A : V →L[ℂ] W) : Submodule ℂ (W × V) :=
  LinearMap.range (A.toLinearMap.prod (LinearMap.id : V →ₗ[ℂ] V))

def linearRelationDomain (R : Submodule ℂ (W × V)) : Submodule ℂ W :=
  R.map (LinearMap.fst ℂ W V)

def linearRelationMultivalued (R : Submodule ℂ (W × V)) : Submodule ℂ V :=
  R.comap (LinearMap.inr ℂ W V)

theorem inverseLawRelation_eq_range_prod (A : V →L[ℂ] W) :
    inverseLawRelation A =
      LinearMap.range (A.toLinearMap.prod (LinearMap.id : V →ₗ[ℂ] V)) := rfl

theorem inverseLawRelation_eq_flipped_graph (A : V →L[ℂ] W) :
    inverseLawRelation A =
      A.toLinearMap.graph.map
        (LinearEquiv.prodComm ℂ V W : (V × W) →ₗ[ℂ] (W × V)) := by
  ext p
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(x, A x), rfl, ?_⟩
    exact hx
  · rintro ⟨q, hq, hqp⟩
    refine ⟨q.1, ?_⟩
    calc
      (A.toLinearMap.prod (LinearMap.id : V →ₗ[ℂ] V)) q.1 = (A q.1, q.1) := rfl
      _ = (q.2, q.1) := Prod.ext hq.symm rfl
      _ = p := hqp

theorem inverseGraphGrassmannian_carrier (A : V →L[ℂ] W) :
    FiniteGrassmannian.carrier (inverseGraphGrassmannian A) = inverseLawRelation A := by
  change LinearMap.range
    (A.toLinearMap.prod (LinearMap.id : V →ₗ[ℂ] V)) = inverseLawRelation A
  rfl

theorem inverseLawRelation_domain (A : V →L[ℂ] W) :
    linearRelationDomain (inverseLawRelation A) = A.toLinearMap.range := by
  ext y
  simp [linearRelationDomain, inverseLawRelation]

theorem inverseLawRelation_multivalued (A : V →L[ℂ] W) :
    linearRelationMultivalued (inverseLawRelation A) = A.toLinearMap.ker := by
  ext x
  simp [linearRelationMultivalued, inverseLawRelation, LinearMap.mem_ker]

section Hilbert

variable [CompleteSpace V] [CompleteSpace W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]

def gramOperator (A : V →L[ℂ] W) : V →L[ℂ] V := A.adjoint.comp A

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem gramOperator_inner (A : V →L[ℂ] W) (x : V) :
    ⟪gramOperator A x, x⟫_ℂ = ⟪A x, A x⟫_ℂ := by
  rw [gramOperator, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem gramOperator_isPositive (A : V →L[ℂ] W) :
    (gramOperator A).IsPositive := by
  simpa only [gramOperator] using ContinuousLinearMap.isPositive_adjoint_comp_self A

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem gramOperator_ker (A : V →L[ℂ] W) :
    (gramOperator A).ker = A.ker := by
  exact A.ker_adjoint_comp_self

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem gramOperator_nullity (A : V →L[ℂ] W) :
    Module.finrank ℂ (gramOperator A).ker = Module.finrank ℂ A.ker := by
  rw [gramOperator_ker]

omit [FiniteDimensional ℂ W] in
theorem gramOperator_det_eq_normDet_sq (A : V →L[ℂ] W) :
    (gramOperator A).det = ((A.normDet ^ (2 : ℕ) : ℝ) : ℂ) := by
  change (A.adjoint.comp A).det = ((A.normDet ^ (2 : ℕ) : ℝ) : ℂ)
  exact A.normDet_sq.symm

omit [FiniteDimensional ℂ W] in
theorem gramOperator_det_eq_zero_iff (A : V →L[ℂ] W) :
    (gramOperator A).det = 0 ↔ A.ker ≠ ⊥ := by
  rw [ContinuousLinearMap.det, LinearMap.det_eq_zero_iff_ker_ne_bot,
    gramOperator_ker]

omit [FiniteDimensional ℂ W] in
theorem normDet_eq_sqrt_norm_gramDet (A : V →L[ℂ] W) :
    A.normDet = Real.sqrt ‖(gramOperator A).det‖ := by
  rw [← Real.sqrt_sq (A.normDet_nonneg)]
  congr 1
  rw [gramOperator_det_eq_normDet_sq]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg A.normDet)]

def framedDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V →L[ℂ] W) (bV : OrthonormalBasis ι ℂ V) (bW : OrthonormalBasis ι ℂ W) : ℂ :=
  (A.toLinearMap.toMatrix bV.toBasis bW.toBasis).det

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem normDet_eq_norm_framedDet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V →L[ℂ] W) (bV : OrthonormalBasis ι ℂ V) (bW : OrthonormalBasis ι ℂ W) :
    A.normDet = ‖framedDet A bV bW‖ := by
  exact A.toLinearMap.normDet_eq_norm_det_toMatrix bV bW

omit [FiniteDimensional ℂ W] in
theorem gramOperator_det_eq_norm_framedDet_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : V →L[ℂ] W) (bV : OrthonormalBasis ι ℂ V) (bW : OrthonormalBasis ι ℂ W) :
    (gramOperator A).det = ((‖framedDet A bV bW‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  letI := bW.toBasis.finiteDimensional_of_finite
  rw [gramOperator_det_eq_normDet_sq,
    normDet_eq_norm_framedDet A bV bW]

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem continuous_gramOperator :
    Continuous (gramOperator : (V →L[ℂ] W) → V →L[ℂ] V) := by
  exact Continuous.clm_comp ContinuousLinearMap.adjoint.continuous continuous_id

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem continuous_gramOperator_det :
    Continuous (fun A : V →L[ℂ] W => (gramOperator A).det) :=
  ContinuousLinearMap.continuous_det.comp continuous_gramOperator

omit [FiniteDimensional ℂ W] in
theorem continuous_normDet :
    Continuous (fun A : V →L[ℂ] W => A.normDet) := by
  simp_rw [normDet_eq_sqrt_norm_gramDet]
  exact (continuous_norm.comp continuous_gramOperator_det).sqrt

omit [FiniteDimensional ℂ W] in
theorem normDet_tendsto_zero_of_tendsto_of_ker_ne_bot
    {α : Type*} {l : Filter α} {A : α → V →L[ℂ] W} {A0 : V →L[ℂ] W}
    (hA : Tendsto A l (𝓝 A0)) (hker : A0.ker ≠ ⊥) :
    Tendsto (fun t => (A t).normDet) l (𝓝 0) := by
  have h0 : A0.normDet = 0 := LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hker
  change Tendsto ((fun B : V →L[ℂ] W => B.normDet) ∘ A) l (𝓝 0)
  convert continuous_normDet.continuousAt.tendsto.comp hA using 1
  rw [h0]

omit [FiniteDimensional ℂ W] in
theorem gramDet_tendsto_zero_of_tendsto_of_ker_ne_bot
    {α : Type*} {l : Filter α} {A : α → V →L[ℂ] W} {A0 : V →L[ℂ] W}
    (hA : Tendsto A l (𝓝 A0)) (hker : A0.ker ≠ ⊥) :
    Tendsto (fun t => (gramOperator (A t)).det) l (𝓝 0) := by
  have h0 : (gramOperator A0).det = 0 :=
    (gramOperator_det_eq_zero_iff A0).mpr hker
  change Tendsto ((fun B : V →L[ℂ] W => (gramOperator B).det) ∘ A) l (𝓝 0)
  convert continuous_gramOperator_det.continuousAt.tendsto.comp hA using 1
  rw [h0]

def transverseComponent (A0 : V →L[ℂ] W) (y : W) : W :=
  y - A0.range.starProjection y

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem transverseComponent_mem_orthogonal (A0 : V →L[ℂ] W) (y : W) :
    transverseComponent A0 y ∈ A0.rangeᗮ := by
  exact A0.range.sub_starProjection_mem_orthogonal y

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem transverseComponent_ne_zero {A0 : V →L[ℂ] W} {y : W}
    (hy : y ∉ A0.range) : transverseComponent A0 y ≠ 0 := by
  intro hzero
  apply hy
  have heq : y = A0.range.starProjection y := sub_eq_zero.mp hzero
  rw [heq]
  exact A0.range.starProjection_apply_mem y

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem transverseComponent_norm_le_operator_mul_lift
    (A A0 : V →L[ℂ] W) (y : W) (x : V) (hx : A x = y) :
    ‖transverseComponent A0 y‖ ≤ ‖A - A0‖ * ‖x‖ := by
  let P : Submodule ℂ W := A0.range
  have hA0x : Pᗮ.starProjection (A0 x) = 0 :=
    P.starProjection_orthogonal_apply_eq_zero ⟨x, rfl⟩
  calc
    ‖transverseComponent A0 y‖ = ‖Pᗮ.starProjection y‖ := by
      rw [P.starProjection_orthogonal_val]
      rfl
    _ = ‖Pᗮ.starProjection (A x)‖ := by rw [hx]
    _ = ‖Pᗮ.starProjection ((A - A0) x)‖ := by
      simp only [sub_apply, map_sub, hA0x, sub_zero]
    _ ≤ ‖(A - A0) x‖ := Pᗮ.norm_starProjection_apply_le _
    _ ≤ ‖A - A0‖ * ‖x‖ := (A - A0).le_opNorm x

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem inverseLiftCost_tendsto_atTop
    {α : Type*} {l : Filter α} {A : α → V →L[ℂ] W} {A0 : V →L[ℂ] W}
    {x : α → V} {y : W} (hA : Tendsto A l (𝓝 A0))
    (hlift : ∀ᶠ t in l, A t (x t) = y) (hy : y ∉ A0.range) :
    Tendsto (fun t => ‖x t‖ ^ (2 : ℕ)) l atTop := by
  let z : W := transverseComponent A0 y
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr (transverseComponent_ne_zero hy)
  rw [Filter.tendsto_atTop]
  intro b
  let c : ℝ := max 1 b + 1
  have hc : 0 < c := by
    dsimp [c]
    linarith [le_max_left (1 : ℝ) b]
  have hdelta : 0 < ‖z‖ / c := div_pos hz hc
  have hclose : ∀ᶠ t in l, ‖A t - A0‖ < ‖z‖ / c := by
    have hball := hA.eventually (Metric.ball_mem_nhds A0 hdelta)
    filter_upwards [hball] with t ht
    simpa only [Metric.mem_ball, dist_eq_norm] using ht
  filter_upwards [hlift, hclose] with t htLift htClose
  have hbound : ‖z‖ ≤ ‖A t - A0‖ * ‖x t‖ :=
    transverseComponent_norm_le_operator_mul_lift (A t) A0 y (x t) htLift
  have hdc : ‖A t - A0‖ * c < ‖z‖ := (lt_div_iff₀ hc).mp htClose
  have hdpos : 0 < ‖A t - A0‖ := by
    by_contra hnot
    have hzero : ‖A t - A0‖ = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    rw [hzero, zero_mul] at hbound
    exact (not_lt_of_ge hbound) hz
  have hc_lt : c < ‖x t‖ := by
    exact lt_of_mul_lt_mul_left (hdc.trans_le hbound) hdpos.le
  have hb_le_c : b ≤ c := by
    dsimp [c]
    linarith [le_max_right (1 : ℝ) b]
  have hxnorm : 0 ≤ ‖x t‖ := norm_nonneg _
  have hone : 1 ≤ ‖x t‖ := by
    dsimp [c] at hc_lt
    linarith [le_max_left (1 : ℝ) b]
  have hx_le_sq : ‖x t‖ ≤ ‖x t‖ ^ (2 : ℕ) := by nlinarith
  exact hb_le_c.trans (hc_lt.le.trans hx_le_sq)

abbrev LiftFiber (A : V →L[ℂ] W) (y : W) := { x : V // A x = y }

instance liftFiberVAdd (A : V →L[ℂ] W) (y : W) : VAdd A.ker (LiftFiber A y) where
  vadd k x := ⟨(k : V) + (x : V), by
    rw [map_add, show A (k : V) = 0 from k.property, x.property, zero_add]⟩

instance liftFiberAddAction (A : V →L[ℂ] W) (y : W) :
    AddAction A.ker (LiftFiber A y) where
  zero_vadd x := by
    apply Subtype.ext
    change (0 : V) + (x : V) = (x : V)
    exact zero_add _
  add_vadd k₁ k₂ x := by
    apply Subtype.ext
    change ((k₁ : V) + (k₂ : V)) + (x : V) =
      (k₁ : V) + ((k₂ : V) + (x : V))
    exact add_assoc _ _ _

instance liftFiberVSub (A : V →L[ℂ] W) (y : W) : VSub A.ker (LiftFiber A y) where
  vsub x₁ x₂ := ⟨(x₁ : V) - (x₂ : V), by
    change A ((x₁ : V) - (x₂ : V)) = 0
    rw [map_sub, x₁.property, x₂.property, sub_self]⟩

instance liftFiberAddTorsor (A : V →L[ℂ] W) (y : W) [Nonempty (LiftFiber A y)] :
    AddTorsor A.ker (LiftFiber A y) where
  vsub_vadd' x₁ x₂ := by
    apply Subtype.ext
    change ((x₁ : V) - (x₂ : V)) + (x₂ : V) = (x₁ : V)
    exact sub_add_cancel _ _
  vadd_vsub' k x := by
    apply Subtype.ext
    change ((k : V) + (x : V) - (x : V)) = (k : V)
    exact add_sub_cancel_right _ _

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem liftFiber_nonempty_iff (A : V →L[ℂ] W) (y : W) :
    Nonempty (LiftFiber A y) ↔ y ∈ A.range := by
  constructor
  · rintro ⟨x⟩
    exact ⟨x, x.property⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, hx⟩⟩

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem liftFiber_isEmpty_iff (A : V →L[ℂ] W) (y : W) :
    IsEmpty (LiftFiber A y) ↔ y ∉ A.range := by
  rw [← not_iff_not]
  simp only [not_not, not_isEmpty_iff]
  exact liftFiber_nonempty_iff A y

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem liftFiber_existsUnique_of_bijective (A : V →L[ℂ] W)
    (hA : Function.Bijective A) (y : W) : ∃! x : V, A x = y := by
  obtain ⟨x, hx⟩ := hA.2 y
  exact ⟨x, hx, fun z hz => hA.1 (hz.trans hx.symm)⟩

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem liftFiber_kernel_torsor_exact (A : V →L[ℂ] W) (y : W)
    (x0 : LiftFiber A y) (x : LiftFiber A y) :
    ∃! k : A.ker, k +ᵥ x0 = x := by
  letI : Nonempty (LiftFiber A y) := ⟨x0⟩
  exact ⟨x -ᵥ x0, vsub_vadd x x0, fun k hk => by
    rw [← vadd_right_cancel_iff (p := x0), hk, vsub_vadd]⟩

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem gramOperator_leftUnitary_invariant (U : W ≃ₗᵢ[ℂ] W) (A : V →L[ℂ] W) :
    gramOperator ((U : W →L[ℂ] W).comp A) = gramOperator A := by
  ext x
  simp only [gramOperator, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply]
  have hU :
      ContinuousLinearMap.adjoint (U : W →L[ℂ] W) ∘L (U : W →L[ℂ] W) = 1 := by
    exact U.toLinearIsometry.adjoint_comp_self
  have hpoint := DFunLike.congr_fun hU (A x)
  exact congrArg A.adjoint (by simp_all)

/-- Keeping the source law alongside its positive shadow loses no information. -/
def lawGramPair (A : V →L[ℂ] W) : (V →L[ℂ] W) × (V →L[ℂ] V) :=
  (A, gramOperator A)

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
@[simp] theorem lawGramPair_fst (A : V →L[ℂ] W) :
    (lawGramPair A).1 = A := rfl

omit [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] in
theorem lawGramPair_injective :
    Function.Injective (lawGramPair : (V →L[ℂ] W) →
      (V →L[ℂ] W) × (V →L[ℂ] V)) := by
  intro A B h
  exact congrArg Prod.fst h

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
theorem det_left_comp (U A : V →L[ℂ] V) :
    (U.comp A).det = U.det * A.det := by
  exact LinearMap.det_comp U.toLinearMap A.toLinearMap

def unitaryOfNormOne (c : ℂ) (hc : ‖c‖ = 1) : unitary ℂ :=
  ⟨c, by
    rw [Unitary.mem_iff]
    change (starRingEnd ℂ) c * c = 1 ∧ c * (starRingEnd ℂ) c = 1
    rw [Complex.conj_mul', Complex.mul_conj', hc]
    norm_num⟩

def scalarPhaseIsometry (c : ℂ) (hc : ‖c‖ = 1) : V ≃ₗᵢ[ℂ] V :=
  unitaryOfNormOne c hc • LinearIsometryEquiv.refl ℂ V

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
@[simp] theorem scalarPhaseIsometry_apply (c : ℂ) (hc : ‖c‖ = 1) (x : V) :
    scalarPhaseIsometry c hc x = c • x := rfl

omit [FiniteDimensional ℂ V] in
theorem scalarPhase_gram_invariant (c : ℂ) (hc : ‖c‖ = 1) (A : V →L[ℂ] V) :
    gramOperator (((scalarPhaseIsometry c hc : V ≃ₗᵢ[ℂ] V) : V →L[ℂ] V).comp A) =
      gramOperator A :=
  gramOperator_leftUnitary_invariant (scalarPhaseIsometry c hc) A

omit [CompleteSpace V] [FiniteDimensional ℂ V] in
theorem scalarPhase_det (c : ℂ) (hc : ‖c‖ = 1) (A : V →L[ℂ] V) :
    ((((scalarPhaseIsometry c hc : V ≃ₗᵢ[ℂ] V) : V →L[ℂ] V).comp A).det) =
      c ^ Module.finrank ℂ V * A.det := by
  rw [det_left_comp]
  have hscalar :
      ((scalarPhaseIsometry c hc : V ≃ₗᵢ[ℂ] V) : V →L[ℂ] V).toLinearMap =
        c • (LinearMap.id : V →ₗ[ℂ] V) := by
    ext x
    simp
  rw [ContinuousLinearMap.det, hscalar, LinearMap.det_smul, LinearMap.det_id, mul_one]

omit [FiniteDimensional ℂ V] in
theorem exists_same_gram_different_det (A : V →L[ℂ] V)
    (hn : 0 < Module.finrank ℂ V) (hdet : A.det ≠ 0) :
    ∃ U : V ≃ₗᵢ[ℂ] V,
      gramOperator ((U : V →L[ℂ] V).comp A) = gramOperator A ∧
      (((U : V →L[ℂ] V).comp A).det ≠ A.det) := by
  let n : ℕ := Module.finrank ℂ V
  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / (2 * n : ℕ))
  have htwo_n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn.ne'
  have hroot : IsPrimitiveRoot c (2 * n) := by
    simpa only [c] using Complex.isPrimitiveRoot_exp (2 * n) htwo_n
  have hc : ‖c‖ = 1 := hroot.norm'_eq_one htwo_n
  have hpow : c ^ n ≠ 1 := by
    apply hroot.pow_ne_one_of_pos_of_lt hn.ne'
    omega
  refine ⟨scalarPhaseIsometry c hc, scalarPhase_gram_invariant c hc A, ?_⟩
  rw [scalarPhase_det]
  intro heq
  apply hpow
  apply mul_right_cancel₀ hdet
  simpa only [one_mul] using heq

omit [CompleteSpace V] [CompleteSpace W] in
theorem inverseLawRelation_isClosed (A : V →L[ℂ] W) :
    IsClosed (inverseLawRelation A : Set (W × V)) :=
  (inverseLawRelation A).closed_of_finiteDimensional

def positiveInverseLift (A : ℝ → V →L[ℂ] W)
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (y : W) (t : ℝ) : V :=
  if ht : 0 < t then Classical.choose ((hinv ht).2 y) else 0

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem positiveInverseLift_spec (A : ℝ → V →L[ℂ] W)
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (y : W) {t : ℝ} (ht : 0 < t) :
    A t (positiveInverseLift A hinv y t) = y := by
  simp only [positiveInverseLift, ht, ↓reduceDIte]
  exact Classical.choose_spec ((hinv ht).2 y)

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem positiveInverseLift_unique (A : ℝ → V →L[ℂ] W)
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (y : W) {t : ℝ} (ht : 0 < t) (x : V) (hx : A t x = y) :
    x = positiveInverseLift A hinv y t := by
  apply (hinv ht).1
  rw [hx, positiveInverseLift_spec A hinv y ht]

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ V]
  [FiniteDimensional ℂ W] in
theorem positiveInverseLift_minimal (A : ℝ → V →L[ℂ] W)
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (y : W) {t : ℝ} (ht : 0 < t) (x : V) (hx : A t x = y) :
    ‖positiveInverseLift A hinv y t‖ ≤ ‖x‖ := by
  rw [positiveInverseLift_unique A hinv y ht x hx]

def positiveInverseLiftCost (A : ℝ → V →L[ℂ] W)
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (y : W) (t : ℝ) : ℝ :=
  ‖positiveInverseLift A hinv y t‖ ^ (2 : ℕ)

omit [CompleteSpace V] [CompleteSpace W] [FiniteDimensional ℂ W] in
theorem positiveInverseLiftCost_tendsto_atTop
    {A : ℝ → V →L[ℂ] W}
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (A 0)))
    {y : W} (hy : y ∉ (A 0).range) :
    Tendsto (positiveInverseLiftCost A hinv y) (𝓝[>] (0 : ℝ)) atTop := by
  apply inverseLiftCost_tendsto_atTop hA
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact positiveInverseLift_spec A hinv y ht
  · exact hy

/-- All five wall shadows, topological relation limit, exact inverse cost, and wall rank synchronize
for one finite norm-continuous law family. -/
theorem finiteLawRelationWall_fiveShadows
    {A : ℝ → V →L[ℂ] W} {r : ℕ}
    (hA : Tendsto A (𝓝[>] (0 : ℝ)) (𝓝 (A 0)))
    (hinv : ∀ {t : ℝ}, 0 < t → Function.Bijective (A t))
    (hrank : Module.finrank ℂ (A 0).ker = r) (hr : 0 < r) :
    Module.finrank ℂ (A 0).ker = r ∧
    0 < r ∧
    (gramOperator (A 0)).IsPositive ∧
    Module.finrank ℂ (gramOperator (A 0)).ker = r ∧
    (∀ t : ℝ, (gramOperator (A t)).det = (((A t).normDet ^ (2 : ℕ) : ℝ) : ℂ)) ∧
    Tendsto (fun t => (A t).normDet) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun t => (gramOperator (A t)).det) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
    Tendsto (fun t => inverseGraphGrassmannian (A t)) (𝓝[>] (0 : ℝ))
      (𝓝 (inverseGraphGrassmannian (A 0))) ∧
    linearRelationDomain (inverseLawRelation (A 0)) = (A 0).range ∧
    linearRelationMultivalued (inverseLawRelation (A 0)) = (A 0).ker ∧
    IsClosed (inverseLawRelation (A 0) : Set (W × V)) ∧
    ∀ y : W, y ∉ (A 0).range →
      Tendsto (positiveInverseLiftCost A hinv y) (𝓝[>] (0 : ℝ)) atTop := by
  have hker : (A 0).ker ≠ ⊥ := by
    intro hbot
    rw [hbot] at hrank
    have hrzero : r = 0 := by simpa using hrank.symm
    omega
  exact ⟨hrank, hr, gramOperator_isPositive (A 0),
    (gramOperator_nullity (A 0)).trans hrank,
    fun t => gramOperator_det_eq_normDet_sq (A t),
    normDet_tendsto_zero_of_tendsto_of_ker_ne_bot hA hker,
    gramDet_tendsto_zero_of_tendsto_of_ker_ne_bot hA hker,
    inverseGraphGrassmannian_tendsto hA,
    inverseLawRelation_domain (A 0), inverseLawRelation_multivalued (A 0),
    inverseLawRelation_isClosed (A 0),
    fun y hy => positiveInverseLiftCost_tendsto_atTop hinv hA hy⟩

end Hilbert

/-! Sharp one-port normal form. -/

def onePortWeight (n : ℕ) (t : ℂ) (i : Fin (n + 1)) : ℂ :=
  if i = 0 then t else 1

def onePortMatrix (n : ℕ) (t : ℂ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (onePortWeight n t)

def onePortLinearMap (n : ℕ) (t : ℂ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  Matrix.toLin' (onePortMatrix n t)

theorem onePortLinearMap_apply (n : ℕ) (t : ℂ) (x : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    onePortLinearMap n t x i = if i = 0 then t * x i else x i := by
  simp [onePortLinearMap, onePortMatrix, onePortWeight, Matrix.mulVec_diagonal]

theorem onePortMatrix_det (n : ℕ) (t : ℂ) :
    (onePortMatrix n t).det = t := by
  simp [onePortMatrix, onePortWeight, Matrix.det_diagonal]

theorem onePortMatrix_gram (n : ℕ) (t : ℝ) :
    Matrix.conjTranspose (onePortMatrix n (t : ℂ)) * onePortMatrix n (t : ℂ) =
      onePortMatrix n ((t ^ (2 : ℕ) : ℝ) : ℂ) := by
  simp only [onePortMatrix, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hi : i = 0
  · subst i
    simp [onePortWeight, pow_two]
  · simp [onePortWeight, hi]

theorem onePortLinearMap_ker_zero (n : ℕ) :
    (onePortLinearMap n 0).ker =
      LinearMap.range (LinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0) := by
  rw [onePortLinearMap, onePortMatrix, Matrix.ker_diagonal_toLin']
  simp [onePortWeight]

theorem onePortLinearMap_nullity (n : ℕ) :
    Module.finrank ℂ (onePortLinearMap n 0).ker = 1 := by
  rw [onePortLinearMap_ker_zero]
  have hf : Function.Injective
      (LinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0) := by
    intro a b h
    change (Pi.single 0 a : Fin (n + 1) → ℂ) =
      (Pi.single 0 b : Fin (n + 1) → ℂ) at h
    exact Pi.single_injective 0 h
  have hfin := (LinearEquiv.ofInjective
    (LinearMap.single ℂ (fun _ : Fin (n + 1) => ℂ) 0) hf).finrank_eq
  simpa only [Module.finrank_self] using hfin.symm

def onePortBasisVector (n : ℕ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  EuclideanSpace.single 0 1

def onePortInverseLift (n : ℕ) (t : ℂ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  EuclideanSpace.single 0 t⁻¹

def onePortLaw (n : ℕ) (t : ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (n + 1)) :=
  (Matrix.toEuclideanLin (onePortMatrix n t)).toContinuousLinearMap

theorem onePortInverseLift_exact (n : ℕ) {t : ℂ} (ht : t ≠ 0) :
    onePortLaw n t (onePortInverseLift n t) = onePortBasisVector n := by
  apply PiLp.ext
  intro i
  by_cases hi : i = 0
  · subst i
    simp [onePortLaw, onePortInverseLift, onePortBasisVector,
      onePortMatrix, onePortWeight, ht]
  · simp [onePortLaw, onePortInverseLift, onePortBasisVector,
      onePortMatrix, onePortWeight, hi]

theorem onePortInverseLift_cost (n : ℕ) (t : ℂ) :
    ‖onePortInverseLift n t‖ ^ (2 : ℕ) = ‖t‖⁻¹ ^ (2 : ℕ) := by
  simp [onePortInverseLift, norm_inv]

end
end GaloisForLFunctions.HTGeometry
