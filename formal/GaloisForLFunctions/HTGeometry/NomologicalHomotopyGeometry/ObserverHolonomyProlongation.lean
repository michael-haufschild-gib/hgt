import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Fintype.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Homotopy.Lifting

/-!
# Observer component boundary and prolongation horizon

This file separates three invariants which the paper card deliberately does not identify:

* the endpoint component of a lifted observer loop;
* vertical holonomy supplied by equivariant principal transport;
* infinitesimal loss forced by finite observer rank.

The component theorem is first proved for an arbitrary actual lift.  It is then instantiated with
mathlib's path lifting and homotopy-invariant monodromy for covering maps.  Principal transport,
cost, and finite-rank statements are kept in independent sections, matching their distinct
hypotheses in the paper theorem.
-/

noncomputable section

namespace HTGeometry.NomologicalHomotopyGeometry.ObserverHolonomyProlongation

open Filter Function Set Topology
open scoped ENNReal

universe u v w z

/-! ## Component boundary of an actual lifted loop -/

namespace ComponentBoundary

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) {x : X} {y : Y}

/-- The strict fibre over `y`; for a fibration it represents the pointed homotopy fibre. -/
abbrev Fiber (y : Y) := p ⁻¹' ({y} : Set Y)

/-- Distinguished point of the fibre. -/
def basePoint (hx : p x = y) : Fiber p y := ⟨x, hx⟩

/-- An actual lift of a based loop, with its projection equation recorded pointwise. -/
structure LiftedLoop (hx : p x = y) (γ : Path y y) where
  endpoint : X
  path : Path x endpoint
  projects : ∀ t, p (path t) = γ t

variable {p}

/-- Endpoint of a lifted loop, regarded as a point of the fibre. -/
def LiftedLoop.fiberEndpoint {γ : Path y y} {hx : p x = y}
    (L : LiftedLoop p hx γ) : Fiber p y :=
  ⟨L.endpoint, by
    change p L.endpoint = y
    calc
      p L.endpoint = p (L.path 1) := congrArg p L.path.target.symm
      _ = γ 1 := L.projects 1
      _ = y := γ.target⟩

/-- Connecting component class: the component of the lifted endpoint. -/
def boundary {γ : Path y y} {hx : p x = y} (L : LiftedLoop p hx γ) :
    ZerothHomotopy (Fiber p y) :=
  ZerothHomotopy.mk L.fiberEndpoint

/-- A lifted loop closes by a path inside the fibre exactly when its endpoint component is the
base component. -/
theorem boundary_eq_base_iff_fiber_path {γ : Path y y} {hx : p x = y}
    (L : LiftedLoop p hx γ) :
    boundary L = ZerothHomotopy.mk (basePoint p hx) ↔
      Joined L.fiberEndpoint (basePoint p hx) := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Expanded existential-path form of the component boundary criterion. -/
theorem boundary_eq_base_iff_exists_closure {γ : Path y y} {hx : p x = y}
    (L : LiftedLoop p hx γ) :
    boundary L = ZerothHomotopy.mk (basePoint p hx) ↔
      Nonempty (Path L.fiberEndpoint (basePoint p hx)) :=
  boundary_eq_base_iff_fiber_path L

/-! ### Covering-map realization -/

variable (p)

/-- Canonical lifted loop supplied by the covering-space path-lifting theorem. -/
def coveringLiftedLoop (cov : IsCoveringMap p) (hx : p x = y) (γ : Path y y) :
    LiftedLoop p hx γ := by
  let h0 : γ 0 = p x := γ.source.trans hx.symm
  let Γ := cov.liftPath γ x h0
  exact
    { endpoint := Γ 1
      path := ⟨Γ, cov.liftPath_zero γ x h0, rfl⟩
      projects := fun t ↦ congrFun (cov.liftPath_lifts γ x h0) t }

/-- Covering-space lift endpoint lies in the fibre. -/
theorem coveringLiftedLoop_endpoint_mem (cov : IsCoveringMap p) (hx : p x = y)
    (γ : Path y y) :
    p (coveringLiftedLoop p cov hx γ).endpoint = y :=
  (coveringLiftedLoop p cov hx γ).fiberEndpoint.property

/-- Component boundary criterion specialized to the canonical covering-space lift. -/
theorem covering_boundary_eq_base_iff (cov : IsCoveringMap p) (hx : p x = y)
    (γ : Path y y) :
    boundary (coveringLiftedLoop p cov hx γ) =
        ZerothHomotopy.mk (basePoint p hx) ↔
      Nonempty (Path (coveringLiftedLoop p cov hx γ).fiberEndpoint (basePoint p hx)) :=
  boundary_eq_base_iff_exists_closure (coveringLiftedLoop p cov hx γ)

/-- Homotopy-invariant boundary on the fundamental group, using mathlib's descended monodromy. -/
def coveringBoundaryClass (cov : IsCoveringMap p) (e : Fiber p y)
    (γ : FundamentalGroup Y y) : ZerothHomotopy (Fiber p y) :=
  ZerothHomotopy.mk (cov.monodromy γ e)

/-- Exact closure criterion for the homotopy-invariant covering boundary. -/
theorem coveringBoundaryClass_eq_base_iff (cov : IsCoveringMap p) (e : Fiber p y)
    (γ : FundamentalGroup Y y) :
    coveringBoundaryClass p cov e γ = ZerothHomotopy.mk e ↔
      Joined (cov.monodromy γ e) e := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound h

/-- Monodromy of concatenated loop classes is iterated monodromy. -/
theorem covering_monodromy_mul (cov : IsCoveringMap p) (e : Fiber p y)
    (γ δ : FundamentalGroup Y y) :
    cov.monodromy (γ * δ) e = cov.monodromy γ (cov.monodromy δ e) := by
  simpa only [FundamentalGroup.mul_def] using cov.monodromy_trans_apply δ γ e

/-- For the identity observer, every loop has trivial component boundary. -/
def identityLiftedLoop {X : Type u} [TopologicalSpace X] {x : X} (γ : Path x x) :
    LiftedLoop (id : X → X) rfl γ where
  endpoint := x
  path := γ
  projects := fun _ ↦ rfl

theorem identity_boundary_trivial {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) :
    boundary (identityLiftedLoop γ) =
      ZerothHomotopy.mk (basePoint (id : X → X) rfl) :=
  rfl

end ComponentBoundary

/-! ## Principal transport and vertical holonomy -/

namespace PrincipalTransport

/-- A right torsor written explicitly in the convention used by principal bundles. -/
structure RightTorsor (G : Type u) (X : Type v) [Group G] where
  act : X → G → X
  act_one : ∀ x, act x 1 = x
  act_mul : ∀ x g h, act (act x g) h = act x (g * h)
  exists_act : ∀ x y, ∃ g, act x g = y
  act_injective : ∀ x, Function.Injective (act x)

variable {G : Type u} {X : Type v} {M : Type w}
  [Group G] [Monoid M] [MulAction M X]

/-- Unique vertical element carrying `x` to its transported endpoint. -/
def holonomy (T : RightTorsor G X) (x : X) (m : M) : G :=
  Classical.choose (T.exists_act x (m • x))

@[simp]
theorem act_holonomy (T : RightTorsor G X) (x : X) (m : M) :
    T.act x (holonomy T x m) = m • x :=
  Classical.choose_spec (T.exists_act x (m • x))

theorem holonomy_eq_of_act_eq (T : RightTorsor G X) (x : X) (m : M) (g : G)
    (h : T.act x g = m • x) : holonomy T x m = g := by
  apply T.act_injective x
  rw [act_holonomy, h]

/-- Equivariance and concatenation force repeated transport to advance through powers of one
vertical holonomy element. -/
theorem pow_smul_eq_act_holonomy_pow (T : RightTorsor G X)
    (equivariant : ∀ (m : M) (x : X) (g : G), m • T.act x g = T.act (m • x) g)
    (x : X) (m : M) :
    ∀ n : ℕ, m ^ n • x = T.act x (holonomy T x m ^ n) := by
  intro n
  induction n with
  | zero => simp [T.act_one]
  | succ n ih =>
      calc
        m ^ (n + 1) • x = m ^ n • (m • x) := by rw [pow_succ, mul_smul]
        _ = m ^ n • T.act x (holonomy T x m) := by rw [act_holonomy]
        _ = T.act (m ^ n • x) (holonomy T x m) :=
          equivariant _ _ _
        _ = T.act (T.act x (holonomy T x m ^ n)) (holonomy T x m) := by rw [ih]
        _ = T.act x (holonomy T x m ^ n * holonomy T x m) := T.act_mul _ _ _
        _ = T.act x (holonomy T x m ^ (n + 1)) := by rw [pow_succ]

/-- Holonomy of the `n`-fold repeated loop is the `n`th power of its holonomy. -/
theorem holonomy_pow (T : RightTorsor G X)
    (equivariant : ∀ (m : M) (x : X) (g : G), m • T.act x g = T.act (m • x) g)
    (x : X) (m : M) (n : ℕ) :
    holonomy T x (m ^ n) = holonomy T x m ^ n := by
  apply holonomy_eq_of_act_eq T
  exact (pow_smul_eq_act_holonomy_pow T equivariant x m n).symm

/-- Marked vertical endpoint cost.  Normalization at the identity is part of the constitutive data. -/
structure VerticalCost (G : Type u) [One G] where
  cost : G → ℝ≥0∞
  cost_one : cost 1 = 0

instance : CoeFun (VerticalCost G) (fun _ ↦ G → ℝ≥0∞) :=
  ⟨VerticalCost.cost⟩

/-- Observer endpoints remain over the basepoint when transport preserves the observer map. -/
theorem observer_recurrence {Y : Type z} (p : X → Y)
    (observer_invariant : ∀ (m : M) (z : X), p (m • z) = p z)
    {x : X} {y : Y} (hx : p x = y) (m : M) :
    ∀ n : ℕ, p (m ^ n • x) = y := by
  intro n
  exact (observer_invariant (m ^ n) x).trans hx

/-- Divergence of powers, supplied independently as a cost law, transfers exactly to costs of
repeated-loop holonomies. -/
theorem endpointCostDiverges (T : RightTorsor G X)
    (equivariant : ∀ (m : M) (x : X) (g : G), m • T.act x g = T.act (m • x) g)
    (c : VerticalCost G) (x : X) (m : M)
    (hdiv : Tendsto (fun n : ℕ ↦ c (holonomy T x m ^ n)) atTop atTop) :
    Tendsto (fun n : ℕ ↦ c (holonomy T x (m ^ n))) atTop atTop := by
  simpa only [holonomy_pow T equivariant x m] using hdiv

/-- Exact recurrence-with-divergent-cost theorem. -/
theorem recurrentWithDivergentCost {Y : Type z} (T : RightTorsor G X)
    (equivariant : ∀ (m : M) (x : X) (g : G), m • T.act x g = T.act (m • x) g)
    (p : X → Y) (observer_invariant : ∀ (m : M) (z : X), p (m • z) = p z)
    (c : VerticalCost G) {x : X} {y : Y} (hx : p x = y) (m : M)
    (hdiv : Tendsto (fun n : ℕ ↦ c (holonomy T x m ^ n)) atTop atTop) :
    (∀ n : ℕ, p (m ^ n • x) = y) ∧
      Tendsto (fun n : ℕ ↦ c (holonomy T x (m ^ n))) atTop atTop :=
  ⟨observer_recurrence p observer_invariant hx m,
    endpointCostDiverges T equivariant c x m hdiv⟩

/-- On a finite holonomy group every endpoint cost is bounded along powers, including powers of a
nonidentity element.  Thus open lift alone does not imply growing cost. -/
theorem finiteHolonomy_cost_bounded [Finite G] (c : VerticalCost G) (h : G) :
    ∃ C : ℝ≥0∞, ∀ n : ℕ, c (h ^ n) ≤ C := by
  obtain ⟨C, hC⟩ := Finite.exists_le c
  exact ⟨C, fun n ↦ hC (h ^ n)⟩

/-- Explicit nontrivial finite holonomy element. -/
theorem zmodTwo_has_nontrivial_holonomy :
    Multiplicative.ofAdd (1 : ZMod 2) ≠ 1 := by
  intro h
  have h' := congrArg Multiplicative.toAdd h
  norm_num at h'

end PrincipalTransport

/-! ## Finite observer horizon -/

namespace ProlongationHorizon

variable {K : Type u} [DivisionRing K]
  {V : Type v} {W : Type w} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Rank-nullity in witness form: an observer of smaller finite rank loses a nonzero direction. -/
theorem finiteObserverHorizon [FiniteDimensional K V] [FiniteDimensional K W]
    (d : V →ₗ[K] W) (h : Module.finrank K W < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ d v = 0 := by
  obtain ⟨v, hv, hv0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := d) h)
  exact ⟨v, hv0, hv⟩

/-- Product observer assembled from a finite family. -/
def productObserver {ι : Type z} (d : ι → V →ₗ[K] W) :
    V →ₗ[K] (ι → W) :=
  LinearMap.pi d

/-- Kernel of the product observer is the intersection of component kernels. -/
theorem ker_productObserver {ι : Type z} (d : ι → V →ₗ[K] W) :
    LinearMap.ker (productObserver d) = ⨅ i, LinearMap.ker (d i) :=
  LinearMap.ker_pi d

/-- A finite product observer loses a nonzero direction whenever total target dimension is smaller
than source dimension. -/
theorem finiteProductObserverHorizon {ι : Type z} [Fintype ι]
    {Wι : ι → Type w} [∀ i, AddCommGroup (Wι i)] [∀ i, Module K (Wι i)]
    [FiniteDimensional K V] [∀ i, FiniteDimensional K (Wι i)]
    (d : ∀ i, V →ₗ[K] Wι i)
    (h : (∑ i, Module.finrank K (Wι i)) < Module.finrank K V) :
    ∃ v : V, v ≠ 0 ∧ ∀ i, d i v = 0 := by
  have hdim : Module.finrank K (∀ i, Wι i) < Module.finrank K V := by
    simpa only [Module.finrank_pi_fintype] using h
  obtain ⟨v, hv0, hv⟩ := finiteObserverHorizon (LinearMap.pi d) hdim
  exact ⟨v, hv0, fun i ↦ congrFun hv i⟩

/-- If source prolongation rank tends to infinity while observer rank has a uniform finite bound,
then all sufficiently high orders have a nontrivial observer kernel. -/
theorem eventually_finiteObserverHorizon
    (Vn : ℕ → Type v) (Wn : ℕ → Type w)
    [∀ n, AddCommGroup (Vn n)] [∀ n, Module K (Vn n)]
    [∀ n, AddCommGroup (Wn n)] [∀ n, Module K (Wn n)]
    [∀ n, FiniteDimensional K (Vn n)] [∀ n, FiniteDimensional K (Wn n)]
    (d : ∀ n, Vn n →ₗ[K] Wn n) (D : ℕ)
    (hbound : ∀ n, Module.finrank K (Wn n) ≤ D)
    (hgrowth : Tendsto (fun n ↦ Module.finrank K (Vn n)) atTop atTop) :
    ∀ᶠ n in atTop, ∃ v : Vn n, v ≠ 0 ∧ d n v = 0 := by
  filter_upwards [Filter.tendsto_atTop.1 hgrowth (D + 1)] with n hn
  apply finiteObserverHorizon (d n)
  exact (hbound n).trans_lt (Nat.lt_of_succ_le hn)

/-- Finite-family version: a uniform bound on the sum of observer ranks forces a common lost
direction for all sufficiently high prolongation orders. -/
theorem eventually_finiteProductObserverHorizon {ι : Type z} [Fintype ι]
    (Vn : ℕ → Type v) (Wn : ℕ → ι → Type w)
    [∀ n, AddCommGroup (Vn n)] [∀ n, Module K (Vn n)]
    [∀ n i, AddCommGroup (Wn n i)] [∀ n i, Module K (Wn n i)]
    [∀ n, FiniteDimensional K (Vn n)] [∀ n i, FiniteDimensional K (Wn n i)]
    (d : ∀ n i, Vn n →ₗ[K] Wn n i) (D : ℕ)
    (hbound : ∀ n, (∑ i, Module.finrank K (Wn n i)) ≤ D)
    (hgrowth : Tendsto (fun n ↦ Module.finrank K (Vn n)) atTop atTop) :
    ∀ᶠ n in atTop, ∃ v : Vn n, v ≠ 0 ∧ ∀ i, d n i v = 0 := by
  filter_upwards [Filter.tendsto_atTop.1 hgrowth (D + 1)] with n hn
  apply finiteProductObserverHorizon (d n)
  exact (hbound n).trans_lt (Nat.lt_of_succ_le hn)

/-- Serial postprocessing cannot repair a direction already killed by an observer. -/
theorem serialObserver_preserves_loss
    {Z : Type z} [AddCommGroup Z] [Module K Z]
    (f : V →ₗ[K] W) (g : W →ₗ[K] Z) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp f) :=
  LinearMap.ker_le_ker_comp f g

/-- A genuinely new parallel coordinate can repair complete loss: `(0,id)` is injective although
its first component is the zero observer. -/
def parallelRepair : V →ₗ[K] V × V :=
  LinearMap.prod (0 : V →ₗ[K] V) LinearMap.id

theorem parallelRepair_injective : Function.Injective (parallelRepair (K := K) (V := V)) := by
  intro a b h
  exact congrArg Prod.snd h

/-! ### Hostile zero-observer model -/

/-- Order-`n` formal jets, used as an explicit unbounded finite-dimensional source tower. -/
abbrev FormalJet (K : Type u) (n : ℕ) := Fin n → K

theorem finrank_formalJet (n : ℕ) :
    Module.finrank K (FormalJet K n) = n := by
  simp [FormalJet]

/-- The point observer on formal jets. -/
def pointObserver (n : ℕ) : FormalJet K n →ₗ[K] (Fin 0 → K) := 0

theorem pointObserver_kernel (n : ℕ) :
    LinearMap.ker (pointObserver (K := K) n) = ⊤ := by
  simp [pointObserver]

/-- Formal-jet dimensions tend to infinity despite the zero-dimensional point observer. -/
theorem formalJet_finrank_tendsto :
    Tendsto (fun n ↦ Module.finrank K (FormalJet K n)) atTop atTop := by
  rw [show (fun n ↦ Module.finrank K (FormalJet K n)) = id from
    funext finrank_formalJet]
  exact Filter.tendsto_id

end ProlongationHorizon

/-! ## Independence of component boundary from connected vertical holonomy -/

namespace HostileModels

/-- A path in a discrete space has equal endpoints. -/
theorem joined_eq_of_discrete {A : Type u} [TopologicalSpace A] [DiscreteTopology A]
    {a b : A} (h : Joined a b) : a = b := by
  let γ := h.somePath
  have hc : γ 0 = γ 1 := PreconnectedSpace.constant inferInstance γ.continuous
  exact γ.source.symm.trans (hc.trans γ.target)

/-- Standard once-around loop in `U(1)`, obtained by projecting the interval `[0,2π]`. -/
def circleGeneratorLoop : Path (1 : Circle) 1 :=
  ((Path.segment (0 : ℝ) (2 * Real.pi)).map Circle.exp.continuous).cast (by simp) (by simp)

/-- Explicit lift of the circle generator from `0` to `2π`. -/
def circleGeneratorLift :
    ComponentBoundary.LiftedLoop (p := Circle.exp) (x := (0 : ℝ)) (y := (1 : Circle))
      (by simp) circleGeneratorLoop where
  endpoint := 2 * Real.pi
  path := Path.segment 0 (2 * Real.pi)
  projects := fun _ ↦ rfl

/-- The circle-generator lift has nontrivial component boundary in the discrete fibre of the
universal covering `ℝ → U(1)`. -/
theorem circleGenerator_boundary_nontrivial :
    ComponentBoundary.boundary circleGeneratorLift ≠
      ZerothHomotopy.mk
        (ComponentBoundary.basePoint Circle.exp (x := (0 : ℝ)) (y := (1 : Circle)) (by simp)) := by
  intro h
  have hj := (ComponentBoundary.boundary_eq_base_iff_fiber_path circleGeneratorLift).mp h
  letI : DiscreteTopology (ComponentBoundary.Fiber Circle.exp (1 : Circle)) :=
    (Circle.isCoveringMap_exp (1 : Circle)).discreteTopology_fiber
  have heq := joined_eq_of_discrete hj
  have hval := congrArg Subtype.val heq
  dsimp [circleGeneratorLift, ComponentBoundary.LiftedLoop.fiberEndpoint,
    ComponentBoundary.basePoint] at hval
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

/-- The same explicit model has both nonzero invariants: nontrivial global component boundary and
a nontrivial local tangent kernel for its zero one-dimensional observer differential. -/
theorem circleCover_with_loss_has_both_invariants :
    ComponentBoundary.boundary circleGeneratorLift ≠
        ZerothHomotopy.mk
          (ComponentBoundary.basePoint Circle.exp (x := (0 : ℝ)) (y := (1 : Circle)) (by simp)) ∧
      LinearMap.ker (0 : ℝ →ₗ[ℝ] (Fin 0 → ℝ)) ≠ ⊥ := by
  refine ⟨circleGenerator_boundary_nontrivial, ?_⟩
  apply LinearMap.ker_ne_bot_of_finrank_lt
  simp

/-- `U(1)` is path connected, so the component class of a nonidentity vertical element `-1` is
the base component even though the element itself is nonidentity.  This is the exact separation
between component boundary and connection holonomy used by the hostile model. -/
theorem circle_component_misses_nontrivial_holonomy :
    ZerothHomotopy.mk (-1 : Circle) = ZerothHomotopy.mk (1 : Circle) ∧
      (-1 : Circle) ≠ 1 := by
  constructor
  · exact Subsingleton.elim _ _
  · intro h
    have h' := congrArg Subtype.val h
    norm_num at h'

end HostileModels

end HTGeometry.NomologicalHomotopyGeometry.ObserverHolonomyProlongation
