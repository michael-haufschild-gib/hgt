import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Tactic

/-!
# Normed intervention two-fields and curvature--filling selection

A normed intervention two-field is a bounded two-term presentation

`C₂ --∂₂--> C₁ --q--> O`

with `q ∂₂ = 0`.  Elements of `C₁` are signed intervention histories, elements of `C₂` are legal
rewrite fillings, and `q` is an observer.  A scalar current `J` has curvature `J ∂₂`.

The main law is exact:

`n J(z) = (J ∂₂)(a) + J(r)` whenever `n z = ∂₂ a + r`.

It yields a coordinate-free norm budget.  A nonzero current forces linear curvature-plus-residual
work along every repeated filling; cofinally sublinear work selects zero current.  Morphisms of
two-fields transport fillings, observer closure, currents, and curvature, so the conservation law
is independent of a route representation.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u₂ u₁ uo v₂ v₁ vo w₂ w₁ wo

/-- A normed presentation of legal two-dimensional rewrites of intervention histories. -/
structure NormedInterventionTwoField
    (C₂ : Type u₂) (C₁ : Type u₁) (O : Type uo)
    [NormedAddCommGroup C₂] [NormedSpace ℝ C₂]
    [NormedAddCommGroup C₁] [NormedSpace ℝ C₁]
    [NormedAddCommGroup O] [NormedSpace ℝ O] where
  /-- Boundary history changed by a legal rewrite. -/
  boundary : C₂ →L[ℝ] C₁
  /-- Observable shadow of a history. -/
  observer : C₁ →L[ℝ] O
  /-- Legal rewrites are information-neutral for the observer. -/
  observer_boundary : observer.comp boundary = 0

namespace NormedInterventionTwoField

variable {C₂ : Type u₂} {C₁ : Type u₁} {O : Type uo}
    [NormedAddCommGroup C₂] [NormedSpace ℝ C₂]
    [NormedAddCommGroup C₁] [NormedSpace ℝ C₁]
    [NormedAddCommGroup O] [NormedSpace ℝ O]

/-- Curvature is the action of a history current on legal rewrite boundaries. -/
def curvature (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ) : C₂ →L[ℝ] ℝ :=
  J.comp P.boundary

/-- A history closes after passage to the observer. -/
def ObserverClosed (P : NormedInterventionTwoField C₂ C₁ O) (z : C₁) : Prop :=
  P.observer z = 0

/-- The chosen current still detects an observer-closed history upstairs. -/
def CurrentOpenLift (P : NormedInterventionTwoField C₂ C₁ O)
    (J : C₁ →L[ℝ] ℝ) (z : C₁) : Prop :=
  P.ObserverClosed z ∧ J z ≠ 0

/-- An `n`-fold history equals a legal two-dimensional filling plus an unresolved residual. -/
def FormationFilling (P : NormedInterventionTwoField C₂ C₁ O)
    (z : C₁) (n : ℕ) (a : C₂) (r : C₁) : Prop :=
  (n : ℝ) • z = P.boundary a + r

/-- The observer kills every individual legal rewrite boundary. -/
theorem observer_boundary_apply (P : NormedInterventionTwoField C₂ C₁ O) (a : C₂) :
    P.observer (P.boundary a) = 0 := by
  have h := congrArg (fun T : C₂ →L[ℝ] O => T a) P.observer_boundary
  simpa using h

/-- **Curvature--filling conservation.** Repeated current is exactly integrated curvature plus
unresolved residual current. -/
theorem formationFilling_current_conservation
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ)
    {z : C₁} {n : ℕ} {a : C₂} {r : C₁} (h : P.FormationFilling z n a r) :
    (n : ℝ) * J z = P.curvature J a + J r := by
  calc
    (n : ℝ) * J z = J ((n : ℝ) • z) := by simp
    _ = J (P.boundary a + r) := by rw [h]
    _ = P.curvature J a + J r := by simp [curvature]

/-- A filling of an observer-closed history can leave only an observer-closed residual. -/
theorem formationFilling_residual_observerClosed
    (P : NormedInterventionTwoField C₂ C₁ O)
    {z : C₁} {n : ℕ} {a : C₂} {r : C₁}
    (hz : P.ObserverClosed z) (h : P.FormationFilling z n a r) :
    P.ObserverClosed r := by
  have hq := congrArg P.observer h
  simp only [map_smul, map_add, observer_boundary_apply] at hq
  simp only [ObserverClosed] at hz ⊢
  rw [hz, smul_zero] at hq
  simpa using hq.symm

/-- **Curvature--filling budget.** Operator norms convert exact conservation into the complete
positive action bound. -/
theorem formationFilling_current_budget
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ)
    {z : C₁} {n : ℕ} {a : C₂} {r : C₁} (h : P.FormationFilling z n a r) :
    (n : ℝ) * ‖J z‖ ≤ ‖P.curvature J‖ * ‖a‖ + ‖J‖ * ‖r‖ := by
  have hc := P.formationFilling_current_conservation J h
  calc
    (n : ℝ) * ‖J z‖ = ‖(n : ℝ) * J z‖ := by
      rw [norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    _ = ‖P.curvature J a + J r‖ := congrArg norm hc
    _ ≤ ‖P.curvature J a‖ + ‖J r‖ := norm_add_le _ _
    _ ≤ ‖P.curvature J‖ * ‖a‖ + ‖J‖ * ‖r‖ :=
      add_le_add ((P.curvature J).le_opNorm a) (J.le_opNorm r)

/-- **Open-lift properness.** Every filling of a nonzero hidden current pays linearly in winding. -/
theorem currentOpenLift_forces_linear_fillingBudget
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ)
    {z : C₁} (hopen : P.CurrentOpenLift J z)
    {n : ℕ} {a : C₂} {r : C₁} (h : P.FormationFilling z n a r) :
    0 < ‖J z‖ ∧
      (n : ℝ) * ‖J z‖ ≤ ‖P.curvature J‖ * ‖a‖ + ‖J‖ * ‖r‖ := by
  exact ⟨norm_pos_iff.mpr hopen.2, P.formationFilling_current_budget J h⟩

/-- Precomposition by a surjective linear isometry preserves the operator norm of a scalar
current. -/
theorem norm_comp_linearIsometryEquiv
    {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (K : F →L[ℝ] ℝ) :
    ‖K.comp e.toLinearIsometry.toContinuousLinearMap‖ = ‖K‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
    intro x
    calc
      ‖K (e x)‖ ≤ ‖K‖ * ‖e x‖ := K.le_opNorm _
      _ = ‖K‖ * ‖x‖ := by rw [e.norm_map]
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro y
    calc
      ‖K y‖ = ‖(K.comp e.toLinearIsometry.toContinuousLinearMap) (e.symm y)‖ := by simp
      _ ≤ ‖K.comp e.toLinearIsometry.toContinuousLinearMap‖ * ‖e.symm y‖ :=
        (K.comp e.toLinearIsometry.toContinuousLinearMap).le_opNorm _
      _ = ‖K.comp e.toLinearIsometry.toContinuousLinearMap‖ * ‖y‖ := by
        rw [e.symm.norm_map]

/-- A route representation is a bounded morphism of intervention presentations. -/
structure Hom
    {D₂ : Type v₂} {D₁ : Type v₁} {U : Type vo}
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P : NormedInterventionTwoField C₂ C₁ O)
    (Q : NormedInterventionTwoField D₂ D₁ U) where
  /-- Representation of legal rewrite chains. -/
  faceMap : C₂ →L[ℝ] D₂
  /-- Representation of intervention histories. -/
  historyMap : C₁ →L[ℝ] D₁
  /-- Representation of observer reports. -/
  observerMap : O →L[ℝ] U
  /-- Route execution commutes with legal rewrite boundary. -/
  boundary_natural : historyMap.comp P.boundary = Q.boundary.comp faceMap
  /-- Route execution commutes with observation. -/
  observer_natural : observerMap.comp P.observer = Q.observer.comp historyMap

namespace Hom

variable {D₂ : Type v₂} {D₁ : Type v₁} {U : Type vo}
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    {P : NormedInterventionTwoField C₂ C₁ O}
    {Q : NormedInterventionTwoField D₂ D₁ U}

/-- Pull a route current back to the common intervention presentation. -/
def pullbackCurrent (A : P.Hom Q) (K : D₁ →L[ℝ] ℝ) : C₁ →L[ℝ] ℝ :=
  K.comp A.historyMap

/-- Pointwise boundary naturality. -/
theorem boundary_natural_apply (A : P.Hom Q) (a : C₂) :
    A.historyMap (P.boundary a) = Q.boundary (A.faceMap a) := by
  have h := congrArg (fun T : C₂ →L[ℝ] D₁ => T a) A.boundary_natural
  simpa using h

/-- Pointwise observer naturality. -/
theorem observer_natural_apply (A : P.Hom Q) (z : C₁) :
    A.observerMap (P.observer z) = Q.observer (A.historyMap z) := by
  have h := congrArg (fun T : C₁ →L[ℝ] U => T z) A.observer_natural
  simpa using h

/-- **Curvature naturality.** Route curvature is exactly represented source curvature. -/
theorem curvature_natural (A : P.Hom Q) (K : D₁ →L[ℝ] ℝ) :
    P.curvature (A.pullbackCurrent K) = (Q.curvature K).comp A.faceMap := by
  ext a
  change K (A.historyMap (P.boundary a)) = K (Q.boundary (A.faceMap a))
  exact congrArg K (A.boundary_natural_apply a)

/-- Legal fillings transport through every route representation. -/
theorem formationFilling_map (A : P.Hom Q)
    {z : C₁} {n : ℕ} {a : C₂} {r : C₁} (h : P.FormationFilling z n a r) :
    Q.FormationFilling (A.historyMap z) n (A.faceMap a) (A.historyMap r) := by
  have hm := congrArg A.historyMap h
  change (n : ℝ) • A.historyMap z = Q.boundary (A.faceMap a) + A.historyMap r
  rw [← A.boundary_natural_apply a]
  simpa using hm

/-- Observer closure transports through every route representation. -/
theorem observerClosed_map (A : P.Hom Q) {z : C₁} (hz : P.ObserverClosed z) :
    Q.ObserverClosed (A.historyMap z) := by
  simp only [ObserverClosed] at hz ⊢
  rw [← A.observer_natural_apply z, hz, map_zero]

/-- Identity representation of an intervention two-field. -/
def identity (P : NormedInterventionTwoField C₂ C₁ O) : P.Hom P where
  faceMap := ContinuousLinearMap.id ℝ C₂
  historyMap := ContinuousLinearMap.id ℝ C₁
  observerMap := ContinuousLinearMap.id ℝ O
  boundary_natural := by ext; rfl
  observer_natural := by ext; rfl

variable {E₂ : Type w₂} {E₁ : Type w₁} {V : Type wo}
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {R : NormedInterventionTwoField E₂ E₁ V}

/-- Serial route representations compose. -/
def comp (B : Q.Hom R) (A : P.Hom Q) : P.Hom R where
  faceMap := B.faceMap.comp A.faceMap
  historyMap := B.historyMap.comp A.historyMap
  observerMap := B.observerMap.comp A.observerMap
  boundary_natural := by
    ext a
    simp only [ContinuousLinearMap.comp_apply]
    rw [A.boundary_natural_apply, B.boundary_natural_apply]
  observer_natural := by
    ext z
    simp only [ContinuousLinearMap.comp_apply]
    rw [A.observer_natural_apply, B.observer_natural_apply]

/-- Pulling back a current through a serial route is associative. -/
theorem pullbackCurrent_comp (B : Q.Hom R) (A : P.Hom Q) (K : E₁ →L[ℝ] ℝ) :
    (B.comp A).pullbackCurrent K = A.pullbackCurrent (B.pullbackCurrent K) := by
  ext z
  rfl

end Hom

/-- An isometric route gauge between two intervention presentations. -/
structure Gauge
    {D₂ : Type v₂} {D₁ : Type v₁} {U : Type vo}
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P : NormedInterventionTwoField C₂ C₁ O)
    (Q : NormedInterventionTwoField D₂ D₁ U) where
  /-- Isometric gauge on legal rewrite chains. -/
  faceEquiv : C₂ ≃ₗᵢ[ℝ] D₂
  /-- Isometric gauge on intervention histories. -/
  historyEquiv : C₁ ≃ₗᵢ[ℝ] D₁
  /-- Isometric gauge on observer reports. -/
  observerEquiv : O ≃ₗᵢ[ℝ] U
  /-- The gauge respects legal rewrite boundary. -/
  boundary_natural :
    historyEquiv.toLinearIsometry.toContinuousLinearMap.comp P.boundary =
      Q.boundary.comp faceEquiv.toLinearIsometry.toContinuousLinearMap
  /-- The gauge respects observation. -/
  observer_natural :
    observerEquiv.toLinearIsometry.toContinuousLinearMap.comp P.observer =
      Q.observer.comp historyEquiv.toLinearIsometry.toContinuousLinearMap

namespace Gauge

variable {D₂ : Type v₂} {D₁ : Type v₁} {U : Type vo}
    [NormedAddCommGroup D₂] [NormedSpace ℝ D₂]
    [NormedAddCommGroup D₁] [NormedSpace ℝ D₁]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    {P : NormedInterventionTwoField C₂ C₁ O}
    {Q : NormedInterventionTwoField D₂ D₁ U}

/-- Forget isometry while retaining the underlying bounded route representation. -/
def toHom (A : P.Gauge Q) : P.Hom Q where
  faceMap := A.faceEquiv.toLinearIsometry.toContinuousLinearMap
  historyMap := A.historyEquiv.toLinearIsometry.toContinuousLinearMap
  observerMap := A.observerEquiv.toLinearIsometry.toContinuousLinearMap
  boundary_natural := A.boundary_natural
  observer_natural := A.observer_natural

/-- Pull back a current through an isometric route gauge. -/
def pullbackCurrent (A : P.Gauge Q) (K : D₁ →L[ℝ] ℝ) : C₁ →L[ℝ] ℝ :=
  A.toHom.pullbackCurrent K

/-- Gauge curvature is the exact pullback of target curvature. -/
theorem curvature_natural (A : P.Gauge Q) (K : D₁ →L[ℝ] ℝ) :
    P.curvature (A.pullbackCurrent K) =
      (Q.curvature K).comp A.faceEquiv.toLinearIsometry.toContinuousLinearMap :=
  A.toHom.curvature_natural K

/-- Isometric gauge transport preserves current norm. -/
theorem norm_pullbackCurrent (A : P.Gauge Q) (K : D₁ →L[ℝ] ℝ) :
    ‖A.pullbackCurrent K‖ = ‖K‖ :=
  norm_comp_linearIsometryEquiv A.historyEquiv K

/-- Isometric gauge transport preserves curvature norm. -/
theorem norm_curvature (A : P.Gauge Q) (K : D₁ →L[ℝ] ℝ) :
    ‖P.curvature (A.pullbackCurrent K)‖ = ‖Q.curvature K‖ := by
  rw [A.curvature_natural K]
  exact norm_comp_linearIsometryEquiv A.faceEquiv (Q.curvature K)

/-- Formation fillings transport through an isometric route gauge. -/
theorem formationFilling_map (A : P.Gauge Q)
    {z : C₁} {n : ℕ} {a : C₂} {r : C₁} (h : P.FormationFilling z n a r) :
    Q.FormationFilling (A.historyEquiv z) n (A.faceEquiv a) (A.historyEquiv r) :=
  A.toHom.formationFilling_map h

/-- Observer closure transports through an isometric route gauge. -/
theorem observerClosed_map (A : P.Gauge Q) {z : C₁} (hz : P.ObserverClosed z) :
    Q.ObserverClosed (A.historyEquiv z) :=
  A.toHom.observerClosed_map hz

/-- **Gauge-neutral action.** Complete curvature-plus-residual work is unchanged by every
isometric representation of the intervention two-field. -/
theorem fillingBudget_eq (A : P.Gauge Q) (K : D₁ →L[ℝ] ℝ) (a : C₂) (r : C₁) :
    ‖P.curvature (A.pullbackCurrent K)‖ * ‖a‖ + ‖A.pullbackCurrent K‖ * ‖r‖ =
      ‖Q.curvature K‖ * ‖A.faceEquiv a‖ + ‖K‖ * ‖A.historyEquiv r‖ := by
  rw [A.norm_curvature K, A.norm_pullbackCurrent K, A.faceEquiv.norm_map,
    A.historyEquiv.norm_map]

end Gauge

/-- **Cofinal sublinear selection.** If arbitrarily late positive fillings have arbitrarily small
curvature-plus-residual work per winding, the current is neutral. -/
theorem cofinal_sublinear_filling_selects_zero
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ) (z : C₁)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, ∃ a : C₂, ∃ r : C₁,
      N ≤ n ∧ 0 < n ∧ P.FormationFilling z n a r ∧
        ‖P.curvature J‖ * ‖a‖ + ‖J‖ * ‖r‖ < (n : ℝ) * ε) :
    J z = 0 := by
  by_contra hz
  have hpos : 0 < ‖J z‖ := norm_pos_iff.mpr hz
  obtain ⟨n, a, r, _hnN, hn, hfill, hlt⟩ := hsub (‖J z‖ / 2) (half_pos hpos) 0
  have hle := P.formationFilling_current_budget J hfill
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-- One positive exact filling kills every flat current on that history. -/
theorem flat_exact_filling_selects_zero
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ)
    {z : C₁} {n : ℕ} {a : C₂} (hn : 0 < n)
    (hflat : P.curvature J = 0) (hfill : P.FormationFilling z n a 0) :
    J z = 0 := by
  have hc := P.formationFilling_current_conservation J hfill
  rw [hflat] at hc
  simp only [zero_apply, add_zero, map_zero] at hc
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_eq_zero.mp hc).resolve_left hnreal

/-- Full capstone: cofinal sublinear formation selects zero, while every residual from the closed
history remains closed in the observer. -/
theorem normedInterventionTwoField_selection_capstone
    (P : NormedInterventionTwoField C₂ C₁ O) (J : C₁ →L[ℝ] ℝ) (z : C₁)
    (hz : P.ObserverClosed z)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, ∃ a : C₂, ∃ r : C₁,
      N ≤ n ∧ 0 < n ∧ P.FormationFilling z n a r ∧
        ‖P.curvature J‖ * ‖a‖ + ‖J‖ * ‖r‖ < (n : ℝ) * ε) :
    J z = 0 ∧
      ∀ n : ℕ, ∀ a : C₂, ∀ r : C₁, P.FormationFilling z n a r → P.ObserverClosed r := by
  constructor
  · exact P.cofinal_sublinear_filling_selects_zero J z hsub
  · intro n a r hfill
    exact P.formationFilling_residual_observerClosed hz hfill

end NormedInterventionTwoField

end

end GaloisForLFunctions.HTGeometry
