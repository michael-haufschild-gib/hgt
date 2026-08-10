import Mathlib

/-!
# Initial-execution symmetry inheritance and anomaly necessity

An initial object inherits every categorical symmetry: for an autoequivalence `F` of `E` and an
initial `I`, the unique arrow `I ⟶ F I` is an isomorphism, it is the identity for `F = 𝟭`, and it
satisfies the strict cocycle law for composites.  Consequently the image of an initial execution
under any isomorphism-invariant, equivariant observation is a fixed point of the acting group, so
it cannot lie in a free nontrivial orbit.

Therefore an exactly symmetric source with an equivariant execution doctrine cannot canonically
produce a symmetry-breaking event.  The infinitesimal form of the same obstruction: a new
differential whose commutator with the grading operator vanishes still commutes with the whole
radial flow, so a nonzero commutator is necessary for radial selection.
-/

namespace HTGeometry.ConstraintRelativity

open CategoryTheory CategoryTheory.Limits

/-! ## Initial objects inherit symmetry -/

section Initial

variable {E : Type*} [Category E]

/-- The canonical comparison arrow from an initial object to its translate. -/
noncomputable def initialCompare {I : E} (hI : IsInitial I) (F : E ⥤ E) : I ⟶ F.obj I :=
  hI.to (F.obj I)

/-- **Uniqueness.**  There is exactly one comparison arrow. -/
theorem initialCompare_unique {I : E} (hI : IsInitial I) (F : E ⥤ E) (f : I ⟶ F.obj I) :
    f = initialCompare hI F :=
  hI.hom_ext f _

/-- **The identity translate.**  `α_1 = id`. -/
theorem initialCompare_id {I : E} (hI : IsInitial I) :
    initialCompare hI (𝟭 E) = 𝟙 I :=
  hI.hom_ext _ _

/-- **The cocycle law.**  `α_{gh} = F_g(α_h) ∘ α_g` in the composition order of the translates. -/
theorem initialCompare_comp {I : E} (hI : IsInitial I) (F F' : E ⥤ E) :
    initialCompare hI (F ⋙ F') = initialCompare hI F' ≫ F'.map (initialCompare hI F) :=
  hI.hom_ext _ _

/-- An autoequivalence sends an initial object to an initial object. -/
noncomputable def isInitialMap {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    IsInitial (F.obj I) :=
  hI.isInitialObj F I

/-- **The comparison arrow is an isomorphism.** -/
theorem isIso_initialCompare {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    IsIso (initialCompare hI F) := by
  have h := isInitialMap hI F
  refine ⟨h.to I, ?_, ?_⟩
  · exact hI.hom_ext _ _
  · exact h.hom_ext _ _

/-- The initial object is isomorphic to each of its translates. -/
noncomputable def initialIsoMap {I : E} (hI : IsInitial I) (F : E ⥤ E) [F.IsEquivalence] :
    I ≅ F.obj I :=
  hI.uniqueUpToIso (isInitialMap hI F)

end Initial

/-! ## The image of an initial execution is a fixed point -/

section Equivariant

variable {E : Type*} [Category E] {X : Type*} {G : Type*} [Group G] [MulAction G X]

/-- **Equivariant initial execution lands in the fixed locus.**  If a group acts on `E` by
autoequivalences and an isomorphism-invariant observation `P` is equivariant, then the observation
of an initial object is fixed by the whole group. -/
theorem smul_obs_initial (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) (g : G) :
    g • P I = P I := by
  have h1 : P I = P ((F g).obj I) := hPiso (initialIsoMap hI (F g))
  rw [hPequiv g I] at h1
  exact h1.symm

/-- **No free nontrivial orbit contains the observation of an initial execution.** -/
theorem not_free_orbit_obs_initial (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) :
    ¬ ∃ g : G, g ≠ 1 ∧ g • P I ≠ P I := by
  rintro ⟨g, _, hne⟩
  exact hne (smul_obs_initial F hI P hPiso hPequiv g)

/-- The stabilizer of the observation of an initial execution is the whole group. -/
theorem stabilizer_obs_initial_eq_top (F : G → E ⥤ E) [∀ g, (F g).IsEquivalence]
    {I : E} (hI : IsInitial I) (P : E → X)
    (hPiso : ∀ {Y Z : E}, (Y ≅ Z) → P Y = P Z)
    (hPequiv : ∀ (g : G) (Y : E), P ((F g).obj Y) = g • P Y) :
    MulAction.stabilizer G (P I) = ⊤ := by
  refine eq_top_iff.2 fun g _ => ?_
  exact smul_obs_initial F hI P hPiso hPequiv g

end Equivariant

/-! ## Infinitesimal anomaly necessity -/

section Anomaly

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- A radial flow: a family of operators acting on each eigenspace of the grading operator `∂` by
a scalar. -/
structure RadialFlow (K M : Type*) [Field K] [AddCommGroup M] [Module K M] where
  /-- The grading operator. -/
  grading : M →ₗ[K] M
  /-- The flow. -/
  flow : K → (M →ₗ[K] M)
  /-- The flow acts on each eigenspace of the grading by a scalar. -/
  weight : K → K → K
  /-- The scalar action on eigenvectors. -/
  flow_eigen : ∀ (c lam : K) (v : M), grading v = lam • v → flow c v = weight c lam • v
  /-- The eigenvectors span. -/
  span_eigen : ∀ v : M, ∃ (n : ℕ) (lam : Fin n → K) (w : Fin n → M),
    (∀ i, grading (w i) = lam i • w i) ∧ v = ∑ i, w i

/-- **Anomaly necessity.**  A new differential whose commutator with the grading operator vanishes
still commutes with the whole radial flow.  Hence a nonzero commutator `[d, ∂] ≠ 0` is a necessary
condition for a radially selecting execution. -/
theorem commute_flow_of_commute_grading (Γ : RadialFlow K M) (d : M →ₗ[K] M)
    (hcomm : d.comp Γ.grading = Γ.grading.comp d) (c : K) :
    d.comp (Γ.flow c) = (Γ.flow c).comp d := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨n, lam, w, hw, rfl⟩ := Γ.span_eigen v
  simp only [LinearMap.comp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdw : Γ.grading (d (w i)) = lam i • d (w i) := by
    have h1 := congrArg (fun f => f (w i)) hcomm
    simp only [LinearMap.comp_apply] at h1
    rw [← h1, hw i, map_smul]
  rw [Γ.flow_eigen c (lam i) (w i) (hw i), Γ.flow_eigen c (lam i) (d (w i)) hdw, map_smul]

/-- The contrapositive: a radial flow that fails to commute with a new differential forces a
nonzero commutator with the grading operator. -/
theorem grading_commutator_ne_zero (Γ : RadialFlow K M) (d : M →ₗ[K] M) (c : K)
    (h : d.comp (Γ.flow c) ≠ (Γ.flow c).comp d) :
    d.comp Γ.grading ≠ Γ.grading.comp d :=
  fun hcomm => h (commute_flow_of_commute_grading Γ d hcomm c)

/-! ### Radial flows exist, and the anomaly condition is satisfiable -/

section AnomalyWitness

variable {K : Type*} [Field K]

/-- The diagonal grading operator with weights `μ`. -/
def diagonalGrading {n : ℕ} (μ : Fin n → K) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v := fun i => μ i * v i
  map_add' _ _ := by funext i; exact mul_add _ _ _
  map_smul' c v := by
    funext i
    show μ i * (c * v i) = c * (μ i * v i)
    ring

@[simp] theorem diagonalGrading_apply {n : ℕ} (μ : Fin n → K) (v : Fin n → K) (i : Fin n) :
    diagonalGrading μ v i = μ i * v i := rfl

/-- **Radial flows exist.**  Any weight family `μ` and any weight law `g` give a radial flow on the
graded space `Kⁿ`: the grading is diagonal with eigenvalues `μ`, and the flow is diagonal with
entries `g c (μ i)`.  The anomaly theorems above are therefore not vacuous. -/
def diagonalRadialFlow {n : ℕ} (μ : Fin n → K) (g : K → K → K) :
    RadialFlow K (Fin n → K) where
  grading := diagonalGrading μ
  flow c := diagonalGrading fun i => g c (μ i)
  weight := g
  flow_eigen c lam v hv := by
    funext i
    have hi : μ i * v i = lam * v i := congrFun hv i
    show g c (μ i) * v i = g c lam * v i
    rcases eq_or_ne (v i) 0 with h0 | h0
    · rw [h0, mul_zero, mul_zero]
    · rw [mul_right_cancel₀ h0 hi]
  span_eigen v := by
    classical
    refine ⟨n, μ, fun i => Pi.single i (v i), fun i => ?_, ?_⟩
    · funext j
      simp only [diagonalGrading_apply, Pi.smul_apply, smul_eq_mul]
      rcases eq_or_ne j i with rfl | hji
      · rfl
      · rw [Pi.single_eq_of_ne hji, mul_zero, mul_zero]
    · exact (Finset.univ_sum_single v).symm

/-- The two-dimensional graded model with weights `0` and `1`, whose flow is the grading itself. -/
def anomalyFlow : RadialFlow K (Fin 2 → K) :=
  diagonalRadialFlow ![0, 1] fun _ lam => lam

/-- The lowering operator `d(v₀, v₁) = (v₁, 0)`. -/
def anomalyDifferential : (Fin 2 → K) →ₗ[K] (Fin 2 → K) where
  toFun v := ![v 1, 0]
  map_add' _ _ := by
    funext i
    fin_cases i <;> simp
  map_smul' c v := by
    funext i
    fin_cases i <;> simp

/-- **The anomaly condition is satisfiable.**  On the two-dimensional graded model the lowering
operator fails to commute with the radial flow, so the hypothesis of `grading_commutator_ne_zero`
is met and its conclusion is a genuine obstruction, not a vacuous one. -/
theorem anomalyDifferential_not_commute_flow (c : K) :
    (anomalyDifferential (K := K)).comp ((anomalyFlow (K := K)).flow c)
      ≠ ((anomalyFlow (K := K)).flow c).comp anomalyDifferential := by
  intro h
  have h1 := congrArg (fun f => f ![0, 1]) h
  have h2 : (1 : K) = 0 := by
    have h3 := congrFun h1 0
    simp [anomalyDifferential, anomalyFlow, diagonalRadialFlow, diagonalGrading] at h3
  exact one_ne_zero h2

/-- Consequently the commutator with the grading operator is nonzero on that model. -/
theorem anomalyDifferential_grading_commutator_ne_zero :
    (anomalyDifferential (K := K)).comp (anomalyFlow (K := K)).grading
      ≠ (anomalyFlow (K := K)).grading.comp anomalyDifferential :=
  grading_commutator_ne_zero _ _ 0 (anomalyDifferential_not_commute_flow 0)

end AnomalyWitness

end Anomaly

end HTGeometry.ConstraintRelativity
