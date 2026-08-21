import GaloisForLFunctions.HTGeometry.LeviCivita.Connection

/-!
# The fundamental theorem of Riemannian geometry

Every Riemannian manifold carries exactly one torsion-free metric covariant derivative on its
tangent bundle: the Levi-Civita connection built in
`GaloisForLFunctions.HTGeometry.LeviCivita.Connection`.

## Main results

* `torsion_leviCivita` — the Levi-Civita connection is torsion free;
* `isMetricCompatible_leviCivita` — it is compatible with the Riemannian metric;
* `koszulForm_eq_two_inner` — *any* torsion-free metric connection satisfies the Koszul formula
  `K(X, Y, Z) = 2⟪∇_X Y, Z⟫`, and is therefore determined by the metric alone;
* `eq_leviCivita` — hence it agrees with `leviCivita` on every section differentiable at the point;
* `difference_leviCivita_eq_zero` — the two connections have vanishing difference tensor;
* `fundamental_theorem_of_riemannian_geometry` — the packaged existence-and-uniqueness statement.

Uniqueness is necessarily stated for sections differentiable at the point in question: the axioms
of `IsCovariantDerivativeOn` constrain a covariant derivative only on such sections, so two
covariant derivatives satisfying the same structural conditions need not be *equal* as bare
functions.  The vanishing of the difference tensor `difference_leviCivita_eq_zero` is the precise
tensorial form of the uniqueness statement.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.LeviCivita

open Bundle NormedSpace Set VectorField FiberBundle
open scoped Manifold ContDiff Bundle

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun (x : M) ↦ TangentSpace I x)]

attribute [local instance] finiteDimensional_tangentSpace

variable {X Y Z σ τ : Π x : M, TangentSpace I x} {x : M}

/-- The Koszul formula with the last slot an arbitrary tangent vector. -/
lemma inner_covLC_right (hσ : MDiffAt (T% σ) x) (hX : MDiffAt (T% X) x)
    (v : TangentSpace I x) :
    (inner ℝ (covLC σ x (X x)) v : ℝ) = (2 : ℝ)⁻¹ * koszulForm X σ (extend E v) x := by
  have h := inner_covLC hσ hX (mdifferentiableAt_extend I E v)
  simpa using h

/-! ## The Levi-Civita connection is torsion free and metric -/

/-- The Levi-Civita connection has vanishing torsion. -/
theorem torsion_leviCivita : (leviCivita I M).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  refine ext_inner_right ℝ fun v ↦ ?_
  have h := koszulForm_sub_swap X Y (extend E v) x
  rw [extend_apply_self] at h
  rw [inner_sub_left, leviCivita_apply, leviCivita_apply, inner_covLC_right hY hX v,
    inner_covLC_right hX hY v]
  linarith

/-- The Levi-Civita connection is compatible with the Riemannian metric. -/
theorem isMetricCompatible_leviCivita :
    CovariantDerivative.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x)
      (leviCivita I M) := by
  rw [CovariantDerivative.isMetricCompatible_iff]
  intro x X σ τ hX hσ hτ
  have h := koszulForm_add_swap X σ τ x
  rw [gPair_def] at h
  have h1 := inner_covLC hσ hX hτ
  have h2 : (inner ℝ (σ x) (covLC τ x (X x)) : ℝ) = (2 : ℝ)⁻¹ * koszulForm X τ σ x := by
    rw [real_inner_comm]
    exact inner_covLC hτ hX hσ
  show mvfderiv I (fun y ↦ (inner ℝ (σ y) (τ y) : ℝ)) x (X x)
      = inner ℝ (covLC σ x (X x)) (τ x) + inner ℝ (σ x) (covLC τ x (X x))
  rw [h1, h2]
  linarith

/-! ## Uniqueness -/

/-- **The Koszul formula.**  A torsion-free metric covariant derivative on the tangent bundle is
completely determined by the Riemannian metric. -/
theorem koszulForm_eq_two_inner (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (htor : cov.torsion = 0)
    (hmet : CovariantDerivative.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x) cov)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    koszulForm X Y Z x = 2 * inner ℝ (cov Y x (X x)) (Z x) := by
  rw [CovariantDerivative.torsion_eq_zero_iff] at htor
  have e1 : mvfderiv I (fun y ↦ (inner ℝ (Y y) (Z y) : ℝ)) x (X x)
      = inner ℝ (cov Y x (X x)) (Z x) + inner ℝ (Y x) (cov Z x (X x)) :=
    hmet.mvfderiv_inner_eq X hY hZ
  have e2 : mvfderiv I (fun y ↦ (inner ℝ (Z y) (X y) : ℝ)) x (Y x)
      = inner ℝ (cov Z x (Y x)) (X x) + inner ℝ (Z x) (cov X x (Y x)) :=
    hmet.mvfderiv_inner_eq Y hZ hX
  have e3 : mvfderiv I (fun y ↦ (inner ℝ (X y) (Y y) : ℝ)) x (Z x)
      = inner ℝ (cov X x (Z x)) (Y x) + inner ℝ (X x) (cov Y x (Z x)) :=
    hmet.mvfderiv_inner_eq Z hX hY
  have b1 := htor hX hY
  have b2 := htor hX hZ
  have b3 := htor hY hZ
  have c1 : (inner ℝ (Y x) (cov Z x (X x)) : ℝ) = inner ℝ (cov Z x (X x)) (Y x) :=
    real_inner_comm _ _
  have c2 : (inner ℝ (Z x) (cov X x (Y x)) : ℝ) = inner ℝ (cov X x (Y x)) (Z x) :=
    real_inner_comm _ _
  have c3 : (inner ℝ (X x) (cov Y x (Z x)) : ℝ) = inner ℝ (cov Y x (Z x)) (X x) :=
    real_inner_comm _ _
  simp only [koszulForm, gPair_def, e1, e2, e3, ← b1, ← b2, ← b3, inner_sub_left, c1, c2, c3]
  ring

/-- Any torsion-free metric covariant derivative on the tangent bundle agrees with the
Levi-Civita connection on every section differentiable at the point. -/
theorem eq_leviCivita (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (htor : cov.torsion = 0)
    (hmet : CovariantDerivative.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x) cov) (hσ : MDiffAt (T% σ) x) :
    cov σ x = covLC σ x := by
  refine clm_ext_of_inner fun u v ↦ ?_
  have hu := mdifferentiableAt_extend I E u
  have hv := mdifferentiableAt_extend I E v
  have h1 : (inner ℝ (cov σ x ((extend E u) x)) ((extend E v) x) : ℝ)
      = (2 : ℝ)⁻¹ * koszulForm (extend E u) σ (extend E v) x := by
    rw [koszulForm_eq_two_inner cov htor hmet hu hσ hv]
    ring
  rw [inner_covLC_extend hσ u v]
  simpa using h1

/-- The difference tensor between any torsion-free metric covariant derivative and the
Levi-Civita connection vanishes. -/
theorem difference_leviCivita_eq_zero
    (cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x))
    (htor : cov.torsion = 0)
    (hmet : CovariantDerivative.IsMetricCompatible (F := E) (V := fun x : M ↦ TangentSpace I x) cov) :
    cov.difference (leviCivita I M) = 0 := by
  funext x
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv := mdifferentiableAt_extend I E v
  have h := IsCovariantDerivativeOn.difference_apply
      cov.isCovariantDerivativeOnUniv (leviCivita I M).isCovariantDerivativeOnUniv
      (x := x) (mem_univ x) hv
  rw [extend_apply_self] at h
  show CovariantDerivative.difference cov (leviCivita I M) x v = 0
  rw [CovariantDerivative.difference, h, leviCivita_apply,
    eq_leviCivita cov htor hmet hv]
  simp


/-! ## Classical restatements -/

/-- Torsion-freeness of the Levi-Civita connection in the classical form
`∇_X Y - ∇_Y X = [X, Y]`. -/
theorem covLC_sub_covLC (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    covLC Y x (X x) - covLC X x (Y x) = mlieBracket I X Y x := by
  have h := (CovariantDerivative.torsion_eq_zero_iff (cov := leviCivita I M)).1
    torsion_leviCivita hX hY
  simpa using h

/-- Metric compatibility of the Levi-Civita connection in the classical form
`X⟪Y, Z⟫ = ⟪∇_X Y, Z⟫ + ⟪Y, ∇_X Z⟫`. -/
theorem mvfderiv_gPair_eq (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    mvfderiv I (gPair Y Z) x (X x)
      = inner ℝ (covLC Y x (X x)) (Z x) + inner ℝ (Y x) (covLC Z x (X x)) := by
  have h := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq
    isMetricCompatible_leviCivita X hY hZ
  simpa [gPair_def] using h

/-! ## The theorem -/

variable (I M) in
/-- **The fundamental theorem of Riemannian geometry.**

On a Riemannian manifold there is a covariant derivative on the tangent bundle which is
torsion free and compatible with the metric, and any other such covariant derivative agrees with
it wherever a covariant derivative is constrained at all — equivalently, their difference tensor
vanishes identically.  This connection is the Levi-Civita connection. -/
theorem fundamental_theorem_of_riemannian_geometry :
    ∃ cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x),
      cov.torsion = 0 ∧ cov.IsMetricCompatible ∧
        ∀ cov' : CovariantDerivative I E (fun x : M ↦ TangentSpace I x),
          cov'.torsion = 0 → cov'.IsMetricCompatible →
            (∀ (σ : Π x : M, TangentSpace I x) (x : M), MDiffAt (T% σ) x → cov' σ x = cov σ x)
              ∧ cov'.difference cov = 0 :=
  ⟨leviCivita I M, torsion_leviCivita, isMetricCompatible_leviCivita, fun cov' h1 h2 ↦
    ⟨fun _ _ hσ ↦ eq_leviCivita cov' h1 h2 hσ, difference_leviCivita_eq_zero cov' h1 h2⟩⟩

/-- **Non-vacuity.**  Every finite-dimensional real inner product space, with its canonical
Riemannian structure, satisfies the entire hypothesis stack of
`fundamental_theorem_of_riemannian_geometry`. -/
example (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] :
    True := by
  have := fundamental_theorem_of_riemannian_geometry 𝓘(ℝ, F) F
  trivial

end GaloisForLFunctions.HTGeometry.LeviCivita
